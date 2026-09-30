#!/usr/bin/env python3
"""Avi blue-to-green migration, converged at every site and published through GSLB.

Customer-agnostic. Everything about one environment lives in its env YAML
(avi_* and gslb_* keys, beside the keys the other migration tools read), and
`converge` makes the green controllers match it:

  - every virtual service on blue, with everything it uses, at every green
    site, on that site's own cloud, VRF, Service Engine group and VIP network;
  - GSLB on the leader: a subdomain per zone, the DNS services authoritative
    for them, and one GSLB service per blue VIP answering <host>.<label>.<zone>;
  - each site's services live or staged, as avi_live_<site> says;
  - a flip list: every DNS name, its GSLB target, and whether it is READY.

No client reaches green until its DNS name is flipped to the GSLB name. The
flips are made from the flip list with Invoke-DnsFlip.ps1, on the Windows
side, name by name, whenever the application owner is ready.

    python3 avi_migrate.py selftest                              # offline, no credentials
    python3 avi_migrate.py --example-config                      # the keys, commented
    python3 avi_migrate.py converge --config env.example.yaml    # dry run: what would change
    python3 avi_migrate.py converge --config env.example.yaml --commit
    python3 avi_migrate.py status   --config env.example.yaml    # read-only: readiness and the flip list
    python3 avi_migrate.py export   --config env.example.yaml    # read blue only, for review
    python3 avi_migrate.py discover --config env.example.yaml    # read-only: DNS names from blue and the DCs
    python3 avi_migrate.py purge    --config env.example.yaml    # dry run: what purge would delete

Idempotent. Each object is reported as ADD, UPDATE, UNCHANGED, FROZEN, KEPT
or BLOCKED; a second run after a commit reports UNCHANGED. Blue is the source
of truth for an application until one of its names is flipped. From then on
green owns it: converge no longer updates it from blue (FROZEN), leaves its
GSLB service's members, priorities and TTL and its services' live state as
green has them, and never takes it offline. converge never deletes anything, and
nothing is ever written to blue (the client refuses it, and a target that
turns out to be blue's cluster is refused). purge takes away what converge
made, and nothing else: never an object that was on green before, never one
a flipped application uses; the next converge builds it all again. A live service is taken out of
service only with --allow-offline, and UPDATEs wait while the DNS export is
missing or lacks a zone of gslb_zones, since then a flip could go unseen.

Private keys are read from blue with export_key while writing and posted
straight to green. They are never written to disk or to a journal.

Objects are posted with blue's API version, so each target converts fields
renamed or removed between the two releases itself.

Python 3.9+, requests. PyYAML optional.
"""
import argparse
import copy
import csv
import fnmatch
import getpass
import hashlib
import ipaddress
import json
import os
import random
import re
import socket
import ssl
import stat
import struct
import subprocess
import sys
import time
from datetime import datetime, timezone
from urllib.parse import parse_qsl, urlencode, urlparse, urlsplit

try:
    import requests
except ImportError:  # selftest runs without it
    requests = None

VERSION = '3.4.6'

# ---------------------------------------------------------------- object model

# Types this tool creates on a target. The order is only a tiebreak between
# objects with no relationship; the real order is derived from references.
PORTABLE = [
    'stringgroup', 'ipaddrgroup', 'prioritylabels', 'protocolparser',
    'analyticsprofile', 'healthmonitor', 'applicationpersistenceprofile',
    'networkprofile', 'pkiprofile', 'sslprofile', 'jwtserverprofile',
    'authprofile', 'certificatemanagementprofile', 'errorpagebody',
    'errorpageprofile', 'icapprofile', 'trafficcloneprofile', 'wafprofile',
    'wafpolicypsmgroup', 'wafpolicy', 'botdetectionpolicy', 'csrfpolicy',
    'securitypolicy', 'ssopolicy', 'applicationprofile', 'sslkeyandcertificate',
    'autoscalelaunchconfig', 'serverautoscalepolicy', 'pool',
    'poolgroupdeploymentpolicy', 'poolgroup', 'vsdatascriptset',
    'httppolicyset', 'dnspolicy', 'l4policyset', 'networksecuritypolicy',
    'natpolicy', 'microservice', 'microservicegroup', 'vsvip', 'virtualservice',
]

# Shipped with the product and present on every controller. Never created;
# resolved by name on the target.
SYSTEM_TYPES = {
    'wafcrs', 'geodb', 'ipreputationdb', 'wafapplicationsignatureprovider',
    'botmapping', 'botconfigconsolidator', 'botipreputationtypemapping',
}

# The environment, not the configuration. Never created. cloud, vrfcontext and
# serviceenginegroup collapse to the site's own (avi_cloud_<site>,
# avi_vrf_<site>, avi_se_group_<site>) unless avi_map_<site> says otherwise.
# Every other environment reference must be mapped explicitly.
ENVIRONMENT = {
    'cloud', 'vrfcontext', 'serviceenginegroup', 'network', 'tenant',
    'vimgrnwruntime', 'vimgrvmruntime', 'ipamdnsproviderprofile', 'seproperties',
    'cluster', 'hardwaresecuritymodulegroup', 'fileobject', 'vcenterserver',
    'nsxtsegmentruntime', 'availabilityzone', 'testsedatastorelevel1',
}
COLLAPSIBLE = {'cloud': 'cloud', 'vrfcontext': 'vrf', 'serviceenginegroup': 'se_group'}

# Server-owned, internal or source-specific fields, removed before posting.
STRIP_ANYWHERE = {'configpb_attributes', 'cloud_config_cksum', 'vsvip_cloud_config_cksum'}
STRIP_TOP = {
    'uuid', 'url', 'tenant_ref', 'created_by', 'last_modified', 'se_uuids',
    'vip_runtime', 'oper_status', 'num_se_assigned', 'version', 'cloud_type',
    'flavor', 'east_west_placement', 'is_federated',
}
STRIP_BY_TYPE = {
    # vip and the address fields are the pre-VsVip inline form, which 32.1
    # no longer has; the VsVip carries the address.
    'virtualservice': {
        'vip', 'ip_address', 'ip6_address', 'floating_ip', 'floating_ip6',
        'floating_subnet_uuid', 'auto_allocate_ip', 'auto_allocate_floating_ip',
        'discovered_network_ref', 'discovered_networks', 'discovered_subnet',
        'network_ref', 'subnet', 'subnet_uuid', 'port_uuid', 'sp_pool_refs',
        'azure_availability_set', 'bgp_local_preference', 'bgp_num_as_path_prepend',
        'dns_info', 'fqdn', 'ipam_network_subnet', 'nsx_securitygroup',
        # Runtime state, in neither release's object model. tls_ticket_key is
        # blue's live session-ticket keys: green makes its own.
        'tls_ticket_key', 'redis_db', 'redis_port', 'marked_for_delete', 'self_se_election',
    },
    'vsvip': {'ipam_selector', 'use_standard_alb'},
    'pool': {'networks', 'sp_gs_info', 'gslb_sp_enabled', 'placement_networks'},
    'sslkeyandcertificate': {
        'status', 'ocsp_response_info', 'ocsp_error_status',
        'ocsp_responder_url_list_from_certs', 'key', 'key_passphrase', 'key_params',
        'import_key_to_hsm', 'enckey_base64', 'enckey_name', 'dynamic_params',
    },
}
# On each VIP: the address, and every reference to where it lived on blue.
VIP_STRIP = {
    'ip_address', 'ip6_address', 'floating_ip', 'floating_ip6', 'floating_subnet_uuid',
    'floating_subnet6_uuid', 'subnet', 'subnet6', 'subnet_uuid', 'subnet6_uuid',
    'network_ref', 'port_uuid', 'discovered_networks', 'placement_networks',
    'avi_allocated_vip', 'avi_allocated_fip', 'auto_allocate_floating_ip',
    'ipam_network_subnet', 'availability_zone',
}
# On each pool server: what the source cloud discovered about it.
SERVER_STRIP = {
    'discovered_networks', 'nw_ref', 'vm_ref', 'mac_address', 'external_uuid',
    'external_orchestration_id', 'server_node',
}

# Objects managed by an orchestrator are recreated by it, not migrated.
ORCHESTRATED = re.compile(r'ako|wcp|supervisor|tkg|kubernetes|k8s|openshift', re.I)
# Signature and chain records sit beside every name in a signed zone; they
# neither block a CNAME nor move with one.
DNSSEC_TYPES = ('RRSIG', 'NSEC', 'NSEC3', 'NSEC3PARAM', 'DNSKEY', 'DS', 'CDS', 'CDNSKEY')
SECRET_KEY = re.compile(r'(^|_)(password|passphrase|secret|shared_secret|client_secret)$')
WEAK_SIG = re.compile(r'(sha1|sha-1|md5)', re.I)
# Not supported from 31.2.1: the target refuses them.
LEGACY_TLS = re.compile(r'(3DES|DES-CBC3|SSL_VERSION_SSLV3)', re.I)
# Accepted, but flagged: TLS 1.0/1.1, RC4/MD5/export/null, and SHA-1 MAC suites.
WEAK_VERSIONS = {'SSL_VERSION_TLS1', 'SSL_VERSION_TLS1_1'}
WEAK_CIPHER = re.compile(r'(RC4|MD5|EXPORT|NULL|-SHA$|_CBC_SHA$)', re.I)
HM_PACKAGES = re.compile(r'\b(pymssql|cx_Oracle)\b')

REF_RE = re.compile(r'^(?:https?://([^/]+))?/api/([a-z0-9]+)/([A-Za-z0-9_.:-]+)(?:#(.*))?$')


# ---------------------------------------------------------------- small helpers

def now():
    return datetime.now(timezone.utc).isoformat()


def as_list(v):
    if v is None or v == '':
        return []
    if isinstance(v, (list, tuple)):
        return [x for x in v if x not in (None, '')]
    return [x.strip() for x in str(v).split(',') if x.strip()]


def pairs(v):
    """['a=b', 'c=d'] -> {'a': 'b', 'c': 'd'}. Names containing ':' stay intact."""
    out = {}
    for item in as_list(v):
        if '=' not in str(item):
            raise ValueError('expected source=target, got: %s' % item)
        k, val = str(item).split('=', 1)
        out[k.strip()] = val.strip()
    return out


def strings(v):
    if isinstance(v, str):
        yield v
    elif isinstance(v, dict):
        for x in v.values():
            yield from strings(x)
    elif isinstance(v, list):
        for x in v:
            yield from strings(x)


def parse_ref(s):
    """An Avi reference as {'host','type','uuid','name'}, else None. A missing
    or empty '#Name' fragment leaves name None: it cannot be resolved by name."""
    if not isinstance(s, str):
        return None
    m = REF_RE.match(s)
    if not m:
        return None
    return {'host': m.group(1), 'type': m.group(2), 'uuid': m.group(3),
            'name': m.group(4) or None, 'raw': s}


def refkey(s):
    r = parse_ref(s)
    return (r['type'], r['uuid']) if r else None


def ref_name(s):
    r = parse_ref(s)
    return r['name'] if r else None


def is_ref_key(k):
    return k.endswith('_ref') or k.endswith('_refs')


def ref_values(v):
    """Every value held in a *_ref or *_refs field, at any depth. In every
    object type this tool moves, that naming is exactly the set of references
    (checked against the 31.1.2 and 32.1.3 object models), so an application
    path such as 'GET /api/v1/health' in a monitor is never mistaken for one."""
    if isinstance(v, dict):
        for k, x in v.items():
            if is_ref_key(k) and isinstance(x, str):
                yield x
            elif is_ref_key(k) and isinstance(x, list):
                for y in x:
                    if isinstance(y, str):
                        yield y
                    else:
                        yield from ref_values(y)
            else:
                yield from ref_values(x)
    elif isinstance(v, list):
        for x in v:
            yield from ref_values(x)


def iter_refs(v):
    seen = set()
    for s in ref_values(v):
        if s in seen:
            continue
        seen.add(s)
        r = parse_ref(s)
        if r:
            yield r


def stray_refs(v):
    """Reference values that do not parse as a reference, e.g. a query form."""
    return sorted(set(x for x in ref_values(v) if not parse_ref(x)))


def map_refs(v, fn):
    """Apply fn to every reference value and leave everything else alone."""
    if isinstance(v, dict):
        out = {}
        for k, x in v.items():
            if is_ref_key(k) and isinstance(x, str):
                out[k] = fn(x)
            elif is_ref_key(k) and isinstance(x, list):
                out[k] = [fn(y) if isinstance(y, str) else map_refs(y, fn) for y in x]
            else:
                out[k] = map_refs(x, fn)
        return out
    if isinstance(v, list):
        return [map_refs(x, fn) for x in v]
    return v


def remap(v, mapping):
    return map_refs(v, lambda s: mapping.get(s, s))


def text_mentions(v, hosts, key=None):
    """Text fields, not references, that name one of these controllers."""
    out = []
    if isinstance(v, dict):
        for k, x in v.items():
            if not is_ref_key(k):
                out.extend(text_mentions(x, hosts, k))
    elif isinstance(v, list):
        for x in v:
            out.extend(text_mentions(x, hosts, key))
    elif isinstance(v, str) and any('//%s' % h in v for h in hosts):
        out.append(key or '?')
    return out


def clean(v, objtype=None, top=True):
    if isinstance(v, dict):
        out = {}
        for k, x in v.items():
            if k.startswith('_') or k in STRIP_ANYWHERE:
                continue
            if top and (k in STRIP_TOP or k in STRIP_BY_TYPE.get(objtype, ())):
                continue
            out[k] = clean(x, objtype, False)
        return out
    if isinstance(v, list):
        return [clean(x, objtype, False) for x in v]
    return v


def ip4(addr):
    return {'addr': str(addr), 'type': 'V4'}


def prefix(cidr):
    net = ipaddress.ip_network(str(cidr), strict=False)
    return {'ip_addr': ip4(net.network_address), 'mask': net.prefixlen}


def split_key(key):
    t, n = key.split('/', 1)
    return t, n


def close_names(name, names, limit=6):
    stem = re.sub(r'^GM:', '', str(name)).lower()[:8]
    return sorted(n for n in names if stem and stem in str(n).lower())[:limit]


def fmt_list(items, limit=8):
    items = list(items)
    s = ', '.join(str(x) for x in items[:limit])
    return s + (' ...+%d' % (len(items) - limit) if len(items) > limit else '')


def banner(title):
    print('')
    print('=' * 78)
    print(' ' + title)
    print(' avi_migrate %s' % VERSION)
    print('=' * 78)


# ---------------------------------------------------------------- config

EXAMPLE_CONFIG = """# ---------------------------------------------------------------------------
# avi_migrate 3: the Avi migration + GSLB keys of an environment file.
# Put them in env.<customer>.yaml beside the keys the other tools read. Flat
# keys; YAML (PyYAML if installed) or JSON.
#
# Passwords: environment variable, then this file, then an interactive prompt.
#   AVI_SOURCE_PASSWORD, AVI_TARGET_PASSWORD_<SITE>   e.g. AVI_TARGET_PASSWORD_D1
# A controller certificate this machine does not trust is shown by fingerprint
# and pinned once you confirm it; for runs with nobody at the prompt, list the
# confirmed fingerprints:  export AVI_TRUST_SHA256='<fp>,<fp>'
# ---------------------------------------------------------------------------
site_name: example
avi_outdir: ./avi_migration            # export, plans, journals, the flip list

# ---- blue: the controller being migrated FROM ------------------------------
avi_source_host: https://old-controller.example.com
avi_source_user: admin
# avi_exclude: [virtualservice/retired-*]   # left out, by type/name or name

# ---- green sites -------------------------------------------------------------
# Every value is the name of an object that already exists on that controller.
# Blue's clouds, VRFs and SE groups all collapse to the site's own.
avi_sites: [site_a, site_b]

avi_target_host_site_a: https://site1-controller.example.com
avi_target_user_site_a: admin
avi_cloud_site_a: Site1-NSX-Cloud
avi_vrf_site_a: T1-SITE1-LOCAL
avi_se_group_site_a: Site1-SE-Group        # never Default-Group, unless avi_allow_default_group_site_a: true
avi_vip_network_site_a: net-10.1.100.0-24  # VIPs are allocated from this network
avi_vip_subnet_site_a: 10.1.100.0/24
# avi_tier1_site_a: /infra/tier-1s/<id>    # read from an existing VIP in the VRF when unset
# avi_map_site_a: [wafcrs/CRS-2023-1=wafcrs/CRS-2025-2]   # explicit renames, when the plan asks
# Which services take traffic here: all, none, or a list of name patterns.
# Live costs Service Engines and licence units; staged costs nothing. No client
# reaches a live service until its DNS name is flipped. Unset means none.
avi_live_site_a: all

avi_target_host_site_b: https://site2-controller.example.com
avi_target_user_site_b: admin
avi_cloud_site_b: Site2-NSX-Cloud
avi_vrf_site_b: T1-SITE2-LOCAL
avi_se_group_site_b: Site2-SE-Group
avi_vip_network_site_b: net-10.2.100.0-24
avi_vip_subnet_site_b: 10.2.100.0/24
avi_live_site_b: all
# The SE group raised (never lowered) so every live service can be placed.
# max_vs_per_se costs no licence units; max_se does, at the group's SE size.
# avi_se_max_vs_per_se_site_b: 25
# avi_se_max_se_site_b: 7

# ---- GSLB --------------------------------------------------------------------
gslb_leader: site_a
gslb_site_name_site_a: SITE-A                  # site names under Infrastructure > GSLB
gslb_site_name_site_b: SITE-B
gslb_priority_site_a: 20                   # higher wins; these win over the template's
gslb_priority_site_b: 10
# The datacenter toggle: the site every GSLB service answers with while its member
# there is up. site_b swaps the priorities above (site_b 20, site_a 10) on every GSLB service
# this tool made, flipped applications included; only the priorities change.
gslb_active_site: site_a
gslb_ttl: 30
gslb_template_service: ""              # an existing GSLB service to copy settings from
gslb_label: gslb                       # names are <host>.<gslb_label>.<zone>
gslb_zones: [example.com]
gslb_dns_profile: gslb-dns             # only if a site's DNS service has no profile
gslb_dns_vips: [10.1.100.11, 10.2.100.11]
gslb_names: ./dns_records.csv          # written by discover (from blue and dns_servers), or on a DC by
                                       # Export-DnsRecords.ps1 -Zones <every gslb_zones entry>
# gslb_discover_names: [db.example.com]   # names discover asks about beyond what blue mentions
# gslb_vip_alias: [203.0.113.10=vsvip-portal]   # an address in front of a blue VIP (a NAT): names pointing at it are its
# gslb_infer_alias: true   # a name blue gives one VIP, served today from another address (another load balancer, a
#                          # NAT): it gets GSLB with that VIP, and a flip moves it from there. false: those get none
# gslb_exclude: [legacy.example.com]   # names never published
# gslb_include_disabled: [old.example.com]   # publish although disabled on blue
# gslb_member: [vsvip-shared=shared-443]     # which service GSLB watches, per blue VIP
# gslb_hold: [photon]                  # GSLB services converge leaves exactly as they are

# The DNS servers clients use (the domain controllers). converge asks them
# which names are already flipped; that decides what it may still update.
# Unset: the resolvers in /etc/resolv.conf.
# dns_servers: [10.1.10.11, 10.2.10.11]

# ---- decisions ---------------------------------------------------------------
# 3DES and SSLv3 are not supported from 31.2.1. false: SSL profiles carrying
# them are blocked. true: the tool removes them and says so.
avi_drop_legacy_tls: false
# What moved between blue's release and green's: source (the default) posts in
# blue's release and the target converts it, as 32.1 converts a pool's timeout;
# target has this tool convert it and post in green's. Either way, what green
# refuses or no longer has is removed first, and the plan lists every change.
# avi_write_version: source
# avi_live_include_disabled: [old-app*]   # live although disabled on blue
# avi_ignore_fields: [pool.description]   # fields green rewrites; never an UPDATE
# avi_vip_dns_info: auto   # a VIP's DNS names (App Domain Name): auto writes them unless the site's cloud registers
#                          # names with an outside DNS provider; keep writes them anyway; drop never does
# avi_sync_moved: false                   # true: keep updating flipped apps from blue
# avi_adopt: [healthmonitor/App-HTTPS]    # same-named objects on green this tool takes over
# avi_secrets: [healthmonitor/LDAP-389]   # secrets blue won't hand back, typed in when written
#                                         # (or AVI_SECRET_<TYPE>_<NAME>_<FIELD> for unattended runs)
# avi_freeze: [portal-*]                  # virtual services never updated from blue again
"""


def read_config(path):
    """YAML via PyYAML if importable; else JSON; else flat 'key: value' YAML."""
    if not path:
        return {}
    if not os.path.exists(path):
        sys.exit('config not found: %s' % path)
    mode = stat.S_IMODE(os.stat(path).st_mode)
    with open(path) as fh:
        text = fh.read()
    has_secret = re.search(r'^[ \t]*[^#\n]*passw[^:\n]*:[ \t]*[^#\s]', text, re.I | re.M)
    if mode & 0o077 and has_secret:
        print('WARNING: %s holds a password and is readable by others (mode %o). '
              'Run: chmod 600 %s' % (path, mode, path), file=sys.stderr)
    try:
        import yaml  # type: ignore
    except ImportError:
        yaml = None
    if yaml is not None:
        try:
            return yaml.safe_load(text) or {}
        except yaml.YAMLError as exc:
            mark = getattr(exc, 'problem_mark', None)
            where = ' at line %d' % (mark.line + 1) if mark else ''
            raise SystemExit('%s is not valid YAML%s: %s\nAnything containing a colon, or '
                             'starting with @ %% * & { or [, has to be quoted.'
                             % (path, where, getattr(exc, 'problem', exc))) from None
    try:
        return json.loads(text)
    except Exception:
        pass
    cfg, pending, buf = {}, None, ''
    for raw in text.splitlines():
        line = raw.split('#', 1)[0].rstrip()
        if pending is not None:
            buf += ' ' + line.strip()
            if ']' in line:
                items = buf[:buf.index(']')]
                cfg[pending] = [x.strip().strip('\'"') for x in items.split(',') if x.strip()]
                pending, buf = None, ''
            continue
        if not line.strip() or ':' not in line:
            continue
        k, v = line.split(':', 1)
        k, v = k.strip(), v.strip()
        if v.startswith('[') and ']' not in v:
            pending, buf = k, v[1:]
            continue
        v = v.strip('\'"')
        if v.startswith('[') and v.endswith(']'):
            v = [x.strip().strip('\'"') for x in v[1:-1].split(',') if x.strip()]
        cfg[k] = v
    return cfg


def truthy(v):
    return str(v).strip().lower() in ('1', 'true', 'yes', 'on')


def secret(cfg, key, env, prompt):
    """Environment variable, then config file, then interactive prompt."""
    return os.environ.get(env) or cfg.get(key) or getpass.getpass(prompt)


def sites_of(cfg):
    sites = [str(s) for s in as_list(cfg.get('avi_sites'))]
    if not sites:
        raise ValueError('avi_sites is not set in the config, e.g. avi_sites: [site_a, site_b]')
    return sites


def site_conf(cfg, site):
    def g(k, default=None):
        v = cfg.get('%s_%s' % (k, site))
        return default if v in (None, '') else v
    return {
        'site': site,
        'host': g('avi_target_host'),
        'cloud': g('avi_cloud'),
        'vrf': g('avi_vrf'),
        'se_group': g('avi_se_group'),
        'vip_network': g('avi_vip_network'),
        'vip_subnet': g('avi_vip_subnet'),
        'tier1': g('avi_tier1'),
        'map': pairs(g('avi_map')),
        'allow_default_group': truthy(g('avi_allow_default_group', 'false')),
        'gslb_site': str(g('gslb_site_name', site.upper())),
        'priority': g('gslb_priority'),
        'live': live_patterns(g('avi_live')),
    }


def live_patterns(v):
    """avi_live_<site>: 'all', 'none' or name patterns -> a list of patterns."""
    items = [str(x) for x in as_list(v)]
    if not items or [x.lower() for x in items] == ['none']:
        return []
    if [x.lower() for x in items] == ['all']:
        return ['*']
    return items


def matches(name, patterns):
    return any(fnmatch.fnmatchcase(str(name), str(p)) for p in patterns)


def site_tag(cfg):
    return re.sub(r'[^A-Za-z0-9_.-]', '_', str(cfg.get('site_name') or 'site'))


def outdir(cfg):
    # avi_outdir, not outdir: the env file's outdir belongs to another tool.
    d = str(cfg.get('avi_outdir') or './avi_migration')
    os.makedirs(d, exist_ok=True)
    return d


def artefact(cfg, kind, ext='json', site=None):
    name = '%s-%s%s.%s' % (site_tag(cfg), kind, ('-' + site) if site else '', ext)
    return os.path.join(outdir(cfg), name)


def save(path, data):
    """Exports, plans and maps are reproducible from a live read, so a re-run
    replaces them. Journals are the only files never overwritten."""
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
    with os.fdopen(fd, 'w') as f:
        json.dump(data, f, indent=2, sort_keys=True)
        f.write('\n')


def read(path):
    if not os.path.exists(path):
        raise ValueError('%s does not exist; run the step that writes it first' % path)
    with open(path) as f:
        return json.load(f)


class Journal:
    """Every write, before and after, one JSON line each. Never overwritten."""
    def __init__(self, path, required=False):
        if required and not path:
            raise ValueError('--journal is required with --commit')
        self.fh, self.path = None, path
        if path:
            fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_APPEND, 0o600)
            self.fh = os.fdopen(fd, 'a')

    def record(self, **kw):
        if not self.fh:
            return
        kw['at'] = now()
        self.fh.write(json.dumps(kw, sort_keys=True) + '\n')
        self.fh.flush()
        os.fsync(self.fh.fileno())

    def close(self):
        if self.fh:
            self.fh.close()
            self.fh = None


class Registry:
    """What this tool made or was handed, per site: (site, type, name) -> uuid.
    Append-only, beside the journals in avi_outdir. converge only ever
    updates, publishes or sets live what is in here; everything else on green
    is left exactly as it is. Losing the file makes the tool touch nothing
    that exists until --adopt hands objects back to it."""

    def __init__(self, cfg):
        self.path = artefact(cfg, 'managed', 'jsonl')
        self.items, self.digests, self.pending, self.how = {}, {}, set(), {}
        if os.path.exists(self.path):
            with open(self.path) as fh:
                for line in fh:
                    try:
                        rec = json.loads(line)
                    except ValueError:
                        continue
                    k = (rec.get('site'), rec.get('type'), rec.get('name'))
                    if rec.get('how') == 'intended':
                        self.pending.add(k)
                    elif rec.get('how') == 'abandoned':
                        self.pending.discard(k)
                    elif rec.get('how') == 'deleted':
                        self.items.pop(k, None)
                        self.digests.pop(k, None)
                        self.how.pop(k, None)
                        self.pending.discard(k)
                    if rec.get('how') in ('added', 'adopted') and rec.get('uuid'):
                        self.items[k] = rec['uuid']
                        self.how[k] = rec['how']
                        self.digests.pop(k, None)
                        self.pending.discard(k)
                    if rec.get('digest') and self.items.get(k) == rec.get('uuid'):
                        self.digests[k] = rec['digest']

    def owns(self, site, objtype, name, uuid):
        """Made or handed over, or created by a write whose reply never came."""
        k = (site, objtype, name)
        return bool(uuid) and (self.items.get(k) == uuid or k in self.pending)

    def claimed(self, site, objtype, name, uuid):
        """Owned only through a write whose reply never came: record it properly."""
        k = (site, objtype, name)
        return bool(uuid) and k in self.pending and self.items.get(k) != uuid

    def digest(self, site, objtype, name):
        """The desired state last written to this object, as a digest."""
        return self.digests.get((site, objtype, name))

    def _write(self, rec):
        fd = os.open(self.path, os.O_WRONLY | os.O_CREAT | os.O_APPEND, 0o600)
        with os.fdopen(fd, 'a') as fh:
            fh.write(json.dumps(rec, sort_keys=True) + '\n')
            fh.flush()
            os.fsync(fh.fileno())

    def intend(self, site, objtype, name):
        """Written before a create: if its reply is lost, the object it made is
        still this tool's, and the next run takes it over."""
        k = (site, objtype, name)
        if k not in self.pending:
            self._write({'site': site, 'type': objtype, 'name': name, 'how': 'intended', 'at': now()})
            self.pending.add(k)

    def abandon(self, site, objtype, name):
        """The create was refused outright, so nothing was made."""
        k = (site, objtype, name)
        if k in self.pending:
            self._write({'site': site, 'type': objtype, 'name': name, 'how': 'abandoned', 'at': now()})
            self.pending.discard(k)

    def at(self, site):
        """(type, name) -> (uuid or None, how) for everything held at one site."""
        out = {}
        for (s_, t, n), u in self.items.items():
            if s_ == site:
                out[(t, n)] = (u, self.how.get((s_, t, n), 'added'))
        for (s_, t, n) in self.pending:
            if s_ == site and (t, n) not in out:
                out[(t, n)] = (None, 'added')
        return out

    def record(self, site, objtype, name, uuid, how, digest=None):
        k = (site, objtype, name)
        if how == 'deleted':
            if k in self.items or k in self.pending:
                self._write({'site': site, 'type': objtype, 'name': name, 'uuid': uuid, 'how': 'deleted', 'at': now()})
                for m in (self.items, self.digests, self.how):
                    m.pop(k, None)
                self.pending.discard(k)
            return
        if not uuid or (self.items.get(k) == uuid and how != 'applied' and k not in self.pending) or \
                (how == 'applied' and self.digests.get(k) == digest):
            return
        rec = {'site': site, 'type': objtype, 'name': name, 'uuid': uuid, 'how': how, 'at': now()}
        if digest:
            rec['digest'] = digest
        self._write(rec)
        if how in ('added', 'adopted'):
            self.items[k] = uuid
            self.how[k] = how
            self.digests.pop(k, None)
            self.pending.discard(k)
        if digest:
            self.digests[k] = digest


def uuid_of(url):
    r = parse_ref(url or '')
    return r['uuid'] if r else None


# ---------------------------------------------------------------- TLS
# The controllers present VMCA-signed or self-signed chains. Verification is
# never disabled. A chain that does not verify is shown by fingerprint and
# pinned under ~/.avi_build/certs (shared with avi_build.py) only when the
# operator vouches for it; a certificate that later changes is refused before
# the password is sent, until the cached copy is deleted. A configured
# ca_bundle is never overridden by pinning.

CERT_CACHE = os.path.join(os.path.expanduser('~'), '.avi_build', 'certs')


def fetch_chain(host, port=443, timeout=15):
    ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
    ctx.check_hostname = False
    ctx.verify_mode = ssl.CERT_NONE  # only to read a chain that does not verify yet
    leaf_der, proto = None, None
    try:
        with socket.create_connection((host, port), timeout=timeout) as sock:
            with ctx.wrap_socket(sock, server_hostname=host) as tls:
                proto = tls.version()
                leaf_der = tls.getpeercert(binary_form=True)
                getter = getattr(tls, 'get_unverified_chain', None)
                if getter:
                    pems = []
                    for cert in getter() or []:
                        try:
                            pems.append(ssl.DER_cert_to_PEM_cert(cert.public_bytes(1)))
                        except Exception:
                            pass
                    if pems:
                        return pems, leaf_der, proto
    except Exception:
        if leaf_der is None:
            raise
    try:
        out = subprocess.run(['openssl', 's_client', '-connect', '%s:%d' % (host, port),
                              '-servername', host, '-showcerts'],
                             input='', capture_output=True, text=True, timeout=timeout).stdout
        pems, cur = [], []
        for line in out.splitlines():
            if 'BEGIN CERTIFICATE' in line:
                cur = [line]
            elif 'END CERTIFICATE' in line and cur:
                cur.append(line)
                pems.append('\n'.join(cur) + '\n')
                cur = []
            elif cur:
                cur.append(line)
        if pems:
            return pems, leaf_der, proto
    except Exception:
        pass
    if leaf_der:
        return [ssl.DER_cert_to_PEM_cert(leaf_der)], leaf_der, proto
    raise RuntimeError('%s presented no certificate' % host)


def fingerprint(der):
    if not der:
        return '?'
    fp = hashlib.sha256(der).hexdigest()
    return ':'.join(fp[i:i + 2] for i in range(0, len(fp), 2)).upper()


def vouched_for(host, fp):
    """A certificate seen for the first time is pinned only when the operator
    vouches for it: its fingerprint in AVI_TRUST_SHA256, or a yes at a prompt.
    Without either, nothing is pinned and no password is sent."""
    def norm(x):
        return re.sub(r'[^0-9a-f]', '', x.lower())
    listed = [norm(x) for x in re.split(r'[\s,;]+', os.environ.get('AVI_TRUST_SHA256', '')) if x.strip()]
    if norm(fp) in listed:
        print('  it matches AVI_TRUST_SHA256')
        return True
    if not (sys.stdin and sys.stdin.isatty()):
        return False
    try:
        ans = input('  Is this the certificate a browser shows for https://%s? Type yes to pin it: ' % host)
    except EOFError:
        return False
    return ans.strip().lower() in ('y', 'yes')


def pin_certificate(host, port=443):
    os.makedirs(CERT_CACHE, mode=0o700, exist_ok=True)
    path = os.path.join(CERT_CACHE, '%s.pem' % (host if port == 443 else '%s_%d' % (host, port)))
    if os.path.exists(path):
        return path, False
    chain, leaf_der, proto = fetch_chain(host, port)
    fp = fingerprint(leaf_der)
    where = host if port == 443 else '%s:%d' % (host, port)
    print('  %s presents a certificate this machine does not trust: %s, %d certificate(s)\n'
          '    leaf SHA-256 %s' % (where, proto or 'TLS', len(chain), fp))
    if not vouched_for(where, fp):
        raise RuntimeError('%s: certificate not pinned, nothing sent. Check the fingerprint above against the '
                           'one a browser shows for https://%s, then run again and answer yes, or set '
                           'AVI_TRUST_SHA256 to it.' % (where, where))
    tmp = path + '.tmp'
    with open(tmp, 'w') as fh:
        fh.write(''.join(chain))
    os.chmod(tmp, 0o600)
    os.replace(tmp, path)
    print('  pinned %s at %s' % (where, path))
    return path, True


def certificate_changed(host, port, bundle):
    """Refuse to send a password to a certificate that is not the pinned one."""
    try:
        with open(bundle) as fh:
            pinned = fingerprint(ssl.PEM_cert_to_DER_cert(fh.read().split('-----END CERTIFICATE-----')[0]
                                                          + '-----END CERTIFICATE-----\n'))
    except (OSError, ValueError):
        pinned = '?'
    try:
        now_fp = fingerprint(fetch_chain(host, port)[1])
    except Exception:
        now_fp = '?'
    return ('%s presents a different certificate from the one pinned for it.\n'
            '  pinned  %s\n  now     %s\n'
            'Nothing was sent. If the certificate was replaced on purpose (VCF Operations renews '
            'them), check the new fingerprint in the controller UI, then delete %s and run again.'
            % (host, pinned, now_fp, bundle))


def verifies(host, bundle, timeout=10, port=443):
    ctx = ssl.create_default_context()
    try:
        ctx.load_verify_locations(cafile=bundle)
        with socket.create_connection((host, port), timeout=timeout) as sock:
            with ctx.wrap_socket(sock, server_hostname=host):
                return True
    except ssl.SSLCertVerificationError:
        return False
    except Exception:
        return None


# ---------------------------------------------------------------- API clients

class ApiBase:
    """Everything above the transport. The real client and the selftest's
    in-memory controller both implement request()."""
    host = ''
    version = ''
    label = ''
    tenant = 'admin'

    def request(self, method, path, body=None, params=None, api_version=None, tenant=None):
        raise NotImplementedError

    def listing(self, objtype, params=None, tenant=None):
        q = {'page_size': '200', 'include_name': 'true'}
        q.update(params or {})
        path = '/api/%s?%s' % (objtype, urlencode(q))
        out, seen = [], set()
        while path:
            if path in seen:
                raise RuntimeError('repeated pagination link: ' + path)
            seen.add(path)
            d = self.request('GET', path, tenant=tenant)
            if d is None or not isinstance(d.get('results'), list):
                raise RuntimeError('unavailable or malformed collection: ' + objtype)
            out.extend(d['results'])
            nxt = d.get('next')
            if nxt:
                sp = urlsplit(nxt)
                qs = dict(parse_qsl(sp.query))
                qs.setdefault('include_name', 'true')
                path = sp.path + '?' + urlencode(qs)
            else:
                path = None
        return out

    def objects(self, objtype):
        return {o['name']: o for o in self.listing(objtype) if o.get('name')}

    def index(self, objtype):
        """name -> reference. Every reference carries its '#Name' fragment, so
        anything built from it can be read back by name."""
        out = {}
        for n, o in self.objects(objtype).items():
            u = o.get('url')
            if u:
                out[n] = u if '#' in u else '%s#%s' % (u, n)
        return out

    def find(self, objtype, name):
        for o in self.listing(objtype, {'name': name}):
            if o.get('name') == name:  # the name filter is not an exact match everywhere
                return o
        return None


class Client(ApiBase):
    def __init__(self, cfg, role, site=None):
        if requests is None:
            raise RuntimeError('the requests module is needed: pip install requests')
        self.role = role
        if role == 'source':
            hkey, ukey, pkey, env = ('avi_source_host', 'avi_source_user',
                                     'avi_source_password', 'AVI_SOURCE_PASSWORD')
        else:
            hkey, ukey, pkey = ['%s_%s' % (k, site) for k in
                                ('avi_target_host', 'avi_target_user', 'avi_target_password')]
            env = 'AVI_TARGET_PASSWORD_%s' % re.sub(r'[^A-Za-z0-9]', '_', str(site)).upper()
        host = cfg.get(hkey)
        if not host:
            raise ValueError('%s is not set in the config' % hkey)
        self.host = str(host).rstrip('/')
        u = urlparse(self.host)
        if u.scheme != 'https' or not u.netloc or u.path or u.username or u.query or u.fragment:
            raise ValueError('%s must be https://hostname with no credentials or path' % hkey)
        self.hostname = u.hostname
        self.port = u.port or 443
        self.label = site or role
        self.tenant = str(cfg.get('avi_tenant') or 'admin')
        user = cfg.get(ukey) or 'admin'
        pw = secret(cfg, pkey, env, '%s password for %s: ' % (user, u.netloc))
        verify = cfg.get('ca_bundle') or True
        if verify is not True and not os.path.exists(str(verify)):
            print('  ca_bundle %s does not exist; ignoring it' % verify)
            verify = True
        # verify is passed on every call rather than set on the session:
        # requests lets REQUESTS_CA_BUNDLE / CURL_CA_BUNDLE override a
        # session-level value, which would silently discard the pinned chain.
        self.session = requests.Session()
        self.verify = verify
        r, last = None, None
        for attempt in range(3):
            try:
                r = self.session.post(self.host + '/login', data={'username': user, 'password': pw},
                                      timeout=(10, 60), allow_redirects=False, verify=self.verify)
                break
            except requests.exceptions.SSLError as exc:
                last = exc
                if verify is not True:
                    # A CA the operator configured is not second-guessed by pinning.
                    raise RuntimeError('%s does not verify against ca_bundle %s; nothing was sent: %s'
                                       % (self.hostname, verify, str(exc)[:200]))
                if attempt >= 1:
                    raise RuntimeError('TLS verification failed for %s and pinning did not help: %s'
                                       % (self.hostname, str(exc)[:200]))
                bundle, fresh = pin_certificate(self.hostname, self.port)
                if not fresh and verifies(self.hostname, bundle, port=self.port) is False:
                    raise RuntimeError(certificate_changed(self.hostname, self.port, bundle))
                self.verify = bundle
            except requests.exceptions.RequestException as exc:
                last = exc
                if attempt >= 2:
                    raise RuntimeError('cannot reach %s: %s' % (self.host, str(exc)[:200]))
                time.sleep(2 * (attempt + 1))
        if r is None:
            raise RuntimeError('cannot reach %s: %s' % (self.host, last))
        if not 200 <= r.status_code < 300:
            hint = ' Check the password (%s).' % env if r.status_code in (401, 403) else ''
            raise RuntimeError('login failed on %s: HTTP %s.%s' % (self.host, r.status_code, hint))
        rv = self.session.get(self.host + '/api/cluster/version', timeout=(10, 60), verify=self.verify)
        if not 200 <= rv.status_code < 300 or not (rv.json() or {}).get('Version'):
            raise RuntimeError('cannot read the controller version from ' + self.host)
        self.version = rv.json()['Version']
        self.session.headers.update({'X-Avi-Version': self.version, 'Referer': self.host + '/',
                                     'X-Avi-Tenant': self.tenant})

    def request(self, method, path, body=None, params=None, api_version=None, tenant=None):
        if getattr(self, 'role', None) == 'source' and method != 'GET':
            raise RuntimeError('refusing %s %s: blue is only ever read' % (method, path.split('?')[0]))
        if not path.startswith('/api/') or '..' in path or '#' in path:
            raise ValueError('invalid API path: ' + path)
        h = {}
        if method != 'GET':
            token = next((ck.value for ck in reversed(list(self.session.cookies))
                          if ck.name == 'csrftoken'), None)
            if not token:
                raise RuntimeError('no CSRF token; the session is not established')
            h['X-CSRFToken'] = token
        if api_version:
            h['X-Avi-Version'] = api_version
        if tenant:
            h['X-Avi-Tenant'] = tenant
        r, last = None, None
        for attempt in range(3):
            try:
                r = self.session.request(method, self.host + path, json=body, params=params,
                                         headers=h, timeout=(10, 120), allow_redirects=False,
                                         verify=self.verify)
                break
            except requests.exceptions.RequestException as exc:
                last = exc
                if method != 'GET' or attempt >= 2:
                    raise RuntimeError('%s %s on %s: %s' % (method, path.split('?')[0],
                                                            self.label, str(exc)[:200]))
                time.sleep(2 * (attempt + 1))
        if r is None:
            raise RuntimeError('%s %s on %s: %s' % (method, path, self.label, last))
        if r.status_code == 404 and method == 'GET':
            return None
        if not 200 <= r.status_code < 300:
            raise RuntimeError('%s %s on %s: HTTP %s; %s' % (method, path.split('?')[0], self.label,
                                                           r.status_code, r.text[:600]))
        return r.json() if r.content else {}


def _real_client(cfg, role, site):
    return Client(cfg, role, site)


CLIENT_FACTORY = _real_client
_POOL = {}


def connect(cfg, role, site=None):
    """One login per controller per run."""
    key = (role, site)
    if key not in _POOL:
        _POOL[key] = CLIENT_FACTORY(cfg, role, site)
    return _POOL[key]


# ---------------------------------------------------------------- export

def exclusion_reason(objtype, o, patterns):
    name = str(o.get('name', ''))
    if name.startswith('System-'):
        return 'system'
    if objtype == 'sslkeyandcertificate' and o.get('type') == 'SSL_CERTIFICATE_TYPE_SYSTEM':
        return 'controller certificate (type SYSTEM)'
    if objtype == 'virtualservice' and o.get('type') == 'VS_TYPE_DNS':
        return 'DNS virtual service: green runs its own GSLB DNS services'
    cb = o.get('created_by')
    if cb and ORCHESTRATED.search(str(cb)):
        return 'created by %s: recreate it from that orchestrator' % cb
    for p in patterns:
        if fnmatch.fnmatchcase('%s/%s' % (objtype, name), p) or fnmatch.fnmatchcase(name, p):
            return 'excluded by avi_exclude (%s)' % p
    return None


def cert_facts(o):
    c = o.get('certificate') or {}
    subj = c.get('subject') or {}
    names = []
    if subj.get('common_name'):
        names.append(str(subj['common_name']).lower())
    for s in c.get('subject_alt_names') or []:
        s = str(s).lower()
        if s not in names:
            names.append(s)
    return {'names': names, 'not_after': c.get('not_after'),
            'signature_algorithm': c.get('signature_algorithm'),
            'expiry_status': c.get('expiry_status'), 'type': o.get('type')}


# A Lua string a DataScript compares with (host == "a.b", "a.b" ~= host) or
# keys a table with (["a.b"] = ...): a name it answers for. A string it only
# passes on (a redirect, a header it sets) is not matched.
_SCRIPT_NAME = re.compile(r'''(?:==|~=)\s*(["'])([^"'\\\s]+)\1|(["'])([^"'\\\s]+)\3\s*(?:==|~=)'''
                          r'''|\[\s*(["'])([^"'\\\s]+)\5\s*\]\s*=(?!=)''')


def policy_hosts(o, objects):
    """The Host header values a policy's rules match on (an HTTP policy set, or
    a WAF policy's allowlist), directly or through a string group: the names
    requests to this service carry. Where a rule sends a request (a redirect, a
    rewritten Host) is another service's name, so it is not read."""
    out = []

    def values(m):
        vals = list(m.get('value') or [])
        for ref in m.get('string_group_refs') or []:
            sg = objects.get('stringgroup/%s' % ref_name(ref)) or {}
            vals.extend(kv.get('key') for kv in sg.get('kv') or [])
        return [str(v).lower() for v in vals if v]

    def walk(x):
        if isinstance(x, dict):
            for k, v in x.items():
                if k == 'match' and isinstance(v, dict):
                    if isinstance(v.get('host_hdr'), dict):
                        out.extend(values(v['host_hdr']))
                    for h in v.get('hdrs') or []:
                        if str(h.get('hdr') or '').lower() == 'host':
                            out.extend(values(h))
                else:
                    walk(v)
        elif isinstance(x, list):
            for v in x:
                walk(v)
    walk(o)
    return out


def script_hosts(o):
    """The names a DataScript set compares a request with; see _SCRIPT_NAME."""
    out = []
    for d in o.get('datascript') or []:
        for m in _SCRIPT_NAME.finditer(str(d.get('script') or '')):
            out.append((m.group(2) or m.group(4) or m.group(6)).lower())
    return out


def vs_hosts(o, objects):
    """Names a virtual service's HTTP policies, WAF allowlist and DataScripts
    match requests on. Only names in gslb_zones are ever asked about, and only
    what DNS points at a VIP is taken as that VIP's."""
    out = []
    for p in o.get('http_policies') or []:
        out.extend(policy_hosts(objects.get('httppolicyset/%s' % ref_name(p.get('http_policy_set_ref'))) or {},
                                objects))
    if o.get('waf_policy_ref'):
        out.extend(policy_hosts(objects.get('wafpolicy/%s' % ref_name(o['waf_policy_ref'])) or {}, objects))
    for s in o.get('vs_datascripts') or []:
        out.extend(script_hosts(objects.get('vsdatascriptset/%s' % ref_name(s.get('vs_datascript_set_ref'))) or {}))
    return sorted(set(out))


def build_inventory(objects):
    vsvips, vs, certs = {}, {}, {}
    for key, o in objects.items():
        t, n = split_key(key)
        if t == 'vsvip':
            ips = [v['ip_address']['addr'] for v in o.get('vip') or []
                   if isinstance(v.get('ip_address'), dict) and v['ip_address'].get('addr')]
            vsvips[n] = {'ips': ips, 'vs': [],
                         'fqdns': [str(d['fqdn']).lower() for d in o.get('dns_info') or [] if d.get('fqdn')]}
        elif t == 'sslkeyandcertificate':
            certs[n] = cert_facts(o)
    for key, o in objects.items():
        t, n = split_key(key)
        if t != 'virtualservice':
            continue
        services = o.get('services') or []
        ports = sorted(set(int(s['port']) for s in services if s.get('port')))
        vs[n] = {'vsvip': ref_name(o.get('vsvip_ref')), 'parent': ref_name(o.get('vh_parent_vs_ref')),
                 'children': [], 'ports': ports,
                 'ssl': any(s.get('enable_ssl') for s in services),
                 'type': o.get('type') or 'VS_TYPE_NORMAL',
                 'enabled': o.get('enabled', True) is not False,
                 'traffic': o.get('traffic_enabled', True) is not False,
                 'se_group': ref_name(o.get('se_group_ref')),
                 'certs': [ref_name(x) for x in o.get('ssl_key_and_certificate_refs') or []],
                 # SNI children by domain name; enhanced virtual hosting children by host
                 'domains': [str(d).lower() for d in o.get('vh_domain_name') or []]
                 + [str(m['host']).lower() for m in o.get('vh_matches') or [] if m.get('host')],
                 'hosts': vs_hosts(o, objects)}
    for n, v in vs.items():
        if v['vsvip'] in vsvips:
            vsvips[v['vsvip']]['vs'].append(n)
        if v['parent'] in vs:
            vs[v['parent']]['children'].append(n)
    for v in vsvips.values():
        v['vs'].sort()
    for v in vs.values():
        v['children'].sort()
    return {'vsvip': vsvips, 'vs': vs, 'certs': certs}


def load_bundle(path):
    """A saved export of blue. What it says of each VIP and service is worked
    out again from its objects, so an export an earlier release saved reads as
    this one would have written it."""
    b = read(path)
    b['inventory'] = build_inventory(b['objects'])
    return b


def export(cfg, args):
    bundle, path, csv_path = read_blue(cfg, getattr(args, 'out', None))
    report_export(bundle, path, csv_path)
    return True


def read_blue(cfg, out=None):
    """Everything portable on blue, as a bundle; saved for the record."""
    c = connect(cfg, 'source')
    types = [str(t) for t in as_list(cfg.get('avi_types'))] or list(PORTABLE)
    unknown = [t for t in types if t not in PORTABLE]
    if unknown:
        raise ValueError('not portable by this tool: ' + ', '.join(unknown))
    patterns = [str(p) for p in as_list(cfg.get('avi_exclude'))]
    objects, excluded, absent, creators = {}, {}, [], {}
    for t in types:
        try:
            found = c.listing(t)
        except RuntimeError:
            absent.append(t)  # the source predates the type, or does not license it
            continue
        for o in found:
            if not o.get('name'):
                continue
            if o.get('created_by'):
                creators[o['created_by']] = creators.get(o['created_by'], 0) + 1
            why = exclusion_reason(t, o, patterns)
            key = '%s/%s' % (t, o['name'])
            if why == 'system':
                continue
            if t == 'virtualservice':
                o.pop('tls_ticket_key', None)  # key material: never on disk, never to green
            if why:
                excluded[key] = {'reason': why, 'refs': sorted(r['raw'] for r in iter_refs(o))}
                continue
            objects[key] = o

    tenants = {}
    try:
        for tn in c.listing('tenant'):
            n = tn.get('name')
            if n and n != c.tenant:
                try:
                    found = [v for v in c.listing('virtualservice', tenant=n)
                             if ref_name(v.get('tenant_ref')) in (None, n)]
                except RuntimeError:
                    found = []
                tenants[n] = len(found)
    except RuntimeError:
        pass

    segs = {}
    try:
        for g in c.listing('serviceenginegroup'):
            segs[g['name']] = {k: g.get(k) for k in ('max_se', 'max_vs_per_se', 'vcpus_per_se',
                                                    'memory_per_se', 'ha_mode', 'buffer_se')}
            segs[g['name']]['engines'] = 0
        for se in c.listing('serviceengine'):
            n = ref_name(se.get('se_group_ref'))
            if n in segs:
                segs[n]['engines'] += 1
    except RuntimeError:
        pass

    gslb = {'configured': None}
    try:
        gl = c.listing('gslb')
        gslb = {'configured': bool(gl),
                'subdomains': [d.get('domain_name') for g in gl for d in g.get('dns_configs') or []],
                'services': [{'name': s.get('name'), 'domain_names': s.get('domain_names') or []}
                             for s in (c.listing('gslbservice') if gl else [])]}
    except RuntimeError:
        pass

    external = {}
    for o in objects.values():
        for r in iter_refs(clean(o)):
            key = '%s/%s' % (r['type'], r['name'])
            if key in objects:
                continue
            if r['type'] in ENVIRONMENT:
                if r['name']:
                    external[key] = 'environment'
            elif r['name'] is None:
                external[r['raw']] = 'reference carries no name'
            elif r['type'] in SYSTEM_TYPES or str(r['name']).startswith('System-'):
                external[key] = 'system object, resolved by name on the target'
            elif r['type'] in PORTABLE:
                external[key] = 'referenced but not exported'
            else:
                external[key] = 'unsupported type'

    inv = build_inventory(objects)
    ref_hosts = sorted(set(r['host'] for o in objects.values() for r in iter_refs(o) if r['host'])
                       | {urlparse(c.host).netloc})
    bundle = {'format': 2, 'tool': VERSION, 'site': cfg.get('site_name'), 'source': c.host,
              'source_version': c.version, 'source_cluster': cluster_uuid(c), 'exported_at': now(), 'types': types,
              'ref_hosts': ref_hosts,
              'absent_on_source': absent, 'objects': objects, 'excluded': excluded,
              'external': external, 'inventory': inv, 'tenants': tenants,
              'se_groups': segs, 'gslb': gslb, 'creators': creators}
    path = out or artefact(cfg, 'avi-export')
    save(path, bundle)
    csv_path = write_vip_inventory(cfg, inv)
    return bundle, path, csv_path


def write_vip_inventory(cfg, inv):
    path = artefact(cfg, 'blue-vips', 'csv')
    with open(path, 'w', newline='') as fh:
        w = csv.writer(fh)
        w.writerow(['vsvip', 'ips', 'virtual_services', 'ports', 'se_group', 'blue_state',
                    'names_seen_in_certificates', 'dns_info', 'names_in_policies'])
        for name, v in sorted(inv['vsvip'].items()):
            members = v['vs']
            ports = sorted(set(p for m in members for p in inv['vs'][m]['ports']))
            segs = sorted(set(str(inv['vs'][m]['se_group']) for m in members))
            state = 'enabled' if any(inv['vs'][m]['enabled'] for m in members) else 'disabled'
            names, hosts = [], []
            for m in members + [c for m in members for c in inv['vs'][m]['children']]:
                for cn in inv['vs'].get(m, {}).get('certs', []):
                    names.extend(inv['certs'].get(cn, {}).get('names', []))
                names.extend(inv['vs'].get(m, {}).get('domains', []))
                hosts.extend(inv['vs'].get(m, {}).get('hosts') or [])
            w.writerow([name, ' '.join(v['ips']), ' '.join(members), ' '.join(str(p) for p in ports),
                        ' '.join(segs), state, ' '.join(sorted(set(names))), ' '.join(v['fqdns']),
                        ' '.join(sorted(set(hosts)))])
    return path


def report_export(b, path, csv_path):
    objs = b['objects']
    counts = {}
    for k in objs:
        t = k.split('/', 1)[0]
        counts[t] = counts.get(t, 0) + 1
    banner('EXPORT  %s  (%s)' % (b['source'], b['source_version']))
    order = ['virtualservice', 'vsvip', 'pool', 'poolgroup', 'sslkeyandcertificate', 'healthmonitor']
    head = ['%d %s' % (counts[t], t) for t in order if counts.get(t)]
    rest = sum(v for t, v in counts.items() if t not in order)
    print('  %d objects: %s%s' % (len(objs), ', '.join(head), ', %d others' % rest if rest else ''))
    if b['excluded']:
        why = {}
        for e in b['excluded'].values():
            why[e['reason']] = why.get(e['reason'], 0) + 1
        print('  left out:')
        for r, n in sorted(why.items()):
            print('      %3d  %s' % (n, r))
    if b['absent_on_source']:
        print('  types the source does not serve: %s' % fmt_list(b['absent_on_source']))
    busy = {t: n for t, n in b['tenants'].items() if n}
    if busy:
        print('  WARNING: other tenants hold virtual services this run does not export: %s'
              % ', '.join('%s (%d)' % x for x in sorted(busy.items())))
    else:
        print('  tenants: admin only')
    g = b['gslb']
    if g.get('configured'):
        print('  blue runs GSLB: subdomains %s; %d GSLB services'
              % (fmt_list(g['subdomains']) or '-', len(g['services'])))
    elif g.get('configured') is False:
        print('  blue does not run GSLB')
    for n, s in sorted(b['se_groups'].items()):
        print('  SE group %-24s %2s engines now, max_se %s, %s vCPU each, %s VS per engine'
              % (n, s.get('engines'), s.get('max_se'), s.get('vcpus_per_se'), s.get('max_vs_per_se')))
    inv = b['inventory']
    keyed = [n for n, c in inv['certs'].items() if c.get('type') != 'SSL_CERTIFICATE_TYPE_CA']
    print('  certificates: %d with private keys (moved at apply time), %d CA'
          % (len(keyed), len(inv['certs']) - len(keyed)))
    soon = [n for n, c in inv['certs'].items() if expires_within(c.get('not_after'), 30)]
    if soon:
        print('      %d expire within 30 days or already have: %s' % (len(soon), fmt_list(sorted(soon), 6)))
    ips = [ip for v in inv['vsvip'].values() for ip in v['ips']]
    print('  VIPs: %d VsVips holding %d addresses -> %s' % (len(inv['vsvip']), len(ips), csv_path))
    odd = [k for k, v in b['external'].items() if v in ('unsupported type', 'reference carries no name')]
    if odd:
        print('  %d references the plan will not be able to resolve: %s' % (len(odd), fmt_list(odd, 5)))
    print('')
    print('  Export: %s' % path)
    print('  Next:   converge --config <file>')


def expires_within(not_after, days):
    if not not_after:
        return False
    s = str(not_after).replace('Z', '+00:00')
    for fmt in (None, '%Y-%m-%d %H:%M:%S'):
        try:
            dt = datetime.fromisoformat(s) if fmt is None else datetime.strptime(s[:19], fmt)
            if dt.tzinfo is None:
                dt = dt.replace(tzinfo=timezone.utc)
            return (dt - datetime.now(timezone.utc)).days < days
        except ValueError:
            continue
    return False


# ---------------------------------------------------------------- scope

def expand_vs(inv, names):
    """Virtual services that must move together: everything on the same VIP,
    and SNI parents with their children."""
    sel = set(n for n in names if n in inv['vs'])
    changed = True
    while changed:
        changed = False
        for n in list(sel):
            v = inv['vs'][n]
            group = list(inv['vsvip'].get(v['vsvip'], {}).get('vs', [])) if v['vsvip'] else []
            group += v['children'] + ([v['parent']] if v['parent'] in inv['vs'] else [])
            for m in group:
                if m not in sel:
                    sel.add(m)
                    changed = True
    return sel


def closure(objects, roots):
    seen, stack = set(), list(roots)
    while stack:
        k = stack.pop()
        if k in seen or k not in objects:
            continue
        seen.add(k)
        for r in iter_refs(objects[k]):
            kk = '%s/%s' % (r['type'], r['name'])
            if kk in objects and kk not in seen:
                stack.append(kk)
    return seen


def select_scope(cfg, args, bundle):
    objects, inv = bundle['objects'], bundle['inventory']
    chosen, note = None, 'every virtual service'
    if getattr(args, 'vs', None):
        chosen = set()
        for pat in as_list(args.vs):
            hit = [n for n in inv['vs'] if fnmatch.fnmatchcase(n, pat)]
            if not hit:
                raise ValueError('--vs %s matches no exported virtual service' % pat)
            chosen.update(hit)
        note = '--vs %s' % args.vs
    names = set(inv['vs']) if chosen is None else chosen
    expanded = expand_vs(inv, names)
    roots = set('virtualservice/%s' % n for n in expanded)
    scope = closure(objects, roots)
    orphans, only_excluded = set(), set()
    if chosen is None:
        ex_roots = set()
        for e in bundle.get('excluded', {}).values():
            for raw in e.get('refs', []):
                r = parse_ref(raw)
                if r and r['name']:
                    ex_roots.add('%s/%s' % (r['type'], r['name']))
        only_excluded = closure(objects, ex_roots) - scope
        for k in objects:
            if k in scope or k in only_excluded:
                continue
            if k.startswith('vsvip/'):
                continue  # an unused VIP would take an address for nothing
            orphans.add(k)
        scope |= orphans
    return scope, {'selection': note, 'virtual_services': len(expanded),
                   'pulled_in': sorted(expanded - names), 'objects': len(scope),
                   'orphans': len(orphans), 'left_with_excluded': sorted(only_excluded)}


# ---------------------------------------------------------------- restaging

SIMPLE_PATH = re.compile(r'^[a-z0-9_]+(\.[a-z0-9_]+)*$')
# What the API returns in place of a value it will not hand back (a monitor's
# username as well as its password). Posted as it is, a target refuses it.
MASKED = '<sensitive>'
_SECRETS = {}  # (type, name, path) -> value: for this run only, never written anywhere
_NO_SECRET = {}  # (type, name, path) -> why none was given: asked once per run, not at every site


def del_path(d, path):
    parts = path.split('.')
    for p in parts[:-1]:
        d = d.get(p) if isinstance(d, dict) else None
    if isinstance(d, dict):
        d.pop(parts[-1], None)


def set_path(d, path, value):
    parts = path.split('.')
    for p in parts[:-1]:
        d = d.setdefault(p, {})
    d[parts[-1]] = value


def secret_env(objtype, name, path):
    return 'AVI_SECRET_' + re.sub(r'[^A-Za-z0-9]', '_', '%s_%s_%s' % (objtype, name, path)).upper()


class NoSecret(RuntimeError):
    """No value for a secret: that object is skipped, not the run."""


def secret_value(objtype, name, path):
    """A value blue does not hand back, for an object listed in avi_secrets:
    from AVI_SECRET_<TYPE>_<NAME>_<FIELD>, else typed at a prompt, once for
    every site. A password is typed unseen and twice; a username is shown.
    Held in memory for this run only. NoSecret when none is given."""
    k = (objtype, name, path)
    if k in _NO_SECRET:
        raise NoSecret(_NO_SECRET[k])
    if k not in _SECRETS:
        env = secret_env(objtype, name, path)
        v = os.environ.get(env)
        if not v and not (sys.stdin and sys.stdin.isatty()):
            _NO_SECRET[k] = 'needs its %s: set %s, or run at a terminal' % (path, env)
            raise NoSecret(_NO_SECRET[k])
        hidden = bool(SECRET_KEY.search(path.split('.')[-1]))
        prompt = '  %s of %s %s (used at every site; Enter skips it): ' % (path, objtype, name)
        tries = 0
        while not v and tries < 3:
            tries += 1
            try:
                if not hidden:
                    v = input(prompt).strip()
                    break
                v = getpass.getpass(prompt)
                if v and getpass.getpass('  again: ') != v:
                    print('  they differ')
                    v = ''
                    continue
            except EOFError:
                v = ''
            break
        if not v:
            _NO_SECRET[k] = 'no %s given (set %s, or type it when asked)' % (path, env)
            raise NoSecret(_NO_SECRET[k])
        _SECRETS[k] = v
    return _SECRETS[k]


def gather_secrets(plans):
    """Every value a commit will need, asked before its first write, so nobody
    is asked half way through, and a run left alone never waits on a prompt
    in the middle. Returns (type, name, path) -> why, for those not given."""
    missing = {}
    for plan in plans:
        for op in plan.get('ops') or []:
            for pth in op.get('secrets') or []:
                k = (op['type'], op['name'], pth)
                if k in missing or k in _SECRETS:
                    continue
                try:
                    secret_value(*k)
                except NoSecret as exc:
                    missing[k] = str(exc)
    return missing


def secrets_in(objtype, raw):
    """Paths of secrets the API does not hand back in usable form."""
    found = []

    def walk(v, path):
        if isinstance(v, dict):
            if v.get('is_sensitive') is True:
                found.append(path or '(root)')
            for k, x in v.items():
                p = '%s.%s' % (path, k) if path else k
                if (SECRET_KEY.search(k) and x not in (None, '', [], {})) or x == MASKED:
                    found.append(p)
                walk(x, p)
        elif isinstance(v, list):
            for i, x in enumerate(v):
                if x == MASKED:
                    found.append('%s[%d]' % (path, i))
                walk(x, '%s[%d]' % (path, i))
    walk(raw, '')
    if objtype == 'sslkeyandcertificate':
        found = [f for f in found if f not in ('key', 'key_passphrase')]
    if objtype == 'healthmonitor':
        if raw.get('authentication'):
            found.append('authentication.password')
        if raw.get('radius_monitor'):
            found.append('radius_monitor.password/shared_secret')
    if objtype == 'authprofile' and raw.get('type') in ('AUTH_PROFILE_LDAP', 'AUTH_PROFILE_TACACS_PLUS'):
        found.append('bind password / shared secret')
    if objtype == 'virtualservice' and raw.get('oauth_vs_config'):
        found.append('oauth_vs_config client secret')
    # A username before its password, as anyone would be asked for them.
    return sorted(set(found), key=lambda p: (bool(SECRET_KEY.search(p.split('.')[-1])), p))


# ---------------------------------------------------------------- product changes between releases

def release(v):
    """'31.1.2' -> (31, 1, 2); what cannot be read sorts first."""
    return tuple(int(x) for x in re.findall(r'\d+', str(v or ''))[:3]) or (0,)


def reach(d, path):
    """(container, key) for every place a path reaches in d: fields joined by
    dots, a list stepped through wherever one is met, '**' for any depth."""
    parts = [p for p in path.replace('[]', '').split('.') if p]

    def go(v, ps):
        if isinstance(v, list):
            for x in v:
                for hit in go(x, ps):
                    yield hit
            return
        if not isinstance(v, dict) or not ps:
            return
        head, rest = ps[0], ps[1:]
        if head == '**':
            for hit in go(v, rest):
                yield hit
            for x in v.values():
                for hit in go(x, ps):
                    yield hit
        elif head in v:
            if rest:
                for hit in go(v[head], rest):
                    yield hit
            else:
                yield v, head
    return list(go(d, parts))


# What changed between the release blue runs and the one green runs, in the
# objects this tool writes, read from the two releases' object models (31.1.2
# and 32.1.3: every field one has and the other does not, and what took its
# place). A rule applies when blue is older than its release and green is at
# it or newer, and every one used is listed in the plan with what it touched.
#   refused  the target refuses the field even in blue's release: it goes.
#   drop     gone, with nothing in its place: it goes.
#   convert  moved to a successor: converted when writing in green's release
#            (avi_write_version: target); left in blue's form when writing in
#            blue's (the default), which the target converts itself, as the first green site
#            converted every pool.
PRODUCT_CHANGES = [
    {'release': '32.1', 'type': 'virtualservice', 'do': 'refused', 'paths': ['content_rewrite.rewritable_content_ref'],
     'note': 'content_rewrite.rewritable_content_ref is gone, and the target refuses it'},
    {'release': '32.1', 'type': 'healthmonitor', 'do': 'refused', 'paths': ['monitor_port'],
     'when': lambda b: b.get('type') == 'HEALTH_MONITOR_PING',
     'note': 'a PING monitor has no port, and the target refuses one'},
    {'release': '32.1', 'type': 'pool', 'do': 'convert', 'paths': ['graceful_disable_timeout'],
     'into': 'graceful_disable_timeout_sec', 'scale': 60,
     'note': 'graceful_disable_timeout (minutes) is graceful_disable_timeout_sec (seconds)'},
    {'release': '32.1', 'type': 'wafpolicy', 'do': 'convert', 'paths': ['updated_crs_rules_in_detection_mode'],
     'into': 'use_evaluation_mode_on_crs_update',
     'note': 'updated_crs_rules_in_detection_mode is use_evaluation_mode_on_crs_update (new CRS rules go into '
             'evaluation mode, not detection)'},
    {'release': '32.1', 'type': 'wafpolicy', 'do': 'drop',
     'paths': ['enable_app_learning', 'enable_auto_rule_updates', 'enable_regex_learning', 'learning_params',
               'min_confidence', 'confidence_override'],
     'note': 'application learning is gone; its settings are not carried'},
    {'release': '32.1', 'type': 'wafpolicy', 'do': 'drop',
     'paths': ['application_signatures.resolved_rules', 'required_data_files'],
     'note': 'computed by the target'},
    {'release': '32.1', 'type': '*', 'do': 'drop', 'paths': ['**.file.file_length'],
     'note': 'a local file\'s length is computed by the target'},
    {'release': '32.1', 'type': 'pool', 'do': 'drop',
     'paths': ['resolve_pool_by_dns', 'analytics_policy.enable_realtime_metrics', 'servers.preference_order',
               'servers.srv_rdata'],
     'note': 'gone, with nothing in its place'},
    {'release': '32.1', 'type': 'authprofile', 'do': 'drop',
     'paths': ['oauth_profile.instance_id', 'oauth_profile.org_id', 'oauth_profile.service_id',
               'oauth_profile.service_name'],
     'note': 'an OAuth profile\'s CSP settings are gone'},
]


def product_changes(objtype, body, ctx):
    """Blue's release to green's, for one body. Returns ([(rule, fields)],
    warnings about this object)."""
    src, tgt = release(ctx.get('source_version')), release(ctx.get('target_version'))
    native = bool(ctx.get('write_target'))
    applied, warns = [], []
    for r in PRODUCT_CHANGES:
        if r['type'] not in ('*', objtype) or not (src < release(r['release']) <= tgt):
            continue
        if r.get('when') and not r['when'](body):
            continue
        fields = []
        for path in r['paths']:
            places = reach(body, path)
            if not places:
                continue
            fields.append(path.replace('**.', ''))
            if r['do'] == 'convert' and not native:
                continue  # blue's form, in blue's release: the target converts it
            for c, k in places:
                v = c.pop(k)
                if r['do'] == 'convert' and r['into'] not in c:
                    scaled = r.get('scale') and isinstance(v, int) and not isinstance(v, bool) and v > 0
                    c[r['into']] = v * r['scale'] if scaled else v
        if fields:
            applied.append((r, fields))
    cr = body.get('content_rewrite') if objtype == 'virtualservice' else None
    if isinstance(cr, dict) and any('rewritable_content_ref' in f for r, fs in applied for f in fs):
        if not cr.get('rsp_rewrite_rules') and not cr.get('req_rewrite_rules'):
            body.pop('content_rewrite')  # with no rules left, it rewrites nothing
        else:
            warns.append('its content rewrite rules are kept without rewritable_content_ref: check which content '
                         'types they apply to')
    return applied, warns


def product_lines(ctx, native):
    """The plan's lines for the product changes one site's objects needed."""
    out = []
    for (t, note, do), objs in sorted((ctx.get('product') or {}).items(), key=lambda x: (x[0][0], x[0][1])):
        fields = sorted(set(f for fs in objs.values() for f in fs))
        how = ('converted' if native else 'left in blue\'s form, which the target converts itself') \
            if do == 'convert' else 'removed'
        out.append('product change %s -> %s, %s: %s. %s: %s. %d: %s'
                   % (ctx.get('source_version'), ctx.get('target_version'), t, note, how.capitalize(),
                      ', '.join(fields), len(objs), fmt_list(sorted(objs), 4)))
    return out


def restage(objtype, name, raw, body, ctx, drop_legacy_tls):
    """Rewrite what belongs to blue's environment. Runs before references are
    resolved, so nothing pointing at blue's networks survives to block the plan.
    Returns (blocks, warnings, key_uuid)."""
    blocks, warns, key_uuid = [], [], None
    label = '%s/%s' % (objtype, name)

    applied, pw = product_changes(objtype, body, ctx)
    warns.extend('%s: %s' % (label, w) for w in pw)
    for rule, fields in applied:
        ctx.setdefault('product', {}).setdefault((objtype, rule['note'], rule['do']), {}).setdefault(
            name, set()).update(fields)

    if objtype == 'vsvip':
        vips = body.get('vip') or []
        if not vips:
            blocks.append('has no VIP entries')
        for vip in vips:
            if vip.get('auto_allocate_ip_type') in ('V6_ONLY', 'V4_V6') or vip.get('ip6_address'):
                warns.append('%s: IPv6 on blue; green allocates IPv4 only' % label)
            for k in VIP_STRIP:
                vip.pop(k, None)
            vip['auto_allocate_ip'] = True
            vip['auto_allocate_ip_type'] = 'V4_ONLY'
            vip['ipam_network_subnet'] = {'network_ref': ctx['urls']['network'],
                                          'subnet': prefix(ctx['vip_subnet'])}
            vip.setdefault('enabled', True)
        if not ctx.get('keep_dns_info', True):
            body.pop('dns_info', None)
        body['tier1_lr'] = ctx['tier1']
        body.setdefault('cloud_ref', ctx['urls']['cloud'])
        body.setdefault('vrf_context_ref', ctx['urls']['vrfcontext'])

    elif objtype == 'pool':
        if raw.get('nsx_securitygroup'):
            blocks.append('takes its members from NSX security groups (%s); confirm the groups '
                          'resolve on the site\'s Local Manager, then create the pool by hand'
                          % fmt_list(raw['nsx_securitygroup'], 3))
        if raw.get('placement_networks'):
            warns.append('%s: placement networks dropped; engines reach servers through the '
                         'Tier-1 on NSX clouds' % label)
        if raw.get('external_autoscale_groups') or raw.get('autoscale_networks'):
            warns.append('%s: autoscale groups do not carry over; review membership' % label)
        for s in body.get('servers') or []:
            for k in SERVER_STRIP:
                s.pop(k, None)
        if 'tier1_lr' in body or raw.get('tier1_lr'):
            body['tier1_lr'] = ctx['tier1']
        body.setdefault('cloud_ref', ctx['urls']['cloud'])
        body.setdefault('vrf_ref', ctx['urls']['vrfcontext'])

    elif objtype == 'poolgroup':
        body.setdefault('cloud_ref', ctx['urls']['cloud'])

    elif objtype == 'virtualservice':
        if raw.get('snat_ip') or raw.get('snat_ip6'):
            blocks.append('uses fixed SNAT addresses (%s) from blue\'s range; choose green '
                          'addresses and create it by hand'
                          % fmt_list([a.get('addr') for a in raw.get('snat_ip') or []], 3))
        if raw.get('nsx_securitygroup'):
            warns.append('%s: nsx_securitygroup dropped; 32.1 no longer has it' % label)
        if raw.get('use_vip_as_snat'):
            warns.append('%s: uses its VIP as the SNAT source; servers will see the new green VIP, '
                         'not an engine address' % label)
        body['enabled'] = False
        body['traffic_enabled'] = False
        body.setdefault('cloud_ref', ctx['urls']['cloud'])
        body.setdefault('vrf_context_ref', ctx['urls']['vrfcontext'])
        if raw.get('type') != 'VS_TYPE_VH_CHILD':
            body.setdefault('se_group_ref', ctx['urls']['serviceenginegroup'])

    elif objtype == 'sslkeyandcertificate':
        cert = raw.get('certificate') or {}
        if raw.get('hardwaresecuritymodulegroup_ref') or raw.get('enckey_base64') or raw.get('enckey_name'):
            blocks.append('its key is held in an HSM; the key cannot leave it')
        pem = cert.get('certificate')
        if not pem:
            blocks.append('holds no issued certificate (status %s)' % raw.get('status', '?'))
        facts = cert_facts(raw)
        if expires_within(facts['not_after'], 0):
            warns.append('%s: EXPIRED %s' % (label, facts['not_after']))
        elif expires_within(facts['not_after'], 30):
            warns.append('%s: expires %s' % (label, facts['not_after']))
        if facts['signature_algorithm'] and WEAK_SIG.search(str(facts['signature_algorithm'])):
            warns.append('%s: signed with %s' % (label, facts['signature_algorithm']))
        if any(ord(ch) > 127 for s in facts['names'] for ch in s):
            warns.append('%s: non-ASCII name in the SAN; 31.2.1+ enforces RFC 5280, use Punycode'
                         % label)
        body['certificate'] = {'certificate': pem}
        if raw.get('type') != 'SSL_CERTIFICATE_TYPE_CA':
            key_uuid = raw.get('uuid')

    elif objtype == 'sslprofile':
        ciphers = str(body.get('accepted_ciphers') or '')
        enums = list(body.get('cipher_enums') or [])
        versions = [v.get('type') if isinstance(v, dict) else v for v in body.get('accepted_versions') or []]
        legacy = sorted(set([c for c in ciphers.split(':') if LEGACY_TLS.search(c)] +
                            [e for e in enums if LEGACY_TLS.search(str(e))] +
                            [v for v in versions if v and LEGACY_TLS.search(str(v))]))
        if legacy and not drop_legacy_tls:
            blocks.append('carries %s, not supported from 31.2.1. Set avi_drop_legacy_tls: true '
                          'to remove them, or fix the profile on blue first' % ', '.join(legacy))
        elif legacy:
            if ciphers:
                body['accepted_ciphers'] = ':'.join(c for c in ciphers.split(':') if not LEGACY_TLS.search(c))
            if enums:
                body['cipher_enums'] = [e for e in enums if not LEGACY_TLS.search(str(e))]
            if body.get('accepted_versions'):
                body['accepted_versions'] = [v for v in body['accepted_versions']
                                             if not LEGACY_TLS.search(str(v.get('type') if isinstance(v, dict) else v))]
            if not (body.get('accepted_ciphers') or body.get('cipher_enums')) or not body.get('accepted_versions', [1]):
                blocks.append('nothing left after removing %s' % ', '.join(legacy))
            else:
                warns.append('%s: removed %s' % (label, ', '.join(legacy)))
        weak = sorted(set([c for c in ciphers.split(':') if c and WEAK_CIPHER.search(c) and not LEGACY_TLS.search(c)] +
                          [str(e) for e in enums if WEAK_CIPHER.search(str(e)) and not LEGACY_TLS.search(str(e))] +
                          [str(v) for v in versions if v in WEAK_VERSIONS]))
        if weak:
            warns.append('%s: weak ciphers or protocols: %s' % (label, fmt_list(weak, 6)))

    elif objtype == 'healthmonitor':
        code = str((raw.get('external_monitor') or {}).get('command_code') or '')
        hit = sorted(set(HM_PACKAGES.findall(code)))
        if hit:
            warns.append('%s: script uses %s, replaced in 31.2.1+ by mssql-python / oracledb'
                         % (label, ', '.join(hit)))
    return blocks, warns, key_uuid


# ---------------------------------------------------------------- plan: desired state against one site

def site_context(cfg, site, tgt, tindex):
    sc = site_conf(cfg, site)
    blocks, notes = [], []
    urls = {}
    wanted = (('cloud', 'avi_cloud', sc['cloud']), ('vrfcontext', 'avi_vrf', sc['vrf']),
              ('serviceenginegroup', 'avi_se_group', sc['se_group']),
              ('network', 'avi_vip_network', sc['vip_network']))
    for t, key, name in wanted:
        if not name:
            blocks.append('%s_%s is not set in the config' % (key, site))
            continue
        url = tindex.get(t, {}).get(name)
        if not url:
            near = close_names(name, tindex.get(t, {}))
            blocks.append('%s "%s" does not exist on %s%s' % (t, name, site,
                          ' (close: %s)' % ', '.join(near) if near else ''))
        urls[t] = url
    if sc['se_group'] == 'Default-Group' and not sc['allow_default_group']:
        blocks.append('avi_se_group_%s is Default-Group, which often carries a Supervisor or other '
                      'platform services; use an application group, or set avi_allow_default_group_%s: true'
                      % (site, site))
    try:
        if sc['vip_subnet']:
            prefix(sc['vip_subnet'])
        else:
            blocks.append('avi_vip_subnet_%s is not set in the config' % site)
    except ValueError:
        blocks.append('avi_vip_subnet_%s is not a CIDR: %s' % (site, sc['vip_subnet']))

    derived, seen_on = set(), []
    try:
        for vv in tgt.listing('vsvip'):
            if ref_name(vv.get('vrf_context_ref')) != sc['vrf'] or not vv.get('tier1_lr'):
                continue
            nets = [ref_name((v.get('ipam_network_subnet') or {}).get('network_ref')) for v in vv.get('vip') or []]
            if sc['vip_network'] and sc['vip_network'] not in nets:
                continue
            derived.add(vv['tier1_lr'])
            seen_on.append(vv['name'])
    except RuntimeError:
        pass
    tier1 = sc['tier1']
    if tier1:
        if derived and tier1 not in derived:
            notes.append('avi_tier1_%s is %s but VIPs already in %s use %s'
                         % (site, tier1, sc['vrf'], ', '.join(sorted(derived))))
        tier1_from = 'config'
    elif len(derived) == 1:
        tier1 = derived.pop()
        tier1_from = 'existing VIPs: %s' % fmt_list(sorted(seen_on), 3)
    elif derived:
        blocks.append('VIPs in %s use more than one Tier-1 (%s); set avi_tier1_%s'
                      % (sc['vrf'], ', '.join(sorted(derived)), site))
        tier1_from = 'ambiguous'
    else:
        blocks.append('no existing VIP in %s shows its Tier-1; set avi_tier1_%s to the policy path, '
                      'e.g. /infra/tier-1s/<id>' % (sc['vrf'], site))
        tier1_from = 'missing'
    # A VIP's DNS names (its App Domain Name) come across, unless the site's
    # cloud registers them with an outside DNS provider: that would publish
    # blue's names at green's addresses, moving clients before any flip.
    mode = str(cfg.get('avi_vip_dns_info') or 'auto').lower()
    keep_dns = mode != 'drop'
    if mode == 'auto' and urls.get('cloud'):
        try:
            cl = tgt.request('GET', '/api/cloud/%s' % uuid_of(urls['cloud'])) or {}
            pref = cl.get('dns_provider_ref')
            prov = (tgt.request('GET', '/api/ipamdnsproviderprofile/%s' % uuid_of(pref)) or {}) if pref else {}
        except RuntimeError:
            pref, prov = None, {}
        if pref and prov.get('type') != 'IPAMDNS_TYPE_INTERNAL_DNS':
            keep_dns = False
            notes.append('VIP DNS names (App Domain Name) are not written on %s: cloud %s registers them with '
                         'DNS provider %s (%s), which would point blue\'s names at green. avi_vip_dns_info: keep '
                         'writes them anyway' % (site, sc['cloud'], prov.get('name') or ref_name(pref),
                                                 prov.get('type') or 'type unknown'))
    return {'site': site, 'urls': urls, 'tier1': tier1, 'tier1_from': tier1_from,
            'vip_network': sc['vip_network'], 'vip_subnet': sc['vip_subnet'],
            'cloud': sc['cloud'], 'vrf': sc['vrf'], 'se_group': sc['se_group'],
            'map': sc['map'], 'allow_default_group': sc['allow_default_group'],
            'keep_dns_info': keep_dns, 'blocks': blocks, 'notes': notes}


# Fields green sets for itself, whatever it is given: never a difference.
# scaleout_ecmp: 32.1's NSX-T cloud sets it on every virtual service it places.
TARGET_OWNED = {'virtualservice': {'scaleout_ecmp'}}


def ignore_fields(cfg):
    """avi_ignore_fields: ['field', 'type.field'] -> {'*' or type: {field}},
    with the fields green always sets for itself."""
    out = dict((t, set(f)) for t, f in TARGET_OWNED.items())
    for item in as_list(cfg.get('avi_ignore_fields')):
        t, _, f = str(item).rpartition('.')
        out.setdefault(t or '*', set()).add(f)
    return out


def same_value(want, have):
    """True when the target holds the desired value, as far as it goes. Dicts
    compare on the desired keys: a key the target does not return was renamed
    or removed in its release and converted on the way in. Lists compare
    element by element, references by type and name."""
    if isinstance(want, dict):
        if not isinstance(have, dict):
            return False
        for k, w in want.items():
            if k.startswith('_') or k in STRIP_ANYWHERE or k not in have:
                continue
            if not same_value(w, have[k]):
                return False
        return True
    if isinstance(want, list):
        if not isinstance(have, list) or len(want) != len(have):
            return False
        return all(same_value(a, b) for a, b in zip(want, have))
    if isinstance(want, str):
        rw = parse_ref(want)
        if rw:
            rh = parse_ref(have) if isinstance(have, str) else None
            return bool(rh) and (rw['type'], rw['name']) == (rh['type'], rh['name'])
    return want == have


def cert_pem(o):
    return str((o.get('certificate') or {}).get('certificate') or '').strip()


def drift(objtype, body, live, ignore):
    """Top-level fields where the target differs from the desired object."""
    skip = STRIP_TOP | {'enabled', 'traffic_enabled'} | ignore.get('*', set()) | ignore.get(objtype, set())
    if objtype == 'pkiprofile':
        # Each CA certificate by its PEM alone: green recomputes the rest (days
        # until expiry changes daily) and stores the PEM with its own line ends.
        def pems(v):
            return [re.sub(r'\s+', '', str((c or {}).get('certificate') or '')) for c in v or []]
        out = []
        for k, w in body.items():
            if k in skip or k.startswith('_') or k in STRIP_ANYWHERE or k not in live:
                continue
            if k in ('ca_certs', 'crls') and isinstance(w, list):
                if pems(w) != pems(live[k]):
                    out.append(k)
            elif not same_value(w, live[k]):
                out.append(k)
        return sorted(out)
    if objtype == 'sslkeyandcertificate':
        # The certificate is what matters; the rest is computed from it.
        out = [] if cert_pem(body) == cert_pem(live) else ['certificate']
        for k in ('type', 'certificate_management_profile_ref', 'ca_certs'):
            if k in body and k in live and k not in skip and not same_value(body[k], live[k]):
                out.append(k)
        return out
    out = []
    for k, w in body.items():
        if k in skip or k.startswith('_') or k in STRIP_ANYWHERE or k not in live:
            continue
        if not same_value(w, live[k]):
            out.append(k)
    # A list of references blue no longer has at all, which green still holds.
    for k, h in live.items():
        if k.endswith('_refs') and h and k not in body and k not in skip:
            out.append(k)
    return sorted(out)


def body_digest(objtype, body):
    """The desired object as a digest, references by type and name, without
    what green owns. Recorded with every write, so a change on blue shows even
    in a field green does not return."""
    skip = STRIP_TOP | {'enabled', 'traffic_enabled'}

    def norm(v):
        if isinstance(v, dict):
            return dict((k, norm(x)) for k, x in v.items() if not k.startswith('_') and k not in STRIP_ANYWHERE)
        if isinstance(v, list):
            return [norm(x) for x in v]
        if isinstance(v, str):
            r = parse_ref(v)
            if r:
                return '%s/%s' % (r['type'], r['name'])
        return v
    b = dict((k, norm(v)) for k, v in body.items() if k not in skip)
    return hashlib.sha256(json.dumps(b, sort_keys=True).encode()).hexdigest()[:20]


def same_name_clash(live, objtype, body, ctx):
    """A same-named object on the target is converged, which is how a re-run
    resumes. For virtual services and VIPs, make sure it is ours."""
    if objtype not in ('virtualservice', 'vsvip') or not live:
        return None
    if objtype == 'vsvip':
        if ref_name(live.get('vrf_context_ref')) != ctx['vrf']:
            return ('a VsVip with this name already exists on %s in VRF %s; rename one of them'
                    % (ctx['site'], ref_name(live.get('vrf_context_ref'))))
        return None
    want, have = ref_name(body.get('vsvip_ref')), ref_name(live.get('vsvip_ref'))
    if want != have:
        return ('a different virtual service with this name already exists on %s (VIP %s); '
                'rename one of them' % (ctx['site'], have or 'none'))
    for field, label in (('se_group_ref', 'SE group'), ('vrf_context_ref', 'VRF')):
        w, h = ref_name(body.get(field)), ref_name(live.get(field))
        if w and h and w != h:
            return ('a virtual service with this name already exists on %s in %s %s, not %s; '
                    'rename or move one of them' % (ctx['site'], label, h, w))
    return None


def write_version(cfg, bundle, tgt):
    mode = str(cfg.get('avi_write_version') or 'source').lower()
    if mode == 'target':
        return tgt.version
    return bundle.get('source_version') or tgt.version


def plan_site(cfg, site, bundle, scope, key_probe, frozen, ignore, registry, adopt=False):
    """Desired state for one site against what the site holds: an entry per
    object (ADD, UPDATE, UNCHANGED, FROZEN, KEPT, MAPPED or BLOCKED) and the
    writes in dependency order. Only what this tool made, or was handed with
    --adopt or avi_adopt, is ever updated. Reads only."""
    adopt_pats = [str(p) for p in as_list(cfg.get('avi_adopt'))]
    secret_pats = [str(p) for p in as_list(cfg.get('avi_secrets'))]
    tgt = connect(cfg, 'target', site)
    if bundle['source'].rstrip('/') == tgt.host:
        raise ValueError('source and target %s are the same controller' % site)
    objects = bundle['objects']
    mapping = site_conf(cfg, site)['map']
    drop_legacy = truthy(cfg.get('avi_drop_legacy_tls', 'false'))
    entries, warnings, env_used, ops, refused = {}, [], {}, {}, set()

    def entry(key, state, detail=''):
        t, n = split_key(key)
        entries[key] = {'site': site, 'type': t, 'name': n, 'state': state, 'detail': detail}

    # Runtime inventories such as vimgrvmruntime are referenced by blue's pool
    # servers but are stripped before resolution; listing them would read every
    # VM in vCenter for nothing.
    needed = set(split_key(k)[0] for k in scope) | {'cloud', 'vrfcontext', 'serviceenginegroup', 'network'}
    for k in scope:
        for r in iter_refs(objects[k]):
            if r['type'] not in ENVIRONMENT:
                needed.add(r['type'])
    for v in mapping.values():
        needed.add(v.split('/', 1)[0])
    tindex, tobjs, site_blocks = {}, {}, []
    for t in sorted(needed):
        try:
            tobjs[t] = tgt.objects(t)
        except RuntimeError:
            tobjs[t] = {}
            if t in PORTABLE or t in ENVIRONMENT:
                site_blocks.append('cannot list %s on %s' % (t, site))
        tindex[t] = dict((n, o['url'] if '#' in o['url'] else '%s#%s' % (o['url'], n))
                         for n, o in tobjs[t].items() if o.get('url'))
    ctx = site_context(cfg, site, tgt, tindex)
    ctx.update(source_version=bundle.get('source_version'), target_version=tgt.version, product={},
               write_target=release(write_version(cfg, bundle, tgt)) == release(tgt.version))
    site_blocks.extend(ctx['blocks'])
    warnings.extend(ctx['notes'])
    plan = {'site': site, 'target': tgt.host, 'target_version': tgt.version, 'source': bundle['source'],
            'source_version': bundle.get('source_version'),
            'ref_hosts': bundle.get('ref_hosts') or [urlparse(bundle['source']).netloc],
            'write_version': write_version(cfg, bundle, tgt), 'context': ctx,
            'site_blocks': site_blocks, 'warnings': warnings, 'entries': entries, 'ops': [],
            'environment': [], 'adopt': [], 'claim': [], 'baseline': []}
    if site_blocks:
        for key in scope:
            entry(key, 'BLOCKED', 'the site itself is blocked: %s' % '; '.join(site_blocks))
        return plan

    tgt_host = urlparse(tgt.host).netloc
    source_hosts = set(plan['ref_hosts'])
    if bundle.get('source_version', '').split('.')[0] != tgt.version.split('.')[0]:
        warnings.append('version skew: blue %s, %s %s. Objects are posted as %s and converted '
                        'by the target.' % (bundle.get('source_version'), site, tgt.version, plan['write_version']))

    def mapped(k2):
        mt, mn = split_key(mapping[k2])
        return tindex.get(mt, {}).get(mn), mapping[k2]

    for key in sorted(scope):
        objtype, name = split_key(key)
        raw = objects[key]
        if key in mapping:
            url, dest = mapped(key)
            if url:
                entry(key, 'MAPPED', 'avi_map_%s: %s' % (site, dest))
            else:
                entry(key, 'BLOCKED', 'avi_map_%s points at %s, which does not exist' % (site, dest))
                refused.add(key)
            continue
        body = clean(raw, objtype)
        blocks, warns, key_uuid = restage(objtype, name, raw, body, ctx, drop_legacy)
        warnings.extend(warns)
        if key_uuid and (key_probe or {}).get(key_uuid):
            blocks.append('%s. Import it by hand on %s with the same name; the next run leaves it alone'
                          % (key_probe[key_uuid], site))
        sec = secrets_in(objtype, raw)
        supplied = []
        if sec and all(SIMPLE_PATH.match(x) for x in sec) and matches(key, secret_pats):
            supplied = sec  # typed in (or read from the environment) when it is written
            for x in sec:
                del_path(body, x)
        elif sec and all(SIMPLE_PATH.match(x) for x in sec):
            blocks.append('carries a secret the API does not hand back (%s). List it in avi_secrets and the tool '
                          'asks for the value when it writes it, or map it with avi_map_%s' % (', '.join(sec), site))
        elif sec:
            blocks.append('carries a secret the API does not hand back (%s). Create it by hand on %s '
                          'with the same name, or map it with avi_map_%s' % (', '.join(sec), site, site))
        if blocks:
            # What the fix says to make by hand, once made, is taken as it is.
            if tobjs.get(objtype, {}).get(name):
                entry(key, 'UNCHANGED', 'made by hand on %s; left as it is' % site)
                continue
            entry(key, 'BLOCKED', '; '.join(blocks))
            refused.add(key)
            continue

        unresolved, url_map, deferred = [], {}, []
        for odd in stray_refs(body):
            unresolved.append('unrecognised reference, would reach the target pointing at blue: ' + odd)
        for r in iter_refs(body):
            if r['host'] == tgt_host:
                continue  # already a target reference, set by restage
            if r['type'] == 'tenant':
                continue
            if r['name'] is None:
                unresolved.append('reference without a name: ' + r['raw'])
                continue
            k2 = '%s/%s' % (r['type'], r['name'])
            if k2 in mapping:
                url, dest = mapped(k2)
                if url:
                    url_map[r['raw']] = url
                    if r['type'] in ENVIRONMENT:
                        env_used.setdefault((r['type'], r['name']), [dest.split('/', 1)[1], 0])[1] += 1
                else:
                    unresolved.append('avi_map_%s points %s at %s, which does not exist' % (site, k2, dest))
            elif r['type'] in ENVIRONMENT:
                if r['type'] in COLLAPSIBLE and ctx['urls'].get(r['type']):
                    url_map[r['raw']] = ctx['urls'][r['type']]
                    env_used.setdefault((r['type'], r['name']), [ctx[COLLAPSIBLE[r['type']]], 0])[1] += 1
                else:
                    names = sorted(tindex.get(r['type'], {}))
                    unresolved.append('%s "%s" has no mapping for %s. Add to avi_map_%s: %s=%s/<%s>'
                                      % (r['type'], r['name'], site, site, k2, r['type'],
                                         ('one of: ' + fmt_list(names, 6)) if names else 'target name'))
            elif r['type'] in SYSTEM_TYPES or r['type'] in PORTABLE:
                hit = tindex.get(r['type'], {}).get(r['name'])
                if hit:
                    url_map[r['raw']] = hit
                elif k2 in scope and r['type'] in PORTABLE and k2 in refused:
                    unresolved.append('depends on %s, which is blocked' % k2)
                elif k2 in scope and r['type'] in PORTABLE:
                    deferred.append(r['raw'])  # added earlier in this run
                elif r['type'] in SYSTEM_TYPES:
                    unresolved.append('%s "%s" does not exist on %s. Map it: avi_map_%s: %s=%s/<one of: %s>'
                                      % (r['type'], r['name'], site, site, k2, r['type'],
                                         fmt_list(sorted(tindex.get(r['type'], {})), 5)))
                else:
                    unresolved.append('%s "%s" does not exist on %s and is not migrated'
                                      % (r['type'], r['name'], site))
            else:
                unresolved.append('unsupported type %s "%s": map it with avi_map_%s' % (r['type'], r['name'], site))
        if unresolved:
            entry(key, 'BLOCKED', '; '.join(sorted(set(unresolved))))
            refused.add(key)
            continue
        body = remap(body, url_map)
        named = text_mentions(body, source_hosts)
        if named:
            warnings.append('%s: text in %s names blue\'s controller and is copied as it is'
                            % (key, ', '.join(sorted(set(named)))))

        if objtype == 'virtualservice':
            dg = tindex.get('serviceenginegroup', {}).get('Default-Group')
            if dg and refkey(body.get('se_group_ref') or '') == refkey(dg) and not ctx['allow_default_group']:
                entry(key, 'BLOCKED', 'would land in Default-Group on %s. Map blue\'s group to an '
                      'application group in avi_map_%s' % (site, site))
                refused.add(key)
                continue

        live_obj = tobjs.get(objtype, {}).get(name)
        if live_obj:
            clash = same_name_clash(live_obj, objtype, body, ctx)
            if clash:
                entry(key, 'BLOCKED', clash)
                refused.add(key)
                continue
            delta = drift(objtype, body, live_obj, ignore)
            mine = registry.owns(site, objtype, name, live_obj.get('uuid'))
            if registry.claimed(site, objtype, name, live_obj.get('uuid')):
                plan['claim'].append((objtype, name, live_obj.get('uuid')))  # made by a run that stopped
            if not mine and (adopt or matches(key, adopt_pats)):
                plan['adopt'].append((objtype, name, live_obj.get('uuid')))
                mine = True
            if not mine:
                if delta:
                    entry(key, 'KEPT', 'on %s, not made by this tool; differs from blue in %s; left as it is '
                          '(--adopt hands it over)' % (site, fmt_list(delta, 4)))
                else:
                    entry(key, 'UNCHANGED', 'not made by this tool; same as blue')
                continue
            digest = body_digest(objtype, body)
            last = registry.digest(site, objtype, name)
            skip = STRIP_TOP | {'enabled', 'traffic_enabled'} | ignore.get('*', set()) | ignore.get(objtype, set())
            absent = sorted(k for k in body if k not in live_obj and k not in skip and not k.startswith('_'))
            if last is None and absent:
                # Nothing recorded to compare with: a field green does not hold is a difference.
                delta = sorted(set(delta) | set(absent))
            elif last is not None and last != digest and not delta:
                # Blue changed it, or this tool now writes it differently (a
                # product change it handles): either way it is written again.
                delta = ['changed since it was last written%s' % (' (%s)' % ', '.join(absent) if absent else '')]
            if not delta:
                entry(key, 'UNCHANGED')
                if last != digest:
                    plan['baseline'].append((objtype, name, live_obj.get('uuid'), digest))
            elif key in frozen:
                entry(key, 'FROZEN', 'differs from blue in %s; green owns it since %s moved'
                      % (fmt_list(delta, 5), fmt_list(sorted(frozen[key]), 3)))
            else:
                entry(key, 'UPDATE', fmt_list(delta, 6))
                ops[key] = {'kind': 'update', 'uuid': live_obj.get('uuid'), 'body': body,
                            'deferred': sorted(set(deferred)), 'key_uuid': key_uuid, 'delta': delta,
                            'secrets': supplied}
            continue
        entry(key, 'ADD', 'private key from blue' if key_uuid else
              ('%s typed in when written' % ', '.join(supplied)) if supplied else '')
        ops[key] = {'kind': 'add', 'body': body, 'deferred': sorted(set(deferred)), 'key_uuid': key_uuid,
                    'secrets': supplied}

    # A dependent of a blocked object can never succeed. Withdraw it now rather
    # than find out half way through writing.
    while True:
        drop = []
        for k, op in ops.items():
            for raw_ref in op['deferred']:
                r = parse_ref(raw_ref)
                dep = '%s/%s' % (r['type'], r['name'])
                if dep in refused:
                    drop.append((k, dep))
                    break
        if not drop:
            break
        for k, dep in drop:
            ops.pop(k, None)
            refused.add(k)
            entry(k, 'BLOCKED', 'depends on %s, which is blocked' % dep)

    # A new VIP that no virtual service would use would only take an address.
    wanted_vips = set()
    for k, op in ops.items():
        if k.startswith('virtualservice/'):
            for r in iter_refs(op['body']):
                if r['type'] == 'vsvip':
                    wanted_vips.add(r['name'])
    for n, v in tobjs.get('virtualservice', {}).items():
        if ref_name(v.get('vsvip_ref')):
            wanted_vips.add(ref_name(v.get('vsvip_ref')))
    for k in sorted(ops):
        if k.startswith('vsvip/') and ops[k]['kind'] == 'add' and split_key(k)[1] not in wanted_vips:
            ops.pop(k)
            refused.add(k)
            entry(k, 'BLOCKED', 'held back; every virtual service on it is blocked')

    ordered, remaining = [], dict(ops)
    while remaining:
        ready = []
        for k, op in remaining.items():
            deps = set('%s/%s' % (parse_ref(u)['type'], parse_ref(u)['name']) for u in op['deferred'])
            if not (deps & (set(remaining) - {k})):
                ready.append(k)
        if not ready:
            for k in sorted(remaining):
                entry(k, 'BLOCKED', 'dependency cycle among: ' + fmt_list(sorted(remaining), 6))
            break
        ready.sort(key=lambda k: (PORTABLE.index(split_key(k)[0]), k))
        for k in ready:
            op = remaining.pop(k)
            t, n = split_key(k)
            ordered.append({'kind': op['kind'], 'type': t, 'name': n, 'uuid': op.get('uuid'),
                            'source_ref': objects[k].get('url'), 'deferred': op['deferred'],
                            'key_uuid': op['key_uuid'], 'body': op['body'], 'delta': op.get('delta'),
                            'secrets': op.get('secrets') or []})
    plan['ops'] = ordered
    plan['environment'] = [{'type': t, 'blue': n, 'target': v[0], 'references': v[1]}
                           for (t, n), v in sorted(env_used.items())]
    plan['product'] = product_lines(ctx, ctx.get('write_target'))
    plan['warnings'] = sorted(set(warnings))
    return plan


def report_site(plan, show_all=False):
    c = plan['context']
    counts = {}
    for e in plan['entries'].values():
        counts[e['state']] = counts.get(e['state'], 0) + 1
    print('')
    print('  %s  %s (%s)   cloud %s   VRF %s   SE group %s'
          % (plan['site'], plan['target'], plan['target_version'], c.get('cloud'), c.get('vrf'), c.get('se_group')))
    if c.get('tier1'):
        print('      VIPs from %s %s, Tier-1 %s (%s)' % (c['vip_network'], c['vip_subnet'], c['tier1'], c['tier1_from']))
    for b in plan['site_blocks']:
        print('      BLOCKED  %s' % b)
    if plan['environment']:
        print('      blue\'s environment here: %s' % '; '.join(
            '%s %s -> %s (%d)' % (e['type'], e['blue'], e['target'], e['references']) for e in plan['environment']))
    print('      %s' % '   '.join('%s %d' % (s, counts.get(s, 0))
                                 for s in ('ADD', 'UPDATE', 'UNCHANGED', 'FROZEN', 'KEPT', 'MAPPED', 'BLOCKED')))
    if plan.get('claim'):
        print('      TAKEN OVER %d objects a stopped run created on %s: %s'
              % (len(plan['claim']), plan['site'], fmt_list(['%s/%s' % (t, n) for t, n, _ in plan['claim']], 5)))
    if plan['adopt']:
        print('      ADOPT      %d objects already on %s are handed to this tool: %s'
              % (len(plan['adopt']), plan['site'], fmt_list(['%s/%s' % (t, n) for t, n, _ in plan['adopt']], 5)))
    adds = {}
    for e in plan['entries'].values():
        if e['state'] == 'ADD':
            adds[e['type']] = adds.get(e['type'], 0) + 1
    if adds:
        print('      ADD        %s' % ', '.join('%d %s' % (v, k) for k, v in sorted(adds.items(), key=lambda x: -x[1])))
    for line in plan.get('product') or []:
        print('      CHANGED    %s' % line)
    shown = ('UPDATE', 'FROZEN', 'KEPT', 'BLOCKED') + (('ADD', 'UNCHANGED', 'MAPPED') if show_all else ())
    for st in shown:
        rows = sorted((e for e in plan['entries'].values() if e['state'] == st), key=lambda e: (e['type'], e['name']))
        for e in rows[:40]:
            print('      %-10s %-22s %-28s %s' % (st, e['type'], e['name'], e['detail']))
        if len(rows) > 40:
            print('      %-10s ... %d more in the plan file' % (st, len(rows) - 40))
    for w in plan['warnings'][:20]:
        print('      WARNING  %s' % w)
    if len(plan['warnings']) > 20:
        print('      WARNING  ... %d more in the plan file' % (len(plan['warnings']) - 20))


def substitute(v, resolved, source_hosts):
    def swap(s):
        r = parse_ref(s)
        if r and r['host'] in source_hosts and (r['type'], r['uuid']) in resolved:
            return resolved[(r['type'], r['uuid'])]
        return s
    return map_refs(v, swap)


def mentions_source(body, source_hosts):
    """A reference that still points at blue, or None."""
    for s in ref_values(body):
        r = parse_ref(s)
        if (r and r['host'] in source_hosts) or not r:
            return s
    return None


class KeyUnavailable(RuntimeError):
    pass


def fetch_key(src, uuid, name):
    """The private key of one certificate, from blue, in memory only."""
    d = src.request('GET', '/api/sslkeyandcertificate/%s' % uuid, params={'export_key': 'True'}) or {}
    key = d.get('key') or ''
    if not key:
        raise KeyUnavailable('blue returned no private key for %s' % name)
    if 'ENCRYPTED' in key:
        raise KeyUnavailable('the private key of %s is passphrase-protected' % name)
    return key, bool(d.get('key_base64'))


def probe_keys(cfg, bundle, scope):
    """Ask blue for every private key a run may need and discard each at once,
    so a key blue will not hand over is BLOCKED now, not a stop half way
    through writing."""
    need = [(k, bundle['objects'][k].get('uuid')) for k in sorted(scope)
            if k.startswith('sslkeyandcertificate/')
            and bundle['objects'][k].get('type') != 'SSL_CERTIFICATE_TYPE_CA']
    if not need or not truthy(cfg.get('avi_probe_keys', 'true')):
        return {}
    src = connect(cfg, 'source')
    out = {}
    for k, u in need:
        try:
            fetch_key(src, u, split_key(k)[1])
            out[u] = None
        except KeyUnavailable as exc:
            out[u] = str(exc)
    return out


def keep_green(objtype, body, live):
    """On an object updated from blue, what belongs to green stays: the VIP
    addresses green allocated, and whether a virtual service is live (the
    live-state step owns that)."""
    body = copy.deepcopy(body)
    body['uuid'] = live.get('uuid')
    if objtype == 'vsvip':
        have = dict((str(v.get('vip_id')), v) for v in live.get('vip') or [])
        for v in body.get('vip') or []:
            h = have.get(str(v.get('vip_id')))
            if h and h.get('ip_address'):
                v['ip_address'] = h['ip_address']
    if objtype == 'virtualservice':
        body['enabled'] = live.get('enabled', True) is not False
        body['traffic_enabled'] = live.get('traffic_enabled', True) is not False
    return body


def apply_site(cfg, plan, journal, ignore, registry, allow_update=True):
    """Write one site's plan: ADD with POST, UPDATE with PUT, in order. A write
    the controller refuses outright (HTTP 4xx: nothing was written) is reported
    and skipped, with whatever depends on it, and the rest goes on; anything
    else stops the run, and a re-run picks up from there."""
    site = plan['site']
    for t, n, u in plan.get('adopt') or []:
        registry.record(site, t, n, u, 'adopted')
        journal.record(state='adopted', type=t, name=n, site=site, uuid=u)
    for t, n, u in plan.get('claim') or []:
        registry.record(site, t, n, u, 'added')
        journal.record(state='taken over', type=t, name=n, site=site, uuid=u)
    for t, n, u, dg in plan.get('baseline') or []:
        registry.record(site, t, n, u, 'applied', dg)
    tgt = connect(cfg, 'target', site)
    if tgt.host != plan['target'] or tgt.version != plan['target_version']:
        raise ValueError('%s changed since it was read; run again' % site)
    ops = plan['ops']
    for op in ops:
        if op['type'] not in PORTABLE:
            raise ValueError('unsupported write type: ' + op['type'])
        if op['body'].get('name') != op['name']:
            raise ValueError('name mismatch in operation: ' + op['name'])
        if op['kind'] == 'add' and op['type'] == 'virtualservice' and (
                op['body'].get('enabled') is not False or op['body'].get('traffic_enabled') is not False):
            raise ValueError('refusing to add a live virtual service: ' + op['name'])
    source_hosts = set(plan['ref_hosts'])
    src = connect(cfg, 'source') if any(op.get('key_uuid') for op in ops) else None
    live_names = dict((t, tgt.index(t)) for t in sorted(set(op['type'] for op in ops if op['kind'] == 'add')))
    added = updated = withheld = present = 0
    resolved, still, refused, failed_src = {}, [], [], set()
    journal.record(state='run', site=site, target=tgt.host, version=tgt.version, tool=VERSION,
                   write_version=plan['write_version'], operations=len(ops))
    for op in ops:
        label = '%s/%s' % (op['type'], op['name'])
        missing = [u for u in op.get('deferred', []) if refkey(u) not in resolved]
        src_key = refkey(op.get('source_ref') or '')
        cause = [u for u in missing if refkey(u) in failed_src]
        if cause:
            refused.append((label, 'not written: it uses %s, which was refused' % ref_label(cause[0])))
            failed_src.add(src_key)
            journal.record(state='skipped', type=op['type'], name=op['name'], site=site)
            continue
        if missing:
            raise RuntimeError('%s references objects not added yet: %s' % (label, fmt_list(missing, 3)))
        body = substitute(op['body'], resolved, source_hosts)
        left = stray_refs(body) or mentions_source(body, source_hosts)
        if left:
            raise RuntimeError('%s still references blue after substitution (%s); refusing it'
                               % (label, left if isinstance(left, str) else left[0]))
        src_key = refkey(op.get('source_ref') or '')
        if op['kind'] == 'update':
            if not allow_update:
                withheld += 1
                journal.record(state='withheld', type=op['type'], name=op['name'], site=site)
                continue
            live = tgt.request('GET', '/api/%s/%s' % (op['type'], op['uuid'])) or {}
            body = keep_green(op['type'], body, live)
        elif op['name'] in live_names[op['type']]:
            # Added since it was read (a reply lost on an earlier run, say). The
            # next run compares it; this one only needs its address.
            if src_key:
                resolved[src_key] = live_names[op['type']][op['name']]
            present += 1
            journal.record(state='present', type=op['type'], name=op['name'], site=site)
            continue
        if op.get('key_uuid'):
            body = dict(body)
            body['key'], b64 = fetch_key(src, op['key_uuid'], op['name'])
            if b64:
                body['key_base64'] = True
        if op.get('secrets'):
            body = copy.deepcopy(body)
            try:
                for pth in op['secrets']:
                    set_path(body, pth, secret_value(op['type'], op['name'], pth))
            except NoSecret as exc:
                # Nothing is written without it; everything else still is.
                refused.append((label, str(exc)))
                failed_src.add(src_key)
                journal.record(state='refused', op=op['kind'], type=op['type'], name=op['name'], site=site,
                               reason=str(exc))
                continue
        journal.record(state='attempt', op=op['kind'], type=op['type'], name=op['name'], site=site,
                       delta=op.get('delta'))
        if op['kind'] == 'add':
            registry.intend(site, op['type'], op['name'])
            try:
                made = tgt.request('POST', '/api/' + op['type'], body, api_version=plan['write_version'])
            except RuntimeError as exc:
                if not re.search(r'HTTP 4\d\d', str(exc)):
                    raise
                registry.abandon(site, op['type'], op['name'])
                refused.append((label, refusal(exc)))
                failed_src.add(src_key)
                journal.record(state='refused', op='add', type=op['type'], name=op['name'], site=site,
                               reason=refusal(exc))
                continue
            url = (made or {}).get('url')
            if not url:
                raise RuntimeError('%s was accepted but no url came back; later objects cannot '
                                   'reference it' % label)
            if src_key:
                resolved[src_key] = url
            registry.record(site, op['type'], op['name'], uuid_of(url), 'added', body_digest(op['type'], op['body']))
            added += 1
            print('      added    %-22s %s' % (op['type'], op['name']))
        else:
            try:
                made = tgt.request('PUT', '/api/%s/%s' % (op['type'], op['uuid']), body,
                                   api_version=plan['write_version'])
            except RuntimeError as exc:
                if not re.search(r'HTTP 4\d\d', str(exc)):
                    raise
                refused.append((label, refusal(exc)))
                journal.record(state='refused', op='update', type=op['type'], name=op['name'], site=site,
                               reason=refusal(exc))
                continue
            url = (made or {}).get('url')
            registry.record(site, op['type'], op['name'], op['uuid'], 'applied', body_digest(op['type'], op['body']))
            updated += 1
            print('      updated  %-22s %-28s %s' % (op['type'], op['name'], fmt_list(op.get('delta') or [], 5)))
            # A field the target rewrites would be an UPDATE on every run.
            now_obj = tgt.request('GET', '/api/%s/%s' % (op['type'], op['uuid'])) or {}
            again = drift(op['type'], op['body'], now_obj, ignore)
            if again:
                still.append('%s on %s still differs after the update in %s: the target rewrites it. '
                             'Add to avi_ignore_fields: %s'
                             % (label, site, ', '.join(again), ', '.join('%s.%s' % (op['type'], f) for f in again)))
        journal.record(state='accepted', op=op['kind'], type=op['type'], name=op['name'], site=site, url=url)
    journal.record(state='done', site=site, added=added, updated=updated, withheld=withheld, present=present,
                   refused=len(refused))
    return {'added': added, 'updated': updated, 'withheld': withheld, 'present': present, 'still': still,
            'refused': refused}


def refusal(exc):
    """The controller's own words, from 'POST /api/x on site_a: HTTP 400: {"error": "..."}'."""
    text = str(exc)
    m = re.search(r'"error"\s*:\s*"((?:[^"\\]|\\.)*)"', text)
    return m.group(1) if m else text[:300]


def ref_label(raw):
    r = parse_ref(raw) or {}
    return '%s/%s' % (r.get('type'), r.get('name') or r.get('uuid'))


def record_vips(cfg, site, tgt, names):
    out = {}
    path = artefact(cfg, 'vips', site=site)
    if os.path.exists(path):
        try:
            out = read(path)
        except ValueError:
            out = {}
    for n in names:
        try:
            vv = tgt.find('vsvip', n)
        except RuntimeError:
            vv = None
        if vv:
            out[n] = [v['ip_address']['addr'] for v in vv.get('vip') or []
                      if isinstance(v.get('ip_address'), dict) and v['ip_address'].get('addr')]
    if out:
        save(path, out)
    return out


# ---------------------------------------------------------------- DNS names -> GSLB names

def load_dns(path):
    if not path or not os.path.exists(path):
        raise ValueError('the DNS names file %s does not exist. Write it from this host with discover, or on a '
                         'domain controller with Export-DnsRecords.ps1, then set gslb_names or pass --names' % path)
    with open(path, newline='', encoding='utf-8-sig') as fh:
        lines = [ln for ln in fh.read().splitlines() if ln.strip() and not ln.startswith('#')]
    rd = csv.DictReader(lines)
    cols = dict((str(c).strip().lower(), c) for c in rd.fieldnames or [])
    for need in ('fqdn', 'type', 'data'):
        if need not in cols:
            raise ValueError('%s needs columns fqdn,type,data[,ttl,zone]; it has %s' % (path, ', '.join(cols)))
    rows = []
    for r in rd:
        fq = str(r.get(cols['fqdn']) or '').strip().lower().rstrip('.')
        ty = str(r.get(cols['type']) or '').strip().upper()
        da = str(r.get(cols['data']) or '').strip().lower().rstrip('.')
        ttl = None
        if 'ttl' in cols and str(r.get(cols['ttl']) or '').strip():
            try:
                ttl = int(float(r[cols['ttl']]))
            except ValueError:
                ttl = None
        zn = str(r.get(cols['zone']) or '').strip().lower().rstrip('.') if 'zone' in cols else ''
        if fq and ty:
            rows.append({'fqdn': fq, 'type': ty, 'data': da, 'ttl': ttl, 'zone': zn})
    return rows


def split_zone(fqdn, zones):
    best = None
    for z in zones:
        if fqdn == z or fqdn.endswith('.' + z):
            if best is None or len(z) > len(best):
                best = z
    if best is None:
        return None, None
    return best, ('' if fqdn == best else fqdn[:-(len(best) + 1)])


def choose_member(inv, vsvip, override=None):
    """The service GSLB watches for a blue VIP: gslb_member if set, else the
    TLS service on 443, else any TLS service, else the lowest port."""
    on_vip = inv['vsvip'].get(vsvip, {}).get('vs', [])
    if override and override in on_vip:
        return override
    cands = [n for n in on_vip if inv['vs'][n]['type'] != 'VS_TYPE_VH_CHILD']
    if not cands:
        return ''

    def score(n):
        v = inv['vs'][n]
        return (0 if (443 in v['ports'] and v['ssl']) else 1 if v['ssl'] else 2,
                0 if v['enabled'] else 1, min(v['ports'] or [99999]), n)
    return sorted(cands, key=score)[0]


def first_members(services, lives, first):
    """GSLB service name -> the name of its member virtual service at the
    first site, which carries the blue service's name."""
    lv = lives.get(first) or {}
    by_uuid = dict((v.get('uuid'), n) for n, v in (lv.get('vs') or {}).items())
    out = {}
    for name, svc in (services or {}).items():
        for g in svc.get('groups') or []:
            for m in g.get('members') or []:
                if m.get('cluster_uuid') == lv.get('cluster_uuid') and m.get('vs_uuid') in by_uuid:
                    out[name] = by_uuid[m['vs_uuid']]
        out.setdefault(name, name)
    return out


def green_vips(lives):
    """Green VIP address -> the virtual services on it, at any site."""
    out = {}
    for lv in (lives or {}).values():
        for n, v in lv['vs'].items():
            for ip in lv['vsvip_ips'].get(ref_name(v.get('vsvip_ref')) or '', []):
                out.setdefault(ip, set()).add(n)
    return out


def build_rows(cfg, bundle, dns_rows, services=None, members=None, green=None):
    """One row per DNS name that points at a blue VIP, or already at its GSLB
    name; the CNAMEs that follow them; the names pointed straight at a green
    VIP by hand; and the blue VIPs no name points at. Decisions come from the
    config, never from an edited file."""
    zones = [str(z).lower().rstrip('.') for z in as_list(cfg.get('gslb_zones'))]
    if not zones:
        raise ValueError('gslb_zones is not set in the config')
    label = str(cfg.get('gslb_label') or 'gslb')
    exclude = [str(p).lower() for p in as_list(cfg.get('gslb_exclude'))]
    include_disabled = [str(p).lower() for p in as_list(cfg.get('gslb_include_disabled'))]
    member_over = pairs(cfg.get('gslb_member'))
    inv = bundle['inventory']
    ip2vsvip = {}
    for name, v in inv['vsvip'].items():
        for ip in v['ips']:
            ip2vsvip[ip] = name
    ip2vsvip.update(vip_aliases(cfg, inv))
    owner = {}
    for n, svc in (services or {}).items():
        for d in svc.get('domain_names') or []:
            owner[str(d).lower()] = n
    a_recs, cnames, ttls, holders, others, shadowed = {}, {}, {}, {}, {}, {}
    for r in dns_rows:
        # The DNS server answers a name from the most specific zone that holds
        # it. A copy left in a parent zone (app.corp in example.com once
        # corp.example.com exists) is never served, and must not be edited.
        z = r.get('zone')
        if z and len(z) > len(holders.get(r['fqdn'], '')):
            holders[r['fqdn']] = z
    for r in dns_rows:
        z = r.get('zone')
        if z and z != holders.get(r['fqdn'], z):
            shadowed.setdefault(r['fqdn'], set()).add(z)
            continue
        if r['type'] in DNSSEC_TYPES:
            continue  # signatures follow the records; a signed zone re-signs itself
        if r['type'] == 'A':
            a_recs.setdefault(r['fqdn'], [])
            if r['data'] not in a_recs[r['fqdn']]:
                a_recs[r['fqdn']].append(r['data'])
        elif r['type'] == 'CNAME':
            cnames[r['fqdn']] = r['data']
        else:
            others.setdefault(r['fqdn'], set()).add(r['type'])
        if r['ttl'] is not None and r['type'] in ('A', 'CNAME'):
            ttls[r['fqdn']] = r['ttl']
    explicit = set(ip2vsvip) - set(ip for v in inv['vsvip'].values() for ip in v['ips'])
    inferred = inferred_aliases(cfg, inv, a_recs, ip2vsvip, green)
    ip2vsvip.update(inferred)

    def base(fq, **kw):
        zone, _ = split_zone(fq, zones)
        row = {'fqdn': fq, 'zone': zone or '', 'dns_zone': holders.get(fq) or zone or '', 'record': '',
               'blue_ip': '', 'blue_vsvip': '', 'member_vs': '', 'gslb_service': '', 'gslb_fqdn': '',
               'ttl': ttls.get(fq, ''), 'note': '', 'flip_checked': False, 'gslb_held': False}
        row.update(kw)
        return row

    rows, named = [], set()
    for fq in sorted(a_recs):
        ips = a_recs[fq]
        blue = [ip for ip in ips if ip in ip2vsvip]
        if not blue:
            # Pointed at green by hand: that application already takes traffic
            # there. A test name belongs in gslb_exclude.
            mine = sorted(set(n for ip in ips for n in (green or {}).get(ip, ()) if n in inv['vs']))
            if mine and not matches(fq, exclude):
                named.add(inv['vs'][mine[0]].get('vsvip'))
                rows.append(base(fq, action='MANUAL', record='A %s' % ' '.join(ips), member_vs=mine[0],
                                 green_direct=True, note='points straight at green (%s): its application counts as '
                                 'flipped; a CNAME to its GSLB name would give it failover. A test name belongs '
                                 'in gslb_exclude' % ', '.join(mine)))
            continue
        zone, host = split_zone(fq, zones)
        vsvip = ip2vsvip[blue[0]]
        named.update(ip2vsvip[i] for i in blue)
        member = choose_member(inv, vsvip, member_over.get(vsvip))
        row = base(fq, record='A', blue_ip=blue[0], blue_vsvip=vsvip, member_vs=member, gslb_service=member)
        dns_zone = row['dns_zone']
        vs_on = inv['vsvip'][vsvip]['vs']
        clash = sorted(t for t in others.get(fq, ()) if not (t in ('SOA', 'NS') and fq == dns_zone))
        if len(set(ip2vsvip[i] for i in blue)) > 1:
            row['action'], row['note'] = 'MANUAL', 'resolves to more than one blue VIP: %s' % ' '.join(blue)
        elif len(ips) > len(blue):
            row['action'], row['note'] = 'MANUAL', 'also resolves to %s, which is not a blue VIP' % ' '.join(
                ip for ip in ips if ip not in blue)
        elif not zone:
            row['action'], row['note'] = 'SKIP', 'not in gslb_zones'
        elif matches(fq, exclude):
            row['action'], row['note'] = 'SKIP', 'excluded by gslb_exclude'
        elif not host or fq == dns_zone:
            row['action'], row['note'] = 'MANUAL', 'zone apex: a CNAME is not allowed here'
        elif host.startswith('*'):
            row['action'], row['note'] = 'MANUAL', 'wildcard record: decide by hand'
        elif clash:
            row['action'], row['note'] = 'MANUAL', ('also holds %s records; a CNAME cannot share a name with them'
                                                    % ', '.join(clash))
        elif host == label or host.endswith('.' + label):
            row['action'], row['note'] = 'SKIP', 'already a GSLB name'
        elif not member:
            row['action'], row['note'] = 'MANUAL', 'no virtual service on this VIP can be a GSLB member'
        else:
            row['gslb_fqdn'] = '%s.%s.%s' % (host, label, zone)
            row['action'] = 'PUBLISH'
            # Only a GSLB name a service already answers for can have been
            # flipped to: a CNAME to any other would not resolve.
            row['gslb_held'] = row['gslb_fqdn'] in owner
            if not any(inv['vs'][n]['enabled'] for n in vs_on) and not matches(fq, include_disabled):
                row['action'], row['note'] = 'SKIP', 'disabled on blue (gslb_include_disabled publishes it)'
        if len(vs_on) > 1 and not row['note']:
            row['note'] = 'VIP shared by %s' % ' '.join('%s:%s' % (n, '/'.join(str(p) for p in inv['vs'][n]['ports']))
                                                     for n in vs_on)
        if blue[0] in inferred or blue[0] in explicit:
            row['fronted'] = 'inferred' if blue[0] in inferred else 'gslb_vip_alias'
            row['note'] = ('%s; ' % row['note'] if row['note'] else '') + (
                'served today from %s, not blue VIP %s (%s): a flip moves it from %s to GSLB, a rollback puts %s '
                'back' % (blue[0], ' '.join(inv['vsvip'][vsvip]['ips']), row['fronted'], blue[0], blue[0]))
        if fq in shadowed:
            row['note'] = ('%s; ' % row['note'] if row['note'] else '') + (
                'an old copy in %s is not served and is left alone' % ', '.join(sorted(shadowed[fq])))
        rows.append(row)

    # A name already flipped is a CNAME to a GSLB name, and no longer joins to a
    # blue VIP. Tie it back through the GSLB service that answers for it: its
    # member at the first site carries the blue service's name.
    have = set(r['fqdn'] for r in rows)
    for fq in sorted(cnames):
        tgt = cnames[fq]
        if fq in have or tgt not in owner:
            continue
        svc = owner[tgt]
        member = (members or {}).get(svc, svc)
        vsvip = inv['vs'].get(member, {}).get('vsvip')
        if vsvip not in inv['vsvip']:
            rows.append(base(fq, action='MANUAL', record='CNAME %s' % tgt, gslb_service=svc, gslb_fqdn=tgt,
                             note='points at GSLB service %s, which does not tie back to a blue VIP' % svc))
            have.add(fq)
            continue
        named.add(vsvip)
        rows.append(base(fq, action='MOVED', record='CNAME %s' % tgt, blue_ip=(inv['vsvip'][vsvip]['ips'] or [''])[0],
                         blue_vsvip=vsvip, member_vs=member, gslb_service=svc, gslb_fqdn=tgt,
                         note='flipped', flip_checked=True, gslb_held=True))
        have.add(fq)

    published = dict((r['fqdn'], r) for r in rows if r['fqdn'])
    for fq in sorted(cnames):
        if fq in published:
            continue
        cur, hops, seen, end = fq, 0, {fq}, None
        while hops < 8:
            nxt = cnames.get(cur)
            if nxt is None or nxt in seen:
                break
            if nxt in published:
                end = nxt
                break
            seen.add(nxt)
            cur, hops = nxt, hops + 1
        if not end:
            continue
        p = published[end]
        rows.append(base(fq, action='FOLLOWS', record='CNAME %s' % cnames[fq], blue_ip=p['blue_ip'],
                         blue_vsvip=p['blue_vsvip'],
                         note=('follows %s; no change needed' % end) if p['action'] in ('PUBLISH', 'MOVED')
                         else 'follows %s, which is %s' % (end, p['action'])))
    for vsvip in sorted(set(inv['vsvip']) - named):
        v = inv['vsvip'][vsvip]
        if not v['vs']:
            continue  # nothing migrated uses this VIP
        hints = set(v['fqdns'])
        for n in v['vs']:
            for m in [n] + inv['vs'][n]['children']:
                for cn in inv['vs'].get(m, {}).get('certs', []):
                    hints.update(inv['certs'].get(cn, {}).get('names', []))
                hints.update(inv['vs'].get(m, {}).get('domains', []))
                hints.update(inv['vs'].get(m, {}).get('hosts') or [])
        # What DNS holds for each name blue gives it: that says why none is its own.
        seen = []
        for h in sorted(hints)[:6]:
            if h in a_recs:
                seen.append('%s -> %s' % (h, ' '.join(a_recs[h])))
            elif h in cnames:
                seen.append('%s CNAME %s' % (h, cnames[h]))
            else:
                seen.append('%s (no record)' % h)
        rows.append({'action': 'NONAME', 'fqdn': '', 'zone': '', 'dns_zone': '', 'record': '',
                     'blue_ip': ' '.join(v['ips']), 'blue_vsvip': vsvip,
                     'member_vs': choose_member(inv, vsvip), 'gslb_service': '', 'gslb_fqdn': '',
                     'ttl': '', 'flip_checked': False,
                     'note': 'no DNS name points here; %s' % (
                         ('names on blue: %s' % ', '.join(seen)) if seen else 'no name on blue')})
    return rows


def inferred_aliases(cfg, inv, a_recs, ip2vsvip, green=None):
    """Addresses in front of blue VIPs (a NAT, or the load balancer an
    application is served from until it moves), inferred from DNS: a name
    that blue's configuration gives to one VIP only, and that points at one
    address which is neither a blue VIP nor a green one, makes that address
    the VIP's, as gslb_vip_alias would. Only for a VIP no name points at, and
    only an address that every such name agrees on. Nothing moves until a
    flip, which moves the name from that address; a rollback puts it back.
    gslb_infer_alias: false turns it off."""
    if not truthy(cfg.get('gslb_infer_alias', 'true')):
        return {}
    zones = [str(z).lower().rstrip('.') for z in as_list(cfg.get('gslb_zones'))]
    label = str(cfg.get('gslb_label') or 'gslb')
    named = set(ip2vsvip[ip] for ips in a_recs.values() for ip in ips if ip in ip2vsvip)
    votes = {}
    for fq, vips in candidate_names(cfg, inv, zones, label).items():
        _, host = split_zone(fq, zones)
        ips = a_recs.get(fq) or []
        if len(vips) != 1 or not host or host.startswith('*') or len(ips) != 1:
            continue
        if ips[0] in ip2vsvip or ips[0] in (green or {}):
            continue
        votes.setdefault(ips[0], set()).update(vips)
    return dict((ip, sorted(v)[0]) for ip, v in votes.items() if len(v) == 1 and sorted(v)[0] not in named)


def vip_aliases(cfg, inv):
    """gslb_vip_alias: [<address>=<blue VsVip, or its address>]. An address a
    name points at that fronts a blue VIP (a NAT, say): names pointing at it
    are that VIP's names, and a flip moves them from that address to GSLB."""
    out = {}
    by_ip = dict((ip, n) for n, v in inv['vsvip'].items() for ip in v['ips'])
    for addr, target in pairs(cfg.get('gslb_vip_alias')).items():
        try:
            ipaddress.IPv4Address(addr)
        except ValueError:
            raise ValueError('gslb_vip_alias %s=%s: %s is not an IPv4 address' % (addr, target, addr))
        vsvip = target if target in inv['vsvip'] else by_ip.get(target)
        if not vsvip:
            raise ValueError('gslb_vip_alias %s=%s: %s is neither a VsVip on blue nor one of its addresses'
                             % (addr, target, target))
        if addr in by_ip:
            raise ValueError('gslb_vip_alias %s=%s: %s is already blue\'s VIP %s' % (addr, target, addr, by_ip[addr]))
        out[addr] = vsvip
    return out


def gslb_zone_list(cfg):
    return [str(z).lower().rstrip('.') for z in as_list(cfg.get('gslb_zones'))]


def resolvers(cfg):
    """The DNS servers clients use: dns_servers, else this host's resolvers."""
    servers = [str(x) for x in as_list(cfg.get('dns_servers'))]
    unfilled = [x for x in servers if not re.match(r'^[A-Za-z0-9._:-]+$', x)]
    if unfilled:
        raise ValueError('dns_servers still holds %s: fill in the IP addresses of the DCs clients use'
                         % ', '.join(unfilled))
    if servers:
        return servers, 'dns_servers'
    try:
        with open('/etc/resolv.conf') as fh:
            for line in fh:
                parts = line.split()
                if len(parts) >= 2 and parts[0] == 'nameserver':
                    servers.append(parts[1])
    except OSError:
        pass
    return servers, '/etc/resolv.conf'


def check_flips(cfg, rows):
    """Ask every DNS server clients use about each name that could be
    flipped. Flipped when any of them answers the CNAME to the GSLB name (a
    flip reaches the other DCs only after replication and polling); not
    flipped only when every one of them answered without it; otherwise
    unknown, which keeps flip_checked False. A name the export already saw
    flipped is asked too, so one rolled back since is not taken for flipped."""
    servers, source = resolvers(cfg)
    down = dns_down(servers, gslb_zone_list(cfg)) if any(
        r['action'] in ('PUBLISH', 'MOVED') and r['gslb_fqdn'] for r in rows) else set()
    asked = 0
    for r in rows:
        if r['action'] not in ('PUBLISH', 'MOVED') or not r['gslb_fqdn']:
            continue
        cname, answered = False, bool(servers)
        for ns in servers:
            if ns in down:
                answered = False  # out of reach: it cannot say the name is not flipped
                continue
            ans = dns_query(ns, r['fqdn'])
            if ans.get('error') or ans.get('rcode') not in (0, 3):
                answered = False
                continue
            if r['gslb_fqdn'] in [str(c).rstrip('.').lower() for c in ans.get('cname', [])]:
                cname = True
        if cname:
            r['flip_checked'] = True
            if r['action'] == 'PUBLISH':
                r['action'], r['record'], r['note'] = 'MOVED', 'CNAME %s' % r['gslb_fqdn'], 'flipped'
        elif answered:
            r['flip_checked'] = True
            if r['action'] == 'MOVED':
                r['action'], r['record'], r['note'] = 'PUBLISH', 'A', 'rolled back since the DNS export'
        asked += 1 if (cname or answered) else 0
    return servers, source, asked


def owned_by_green(cfg, bundle, rows, trust_export=False):
    """Virtual service -> why green owns it: a name of its VIP is flipped, its
    flip state could not be read while a GSLB service already answers for its
    GSLB name (none can be flipped before that), or avi_freeze names it."""
    inv = bundle['inventory']
    owners = {}
    for r in rows:
        moved = r['action'] == 'MOVED' or r.get('green_direct')
        unknown = (r['action'] == 'PUBLISH' and r.get('gslb_fqdn') and not r.get('flip_checked') and not trust_export
                   and r.get('gslb_held'))
        if not (moved or unknown) or r.get('member_vs') not in inv['vs']:
            continue
        why = r['fqdn'] if moved else '%s (flip state unknown)' % r['fqdn']
        for vs in expand_vs(inv, [r['member_vs']]):
            owners.setdefault(vs, set()).add(why)
    for pat in as_list(cfg.get('avi_freeze')):
        for vs in inv['vs']:
            if fnmatch.fnmatchcase(vs, str(pat)):
                owners.setdefault(vs, set()).add('avi_freeze')
    return owners


def frozen_objects(cfg, bundle, owners):
    """Every object a green-owned virtual service uses, with why. Empty with
    avi_sync_moved: true, which keeps updating flipped applications from blue."""
    if truthy(cfg.get('avi_sync_moved', 'false')):
        return {}
    frozen = {}
    for vs, why in owners.items():
        for k in closure(bundle['objects'], ['virtualservice/%s' % vs]):
            frozen.setdefault(k, set()).update(why)
    return frozen


def cluster_uuid(c):
    """The controller cluster's uuid: which cluster a client really reaches."""
    cluster = c.request('GET', '/api/cluster') or {}
    if isinstance(cluster.get('results'), list):
        cluster = cluster['results'][0] if cluster['results'] else {}
    return cluster.get('uuid')


def live_site(cfg, site):
    """Virtual services, VIP addresses, cluster and cloud of one site."""
    c = connect(cfg, 'target', site)
    sc = site_conf(cfg, site)
    vs = c.objects('virtualservice')
    vsvips = c.objects('vsvip')
    ips = {}
    for n, vv in vsvips.items():
        ips[n] = [v['ip_address']['addr'] for v in vv.get('vip') or []
                  if isinstance(v.get('ip_address'), dict) and v['ip_address'].get('addr')]
    cloud = c.find('cloud', sc['cloud']) if sc['cloud'] else None
    return {'client': c, 'vs': vs, 'vsvip_ips': ips, 'cluster_uuid': cluster_uuid(c),
            'cloud_uuid': (cloud or {}).get('uuid'), 'conf': sc}


def site_vip(live, vs_name):
    v = live['vs'].get(vs_name)
    if not v:
        return None
    ips = live['vsvip_ips'].get(ref_name(v.get('vsvip_ref')) or '', [])
    return ips[0] if ips else None


# ---------------------------------------------------------------- GSLB on the leader

def gslb_zone_names(cfg):
    label = str(cfg.get('gslb_label') or 'gslb')
    return ['%s.%s' % (label, str(z).lower().rstrip('.')) for z in as_list(cfg.get('gslb_zones'))]


def gslb_checks(cfg, lives, leader_site, commit, journal):
    """Subdomains on the GSLB object, authoritative zones on each site's DNS
    profile, and each DNS service hosting them; what is missing is added on a
    commit. Returns (ok, gslb, messages)."""
    want = gslb_zone_names(cfg)
    leader = lives[leader_site]['client']
    msgs, ok = [], True
    gl = leader.listing('gslb')
    if not gl:
        return False, None, ['FAIL  no GSLB configuration on %s; it is the configured leader' % leader_site]
    g = gl[0]
    lead_uuid = lives[leader_site]['cluster_uuid']
    if g.get('leader_cluster_uuid') and lead_uuid and g['leader_cluster_uuid'] != lead_uuid:
        return False, g, ['FAIL  %s is not the GSLB leader; set gslb_leader to the leader site' % leader_site]
    by_name = dict((s.get('name'), s) for s in g.get('sites') or [])
    for site, lv in lives.items():
        s = by_name.get(lv['conf']['gslb_site'])
        if not s:
            ok = False
            msgs.append('FAIL  site %s is not in the GSLB configuration (sites: %s); set gslb_site_name_%s'
                        % (lv['conf']['gslb_site'], fmt_list(by_name), site))
        elif lv['cluster_uuid'] and s.get('cluster_uuid') != lv['cluster_uuid']:
            ok = False
            msgs.append('FAIL  GSLB site %s is cluster %s, but %s is %s'
                        % (s.get('name'), s.get('cluster_uuid'), site, lv['cluster_uuid']))
    def gaps(gx):
        """The subdomains the GSLB configuration lacks, and each site DNS
        service that lists the subdomains it hosts (Host All Subdomains off)
        without all of them."""
        have = [d.get('domain_name') for d in gx.get('dns_configs') or []]
        sv = []
        for s in gx.get('sites') or []:
            for dv in s.get('dns_vses') or []:
                doms = dv.get('domain_names') or []
                gap = [w for w in want if doms and w not in doms]
                if gap:
                    sv.append((s.get('name'), gap))
        return [w for w in want if w not in have], sv

    missing, vs_gaps = gaps(g)
    if missing or vs_gaps:
        if commit:
            # 32.1 refuses a PATCH that adds to these lists ("Failed to patch list
            # of sub objects. Key not found": their entries have no key), so the
            # GSLB configuration is read whole and put back with the subdomains
            # added, as the UI saves it. A site's password comes back masked, and
            # the controller keeps the one it holds.
            body = leader.request('GET', '/api/gslb/%s' % g['uuid'])
            if not isinstance(body, dict) or body.get('uuid') != g['uuid'] or not body.get('sites'):
                raise RuntimeError('the GSLB configuration on %s did not read back whole; nothing was changed'
                                   % leader_site)
            missing, vs_gaps = gaps(body)
            body['dns_configs'] = list(body.get('dns_configs') or []) + [{'domain_name': w} for w in missing]
            for s in body['sites']:
                for dv in s.get('dns_vses') or []:
                    doms = dv.get('domain_names') or []
                    if doms:
                        dv['domain_names'] = doms + [w for w in want if w not in doms]
            if missing or vs_gaps:
                journal.record(state='attempt', type='gslb', name=body.get('name'), added_subdomains=missing,
                               added_to_dns_services=vs_gaps)
                g = leader.request('PUT', '/api/gslb/%s' % g['uuid'], body) or body
                journal.record(state='accepted', type='gslb', name=body.get('name'), added_subdomains=missing,
                               added_to_dns_services=vs_gaps)
            if missing:
                msgs.append('ADDED GSLB subdomains %s' % ', '.join(missing))
            for sn, gap in vs_gaps:
                msgs.append('ADDED %s to the subdomains the DNS service on site %s hosts' % (', '.join(gap), sn))
        else:
            ok = False
            if missing:
                msgs.append('ADD   GSLB subdomains %s' % ', '.join(missing))
            for sn, gap in vs_gaps:
                msgs.append('ADD   %s to the subdomains the DNS service on site %s hosts' % (', '.join(gap), sn))
    else:
        msgs.append('OK    GSLB subdomains: %s' % ', '.join(want))
    configured = str(cfg.get('gslb_dns_profile') or '')
    for site, lv in sorted(lives.items()):
        c = lv['client']
        # The profile that matters is the one the site's GSLB DNS service uses.
        gs = by_name.get(lv['conf']['gslb_site']) or {}
        used = set()
        for dv in gs.get('dns_vses') or []:
            for v in lv['vs'].values():
                if v.get('uuid') == dv.get('dns_vs_uuid') and v.get('application_profile_ref'):
                    used.add(ref_name(v['application_profile_ref']))
        if len(used) > 1:
            ok = False
            msgs.append('FAIL  the DNS services on %s use different profiles (%s)' % (site, ', '.join(sorted(used))))
            continue
        prof_name = used.pop() if used else configured
        if not prof_name:
            msgs.append('SKIP  no DNS profile found for %s; authoritative zones not checked' % site)
            continue
        if configured and prof_name != configured:
            msgs.append('NOTE  the DNS service on %s uses %s, not gslb_dns_profile %s; that is the one checked'
                        % (site, prof_name, configured))
        if prof_name.startswith('System-'):
            ok = False
            msgs.append('FAIL  the DNS service on %s uses %s. Give it its own DNS profile (Broadcom: a '
                        'customised profile used only by the GSLB DNS service); System- profiles are '
                        'not edited by this tool' % (site, prof_name))
            continue
        prof = c.find('applicationprofile', prof_name)
        if not prof:
            ok = False
            msgs.append('FAIL  DNS profile %s not found on %s' % (prof_name, site))
            continue
        dsp = prof.get('dns_service_profile') or {}
        zones = [z.get('domain_name') for z in dsp.get('dns_zones') or []]
        gap = [w for w in want if w not in zones]
        if not gap:
            msgs.append('OK    %s on %s is authoritative for all %d subdomains' % (prof_name, site, len(want)))
            continue
        if commit:
            body = copy.deepcopy(prof)
            tmpl = next((z for z in dsp.get('dns_zones') or [] if z.get('domain_name') in want), None)
            extra = []
            for w in gap:
                z = {'domain_name': w}
                if tmpl:
                    for k in ('admin_email', 'name_server'):
                        if tmpl.get(k):
                            z[k] = tmpl[k]
                extra.append(z)
            body.setdefault('dns_service_profile', {}).setdefault('dns_zones', []).extend(extra)
            c.request('PUT', '/api/applicationprofile/%s' % prof['uuid'], body)
            journal.record(state='accepted', type='applicationprofile', name=prof_name, site=site,
                           added_zones=gap)
            msgs.append('ADDED authoritative zones %s to %s on %s' % (', '.join(gap), prof_name, site))
        else:
            ok = False
            msgs.append('ADD   authoritative zones %s to %s on %s' % (', '.join(gap), prof_name, site))
    # What GSLB itself can survive. Each site's DNS service needs a second
    # engine to outlive one (Broadcom: DNS on SE groups of its own), and the
    # leader is changed by hand, so its loss stops changes, not answers.
    for site, lv in sorted(lives.items()):
        gs = by_name.get(lv['conf']['gslb_site']) or {}
        for dv in gs.get('dns_vses') or []:
            v = next((x for x in lv['vs'].values() if x.get('uuid') == dv.get('dns_vs_uuid')), None)
            if not v:
                continue
            grp_name = ref_name(v.get('se_group_ref')) or ''
            try:
                grp = lv['client'].find('serviceenginegroup', grp_name) or {}
            except RuntimeError:
                grp = {}
            if not grp:
                continue
            if int(grp.get('max_se') or 1) < 2:
                msgs.append('WARN  the DNS service %s on %s can run on one engine only (SE group %s, max_se %s): '
                            'if it fails, that site stops answering and clients wait for the other site. A second '
                            'engine (max_se 2) removes that' % (v.get('name'), site, grp_name, grp.get('max_se')))
            elif grp.get('ha_mode') != 'HA_MODE_LEGACY_ACTIVE_STANDBY' and int(grp.get('min_scaleout_per_vs') or 1) < 2:
                msgs.append('NOTE  the DNS service %s on %s runs on one engine at a time (SE group %s, '
                            'min_scaleout_per_vs %s): 2 keeps a second engine answering' % (
                                v.get('name'), site, grp_name, grp.get('min_scaleout_per_vs') or 1))
    others = [s for s in lives if s != leader_site]
    if others:
        msgs.append('NOTE  the leader is %s. If its controller is lost, every site keeps answering DNS, but no GSLB '
                    'change is possible until %s is made leader on its own controller' % (leader_site, others[0]))
    return ok, g, msgs


def gslb_template(cfg, leader):
    name = str(cfg.get('gslb_template_service') or '')
    if not name:
        return None
    t = leader.find('gslbservice', name)
    if not t:
        raise ValueError('gslb_template_service %s does not exist on the leader' % name)
    return t


TEMPLATE_APP_SPECIFIC = ('health_monitor_refs', 'application_persistence_profile_ref', 'pki_profile_ref')
DOWN_RESPONSES = {'all_records': 'GSLB_SERVICE_DOWN_RESPONSE_ALL_RECORDS', 'none': 'GSLB_SERVICE_DOWN_RESPONSE_NONE',
                  'empty': 'GSLB_SERVICE_DOWN_RESPONSE_EMPTY', 'fallback_ip': 'GSLB_SERVICE_DOWN_RESPONSE_FALLBACK_IP'}
# A GSLB monitor the tool makes: TCP from each site's DNS engines to a member's
# own service port. Down after 3 failed checks 10 seconds apart; up again only
# after 3 good ones, so a member that flaps does not pull traffic back and forth.
GSLB_MONITOR_TIMING = {'send_interval': 10, 'receive_timeout': 4, 'failed_checks': 3, 'successful_checks': 3}
# Settings a GSLB service must keep as the config (or template) has them.
GSLB_SETTINGS = ('down_response', 'health_monitor_refs', 'controller_health_status_enabled', 'pool_algorithm',
                 'site_persistence_enabled', 'health_monitor_scope', 'num_dns_ip')


def gslb_down_response(cfg):
    """gslb_down_response: what DNS answers when every member is down.
    all_records (the default) returns every member anyway, so a monitoring
    fault cannot take an application out of DNS on its own; none, empty, or
    fallback_ip:<address>."""
    v = str(cfg.get('gslb_down_response') or 'all_records').strip().lower()
    kind, _, ip = v.partition(':')
    if kind not in DOWN_RESPONSES:
        raise ValueError('gslb_down_response %s: use one of %s' % (v, ', '.join(sorted(DOWN_RESPONSES))))
    out = {'type': DOWN_RESPONSES[kind]}
    if kind == 'fallback_ip':
        if not ip.strip():
            raise ValueError('gslb_down_response fallback_ip needs an address: fallback_ip:10.1.2.3')
        out['fallback_ip'] = ip4(ip.strip())
    return out


def gslb_monitor_mode(cfg):
    """gslb_health_monitor: tcp (the default: a TCP monitor to each service's
    own port, made by this tool), none (the site controllers' view only), or
    the name of a federated monitor on the leader."""
    return str(cfg.get('gslb_health_monitor') or 'tcp').strip()


def site_priorities(cfg, sites=None):
    """site -> the priority its GSLB pools get, and the active site (the one
    GSLB answers with while its member is up). gslb_priority_<site> sets them
    (unset: 20 for the first site, 10 for the next). gslb_active_site is the
    datacenter toggle: that site gets the highest of those priorities and the
    others keep their order below it, so site_a 20 / site_b 10 with gslb_active_site:
    site_b becomes site_b 20 / site_a 10, on every GSLB service this tool made, flipped
    applications included."""
    sites = list(sites or sites_of(cfg))
    base = {}
    for i, s in enumerate(sites):
        v = site_conf(cfg, s)['priority']
        base[s] = int(v) if v not in (None, '') else (20 if i == 0 else max(10 - (i - 1), 1))
    active = str(cfg.get('gslb_active_site') or '').strip()
    if not active:
        return base, max(sites, key=lambda s: (base[s], -sites.index(s)))
    if active not in sites:
        raise ValueError('gslb_active_site %s is not in avi_sites (%s)' % (active, ', '.join(sites)))
    vals = sorted(base.values(), reverse=True)
    if len(set(vals)) == 1:
        vals[0] += 10  # equal priorities share traffic; the active site must stand above them
    order = [active] + sorted((s for s in sites if s != active), key=lambda s: (-base[s], sites.index(s)))
    return dict(zip(order, vals)), active


def gslb_settings_text(cfg, sites):
    """The GSLB service settings in words, for every plan."""
    eff, active = site_priorities(cfg, sites)
    prio = ', '.join('%s %s' % (s, eff[s]) for s in sites) + '; %s active%s' % (
        active, ' (gslb_active_site)' if cfg.get('gslb_active_site') else '')
    mode = gslb_monitor_mode(cfg)
    health = ('the site controllers and a TCP check from the DNS engines to each service\'s port every %ds '
              '(down after %d failures, up after %d successes)' % (
                  GSLB_MONITOR_TIMING['send_interval'], GSLB_MONITOR_TIMING['failed_checks'],
                  GSLB_MONITOR_TIMING['successful_checks'])) if mode.lower() == 'tcp' else \
        'the site controllers only' if mode.lower() == 'none' else 'the site controllers and monitor %s' % mode
    down = str(cfg.get('gslb_down_response') or 'all_records').lower()
    return ('active/standby by priority (%s); TTL %ss; health from %s; when every member is down, %s; %s failback'
            % (prio, cfg.get('gslb_ttl') or 'the DNS service\'s', health,
               'all records are returned' if down == 'all_records' else 'the answer is %s' % down,
               'manual' if truthy(cfg.get('gslb_manual_resume', 'false')) else 'automatic'))


def gslb_body(cfg, name, domains, members, template, gslb_obj, monitors=None):
    """members: site -> {cluster_uuid, vs_uuid, ip, cloud_uuid, priority}.
    The service-wide settings come from the config, with best-practice
    defaults (or from gslb_template_service, when one is named); then the
    name, the domains, one group per site with that site's virtual service as
    its member, and the TTL and priorities, where the config's always win.
    monitors: the health monitor references it gets."""
    if template:
        body = copy.deepcopy(template)
        for k in ('uuid', 'url', '_last_modified', 'tenant_ref', 'created_by', 'description', 'markers'):
            body.pop(k, None)
        # Monitors and persistence describe the template's own application.
        # The service-wide behaviour is copied; these are not.
        for k in TEMPLATE_APP_SPECIFIC:
            body.pop(k, None)
        body['site_persistence_enabled'] = False
        if cfg.get('gslb_down_response'):
            body['down_response'] = gslb_down_response(cfg)
    else:
        # Active/standby by priority, health from the site controllers and
        # the DNS engines' own checks together (both must say UP; a site whose
        # controller cannot be reached is judged by the checks alone).
        body = {'controller_health_status_enabled': True,
                'down_response': gslb_down_response(cfg),
                'health_monitor_scope': 'GSLB_SERVICE_HEALTH_MONITOR_ALL_MEMBERS',
                'is_federated': True, 'pool_algorithm': 'GSLB_SERVICE_ALGORITHM_PRIORITY',
                'site_persistence_enabled': False, 'use_edns_client_subnet': True,
                'wildcard_match': False, 'num_dns_ip': 1}
    if monitors:
        body['health_monitor_refs'] = list(monitors)
    tgroups = {}
    for tg in (template or {}).get('groups') or []:
        for m in tg.get('members') or []:
            tgroups.setdefault(m.get('cluster_uuid'), tg)
    groups = []
    for site, m in members:
        tg = tgroups.get(m['cluster_uuid'])
        g = copy.deepcopy(tg) if tg else {'algorithm': 'GSLB_ALGORITHM_ROUND_ROBIN', 'enabled': True}
        g.pop('description', None)
        tm = (g.get('members') or [{}])[0] if tg else {}
        member = dict((k, v) for k, v in tm.items() if k in ('ratio', 'enabled', 'resolve_fqdn_to_v6'))
        member.setdefault('ratio', 1)
        member.setdefault('enabled', True)
        member.update({'cluster_uuid': m['cluster_uuid'], 'vs_uuid': m['vs_uuid'], 'ip': ip4(m['ip'])})
        if m.get('cloud_uuid'):
            member['cloud_uuid'] = m['cloud_uuid']
        g['members'] = [member]
        g['name'] = '%s-%s' % (name, site)
        if not tg or m.get('priority_override'):
            g['priority'] = int(m['priority'])
        if truthy(cfg.get('gslb_manual_resume', 'false')):
            g['manual_resume'] = True  # a member that went down stays out until someone re-enables it
        groups.append(g)
    body.update({'name': name, 'domain_names': sorted(domains), 'groups': groups, 'enabled': True})
    ttl = cfg.get('gslb_ttl')
    if ttl not in (None, ''):
        body['ttl'] = int(ttl)
    return body


def service_port(vs):
    """The port a GSLB monitor checks for a member: 443 where it has it,
    else its lowest."""
    ports = sorted(set(int(s['port']) for s in (vs or {}).get('services') or [] if s.get('port')))
    return 443 if 443 in ports else (ports[0] if ports else None)


def admits_listed_only(nsp):
    """A network security policy that ends in deny-all (0.0.0.0/0): it admits
    only the clients it lists, so it refuses the GSLB DNS engines' checks."""
    for r in (nsp or {}).get('rules') or []:
        ci = (r.get('match') or {}).get('client_ip') or {}
        if r.get('enable', True) is not False and r.get('action') == 'NETWORK_SECURITY_POLICY_ACTION_TYPE_DENY' \
                and ci.get('match_criteria', 'IS_IN') == 'IS_IN' \
                and any(str((x.get('ip_addr') or {}).get('addr')) == '0.0.0.0' and int(x.get('mask') or 0) == 0
                        for x in ci.get('prefixes') or []):
            return True
    return False


def gslb_monitor_name(cfg, port):
    return '%s-tcp-%d' % (str(cfg.get('gslb_label') or 'gslb'), port)


def gslb_monitor_fits(hm, port):
    return (hm.get('type') == 'HEALTH_MONITOR_TCP' and hm.get('is_federated') is True
            and int(hm.get('monitor_port') or 0) == port)


def gslb_settings_moved(cur, body):
    """The settings of an existing GSLB service that differ from what it should have."""
    out = []
    for k in GSLB_SETTINGS:
        if k not in body:
            continue
        want, have = body[k], cur.get(k)
        if k == 'health_monitor_refs':
            # By uuid: the leader names a reference (…/uuid#name), an object's own url it does not.
            want = sorted(uuid_of(x) or x for x in want or [])
            have = sorted(uuid_of(x) or x for x in have or [])
            if want != have:
                out.append(k)
        elif have is not None and not same_value(want, have):
            out.append(k)  # a setting the leader does not return is not a difference
    return out


def members_np(svc):
    """members_of without the priorities: who the members are."""
    return sorted((m.get('cluster_uuid'), m.get('vs_uuid'), (m.get('ip') or {}).get('addr'))
                  for g in svc.get('groups') or [] for m in g.get('members') or [])


def members_of(svc):
    # With the group priority: a service someone flipped to site_b is not UNCHANGED.
    return sorted((m.get('cluster_uuid'), m.get('vs_uuid'), (m.get('ip') or {}).get('addr'), g.get('priority'))
                  for g in svc.get('groups') or [] for m in g.get('members') or [])


def flag_test_services(lives, leader_site, g):
    dns_uuids = set()
    for s in (g or {}).get('sites') or []:
        for dv in s.get('dns_vses') or []:
            dns_uuids.add(dv.get('dns_vs_uuid'))
    try:
        svcs = lives[leader_site]['client'].listing('gslbservice')
    except RuntimeError:
        return
    for s in svcs:
        if any(m.get('vs_uuid') in dns_uuids for grp in s.get('groups') or [] for m in grp.get('members') or []):
            print('    NOTE  GSLB service %s has the DNS service itself as a member; it is a test '
                  'service and should be deleted' % s.get('name'))


def gslb_services_converge(cfg, rows, lives, leader_site, g, checks_ok, commit, journal, registry,
                           pending=None, adopt=False, owners=None, rewrite=False):
    """One GSLB service per blue VIP with every name that points at it. Names
    are only ever added; members, priorities and TTL follow the config until
    one of the service's names is flipped, and from then on only with
    --rewrite-gslb, so a failover or maintenance change on the leader stands.
    gslb_hold leaves a service exactly as it is, and a same-named service this
    tool did not make is left alone unless it is adopted."""
    adopt_pats = [str(p) for p in as_list(cfg.get('avi_adopt'))]
    adopted = []
    leader = lives[leader_site]['client']
    subs = gslb_zone_names(cfg)
    hold = [str(p) for p in as_list(cfg.get('gslb_hold'))]
    sites = sites_of(cfg)
    groups = {}
    for r in rows:
        if r['action'] in ('PUBLISH', 'MOVED') and r.get('gslb_fqdn'):
            groups.setdefault(r['gslb_service'] or r['member_vs'], []).append(r)
    template = gslb_template(cfg, leader)
    existing = leader.objects('gslbservice')
    owner = {}
    for n, s in existing.items():
        for d in s.get('domain_names') or []:
            owner[d] = n
    eff_prio, active_site = site_priorities(cfg, sites)
    toggle = str(cfg.get('gslb_active_site') or '').strip()
    prio_default = {sites[0]: 20}
    for i, s in enumerate(sites[1:]):
        prio_default[s] = max(10 - i, 1)
    ttl_cfg = cfg.get('gslb_ttl')
    states, todo, nsps = {}, [], None
    # The data-plane monitor each service gets: one per service port, made
    # here on the leader and federated, or the one gslb_health_monitor names.
    mode = gslb_monitor_mode(cfg)
    hms = leader.objects('healthmonitor') if mode.lower() != 'none' else {}
    new_monitors, monitor_problem = {}, None
    if mode.lower() not in ('tcp', 'none'):
        named = hms.get(mode)
        if not named or named.get('is_federated') is not True:
            monitor_problem = ('gslb_health_monitor %s is not a federated monitor on %s' % (mode, leader_site))

    def monitors_for(member):
        if mode.lower() == 'none':
            return [], None
        if mode.lower() != 'tcp':
            return ([hms[mode]['url']], None) if not monitor_problem else ([], monitor_problem)
        port = service_port(lives[leader_site]['vs'].get(member)) or next(
            (service_port(lives[s]['vs'].get(member)) for s in sites if lives[s]['vs'].get(member)), None)
        if not port:
            return [], None  # not staged anywhere yet; its monitor comes with it
        hm_name = gslb_monitor_name(cfg, port)
        hm = hms.get(hm_name)
        if hm and not gslb_monitor_fits(hm, port):
            return [], ('healthmonitor %s on %s is not a federated TCP monitor to port %d; rename it, or set '
                        'gslb_health_monitor' % (hm_name, leader_site, port))
        if hm:
            return [hm['url']], None
        new_monitors[hm_name] = port
        return ['pending:%s' % hm_name], None

    print('')
    print('  GSLB services on %s: %s' % (leader_site, ('settings from %s, with the config\'s priorities (%s; %s '
                                                     'active%s), TTL and monitors' % (
                                                         template['name'],
                                                         ', '.join('%s %s' % (s_, eff_prio[s_]) for s_ in sites),
                                                         active_site, ' (gslb_active_site)' if toggle else ''))
                                        if template else gslb_settings_text(cfg, sites)))
    for name, grp in sorted(groups.items()):
        members = sorted(set(r['member_vs'] for r in grp))
        domains = sorted(set(r['gslb_fqdn'] for r in grp))
        problems, waiting, mlist = [], [], []
        refs, why_not = monitors_for(members[0]) if members else ([], None)
        if why_not:
            problems.append(why_not)
        # A member that admits listed clients only would refuse the DNS
        # engines' checks and read as down: its health comes from the site
        # controllers alone (the service and its pool, as each site sees them).
        nsp_name = ref_name((lives[leader_site]['vs'].get(members[0]) or {}).get('network_security_policy_ref')) \
            if members else None
        controller_only = None
        if nsp_name and mode.lower() == 'tcp':
            if nsps is None:
                try:
                    nsps = leader.objects('networksecuritypolicy')
                except RuntimeError:
                    nsps = {}
            if admits_listed_only(nsps.get(nsp_name)):
                controller_only = nsp_name
                refs = []
        if len(members) != 1:
            problems.append('names disagree on the member: %s' % ', '.join(members))
        for d in domains:
            if not any(d.endswith('.' + s) for s in subs):
                problems.append('%s is under no GSLB subdomain' % d)
            if owner.get(d) and owner[d] != name:
                problems.append('%s already belongs to GSLB service %s' % (d, owner[d]))
        for s in sites:
            lv = lives[s]
            vs = lv['vs'].get(members[0]) if members else None
            ip = site_vip(lv, members[0]) if members else None
            if not vs or not ip:
                if members and members[0] in (pending or {}).get(s, ()):
                    waiting.append(s)
                else:
                    problems.append('%s is not staged on %s' % (members[0] if members else '?', s))
                continue
            set_in_cfg = lv['conf']['priority'] not in (None, '') or bool(toggle)
            prio = eff_prio.get(s, prio_default.get(s, 10))
            # A priority in the config wins over the template's, so a template
            # flipped to site_b for a test does not flip every service with it.
            mlist.append((s, {'cluster_uuid': lv['cluster_uuid'], 'vs_uuid': vs['uuid'], 'ip': ip,
                              'cloud_uuid': lv['cloud_uuid'], 'priority': prio, 'priority_override': set_in_cfg}))
        detail = ''
        if problems:
            state, detail = 'BLOCKED', '; '.join(problems)
        elif waiting:
            state = 'UPDATE' if name in existing else 'CREATE'
            detail = '%s, once staged on %s' % (' '.join(domains), ', '.join(waiting))
        elif name in existing and matches(name, hold):
            state, detail = 'HOLD', 'gslb_hold: left as it is'
        elif name in existing and not registry.owns(leader_site, 'gslbservice', name, existing[name].get('uuid')) \
                and not (adopt or matches('gslbservice/' + name, adopt_pats)):
            state, detail = 'KEPT', 'on %s, not made by this tool; left as it is (--adopt hands it over)' % leader_site
        else:
            u = existing[name].get('uuid') if name in existing else None
            if u and registry.claimed(leader_site, 'gslbservice', name, u):
                adopted.append((name, u, 'added'))
            elif u and not registry.owns(leader_site, 'gslbservice', name, u):
                adopted.append((name, u, 'adopted'))
            body = gslb_body(cfg, name, domains, mlist, template, g, refs)
            if not refs and (mode.lower() == 'none' or controller_only):
                body['health_monitor_refs'] = []
            add = []
            if name in existing:
                cur = existing[name]
                add = sorted(set(domains) - set(cur.get('domain_names') or []))
                moved = members_of(cur) != members_of(body)
                ttl_moved = ttl_cfg not in (None, '') and str(cur.get('ttl')) != str(int(ttl_cfg))
                settings = gslb_settings_moved(cur, body)
                why_green = sorted((owners or {}).get(members[0], ())) if members else []
                # The datacenter toggle moves a flipped application too: only its
                # priorities are written; everything else stays as the leader has it.
                prio_only = bool(toggle) and moved and members_np(cur) == members_np(body) and bool(why_green) \
                    and not rewrite
                if prio_only:
                    others = [x for x in ('ttl %s' % cur.get('ttl') if ttl_moved else '', ', '.join(settings)) if x]
                    state = 'ACTIVE'
                    detail = '%s active (gslb_active_site): %s%s%s' % (
                        active_site, ', '.join('%s %s' % (s_, m_['priority']) for s_, m_ in mlist),
                        ('; + %s' % ' '.join(add)) if add else '',
                        ('; %s kept as the leader has them: green owns it since %s' % (
                            ' and '.join(others), fmt_list(why_green, 2))) if others else '')
                elif (moved or ttl_moved or settings) and why_green and not rewrite:
                    kept = '%s kept as the leader has %s: green owns it since %s (--rewrite-gslb writes them)' % (
                        ' and '.join(x for x in ('members and priorities' if moved else '',
                                                 'ttl %s' % cur.get('ttl') if ttl_moved else '',
                                                 ', '.join(settings)) if x),
                        'them' if (moved or settings) else 'it', fmt_list(why_green, 2))
                    if add:
                        state, detail = 'ADD NAMES', '%s; %s' % (' '.join(add), kept)
                    else:
                        state, detail = 'DIFFERS', kept
                elif moved or ttl_moved or settings:
                    state = 'UPDATE'
                    detail = ', '.join(x for x in (
                        'members and priorities' if moved else '',
                        'ttl %s -> %s' % (cur.get('ttl'), ttl_cfg) if ttl_moved else '',
                        ', '.join(settings),
                        '+ %s' % ' '.join(add) if add else '') if x)
                elif add:
                    state, detail = 'ADD NAMES', ' '.join(add)
                else:
                    state = 'UNCHANGED'
            else:
                state, detail = 'CREATE', '%s  %s' % (' '.join(domains), ' '.join('%s=%s' % (s, m['ip']) for s, m in mlist))
            if state in ('CREATE', 'UPDATE', 'ADD NAMES', 'ACTIVE'):
                todo.append((state, name, body, add))
        states[name] = state
        if controller_only:
            detail = ('%s; ' % detail if detail else '') + (
                'health from the site controllers only: %s admits listed clients only, so it would refuse the DNS '
                'engines\' checks' % controller_only)
        print('    %-10s %-28s %s' % (state, name, detail))
    if not groups:
        print('    no names to publish')
    for hm_name, port in sorted(new_monitors.items()):
        if not commit:
            print('    %-10s %-28s TCP from the DNS engines to port %d, federated' % ('ADD', hm_name, port))
    if commit:
        # Handed over (--adopt), or made by a run whose reply never came.
        for name, u, how in adopted:
            registry.record(leader_site, 'gslbservice', name, u, how)
            journal.record(state=how, type='gslbservice', name=name, site=leader_site, uuid=u)
    if not commit or not todo:
        return states
    if not checks_ok:
        print('    STOP: GSLB services are not written until the checks above pass.')
        for _, name, _, _ in todo:
            states[name] = 'BLOCKED'
        return states
    # Each monitor a service needs, before the service that uses it.
    made_hm = {}
    for hm_name, port in sorted(new_monitors.items()):
        if not any(('pending:%s' % hm_name) in (b.get('health_monitor_refs') or []) for _, _, b, _ in todo):
            continue
        hm_body = dict(GSLB_MONITOR_TIMING, name=hm_name, type='HEALTH_MONITOR_TCP', monitor_port=port,
                       is_federated=True, description='GSLB: TCP from the DNS engines to port %d. Made by '
                                                      'avi_migrate' % port)
        journal.record(state='attempt', op='add', type='healthmonitor', name=hm_name, site=leader_site)
        registry.intend(leader_site, 'healthmonitor', hm_name)
        try:
            made = leader.request('POST', '/api/healthmonitor', hm_body)
        except RuntimeError as exc:
            if re.search(r'HTTP 4\d\d', str(exc)):
                registry.abandon(leader_site, 'healthmonitor', hm_name)
            raise
        made_hm['pending:%s' % hm_name] = made['url']
        registry.record(leader_site, 'healthmonitor', hm_name, uuid_of(made['url']), 'added')
        journal.record(state='accepted', op='add', type='healthmonitor', name=hm_name, site=leader_site,
                       url=made['url'])
        print('    written    healthmonitor %s' % hm_name)
    for _, _, b, _ in todo:
        if b.get('health_monitor_refs'):
            b['health_monitor_refs'] = [made_hm.get(x, x) for x in b['health_monitor_refs']]
    # Names are only ever added: a name that was flipped to one keeps resolving.
    for state, name, body, add in todo:
        journal.record(state='attempt', type='gslbservice', name=name, op=state, add=add)
        if state == 'CREATE':
            registry.intend(leader_site, 'gslbservice', name)
            try:
                made = leader.request('POST', '/api/gslbservice', body)
            except RuntimeError as exc:
                if re.search(r'HTTP 4\d\d', str(exc)):
                    registry.abandon(leader_site, 'gslbservice', name)
                raise
            registry.record(leader_site, 'gslbservice', name, uuid_of((made or {}).get('url')), 'added')
        elif state == 'ADD NAMES':
            made = leader.request('PATCH', '/api/gslbservice/%s' % existing[name]['uuid'],
                                  {'add': {'domain_names': add}})
        elif state == 'ACTIVE':
            cur = existing[name]
            put = copy.deepcopy(cur)
            by_cl = dict((m.get('cluster_uuid'), grp.get('priority')) for grp in body['groups']
                         for m in grp.get('members') or [])
            for grp in put.get('groups') or []:
                cl = next((m.get('cluster_uuid') for m in grp.get('members') or []), None)
                if cl in by_cl:
                    grp['priority'] = by_cl[cl]
            put['domain_names'] = sorted(set(cur.get('domain_names') or []) | set(add))
            made = leader.request('PUT', '/api/gslbservice/%s' % cur['uuid'], put)
        else:
            cur = existing[name]
            put = copy.deepcopy(cur)
            put['domain_names'] = sorted(set(cur.get('domain_names') or []) | set(body['domain_names']))
            put['groups'] = body['groups']
            if 'ttl' in body:
                put['ttl'] = body['ttl']
            for k in GSLB_SETTINGS:
                if k in body:
                    put[k] = body[k]
            made = leader.request('PUT', '/api/gslbservice/%s' % cur['uuid'], put)
        journal.record(state='accepted', type='gslbservice', name=name, url=(made or {}).get('url'))
        print('    written    %s' % name)
    return states


# ---------------------------------------------------------------- live state

def se_group_raise(cfg, site, c, commit, journal):
    """avi_se_max_se_<site> / avi_se_max_vs_per_se_<site>: what the site's SE
    group (avi_se_group_<site>) is raised to, so every service can be placed.
    Only ever raised, never lowered. Returns ({group: fields}, lines)."""
    grp = site_conf(cfg, site)['se_group']
    want = {}
    for k in ('max_se', 'max_vs_per_se'):
        v = cfg.get('avi_se_%s_%s' % (k, site))
        if v not in (None, ''):
            want[k] = int(v)
    if not want or not grp:
        return {}, []
    o = c.find('serviceenginegroup', grp)
    if not o:
        return {}, ['WARNING  SE group %s is not on %s; avi_se_*_%s not applied' % (grp, site, site)]
    up = dict((k, v) for k, v in want.items() if v > int(o.get(k) or 0))
    lines = ['NOTE     SE group %s keeps %s %s: avi_se_%s_%s (%s) is lower, and it is never lowered'
             % (grp, k, o.get(k), k, site, v) for k, v in sorted(want.items()) if v < int(o.get(k) or 0)]
    if not up:
        return {}, lines
    text = ', '.join('%s %s -> %s' % (k, o.get(k), v) for k, v in sorted(up.items()))
    if commit:
        body = c.request('GET', '/api/serviceenginegroup/%s' % o['uuid'])
        if not isinstance(body, dict) or body.get('uuid') != o['uuid']:
            raise RuntimeError('SE group %s on %s did not read back whole; nothing was changed' % (grp, site))
        body.update(up)
        journal.record(state='attempt', type='serviceenginegroup', name=grp, site=site, raised=up)
        c.request('PUT', '/api/serviceenginegroup/%s' % o['uuid'], body)
        journal.record(state='accepted', type='serviceenginegroup', name=grp, site=site, raised=up)
        lines.append('RAISED   SE group %s: %s' % (grp, text))
    else:
        lines.append('RAISE    SE group %s: %s (avi_se_*_%s)' % (grp, text, site))
    return {grp: up}, lines


def capacity(c, live, want, raised=None):
    """Live virtual services per SE group once `want` (name -> enabled) is
    applied, against what each group can place (as raised by the config).
    Returns the groups over."""
    try:
        segs = c.objects('serviceenginegroup')
    except RuntimeError:
        return [], []
    for g_, fields in (raised or {}).items():
        if g_ in segs:
            segs[g_] = dict(segs[g_], **fields)
    per, lines, over = {}, [], []
    for n, v in live.items():
        on = want.get(n, v.get('enabled', True) is not False)
        if on and v.get('type') != 'VS_TYPE_VH_CHILD':
            g = ref_name(v.get('se_group_ref'))
            per[g] = per.get(g, 0) + 1
    for g, cnt in sorted(per.items(), key=lambda x: str(x[0])):
        o = segs.get(g) or {}
        if o.get('max_se') and o.get('max_vs_per_se'):
            cap = int(o['max_se']) * int(o['max_vs_per_se'])
            units = int(o['max_se']) * int(o.get('vcpus_per_se') or 1)
            lines.append('%s: %d enabled of %d it can place (max_se %s x max_vs_per_se %s; %d licence units at full size)'
                         % (g, cnt, cap, o['max_se'], o['max_vs_per_se'], units))
            if cnt > cap:
                over.append(g)
    return over, lines


LIVE_WORD = {(True, True): 'live', (True, False): 'placed', (False, True): 'off', (False, False): 'off'}


def live_converge(cfg, site, bundle, scope_vs, lives, owners, commit, journal, registry, pending=(), force=False,
                  allow_offline=False, live_flipped=False):
    """Each virtual service this tool made at one site live or staged, as
    avi_live_<site> says. A live service is taken out of service only with
    --allow-offline. A flipped application is left as green has it, so a
    failover test or maintenance on green stands; --live-flipped may bring
    one up, and nothing ever takes one down. One this tool did not make is
    never touched."""
    sc = site_conf(cfg, site)
    inv = bundle['inventory']
    lv = lives[site]
    c, live = lv['client'], lv['vs']
    include_disabled = [str(p) for p in as_list(cfg.get('avi_live_include_disabled'))]
    changes, kept, held, counts, waiting = [], [], [], {}, 0
    for n in sorted(scope_vs, key=lambda n: (inv['vs'][n]['type'] == 'VS_TYPE_VH_CHILD', n)):
        v = live.get(n)
        if not v:
            waiting += 1 if n in pending else 0
            continue
        if not registry.owns(site, 'virtualservice', n, v.get('uuid')):
            counts['foreign'] = counts.get('foreign', 0) + 1
            continue
        blue = inv['vs'][n]
        have = (v.get('enabled', True) is not False, v.get('traffic_enabled', True) is not False)
        if matches(n, sc['live']):
            if not blue['enabled'] and not matches(n, include_disabled):
                want, why = (False, False), 'disabled on blue'
            elif blue.get('traffic', True) is False and not matches(n, include_disabled):
                want, why = (True, False), 'placed only: takes no traffic on blue'
            else:
                want, why = (True, True), 'live'
        else:
            want, why = (False, False), 'staged: not in avi_live_%s' % site
        if have == want:
            counts['unchanged'] = counts.get('unchanged', 0) + 1
            continue
        if n in owners:
            down = have[0] and not (want[0] and want[1])
            if down or not live_flipped:
                kept.append('%s stays %s: green owns it (%s)%s' % (
                    n, LIVE_WORD[have], fmt_list(sorted(owners[n]), 2),
                    '' if down else '; --live-flipped makes it %s' % LIVE_WORD[want]))
                continue
        if have == (True, True) and not allow_offline:
            # Out of service is a decision for the operator, not a side effect:
            # a flip this tool cannot see would otherwise take traffic down.
            held.append((n, why))
            continue
        changes.append((n, have, want, why))
    want_map = dict((n, w[0]) for n, _, w, _ in changes)
    raised, raise_lines = se_group_raise(cfg, site, c, commit, journal)
    over, lines = capacity(c, live, want_map, raised)
    ons = [x for x in changes if x[2][0] and x[2][1]]
    print('')
    shown = 'all' if sc['live'] == ['*'] else ', '.join(sc['live']) if sc['live'] else 'none (staged only)'
    print('  live %s  avi_live_%s: %s' % (site, site, shown))
    print('      to set %d (%d live, %d otherwise)   unchanged %d%s%s%s' % (
        len(changes), len(ons), len(changes) - len(ons), counts.get('unchanged', 0),
        ('   held live %d' % len(held)) if held else '',
        ('   after staging %d' % waiting) if waiting else '',
        ('   not made by this tool, left alone %d' % counts['foreign']) if counts.get('foreign') else ''))
    for n, have, want, why in changes[:40]:
        print('      %-10s %-30s %s' % ('LIVE' if want == (True, True) else 'PLACED' if want[0] else 'OFF', n, why))
    if len(changes) > 40:
        print('      ... %d more' % (len(changes) - 40))
    for k in kept:
        print('      KEPT       %s' % k)
    for n, why in held[:40]:
        print('      HELD       %-30s stays live (%s): taking a live service offline needs --allow-offline' % (n, why))
    if len(held) > 40:
        print('      HELD       ... %d more' % (len(held) - 40))
    for ln in raise_lines:
        print('      %s' % ln)
    for ln in lines:
        print('      capacity   %s' % ln)
    if over and not force:
        print('      STOP: %s would hold more than it can place. Nothing changes here until max_se and licence '
              'units allow it (--force overrides).' % ', '.join(over))
        return {'changed': 0, 'stopped': True, 'pending': len(changes), 'held': len(held)}
    if not commit:
        return {'changed': 0, 'stopped': False, 'pending': len(changes), 'held': len(held)}
    # Parents before children going live; children before parents going off.
    ups = [x for x in changes if x[2][0]]
    downs = list(reversed([x for x in changes if not x[2][0]]))
    for n, have, want, why in downs + ups:
        journal.record(state='attempt', type='virtualservice', name=n, site=site, enabled=want[0], traffic_enabled=want[1])
        c.request('PATCH', '/api/virtualservice/%s' % live[n]['uuid'],
                  {'replace': {'enabled': want[0], 'traffic_enabled': want[1]}})
        journal.record(state='accepted', type='virtualservice', name=n, site=site)
    print('      set %d' % len(changes))
    return {'changed': len(changes), 'stopped': False, 'pending': 0, 'held': len(held)}


# ---------------------------------------------------------------- DNS

QTYPE = {'A': 1, 'CNAME': 5, 'SOA': 6, 'PTR': 12}


def dns_query(server, name, timeout=3.0, port=53, qtype=1):
    """One query over UDP, A unless qtype says otherwise. Returns {'rcode',
    'aa', 'a', 'cname', 'soa', 'ptr', 'ttl'} or {'error'}."""
    tid = random.randint(0, 0xFFFF)
    try:
        qname = b''.join(bytes([len(p)]) + p.encode('ascii') for p in name.rstrip('.').split('.')) + b'\x00'
    except (UnicodeEncodeError, ValueError):
        return {'error': 'name is not ASCII'}
    pkt = struct.pack('>HHHHHH', tid, 0x0100, 1, 0, 0, 0) + qname + struct.pack('>HH', qtype, 1)
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    s.settimeout(timeout)
    try:
        s.sendto(pkt, (server, port))
        data, _ = s.recvfrom(4096)
    except (socket.timeout, OSError) as exc:
        return {'error': 'no answer (%s)' % exc.__class__.__name__}
    finally:
        s.close()
    return parse_dns(data, tid)


def _read_name(data, off):
    labels, jumped, end, hops = [], False, off, 0
    while True:
        if off >= len(data) or hops > 64:
            raise ValueError('malformed name')
        ln = data[off]
        if ln & 0xC0 == 0xC0:
            ptr = ((ln & 0x3F) << 8) | data[off + 1]
            if not jumped:
                end = off + 2
            off, jumped, hops = ptr, True, hops + 1
            continue
        if ln == 0:
            if not jumped:
                end = off + 1
            return '.'.join(labels), end
        labels.append(data[off + 1:off + 1 + ln].decode('ascii', 'replace'))
        off += 1 + ln


def parse_dns(data, tid=None):
    try:
        rid, flags, qd, an, _, _ = struct.unpack('>HHHHHH', data[:12])
        if tid is not None and rid != tid:
            return {'error': 'mismatched reply'}
        off = 12
        for _ in range(qd):
            _, off = _read_name(data, off)
            off += 4
        # aa: the server holds the zone itself. soa: the owners of the SOA
        # records answered, which is the zone when the name asked is its apex.
        # ttl: the first record's, which is the name's own.
        out = {'rcode': flags & 0xF, 'aa': bool(flags & 0x0400), 'a': [], 'cname': [], 'soa': [], 'ptr': [],
               'ttl': None}
        for _ in range(an):
            owner, off = _read_name(data, off)
            rtype, _, ttl, rdlen = struct.unpack('>HHIH', data[off:off + 10])
            off += 10
            rdata = data[off:off + rdlen]
            if rtype == 1 and rdlen == 4:
                out['a'].append(socket.inet_ntoa(rdata))
            elif rtype == 5:
                out['cname'].append(_read_name(data, off)[0])
            elif rtype == 6:
                out['soa'].append(owner.lower().rstrip('.'))
            elif rtype == 12:
                out['ptr'].append(_read_name(data, off)[0].lower().rstrip('.'))
            if rtype in (1, 5) and out['ttl'] is None:
                out['ttl'] = ttl
            off += rdlen
        return out
    except (struct.error, ValueError, IndexError) as exc:
        return {'error': 'unparseable reply (%s)' % exc}


def answer_text(ans):
    if ans.get('error'):
        return ans['error']
    if ans.get('rcode'):
        return 'rcode %d' % ans['rcode']
    return ' '.join(ans.get('a') or []) or 'no address'


# ---------------------------------------------------------------- readiness and the flip list

FLIP_COLUMNS = ['fqdn', 'state', 'zone', 'host', 'blue_ip', 'gslb_fqdn', 'gslb_service', 'vip']
FLIP_TAIL = ['dns_vips', 'ttl', 'record', 'blue_vsvip', 'member_vs', 'note']
STATE_ORDER = ['READY', 'NOT READY', 'MOVED', 'MANUAL', 'SKIP', 'FOLLOWS', 'NONAME']


def vs_oper(lv, name, cache):
    k = (lv['conf']['site'], name)
    if k not in cache:
        v = lv['vs'].get(name)
        if not v:
            cache[k] = 'missing'
        else:
            try:
                rt = lv['client'].request('GET', '/api/virtualservice/%s/runtime/' % v['uuid'])
            except RuntimeError:
                rt = None
            rt = rt[0] if isinstance(rt, list) and rt else rt
            cache[k] = str(((rt or {}).get('oper_status') or {}).get('state', '?')).replace('OPER_', '')
    return cache[k]


def verify_rows(cfg, rows, lives, services):
    """The state of every name. READY: every site holds its member, its GSLB
    service holds the name, and every GSLB DNS service (and every server in
    dns_servers, which proves the delegation) answers the active site's VIP
    (the first site's, unless gslb_active_site names another)."""
    sites = sites_of(cfg)
    first = site_priorities(cfg, sites)[1]
    dns_vips = [str(x) for x in as_list(cfg.get('gslb_dns_vips'))]
    ad, _ = resolvers(cfg)
    cache = {}
    for r in rows:
        for s in sites:
            r['vip_%s' % s] = (site_vip(lives[s], r['member_vs']) or '') if r.get('member_vs') else ''
        r['vip'] = r.get('vip_%s' % first, '')
        r['dns_vips'] = ' '.join(dns_vips)
        if r['action'] not in ('PUBLISH', 'MOVED'):
            r['state'] = r['action']
            continue
        problems, notes = [], []
        missing = [s for s in sites if not r['vip_%s' % s]]
        if missing:
            problems.append('not staged on %s' % ', '.join(missing))
        svc = (services or {}).get(r['gslb_service'] or r['member_vs'])
        if not svc:
            problems.append('GSLB service %s does not exist yet' % (r['gslb_service'] or r['member_vs']))
        elif r['gslb_fqdn'] not in (svc.get('domain_names') or []):
            problems.append('GSLB service %s does not hold %s yet' % (svc.get('name'), r['gslb_fqdn']))
        if not problems:
            if not dns_vips:
                problems.append('gslb_dns_vips is not set, so the GSLB DNS services cannot be asked')
            if not ad:
                problems.append('no DNS server to prove the delegation through: set dns_servers')
            for ns in dns_vips:
                ans = dns_query(ns, r['gslb_fqdn'])
                got = ans.get('a', [])
                if len(got) > 1 and r['vip'] in got:
                    # Every member marked down, and answered anyway (all_records):
                    # names work, but GSLB is not choosing a site.
                    problems.append('%s answers every site (%s): GSLB has every member down. Do the DNS engines\' '
                                    'checks reach the VIPs?' % (ns, answer_text(ans)))
                elif got != [r['vip']]:
                    problems.append('%s answers %s, not %s' % (ns, answer_text(ans), r['vip']))
            for ns in ad:
                if ns in dns_down(ad, gslb_zone_list(cfg)):
                    problems.append('%s (clients\' DNS) does not answer from this host' % ns)
                    break
                ans = dns_query(ns, r['gslb_fqdn'])
                if ans.get('a', []) != [r['vip']] and r['vip'] not in ans.get('a', []):
                    problems.append('%s (clients\' DNS) answers %s: is %s delegated?'
                                    % (ns, answer_text(ans), r['gslb_fqdn'].split('.', 1)[1]))
                    break
        if not missing:
            for s in [x for x in sites if x != first]:
                st = vs_oper(lives[s], r['member_vs'], cache)
                if st != 'UP':
                    notes.append('no failover yet: %s member %s' % (s, st))
        if r['action'] == 'MOVED':
            r['state'] = 'MOVED'
            r['note'] = '; '.join((['FLIPPED, BUT ' + '; '.join(problems)] if problems else []) + notes) or 'flipped'
        else:
            r['state'] = 'NOT READY' if problems else 'READY'
            r['note'] = '; '.join(problems + notes + ([r['note']] if r.get('note') else []))
    return rows


def write_flips(cfg, rows):
    """The flip list Invoke-DnsFlip.ps1 reads: one row per name."""
    sites = sites_of(cfg)
    cols = FLIP_COLUMNS + ['vip_%s' % s for s in sites] + FLIP_TAIL
    out = []
    for r in rows:
        zone = r.get('dns_zone') or r.get('zone') or ''
        fq = r.get('fqdn') or ''
        d = dict(r)
        d['zone'] = zone
        d['host'] = fq[:-(len(zone) + 1)] if zone and fq.endswith('.' + zone) else ''
        d.setdefault('state', r['action'])
        out.append(d)
    out.sort(key=lambda d: (STATE_ORDER.index(d['state']) if d['state'] in STATE_ORDER else 99,
                            d['fqdn'] or d.get('blue_vsvip', '')))
    path = artefact(cfg, 'dns-flips', 'csv')
    tmp = path + '.tmp'
    with open(tmp, 'w', newline='') as fh:
        w = csv.DictWriter(fh, fieldnames=cols, extrasaction='ignore')
        w.writeheader()
        for d in out:
            w.writerow(d)
    os.replace(tmp, path)
    counts = {}
    for d in out:
        counts[d['state']] = counts.get(d['state'], 0) + 1
    return path, counts, out


def report_flips(path, counts, rows, limit=20):
    print('')
    print('  flip list  %s' % path)
    print('      %s' % '   '.join('%s %d' % (s, counts[s]) for s in STATE_ORDER if counts.get(s)))
    for st in ('NOT READY', 'MOVED'):
        shown = [r for r in rows if r['state'] == st and (st == 'NOT READY' or 'FLIPPED, BUT' in r.get('note', ''))]
        for r in shown[:limit]:
            print('      %-9s %-34s %s' % (st, r['fqdn'], r['note']))
        if len(shown) > limit:
            print('      %-9s ... %d more in the flip list' % (st, len(shown) - limit))


# ---------------------------------------------------------------- converge and status

def export_gaps(cfg, dns_rows):
    """The gslb_zones the DNS export holds no record of (an exported zone
    always has its SOA and NS). Which of their names are flipped cannot be
    known from it."""
    zones = [str(z).lower().rstrip('.') for z in as_list(cfg.get('gslb_zones'))]
    seen = set()
    for r in dns_rows:
        z, _ = split_zone(r['fqdn'], zones)
        if z:
            seen.add(z)
    return [z for z in zones if z not in seen]


def read_names(cfg, args, bundle, lives, services):
    """(rows, path, zones missing from the export); rows is None without an export.
    A discovered file has no gaps to speak of: it never claims a whole zone,
    and every name the flip list can hold is in it (discover only adds)."""
    names_path = getattr(args, 'names', None) or cfg.get('gslb_names')
    if not names_path or not os.path.exists(str(names_path)):
        return None, names_path, []
    sites = sites_of(cfg)
    dns_rows = load_dns(str(names_path))
    rows = build_rows(cfg, bundle, dns_rows, services, first_members(services, lives, sites[0]), green_vips(lives))
    return rows, names_path, ([] if names_discovered(names_path) else export_gaps(cfg, dns_rows))


# ---------------------------------------------------------------- names from blue's own configuration

DISCOVERED_MARK = '# discovered by avi_migrate.py'


def names_discovered(path):
    """True when the names file was written by discover, not exported on a DC."""
    try:
        with open(str(path), encoding='utf-8-sig') as fh:
            for line in fh:
                if line.strip():
                    return line.startswith(DISCOVERED_MARK)
    except OSError:
        pass
    return False


def is_gslb_name(fq, zones, label):
    _, host = split_zone(fq, zones)
    return bool(host) and (host == label or host.endswith('.' + label))


def clean_name(fq, zones, label):
    """A host name in gslb_zones, lower case; None for anything else (a
    wildcard, a display name, a GSLB name)."""
    fq = str(fq or '').strip().lower().rstrip('.')
    if not re.match(r'^[a-z0-9_-]+(\.[a-z0-9_-]+)+$', fq) or is_gslb_name(fq, zones, label):
        return None
    return fq if split_zone(fq, zones)[0] else None


def candidate_names(cfg, inv, zones, label):
    """Name -> the blue VIPs whose own configuration mentions it: the VsVip's
    DNS info, the names on its services' certificates, the SNI domains of
    their child services and the Host names their policies and DataScripts
    match; and gslb_discover_names, tied to no VIP."""
    out = {}
    for vsvip, v in sorted(inv['vsvip'].items()):
        if not v['vs']:
            continue  # nothing migrated uses this VIP
        found = list(v['fqdns'])
        for n in v['vs']:
            for m in [n] + inv['vs'][n]['children']:
                mv = inv['vs'].get(m) or {}
                for cn in mv.get('certs') or []:
                    found.extend(inv['certs'].get(cn, {}).get('names', []))
                found.extend(mv.get('domains') or [])
                found.extend(mv.get('hosts') or [])
        for fq in found:
            fq = clean_name(fq, zones, label)
            if fq:
                out.setdefault(fq, set()).add(vsvip)
    for fq in as_list(cfg.get('gslb_discover_names')):
        fq = clean_name(fq, zones, label)
        if fq:
            out.setdefault(fq, set())
    return out


def reverse_name(ip):
    return '.'.join(reversed(str(ip).split('.'))) + '.in-addr.arpa'


def zone_of(server, fq, floor, cache):
    """The zone that holds fq on server, found the way resolvers find it: the
    nearest name at or above fq, no higher than floor, whose SOA query answers
    an SOA of its own. (zone, held by this server) or (None, False)."""
    n = fq
    while True:
        k = (server, n)
        if k not in cache:
            cache[k] = dns_query(server, n, qtype=QTYPE['SOA'])
        ans = cache[k]
        if ans.get('error') or ans.get('rcode') not in (0, 3):
            return None, False
        if n in ans.get('soa', []):
            return n, bool(ans.get('aa'))
        if n == floor or '.' not in n:
            return None, False
        n = n.split('.', 1)[1]


_DNS_ASKED = {}  # server -> whether it answers this host at all; asked once per run


def dns_down(servers, zones):
    """The DNS servers that do not answer this host at all, each asked once per
    run with a short timeout, so a DC out of reach costs two seconds rather
    than a timeout for every name."""
    probe = (list(zones) or ['localhost'])[0]
    for ns in servers:
        if ns not in _DNS_ASKED:
            _DNS_ASKED[ns] = not dns_query(ns, probe, timeout=2.0, qtype=QTYPE['SOA']).get('error')
    return set(ns for ns in servers if not _DNS_ASKED[ns])


def discover_names(cfg, bundle, path):
    """The names file, from blue's configuration and what the DNS servers
    answer; see discover_cmd. Returns what it found, for the report."""
    zones = [str(z).lower().rstrip('.') for z in as_list(cfg.get('gslb_zones'))]
    if not zones:
        raise ValueError('gslb_zones is not set in the config')
    label = str(cfg.get('gslb_label') or 'gslb')
    carried = []
    if os.path.exists(path):
        if not names_discovered(path):
            raise ValueError('%s is a DNS export from a DC (or was written by hand), which holds every name, so '
                             'discover never replaces it; converge uses it as it is' % path)
        carried = [r for r in load_dns(path) if r['type'] in ('A', 'CNAME')]
    everyone, source = resolvers(cfg)
    if not everyone:
        raise ValueError('no DNS server to ask: set dns_servers to the DCs clients use')
    down = dns_down(everyone, zones)
    servers = [ns for ns in everyone if ns not in down]
    if not servers:
        raise ValueError('none of %s (%s) answers from this host, so no name can be confirmed; nothing was '
                         'changed' % (', '.join(everyone), source))
    inv = bundle['inventory']
    ip2vsvip = dict((ip, n) for n, v in inv['vsvip'].items() for ip in v['ips'])
    ip2vsvip.update(vip_aliases(cfg, inv))
    cands = candidate_names(cfg, inv, zones, label)
    from_config = len(cands)

    # A VIP's reverse record can name what nothing on blue mentions. It is only
    # a lead: the name goes in only if its own record points back.
    by_ptr = []
    for ip, vsvip in sorted(ip2vsvip.items()):
        if not inv['vsvip'][vsvip]['vs']:
            continue
        for ns in servers:
            ans = dns_query(ns, reverse_name(ip), qtype=QTYPE['PTR'])
            if ans.get('error') or ans.get('rcode') not in (0, 3):
                continue
            for fq in ans.get('ptr', []):
                fq = clean_name(fq, zones, label)
                if fq and fq not in cands:
                    cands[fq] = {vsvip}
                    by_ptr.append(fq)
            break

    prev = {}
    for r in carried:
        prev.setdefault(r['fqdn'], []).append(r)
    queue = sorted(n for n in set(cands) | set(prev) if split_zone(n, zones)[0])
    queued = set(queue)
    records, zcache, said = [], {}, {}
    found = dict((k, []) for k in ('blue', 'follows', 'flipped', 'elsewhere', 'absent', 'unanswered', 'foreign'))
    while queue:
        fq = queue.pop(0)
        answers = []
        for ns in servers:
            ans = dns_query(ns, fq)
            if not ans.get('error') and ans.get('rcode') in (0, 3):
                answers.append((ns, ans))
        if not answers:
            found['unanswered'].append(fq)
            said[fq] = 'no DNS server answered'
            records.extend(prev.get(fq, []))  # keep what was known; converge asks again
            continue
        # A CNAME anywhere wins, as a flip seen by one DC counts in converge.
        target = next((a['cname'][0].lower().rstrip('.') for _, a in answers if a.get('cname')), None)
        ips = []
        if not target:
            for _, a in answers:
                ips.extend(ip for ip in a.get('a', []) if ip not in ips)
        if not target and not ips:
            found['absent'].append(fq)
            said[fq] = 'not in DNS'
            continue
        if target:
            said[fq] = 'CNAME %s' % target
        else:
            said[fq] = '-> %s%s' % (' '.join(ips), '' if any(ip in ip2vsvip for ip in ips) else ' (not a blue VIP)')
        ns, first = next((x for x in answers if x[1].get('cname') or x[1].get('a')), answers[0])
        floor = split_zone(fq, zones)[0]
        zone, held = zone_of(ns, fq, floor, zcache)
        if zone and not held:
            found['foreign'].append('%s (%s)' % (fq, zone))
        rec = {'fqdn': fq, 'ttl': first.get('ttl'), 'zone': zone or floor}
        if target:
            records.append(dict(rec, type='CNAME', data=target))
            if is_gslb_name(target, zones, label):
                found['flipped'].append(fq)
                continue
            found['follows'].append(fq)
            if target not in queued and split_zone(target, zones)[0]:
                queue.append(target)
                queued.add(target)
            continue
        for ip in ips:
            records.append(dict(rec, type='A', data=ip))
        found['blue' if any(ip in ip2vsvip for ip in ips) else 'elsewhere'].append(fq)

    os.makedirs(os.path.dirname(os.path.abspath(path)), exist_ok=True)
    tmp = path + '.tmp'
    with open(tmp, 'w', newline='', encoding='utf-8') as fh:
        fh.write('%s %s from %s and %s: the names blue\'s services mention, not a zone export\n'
                 % (DISCOVERED_MARK, now(), bundle['source'], ', '.join(servers)))
        w = csv.writer(fh, quoting=csv.QUOTE_ALL, lineterminator='\n')
        w.writerow(['fqdn', 'type', 'data', 'ttl', 'zone'])
        for r in sorted(records, key=lambda x: (x['zone'], x['fqdn'], x['type'], x['data'])):
            w.writerow([r['fqdn'], r['type'], r['data'], '' if r['ttl'] is None else r['ttl'], r['zone']])
    os.replace(tmp, path)

    a_recs = {}
    for r in records:
        if r['type'] == 'A' and r['data'] not in a_recs.setdefault(r['fqdn'], []):
            a_recs[r['fqdn']].append(r['data'])
    inferred = inferred_aliases(cfg, inv, a_recs, ip2vsvip)
    named = set(ip2vsvip[r['data']] for r in records if r['type'] == 'A' and r['data'] in ip2vsvip)
    named.update(inferred.values())
    named.update(v for fq in found['flipped'] for v in cands.get(fq, ()))
    inuse = sorted(n for n, v in inv['vsvip'].items() if v['vs'])
    nameless = [n for n in inuse if n not in named]
    # For each VIP no name points at: the names blue gives it, and what DNS said
    # of each, following a CNAME one step.
    why = {}
    for vip in nameless:
        why[vip] = []
        for fq in sorted(f for f, vs in cands.items() if vip in vs):
            text = said.get(fq, 'not asked')
            t = text[len('CNAME '):] if text.startswith('CNAME ') else None
            if t and said.get(t, '').startswith('->'):
                text = '%s %s' % (text, said[t])
            why[vip].append('%s %s' % (fq, text) if not text.startswith('not') and not text.startswith('no ')
                            else '%s: %s' % (fq, text))
    return {'path': path, 'zones': zones, 'records': records, 'found': found, 'asked': len(queued),
            'servers': servers, 'down': sorted(down), 'source': source, 'from_config': from_config,
            'by_ptr': by_ptr, 'inuse': inuse, 'nameless': nameless, 'why': why, 'inferred': inferred}


def fronted_lines(inferred):
    """What discover took to stand in front of a blue VIP, and why."""
    if not inferred:
        return []
    return ['elsewhere  %d addresses that are not blue VIPs serve names blue gives one VIP (another load balancer, or '
            'a NAT): those names get GSLB with that VIP, and a flip moves each from there. gslb_infer_alias: false '
            'turns this off' % len(inferred)] + [
        '           %-15s -> %s' % (ip, vip) for ip, vip in sorted(inferred.items(), key=lambda x: x[1])]


def nameless_lines(inv, d):
    """One line per VIP in use that no DNS name points at, with why, and what to do."""
    out = []
    for vip in d['nameless']:
        v = inv['vsvip'][vip]
        ev = d['why'].get(vip) or []
        more = (' (+%d more)' % (len(ev) - 6)) if len(ev) > 6 else ''
        out.append('%-28s %-15s %-26s %s' % (vip, ' '.join(v['ips']), ' '.join(v['vs'])[:26],
                                             ('blue names it: %s%s' % ('; '.join(ev[:6]), more)) if ev
                                             else 'no name on blue'))
    if out:
        out.append('A name pointing at an address that fronts the VIP (a NAT, say): gslb_vip_alias: '
                   '[<that address>=<VsVip>]. A name blue does not carry: gslb_discover_names. A VIP clients reach by '
                   'address only: GSLB cannot move them')
    return out


def discover_cmd(cfg, args):
    """Read-only. The DNS names of blue's services, from blue's own
    configuration and the reverse records of its VIPs, each confirmed with the
    DNS servers clients use, written as the names file (gslb_names) so
    converge can build GSLB without an export from a DC. It only ever adds: a
    name it wrote before is asked again and kept, so no name the flip list
    held can drop out."""
    _DNS_ASKED.clear()
    names_cfg = cfg.get('gslb_names')
    path = str(getattr(args, 'out', None) or names_cfg or artefact(cfg, 'dns-records', 'csv'))
    banner('DISCOVER  %s   read-only: blue\'s configuration, and what the DNS servers answer' % site_tag(cfg))
    if getattr(args, 'export', None):
        bundle = load_bundle(args.export)
        print('  blue       %s (%s), from %s exported %s' % (bundle['source'], bundle.get('source_version'),
                                                             args.export, bundle.get('exported_at')))
    else:
        bundle, where, _ = read_blue(cfg)
        print('  blue       %s (%s) read now; saved to %s' % (bundle['source'], bundle.get('source_version'), where))
    d = discover_names(cfg, bundle, path)
    inv, found, records, nameless, inuse = bundle['inventory'], d['found'], d['records'], d['nameless'], d['inuse']
    print('  names      %d on blue\'s services in %s (VsVip DNS info, certificate names, SNI domains, Host names '
          'policies and DataScripts match%s); '
          '%d more from the VIPs\' reverse records'
          % (d['from_config'], ', '.join(d['zones']), ', gslb_discover_names' if cfg.get('gslb_discover_names') else '',
             len(d['by_ptr'])))
    if d['down']:
        print('  WARNING    %s did not answer from this host and was not asked' % ', '.join(d['down']))
    print('  asked      %s (%s) about %d names' % (', '.join(d['servers']), d['source'], d['asked']))
    print('  found      %d at a blue VIP, %d following another name, %d flipped to a GSLB name, %d elsewhere, '
          '%d not in DNS' % (len(found['blue']), len(found['follows']), len(found['flipped']),
                             len(found['elsewhere']), len(found['absent'])))
    if found['elsewhere']:
        print('             elsewhere (not a blue VIP): %s' % fmt_list(found['elsewhere'], 8))
    if found['unanswered']:
        print('  WARNING    no DNS server answered for %s; what was known of them is kept, and a run later asks '
              'again' % fmt_list(found['unanswered'], 8))
    if found['foreign']:
        print('  NOTE       %s: in zones these DNS servers do not hold themselves; the flip script cannot change '
              'them there' % fmt_list(found['foreign'], 6))
    for line in fronted_lines(d['inferred']):
        print('  %s' % line)
    print('  VIPs       %d of %d blue VIPs in use have a name%s' % (
        len(inuse) - len(nameless), len(inuse), '; no DNS name points at these, and why:' if nameless else ''))
    for line in nameless_lines(inv, d):
        print('             %s' % line)
    same = names_cfg and os.path.abspath(str(names_cfg)) == os.path.abspath(path)
    print('  wrote      %s: %d records%s' % (path, len(records), '; converge reads it (gslb_names)' if same
                                             else '; give it to converge with --names, or set gslb_names'))
    print('             Enough to build GSLB. Before names are flipped, a DC export (Export-DnsRecords.ps1) is the '
          'complete list:')
    print('             it also sees other records sharing a name, and names pointed at green by hand.')
    return 0


def converge_cmd(cfg, args):
    commit = bool(args.commit)
    _SECRETS.clear()  # asked once per run, and only for this run
    _NO_SECRET.clear()
    _DNS_ASKED.clear()
    all_sites = sites_of(cfg)
    if args.site and args.site not in all_sites:
        raise ValueError('--site %s is not in avi_sites' % args.site)
    sites = [args.site] if args.site else all_sites
    leader_site = str(cfg.get('gslb_leader') or all_sites[0])
    if leader_site not in all_sites:
        raise ValueError('gslb_leader %s is not in avi_sites' % leader_site)
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')
    journal = Journal(args.journal or (artefact(cfg, 'converge-' + stamp, 'jsonl') if commit else None))
    ignore = ignore_fields(cfg)
    registry = Registry(cfg)
    banner('CONVERGE  %s   %s' % (site_tag(cfg), 'COMMIT' if commit else 'DRY RUN: nothing is written without --commit'))
    try:
        # Blue, read now unless a saved export is given.
        if args.export:
            bundle = load_bundle(args.export)
            print('  blue       %s (%s), from %s exported %s' % (bundle['source'], bundle.get('source_version'),
                                                                 args.export, bundle.get('exported_at')))
        else:
            bundle, where, _ = read_blue(cfg)
            print('  blue       %s (%s) read now; saved to %s' % (bundle['source'], bundle.get('source_version'), where))
        inv = bundle['inventory']
        print('             %d virtual services, %d objects, %d left out'
              % (len(inv['vs']), len(bundle['objects']), len(bundle.get('excluded', {}))))
        busy = dict((t, n) for t, n in (bundle.get('tenants') or {}).items() if n)
        if busy:
            print('             WARNING: other tenants hold virtual services this tool does not move: %s'
                  % ', '.join('%s (%d)' % x for x in sorted(busy.items())))

        # Green, and the names. Each target must be a cluster of its own, and
        # none of them blue: host names can alias, cluster uuids cannot.
        lives = dict((s, live_site(cfg, s)) for s in all_sites)
        blue_cluster = bundle.get('source_cluster') or cluster_uuid(connect(cfg, 'source'))
        seen = {}
        for s in all_sites:
            u = lives[s]['cluster_uuid']
            if u and u == blue_cluster:
                raise ValueError('avi_target_host_%s (%s) is blue\'s own cluster %s; refusing to write to it'
                                 % (s, lives[s]['client'].host, u))
            if u and u in seen:
                raise ValueError('avi_target_host_%s and avi_target_host_%s reach the same cluster %s'
                                 % (seen[u], s, u))
            seen[u] = s
        leader = lives[leader_site]['client']
        try:
            services = leader.objects('gslbservice')
        except RuntimeError:
            services = {}
        rows, names_path, gaps = read_names(cfg, args, bundle, lives, services)
        made_gslb = [n for (t, n) in registry.at(leader_site) if t == 'gslbservice']
        if rows is None and names_path and not getattr(args, 'names', None) and as_list(cfg.get('gslb_zones')) \
                and not made_gslb:
            # A first build: no names yet, and no GSLB service this tool made,
            # so no name can have been flipped. Find them as discover does, and
            # this run builds GSLB once everything else is written.
            try:
                d_ = discover_names(cfg, bundle, str(names_path))
                print('  names      discovered from blue\'s configuration, confirmed with %s: %d records, for %d of '
                      '%d VIPs in use; written to %s' % (', '.join(d_['servers']), len(d_['records']),
                                                         len(d_['inuse']) - len(d_['nameless']), len(d_['inuse']),
                                                         names_path))
                if d_['down']:
                    print('             %s did not answer from this host and was not asked' % ', '.join(d_['down']))
                for line in fronted_lines(d_['inferred']):
                    print('  %s' % line)
                if d_['nameless']:
                    print('             no DNS name points at %d VIPs, so they get no GSLB service (their services are '
                          'still built at every site). Why, for each:' % len(d_['nameless']))
                    for line in nameless_lines(bundle['inventory'], d_):
                        print('             %s' % line)
                rows, names_path, gaps = read_names(cfg, args, bundle, lives, services)
            except ValueError as exc:
                print('  names      not discovered: %s' % exc)
        allow_update = True
        discovered = bool(rows is not None and names_discovered(names_path))
        if rows is None:
            rows = []
            allow_update = False
            print('  names      no DNS names at %s. GSLB and the flip list wait for them, and UPDATEs are withheld:'
                  % names_path)
            print('             without them the tool cannot tell which applications are flipped. From this host:')
            print('             python3 avi_migrate.py discover --config %s' % (getattr(args, 'config', None)
                                                                             or '<env file>'))
            print('             (or on a DC: .\\Export-DnsRecords.ps1 -Zones %s)'
                  % ','.join(str(z) for z in as_list(cfg.get('gslb_zones'))))
            if made_gslb:
                print('             This tool has made GSLB services, so a name could be flipped: it no longer finds '
                      'the names on its own. Put back the names file it had, or run discover')
        else:
            cands = sum(1 for r in rows if r['action'] in ('PUBLISH', 'MOVED') and r['gslb_fqdn'])
            servers, source, asked = check_flips(cfg, rows)
            counts = {}
            for r in rows:
                counts[r['action']] = counts.get(r['action'], 0) + 1
            print('  names      %s: %s' % (names_path, ', '.join('%d %s' % (counts[k], k) for k in
                                                                ['PUBLISH', 'MOVED', 'MANUAL', 'SKIP', 'FOLLOWS', 'NONAME']
                                                                if counts.get(k))))
            fr = {}
            for r in rows:
                if r.get('fronted'):
                    fr.setdefault(r['blue_ip'], set()).add(r['fqdn'])
            if fr:
                print('  elsewhere  %d names blue carries are served today from %d addresses that are not blue VIPs (another '
                      'load balancer, or a NAT): they get GSLB with their VIPs, and a flip moves each from there (flip '
                      'list notes)' % (sum(len(v) for v in fr.values()), len(fr)))
            print('  flips      asked %s (%s) about %d names: %d answered; %d names flipped in all'
                  % (', '.join(servers) or 'no DNS server', source, cands, asked, counts.get('MOVED', 0)))
            unknown = [r for r in rows if r['action'] == 'PUBLISH' and r['gslb_fqdn'] and not r.get('flip_checked')]
            held = [r for r in unknown if r.get('gslb_held')]
            if held and not args.trust_export:
                print('             %d names not answered by every DNS server: their applications are treated as '
                      'flipped (FROZEN) until all answer, or --trust-export' % len(held))
            if len(unknown) > len(held):
                print('             %d names not answered by every DNS server, but no GSLB service answers for their '
                      'GSLB names yet, so none of them can be flipped' % (len(unknown) - len(held)))
            if gaps:
                allow_update = False
                print('             the export holds no record of %s: which of their names are flipped cannot be '
                      'known, so UPDATEs are withheld.' % ', '.join(gaps))
                print('             Export them (.\\Export-DnsRecords.ps1 -Zones %s), or append their records.'
                      % ','.join(str(z) for z in as_list(cfg.get('gslb_zones'))))
            if discovered:
                print('             discovered from blue\'s configuration, not a zone export: a name pointed at '
                      'green by hand is seen only in a DC export')
        # Taking a service offline needs the whole picture: a name the export
        # does not hold could be flipped, and its application would go down.
        allow_offline = bool(getattr(args, 'allow_offline', False)) and allow_update and not discovered
        if getattr(args, 'allow_offline', False) and not allow_offline:
            print('             --allow-offline is not used: without a DNS export of every zone (from a DC; '
                  'discovered names are not one) a flipped application could go unseen')
        owners = owned_by_green(cfg, bundle, rows, args.trust_export)
        frozen = frozen_objects(cfg, bundle, owners)
        if truthy(cfg.get('avi_sync_moved', 'false')) and owners:
            print('             avi_sync_moved: true; flipped applications are still updated from blue')

        # Every site: the desired objects against what it holds.
        scope, scope_info = select_scope(cfg, args, bundle)
        key_probe = probe_keys(cfg, bundle, scope)
        plans = dict((s, plan_site(cfg, s, bundle, scope, key_probe, frozen, ignore, registry, args.adopt))
                     for s in sites)
        for s in sites:
            report_site(plans[s], getattr(args, 'verbose', False))
        plan_csv = write_plan_csv(cfg, plans)
        print('')
        print('  plan       %s' % plan_csv)
        results = {}
        if commit:
            # Every value blue will not hand back, asked now, before the first
            # write. One not given skips its object and what uses it; the rest
            # is written.
            writable = [plans[s] for s in sites if not plans[s]['site_blocks']]
            asks = sorted(set('%s/%s' % (op['type'], op['name']) for p_ in writable for op in p_['ops']
                              if op.get('secrets')))
            if asks:
                print('')
                print('  secrets    %s: what blue does not hand back, asked once for every site' % fmt_list(asks, 6))
                for (t, n, pth), why in sorted(gather_secrets(writable).items()):
                    print('             %s/%s %s: it is skipped, with what uses it' % (t, n, why))
            for s in sites:
                if plans[s]['site_blocks']:
                    continue
                print('')
                print('  writing %s' % s)
                results[s] = apply_site(cfg, plans[s], journal, ignore, registry, allow_update)
                vips = record_vips(cfg, s, connect(cfg, 'target', s),
                                   [op['name'] for op in plans[s]['ops'] if op['type'] == 'vsvip'])
                r = results[s]
                print('      %d added, %d updated%s%s; %d VIP addresses recorded in %s'
                      % (r['added'], r['updated'], ', %d withheld' % r['withheld'] if r['withheld'] else '',
                         ', %d already there' % r['present'] if r['present'] else '', len(vips),
                         artefact(cfg, 'vips', site=s)))
                for line in r['still']:
                    print('      WARNING  ' + line)
                for label, why in r['refused']:
                    print('      REFUSED  %-40s %s' % (label, why))
                if r['refused']:
                    print('      %d refused by %s and skipped; fix what the lines above say and run again'
                          % (len(r['refused']), s))
            lives = dict((s, live_site(cfg, s)) for s in all_sites)
        pending = {} if commit else dict(
            (s, set(e['name'] for e in plans[s]['entries'].values()
                    if e['type'] == 'virtualservice' and e['state'] == 'ADD')) for s in sites)

        # GSLB on the leader.
        gslb_ok, gslb_states, gslb_fails, gslb_adds = True, {}, 0, 0
        if args.site:
            print('')
            print('  GSLB       not converged with --site; run without it')
        elif rows:
            print('')
            print('  GSLB  leader %s (%s)' % (leader_site, leader.host))
            gslb_ok, g, msgs = gslb_checks(cfg, lives, leader_site, commit, journal)
            for m in msgs:
                print('    ' + m)
            gslb_fails = sum(1 for m in msgs if m.startswith('FAIL'))
            gslb_adds = sum(1 for m in msgs if m.startswith('ADD '))
            flag_test_services(lives, leader_site, g)
            gslb_states = gslb_services_converge(cfg, rows, lives, leader_site, g, gslb_ok or not commit,
                                                 commit, journal, registry, pending, args.adopt, owners,
                                                 getattr(args, 'rewrite_gslb', False))
            if commit:
                services = leader.objects('gslbservice')

        # Live state, per site.
        scope_vs = set(split_key(k)[1] for k in scope if k.startswith('virtualservice/'))
        live_results = {}
        for s in sites:
            if plans[s]['site_blocks']:
                continue
            live_results[s] = live_converge(cfg, s, bundle, scope_vs, lives, owners, commit, journal, registry,
                                            pending.get(s, ()), args.force, allow_offline,
                                            getattr(args, 'live_flipped', False))
        if commit and any(v['changed'] for v in live_results.values()):
            lives = dict((s, live_site(cfg, s)) for s in all_sites)

        # Every name, and the flip list.
        flip_counts = {}
        if rows:
            verify_rows(cfg, rows, lives, services)
            path, flip_counts, ordered = write_flips(cfg, rows)
            report_flips(path, flip_counts, ordered)
            if commit and any(v['changed'] for v in live_results.values()):
                print('      services just set live take a minute to come up: status shows the latest')
    finally:
        journal.close()

    blocked = sum(1 for p in plans.values() for e in p['entries'].values() if e['state'] == 'BLOCKED')
    blocked += sum(1 for p in plans.values() if p['site_blocks'])
    blocked += sum(1 for st in gslb_states.values() if st == 'BLOCKED')
    blocked += sum(v.get('held', 0) for v in live_results.values())
    blocked += gslb_fails
    blocked += sum(len(r.get('refused') or []) for r in results.values())
    stopped = any(v['stopped'] for v in live_results.values())
    changes = sum(1 for p in plans.values() for e in p['entries'].values() if e['state'] in ('ADD', 'UPDATE'))
    changes += sum(1 for st in gslb_states.values() if st in ('CREATE', 'UPDATE', 'ADD NAMES', 'ACTIVE'))
    changes += gslb_adds
    changes += sum(v['pending'] for v in live_results.values())
    print('')
    if commit:
        print('  %s. %d blocked%s.%s' % ('Written' if not blocked else 'Written, except what is blocked', blocked,
                                       ', live state stopped at a capacity limit' if stopped else '',
                                       ' Journal: %s' % journal.path if journal.path else ''))
        return 1 if (blocked or stopped) else 0
    print('  DRY RUN: %d changes to make, %d blocked. Nothing written; add --commit.' % (changes, blocked))
    if blocked or stopped:
        return 1
    return 2 if changes else 0


def write_plan_csv(cfg, plans):
    path = artefact(cfg, 'converge-plan', 'csv')
    tmp = path + '.tmp'
    with open(tmp, 'w', newline='') as fh:
        w = csv.writer(fh)
        w.writerow(['site', 'state', 'type', 'name', 'detail'])
        for s, p in sorted(plans.items()):
            for b in p['site_blocks']:
                w.writerow([s, 'BLOCKED', 'site', s, b])
            order = ['BLOCKED', 'UPDATE', 'FROZEN', 'KEPT', 'ADD', 'MAPPED', 'UNCHANGED']
            for e in sorted(p['entries'].values(), key=lambda e: (order.index(e['state']), e['type'], e['name'])):
                w.writerow([s, e['state'], e['type'], e['name'], e['detail']])
            for x in p.get('product') or []:
                w.writerow([s, 'CHANGED', '', '', x])
            for x in p['warnings']:
                w.writerow([s, 'WARNING', '', '', x])
    os.replace(tmp, path)
    return path


def status_cmd(cfg, args):
    """Read-only: every name's state now, and a fresh flip list. Uses the last
    export of blue, so it does not log in to blue."""
    _DNS_ASKED.clear()
    bundle = load_bundle(args.export or artefact(cfg, 'avi-export'))
    sites = sites_of(cfg)
    leader_site = str(cfg.get('gslb_leader') or sites[0])
    lives = dict((s, live_site(cfg, s)) for s in sites)
    try:
        services = lives[leader_site]['client'].objects('gslbservice')
    except RuntimeError:
        services = {}
    rows, names_path, gaps = read_names(cfg, args, bundle, lives, services)
    if rows is None:
        raise ValueError('no DNS names at %s; write them from this host with discover, or with '
                         'Export-DnsRecords.ps1 on a DC' % names_path)
    check_flips(cfg, rows)
    verify_rows(cfg, rows, lives, services)
    path, counts, ordered = write_flips(cfg, rows)
    banner('STATUS  %s   blue export of %s' % (site_tag(cfg), bundle.get('exported_at')))
    if gaps:
        print('  WARNING   the DNS export holds no record of %s; their names are not in the list' % ', '.join(gaps))
    for r in ordered:
        if r['state'] in ('READY', 'NOT READY', 'MOVED'):
            print('  %-9s %-34s %-36s %s' % (r['state'], r['fqdn'], r['gslb_fqdn'],
                                            '  '.join('%s %s' % (s, r.get('vip_%s' % s) or '-') for s in sites)))
            if r.get('note') and r['state'] != 'READY':
                print('  %-9s %s' % ('', r['note']))
    report_flips(path, counts, ordered, limit=0)
    return 0


# ---------------------------------------------------------------- purge

def purge_flips(cfg, args, all_sites, leader_site, registry):
    """VS -> why it is flipped, and every object those applications use, from
    the DNS export and the last export of blue. Without them, a purge goes
    ahead only while this tool has made no GSLB service, since until then no
    name can have been flipped to one."""
    made_gslb = sorted(n for (t, n) in registry.at(leader_site) if t == 'gslbservice')
    bundle_path = getattr(args, 'export', None) or artefact(cfg, 'avi-export')
    names_path = getattr(args, 'names', None) or cfg.get('gslb_names')
    if names_path and os.path.exists(str(names_path)) and os.path.exists(bundle_path):
        bundle = load_bundle(bundle_path)
        lives = dict((s, live_site(cfg, s)) for s in all_sites)
        try:
            services = lives[leader_site]['client'].objects('gslbservice')
        except RuntimeError:
            services = {}
        rows, _, gaps = read_names(cfg, args, bundle, lives, services)
        if gaps and made_gslb:
            raise ValueError('the DNS export holds no record of %s, so which of their names are flipped cannot be '
                             'told; export every zone of gslb_zones before a purge' % ', '.join(gaps))
        servers, source, _ = check_flips(cfg, rows)
        owners = owned_by_green(cfg, bundle, rows)
        protected = {}
        for vs, why in owners.items():
            for k in closure(bundle['objects'], ['virtualservice/%s' % vs]):
                protected.setdefault(k, set()).update(why)
        print('  flips      asked %s (%s): %d applications flipped or unknown, left alone'
              % (', '.join(servers) or 'no DNS server', source, len(owners)))
        return owners, protected
    if made_gslb:
        raise ValueError('this tool has made GSLB services (%s), so a name could be flipped to one. A purge needs '
                         'the DNS export (gslb_names: from discover, or a DC) and the last export of blue to tell '
                         'which applications are flipped, and leaves those alone' % fmt_list(made_gslb, 3))
    print('  flips      no GSLB service was ever made by this tool, so no name can be flipped to one yet')
    return {}, {}


def purge_order(cand, uses):
    """What refers to something before what it refers to, so every delete is allowed."""
    after = dict((k, set(d for d in uses(o) if d in cand and d != k)) for k, o in cand.items())
    indeg = dict((k, 0) for k in cand)
    for k, ds in after.items():
        for d in ds:
            indeg[d] += 1
    ready, out = sorted(k for k, v in indeg.items() if v == 0), []
    while ready:
        k = ready.pop(0)
        out.append(k)
        for d in sorted(after[k]):
            indeg[d] -= 1
            if indeg[d] == 0:
                ready.append(d)
    return out + sorted(k for k in cand if k not in out)  # a cycle, if any, goes last


def purge_gslb(cfg, leader_site, registry, owners, commit, journal):
    """GSLB services this tool made on the leader, except a flipped application's."""
    c = connect(cfg, 'target', leader_site)
    services = c.objects('gslbservice')
    delete, keep = [], {}
    for (t, n), (u, how) in sorted(registry.at(leader_site).items()):
        s_ = services.get(n)
        if t != 'gslbservice' or not s_ or not registry.owns(leader_site, t, n, s_.get('uuid')):
            continue
        if how == 'adopted':
            keep[n] = 'on the leader before this tool (adopted)'
        elif n in owners:
            keep[n] = 'its application is flipped (%s)' % fmt_list(sorted(owners[n]), 2)
        else:
            delete.append((n, s_))
    print('')
    print('  GSLB  leader %s (%s)' % (leader_site, c.host))
    print('      DELETE   %d GSLB services this tool made%s' % (
        len(delete), (': %s' % fmt_list([n for n, _ in delete], 6)) if delete else ''))
    for n, why in sorted(keep.items()):
        print('      KEEP     gslbservice %-26s %s' % (n, why))
    failed = []
    if commit:
        for n, s_ in delete:
            journal.record(state='attempt', op='delete', type='gslbservice', name=n, site=leader_site, uuid=s_['uuid'])
            try:
                c.request('DELETE', '/api/gslbservice/%s' % s_['uuid'])
            except RuntimeError as exc:
                if 'HTTP 404' not in str(exc):
                    failed.append('gslbservice/%s: %s' % (n, str(exc)[:200]))
                    continue
            registry.record(leader_site, 'gslbservice', n, s_['uuid'], 'deleted')
            journal.record(state='accepted', op='delete', type='gslbservice', name=n, site=leader_site)
        for f in failed:
            print('      FAILED   ' + f)
    gone = set(n for n, _ in delete if not any(f.startswith('gslbservice/%s:' % n) for f in failed))
    members = {}
    for n, s_ in services.items():
        if n in gone:
            continue
        for g in s_.get('groups') or []:
            for m in g.get('members') or []:
                members[m.get('vs_uuid')] = n
    return {'delete': len(delete), 'failed': failed, 'members': members, 'gone': gone}


def purge_site(cfg, site, registry, protected, members, commit, journal, gone=()):
    """Everything this tool made at one site, in an order the controller
    accepts. Never what it did not make or was handed (--adopt), never what a
    flipped application uses, and never what something that stays still uses
    (a GSLB service that stays keeps its monitor). gone: the GSLB services this
    purge deletes, which keep nothing."""
    c = connect(cfg, 'target', site)
    mine = registry.at(site)
    live = {}
    for t in sorted(set(PORTABLE) | set(t for t, _ in mine)):
        try:
            live[t] = c.objects(t)
        except RuntimeError:
            live[t] = {}
    key_of = {}
    for t, objs in live.items():
        for n, o in objs.items():
            if o.get('uuid'):
                key_of[o['uuid']] = (t, n)

    def uses(o):
        return set(key_of[r['uuid']] for r in iter_refs(o) if r.get('uuid') in key_of and r['raw'] != o.get('url'))
    cand, keep = {}, {}
    for (t, n), (u, how) in sorted(mine.items()):
        o = live.get(t, {}).get(n)
        if t == 'gslbservice' or not o or not registry.owns(site, t, n, o.get('uuid')):
            continue  # a GSLB service goes with the leader; gone already; or replaced by another of that name
        k = '%s/%s' % (t, n)
        if how == 'adopted':
            keep[(t, n)] = 'on green before this tool (adopted)'
        elif k in protected:
            keep[(t, n)] = 'serves a flipped application (%s)' % fmt_list(sorted(protected[k]), 2)
        elif t == 'virtualservice' and o.get('uuid') in members:
            keep[(t, n)] = 'a member of GSLB service %s, which stays' % members[o['uuid']]
        else:
            cand[(t, n)] = o
    # What stays keeps everything it uses.
    changed = True
    while changed:
        changed = False
        for t, objs in live.items():
            for n, o in objs.items():
                if (t, n) in cand or (t == 'gslbservice' and n in gone):
                    continue
                for dep in uses(o):
                    if dep in cand:
                        keep[dep] = 'used by %s/%s, which stays' % (t, n)
                        del cand[dep]
                        changed = True
    order = purge_order(cand, uses)
    counts = {}
    for t, _ in order:
        counts[t] = counts.get(t, 0) + 1
    print('')
    print('  %s  %s' % (site, c.host))
    print('      DELETE   %d objects this tool made%s' % (len(order), (': %s' % ', '.join(
        '%d %s' % (v, k) for k, v in sorted(counts.items(), key=lambda x: -x[1]))) if order else ''))
    for (t, n), why in sorted(keep.items())[:40]:
        print('      KEEP     %-22s %-30s %s' % (t, n, why))
    if len(keep) > 40:
        print('      KEEP     ... %d more' % (len(keep) - 40))
    failed = []
    if commit:
        for t, n in order:
            o = cand[(t, n)]
            journal.record(state='attempt', op='delete', type=t, name=n, site=site, uuid=o['uuid'])
            try:
                c.request('DELETE', '/api/%s/%s' % (t, o['uuid']))
            except RuntimeError as exc:
                if 'HTTP 404' not in str(exc):
                    failed.append('%s/%s: %s' % (t, n, str(exc)[:200]))
                    journal.record(state='failed', op='delete', type=t, name=n, site=site)
                    continue
            registry.record(site, t, n, o['uuid'], 'deleted')
            journal.record(state='accepted', op='delete', type=t, name=n, site=site)
        print('      deleted  %d%s' % (len(order) - len(failed), ', %d failed' % len(failed) if failed else ''))
        for f in failed[:20]:
            print('      FAILED   ' + f)
    return {'delete': len(order), 'failed': failed}


def purge_cmd(cfg, args):
    """Take away what converge made, so the next converge builds it again.
    Dry run unless --commit."""
    commit = bool(args.commit)
    _DNS_ASKED.clear()
    all_sites = sites_of(cfg)
    if args.site and args.site not in all_sites:
        raise ValueError('--site %s is not in avi_sites' % args.site)
    sites = [args.site] if args.site else all_sites
    leader_site = str(cfg.get('gslb_leader') or all_sites[0])
    registry = Registry(cfg)
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')
    journal = Journal(args.journal or (artefact(cfg, 'purge-' + stamp, 'jsonl') if commit else None))
    banner('PURGE  %s   %s' % (site_tag(cfg), 'COMMIT' if commit else 'DRY RUN: nothing is deleted without --commit'))
    try:
        owners, protected = purge_flips(cfg, args, all_sites, leader_site, registry)
        if args.site:
            print('')
            print('  GSLB       left as it is with --site; its services keep their members at %s' % args.site)
            svcs = connect(cfg, 'target', leader_site).objects('gslbservice')
            g = {'delete': 0, 'failed': [], 'members': dict(
                (m.get('vs_uuid'), n) for n, s_ in svcs.items() for grp in s_.get('groups') or []
                for m in grp.get('members') or [])}
        else:
            g = purge_gslb(cfg, leader_site, registry, owners, commit, journal)
        results = dict((s_, purge_site(cfg, s_, registry, protected, g['members'], commit, journal,
                                       g.get('gone', ()))) for s_ in sites)
    finally:
        journal.close()
    total = g['delete'] + sum(r['delete'] for r in results.values())
    failed = len(g['failed']) + sum(len(r['failed']) for r in results.values())
    print('')
    print('  GSLB subdomains and DNS-profile zones the tool added stay; the next converge uses them again.')
    if commit:
        print('  Deleted %d, %d failed.%s Next: converge --commit builds it all again.'
              % (total - failed, failed, ' Journal: %s.' % journal.path if journal.path else ''))
        return 1 if failed else 0
    print('  DRY RUN: %d to delete. Nothing deleted; add --commit.' % total)
    return 2 if total else 0


# ---------------------------------------------------------------- selftest
# In-memory controllers that behave like the real ones where it matters: names
# on references only with include_name; paginated collections whose next link
# drops include_name; a name filter that matches prefixes; references that must
# point at existing objects on the same controller; fields removed in 32.1
# refused unless the request says it speaks 31.1; IPAM allocation for VIPs; a
# Tier-1 required on NSX VIPs; private keys only with export_key; and a GSLB
# leader that validates every member against the site that holds it.

class _Fake(ApiBase):
    def __init__(self, world, netloc, version, label, page=3):
        self.world, self.netloc, self.host = world, netloc, 'https://' + netloc
        self.version, self.label, self.tenant, self.page = version, label, 'admin', page
        self.db, self.keys, self.calls, self.n = {}, {}, [], 0
        self.cluster_uuid = 'cluster-%s' % label
        self.tenants, self.unserved = {}, set()
        self.rewrite = {}  # (type, field) -> fn: a field this release rewrites on the way in
        self.lose = set()  # 'type/name': the object is created, then the reply is lost
        self.refuse = {}  # 'type/name' -> why: the controller refuses the write outright
        world[label] = self

    def url(self, t, u):
        return '%s/api/%s/%s' % (self.host, t, u)

    def put(self, t, obj):
        self.n += 1
        obj = copy.deepcopy(obj)
        u = obj.get('uuid') or '%s-%s-%04d' % (t, self.label, self.n)
        obj['uuid'], obj['url'] = u, self.url(t, u)
        self.db.setdefault(t, {})[u] = obj
        return obj

    def by_name(self, t, name):
        for o in self.db.get(t, {}).values():
            if o.get('name') == name:
                return o
        raise KeyError('%s/%s on %s' % (t, name, self.label))

    def ref(self, t, name):
        return self.by_name(t, name)['url']

    def named(self, v):
        def add(s):
            r = parse_ref(s)
            if r and r['host'] == self.netloc and not r['name']:
                o = self.db.get(r['type'], {}).get(r['uuid'])
                if o:
                    return s + '#' + o['name']
            return s
        return map_refs(v, add)  # like Avi: reference fields only, never the object's own url

    def bare(self, v):
        return map_refs(v, lambda s: s.split('#', 1)[0])

    def check_refs(self, body):
        for s in ref_values(body):
            r = parse_ref(s)
            if not r:
                raise RuntimeError('HTTP 400 on %s: malformed reference %s' % (self.label, s))
            if r['host'] not in (None, self.netloc):
                raise RuntimeError('HTTP 400 on %s: reference to another controller: %s' % (self.label, s))
            if r['uuid'] not in self.db.get(r['type'], {}):
                raise RuntimeError('HTTP 400 on %s: no %s %s' % (self.label, r['type'], r['uuid']))

    def schema(self, t, body, ver):
        """32.1 as it treats a body. Told 32.1, a field it no longer has is
        unknown. Told an older release, it converts what moved and drops what
        is gone, as the first green site did, but still refuses what validate() refuses."""
        gone = [p for p in _GONE_32_1.get(t, []) + _GONE_32_1['*'] if reach(body, p)]
        if ver.startswith('32.'):
            for k in ('configpb_attributes',) + tuple(gone):
                if reach(body, k):
                    raise RuntimeError('POST /api/%s on %s: HTTP 400: {"error":"Unknown field %s"}' % (t, self.label, k))
            if t == 'virtualservice' and 'vip' in body:
                raise RuntimeError('HTTP 400 on %s: unknown field vip' % self.label)
        elif self.version.startswith('32.'):
            for p in gone:
                if p in _REFUSED_32_1:
                    continue
                for c, k in reach(body, p):
                    v = c.pop(k)
                    into, scale = _MOVED_32_1.get((t, p), (None, None))
                    if into:
                        c[into] = v * scale if scale else v
        body.pop('configpb_attributes', None)
        return body

    @staticmethod
    def masked(t, o):
        """Like the controller: a GSLB site's password is read as the placeholder."""
        if t == 'gslb':
            for st in o.get('sites') or []:
                if st.get('password'):
                    st['password'] = MASKED
        return o

    def unmask(self, new, old):
        """Like the controller: a placeholder put back keeps the value it holds."""
        if isinstance(new, dict) and isinstance(old, dict):
            for k, v in list(new.items()):
                if v == MASKED and k in old:
                    new[k] = copy.deepcopy(old[k])
                else:
                    self.unmask(v, old.get(k))
        elif isinstance(new, list) and isinstance(old, list):
            for a, b in zip(new, old):
                self.unmask(a, b)

    def validate(self, method, t, obj):
        """Checks 32.1 makes whatever version the request speaks."""
        if self.version.startswith('32.') and t == 'healthmonitor' and obj.get('type') == 'HEALTH_MONITOR_PING' \
                and obj.get('monitor_port'):
            raise RuntimeError('%s /api/healthmonitor on %s: HTTP 400: {"error":"Configuring Monitor Port is not '
                               'supported for the PING Health Monitor %s."}' % (method, self.label, obj.get('name')))
        if self.version.startswith('32.') and t == 'virtualservice' and \
                'rewritable_content_ref' in (obj.get('content_rewrite') or {}):
            raise RuntimeError('%s /api/virtualservice on %s: HTTP 400: {"error":"Invalid field '
                               'content_rewrite.rewritable_content_ref"}' % (method, self.label))
        if MASKED in json.dumps(obj):
            raise RuntimeError('%s /api/%s on %s: HTTP 400: {"error":"%s holds the placeholder %s, not a value"}'
                               % (method, t, self.label, obj.get('name'), MASKED))
        why = self.refuse.get('%s/%s' % (t, obj.get('name')))
        if why:
            raise RuntimeError('%s /api/%s on %s: HTTP 400: {"error":"%s"}' % (method, t, self.label, why))

    def defaults(self, t, obj):
        """What the target adds of its own: a field only its release has, and
        per-server defaults. None of it may ever read as a difference."""
        if self.version.startswith('32.') and t in PORTABLE:
            obj.setdefault('green_default', True)
            for s in obj.get('servers') or []:
                s.setdefault('ratio', 1)
            if t == 'virtualservice':
                obj['scaleout_ecmp'] = True  # as both green sites set it on their NSX-T clouds
            if t == 'pkiprofile':
                for c in obj.get('ca_certs') or []:
                    c['certificate'] = str(c.get('certificate') or '').replace('\r\n', '\n')
                    c['days_until_expire'] = 1000
        for (tt, f), fn in self.rewrite.items():
            if tt == t and f in obj:
                obj[f] = fn(obj[f])
        return obj

    def allocate(self, vv):
        if not vv.get('tier1_lr'):
            raise RuntimeError('HTTP 400 on %s: tier1_lr is required on an NSX-T cloud' % self.label)
        # Like IPAM: an entry without its address gets a new one, never the one
        # it held, which is only released once the update is done.
        used = set(v['ip_address']['addr'] for o in self.db.get('vsvip', {}).values()
                   for v in o.get('vip') or [] if v.get('ip_address'))
        used |= set(v['ip_address']['addr'] for v in vv.get('vip') or [] if v.get('ip_address'))
        for vip in vv.get('vip') or []:
            if not vip.get('auto_allocate_ip') or vip.get('ip_address'):
                continue  # an address already allocated stays, as on the controller
            r = parse_ref((vip.get('ipam_network_subnet') or {}).get('network_ref') or '')
            if not r:
                raise RuntimeError('HTTP 400 on %s: auto-allocation without a network' % self.label)
            rng = self.db['network'][r['uuid']]['configured_subnets'][0]['static_ip_ranges'][0]['range']
            ip, end = ipaddress.ip_address(rng['begin']['addr']), ipaddress.ip_address(rng['end']['addr'])
            while str(ip) in used:
                ip += 1
            if ip > end:
                raise RuntimeError('HTTP 400 on %s: VIP pool exhausted' % self.label)
            vip['ip_address'] = ip4(ip)
            used.add(str(ip))

    def check_gslb_service(self, body):
        g = next(iter(self.db.get('gslb', {}).values()), None)
        if not g or g.get('leader_cluster_uuid') != self.cluster_uuid:
            raise RuntimeError('HTTP 400 on %s: not the GSLB leader' % self.label)
        subs = [d['domain_name'] for d in g.get('dns_configs') or []]
        for d in body.get('domain_names') or []:
            if not any(d.endswith('.' + s) for s in subs):
                raise RuntimeError('HTTP 400: %s matches no GSLB subdomain' % d)
            for o in self.db.get('gslbservice', {}).values():
                if o.get('name') != body.get('name') and d in (o.get('domain_names') or []):
                    raise RuntimeError('HTTP 400: %s already belongs to %s' % (d, o['name']))
        clusters = set(s['cluster_uuid'] for s in g['sites'])
        for grp in body.get('groups') or []:
            for m in grp.get('members') or []:
                if m['cluster_uuid'] not in clusters:
                    raise RuntimeError('HTTP 400: cluster %s is not a GSLB site' % m['cluster_uuid'])
                site = [f for f in self.world.values() if f.cluster_uuid == m['cluster_uuid']][0]
                vs = site.db.get('virtualservice', {}).get(m['vs_uuid'])
                if not vs:
                    raise RuntimeError('HTTP 400: virtual service %s not found on %s' % (m['vs_uuid'], site.label))
                vv = site.db['vsvip'][parse_ref(vs['vsvip_ref'])['uuid']]
                if m['ip']['addr'] not in [v['ip_address']['addr'] for v in vv['vip']]:
                    raise RuntimeError('HTTP 400: %s is not the VIP of %s' % (m['ip']['addr'], vs['name']))

    def request(self, method, path, body=None, params=None, api_version=None, tenant=None):
        sp = urlsplit(path)
        q = dict(parse_qsl(sp.query))
        q.update(params or {})
        parts = sp.path.strip('/').split('/')
        t = parts[1]
        u = parts[2] if len(parts) > 2 else None
        sub = parts[3] if len(parts) > 3 else None
        ver = api_version or self.version
        self.calls.append({'method': method, 'type': t, 'uuid': u, 'version': ver,
                           'body': copy.deepcopy(body), 'params': dict(q)})
        if t in self.unserved:
            return None
        if method == 'GET':
            if t == 'cluster' and u is None:
                return {'uuid': self.cluster_uuid, 'name': 'cluster-0-1'}
            if u is None:
                if tenant and tenant != 'admin':
                    items = copy.deepcopy(self.tenants.get(tenant, {}).get(t, []))
                else:
                    items = sorted(self.db.get(t, {}).values(), key=lambda o: o.get('name', ''))
                if 'name' in q:
                    items = [o for o in items if str(o.get('name', '')).startswith(q['name'])]
                page = int(q.get('page', 1))
                start = (page - 1) * self.page
                nxt = None
                if start + self.page < len(items):
                    qq = dict(q)
                    qq['page'] = str(page + 1)
                    qq.pop('include_name', None)
                    nxt = '%s/api/%s?%s' % (self.host, t, urlencode(qq))
                out = [self.masked(t, copy.deepcopy(o)) for o in items[start:start + self.page]]
                if q.get('include_name') == 'true':
                    out = [self.named(o) for o in out]
                return {'count': len(items), 'results': out, 'next': nxt}
            o = self.db.get(t, {}).get(u)
            if o is None:
                return None
            if sub == 'runtime':
                up = o.get('enabled', True) and o.get('traffic_enabled', True)
                return {'oper_status': {'state': 'OPER_UP' if up else 'OPER_DISABLED'}}
            out = self.masked(t, copy.deepcopy(o))
            if t == 'sslkeyandcertificate' and str(q.get('export_key')) == 'True' and u in self.keys:
                out['key'] = self.keys[u]
            return self.named(out) if q.get('include_name') == 'true' else out
        if method == 'POST':
            self.check_refs(body)
            obj = self.schema(t, self.bare(copy.deepcopy(body)), ver)
            self.validate('POST', t, obj)
            if any(o.get('name') == obj.get('name') for o in self.db.get(t, {}).values()):
                raise RuntimeError('HTTP 409 on %s: %s %s exists' % (self.label, t, obj.get('name')))
            if t == 'vsvip':
                self.allocate(obj)
            if t == 'gslbservice':
                self.check_gslb_service(obj)
            key = obj.pop('key', None)
            if t == 'sslkeyandcertificate' and obj.get('type') != 'SSL_CERTIFICATE_TYPE_CA' and not key:
                raise RuntimeError('HTTP 400 on %s: a certificate of this type needs its key' % self.label)
            made = self.put(t, self.defaults(t, obj))
            if key:
                self.keys[made['uuid']] = key
            if '%s/%s' % (t, made.get('name')) in self.lose:
                self.lose.discard('%s/%s' % (t, made.get('name')))
                raise RuntimeError('POST /api/%s on %s: Read timed out.' % (t, self.label))
            return copy.deepcopy(made)
        o = self.db.get(t, {}).get(u)
        if o is None:
            raise RuntimeError('HTTP 404 on %s: %s %s' % (self.label, t, u))
        if method == 'DELETE':
            # Like the controller: nothing still referred to, and no GSLB member, can go.
            for t2, objs in self.db.items():
                for o2 in objs.values():
                    if o2 is not o and any((parse_ref(r) or {}).get('uuid') == u for r in ref_values(o2)):
                        raise RuntimeError('HTTP 400 on %s: %s %s is referred to by %s %s'
                                           % (self.label, t, o.get('name'), t2, o2.get('name')))
            for f in self.world.values():
                for gs in f.db.get('gslbservice', {}).values():
                    if any(m.get('vs_uuid') == u for g in gs.get('groups') or [] for m in g.get('members') or []):
                        raise RuntimeError('HTTP 400 on %s: %s is a member of GSLB service %s'
                                           % (self.label, o.get('name'), gs.get('name')))
            del self.db[t][u]
            self.keys.pop(u, None)
            return {}
        if method == 'PATCH':
            new = copy.deepcopy(o)
            for verb, fields in body.items():
                for k, v in fields.items():
                    if verb in ('add', 'delete') and isinstance(v, list) and any(isinstance(x, dict) for x in v):
                        # As 32.1.3 answered the leader for the GSLB subdomains.
                        raise RuntimeError('HTTP 400; {"error":"Failed to patch list of sub objects. Key not found."}')
                    if verb == 'add' and isinstance(new.get(k), list):
                        new[k].extend(copy.deepcopy(v))
                    elif verb in ('add', 'replace'):
                        new[k] = copy.deepcopy(v)
            if t == 'gslbservice':
                self.check_gslb_service(new)
            self.db[t][u] = new
            return copy.deepcopy(new)
        if method == 'PUT':
            # Like the controller: the body replaces the object. A VIP entry
            # without its address gets a new one; a certificate needs its key.
            self.check_refs(body)
            new = self.schema(t, self.bare(copy.deepcopy(body)), ver)
            self.unmask(new, o)
            self.validate('PUT', t, new)
            if new.get('uuid') not in (None, u):
                raise RuntimeError('HTTP 400 on %s: uuid in the body is not the one in the path' % self.label)
            if t == 'vsvip':
                self.allocate(new)
            if t == 'gslbservice':
                self.check_gslb_service(new)
            key = new.pop('key', None)
            if t == 'sslkeyandcertificate' and new.get('type') != 'SSL_CERTIFICATE_TYPE_CA' and not key:
                raise RuntimeError('HTTP 400 on %s: a certificate of this type needs its key' % self.label)
            if key:
                self.keys[u] = key
            new = self.defaults(t, new)
            new['uuid'], new['url'] = u, self.url(t, u)
            self.db[t][u] = new
            return copy.deepcopy(new)
        raise RuntimeError('unsupported %s' % method)


PEM_CERT = '-----BEGIN CERTIFICATE-----\nMIIBselftest\n-----END CERTIFICATE-----\n'
PEM_KEY = '-----BEGIN PRIVATE KEY-----\nMIIEselftest\n-----END PRIVATE KEY-----\n'


# What 32.1.3's object model no longer has, against 31.1.2's, for the types
# this tool writes: the stand-in 32.1 controller's own statement of the
# product, kept apart from PRODUCT_CHANGES so one checks the other.
_GONE_32_1 = {
    '*': [],
    'virtualservice': ['content_rewrite.rewritable_content_ref', 'connections_rate_limit.action.file.file_length',
                       'requests_rate_limit.action.file.file_length'],
    'pool': ['graceful_disable_timeout', 'resolve_pool_by_dns', 'analytics_policy.enable_realtime_metrics',
             'servers.preference_order', 'servers.srv_rdata', 'fail_action.local_rsp.file.file_length',
             'max_conn_rate_per_server.action.file.file_length'],
    'poolgroup': ['fail_action.local_rsp.file.file_length'],
    'applicationprofile': ['dos_rl_profile.rl_profile.**.file.file_length'],
    'wafpolicy': ['enable_app_learning', 'enable_auto_rule_updates', 'enable_regex_learning', 'learning_params',
                  'min_confidence', 'confidence_override', 'updated_crs_rules_in_detection_mode',
                  'application_signatures.resolved_rules', 'required_data_files'],
    'authprofile': ['oauth_profile.instance_id', 'oauth_profile.org_id', 'oauth_profile.service_id',
                    'oauth_profile.service_name'],
}
_MOVED_32_1 = {('pool', 'graceful_disable_timeout'): ('graceful_disable_timeout_sec', 60),
               ('wafpolicy', 'updated_crs_rules_in_detection_mode'): ('use_evaluation_mode_on_crs_update', None)}
_REFUSED_32_1 = {'content_rewrite.rewritable_content_ref'}  # refused whatever release the request speaks


def _world():
    W = {}
    blue = _Fake(W, 'blue-ctrl.test', '31.1.2', 'blue')
    site_a = _Fake(W, 'site1-ctrl.test', '32.1.3', 'site_a')
    site_b = _Fake(W, 'site2-ctrl.test', '32.1.3', 'site_b')
    blue.unserved = {'csrfpolicy'}
    system = [('healthmonitor', {'name': 'System-HTTP', 'type': 'HEALTH_MONITOR_HTTP'}),
              ('analyticsprofile', {'name': 'System-Analytics-Profile'}),
              ('networkprofile', {'name': 'System-TCP-Proxy'}),
              ('sslprofile', {'name': 'System-Standard'}),
              ('sslkeyandcertificate', {'name': 'System-Default-Cert', 'type': 'SSL_CERTIFICATE_TYPE_SYSTEM'}),
              ('stringgroup', {'name': 'System-Rewritable-Content-Types', 'kv': [{'key': 'text/html'}]})]
    for f in (blue, site_a, site_b):
        for t, o in system:
            f.put(t, o)
        f.put('tenant', {'name': 'admin', 'uuid': 'tenant-admin'})
    blue.put('wafcrs', {'name': 'CRS-2023-1'})
    for f in (site_a, site_b):
        f.put('wafcrs', {'name': 'CRS-2025-2'})

    b = blue
    b.put('tenant', {'name': 'finance'})
    b.tenants = {'finance': {'virtualservice': [{'name': 'fin-app', 'uuid': 'virtualservice-fin',
                                                 'tenant_ref': b.url('tenant', 'tenant-fin') + '#finance'}]}}
    b.put('cloud', {'name': 'site-a-nsx-cloud'})
    for n in ('T1-STRETCHED-A-B', 'global'):
        b.put('vrfcontext', {'name': n})
    for n in ('site-a-se-group', 'Default-Group', 'site-a-ako-group'):
        b.put('serviceenginegroup', {'name': n, 'max_se': 10, 'max_vs_per_se': 10, 'vcpus_per_se': 2})
    for i in range(3):
        b.put('serviceengine', {'name': 'blue-se-%d' % i, 'se_group_ref': b.ref('serviceenginegroup', 'site-a-se-group')})
    b.put('network', {'name': 'net-10.1.92.0-24'})
    cloud, vrf = b.ref('cloud', 'site-a-nsx-cloud'), b.ref('vrfcontext', 'T1-STRETCHED-A-B')
    seg, net = b.ref('serviceenginegroup', 'site-a-se-group'), b.ref('network', 'net-10.1.92.0-24')
    common = {'tenant_ref': b.url('tenant', 'tenant-admin'), 'configpb_attributes': {'version': 3},
              '_last_modified': '1700000000000000'}

    def o(t, **kw):
        body = dict(common)
        body.update(kw)
        return b.put(t, body)

    o('healthmonitor', name='App-HTTPS', type='HEALTH_MONITOR_HTTPS',
      https_monitor={'http_request': 'GET /api/v1/health HTTP/1.1', 'http_response_code': ['HTTP_2XX']})
    # As the API hands a monitor's credentials back: both masked.
    o('healthmonitor', name='Auth-HM', type='HEALTH_MONITOR_HTTP',
      authentication={'username': MASKED, 'password': MASKED})
    o('healthmonitor', name='SQL-HM', type='HEALTH_MONITOR_EXTERNAL',
      external_monitor={'command_code': 'import pymssql\nprint(1)'})
    o('healthmonitor', name='Unused-HM', type='HEALTH_MONITOR_TCP')
    o('healthmonitor', name='Ping-HM', type='HEALTH_MONITOR_PING', monitor_port=21032)
    o('authprofile', name='ldap-auth', type='AUTH_PROFILE_LDAP', ldap={'server': ['10.1.1.1']})
    o('authprofile', name='oauth-auth', type='AUTH_PROFILE_OAUTH',
      oauth_profile={'oauth_resp_buffer_sz': 1024, 'client_secret': '$AES256$c2VjcmV0'})
    modern = o('sslprofile', name='Modern-TLS', accepted_ciphers='ECDHE-RSA-AES256-GCM-SHA384:AES256-SHA',
               accepted_versions=[{'type': 'SSL_VERSION_TLS1_2'}])
    legacy = o('sslprofile', name='Legacy-TLS', accepted_ciphers='ECDHE-RSA-AES256-GCM-SHA384:DES-CBC3-SHA',
               accepted_versions=[{'type': 'SSL_VERSION_SSLV3'}, {'type': 'SSL_VERSION_TLS1'},
                                  {'type': 'SSL_VERSION_TLS1_2'}])
    ca = o('sslkeyandcertificate', name='Example-Issuing-CA', type='SSL_CERTIFICATE_TYPE_CA',
           certificate={'certificate': PEM_CERT, 'subject': {'common_name': 'Example Issuing CA'},
                        'not_after': '2031-01-01 00:00:00', 'signature_algorithm': 'sha256WithRSAEncryption'})
    cert = o('sslkeyandcertificate', name='portal-cert', type='SSL_CERTIFICATE_TYPE_VIRTUALSERVICE',
             status='SSL_CERTIFICATE_FINISHED', ocsp_response_info={'ocsp_resp_status': 'x'},
             ca_certs=[{'name': 'Example-Issuing-CA', 'ca_ref': ca['url']}],
             certificate={'certificate': PEM_CERT, 'subject': {'common_name': 'portal.myexample.com'},
                          'subject_alt_names': ['portal.myexample.com', 'www.myexample.com'],
                          'not_after': '2030-05-01 00:00:00', 'signature_algorithm': 'sha256WithRSAEncryption'})
    soon = (datetime.now(timezone.utc).replace(microsecond=0)).isoformat()
    sni_cert = o('sslkeyandcertificate', name='sni-cert', type='SSL_CERTIFICATE_TYPE_VIRTUALSERVICE',
                 certificate={'certificate': PEM_CERT, 'subject': {'common_name': 'app.exampleapp.com'},
                              'not_after': soon, 'signature_algorithm': 'sha1WithRSAEncryption'})
    for c in (cert, sni_cert):
        b.keys[c['uuid']] = PEM_KEY
    o('sslkeyandcertificate', name='portal-controller-cert', type='SSL_CERTIFICATE_TYPE_SYSTEM',
      certificate={'certificate': PEM_CERT})
    o('sslkeyandcertificate', name='nokey-cert', type='SSL_CERTIFICATE_TYPE_VIRTUALSERVICE',
      certificate={'certificate': PEM_CERT, 'subject': {'common_name': 'nokey.example.com'}})
    app = o('applicationprofile', name='Portal-HTTP', type='APPLICATION_PROFILE_TYPE_HTTP')
    redirect = o('httppolicyset', name='portal-80-redirect',
                 http_request_policy={'rules': [
                     {'name': 'orders', 'match': {'path': {'match_criteria': 'BEGINS_WITH',
                                                           'match_str': ['/api/v2/orders']}},
                      'redirect_action': {'host': {'tokens': [{'str_value': 'portal.myexample.com'}]},
                                          'path': {'tokens': [{'str_value': '/api/v1/login'}]}}},
                     {'name': 'to-443', 'redirect_action': {'port': 443}}]})
    # 31.1's application learning, which 32.1 no longer has, as policies written on 31.1 carry it.
    waf = o('wafpolicy', name='portal-waf', waf_crs_ref=b.ref('wafcrs', 'CRS-2023-1'), mode='WAF_MODE_DETECTION_ONLY',
            enable_app_learning=False, enable_auto_rule_updates=True, enable_regex_learning=False,
            learning_params={'enable_per_uri_learning': True}, min_confidence='CONFIDENCE_VERY_HIGH',
            updated_crs_rules_in_detection_mode=True)

    def pool(name, hms, **kw):
        return o('pool', name=name, cloud_ref=cloud, vrf_ref=vrf, tier1_lr='/infra/tier-1s/T1-STRETCHED-A-B',
                 graceful_disable_timeout=1, health_monitor_refs=[b.ref('healthmonitor', h) for h in hms],
                 servers=[{'ip': ip4('10.1.30.11'), 'port': 443,
                           'vm_ref': 'https://blue-ctrl.test/api/vimgrvmruntime/vm-1',
                           'nw_ref': 'https://blue-ctrl.test/api/vimgrnwruntime/dvportgroup-9',
                           'discovered_networks': [{'network_ref': net, 'subnet': [prefix('10.1.30.0/24')]}],
                           'mac_address': '00:50:56:aa:bb:cc'},
                          {'ip': ip4('10.1.30.12'), 'port': 443}], **kw)
    pool('portal-pool', ['App-HTTPS', 'System-HTTP'],
         placement_networks=[{'network_ref': net, 'subnet': prefix('10.1.30.0/24')}],
         description='runbook https://blue-ctrl.test/#!/admin/applications/pools',
         fail_action={'type': 'FAIL_ACTION_HTTP_LOCAL_RSP',
                      'local_rsp': {'status_code': 'FAIL_HTTP_STATUS_CODE_503',
                                    'file': {'content_type': 'text/html', 'file_content': '<p>down</p>',
                                             'file_length': 11}}})
    pool('legacy-pool', ['Auth-HM'])
    pool('sql-pool', ['SQL-HM'])
    pool('sni-pool', ['System-HTTP', 'Ping-HM'])

    def vsvip(name, ip):
        return o('vsvip', name=name, cloud_ref=cloud, vrf_context_ref=vrf, tier1_lr='/infra/tier-1s/T1-STRETCHED-A-B',
                 dns_info=[{'fqdn': name.replace('vsvip-', '') + '.example.com'}],
                 vip=[{'vip_id': '0', 'ip_address': ip4(ip), 'auto_allocate_ip': True, 'avi_allocated_vip': True,
                       'ipam_network_subnet': {'network_ref': net, 'subnet': prefix('10.1.92.0/24')},
                       'placement_networks': [{'network_ref': net, 'subnet': prefix('10.1.92.0/24')}],
                       'discovered_networks': [{'network_ref': net}], 'enabled': True}])
    for n, ip in (('vsvip-portal', '10.1.92.45'), ('vsvip-sni', '10.1.92.46'), ('vsvip-legacy', '10.1.92.47'),
                  ('vsvip-old', '10.1.92.48'), ('vsvip-waf', '10.1.92.49'), ('vsvip-snat', '10.1.92.50'),
                  ('vsvip-noname', '10.1.92.51'), ('vsvip-dg', '10.1.92.52'), ('vsvip-dns', '10.1.92.53'),
                  ('vsvip-ako', '10.1.92.54'), ('vsvip-unused', '10.1.92.60')):
        vsvip(n, ip)

    def vs(name, vip, pool_name=None, ports=(443,), **kw):
        body = dict(cloud_ref=cloud, vrf_context_ref=vrf, se_group_ref=seg, enabled=True, traffic_enabled=True,
                    services=[{'port': p, 'enable_ssl': p == 443} for p in ports],
                    analytics_profile_ref=b.ref('analyticsprofile', 'System-Analytics-Profile'),
                    application_profile_ref=app['url'], network_profile_ref=b.ref('networkprofile', 'System-TCP-Proxy'))
        if vip:
            body['vsvip_ref'] = b.ref('vsvip', vip)
            body['vip'] = [{'vip_id': '0', 'ip_address': ip4('10.1.92.45')}]
        if pool_name:
            body['pool_ref'] = b.ref('pool', pool_name)
        body.update(kw)
        return o('virtualservice', name=name, **body)
    vs('portal-443', 'vsvip-portal', 'portal-pool', ssl_key_and_certificate_refs=[cert['url']],
       ssl_profile_ref=modern['url'],
       content_rewrite={'rewritable_content_ref': b.ref('stringgroup', 'System-Rewritable-Content-Types')},
       # Runtime state blue hands back with every service, in no release's object model.
       tls_ticket_key=[{'name': 'k1', 'aes_key': 'VElDS0VUQUVTS0VZ', 'hmac_key': 'VElDS0VUSE1BQ0tFWQ=='}],
       redis_db=11, redis_port=5021, marked_for_delete=False, self_se_election=False)
    vs('portal-80', 'vsvip-portal', ports=(80,), enabled=False,
       http_policies=[{'index': 11, 'http_policy_set_ref': redirect['url']}])
    parent = vs('sni-parent', 'vsvip-sni', type='VS_TYPE_VH_PARENT', ssl_key_and_certificate_refs=[cert['url']])
    vs('sni-child', None, 'sni-pool', type='VS_TYPE_VH_CHILD', vh_parent_vs_ref=parent['url'],
       vh_domain_name=['app.exampleapp.com'], ssl_key_and_certificate_refs=[sni_cert['url']])
    vs('legacy-app', 'vsvip-legacy', 'legacy-pool', ssl_profile_ref=legacy['url'])
    vs('old-app', 'vsvip-old', 'sql-pool', enabled=False)
    vs('waf-app', 'vsvip-waf', 'portal-pool', waf_policy_ref=waf['url'])
    vs('snat-app', 'vsvip-snat', 'portal-pool', snat_ip=[ip4('10.1.92.200')])
    vs('internal-api', 'vsvip-noname', 'portal-pool', traffic_enabled=False)
    vs('dg-app', 'vsvip-dg', 'portal-pool', se_group_ref=b.ref('serviceenginegroup', 'Default-Group'),
       use_vip_as_snat=True)
    vs('blue-dns', 'vsvip-dns', type='VS_TYPE_DNS', ports=(53,))
    vs('ako-app', 'vsvip-ako', 'portal-pool', created_by='ako-cluster1')

    for f, base, t1, cloud_name, vrf_name, seg_name in (
            (site_a, '10.1.100', 'T1-SITE-A-LOCAL', 'site-a-nsx-cloud', 'T1-SITE-A-LOCAL', 'site-a-se-group'),
            (site_b, '10.2.100', 'T1-SITE-B-LOCAL', 'site-b-nsx-cloud', 'T1-SITE-B-LOCAL', 'site-b-se-group')):
        s = f.label.upper()
        f.put('cloud', {'name': cloud_name})
        for n in (vrf_name, 'global'):
            f.put('vrfcontext', {'name': n})
        f.put('serviceenginegroup', {'name': seg_name, 'max_se': 10, 'max_vs_per_se': 1, 'vcpus_per_se': 1})
        f.put('serviceenginegroup', {'name': 'Default-Group', 'max_se': 10, 'max_vs_per_se': 10})
        f.put('serviceenginegroup', {'name': '%s-DNS-SE-Group' % s, 'max_se': 1, 'max_vs_per_se': 1})
        n = f.put('network', {'name': 'net-%s.0-24' % base, 'vrf_context_ref': f.ref('vrfcontext', vrf_name),
                              'configured_subnets': [{'prefix': prefix('%s.0/24' % base), 'static_ip_ranges': [
                                  {'type': 'STATIC_IPS_FOR_VIP',
                                   'range': {'begin': ip4('%s.10' % base), 'end': ip4('%s.240' % base)}}]}]})
        f.put('network', {'name': 'net-%s.0-24-old' % base})
        for vname, last, vsname, group in (('svip-%s-gslb-dns' % f.label, 11, '%s-gslb-dns' % f.label, '%s-DNS-SE-Group' % s),
                                           ('svip-%s-canary' % f.label, 12, '%s-canary' % f.label, seg_name)):
            vv = f.put('vsvip', {'name': vname, 'cloud_ref': f.ref('cloud', cloud_name),
                                 'vrf_context_ref': f.ref('vrfcontext', vrf_name),
                                 'tier1_lr': '/infra/tier-1s/%s' % t1,
                                 'vip': [{'vip_id': '0', 'ip_address': ip4('%s.%d' % (base, last)),
                                          'auto_allocate_ip': True,
                                          'ipam_network_subnet': {'network_ref': n['url'],
                                                                  'subnet': prefix('%s.0/24' % base)}}]})
        prof = f.put('applicationprofile', {'name': 'site-gslb-dns', 'type': 'APPLICATION_PROFILE_TYPE_DNS',
                                            'dns_service_profile': {'dns_zones': [
                                                {'domain_name': 'gslb.example.com',
                                                 'admin_email': 'hostmaster.example.com'}]}})
        f.put('applicationprofile', {'name': 'site-other-dns', 'type': 'APPLICATION_PROFILE_TYPE_DNS',
                                     'dns_service_profile': {'dns_zones': []}})
        for vname, last, vsname, group in (('svip-%s-gslb-dns' % f.label, 11, '%s-gslb-dns' % f.label, '%s-DNS-SE-Group' % s),
                                           ('svip-%s-canary' % f.label, 12, '%s-canary' % f.label, seg_name)):
            vv = f.by_name('vsvip', vname)
            body = {'name': vsname, 'vsvip_ref': vv['url'], 'enabled': True,
                    'type': 'VS_TYPE_DNS' if 'dns' in vsname else 'VS_TYPE_NORMAL',
                    'se_group_ref': f.ref('serviceenginegroup', group)}
            if 'dns' in vsname:
                body['application_profile_ref'] = prof['url']
            f.put('virtualservice', body)
    site_b.put('healthmonitor', {'name': 'App-HTTPS', 'type': 'HEALTH_MONITOR_HTTPS',
                             'https_monitor': {'http_request': 'GET / HTTP/1.0'}})
    squat_vip = site_b.put('vsvip', {'name': 'vsvip-noname', 'cloud_ref': site_b.ref('cloud', 'site-b-nsx-cloud'),
                                 'vrf_context_ref': site_b.ref('vrfcontext', 'T1-SITE-B-LOCAL'),
                                 'tier1_lr': '/infra/tier-1s/T1-SITE-B-LOCAL',
                                 'vip': [{'vip_id': '0', 'ip_address': ip4('10.2.100.99')}]})
    site_b.put('virtualservice', {'name': 'internal-api', 'vsvip_ref': squat_vip['url'], 'enabled': True,
                              'vrf_context_ref': site_b.ref('vrfcontext', 'T1-SITE-B-LOCAL'),
                              'se_group_ref': site_b.ref('serviceenginegroup', 'Default-Group')})
    sites = []
    for f in (site_a, site_b):
        dv = {'dns_vs_uuid': f.by_name('virtualservice', '%s-gslb-dns' % f.label)['uuid']}
        if f is site_b:
            dv['domain_names'] = ['gslb.example.com']  # Host All Subdomains off
        sites.append({'name': f.label.upper(), 'cluster_uuid': f.cluster_uuid, 'member_type': 'GSLB_ACTIVE_MEMBER',
                      'username': 'admin', 'password': 'site-secret', 'dns_vses': [dv]})
    site_a.put('gslb', {'name': 'Default', 'leader_cluster_uuid': site_a.cluster_uuid, 'sites': sites,
                    'dns_configs': [{'domain_name': 'gslb.example.com'}]})

    def member(f, vsname, last, base):
        return {'cluster_uuid': f.cluster_uuid, 'vs_uuid': f.by_name('virtualservice', vsname)['uuid'],
                'ip': ip4('%s.%d' % (base, last)), 'ratio': 1, 'enabled': True, 'description': 'canary'}
    site_a.put('healthmonitor', {'name': 'canary-gslb-hm', 'type': 'HEALTH_MONITOR_HTTP', 'is_federated': True})
    site_a.put('gslbservice', {'name': 'canary', 'domain_names': ['canary.gslb.example.com'], 'ttl': 30,
                           'health_monitor_refs': [site_a.ref('healthmonitor', 'canary-gslb-hm')],
                           'pool_algorithm': 'GSLB_SERVICE_ALGORITHM_PRIORITY', 'controller_health_status_enabled': True,
                           'down_response': {'type': 'GSLB_SERVICE_DOWN_RESPONSE_NONE'}, 'is_federated': True,
                           'description': 'canary app',
                           'groups': [{'name': 'canary-site_a', 'priority': 20, 'algorithm': 'GSLB_ALGORITHM_ROUND_ROBIN',
                                       'description': 'site_a first', 'members': [member(site_a, 'site_a-canary', 12, '10.1.100')]},
                                      {'name': 'canary-site_b', 'priority': 10, 'algorithm': 'GSLB_ALGORITHM_ROUND_ROBIN',
                                       'members': [member(site_b, 'site_b-canary', 12, '10.2.100')]}]})
    site_a.put('gslbservice', {'name': 'dns-gslb', 'domain_names': ['dns.gslb.example.com'],
                           'groups': [{'name': 'dns-gslb-site_a', 'priority': 10,
                                       'members': [member(site_a, 'site_a-gslb-dns', 11, '10.1.100')]}]})
    return W


DNS_EXPORT = """#TYPE Selected.Microsoft.Management.Infrastructure.CimInstance
"fqdn","type","data","ttl","zone"
"portal.myexample.com","A","10.1.92.45","3600","myexample.com"
"www.myexample.com","CNAME","portal.myexample.com.","3600","myexample.com"
"myexample.com","A","10.1.92.45","3600","myexample.com"
"portal.example.com","A","10.1.92.45","1200","example.com"
"app.exampleapp.com","A","10.1.92.46","3600","exampleapp.com"
"old.example.com","A","10.1.92.48","3600","example.com"
"shop.exampleshop.org","A","10.1.92.49","3600","exampleshop.org"
"legacy.example.com","A","10.1.92.47","3600","example.com"
"split.example.com","A","10.1.92.50","3600","example.com"
"split.example.com","A","10.99.1.1","3600","example.com"
"partner.example.org","A","10.1.92.52","3600","example.org"
"dg.example.com","A","10.1.92.52","3600","example.com"
"canary.example.com","CNAME","canary.gslb.example.com","3600","example.com"
"fileserver.example.com","A","10.1.2.3","3600","example.com"
"*.exampleshop.org","A","10.1.92.45","3600","exampleshop.org"
"api.corp.example.com","A","10.99.9.9","3600","example.com"
"api.corp.example.com","A","10.1.92.46","3600","corp.example.com"
"app.exampleapp.com","RRSIG","","3600","exampleapp.com"
"corp.example.com","A","10.1.92.46","3600","corp.example.com"
"corp.example.com","SOA","","3600","corp.example.com"
"txt.example.com","A","10.1.92.45","3600","example.com"
"txt.example.com","TXT","v=spf1 -all","3600","example.com"
"""


def selftest(cfg, args):
    """Exercise every command offline against in-memory controllers and DNS.
    No network, no credentials, no writes outside a temporary directory."""
    import contextlib
    import io
    import tempfile
    global CLIENT_FACTORY, dns_query
    passed, failed = [], []
    saved = (CLIENT_FACTORY, dns_query)
    W = _world()
    CLIENT_FACTORY = lambda c, role, site: W['blue'] if role == 'source' else W[site]
    _POOL.clear()
    d = tempfile.mkdtemp(prefix='avi_migrate_selftest_')
    dns_csv = os.path.join(d, 'dns_records.csv')
    with open(dns_csv, 'w', encoding='utf-8-sig') as fh:
        fh.write(DNS_EXPORT)
    zones = ['example.com', 'myexample.com', 'exampleapp.com', 'exampleshop.org']
    gslb_vips = ['10.1.100.11', '10.2.100.11']
    cfg = {'site_name': 'selftest', 'avi_outdir': d, 'avi_source_host': 'https://blue-ctrl.test',
           'avi_sites': ['site_a', 'site_b'],
           'avi_target_host_site_a': 'https://site1-ctrl.test', 'avi_cloud_site_a': 'site-a-nsx-cloud',
           'avi_vrf_site_a': 'T1-SITE-A-LOCAL', 'avi_se_group_site_a': 'site-a-se-group',
           'avi_vip_network_site_a': 'net-10.1.100.0-24', 'avi_vip_subnet_site_a': '10.1.100.0/24',
           'avi_target_host_site_b': 'https://site2-ctrl.test', 'avi_cloud_site_b': 'site-b-nsx-cloud',
           'avi_vrf_site_b': 'T1-SITE-B-LOCAL', 'avi_se_group_site_b': 'site-b-se-group',
           'avi_vip_network_site_b': 'net-10.2.100.0-24', 'avi_vip_subnet_site_b': '10.2.100.0/24',
           'avi_map_site_b': ['wafcrs/CRS-2023-1=wafcrs/CRS-2025-2'],
           'avi_live_site_a': 'all', 'avi_live_site_b': 'all',
           'gslb_leader': 'site_a', 'gslb_site_name_site_a': 'SITE-A', 'gslb_site_name_site_b': 'SITE-B',
           'gslb_template_service': 'canary', 'gslb_zones': zones, 'gslb_label': 'gslb',
           'gslb_dns_profile': 'site-gslb-dns', 'gslb_dns_vips': gslb_vips,
           'gslb_names': dns_csv, 'gslb_ttl': 30, 'gslb_priority_site_a': 20, 'gslb_priority_site_b': 10,
           'dns_servers': ['192.0.2.53']}
    ns = argparse.Namespace

    # The DNS clients use: every A and CNAME of the export, the GSLB names
    # delegated to the GSLB DNS services, which answer from the GSLB services
    # on the leader as Avi would.
    ad, down, undelegated, stale, ad_ttl, ptr = {}, set(), set(), set(), {}, {}
    flaky = set()  # (server, name): a server that answers, but not about that name
    for r in load_dns(dns_csv):
        if r['type'] in ('A', 'CNAME') and r['fqdn'] not in ad and (r['zone'] != 'example.com' or
                                                                   not r['fqdn'].endswith('corp.example.com')):
            ad[r['fqdn']] = (r['type'], r['data'])
            ad_ttl[r['fqdn']] = r['ttl']
    ad_then = dict(ad)  # what a DC that has not caught up still answers
    hosted = set(r['zone'] for r in load_dns(dns_csv) if r['zone'])  # the zones the DCs hold

    def gslb_answer(name):
        for svc in W['site_a'].db.get('gslbservice', {}).values():
            if name in svc.get('domain_names', []):
                for grp in sorted(svc['groups'], key=lambda x: -x.get('priority', 0)):
                    m = grp['members'][0]
                    site = [f for f in W.values() if f.cluster_uuid == m['cluster_uuid']][0]
                    vsx = site.db['virtualservice'].get(m['vs_uuid'])
                    if vsx and vsx.get('enabled') and vsx.get('traffic_enabled', True):
                        return {'rcode': 0, 'a': [m['ip']['addr']], 'cname': []}
                if (svc.get('down_response') or {}).get('type') == 'GSLB_SERVICE_DOWN_RESPONSE_ALL_RECORDS':
                    return {'rcode': 0, 'a': [g_['members'][0]['ip']['addr'] for g_ in svc['groups']], 'cname': []}
                return {'rcode': 3, 'a': [], 'cname': []}
        return {'rcode': 3, 'a': [], 'cname': []}

    def fake_dns(server, name, timeout=3.0, port=53, qtype=1):
        name = name.lower().rstrip('.')
        if server in down or (qtype == 1 and (server, name) in flaky):
            return {'error': 'no answer (timeout)'}
        if server in gslb_vips:
            return gslb_answer(name)
        if qtype == QTYPE['SOA']:
            return {'rcode': 0, 'aa': True, 'a': [], 'cname': [], 'soa': [name] if name in hosted else []}
        if qtype == QTYPE['PTR']:
            return {'rcode': 0 if name in ptr else 3, 'aa': True, 'a': [], 'cname': [],
                    'ptr': [ptr[name]] if name in ptr else []}
        if any(name.endswith('.' + z) for z in undelegated):
            return {'rcode': 3, 'a': [], 'cname': []}  # the clients' DNS has no delegation for it
        table = ad_then if server in stale else ad
        if name in table:
            kind, data = table[name]
            if kind == 'A':
                return {'rcode': 0, 'a': [data], 'cname': [], 'ttl': ad_ttl.get(name)}
            return {'rcode': 0, 'a': gslb_answer(data).get('a', []), 'cname': [data], 'ttl': ad_ttl.get(name)}
        if '.gslb.' in name:
            return gslb_answer(name)
        return {'rcode': 3, 'a': [], 'cname': []}
    dns_query = fake_dns

    def quiet(fn, *a):
        buf = io.StringIO()
        try:
            with contextlib.redirect_stdout(buf):
                rv = fn(*a)
        except Exception:
            sys.stdout.write(buf.getvalue()[-4000:])
            raise
        return rv, buf.getvalue()

    def check(name, fn):
        try:
            fn()
            passed.append(name)
            print('  ok    ' + name)
        except Exception as exc:
            failed.append('%s: %s' % (name, exc))
            print('  FAIL  %s: %s' % (name, str(exc)[:1500]))

    def expect(cond, msg=''):
        if not cond:
            raise AssertionError(msg)

    def cv_args(**kw):
        a = dict(commit=False, site=None, vs=None, journal=None, force=False, trust_export=False,
                 verbose=False, adopt=False, export=None, names=None, allow_offline=False,
                 live_flipped=False, rewrite_gslb=False)
        a.update(kw)
        return ns(**a)

    def cv(**kw):
        return quiet(converge_cmd, cfg, cv_args(**kw))

    def cv_raises(**kw):
        """Run converge where it is meant to stop; returns what it raised."""
        try:
            with contextlib.redirect_stdout(io.StringIO()):
                converge_cmd(cfg, cv_args(**kw))
        except (RuntimeError, ValueError) as exc:
            return exc
        return None

    def writes(label):
        return [c for c in W[label].calls if c['method'] in ('POST', 'PUT', 'PATCH', 'DELETE')]

    def plan_rows():
        with open(artefact(cfg, 'converge-plan', 'csv'), newline='') as fh:
            return dict(('%s %s/%s' % (r['site'], r['type'], r['name']), r) for r in csv.DictReader(fh))

    def flips():
        with open(artefact(cfg, 'dns-flips', 'csv'), newline='') as fh:
            return dict((r['fqdn'] or 'vip:' + r['blue_vsvip'], r) for r in csv.DictReader(fh))

    def vip_of(label, vsvip):
        return W[label].by_name('vsvip', vsvip)['vip'][0]['ip_address']['addr']

    def reset_calls():
        for f in W.values():
            f.calls = []

    try:
        print('config')
        cpath = os.path.join(d, 'c.yaml')
        with open(cpath, 'w') as fh:
            fh.write('site_name: t\navi_sites: [site_a, site_b]\navi_map_site_a: [\n  vrfcontext/T1-STRETCHED-A-B=vrfcontext/GM:X,\n'
                     '  serviceenginegroup/A=serviceenginegroup/B\n]\ngslb_priority_site_a: 20\navi_live_site_a: all\n'
                     'avi_live_site_b: [web-*, api-*]\n')
        os.chmod(cpath, 0o600)

        def cfg_same():
            import builtins
            real = builtins.__import__

            def no_yaml(name, *a, **k):
                if name == 'yaml':
                    raise ImportError('hidden')
                return real(name, *a, **k)
            builtins.__import__ = no_yaml
            try:
                flat = read_config(cpath)
            finally:
                builtins.__import__ = real
            for c in (flat, read_config(cpath)):
                m = site_conf(c, 'site_a')['map']
                expect(m['vrfcontext/T1-STRETCHED-A-B'] == 'vrfcontext/GM:X', m)
                expect(sites_of(c) == ['site_a', 'site_b'])
                expect(str(site_conf(c, 'site_a')['priority']) == '20')
                expect(site_conf(c, 'site_a')['live'] == ['*'] and site_conf(c, 'site_b')['live'] == ['web-*', 'api-*'])
                expect(site_conf(c, 'd3')['live'] == [], 'unset means staged only')
        check('flat reader and PyYAML agree: per-site keys, multi-line maps, avi_live all / patterns / unset', cfg_same)

        def example_parses():
            p = os.path.join(d, 'example.yaml')
            with open(p, 'w') as fh:
                fh.write(EXAMPLE_CONFIG)
            c = read_config(p)
            expect(c.get('avi_live_site_a') == 'all' and c.get('avi_outdir') and sites_of(c) == ['site_a', 'site_b'], c)
            expect('customer.internal' not in EXAMPLE_CONFIG.lower(), 'the example is customer-agnostic')
        check('the example config parses and names no customer', example_parses)

        def placeholder_dns():
            try:
                resolvers(dict(cfg, dns_servers=['<site_a DC IP>', '10.1.1.1']))
            except ValueError as exc:
                expect('fill in the IP addresses' in str(exc), exc)
            else:
                expect(False, 'a placeholder in dns_servers was taken for a server')
        check('dns_servers left with its placeholders stops the run with what to fill in', placeholder_dns)

        print('\nexport')
        quiet(export, cfg, ns(out=None))
        bundle = read(artefact(cfg, 'avi-export'))
        objs = bundle['objects']

        def names_on_refs():
            for k, o in objs.items():
                for r in iter_refs(o):
                    if r['type'] in ('vimgrvmruntime', 'vimgrnwruntime') or r['raw'] == o.get('url'):
                        continue
                    expect(r['name'], '%s has a reference without a name: %s' % (k, r['raw']))
        check('every reference carries its name (include_name, and kept across pages)', names_on_refs)
        check('System- objects and the controller certificate are left behind',
              lambda: expect(not any(k.split('/', 1)[1].startswith('System-') for k in objs)
                             and 'sslkeyandcertificate/portal-controller-cert' in bundle['excluded']))
        check('blue\'s DNS service and AKO objects are excluded with a reason',
              lambda: expect('DNS virtual service' in bundle['excluded']['virtualservice/blue-dns']['reason']
                             and 'ako' in bundle['excluded']['virtualservice/ako-app']['reason']))
        check('another tenant\'s virtual services are reported, not silently skipped',
              lambda: expect(bundle['tenants'].get('finance') == 1, bundle['tenants']))
        check('a type the source does not serve is recorded', lambda: expect('csrfpolicy' in bundle['absent_on_source']))
        check('inventory ties VIP 10.1.92.45 to both portal services',
              lambda: expect(bundle['inventory']['vsvip']['vsvip-portal']['vs'] == ['portal-443', 'portal-80']
                             and bundle['inventory']['vsvip']['vsvip-portal']['ips'] == ['10.1.92.45']))

        print('\nconverge: dry run')
        reset_calls()
        rc, out = cv()
        p = plan_rows()
        check('a dry run writes nothing anywhere, and blue is only ever read',
              lambda: expect(not writes('site_a') and not writes('site_b') and not writes('blue')
                             and rc == 1 and 'DRY RUN' in out, (rc, writes('site_a')[:2])))

        def dry_states():
            for site in ('site_a', 'site_b'):
                for k in ('vsvip/vsvip-portal', 'pool/portal-pool', 'virtualservice/portal-443',
                          'sslkeyandcertificate/portal-cert', 'httppolicyset/portal-80-redirect'):
                    expect(p['%s %s' % (site, k)]['state'] == 'ADD', (site, k, p.get('%s %s' % (site, k))))
            for k, why in (('sslprofile/Legacy-TLS', 'carries'), ('healthmonitor/Auth-HM', 'carries a secret'),
                           ('authprofile/ldap-auth', 'carries a secret'), ('authprofile/oauth-auth', 'carries a secret'),
                           ('virtualservice/snat-app', 'uses fixed SNAT'),
                           ('wafpolicy/portal-waf', 'wafcrs "CRS-2023-1" does not exist on site_a'),
                           ('virtualservice/legacy-app', 'depends on'), ('virtualservice/waf-app', 'depends on'),
                           ('sslkeyandcertificate/nokey-cert', 'blue returned no private key')):
                e = p['site_a ' + k]
                expect(e['state'] == 'BLOCKED' and why in e['detail'], (k, e))
            for k in ('vsvip/vsvip-legacy', 'vsvip/vsvip-snat'):
                e = p['site_a ' + k]
                expect(e['state'] == 'BLOCKED' and 'held back' in e['detail'], ('a VIP only a blocked service uses', k, e))
            expect(p['site_b wafpolicy/portal-waf']['state'] == 'ADD', 'avi_map_site_b maps the CRS at site_b')
            expect(p['site_b virtualservice/internal-api']['state'] == 'BLOCKED'
                   and 'SE group Default-Group' in p['site_b virtualservice/internal-api']['detail'])
            e = p['site_b healthmonitor/App-HTTPS']
            expect(e['state'] == 'KEPT' and 'not made by this tool' in e['detail'], e)
        check('every object is ADD, BLOCKED with its reason, or KEPT when green made it', dry_states)

        def dry_gslb():
            expect('ADD   GSLB subdomains gslb.myexample.com, gslb.exampleapp.com, gslb.exampleshop.org' in out, out)
            expect('ADD   authoritative zones' in out and 'CREATE     portal-443' in out and 'once staged on site_a, site_b' in out)
        check('GSLB in a dry run: subdomains, zones and services it would add', dry_gslb)
        f0 = flips()

        def dry_flips():
            expect(f0['portal.myexample.com']['state'] == 'NOT READY' and 'not staged' in f0['portal.myexample.com']['note'])
            expect(f0['www.myexample.com']['state'] == 'FOLLOWS')
            expect(f0['myexample.com']['state'] == 'MANUAL' and 'apex' in f0['myexample.com']['note'])
            expect(f0['old.example.com']['state'] == 'SKIP' and 'disabled on blue' in f0['old.example.com']['note'])
            expect(f0['split.example.com']['state'] == 'MANUAL' and f0['partner.example.org']['state'] == 'SKIP')
            expect(f0['*.exampleshop.org']['state'] == 'MANUAL' and 'TXT' in f0['txt.example.com']['note'])
            expect(f0['corp.example.com']['state'] == 'MANUAL' and 'apex' in f0['corp.example.com']['note'])
            api = f0['api.corp.example.com']
            expect(api['zone'] == 'corp.example.com' and api['host'] == 'api' and api['blue_ip'] == '10.1.92.46'
                   and 'old copy in example.com' in api['note'], api)
            expect(f0['app.exampleapp.com']['gslb_fqdn'] == 'app.gslb.exampleapp.com', 'an RRSIG does not block a name')
            expect(f0['vip:vsvip-noname']['state'] == 'NONAME')
            expect(not any(r['blue_vsvip'] in ('vsvip-ako', 'vsvip-dns', 'vsvip-unused') for r in f0.values()))
        check('the flip list: names joined to blue VIPs, followers, apex, split, shadowed copies, no-name VIPs',
              dry_flips)

        def restaged():
            fr = {}
            pl = plan_site(cfg, 'site_a', bundle, select_scope(cfg, ns(vs=None), bundle)[0], {}, fr,
                           ignore_fields(cfg), Registry(cfg))
            ops = dict(('%s/%s' % (o['type'], o['name']), o) for o in pl['ops'])
            vip = ops['vsvip/vsvip-portal']['body']['vip'][0]
            expect('ip_address' not in vip and 'placement_networks' not in vip and vip['auto_allocate_ip'] is True)
            expect(ref_name(vip['ipam_network_subnet']['network_ref']) == 'net-10.1.100.0-24')
            expect(ops['vsvip/vsvip-portal']['body']['tier1_lr'] == '/infra/tier-1s/T1-SITE-A-LOCAL')
            pb = ops['pool/portal-pool']['body']
            expect(all(not (set(s) & SERVER_STRIP) for s in pb['servers']) and 'placement_networks' not in pb)
            expect(ref_name(pb['vrf_ref']) == 'T1-SITE-A-LOCAL' and 'configpb_attributes' not in pb)
            vb = ops['virtualservice/portal-443']['body']
            expect(vb['enabled'] is False and vb['traffic_enabled'] is False and 'vip' not in vb)
            expect(ref_name(ops['virtualservice/dg-app']['body']['se_group_ref']) == 'site-a-se-group')
            expect(any('pool/portal-pool: text in description names blue' in w for w in pl['warnings']))
            expect(ops['healthmonitor/App-HTTPS'] and ops['httppolicyset/portal-80-redirect'],
                   'application paths like /api/v1/health are content, not references')
        check('restaging: VIPs allocate from the site, Tier-1 derived, pools cleaned, services added disabled',
              restaged)

        print('\nconverge --commit')
        reset_calls()
        rc, out = cv(commit=True)
        reg = Registry(cfg)

        def first_commit():
            for site, base in (('site_a', '10.1.100.'), ('site_b', '10.2.100.')):
                f = W[site]
                expect(vip_of(site, 'vsvip-portal').startswith(base))
                v = f.by_name('virtualservice', 'portal-443')
                expect(v['enabled'] is True and v['traffic_enabled'] is True, (site, 'live per avi_live'))
                expect(f.by_name('virtualservice', 'portal-80')['enabled'] is False, 'off on blue, off on green')
                expect(reg.owns(site, 'virtualservice', 'portal-443', v['uuid']))
            ia = W['site_a'].by_name('virtualservice', 'internal-api')
            expect(ia['enabled'] is True and ia['traffic_enabled'] is False, 'no traffic on blue: placed only on green')
            for site in ('site_a', 'site_b'):
                f = W[site]
                posts = [c for c in f.calls if c['method'] == 'POST' and c['type'] in PORTABLE
                         and not str((c['body'] or {}).get('name', '')).startswith('gslb-tcp-')]
                expect(posts and all(c['version'] == '31.1.2' for c in posts), 'posted in blue\'s schema')
            expect(not writes('blue'))
        check('commit: everything added at both sites, recorded as this tool\'s, then set live per site',
              first_commit)
        check('a service keeps no content_rewrite.rewritable_content_ref, which 32.1 refuses; without rules, '
              'no content_rewrite at all',
              lambda: expect('content_rewrite' not in W['site_a'].by_name('virtualservice', 'portal-443')))
        check('a PING monitor loses the port 31.1 allowed and 32.1 refuses, and the plan says so',
              lambda: expect('monitor_port' not in W['site_a'].by_name('healthmonitor', 'Ping-HM')
                             and 'CHANGED    product change 31.1.2 -> 32.1.3, healthmonitor: a PING monitor has no '
                                 'port' in out and 'monitor_port. 1: Ping-HM' in out, out[-3000:]))

        def product_changed():
            def sent(site, t, name):
                return [c['body'] for c in W[site].calls if c['method'] == 'POST' and c['type'] == t
                        and (c['body'] or {}).get('name') == name][0]
            v = sent('site_a', 'virtualservice', 'portal-443')
            expect(not set(v) & {'tls_ticket_key', 'redis_db', 'redis_port', 'marked_for_delete', 'self_se_election'},
                   ('runtime state, and blue\'s session-ticket keys, stay behind', sorted(v)))
            p = sent('site_a', 'pool', 'portal-pool')
            expect(p.get('graceful_disable_timeout') == 1 and 'file_length' not in p['fail_action']['local_rsp']['file'],
                   ('moved: left in blue\'s form for the target; computed: removed', p.get('fail_action')))
            w = sent('site_b', 'wafpolicy', 'portal-waf')
            expect(not set(w) & {'enable_app_learning', 'enable_auto_rule_updates', 'enable_regex_learning',
                                 'learning_params', 'min_confidence'}, ('gone: removed', sorted(w)))
            expect(w.get('updated_crs_rules_in_detection_mode') is True, 'moved: blue\'s form, converted by the target')
            held = W['site_b'].by_name('wafpolicy', 'portal-waf')
            expect(held.get('use_evaluation_mode_on_crs_update') is True and 'updated_crs_rules_in_detection_mode'
                   not in held, held)
            expect(W['site_a'].by_name('pool', 'portal-pool').get('graceful_disable_timeout_sec') == 60)
            for text in ('pool: graceful_disable_timeout (minutes) is graceful_disable_timeout_sec (seconds). Left in '
                         'blue\'s form, which the target converts itself: graceful_disable_timeout.',
                         'wafpolicy: application learning is gone; its settings are not carried. Removed: '
                         'enable_app_learning, enable_auto_rule_updates, enable_regex_learning, learning_params, '
                         'min_confidence. 1: portal-waf',
                         'virtualservice: content_rewrite.rewritable_content_ref is gone, and the target refuses it',
                         "pool: a local file's length is computed by the target. Removed: file.file_length"):
                expect(text in out, (text, out[-4000:]))
            expect('tls_ticket_key' not in json.dumps(read(artefact(cfg, 'avi-export'))),
                   'blue\'s session-ticket keys are not kept in the saved export either')
        check('the product changes from 31.1.2 to 32.1.3 are made before writing and listed in the plan: gone '
              'fields removed, moved ones left for the target to convert, runtime state and ticket keys left behind',
              product_changed)

        def written_natively():
            """avi_write_version: target. Every change is made by this tool, and
            32.1, told its own release, has nothing left to refuse."""
            b_ = read(artefact(cfg, 'avi-export'))
            ctx_ = {'source_version': '31.1.2', 'target_version': '32.1.3', 'write_target': True,
                    'urls': {'network': 'n', 'cloud': 'c', 'vrfcontext': 'v', 'serviceenginegroup': 's'},
                    'vip_subnet': '10.1.100.0/24', 'tier1': '/infra/tier-1s/x'}
            for k in ('pool/portal-pool', 'wafpolicy/portal-waf', 'virtualservice/portal-443', 'healthmonitor/Ping-HM'):
                t, n = split_key(k)
                body = clean(b_['objects'][k], t)
                restage(t, n, b_['objects'][k], body, ctx_, False)
                W['site_a'].schema(t, copy.deepcopy(body), '32.1.3')  # raises on any field 32.1 does not have
                if t == 'pool':
                    expect(body.get('graceful_disable_timeout_sec') == 60 and 'graceful_disable_timeout' not in body)
                if t == 'wafpolicy':
                    expect(body.get('use_evaluation_mode_on_crs_update') is True)
            # Every field the stand-in 32.1 no longer has is one a rule of this tool handles.
            ruled = set((r['type'], p.replace('**.', '')) for r in PRODUCT_CHANGES for p in r['paths'])
            for t, paths in _GONE_32_1.items():
                for p in paths:
                    tail = p.split('**.')[-1]
                    expect((t, p) in ruled or ('*', tail) in ruled or ('*', 'file.file_length') in ruled
                           and tail.endswith('file.file_length'), ('no rule for', t, p))
        check('written in green\'s release, every product change is made by this tool, and each field 32.1.3 no '
              'longer has is covered by a rule', written_natively)

        def target_owned():
            ig = ignore_fields(cfg)
            vs_body = {'name': 'x', 'scaleout_ecmp': False, 'services': [{'port': 443}]}
            expect(drift('virtualservice', vs_body, dict(vs_body, scaleout_ecmp=True), ig) == [], 'scaleout_ecmp')
            pem = '-----BEGIN CERTIFICATE-----\r\nMIIB\r\n-----END CERTIFICATE-----\r\n'
            want = {'name': 'p', 'crl_check': False,
                    'ca_certs': [{'certificate': pem, 'days_until_expire': 365, 'text': 'a'}]}
            have = {'name': 'p', 'crl_check': False,
                    'ca_certs': [{'certificate': pem.replace('\r\n', '\n').strip(), 'days_until_expire': 1000,
                                  'text': 'b'}]}
            expect(drift('pkiprofile', want, have, ig) == [], 'the same PEM with other line ends, and computed fields')
            other = {'name': 'p', 'crl_check': False, 'ca_certs': [{'certificate': pem.replace('MIIB', 'MIIC')}]}
            expect(drift('pkiprofile', want, other, ig) == ['ca_certs'], 'another certificate is a difference')
            expect(drift('pkiprofile', want, dict(have, crl_check=True), ig) == ['crl_check'])
        check('what green sets itself (scaleout_ecmp on NSX-T) or recomputes (a PKI profile\'s CA certificate '
              'details) is never a difference; another certificate is', target_owned)

        def vip_dns_names():
            vv = W['site_a'].by_name('vsvip', 'vsvip-portal')
            expect([x.get('fqdn') for x in vv.get('dns_info') or []] == ['portal.example.com'], vv.get('dns_info'))
            prov = W['site_b'].put('ipamdnsproviderprofile', {'name': 'corp-infoblox', 'type': 'IPAMDNS_TYPE_INFOBLOX_DNS'})
            cloud = W['site_b'].by_name('cloud', 'site-b-nsx-cloud')
            cloud['dns_provider_ref'] = prov['url']
            try:
                _, o = cv()
                expect('are not written on site_b: cloud site-b-nsx-cloud registers them with DNS provider corp-infoblox' in o,
                       o[-3000:])
                expect('are not written on site_a' not in o, 'site_a has no DNS provider')
            finally:
                cloud.pop('dns_provider_ref')
        check('a VIP\'s DNS names (App Domain Name) come across, except where the site\'s cloud would register them '
              'with an outside DNS provider', vip_dns_names)

        def keys_never_stored():
            for name in os.listdir(d):
                with open(os.path.join(d, name), 'rb') as fh:
                    expect(b'MIIEselftest' not in fh.read(), '%s holds a private key' % name)
            expect(W['site_a'].keys and all(k == PEM_KEY for k in W['site_a'].keys.values()))
        check('private keys go from blue to green and are never written to disk or a journal', keys_never_stored)

        def gslb_built():
            g = W['site_a'].by_name('gslb', 'Default')
            expect(set(x['domain_name'] for x in g['dns_configs']) >= set('gslb.' + z for z in zones))
            d2dns = [dv for st in g['sites'] if st['name'] == 'SITE-B' for dv in st['dns_vses']][0]
            expect(set(d2dns['domain_names']) == set('gslb.' + z for z in zones), ('a DNS service that lists what it '
                                                                                 'hosts lists them all', d2dns))
            expect(all(st.get('password') == 'site-secret' for st in g['sites']),
                   ('a site password read back masked is kept as the leader holds it', g['sites']))
            expect(not [c for c in W['site_a'].calls if c['type'] == 'gslb' and c['method'] == 'PATCH'],
                   'never a PATCH that adds to a list of sub-objects: 32.1 refuses it')
            for site in ('site_a', 'site_b'):
                zs = [z['domain_name'] for z in W[site].by_name('applicationprofile', 'site-gslb-dns')
                      ['dns_service_profile']['dns_zones']]
                expect(set(zs) >= set('gslb.' + z for z in zones), (site, zs))
            svc = W['site_a'].by_name('gslbservice', 'portal-443')
            expect(svc['domain_names'] == ['portal.gslb.example.com', 'portal.gslb.myexample.com'], svc['domain_names'])
            expect([x['priority'] for x in svc['groups']] == [20, 10] and svc['ttl'] == 30)
            hm = W['site_a'].by_name('healthmonitor', 'gslb-tcp-443')
            expect('canary' not in json.dumps(svc) and [uuid_of(x) for x in svc.get('health_monitor_refs')] == [hm['uuid']],
                   ('the template\'s own monitor is not copied; the TCP monitor to its port is', svc.get('health_monitor_refs')))
            expect(hm['type'] == 'HEALTH_MONITOR_TCP' and hm['monitor_port'] == 443 and hm['is_federated'] is True, hm)
            expect(svc['groups'][0]['members'][0]['ip']['addr'] == vip_of('site_a', 'vsvip-portal'))
            expect(W['site_a'].by_name('gslbservice', 'sni-parent')['domain_names'] ==
                   ['api.corp.gslb.example.com', 'app.gslb.exampleapp.com'], 'every name on one VIP, one service')
            expect('dns-gslb has the DNS service itself as a member' in out)
        check('GSLB: subdomains, both sites\' DNS zones, one service per VIP from the template, site_a 20 / site_b 10',
              gslb_built)
        f1 = flips()

        def ready():
            r = f1['portal.myexample.com']
            expect(r['state'] == 'READY' and r['vip'] == vip_of('site_a', 'vsvip-portal'), r)
            expect(r['vip_site_b'] == vip_of('site_b', 'vsvip-portal') and r['dns_vips'] == ' '.join(gslb_vips))
            expect(r['zone'] == 'myexample.com' and r['host'] == 'portal' and r['gslb_fqdn'] == 'portal.gslb.myexample.com')
            expect(f1['app.exampleapp.com']['state'] == 'READY' and f1['api.corp.example.com']['state'] == 'READY')
            expect(f1['dg.example.com']['state'] == 'READY', f1['dg.example.com'])
        check('flip list: READY once every GSLB DNS service and the clients\' DNS answer site_a\'s VIP', ready)

        print('\nconverge again')
        reset_calls()
        rc2, out2 = cv(commit=True)
        p2 = plan_rows()
        check('a second run changes nothing: no write anywhere, nothing to ADD or UPDATE',
              lambda: expect(not writes('site_a') and not writes('site_b') and not any(
                  e['state'] in ('ADD', 'UPDATE') for e in p2.values()) and 'UNCHANGED  portal-443' in out2,
                  (writes('site_a')[:3], [k for k, e in p2.items() if e['state'] in ('ADD', 'UPDATE')][:5])))

        print('\nblue changes before a flip')
        bp = W['blue'].by_name('pool', 'portal-pool')
        bp['servers'].append({'ip': ip4('10.1.30.13'), 'port': 443})
        bv = W['blue'].by_name('vsvip', 'vsvip-portal')
        bv['description'] = 'portal VIP'
        bc = W['blue'].by_name('sslkeyandcertificate', 'portal-cert')
        bc['certificate']['certificate'] = PEM_CERT.replace('selftest', 'renewed')
        W['blue'].keys[bc['uuid']] = PEM_KEY
        W['blue'].by_name('virtualservice', 'portal-443')['description'] = 'the portal'
        before = dict((s, vip_of(s, 'vsvip-portal')) for s in ('site_a', 'site_b'))
        reset_calls()
        rc3, out3 = cv(commit=True)
        p3 = plan_rows()

        def updates():
            for site in ('site_a', 'site_b'):
                for k in ('pool/portal-pool', 'vsvip/vsvip-portal', 'sslkeyandcertificate/portal-cert',
                          'virtualservice/portal-443'):
                    expect(p3['%s %s' % (site, k)]['state'] == 'UPDATE', (site, k, p3['%s %s' % (site, k)]))
                puts = [c for c in W[site].calls if c['method'] == 'PUT' and c['type'] in PORTABLE]
                expect(len(puts) == 4, (site, [c['type'] for c in puts]))
                expect(len(W[site].by_name('pool', 'portal-pool')['servers']) == 3)
                expect(cert_pem(W[site].by_name('sslkeyandcertificate', 'portal-cert')) == cert_pem(bc))
            expect(any(c['method'] == 'GET' and c['params'].get('export_key') == 'True' for c in W['blue'].calls),
                   'a renewed certificate takes its key from blue')
        check('UPDATE: a pool, a VIP and a renewed certificate follow blue at both sites', updates)
        check('an updated VIP keeps its address, so GSLB and DNS do not move',
              lambda: expect(dict((s, vip_of(s, 'vsvip-portal')) for s in ('site_a', 'site_b')) == before, before))

        def update_keeps_live():
            for site in ('site_a', 'site_b'):
                put = [c['body'] for c in W[site].calls if c['method'] == 'PUT' and c['type'] == 'virtualservice']
                expect(put and put[0]['enabled'] is True and put[0]['traffic_enabled'] is True, (site, 'the PUT itself'))
                expect(not [c for c in W[site].calls if c['method'] == 'PATCH' and c['type'] == 'virtualservice'],
                       (site, 'no live-state repair was needed after the update'))
        check('an updated live service is never taken down by its update', update_keeps_live)
        reset_calls()
        rc4, out4 = cv(commit=True)
        check('after the update the next run is UNCHANGED again',
              lambda: expect(not [c for c in writes('site_a') + writes('site_b') if c['type'] in PORTABLE],
                             [(c['method'], c['type']) for c in writes('site_a')][:4]))

        def rewritten():
            W['site_a'].rewrite[('healthmonitor', 'description')] = str.upper
            W['blue'].by_name('healthmonitor', 'App-HTTPS')['description'] = 'Checks the portal'
            _, o1 = cv(commit=True)
            expect('healthmonitor/App-HTTPS on site_a still differs after the update in description' in o1, o1[-2000:])
            cfg['avi_ignore_fields'] = ['healthmonitor.description']
            reset_calls()
            _, o2 = cv(commit=True)
            expect(not [c for c in writes('site_a') if c['type'] == 'healthmonitor'], 'ignored fields are no UPDATE')
            W['site_a'].rewrite.clear()
        check('a field the target rewrites is reported, and avi_ignore_fields ends the update loop', rewritten)

        def gslb_names_kept():
            W['site_a'].by_name('gslbservice', 'portal-443')['domain_names'].append('portal-old.gslb.example.com')
            cfg['gslb_ttl'] = 60
            try:
                reset_calls()
                _, o = cv(commit=True)
                svc = W['site_a'].by_name('gslbservice', 'portal-443')
                expect('UPDATE     portal-443' in o and svc['ttl'] == 60, o[-2500:])
                expect({'portal-old.gslb.example.com', 'portal.gslb.myexample.com'} <= set(svc['domain_names']),
                       svc['domain_names'])
            finally:
                cfg['gslb_ttl'] = 30
                cv(commit=True)
        check('an UPDATE of a GSLB service keeps every name it holds: names are only ever added', gslb_names_kept)

        def template_flipped():
            t = W['site_a'].by_name('gslbservice', 'canary')
            for grp in t['groups']:
                grp['priority'] = 30 - grp['priority']  # site_a 10, site_b 20: the canary moved to site_b for a test
            try:
                reset_calls()
                _, o = cv(commit=True)
                svc = W['site_a'].by_name('gslbservice', 'portal-443')
                expect([x['priority'] for x in svc['groups']] == [20, 10], svc['groups'])
                expect(not [c for c in writes('site_a') if c['type'] == 'gslbservice'], 'no service follows it')
            finally:
                for grp in t['groups']:
                    grp['priority'] = 30 - grp['priority']
        check('a template flipped to site_b for a test flips no service: the configured priorities win', template_flipped)

        print('\na name is flipped')
        ad['portal.myexample.com'] = ('CNAME', 'portal.gslb.myexample.com')
        bp['servers'].append({'ip': ip4('10.1.30.14'), 'port': 443})
        W['blue'].by_name('pool', 'sni-pool')['servers'].append({'ip': ip4('10.1.30.15'), 'port': 443})
        reset_calls()
        rc5, out5 = cv(commit=True)
        p5, f5 = plan_rows(), flips()

        def frozen():
            for site in ('site_a', 'site_b'):
                e = p5['%s pool/portal-pool' % site]
                expect(e['state'] == 'FROZEN' and 'portal.myexample.com' in e['detail'], e)
                expect(len(W[site].by_name('pool', 'portal-pool')['servers']) == 3, 'green owns it now')
                expect(p5['%s pool/sni-pool' % site]['state'] == 'UPDATE', 'an app not flipped still follows blue')
            expect(f5['portal.myexample.com']['state'] == 'MOVED' and f5['portal.example.com']['state'] == 'READY')
        check('once a name is flipped its application is FROZEN; the rest still follow blue', frozen)

        def gslb_flipped_kept():
            svc = W['site_a'].by_name('gslbservice', 'portal-443')
            svc['groups'][1]['priority'] = 30  # site_b takes over on the leader for maintenance at site_a
            svc['ttl'] = 300
            reset_calls()
            _, o = cv(commit=True)
            svc = W['site_a'].by_name('gslbservice', 'portal-443')
            expect([x['priority'] for x in svc['groups']] == [20, 30] and svc['ttl'] == 300, svc['groups'])
            expect('DIFFERS    portal-443' in o and '--rewrite-gslb' in o, o[-2500:])
            expect(not [c for c in writes('site_a') if c['type'] == 'gslbservice'], 'the leader is left as it is')
            cv(commit=True, rewrite_gslb=True)
            svc = W['site_a'].by_name('gslbservice', 'portal-443')
            expect([x['priority'] for x in svc['groups']] == [20, 10] and svc['ttl'] == 30, svc['groups'])
        check('a flipped application\'s GSLB service stays as the leader has it; --rewrite-gslb writes it',
              gslb_flipped_kept)

        def every_server():
            bp['servers'].append({'ip': ip4('10.1.30.20'), 'port': 443})
            saved = cfg['dns_servers']
            cfg['dns_servers'] = ['192.0.2.54', '192.0.2.53']  # .54 has not caught up with the flip
            stale.add('192.0.2.54')
            try:
                cv()
                expect(flips()['portal.myexample.com']['state'] == 'MOVED', flips()['portal.myexample.com'])
                expect(plan_rows()['site_a pool/portal-pool']['state'] == 'FROZEN', plan_rows()['site_a pool/portal-pool'])
                cfg['dns_servers'] = ['192.0.2.53', '192.0.2.55']
                down.add('192.0.2.55')
                cv()
                e = plan_rows()['site_a pool/sni-pool']
                expect(e['state'] in ('FROZEN', 'UNCHANGED') and ('flip state unknown' in e['detail']
                                                                  or e['state'] == 'UNCHANGED'), e)
                expect(flips()['app.exampleapp.com']['state'] != 'MOVED', 'unknown is not flipped in the list')
            finally:
                cfg['dns_servers'] = saved
                stale.discard('192.0.2.54')
                down.discard('192.0.2.55')
        check('every DNS server is asked: one that has the flip is enough, one that does not answer leaves it '
              'unknown', every_server)

        def never_offline():
            cfg['avi_live_site_b'] = 'none'
            reset_calls()
            rc, o = cv(commit=True)
            expect(W['site_b'].by_name('virtualservice', 'sni-parent')['enabled'] is True and rc == 1
                   and 'HELD       sni-parent' in o and 'needs --allow-offline' in o, o[-1500:])
            expect(not [c for c in writes('site_b') if c['type'] == 'virtualservice'], 'nothing is taken offline')
            _, o = cv(commit=True, allow_offline=True)
            v2 = W['site_b'].by_name('virtualservice', 'portal-443')
            expect(v2['enabled'] is True and 'portal-443 stays live: green owns it' in o, o[-1500:])
            expect(W['site_b'].by_name('virtualservice', 'sni-parent')['enabled'] is False, 'not flipped: staged')
            expect(W['site_b'].by_name('virtualservice', 'internal-api')['enabled'] is True,
                   'a service this tool did not make is never touched')
            cfg['avi_live_site_b'] = 'all'
            cv(commit=True)
            expect(W['site_b'].by_name('virtualservice', 'sni-parent')['enabled'] is True)
        check('live state follows avi_live; a live service goes offline only with --allow-offline, a flipped '
              'one never; green\'s own are never touched', never_offline)

        def flipped_live_kept():
            W['site_a'].by_name('virtualservice', 'portal-443')['enabled'] = False  # a failover test on green
            reset_calls()
            _, o = cv(commit=True)
            expect(W['site_a'].by_name('virtualservice', 'portal-443')['enabled'] is False
                   and 'portal-443 stays off: green owns it' in o and '--live-flipped' in o, o[-2000:])
            cv(commit=True, live_flipped=True)
            expect(W['site_a'].by_name('virtualservice', 'portal-443')['enabled'] is True)
            cfg['avi_live_site_a'] = 'none'  # even asked for with every flag, a flipped app is never taken down
            try:
                _, o = cv(commit=True, live_flipped=True, allow_offline=True)
                expect(W['site_a'].by_name('virtualservice', 'portal-443')['enabled'] is True
                       and 'portal-443 stays live: green owns it' in o, o[-2000:])
            finally:
                cfg['avi_live_site_a'] = 'all'
                cv(commit=True)
        check('a flipped application stays up or down as green has it; --live-flipped brings it up',
              flipped_live_kept)

        def unknown_flip_state():
            W['blue'].by_name('pool', 'sni-pool')['servers'].append({'ip': ip4('10.1.30.16'), 'port': 443})
            down.add('192.0.2.53')
            try:
                reset_calls()
                _, o = cv(commit=True)
                e = plan_rows()['site_a pool/sni-pool']
                expect(e['state'] == 'FROZEN' and 'flip state unknown' in e['detail'], e)
                expect(not [c for c in writes('site_a') if c['type'] == 'pool'])
                _, o = cv(commit=True, trust_export=True)
                expect(plan_rows()['site_a pool/sni-pool']['state'] == 'UPDATE')
            finally:
                down.discard('192.0.2.53')
        check('when no DNS server answers, apps count as flipped until one does (or --trust-export)',
              unknown_flip_state)

        def flipped_before_export():
            moved = DNS_EXPORT.replace('"portal.myexample.com","A","10.1.92.45","3600","myexample.com"',
                                       '"portal.myexample.com","CNAME","portal.gslb.myexample.com","60","myexample.com"')
            with open(dns_csv, 'w', encoding='utf-8-sig') as fh:
                fh.write(moved)
            try:
                down.add('192.0.2.53')
                _, o = cv(trust_export=True)
                r = flips()['portal.myexample.com']
                expect(r['state'] == 'MOVED' and r['blue_ip'] == '10.1.92.45' and r['member_vs'] == 'portal-443', r)
                expect(plan_rows()['site_a pool/portal-pool']['state'] in ('FROZEN', 'UNCHANGED'))
            finally:
                down.discard('192.0.2.53')
                with open(dns_csv, 'w', encoding='utf-8-sig') as fh:
                    fh.write(DNS_EXPORT)
        check('a name already flipped in the export is tied back through its GSLB service, and stays FROZEN',
              flipped_before_export)

        def rolled_back_since():
            moved = DNS_EXPORT.replace('"portal.myexample.com","A","10.1.92.45","3600","myexample.com"',
                                       '"portal.myexample.com","CNAME","portal.gslb.myexample.com","60","myexample.com"')
            with open(dns_csv, 'w', encoding='utf-8-sig') as fh:
                fh.write(moved)
            ad['portal.myexample.com'] = ('A', '10.1.92.45')  # rolled back after that export
            bp['servers'].append({'ip': ip4('10.1.30.22'), 'port': 443})
            try:
                cv()
                r = flips()['portal.myexample.com']
                expect(r['state'] in ('READY', 'NOT READY') and 'rolled back since the DNS export' in r['note'], r)
                expect(plan_rows()['site_a pool/portal-pool']['state'] == 'UPDATE', 'it follows blue again')
            finally:
                ad['portal.myexample.com'] = ('CNAME', 'portal.gslb.myexample.com')
                with open(dns_csv, 'w', encoding='utf-8-sig') as fh:
                    fh.write(DNS_EXPORT)
        check('a name the export saw flipped but every DC now answers on blue is not taken for flipped',
              rolled_back_since)

        def green_direct():
            with open(dns_csv, 'w', encoding='utf-8-sig') as fh:
                fh.write(DNS_EXPORT + '"direct.exampleapp.com","A","%s","300","exampleapp.com"\n'
                         % vip_of('site_a', 'vsvip-sni'))
            W['blue'].by_name('pool', 'sni-pool')['servers'].append({'ip': ip4('10.1.30.21'), 'port': 443})
            try:
                cv()
                r = flips()['direct.exampleapp.com']
                expect(r['state'] == 'MANUAL' and 'points straight at green (sni-parent)' in r['note'], r)
                e = plan_rows()['site_a pool/sni-pool']
                expect(e['state'] == 'FROZEN' and 'direct.exampleapp.com' in e['detail'], e)
                cfg['gslb_exclude'] = ['direct.*']
                cv()
                expect('direct.exampleapp.com' not in flips() and plan_rows()['site_a pool/sni-pool']['state'] == 'UPDATE')
            finally:
                cfg.pop('gslb_exclude', None)
                with open(dns_csv, 'w', encoding='utf-8-sig') as fh:
                    fh.write(DNS_EXPORT)
        check('a name pointed straight at a green VIP counts as flipped (a test name goes in gslb_exclude)',
              green_direct)

        print('\nwhat green made itself')

        def adopt():
            e = plan_rows()['site_b healthmonitor/App-HTTPS']
            expect(e['state'] == 'KEPT' and not [c for c in W['site_b'].calls if c['type'] == 'healthmonitor'
                                                 and c['method'] == 'PUT'])
            reset_calls()
            _, o = cv(commit=True, adopt=True)
            e = plan_rows()['site_b healthmonitor/App-HTTPS']
            expect(Registry(cfg).owns('site_b', 'healthmonitor', 'App-HTTPS', W['site_b'].by_name('healthmonitor', 'App-HTTPS')['uuid']))
            # Adopted, it follows the same rules: it serves a flipped application, so it is FROZEN.
            expect(e['state'] == 'FROZEN' and 'portal.myexample.com' in e['detail'], e)
            expect(not [c for c in W['site_b'].calls if c['type'] == 'healthmonitor' and c['method'] == 'PUT'])
        check('a same-named object green made is KEPT until --adopt; then the usual rules apply', adopt)

        def lost_registry():
            os.rename(Registry(cfg).path, Registry(cfg).path + '.away')
            try:
                W['blue'].by_name('pool', 'sni-pool')['servers'].append({'ip': ip4('10.1.30.17'), 'port': 443})
                reset_calls()
                _, o = cv(commit=True)
                expect(not writes('site_a') and not writes('site_b'), [(c['method'], c['type']) for c in writes('site_a')][:4])
                expect(plan_rows()['site_a pool/sni-pool']['state'] == 'KEPT' and 'KEPT       sni-parent' in o)
            finally:
                os.rename(Registry(cfg).path + '.away', Registry(cfg).path)
        check('without its registry the tool changes nothing that exists, GSLB services included', lost_registry)

        print('\nlimits and guards')

        def capacity_stop():
            cfg['avi_live_site_b'] = 'none'
            cv(commit=True, allow_offline=True)
            seg = W['site_b'].by_name('serviceenginegroup', 'site-b-se-group')
            seg['max_se'] = 2
            cfg['avi_live_site_b'] = 'all'
            reset_calls()
            rc, o = cv(commit=True)
            expect('STOP' in o and rc == 1 and not [c for c in writes('site_b') if c['type'] == 'virtualservice'], o[-1500:])
            cfg['avi_se_max_vs_per_se_site_b'] = 5  # what the operator raises it to: 2 x 5 places them all
            try:
                _, o = cv()
                expect('RAISE    SE group site-b-se-group: max_vs_per_se 1 -> 5' in o and seg['max_vs_per_se'] == 1, o[-1500:])
                rc, o = cv(commit=True)
                seg = W['site_b'].by_name('serviceenginegroup', 'site-b-se-group')  # the PUT replaced it
                expect('RAISED   SE group site-b-se-group: max_vs_per_se 1 -> 5' in o and 'STOP' not in o
                       and seg['max_vs_per_se'] == 5 and seg['max_se'] == 2, o[-1500:])
                expect(W['site_b'].by_name('virtualservice', 'sni-parent')['enabled'] is True)
                cfg['avi_se_max_vs_per_se_site_b'] = 3
                _, o = cv()
                expect('never lowered' in o and 'RAISE ' not in o, o[-1500:])
            finally:
                cfg.pop('avi_se_max_vs_per_se_site_b', None)
                seg = W['site_b'].by_name('serviceenginegroup', 'site-b-se-group')
                seg['max_se'], seg['max_vs_per_se'] = 10, 1
        check('live state stops, changing nothing, when an SE group could not place it all; avi_se_max_*_<site> '
              'raises the group (never lowers it)', capacity_stop)

        def default_group():
            cfg['avi_map_site_a'] = ['serviceenginegroup/Default-Group=serviceenginegroup/Default-Group']
            try:
                _, o = cv()
                e = plan_rows()['site_a virtualservice/dg-app']
                expect(e['state'] == 'BLOCKED' and 'would land in Default-Group' in e['detail'], e)
            finally:
                del cfg['avi_map_site_a']
        check('a service mapped into Default-Group is BLOCKED', default_group)

        def system_profile():
            dv = W['site_b'].by_name('virtualservice', 'site_b-gslb-dns')
            prof = W['site_b'].put('applicationprofile', {'name': 'System-DNS', 'type': 'APPLICATION_PROFILE_TYPE_DNS',
                                                     'dns_service_profile': {'dns_zones': []}})
            saved_ref = dv['application_profile_ref']

            def blocked_count(text):
                m = re.search(r'(\d+) blocked', text.strip().splitlines()[-1])
                return int(m.group(1)) if m else -1
            base = blocked_count(cv(commit=True)[1])
            dv['application_profile_ref'] = prof['url']
            try:
                reset_calls()
                rc, o = cv(commit=True)
                expect('FAIL  the DNS service on site_b uses System-DNS' in o and rc == 1, (rc, o[-2500:]))
                expect(blocked_count(o) == base + 1, ('the failure counts as blocked', base, o.strip().splitlines()[-1]))
                expect(not [c for c in writes('site_b') if c['type'] == 'applicationprofile'], 'System- profiles are not edited')
            finally:
                dv['application_profile_ref'] = saved_ref
        check('a GSLB DNS service on a System- profile is a failure, and that profile is never edited', system_profile)

        def made_by_hand():
            W['site_a'].put('healthmonitor', {'name': 'Auth-HM', 'type': 'HEALTH_MONITOR_HTTP'})
            _, o = cv()
            p = plan_rows()
            expect(p['site_a healthmonitor/Auth-HM']['state'] == 'UNCHANGED' and 'made by hand' in p['site_a healthmonitor/Auth-HM']['detail'])
            expect(p['site_a pool/legacy-pool']['state'] == 'ADD', 'what depended on it can be added now')
        check('what a blocker says to make by hand is taken as it is once made', made_by_hand)

        def missing_secret():
            cfg['avi_secrets'] = ['healthmonitor/Auth-HM']
            try:
                reset_calls()
                _, o = cv(commit=True)  # no terminal here, and nothing in the environment
            finally:
                cfg.pop('avi_secrets', None)
            expect('secrets    healthmonitor/Auth-HM' in o and 'it is skipped, with what uses it' in o, o[-3000:])
            expect('REFUSED  healthmonitor/Auth-HM' in o and 'AVI_SECRET_HEALTHMONITOR_AUTH_HM_AUTHENTICATION_'
                   in o, o[-3000:])
            expect('pool/legacy-pool' in o and 'not written: it uses healthmonitor/Auth-HM' in o, o[-3000:])
            expect('live site_b' in o and 'STOPPED' not in o, 'the run carries on past it')
            expect(not [c for c in writes('site_b') if c['type'] == 'healthmonitor'], 'nothing posted without it')
        check('a secret nobody gives skips its object and what uses it, and the run carries on', missing_secret)

        def supplied_secret():
            env = secret_env('healthmonitor', 'Auth-HM', 'authentication.password')
            env_user = secret_env('healthmonitor', 'Auth-HM', 'authentication.username')
            expect(env == 'AVI_SECRET_HEALTHMONITOR_AUTH_HM_AUTHENTICATION_PASSWORD', env)
            _, o = cv()
            detail = plan_rows()['site_b healthmonitor/Auth-HM']['detail']
            expect('List it in avi_secrets' in detail and 'authentication.username' in detail,
                   ('the masked username is a secret too', detail))
            cfg['avi_secrets'] = ['healthmonitor/Auth-HM']
            os.environ[env], os.environ[env_user] = 'Sup3rS3cret', 'svc-monitor'
            try:
                _, o = cv()
                detail = plan_rows()['site_b healthmonitor/Auth-HM']['detail']
                expect('authentication.username, authentication.password typed in when written' in detail, detail)
                reset_calls()
                _, o = cv(commit=True)
                posts = [c for c in W['site_b'].calls if c['method'] == 'POST' and c['type'] == 'healthmonitor']
                expect(posts and posts[0]['body']['authentication'] ==
                       {'username': 'svc-monitor', 'password': 'Sup3rS3cret'}, [c['body'] for c in posts])
                expect(not [c for c in W['site_a'].calls if c['type'] == 'healthmonitor' and c['method'] != 'GET'],
                       'site_a keeps the one made by hand')
                expect(plan_rows()['site_b pool/legacy-pool']['state'] == 'ADD', 'what waited on it goes too')
                for fn in os.listdir(d):
                    with open(os.path.join(d, fn), 'rb') as fh:
                        expect(b'Sup3rS3cret' not in fh.read(), '%s holds the secret' % fn)
                reset_calls()
                cv(commit=True)
                expect(not [c for c in writes('site_b') if c['type'] == 'healthmonitor'], 'no update on every run')
            finally:
                cfg.pop('avi_secrets', None)
                os.environ.pop(env, None)
                os.environ.pop(env_user, None)
        check('what blue masks (a password, and a username shown as <sensitive>) is typed in, or read from the '
              'environment, when written; never stored', supplied_secret)

        def one_site():
            reset_calls()
            _, o = cv(site='site_a', vs='portal-*')
            p = plan_rows()
            expect(all(k.startswith('site_a ') for k in p) and 'GSLB       not converged with --site' in o)
            expect(not any('sni' in k for k in p), 'only the portal services and what they use')
        check('--site and --vs narrow the run; GSLB waits for a run over every site', one_site)

        def no_names():
            os.rename(dns_csv, dns_csv + '.away')
            try:
                W['blue'].by_name('pool', 'sni-pool')['servers'].append({'ip': ip4('10.1.30.18'), 'port': 443})
                reset_calls()
                _, o = cv(commit=True)
                expect('UPDATEs are withheld' in o and not [c for c in writes('site_a') if c['method'] == 'PUT'], o[:1500])
                # Without the export no flip can be seen, so nothing goes offline, even when asked.
                cfg['avi_live_site_b'] = 'none'
                reset_calls()
                _, o = cv(commit=True, allow_offline=True)
                expect('--allow-offline is not used' in o and W['site_b'].by_name('virtualservice', 'portal-443')['enabled']
                       and not [c for c in writes('site_b') if c['type'] == 'virtualservice'], o[-2000:])
            finally:
                cfg['avi_live_site_b'] = 'all'
                os.rename(dns_csv + '.away', dns_csv)
        check('without the DNS export nothing that exists is updated: flipped apps cannot be told apart', no_names)

        def export_gap():
            with open(dns_csv, 'w', encoding='utf-8-sig') as fh:
                fh.write('\n'.join(ln for ln in DNS_EXPORT.split('\n') if 'exampleshop.org' not in ln))
            try:
                W['blue'].by_name('pool', 'sni-pool')['servers'].append({'ip': ip4('10.1.30.19'), 'port': 443})
                reset_calls()
                _, o = cv(commit=True)
                expect('the export holds no record of exampleshop.org' in o and 'UPDATEs are withheld' in o, o[:2000])
                expect(not [c for c in writes('site_a') if c['method'] == 'PUT'], 'nothing that exists is updated')
                _, o = quiet(status_cmd, cfg, ns(export=None, names=None))
                expect('WARNING   the DNS export holds no record of exampleshop.org' in o, o[:1500])
            finally:
                with open(dns_csv, 'w', encoding='utf-8-sig') as fh:
                    fh.write(DNS_EXPORT)
        check('an export that lacks a zone of gslb_zones: nothing that exists is updated, and status says so',
              export_gap)

        def undelegated_zone():
            undelegated.add('gslb.exampleapp.com')
            try:
                quiet(status_cmd, cfg, ns(export=None, names=None))
                r = flips()['app.exampleapp.com']
                expect(r['state'] == 'NOT READY' and 'is gslb.exampleapp.com delegated?' in r['note'], r)
                expect(flips()['portal.example.com']['state'] == 'READY', 'other zones are not affected')
            finally:
                undelegated.discard('gslb.exampleapp.com')
        check('a GSLB name the clients\' DNS cannot resolve is NOT READY: its delegation is missing', undelegated_zone)

        def target_is_blue():
            global CLIENT_FACTORY
            saved_factory = CLIENT_FACTORY
            try:
                for other, says in (('blue', "is blue's own cluster"), ('site_a', 'reach the same cluster')):
                    CLIENT_FACTORY = (lambda o: lambda c, role, site: W['blue'] if role == 'source' else
                                      W[o] if site == 'site_b' else W[site])(other)
                    _POOL.clear()
                    reset_calls()
                    exc = cv_raises(commit=True)
                    expect(exc is not None and says in str(exc), (other, exc))
                    expect(not writes('blue') and not writes('site_a'), 'refused before any write')
            finally:
                CLIENT_FACTORY = saved_factory
                _POOL.clear()
        check('a target that reaches blue, or the same cluster as another site, is refused before any write',
              target_is_blue)

        def lost_reply():
            b = W['blue']
            vv = copy.deepcopy(b.by_name('vsvip', 'vsvip-noname'))
            for k in ('uuid', 'url'):
                vv.pop(k)
            vv['name'], vv['vip'][0]['ip_address'] = 'vsvip-late', ip4('10.1.92.70')
            b.put('vsvip', vv)
            vs = copy.deepcopy(b.by_name('virtualservice', 'internal-api'))
            for k in ('uuid', 'url'):
                vs.pop(k)
            vs.update(name='late-app', vsvip_ref=b.ref('vsvip', 'vsvip-late'), traffic_enabled=True)
            b.put('virtualservice', vs)
            W['site_a'].lose.add('virtualservice/late-app')
            exc = cv_raises(commit=True)
            expect(exc is not None and 'timed out' in str(exc), exc)
            made = W['site_a'].by_name('virtualservice', 'late-app')
            expect(Registry(cfg).items.get(('site_a', 'virtualservice', 'late-app')) is None, 'no uuid came back')
            _, o = cv(commit=True)
            reg2 = Registry(cfg)
            expect(reg2.items.get(('site_a', 'virtualservice', 'late-app')) == made['uuid'] and 'TAKEN OVER' in o
                   and reg2.how[('site_a', 'virtualservice', 'late-app')] == 'added', o[-2500:])
            expect(W['site_a'].by_name('virtualservice', 'late-app')['enabled'] is True, 'set live like the rest')
            expect(not reg2.pending, reg2.pending)
        check('an object created by a write whose reply was lost is taken over by the next run', lost_reply)

        def no_resolver():
            global resolvers
            saved_resolvers = resolvers
            resolvers = lambda c: ([], 'nowhere')
            try:
                quiet(status_cmd, cfg, ns(export=None, names=None))
                r = flips()['portal.example.com']
                expect(r['state'] == 'NOT READY' and 'no DNS server to prove the delegation' in r['note'], r)
            finally:
                resolvers = saved_resolvers
        check('with no DNS server to ask, nothing is READY: the delegation is unproven', no_resolver)

        def pg(**kw):
            a = dict(commit=False, site=None, journal=None, export=None, names=None)
            a.update(kw)
            return quiet(purge_cmd, cfg, ns(**a))

        def vs_names(label):
            return set(o['name'] for o in W[label].db.get('virtualservice', {}).values())

        def refused_goes_on():
            b = W['blue']
            for t, src, name, extra in (('pool', 'sql-pool', 'late-pool', {}),
                                        ('vsvip', 'vsvip-late', 'vsvip-late2', None),
                                        ('virtualservice', 'late-app', 'late2-app', None)):
                x = copy.deepcopy(b.by_name(t, src))
                for k in ('uuid', 'url'):
                    x.pop(k)
                x['name'] = name
                if t == 'vsvip':
                    x['vip'][0]['ip_address'] = ip4('10.1.92.71')
                if t == 'virtualservice':
                    x.update(vsvip_ref=b.ref('vsvip', 'vsvip-late2'), pool_ref=b.ref('pool', 'late-pool'))
                b.put(t, x)
            W['site_a'].refuse['pool/late-pool'] = 'Pool late-pool has a setting this release does not accept'
            try:
                reset_calls()
                _, o = cv(commit=True)
                expect('REFUSED  pool/late-pool' in o and 'a setting this release does not accept' in o, o[-2500:])
                expect('not written: it uses pool/late-pool, which was refused' in o, o[-2500:])
                expect('late2-app' not in vs_names('site_a') and 'late2-app' in vs_names('site_b'),
                       'site_a skips only what depends on it; site_b goes on')
                expect('live site_a' in o and not Registry(cfg).pending, 'the run carries on; nothing left pending')
            finally:
                W['site_a'].refuse.clear()
            cv(commit=True)
            expect('late2-app' in vs_names('site_a'), 'once the cause is gone, the next run writes it')
        check('a write the controller refuses is reported with its reason and skipped with what depends on it; '
              'the rest goes on', refused_goes_on)

        def purge_needs_names():
            os.rename(dns_csv, dns_csv + '.away')
            try:
                try:
                    with contextlib.redirect_stdout(io.StringIO()):
                        purge_cmd(cfg, ns(commit=True, site=None, journal=None, export=None, names=None))
                except ValueError as exc:
                    expect('needs the DNS export' in str(exc), exc)
                else:
                    expect(False, 'a purge went ahead without knowing which applications are flipped')
                expect(not [c for c in writes('site_a') + writes('site_b') if c['method'] == 'DELETE'])
            finally:
                os.rename(dns_csv + '.away', dns_csv)
        check('once GSLB services exist, a purge needs the DNS export to tell flipped applications apart',
              purge_needs_names)

        def purge_one_site():
            reset_calls()
            rc, o = pg(commit=True, site='site_b')
            expect(rc == 0 and 'sni-parent' in vs_names('site_b') and 'a member of GSLB service sni-parent' in o, o[-2500:])
            expect(not writes('site_a') and 'left as it is with --site' in o)
            expect('late-app' not in vs_names('site_b'), 'not a GSLB member: gone')
            cv(commit=True)  # back again
            expect('late-app' in vs_names('site_b'))
        check('purge --site leaves GSLB alone, and with it every service that is still a GSLB member',
              purge_one_site)

        def purge_and_redeploy():
            reset_calls()
            rc, o = pg()
            expect(rc == 2 and not writes('site_a') and not writes('site_b') and 'DRY RUN' in o, (rc, o[-1500:]))
            expect('serves a flipped application' in o, o[-2500:])
            hm = W['site_a'].by_name('healthmonitor', 'SQL-HM')
            with open(Registry(cfg).path, 'a') as fh:  # as if --adopt had handed it over
                fh.write(json.dumps({'site': 'site_a', 'type': 'healthmonitor', 'name': 'SQL-HM', 'uuid': hm['uuid'],
                                     'how': 'adopted'}) + '\n')
            reset_calls()
            rc, o = pg(commit=True)
            expect(rc == 0, o[-3000:])
            expect(W['site_a'].by_name('healthmonitor', 'SQL-HM') and 'on green before this tool (adopted)' in o,
                   'handed over, so it stays')
            for site in ('site_a', 'site_b'):
                names = vs_names(site)
                expect('sni-parent' not in names and 'late-app' not in names, (site, sorted(names)))
                expect({'portal-443', 'portal-80'} <= names, 'a flipped application stays')
                expect({'%s-gslb-dns' % site, '%s-canary' % site} <= names, 'what the tool did not make stays')
                expect(W[site].by_name('pool', 'portal-pool') and not [
                    x for x in W[site].db.get('pool', {}).values() if x['name'] == 'sni-pool'])
            expect('internal-api' in vs_names('site_b'), "green's own stays")
            expect([x for x in W['site_a'].db['healthmonitor'].values() if x['name'] == 'gslb-tcp-443'],
                   'the GSLB monitor stays while the flipped application\'s GSLB service uses it')
            expect(W['site_b'].by_name('healthmonitor', 'App-HTTPS'), 'adopted, so it stays')
            expect(W['site_a'].by_name('healthmonitor', 'Auth-HM'), 'made by hand, so it stays')
            svcs = set(x['name'] for x in W['site_a'].db.get('gslbservice', {}).values())
            expect('portal-443' in svcs and 'canary' in svcs and 'sni-parent' not in svcs, sorted(svcs))
            reg = Registry(cfg)
            expect(('site_a', 'virtualservice', 'sni-parent') not in reg.items and
                   ('site_a', 'virtualservice', 'portal-443') in reg.items)
            reset_calls()
            rc, o = pg(commit=True)
            expect(not [c for c in writes('site_a') + writes('site_b') if c['method'] == 'DELETE'], 'nothing left to delete')
            reset_calls()
            _, o = cv(commit=True)
            for site in ('site_a', 'site_b'):
                v = W[site].by_name('virtualservice', 'sni-parent')
                expect(v['enabled'] is True and v['traffic_enabled'] is True, (site, 'rebuilt and live'))
                expect('late-app' in vs_names(site))
            expect(W['site_a'].by_name('gslbservice', 'sni-parent')['domain_names'] ==
                   ['api.corp.gslb.example.com', 'app.gslb.exampleapp.com'])
            reset_calls()
            _, o = cv(commit=True)
            expect(not writes('site_a') and not writes('site_b'), [(c['method'], c['type']) for c in writes('site_a') + writes('site_b')][:6])
        check('purge removes what the tool made (never a flipped application, never what it did not make), '
              'converge rebuilds it, and the run after changes nothing', purge_and_redeploy)

        def status_only():
            reset_calls()
            rc, o = quiet(status_cmd, cfg, ns(export=None, names=None))
            expect(not writes('site_a') and not writes('site_b') and not W['blue'].calls, 'status reads green and DNS only')
            expect('MOVED     portal.myexample.com' in o and 'READY     portal.example.com' in o, o[:2000])
        check('status: every name\'s state and a fresh flip list, read-only, without logging in to blue', status_only)

        print('\ndiscover')
        disc = os.path.join(d, 'discovered.csv')

        def dc(**kw):
            a = dict(export=None, out=disc, config=None)
            a.update(kw)
            return quiet(discover_cmd, cfg, ns(**a))

        def discover_keeps_export():
            try:
                dc(out=None)  # gslb_names is the export from a DC
            except ValueError as exc:
                expect('never replaces it' in str(exc), exc)
            else:
                expect(False, 'discover replaced an export from a DC')
            expect(not names_discovered(dns_csv) and len(load_dns(dns_csv)) == 22)
        check('discover never replaces an export from a DC, which holds every name', discover_keeps_export)

        def discover_names():
            ptr[reverse_name('10.1.92.49')] = 'shop.exampleshop.org'  # nothing on blue names that VIP
            ptr[reverse_name('10.1.92.51')] = 'gone.example.com'  # a stale reverse record
            saved = cfg['dns_servers']
            cfg['dns_servers'] = ['192.0.2.54', '192.0.2.53']  # .54 has not caught up with the flip
            stale.add('192.0.2.54')
            cfg['gslb_discover_names'] = ['api.corp.example.com', 'canary.example.com']
            try:
                reset_calls()
                rc, o = dc()
            finally:
                cfg['dns_servers'] = saved
                stale.discard('192.0.2.54')
                cfg.pop('gslb_discover_names')
            expect(rc == 0 and names_discovered(disc), o[-2000:])
            expect(not writes('site_a') and not writes('site_b') and not writes('blue'), 'read-only')
            recs = dict(((r['fqdn'], r['type']), r) for r in load_dns(disc))
            p = recs.get(('portal.example.com', 'A')) or {}
            expect(p.get('data') == '10.1.92.45' and p.get('ttl') == 1200 and p.get('zone') == 'example.com',
                   ('the VsVip\'s DNS info, with the TTL DNS answers', p))
            expect(recs[('www.myexample.com', 'CNAME')]['data'] == 'portal.myexample.com', 'a certificate name')
            expect(recs[('portal.myexample.com', 'CNAME')]['data'] == 'portal.gslb.myexample.com',
                   'flipped: one DNS server seeing it is enough')
            expect(recs[('app.exampleapp.com', 'A')]['data'] == '10.1.92.46', 'an SNI domain')
            expect(recs[('shop.exampleshop.org', 'A')]['data'] == '10.1.92.49', 'through the VIP\'s reverse record')
            expect(recs[('api.corp.example.com', 'A')]['zone'] == 'corp.example.com', 'the child zone that holds it')
            expect(recs[('canary.example.com', 'CNAME')]['data'] == 'canary.gslb.example.com')
            expect(not any('.gslb.' in f for f, _ in recs), ('a GSLB name is never a record of its own', sorted(recs)))
            expect(not any(f in ('gone.example.com', 'sni.example.com', 'noname.example.com') for f, _ in recs),
                   'a name DNS does not hold is left out')
            expect('6 of 10 blue VIPs in use have a name; no DNS name points at these, and why:' in o
                   and 'vsvip-waf' not in o, o[-2500:])
            lines = dict((ln.split()[0], ln) for ln in o.splitlines()[o.splitlines().index(
                [x for x in o.splitlines() if 'blue VIPs in use have a name' in x][0]) + 1:] if ln.strip().startswith('vsvip'))
            expect('noname.example.com: not in DNS' in lines.get('vsvip-noname', '')
                   and 'gone.example.com: not in DNS' in lines['vsvip-noname'], ('why, for each', lines))
            expect('snat.example.com: not in DNS' in lines.get('vsvip-snat', ''), lines)
            none_ = nameless_lines(read(artefact(cfg, 'avi-export'))['inventory'],
                                   {'nameless': ['vsvip-snat'], 'why': {'vsvip-snat': []}})
            expect('no name on blue' in none_[0] and 'gslb_vip_alias' in none_[-1], ('a VIP blue gives no name', none_))
            expect('7 at a blue VIP, 1 following another name, 2 flipped to a GSLB name, 0 elsewhere, 5 not in DNS'
                   in o, o[-2500:])
        check('discover: names from VsVip DNS info, certificates, SNI domains, reverse records and '
              'gslb_discover_names, as DNS answers them, in the zone that holds them', discover_names)

        def discovered_drives_converge():
            cfg['gslb_zones'] = zones + ['exampleempty.com']  # a zone no name on blue is in
            try:
                reset_calls()
                _, o = cv(names=disc, allow_offline=True)
            finally:
                cfg['gslb_zones'] = zones
            expect(not writes('site_a') and not writes('site_b'))
            expect('discovered from blue' in o and '--allow-offline is not used' in o, o[-3000:])
            expect('holds no record' not in o, 'a discovered list claims no whole zone')
            f = flips()
            expect(f['portal.myexample.com']['state'] == 'MOVED', f['portal.myexample.com'])
            expect(f['portal.example.com']['state'] == 'READY', f['portal.example.com'])
            expect(f['www.myexample.com']['state'] == 'FOLLOWS', f['www.myexample.com'])
            api = f['api.corp.example.com']
            expect(api['zone'] == 'corp.example.com' and api['gslb_fqdn'] == 'api.corp.gslb.example.com', api)
            expect(f['shop.exampleshop.org']['gslb_fqdn'] == 'shop.gslb.exampleshop.org')
        check('converge takes discovered names as it takes an export, but not for --allow-offline',
              discovered_drives_converge)

        def discover_only_adds():
            def seen():
                return set((r['fqdn'], r['type'], r['data'], r['ttl'], r['zone']) for r in load_dns(disc))
            before = seen()
            down.add('192.0.2.53')
            try:
                dc()
            except ValueError as exc:
                expect('answers from this host' in str(exc) and 'nothing was changed' in str(exc), exc)
            else:
                expect(False, 'discover ran with no DNS server answering')
            finally:
                down.discard('192.0.2.53')
            expect(seen() == before, 'kept as it was')
            flaky.add(('192.0.2.53', 'api.corp.example.com'))  # it answers, but not about this name
            try:
                _, o = dc()
            finally:
                flaky.clear()
            expect('no DNS server answered for api.corp.example.com' in o and seen() == before,
                   ('what was known of a name nobody answered for is kept', o[-1500:]))
            _, o = dc()
            names = set(x[0] for x in seen())
            expect({'api.corp.example.com', 'canary.example.com', 'shop.exampleshop.org'} <= names,
                   'asked again and kept, though only the last run was given them')
            gone = ad.pop('legacy.example.com')
            try:
                dc()
                expect('legacy.example.com' not in set(x[0] for x in seen()), 'a name DNS no longer holds goes')
            finally:
                ad['legacy.example.com'] = gone
        check('discover only adds: what it wrote before is asked again and kept, and kept as it was while no DNS '
              'server answers', discover_only_adds)

        def fronted_vip():
            """A name that points at an address in front of a blue VIP (a NAT):
            discover says so, and gslb_vip_alias makes it that VIP's name."""
            ad['noname.example.com'] = ('A', '198.51.100.51')
            try:
                _, o = dc()
                expect('noname.example.com -> 198.51.100.51 (not a blue VIP)' in o, ('why, for that VIP', o[-2500:]))
                for bad, msg in ((['198.51.100.51=no-such-vip'], 'neither a VsVip on blue'),
                                 (['nat=vsvip-noname'], 'is not an IPv4 address'),
                                 (['10.1.92.45=vsvip-noname'], 'is already blue\'s VIP vsvip-portal')):
                    cfg['gslb_vip_alias'] = bad
                    try:
                        dc()
                    except ValueError as exc:
                        expect(msg in str(exc), exc)
                    else:
                        expect(False, ('accepted', bad))
                cfg['gslb_vip_alias'] = ['198.51.100.51=vsvip-noname']
                _, o = dc()
                expect('198.51.100.51 (not a blue VIP)' not in o, o[-2500:])
                rows_ = build_rows(cfg, read(artefact(cfg, 'avi-export')), load_dns(disc), {}, {}, {})
                r = [x for x in rows_ if x['fqdn'] == 'noname.example.com'][0]
                expect(r['action'] == 'PUBLISH' and r['gslb_fqdn'] == 'noname.gslb.example.com'
                       and r['blue_vsvip'] == 'vsvip-noname' and r['blue_ip'] == '198.51.100.51',
                       ('its GSLB name, and the address a rollback puts back', r))
                cfg.pop('gslb_vip_alias')
                rows_ = build_rows(cfg, read(artefact(cfg, 'avi-export')), load_dns(disc), {}, {}, {})
                nn = [x for x in rows_ if x['action'] == 'NONAME' and x['blue_vsvip'] == 'vsvip-noname'][0]
                expect('noname.example.com -> 198.51.100.51' in nn['note'], ('the flip list says why too', nn['note']))
                # Inferred: snat.example.com is a name blue gives vsvip-snat only, served from an F5 address.
                # noname.example.com is given to two VIPs, so the address it points at is no one's.
                ad['snat.example.com'] = ('A', '198.51.100.50')
                _, o = dc()
                expect('198.51.100.50   -> vsvip-snat' in o and '198.51.100.51' not in o.split('VIPs  ')[0], o[-2500:])
                rows_ = dict(((x['fqdn'] or x['blue_vsvip']), x) for x in build_rows(
                    cfg, read(artefact(cfg, 'avi-export')), load_dns(disc), {}, {}, {}))
                r = rows_['snat.example.com']
                expect(r['action'] == 'PUBLISH' and r['blue_vsvip'] == 'vsvip-snat' and r['blue_ip'] == '198.51.100.50'
                       and r.get('fronted') == 'inferred' and 'a flip moves it from 198.51.100.50' in r['note'], r)
                expect(rows_['vsvip-noname']['action'] == 'NONAME', 'an address two VIPs\' names share is no one\'s')
                cfg['gslb_infer_alias'] = 'false'
                rows_ = dict(((x['fqdn'] or x['blue_vsvip']), x) for x in build_rows(
                    cfg, read(artefact(cfg, 'avi-export')), load_dns(disc), {}, {}, {}))
                expect('snat.example.com' not in rows_ and rows_['vsvip-snat']['action'] == 'NONAME', 'turned off')
            finally:
                ad.pop('noname.example.com', None)
                ad.pop('snat.example.com', None)
                cfg.pop('gslb_vip_alias', None)
                cfg.pop('gslb_infer_alias', None)
        check('a VIP no name points at is explained, name by name; gslb_vip_alias ties an address in front of it '
              '(a NAT) to it, and a name blue gives it alone that is served from elsewhere (an F5) makes that '
              'address its own, so its names get GSLB too', fronted_vip)

        def first_build_from_nothing():
            """What a second site runs next: no names file and no GSLB service yet. One
            commit finds the names, writes every object at both sites, then
            builds GSLB on the leader and sets the services live."""
            global CLIENT_FACTORY
            W2, d2_ = _world(), tempfile.mkdtemp(prefix='avi_migrate_first_')
            cfg2 = dict(cfg, avi_outdir=d2_, gslb_names=os.path.join(d2_, 'dns_records.csv'),
                        dns_servers=['192.0.2.54', '192.0.2.53'], gslb_template_service='')  # as a site with no template yet:
            saved_f, saved_ad = CLIENT_FACTORY, dict(ad)
            CLIENT_FACTORY = lambda c, role, site: W2['blue'] if role == 'source' else W2[site]
            _POOL.clear()
            ad.clear()
            ad.update(ad_then)  # the DCs as they were before any flip
            down.add('192.0.2.54')  # and one of them out of reach of this host
            try:
                rc, o = quiet(converge_cmd, cfg2, cv_args(commit=True))
            finally:
                CLIENT_FACTORY = saved_f
                _POOL.clear()
                ad.clear()
                ad.update(saved_ad)
                down.discard('192.0.2.54')
            try:
                expect('names      discovered from blue\'s configuration, confirmed with 192.0.2.53' in o
                       and '192.0.2.54 did not answer from this host' in o, o[:3000])
                expect(names_discovered(cfg2['gslb_names']), 'the names file is written, and marked as discovered')
                svcs = dict((x['name'], x) for x in W2['site_a'].db.get('gslbservice', {}).values())
                expect('portal-443' in svcs and 'portal.gslb.example.com' in svcs['portal-443']['domain_names'],
                       ('GSLB built in the same run, after the objects', sorted(svcs)))
                expect([g['priority'] for g in svcs['portal-443']['groups']] == [20, 10], svcs['portal-443']['groups'])
                s_ = svcs['portal-443']
                hm = [x for x in W2['site_a'].db['healthmonitor'].values() if x['name'] == 'gslb-tcp-443'][0]
                expect(s_['down_response'] == {'type': 'GSLB_SERVICE_DOWN_RESPONSE_ALL_RECORDS'}
                       and s_['controller_health_status_enabled'] is True
                       and [uuid_of(x) for x in s_['health_monitor_refs']] == [hm['uuid']]
                       and s_['pool_algorithm'] == 'GSLB_SERVICE_ALGORITHM_PRIORITY'
                       and s_['site_persistence_enabled'] is False and s_['num_dns_ip'] == 1 and s_['ttl'] == 30
                       and all(g['algorithm'] == 'GSLB_ALGORITHM_ROUND_ROBIN' for g in s_['groups']),
                       ('best-practice settings from the config, none from a template', s_))
                expect(hm['monitor_port'] == 443 and hm['is_federated'] is True and hm['send_interval'] == 10
                       and hm['failed_checks'] == 3 and hm['successful_checks'] == 3, hm)
                expect('active/standby by priority (site_a 20, site_b 10; site_a active); TTL 30s' in o
                       and 'all records are returned' in o,
                       ('the settings, in words, in every plan', o[-4000:]))
                expect('WARN  the DNS service site_a-gslb-dns on site_a can run on one engine only' in o
                       and 'no GSLB change is possible until site_b is made leader' in o, o[-4000:])
                expect(not [c for c in W2['site_a'].calls if c['type'] == 'gslbservice' and c['method'] != 'GET'
                            and (c['body'] or {}).get('name') == 'canary'], 'the test service is never touched')
                gl = W2['site_a'].db['gslb']
                subs = [c['domain_name'] for g in gl.values() for c in g.get('dns_configs') or []]
                expect('gslb.myexample.com' in subs and 'gslb.exampleapp.com' in subs, subs)
                for site in ('site_a', 'site_b'):
                    v = W2[site].by_name('virtualservice', 'portal-443')
                    expect(v and v['enabled'] is True and v['traffic_enabled'] is True,
                           (site, 'live: no GSLB service existed, so a DC out of reach cannot hold it back'))
                expect('flip state unknown' not in o and 'STOPPED' not in o, o[-3000:])
            finally:
                import shutil
                shutil.rmtree(d2_, ignore_errors=True)
        check('a first build with no names file: one commit discovers the names (one DC out of reach), writes '
              'everything, then builds GSLB and sets the services live', first_build_from_nothing)

        def one_name_unanswered():
            rows_ = build_rows(cfg, read(artefact(cfg, 'avi-export')), load_dns(dns_csv), {}, {}, {})
            flaky.add(('192.0.2.53', 'portal.example.com'))  # the DC answers, but not about this name
            _DNS_ASKED.clear()
            try:
                check_flips(cfg, rows_)
            finally:
                flaky.clear()
            got = dict((r['fqdn'], r) for r in rows_)
            expect(got['portal.example.com']['flip_checked'] is False, 'an unanswered name is not taken as unflipped')
            expect(got['app.exampleapp.com']['flip_checked'] is True, 'the names it did answer are')
        check('a DC that answers but not about one name leaves that name\'s flip state unknown', one_name_unanswered)

        def gslb_settings_follow_config():
            cfg['gslb_down_response'] = 'empty'
            try:
                reset_calls()
                _, o = cv(commit=True)
                puts = [c for c in writes('site_a') if c['type'] == 'gslbservice' and c['method'] == 'PUT']
                names = sorted(c['body']['name'] for c in puts)
                expect(names and 'portal-443' not in names, ('every service but the flipped one follows', names))
                expect(all(c['body']['down_response']['type'] == 'GSLB_SERVICE_DOWN_RESPONSE_EMPTY' for c in puts))
                expect('DIFFERS    portal-443' in o and 'down_response kept as the leader has them' in o, o[-3000:])
                reset_calls()
                cv(commit=True)
                expect(not [c for c in writes('site_a') if c['type'] == 'gslbservice'], 'and then nothing')
                hm = W['site_a'].by_name('healthmonitor', 'gslb-tcp-443')
                hm['monitor_port'] = 8443  # someone changed it by hand
                try:
                    _, o = cv()
                    expect('is not a federated TCP monitor to port 443' in o, ('a misfit is not used', o[-3000:]))
                finally:
                    hm['monitor_port'] = 443
            finally:
                cfg.pop('gslb_down_response')
                cv(commit=True)
        check('a GSLB setting changed in the config reaches every service but a flipped one, and a monitor that is '
              'not what its name says is not used', gslb_settings_follow_config)

        def datacenter_toggle():
            """gslb_active_site: site_b moves every GSLB service to site_b (a flipped one too, priorities only),
            status judges READY by site_b, and site_a moves them back; each way once, then nothing."""
            cfg['gslb_active_site'] = 'site_b'
            try:
                _, o = cv()
                expect('site_a 10, site_b 20; site_b active (gslb_active_site)' in o and 'ACTIVE     portal-443' in o, o[-3000:])
                expect('UPDATE     sni-parent' in o, ('a service not flipped follows the config as a whole', o[-3000:]))
                reset_calls()
                cv(commit=True)
                svcs = [g_ for g_ in W['site_a'].db['gslbservice'].values() if g_['name'] in ('portal-443', 'sni-parent')]
                for g_ in svcs:
                    pr = dict((grp['name'].rsplit('-', 1)[-1], grp['priority']) for grp in g_['groups'])
                    expect(pr == {'site_a': 10, 'site_b': 20}, (g_['name'], pr))
                reset_calls()
                _, o = cv(commit=True)
                expect(not [c for c in writes('site_a') if c['type'] == 'gslbservice'], ('then nothing', o[-2000:]))
                f = flips()
                r = f['portal.example.com']
                expect(r['vip'] == r['vip_site_b'] and r['state'] == 'READY', ('READY by site_b', r))
            finally:
                cfg['gslb_active_site'] = 'site_a'
                cv(commit=True)
                cfg.pop('gslb_active_site')
            pr = dict((grp['name'].rsplit('-', 1)[-1], grp['priority'])
                      for grp in W['site_a'].by_name('gslbservice', 'portal-443')['groups'])
            expect(pr == {'site_a': 20, 'site_b': 10}, ('and back', pr))
            try:
                cfg['gslb_active_site'] = 'd3'
                expect(isinstance(cv_raises(), ValueError), 'a site that is not in avi_sites')
            finally:
                cfg.pop('gslb_active_site')
        check('gslb_active_site toggles every GSLB service between the datacenters (a flipped one by its '
              'priorities only), and status judges READY by the active site', datacenter_toggle)

        def allow_listed_member():
            """A service that admits listed clients only (D1pAI-AllowList-NSP) refuses the DNS engines'
            checks: its GSLB health comes from the site controllers, and goes back when the policy does."""
            svc0 = [g_ for g_ in W['site_a'].db['gslbservice'].values() if g_.get('health_monitor_refs')
                    and g_['name'] in ('sni-parent', 'legacy-app', 'waf-app', 'snat-app')][0]  # made here, not flipped
            member = [v for v in W['site_a'].db['virtualservice'].values()
                      if v['uuid'] == svc0['groups'][0]['members'][0]['vs_uuid']][0]
            nsp = W['site_a'].put('networksecuritypolicy', {'name': 'AllowList-NSP', 'rules': [
                {'index': 0, 'name': 'allow-k8s', 'action': 'NETWORK_SECURITY_POLICY_ACTION_TYPE_ALLOW', 'enable': True,
                 'match': {'client_ip': {'match_criteria': 'IS_IN', 'prefixes': [prefix('10.1.88.0/24')]}}},
                {'index': 5, 'name': 'deny-all', 'action': 'NETWORK_SECURITY_POLICY_ACTION_TYPE_DENY', 'enable': True,
                 'match': {'client_ip': {'match_criteria': 'IS_IN', 'prefixes': [prefix('0.0.0.0/0')]}}}]})
            member['network_security_policy_ref'] = nsp['url']
            try:
                _, o = cv()
                expect('health from the site controllers only: AllowList-NSP admits listed clients only' in o
                       and ('UPDATE     %s' % svc0['name']) in o, o[-3000:])
                cv(commit=True)
                expect(W['site_a'].by_name('gslbservice', svc0['name']).get('health_monitor_refs') == [], 'no monitor')
                reset_calls()
                cv(commit=True)
                expect(not [c for c in writes('site_a') if c['type'] == 'gslbservice'], 'and then nothing')
            finally:
                member.pop('network_security_policy_ref', None)
                cv(commit=True)
            expect(W['site_a'].by_name('gslbservice', svc0['name']).get('health_monitor_refs'), 'the monitor is back')
            expect(not admits_listed_only({'rules': [{'action': 'NETWORK_SECURITY_POLICY_ACTION_TYPE_RATE_LIMIT',
                                                      'match': {'client_ip': {'prefixes': [prefix('0.0.0.0/0')]}}}]}))
        check('a GSLB member that admits listed clients only is watched through its site controllers, not the DNS '
              'engines\' checks it would refuse', allow_listed_member)

        def fail_open_not_ready():
            cfg['gslb_down_response'] = 'all_records'
            downs = [W[s].by_name('virtualservice', 'sni-parent') for s in ('site_a', 'site_b')]
            try:
                cv(commit=True)
                for v in downs:
                    v['enabled'] = False  # every member down: GSLB answers all of them anyway
                _, o = quiet(status_cmd, cfg, ns(export=None, names=None))
                f = flips()['app.exampleapp.com']
                expect(f['state'] == 'NOT READY' and 'answers every site' in f['note'], f)
            finally:
                for v in downs:
                    v['enabled'] = True
                cfg.pop('gslb_down_response')
                cv(commit=True)
            f = flips()['app.exampleapp.com']
            expect(f['state'] == 'READY', ('and READY again once a member is up', f))
        check('a GSLB answer that is every site at once (all members down, answered anyway) is never READY',
              fail_open_not_ready)

        def unknown_needs_a_gslb_name():
            b_ = read(artefact(cfg, 'avi-export'))

            def unanswered(services):
                rows_ = build_rows(cfg, b_, load_dns(dns_csv), services, {}, {})
                for r in rows_:
                    r['flip_checked'] = False  # no DNS server answered
                return owned_by_green(cfg, b_, rows_)
            expect(not unanswered({}), 'no GSLB service answers for any name yet, so none can be flipped')
            own = unanswered({'portal-443': {'name': 'portal-443', 'domain_names': ['portal.gslb.example.com']}})
            expect('portal-443' in own and 'flip state unknown' in ' '.join(own['portal-443']), own)
            expect('sni-parent' not in own, 'no service answers for its GSLB name')
        check('an application whose flip state cannot be read counts as flipped only once a GSLB service answers '
              'for its name, so a first build with a DC unreachable still sets services live',
              unknown_needs_a_gslb_name)
    except Exception as exc:  # a step between checks failed; report it, do not crash
        failed.append('aborted: %s' % exc)
        print('  FAIL  aborted: %s: %s' % (exc.__class__.__name__, str(exc)[:500]))
    finally:
        CLIENT_FACTORY, dns_query = saved
        _POOL.clear()
        if os.environ.get('AVI_SELFTEST_KEEP'):
            print('  (kept %s)' % d)
        else:
            import shutil
            shutil.rmtree(d, ignore_errors=True)

    print('\ndns')

    def dns_wire():
        name = 'app.gslb.example.com'
        q = b''.join(bytes([len(x)]) + x.encode() for x in name.split('.')) + b'\x00'
        cname_rdata = b'\x03www\xc0\x0c'  # www.<question name>, compressed
        pkt = struct.pack('>HHHHHH', 0x1234, 0x8180, 1, 2, 0, 0) + q + struct.pack('>HH', 1, 1)
        pkt += b'\xc0\x0c' + struct.pack('>HHIH', 5, 1, 30, len(cname_rdata)) + cname_rdata
        pkt += b'\xc0\x0c' + struct.pack('>HHIH', 1, 1, 30, 4) + socket.inet_aton('10.1.100.23')
        out = parse_dns(pkt, 0x1234)
        expect(out['a'] == ['10.1.100.23'] and out['cname'] == ['www.app.gslb.example.com'], out)
        expect(out['aa'] is False and out['ttl'] == 30, out)
        expect(parse_dns(pkt, 0x9999).get('error'))

        def enc(n):
            return b''.join(bytes([len(x)]) + x.encode() for x in n.split('.')) + b'\x00'
        soa = enc('ns1.example.com') + enc('hostmaster.example.com') + struct.pack('>IIIII', 1, 2, 3, 4, 5)
        pkt2 = struct.pack('>HHHHHH', 0x2222, 0x8580, 1, 1, 0, 0) + enc('example.com') + struct.pack('>HH', 6, 1)
        pkt2 += b'\xc0\x0c' + struct.pack('>HHIH', 6, 1, 3600, len(soa)) + soa
        out2 = parse_dns(pkt2, 0x2222)
        expect(out2['soa'] == ['example.com'] and out2['aa'] is True, ('an SOA answer names its zone', out2))
        target = enc('portal.example.com')
        pkt3 = struct.pack('>HHHHHH', 0x3333, 0x8580, 1, 1, 0, 0) + enc('45.92.1.10.in-addr.arpa')
        pkt3 += struct.pack('>HH', 12, 1) + b'\xc0\x0c' + struct.pack('>HHIH', 12, 1, 3600, len(target)) + target
        expect(parse_dns(pkt3, 0x3333)['ptr'] == ['portal.example.com'], 'a reverse record')
        expect(reverse_name('10.1.92.45') == '45.92.1.10.in-addr.arpa')

        srv = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        srv.bind(('127.0.0.1', 0))
        port = srv.getsockname()[1]
        import threading

        def answer():
            data, addr = srv.recvfrom(512)
            tid = data[:2]
            srv.sendto(tid + pkt[2:], addr)
        t = threading.Thread(target=answer)
        t.start()
        got = dns_query('127.0.0.1', name, timeout=2, port=port)
        t.join()
        srv.close()
        expect(got.get('a') == ['10.1.100.23'], got)
    check('DNS client: compression, CNAME and A, and a real UDP round trip', dns_wire)

    print('\nblue')

    def blue_read_only():
        c = Client.__new__(Client)  # no login: the refusal comes before any network
        c.role, c.label, c.host = 'source', 'source', 'https://blue.invalid'
        for method in ('POST', 'PUT', 'PATCH', 'DELETE'):
            try:
                c.request(method, '/api/pool/pool-1', {'name': 'x'})
            except RuntimeError as exc:
                expect('blue is only ever read' in str(exc), exc)
            else:
                expect(False, '%s to blue went through' % method)
    check('the client refuses every write to blue, whatever asks for it', blue_read_only)

    print('\ntls')

    def first_use():
        fp = 'AB:CD:' + 'EF:' * 29 + '01'
        saved_env, saved_in = os.environ.get('AVI_TRUST_SHA256'), sys.stdin
        try:
            with contextlib.redirect_stdout(io.StringIO()):
                sys.stdin = io.StringIO('yes\n')  # not a terminal, so nobody can vouch at a prompt
                os.environ.pop('AVI_TRUST_SHA256', None)
                expect(vouched_for('h', fp) is False, 'no terminal and nothing listed: not pinned')
                os.environ['AVI_TRUST_SHA256'] = 'ff:ff, ' + fp.replace(':', '').lower()
                expect(vouched_for('h', fp) is True, 'listed in AVI_TRUST_SHA256, any case, colons or not')
                os.environ['AVI_TRUST_SHA256'] = 'ff:ff'
                expect(vouched_for('h', fp) is False, 'a different fingerprint is not vouched for')
        finally:
            sys.stdin = saved_in
            if saved_env is None:
                os.environ.pop('AVI_TRUST_SHA256', None)
            else:
                os.environ['AVI_TRUST_SHA256'] = saved_env
    check('a certificate seen for the first time is pinned only when the operator vouches for it', first_use)

    print('\n%d passed, %d failed' % (len(passed), len(failed)))
    return not failed


# ---------------------------------------------------------------- cli

def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--example-config', action='store_true', help='print the commented keys and exit')
    p.add_argument('--version', action='version', version='avi_migrate %s' % VERSION)
    sub = p.add_subparsers(dest='command')
    cv = sub.add_parser('converge', help='make every green site and GSLB match blue and the config')
    st = sub.add_parser('status', help='read-only: the state of every name, and a fresh flip list')
    e = sub.add_parser('export', help='read blue only (read-only)')
    pg = sub.add_parser('purge', help='delete what converge made on green (never anything else, never a flipped '
                                      'application), so the next converge builds it again')
    dc = sub.add_parser('discover', help='read-only: the DNS names of blue\'s services, from blue\'s configuration '
                                         'and dns_servers, written as gslb_names (no DC export needed)')
    sub.add_parser('selftest', help='offline checks; no controller or credentials')
    for s_ in (cv, st, e, pg, dc):
        s_.add_argument('--config', required=True, help='the environment file, env.<customer>.yaml')
    e.add_argument('--out', help='override the export path')
    dc.add_argument('--export', help='use this saved export of blue instead of reading blue now')
    dc.add_argument('--out', help='write here instead of gslb_names')
    cv.add_argument('--commit', action='store_true', help='write; without it nothing is written')
    cv.add_argument('--site', help='one site only; GSLB is left for a run without --site')
    cv.add_argument('--vs', help='only these virtual services and what they use (comma list, globs)')
    cv.add_argument('--journal', help='journal file (default: a new one in avi_outdir on --commit)')
    cv.add_argument('--force', action='store_true',
                    help='set services live even where an SE group cannot place them all')
    cv.add_argument('--allow-offline', action='store_true',
                    help='let live state take a live service out of service (never a flipped one)')
    cv.add_argument('--live-flipped', action='store_true',
                    help='let live state bring up services of flipped applications (never take one down)')
    cv.add_argument('--rewrite-gslb', action='store_true',
                    help='rewrite members, priorities and TTL of GSLB services whose names are flipped')
    cv.add_argument('--trust-export', action='store_true',
                    help='take the DNS export as the flip state for names no DNS server answers for')
    cv.add_argument('--verbose', action='store_true', help='list every object, not only the changes')
    cv.add_argument('--adopt', action='store_true',
                    help='hand same-named objects already on green to this tool, so it converges them too')
    pg.add_argument('--commit', action='store_true', help='delete; without it nothing is deleted')
    pg.add_argument('--site', help='one site only; GSLB services are left for a purge without --site')
    pg.add_argument('--journal', help='journal file (default: a new one in avi_outdir on --commit)')
    for s_ in (cv, st, pg):
        s_.add_argument('--export', help='use this saved export of blue instead of reading blue now'
                        if s_ is cv else 'the export of blue to use (default: the last one written)')
        s_.add_argument('--names', help='the DNS export (default: gslb_names in the config)')
    args = p.parse_args(argv)
    if args.example_config:
        print(EXAMPLE_CONFIG, end='')
        return 0
    if not args.command:
        p.error('a command is required (or --example-config)')
    if args.command == 'selftest':
        return 0 if selftest({}, args) else 1
    cfg = read_config(args.config)
    handler = {'converge': converge_cmd, 'status': status_cmd, 'export': export, 'purge': purge_cmd,
               'discover': discover_cmd}[args.command]
    rc = handler(cfg, args)
    if rc is True or rc is None:
        return 0
    if rc is False:
        return 1
    return int(rc)


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (Exception, KeyboardInterrupt) as exc:
        print('STOPPED: %s. If a write was in progress, read the journal and the target before '
              'running it again.' % exc, file=sys.stderr)
        sys.exit(1)
