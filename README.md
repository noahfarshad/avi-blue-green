# Avi, blue to green

Converge virtual services from a source controller onto each new site's own cloud, VRF, SE group, and VIP network. GSLB is part of the same run. Nothing is written back to the source, and nothing is written to DNS.

License: GPL-3.0. Built and proved out for [essential.coach](https://essential.coach).
Full write-up: [Moving Avi from Blue to Green Without Ever Writing Back to Blue](https://essential.coach/avi-blue-to-green-without-writing-back/). The GSLB build order is [Avi GSLB Across Two Sites](https://essential.coach/avi-gslb-across-two-vcf-sites/), and the controllers, the licensing and the supported design under NSX Federation are in [Avi 32.1.3 Under NSX Federation](https://essential.coach/avi-under-nsx-federation-local-objects-only/).

The sample environment calls the sites `site_a` and `site_b`. Rename those keys to yours. The example hosts are `example.com`. They are not a design.

## Run

```bash
python3 avi_migrate.py selftest                              # offline, no credentials
python3 avi_migrate.py --example-config > env.yaml           # the keys, commented
python3 avi_migrate.py export   --config env.yaml            # read blue only
python3 avi_migrate.py discover --config env.yaml            # read-only: DNS names from blue and the domain controllers
python3 avi_migrate.py converge --config env.yaml            # dry run: every object and its state
python3 avi_migrate.py converge --config env.yaml --commit
python3 avi_migrate.py status   --config env.yaml            # read-only: readiness and a fresh flip list
python3 avi_migrate.py purge    --config env.yaml            # dry run: what purge would delete
```

Converge is a dry run unless you pass `--commit`. Every object is reported as ADD, UPDATE, UNCHANGED, FROZEN, KEPT, MAPPED or BLOCKED, and a second run after a commit reports UNCHANGED. Exit codes: 0 nothing to do, 2 changes pending, 1 blocked.

Blue is the source of truth for an application until one of its DNS names is flipped. After that it is FROZEN: the next converge will not update it from the source, rearrange its GSLB members, or take it offline. Flip state is read live from the domain controllers.

Converge never deletes. Purge deletes only what converge made, never an object that was on green before and never one a flipped application uses. A live service is taken out of service only with `--allow-offline`. SE groups are raised, never lowered, and a migrated service never lands in the Supervisor's `Default-Group` unless the config says so.

Nothing is written to blue: the client refuses it, and a target that turns out to be blue's cluster stops the run. Controller passwords come from the environment or a prompt. Private keys are read from blue at write time and posted straight to green; they are never written to disk or a journal. Values blue masks are asked for once and kept in memory. Each controller's certificate fingerprint is pinned only after you confirm it, and a changed certificate stops the run before the password is sent.

Objects are posted with blue's API version, so the target converts renamed fields itself. The fields the newer release refuses are removed, from a table built by diffing the two releases' object models.

The DNS cutover is a separate PowerShell script that runs on a domain controller and flips one name at a time. It is not in this repository.

## Tests

`python3 avi_migrate.py selftest` exercises every command offline against in-memory blue and green controllers and stand-in DNS. It needs no controller and no credentials. Run it before the first converge against a controller.

Python 3.9 or later and `requests`. PyYAML is optional.
