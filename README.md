# Avi, blue to green

Converge virtual services from a source controller onto each new site's own cloud, VRF, SE group, and VIP network. GSLB is part of the same run. Nothing is written back to the source.

License: GPL-3.0. Built and proved out for [essential.coach](https://essential.coach).
Full write-up: [Moving Avi from Blue to Green Without Ever Writing Back to Blue](https://essential.coach/avi-blue-to-green-without-writing-back/)

The sample environment calls the sites `site_a` and `site_b`. Rename those keys to yours. The example hosts are `example.com`. They are not a design.

## Run

```bash
python3 avi_migrate.py --help
```

Converge is a dry run unless you pass `--commit`. A second run after a commit reports unchanged. After one of an application's DNS names is flipped, that application is frozen: the next converge will not update it from the source, rearrange its GSLB members, or take it offline.

Converge never deletes. Private keys are posted to the target in the same pass and are not written to disk.

There is an offline self-test that needs no credentials. Run that before the first converge against a controller.
