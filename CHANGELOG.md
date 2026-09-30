# Changelog

All notable changes to this project are documented here.

## [1.0.0] — 2026-09-30

### Added

- Initial public release. Converge virtual services from a source Avi controller onto each new site's own cloud, VRF, SE group, and VIP network. Dry run unless --commit. Nothing is written back to the source. Site keys in the sample are site_a and site_b.

### Notes

- All customer-specific identifiers have been replaced with generic example values.
- Configuration files use placeholder credentials (ChangeMe!) that must be replaced with your own before use.
- Hostnames follow the *.example.com pattern and IP addresses use the RFC 5737 documentation range (192.0.2.0/24).
