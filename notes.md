# Package management

## Nix vs RPM vs .buildinfo
Dependency specifications in RPM do not guarantee that the listed dependencies are the only ones needed. A particular dependency could exist on a package developer's machine but not the specification, leading to a working build on that machine but not other ones.

RPM specifications are not explicit on the versions used to build a particular package. Instead, they only specify, for example, a minimum version. This might not always work if versions are not backward compatible.

Are .buildinfo dependency version numbers fixed?

## GUIX
Based on Nix.
Can be extended with code written in Guile (Scheme).





# P2P

## Safe
aka MaidSafe

based on **Sigmoid** Distributed network storage

