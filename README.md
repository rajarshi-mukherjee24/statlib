# Statlib

Lean formalization project for probability and statistics.

## Build

```bash
lake update mathlib
lake build Statlib
```

## Documentation

The generated website is published from the sibling `stat-lib.github.io`
repository. From this repo, run:

```bash
./build_api_docs.sh
./build_tutorial.sh
```

Both scripts write their generated HTML into `../stat-lib.github.io` by default.
Set `WEBSITE_DIR=/path/to/stat-lib.github.io` if your checkout lives elsewhere.
