#!/usr/bin/env bash
# Build doc-gen4 API documentation for the Statlib Lean library.
set -euo pipefail
set -x

ROOT_DIR="$(cd "$(dirname "$0")" && pwd)"
WEBSITE_DIR="${WEBSITE_DIR:-"$ROOT_DIR/../stat-lib.github.io"}"

cd "$ROOT_DIR"

if [[ ! -d "$WEBSITE_DIR" ]]; then
  echo "Website directory not found: $WEBSITE_DIR" >&2
  exit 1
fi

clean=false
if [[ "${1:-}" == "--clean" ]]; then
  clean=true
fi

lake build Statlib

cd docbuild
mkdir -p docs
: > docs/references.bib
lake update Statlib

if [[ "$clean" == true ]]; then
  rm -f .lake/build/api-docs.db .lake/build/api-docs.db-shm .lake/build/api-docs.db-wal
  rm -rf .lake/build/doc .lake/build/doc-data .lake/build/doc-manifest.json
fi

lake build Statlib:docs

cd ..
rm -rf "$WEBSITE_DIR/docs"
mkdir -p "$WEBSITE_DIR/docs"
cp -r docbuild/.lake/build/doc/* "$WEBSITE_DIR/docs/"

echo
echo "API docs built. Open $WEBSITE_DIR/docs/index.html via the local static server."
