#!/usr/bin/env bash
set -euo pipefail

lake build Certificates.CertCheck

for f in projects/f4/certificates/t16/*.json; do
  echo "$f"
  lake exe cert_check "$f"
done

for f in projects/e6/certificates/t22/*.json; do
  echo "$f"
  lake exe cert_check "$f"
done

echo "All certificates passed."
