#!/usr/bin/env bash
set -euo pipefail

lake build Certificates.CertCheck

echo "Checking F4 small certificates..."
for f in projects/f4/certificates/t10/*.json \
         projects/f4/certificates/t12/*.json \
         projects/f4/certificates/t14/*.json
do
  echo "$f"
  lake exe cert_check "$f"
done

echo "Checking E6 small certificates..."
for f in projects/e6/certificates/t14/*.json \
         projects/e6/certificates/t16/*.json \
         projects/e6/certificates/t18/*.json \
         projects/e6/certificates/t20/*.json
do
  echo "$f"
  lake exe cert_check "$f"
done

echo "All selected certificates passed."
