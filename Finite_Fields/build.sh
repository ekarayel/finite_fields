#!/bin/bash
THIS=`realpath $(dirname "$0")`

isabelle build \
  -D $THIS \
  -o browser_info \
  -o document=pdf \
  -o document_variants="document:outline=/proof" \
  -o document_output="$THIS/output" \
  -v
