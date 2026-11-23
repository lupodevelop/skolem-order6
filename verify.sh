#!/bin/sh
set -eu
cd "$(dirname -- "$0")"
build_dir=$(mktemp -d)
trap 'rm -rf -- "$build_dir"' EXIT
export LEAN_PATH="$build_dir"
toolchain=$(cat lean-toolchain)
for module in Skolem Frontier FrontierTerms Gaussian NoZero Audit
do
    elan run "$toolchain" lean -M 640 -T 24000 -DwarningAsError=true -o "$build_dir/$module.olean" "$module.lean"
done
