#!/bin/sh
set -eu
cd "$(dirname -- "$0")"
case "$#:${1-}" in
    0:|1:--kernel) ;;
    *) echo "Usage: $0 [--kernel]" >&2; exit 2 ;;
esac
build_dir=$(mktemp -d)
trap 'rm -rf -- "$build_dir"' EXIT
export LEAN_PATH="$build_dir"
toolchain=$(cat lean-toolchain)
modules="Skolem Frontier FrontierTerms Gaussian NoZero Survey13 Audit"
elan run "$toolchain" lean --version
for module in $modules
do
    echo "Checking $module.lean"
    elan run "$toolchain" lean -j 1 -M 640 -T 24000 -DwarningAsError=true -o "$build_dir/$module.olean" "$module.lean"
done
if [ "${1-}" = "--kernel" ]; then
    for module in $modules
    do
        elan run "$toolchain" leanchecker --verbose "$module"
    done
fi
