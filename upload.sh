#!/bin/sh
set -euxo pipefail
TOP=$(readlink -f $(dirname $0))

tmp=$(mktemp -d $TOP/dist.XXXXXX)

git push origin hakyll # Ensure we are up to date

nix run . -- rebuild
cp .gitignore _site/
commit=$(git rev-parse HEAD)
git fetch origin master
git branch --force master origin/master
git clone . --branch master tmp
trap 'rm -rf "tmp"' EXIT

cp -a _site/. tmp
git -C tmp add --all
git -C tmp commit -m "[$(date '+%F %T %Z')] New release in response to commit ${commit}" || true
git -C tmp push origin master:master
if [ x"$1" = "x--publish" ]; then
  git push origin master:master
fi
