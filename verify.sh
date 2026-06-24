#!/usr/bin/env bash
# Independently verify the solution with leanprover/comparator.
#
# Trust required: the Lean kernel, Mathlib, Challenge.lean (the statement),
# and comparator itself.  The proof in the KrafftSieve library does
# NOT need to be trusted — comparator checks it independently.
set -euo pipefail

TOOLCHAIN_TAG=$(sed -e 's/^leanprover\/lean4://' lean-toolchain | tr -d '[:space:]')
WORK="${COMPARATOR_WORK:-$HOME/.cache/krafftsieve-comparator}"
mkdir -p "$WORK"

if [ ! -d "$WORK/comparator" ]; then
  git clone --branch "$TOOLCHAIN_TAG" --depth 1 \
    https://github.com/leanprover/comparator "$WORK/comparator"
fi
if [ ! -d "$WORK/lean4export" ]; then
  git clone --branch "$TOOLCHAIN_TAG" --depth 1 \
    https://github.com/leanprover/lean4export "$WORK/lean4export"
fi
(cd "$WORK/comparator" && lake build)
(cd "$WORK/lean4export" && lake build)

# landrun, wrapped to grant the dynamic loader paths that its -ldd
# resolution can miss (the ELF interpreter on Ubuntu; the Nix store on
# NixOS).  Without execute permission on the interpreter, every execve
# inside the sandbox fails with EACCES.
if [ ! -x "$WORK/landrun-bin" ]; then
  curl -sL -o "$WORK/landrun-bin" \
    https://github.com/Zouuup/landrun/releases/download/v0.1.14/landrun-linux-amd64
  chmod +x "$WORK/landrun-bin"
fi
EXTRA=""
for d in /lib64 /lib /usr/lib /nix/store; do
  [ -e "$d" ] && EXTRA="$EXTRA --rox $d"
done
printf '#!/usr/bin/env bash\nexec "%s/landrun-bin"%s "$@"\n' "$WORK" "$EXTRA" \
  > "$WORK/landrun"
chmod +x "$WORK/landrun"
export COMPARATOR_LANDRUN="$WORK/landrun"
export PATH="$WORK:$PATH"

export PATH="$WORK/lean4export/.lake/build/bin:$PATH"

lake exe cache get
lake env "$WORK/comparator/.lake/build/bin/comparator" comparator_config.json
