# Replaying the final checks

On ordinary Linux with bubblewrap and user namespaces, run:

```sh
lake comparator --config comparator.json
bash scripts/replay-kernels.sh
```

The first command uses the pinned toolchain's comparator and its default Lean
kernel. The second uses a temporary copy of the same configuration, retaining
the theorem names and permitted axioms and additionally requiring acceptance
by the toolchain's NanoDa and con-ron kernels.

For the local run the dependencies and toolchain resided under `/workspace`.
The prefix `bash verification/host/run.sh` exposes the Linux filesystem layout
expected by Lake. The `offline-bwrap` helper creates an outer empty network
namespace so bubblewrap does not have to configure a network interface inside
the container. It preserves the build, export and kernel sandboxes. An ordinary
Linux checkout calls Lake directly.

These two host-specific scripts were adapted from the Sharp Variation Graphs
Lean project by the same project group; their isolation logic is unchanged.
