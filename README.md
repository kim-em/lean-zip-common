# lean-zip-common

Shared utilities for [lean-zip](https://github.com/kim-em/lean-zip) and
[lean-zstd](https://github.com/kim-em/lean-zstd).

## Contents

- **ZipForStd/** — Lemmas about `Array`, `ByteArray`, `List`, and `Nat` that are
  missing from Lean's standard library. Candidates for upstreaming.
- **ZipCommon.Binary** — Little-endian and octal ASCII binary encoding/decoding.
- **ZipCommon.Handle** — File handle shims (seek, fileSize, symlink) via C FFI.
- **ZipCommon.Spec.BinaryCorrect** — Roundtrip correctness proofs for binary encoding.

## Usage

Add to your `lakefile.lean`:

```lean
require zipCommon from git
  "https://github.com/kim-em/lean-zip-common" @ "main"
```

In Lean source files, use the module system and import either library:

```lean
module

import ZipCommon
import ZipForStd
```

The root modules re-export their submodules. Binary and bit-reader definitions
are exposed so downstream proofs can unfold them; proof helpers remain private.

## Build

```
lake build
lake test
```

`lake test` checks the public API from separate modules, including definition
unfolding, theorem re-exports, and file-handle shim signatures.

## License

Apache-2.0
