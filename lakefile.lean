import Lake
open Lake DSL

package «formalising-mathematics-2024» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require aesop from git "https://github.com/JLimperg/aesop" @ "v0.4.0"

@[default_target]
lean_lib «FormalisingMathematics2024» {
  -- add any library configuration options here
}
