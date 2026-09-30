import Mathlib
import Submission.Work.Pi6.EMM2.kOneFieldClean
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.EMM2

/-- The `𝕜`-cohomology of a range model of `K(ℤ,1)` through degree `M` is that of the circle:
`H⁰ = 𝕜`, `H¹ = 𝕜` and `H^q = 0` for `2 ≤ q ≤ M`.  Immediate from
`Work.Pi6.EMM2.kOneFieldLowTF`. -/
theorem kOneFibre {𝕜 : Type} [Field 𝕜] (Y : Type) [TopologicalSpace Y] (y₀ : Y) (M : ℕ)
    (hY : Work.Serre.IsEMSpaceUpTo ℤ 1 (by norm_num) M Y y₀) :
    Module.finrank 𝕜 (Work.Pi6.Coh 𝕜 Y 0) = 1 ∧
      Module.finrank 𝕜 (Work.Pi6.Coh 𝕜 Y 1) = 1 ∧
      (∀ q : ℕ, 2 ≤ q → q ≤ M → CategoryTheory.Limits.IsZero (Work.Pi6.Coh 𝕜 Y q)) :=
  kOneFieldLowTF Y y₀ M hY

end Work.Pi6.EMM2
