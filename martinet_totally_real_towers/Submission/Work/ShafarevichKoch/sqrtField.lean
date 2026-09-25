import Mathlib
import Submission.Work.ShafarevichKoch.SupportedTower
import Submission.Work.ShafarevichKoch.isGalois_sup_kSupported_adjoin_sqrt
import Submission.Work.ClassFieldTower.All

/-!
# `Work.ShafarevichKoch.sqrtField` -- the Kummer field `K_∅(√x)` of the `κ`-route

README §32.1: for `x ∈ Kc`, the extension `K_∅(√x)/Kc` is Galois (`k_∅ = kSupported Kc 2 ∅` inside
`AlgebraicClosure Kc`), so `x` defines an extension of `G_∅ = Gal(K_∅/Kc)` by `𝔽₂`, hence a class in
`H²_cont(G_∅,𝔽₂)`.  The map `κ : V_∅/Kc^{×2} → H²_cont(G_∅,𝔽₂)` this produces is the classical
"Kummer radical" map of Koch's theorem; this module *names* its domain-side object and records its
two elementary properties.

## Main declarations

* `Work.ShafarevichKoch.sqrtField x` -- the compositum `k_∅ ⊔ Kc⟮√x⟯`;
* `kSupported_le_sqrtField` -- `k_∅ ≤ K_∅(√x)`;
* `isGalois_sqrtField` -- `K_∅(√x)/Kc` is Galois.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace Work.ShafarevichKoch

open Work.ClassFieldTower

/-- **The Kummer field `K_∅(√x)`**: the compositum of the maximal unramified pro-`2` extension of
`Kc` (the explicit tower `k_∅ = kSupported Kc 2 ∅` inside `AlgebraicClosure Kc`) with the adjoin of
the square roots of `x`. -/
abbrev sqrtField (x : Kc) : IntermediateField Kc (AlgebraicClosure Kc) :=
  kSupported Kc 2 (∅ : Finset ℕ) ⊔
    IntermediateField.adjoin Kc
      {y : AlgebraicClosure Kc | y ^ 2 = algebraMap Kc (AlgebraicClosure Kc) x}

/-- The maximal unramified pro-`2` extension sits inside `K_∅(√x)`. -/
theorem kSupported_le_sqrtField (x : Kc) : kSupported Kc 2 (∅ : Finset ℕ) ≤ sqrtField x :=
  le_sup_left

/-- **`K_∅(√x)/Kc` is Galois** (the first runway piece of the `κ`-route, README §32.1). -/
theorem isGalois_sqrtField (x : Kc) : IsGalois Kc ↥(sqrtField x) := by
  have h := isGalois_sup_kSupported_adjoin_sqrt x
  simpa [sqrtField] using h

end Work.ShafarevichKoch
