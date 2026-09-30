import Mathlib
import Submission.Work.HomologyMV.Data
import Submission.Work.HomologyMV.ker_toLin_iso_int_of_normalForm
import Submission.Work.HomologyMV.coker_toLin_iso_int_of_normalForm

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `HomologyMV/`: the two degree-`0`/`3` end certificates

The two ends of the Mayer–Vietoris computation of `H_*(M̂)`:

* in degree `3` the model map `φ₃ : ℤ⁵ → ℤ⁴` has kernel `ℤ`, which is why `H₄(M̂) ≅ ℤ`
  (`ker_phi3_iso_int`);
* in degree `0` the model map `φ₀ : ℤ⁵ → ℤ⁶` has cokernel `ℤ`, which is why `H₀(M̂) ≅ ℤ`
  (`coker_phi0_iso_int`; the alternative to deducing `H₀ ≅ ℤ` from connectedness of `M̂`).

Both are direct applications of the normal-form lemmas of
`ker_toLin_iso_int_of_normalForm.lean` / `coker_toLin_iso_int_of_normalForm.lean` to the
certificates of the generated `Data.lean`.
-/

namespace Work.HomologyMV

open CategoryTheory

noncomputable section

/-- `ker φ₃ ≅ ℤ`, from the unimodular normal form `P3Mat` (`φ₃ ∘ P3 = [1₄ | 0]`). -/
theorem ker_phi3_iso_int : Nonempty ((Matrix.toLin' phi3Mat).ker ≃ₗ[ℤ] ℤ) :=
  ker_toLin_iso_int_of_normalForm 4 phi3Mat P3Mat Q3Mat P3Mat_mul_Q3Mat Q3Mat_mul_P3Mat
    phi3Mat_mul_P3Mat

/-- `coker φ₀ ≅ ℤ`, from the unimodular normal form `U0Mat` (`U0 ∘ φ₀ = [1₅ ; 0]`). -/
theorem coker_phi0_iso_int :
    Nonempty (((Fin 6 → ℤ) ⧸ (Matrix.toLin' phi0Mat).range) ≃ₗ[ℤ] ℤ) :=
  coker_toLin_iso_int_of_normalForm 5 phi0Mat U0Mat V0Mat U0Mat_mul_V0Mat V0Mat_mul_U0Mat
    U0Mat_mul_phi0Mat

end

end Work.HomologyMV
