import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.auxpolydefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Complex

/-- Coercion of an integer power from an `IntermediateField` to the ambient field. -/
lemma IntermediateField.coe_intCast_zpow {K L : Type*} [Field K] [Field L] [Algebra K L]
    (S : IntermediateField K L) (x : S) (m : ℤ) : ((x ^ m : S) : L) = (x : L) ^ m := by
  rw [← Subfield.subtype_apply (s := S.toSubfield) (x := x ^ m),
      ← Subfield.subtype_apply (s := S.toSubfield) (x := x)]
  exact map_zpow₀ (S.toSubfield.subtype) x m

theorem Qval_eq_sum {K : Type*} [Field K] [NumberField K] {n r : ℕ} (φ : K →+* ℂ)
    (α : Fin n → K) (b : Fin n → ℤ) (k : Fin n) (L : Fin r → Fin n → ℤ)
    (ι : Fin (r - 1) → Fin n) (α' : Fin r → K) (h D0 : ℕ) (Dj : Fin r → ℕ)
    (p : AuxIdx r h D0 Dj → K) (t0 : ℕ) (t : Fin (r - 1) → ℕ) (s : ℤ) :
    Qval φ b k L ι α' h D0 Dj p t0 t s
      = ∑ lm, φ (p lm) * φ (((coefF b k L ι α' h D0 Dj t0 t s lm : auxField α') : K)) := by
  rw [Qval]
  apply Finset.sum_congr rfl
  intro lm _
  rw [coefF]
  simp only [IntermediateField.coe_mul, IntermediateField.coe_prod,
    IntermediateField.coe_intCast_zpow, SubfieldClass.coe_ratCast, map_mul, map_prod,
    map_zpow₀, alphaF_coe]
  rw [map_ratCast, coefRat]
  push_cast
  simp only [← Delta_eq_deltaRat, ← Theta_eq_thetaRat, gamInt_cast]
  push_cast
  ring

end Work.BW
