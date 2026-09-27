import Mathlib
import Submission.Work.Mostow.ftbDefs
import Submission.Work.Mostow.ellipticAux
import Submission.Work.Mostow.fix_zero_is_euclidean

/-!
# Auxiliary vocabulary for `Work.Mostow.rotCanonEqRotN`

* `rcPOActionProp`, `rcHypIsometryProp` : the two hypothesis `Prop`s hold in every dimension;
* `rcBoost p` : the boost `0 ↦ p` as an element of `PO n 1`;
* `rcLin g hg` : the linear isometry of the chart by which an element `g` fixing `0` acts.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-- `POActionProp n` holds unconditionally. -/
theorem rcPOActionProp (n : ℕ) : POActionProp n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; exact poAction_hypIso_zero.1
  · exact poAction_ge1 n h

/-- `HypIsometryProp n` holds unconditionally. -/
theorem rcHypIsometryProp (n : ℕ) : HypIsometryProp n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; exact poAction_hypIso_zero.2
  · exact hypIsometry_ge1 n h (poAction_ge1 n h)

/-- The hyperbolic boost carrying the base point `0` to `p`, as an element of `PO n 1`. -/
def rcBoost {n : ℕ} (p : E n) : PO n 1 := ((boost p : O1 n) : PO n 1)

lemma rcBoost_smul_zero {n : ℕ} (p : E n) : rcBoost p • (0 : E n) = p :=
  boost_smul_zero (rcPOActionProp n) p

/-- The linear isometry of the chart by which an element fixing the base point `0` acts. -/
def rcLin {N : ℕ} (g : PO N 1) (hg : g • (0 : E N) = 0) : E N ≃ₗᵢ[ℝ] E N :=
  Classical.choose (fix_zero_is_euclidean N (rcPOActionProp N) (rcHypIsometryProp N) g hg)

lemma rcLin_apply {N : ℕ} (g : PO N 1) (hg : g • (0 : E N) = 0) (u : E N) :
    g • u = rcLin g hg u :=
  Classical.choose_spec (fix_zero_is_euclidean N (rcPOActionProp N) (rcHypIsometryProp N) g hg) u

/-- `rcLin` does not depend on the proof that `g` fixes `0`. -/
lemma rcLin_ext {N : ℕ} (g : PO N 1) (h₁ h₂ : g • (0 : E N) = 0) :
    rcLin g h₁ = rcLin g h₂ := by
  refine LinearIsometryEquiv.ext (fun u => ?_)
  exact (rcLin_apply g h₁ u).symm.trans (rcLin_apply g h₂ u)

lemma rcLin_one {N : ℕ} (h₁ : (1 : PO N 1) • (0 : E N) = 0) :
    rcLin (1 : PO N 1) h₁ = 1 := by
  refine LinearIsometryEquiv.ext (fun u => ?_)
  show rcLin (1 : PO N 1) h₁ u = u
  rw [← rcLin_apply (1 : PO N 1) h₁ u]
  exact (POBasic.ofProp (rcPOActionProp N)).one_smul u

lemma rcLin_congr {N : ℕ} {g g' : PO N 1} (h : g = g') (hg : g • (0 : E N) = 0)
    (hg' : g' • (0 : E N) = 0) : rcLin g hg = rcLin g' hg' := by
  cases h
  exact rcLin_ext g hg hg'

lemma rcLin_mul {N : ℕ} (g h : PO N 1) (hg : g • (0 : E N) = 0) (hh : h • (0 : E N) = 0)
    (hgh : (g * h) • (0 : E N) = 0) :
    rcLin (g * h) hgh = rcLin g hg * rcLin h hh := by
  have hA := POBasic.ofProp (rcPOActionProp N)
  refine LinearIsometryEquiv.ext (fun u => ?_)
  have e1 : rcLin (g * h) hgh u = (g * h) • u := (rcLin_apply (g * h) hgh u).symm
  have e2 : rcLin h hh u = h • u := (rcLin_apply h hh u).symm
  have e3 : rcLin g hg (h • u) = g • (h • u) := (rcLin_apply g hg (h • u)).symm
  rw [LinearIsometryEquiv.coe_mul, Function.comp_apply, e1, hA.mul_smul g h u, e2, e3]

lemma rcLin_inv {N : ℕ} (g : PO N 1) (hg : g • (0 : E N) = 0) (hgi : g⁻¹ • (0 : E N) = 0) :
    rcLin g⁻¹ hgi = (rcLin g hg)⁻¹ := by
  have hA := POBasic.ofProp (rcPOActionProp N)
  have hone : (1 : PO N 1) • (0 : E N) = 0 := hA.one_smul 0
  have hgg : (g * g⁻¹) • (0 : E N) = 0 := by rw [mul_inv_cancel]; exact hone
  have hmul := rcLin_mul g g⁻¹ hg hgi hgg
  have h1 : rcLin (g * g⁻¹) hgg = 1 := by
    rw [rcLin_congr (mul_inv_cancel g) hgg hone, rcLin_one hone]
  rw [h1] at hmul
  exact eq_inv_of_mul_eq_one_right hmul.symm

end

end Work.Mostow
