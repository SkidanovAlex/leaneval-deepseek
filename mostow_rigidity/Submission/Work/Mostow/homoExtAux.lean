import Mathlib
import Submission.Work.Mostow.visualDefs
import Submission.Work.Mostow.o1SignTime
import Submission.Work.Mostow.nullNormOne

/-!
# Elementary facts about `sMat`, `wvec_visualDefs`, `dfun`, `phiFun`

The raw representative matrix `sMat g = tsign (rep g) • mat (rep g)` of `g : PO n 1` is a
Minkowski isometry, `wvec_visualDefs g ξ = sMat g *ᵥ (ξ,1)` is the homogeneous lift of the boundary point,
`dfun g ξ` is its time coordinate, and `phiFun g ξ` is the resulting renormalised boundary point.

This module collects the few consequences used by the computation of the Jacobian of
`homoExt g`; it deliberately keeps the names `sMat_mink`/`wvec_mink` (they are imported by
`Submission.Work.Mostow.dfun_pos`).
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

/-- `sMat g` preserves the Minkowski form. -/
theorem sMat_mink (n : ℕ) (g : PO n 1) (x y : Fin n ⊕ Fin 1 → ℝ) :
    Hyper.mink ((sMat g).mulVec x) ((sMat g).mulVec y) = Hyper.mink x y := by
  simp only [sMat, Matrix.smul_mulVec]
  rw [Hyper.mink_smul, Hyper.mink_mulVec (mat (rep g)) (Hyper.mat_conj (rep g)),
    Hyper.tsign_mul_self, one_mul]

/-- Minkowski pairing of two `wvec_visualDefs`'s: `⟪(ξ,1),(η,1)⟫ = ⟪ξ,η⟫ - 1`. -/
theorem wvec_mink (n : ℕ) (g : PO n 1) (ξ η : E n) :
    Hyper.mink (wvec_visualDefs g ξ) (wvec_visualDefs g η) = inner ℝ ξ η - 1 := by
  simp only [wvec_visualDefs]
  rw [sMat_mink, Hyper.mink_apply]
  simp [hvec, Hyper.inner_eq_sum]

/-- On the sphere the time coordinate `dfun g ξ` of the lift `wvec_visualDefs g ξ` is strictly positive. -/
theorem dfunPosAux (n : ℕ) (g : PO n 1) (ξ : E n) (hξ : ξ ∈ Sph n) : 0 < dfun g ξ := by
  rw [dfun, wvec_visualDefs, sMat, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
  exact o1SignTime (rep g) ξ (le_of_eq (mem_sphere_zero_iff_norm.mp hξ))

/-- The explicit boundary formula maps the sphere to itself. -/
theorem phiFunUnitAux (n : ℕ) (g : PO n 1) (ξ : E n) (hξ : ξ ∈ Sph n) :
    ‖phiFun g ξ‖ = 1 := by
  have hz : phiFun g ξ = (WithLp.toLp 2 (fun i =>
      (wvec_visualDefs g ξ) (Sum.inl i) / (wvec_visualDefs g ξ) (Sum.inr 0)) : E n) := by
    simp only [phiFun, dfun]
  have hnull : (∑ i : Fin n, (wvec_visualDefs g ξ) (Sum.inl i) ^ 2) = ((wvec_visualDefs g ξ) (Sum.inr 0)) ^ 2 := by
    have hm := wvec_mink n g ξ ξ
    rw [Hyper.mink_apply, real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp hξ] at hm
    norm_num at hm
    simp only [pow_two]
    linarith [hm]
  have ht : (wvec_visualDefs g ξ) (Sum.inr 0) ≠ 0 := by
    rw [← dfun]; exact ne_of_gt (dfunPosAux n g ξ hξ)
  rw [hz]
  exact nullNormOne (wvec_visualDefs g ξ) hnull ht

end

end Work.Mostow
