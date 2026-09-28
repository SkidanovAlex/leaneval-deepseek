import Mathlib
import Submission.Work.HP.JcVolDefs
import Submission.Work.HP.BallVolIntrinsic

/-!
# The volume of the unit ball of `Q = (ℝw ⊕ ℝz)ᗮ`

`VQ w z` is by definition the volume of the closed unit ball of the orthogonal complement
`Q = (span {w, z})ᗮ` of the plane spanned by two linearly independent vectors `w, z` in
`EuclideanSpace ℝ ι`.  Since `Q` is a finite-dimensional real inner product space, this
volume is intrinsic: it equals `ballVol (finrank ℝ Q)`, the volume of the unit ball of the
standard Euclidean space of the same dimension (`BallVolIntrinsic`).  When `w, z` are linearly
independent, `finrank ℝ Q = card ι - 2`, which gives the stated identity.
-/

set_option autoImplicit false
noncomputable section

namespace Work.HP

/-- The orthogonal complement `Q = (ℝw ⊕ ℝz)ᗮ` of the plane spanned by two linearly
independent vectors has dimension `card ι - 2`. -/
theorem finrank_perpQ_of_indep {ι : Type*} [Fintype ι] {w z : EuclideanSpace ℝ ι}
    (h : IsIndep w z) :
    Module.finrank ℝ (perpQ w z) = Fintype.card ι - 2 := by
  have hspan : Submodule.span ℝ {w, z} = Submodule.span ℝ (Set.range ![w, z]) := by
    congr 1
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range, Fin.exists_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    tauto
  have h1 : Module.finrank ℝ ↥(planeP w z) = 2 := by
    rw [planeP, hspan, finrank_span_eq_card (b := ![w, z]) h]
    simp
  have h2 := Submodule.finrank_add_finrank_orthogonal (planeP w z)
  have h3 : Module.finrank ℝ (EuclideanSpace ℝ ι) = Fintype.card ι := by simp
  simp only [perpQ]
  omega

/-- The volume `VQ w z` of the unit ball of `Q = (ℝw ⊕ ℝz)ᗮ` is the `(card ι - 2)`-dimensional
ball volume. -/
theorem VQ_ballVol {ι : Type*} [Fintype ι] (hN : 3 ≤ Fintype.card ι)
    {w z : EuclideanSpace ℝ ι} (h : IsIndep w z) :
    VQ w z = ballVol (Fintype.card ι - 2) := by
  rw [VQ, BallVolIntrinsic (V := ↥(perpQ w z)), finrank_perpQ_of_indep h]

end Work.HP
