import Mathlib
import Submission.Work.HP.ArchDefs
import Submission.Work.HP.Defs
import Submission.Work.HP.evaldefs
import Submission.Work.HP.veronese_first
import Submission.Work.HP.rNorm_smul

/-!
# `Work.HP.BoundaryMain.Utils`

Elementary infrastructure shared by the lemmas used to prove
`Work.HP.BoundaryMain.exists_crit_zero` (the boundary point of the proof of Theorem 1.1:

* `continuous_formEvalR` : `y ↦ f_c(y)` is continuous;
* `IPt_of_ne_zero` : a nonzero real zero of `f_c` can be scaled to the unit sphere, so gives
  `IPt d n c`;
* `continuous_segment` : `t ↦ toR a + t • (b - toR a)` is continuous;
* `isClosed_preimage_IPt_segment` : the set of parameters `t` along the segment at which the
  point is real-soluble on the unit sphere is closed (given that `IPt` is closed);
* `dotR_self_eq_rNorm_sq` : `⟨v, v⟩ = ‖v‖²`;
* `rNorm_segment_sub` : `‖(toR a + t • (b - toR a)) - toR a‖ = |t| ‖b - toR a‖`.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP.BoundaryMain

open Work.HP

/-- `y ↦ f_c(y) = formEvalR d n c y` is continuous on the finite-dimensional space
`Fin (n+1) → ℝ` (with the product topology). -/
lemma continuous_formEvalR (d n : ℕ) (c : Mon d n → ℝ) :
    Continuous (fun y : Fin (n + 1) → ℝ => formEvalR d n c y) := by
  simp only [formEvalR]
  refine continuous_finsetSum _ (fun m _ => ?_)
  refine continuous_const.mul ?_
  simp only [veronese]
  exact continuous_finsetProd _ (fun i _ => (continuous_apply i).pow _)

/-- `y ↦ f_c(x + s • v)` is continuous in `s`. -/
lemma continuous_formEvalR_along (d n : ℕ) (c : Mon d n → ℝ) (x v : Fin (n + 1) → ℝ) :
    Continuous (fun s : ℝ => formEvalR d n c (x + s • v)) :=
  (continuous_formEvalR d n c).comp (by fun_prop)

/-- A nonzero real zero of `f_c` can be scaled to the Euclidean unit sphere: any `y ≠ 0` with
`f_c(y) = 0` witnesses `IPt d n c`. -/
lemma IPt_of_ne_zero (d n : ℕ) {c : Mon d n → ℝ} {y : Fin (n + 1) → ℝ}
    (hy : y ≠ 0) (h : formEvalR d n c y = 0) : IPt d n c := by
  have hpos : 0 < rNorm y :=
    lt_of_le_of_ne (rNorm_nonneg y) (fun h0 => hy (rNorm_eq_zero.mp h0.symm))
  refine ⟨(rNorm y)⁻¹ • y, ?_, ?_⟩
  · rw [rNorm_smul', abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ (ne_of_gt hpos)]
  · rw [formEvalR_homogeneous, h, mul_zero]

/-- The segment `t ↦ toR a + t • (b - toR a)` joining the integer form `toR a` to `b`
is continuous. -/
lemma continuous_segment (d n : ℕ) (a : Mon d n → ℤ) (b : Mon d n → ℝ) :
    Continuous (fun t : ℝ => toR a + t • (b - toR a)) := by
  fun_prop

/-- Along the segment, the set of parameters at which the point is real-soluble on the unit
sphere is closed. -/
lemma isClosed_preimage_IPt_segment (d n : ℕ)
    (hclose : IsClosed {a : Mon d n → ℝ | IPt d n a})
    (a : Mon d n → ℤ) (b : Mon d n → ℝ) :
    IsClosed {t : ℝ | IPt d n (toR a + t • (b - toR a))} :=
  hclose.preimage (continuous_segment d n a b)

/-- `⟨v, v⟩ = ‖v‖²`. -/
lemma dotR_self_eq_rNorm_sq {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    dotR v v = rNorm v ^ 2 := by
  rw [dotR, rNorm_sq]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- The distance from a point of the segment to its initial point. -/
lemma rNorm_segment_sub (d n : ℕ) (a : Mon d n → ℤ) (b : Mon d n → ℝ) (t : ℝ) :
    rNorm ((toR a + t • (b - toR a)) - toR a) = |t| * rNorm (b - toR a) := by
  rw [add_sub_cancel_left, rNorm_smul']

end Work.HP.BoundaryMain
