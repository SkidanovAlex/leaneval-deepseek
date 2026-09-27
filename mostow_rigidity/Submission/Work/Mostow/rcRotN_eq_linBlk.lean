import Mathlib
import Submission.Work.Mostow.nearId_rotN_bound
import Submission.Work.Mostow.blkMap_linBlk

/-!
# `rcRotN_eq_linBlk`

The block map `linBlk k m R` keeps the first `k` coordinates of `u : E (k + m)` and applies the
linear isometry `R` of `E m` to the last `m` ones, so its displacement is exactly the
displacement of `R` on the normal coordinate `nrmC k m u`:

  `linBlk k m R u - u = nrb_mk k m 0 (R (nrmC k m u) - nrmC k m u)`,

whence `‖linBlk k m R u - u‖ = ‖R (nrmC k m u) - nrmC k m u‖`.  Since `‖nrmC k m u‖ ≤ ‖u‖`
and conversely every vector of `E m` occurs as the normal coordinate of a vector of `E (k + m)`
of the same norm (`nrb_mk k m 0 y`), the condition `∀ u, ‖linBlk k m R u - u‖ ≤ K ‖u‖` is
equivalent to `∀ y, ‖R y - y‖ ≤ K ‖y‖`, i.e. to `rotN R ≤ K`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-- The normal coordinate is no longer than the whole vector. -/
private lemma nrmC_norm_le (k m : ℕ) (u : E (k + m)) : ‖nrmC k m u‖ ≤ ‖u‖ := by
  have h : ‖nrmC k m u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    rw [nib_norm_sq_split k m u]
    nlinarith [sq_nonneg ‖tanC k m u‖]
  calc ‖nrmC k m u‖ = Real.sqrt (‖nrmC k m u‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖u‖ ^ 2) := Real.sqrt_le_sqrt h
    _ = ‖u‖ := Real.sqrt_sq (norm_nonneg _)

/-- The displacement of the block map is the displacement of `R` on the normal coordinate. -/
private lemma linBlk_sub_norm (k m : ℕ) (R : E m ≃ₗᵢ[ℝ] E m) (u : E (k + m)) :
    ‖linBlk k m R u - u‖ = ‖R (nrmC k m u) - nrmC k m u‖ := by
  have hsplit := nib_norm_sq_split k m (linBlk k m R u - u)
  have h1 : tanC k m (linBlk k m R u - u) = 0 := by
    ext i; simp [tanC, linBlk]
  have h2 : nrmC k m (linBlk k m R u - u) = R (nrmC k m u) - nrmC k m u := by
    ext i; simp [nrmC, linBlk]
  rw [h1, h2] at hsplit
  have h2' : ‖linBlk k m R u - u‖ ^ 2 = ‖R (nrmC k m u) - nrmC k m u‖ ^ 2 := by
    rw [hsplit]; simp
  calc ‖linBlk k m R u - u‖ = Real.sqrt (‖linBlk k m R u - u‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖R (nrmC k m u) - nrmC k m u‖ ^ 2) := by rw [h2']
    _ = ‖R (nrmC k m u) - nrmC k m u‖ := Real.sqrt_sq (norm_nonneg _)

/-- The `nrb_mk k m 0 y` has the same norm as `y`. -/
private lemma nrb_mk_zero_norm (k m : ℕ) (y : E m) :
    ‖nrb_mk k m (0 : E k) y‖ = ‖y‖ := by
  calc ‖nrb_mk k m (0 : E k) y‖ = Real.sqrt (‖nrb_mk k m (0 : E k) y‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖y‖ ^ 2) := by
          congr 1
          rw [nrb_norm_sq_mk]; simp
    _ = ‖y‖ := Real.sqrt_sq (norm_nonneg _)

theorem rcRotN_eq_linBlk (k m : ℕ) (R : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) {K : ℝ} (hK : 0 ≤ K) :
    Submission.Mostow.rotN R ≤ K ↔
      ∀ u : Submission.Mostow.E (k + m), ‖Work.Mostow.linBlk k m R u - u‖ ≤ K * ‖u‖ := by
  constructor
  · intro hR u
    rw [linBlk_sub_norm]
    calc ‖R (nrmC k m u) - nrmC k m u‖ ≤ rotN R * ‖nrmC k m u‖ := nib_apply_le_rotN m R _
      _ ≤ K * ‖u‖ := mul_le_mul hR (nrmC_norm_le k m u) (norm_nonneg _) hK
  · intro h
    refine nib_rotN_le_of_unit hK ?_
    intro y hy
    set u : E (k + m) := nrb_mk k m (0 : E k) y with hu
    have hnu : ‖u‖ = 1 := by rw [hu, nrb_mk_zero_norm, hy]
    have hnc : nrmC k m u = y := by rw [hu]; exact nrb_nrmC_mk k m 0 y
    have hh := h u
    rw [linBlk_sub_norm, hnc, hnu, mul_one] at hh
    exact hh

end

end Work.Mostow
