import Mathlib
import Submission.Work.Drive.fiveCollinearDefs
import Submission.Work.Drive.knobRank
import Submission.Work.Drive.rank_patchA

/-!
# The rank of the coefficient derivative of the five-point collinearity map

**`Work.Drive.rank_fivePsi_slice`**: at any `(c₀, w)` with nonzero first chord
`pertV r c₀ (w 1) - pertV r c₀ (w 0)`, the partial derivative of `fivePsi r` in the coefficient
variable has rank at least `6`.  Since the parameter space `Fin 5 → ℝ` is `5`-dimensional, this is
the strict `rank > finrank W` hypothesis of
`Work.Proj.interior_zeroSet_projection_empty_of_rank`.

The three independent knobs are the three slots `2, 3, 4`: a coefficient direction whose value-map
derivative is `-u` in slot `j` and `0` elsewhere produces `u × a` (with `a` the first chord) in the
`j`-th factor of the target and `0` in the other two; `three_knob_rank`
(`Submission/Work/Drive/knobRank.lean`) then adds the three ranks `2 + 2 + 2`.
-/

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-! ## The target tuples of the knobs -/

/-- The tuple of values which is `-u` in slot `j` and `0` in the other four. -/
def knobTgt (j : Fin 5) (u : Space) : Fin 5 → Space := fun i => if i = j then -u else 0

lemma knobTgt_self (j : Fin 5) (u : Space) : knobTgt j u j = -u := by
  simp [knobTgt]

lemma knobTgt_of_ne {j i : Fin 5} (h : i ≠ j) (u : Space) : knobTgt j u i = 0 := by
  simp [knobTgt, h]

lemma cross3_neg_right_eq_swap (a u : Space) : cross3 a (-u) = cross3 u a := by
  rw [cross3_neg_right, cross3_anticomm a u]

/-! ## The coefficient derivative of `fivePsi` along a coefficient line -/

/-- The coefficient derivative of `fivePsi r` in coordinates: the Leibniz rule for the three
components `(P₁-P₀) × (P_k-P₀)` of `collMap5`. -/
lemma fderiv_fivePsi_axis {r : ℝ → Space} (hr : IsSmoothKnot r) (w : Fin 5 → ℝ) (c₀ dc : Coeff) :
    (fderiv ℝ (fun c : Coeff => fivePsi r (c, w)) c₀) dc
      = (cross3 (valLin w dc 1 - valLin w dc 0) (pertV r c₀ (w 2) - pertV r c₀ (w 0))
           + cross3 (pertV r c₀ (w 1) - pertV r c₀ (w 0)) (valLin w dc 2 - valLin w dc 0),
         cross3 (valLin w dc 1 - valLin w dc 0) (pertV r c₀ (w 3) - pertV r c₀ (w 0))
           + cross3 (pertV r c₀ (w 1) - pertV r c₀ (w 0)) (valLin w dc 3 - valLin w dc 0),
         cross3 (valLin w dc 1 - valLin w dc 0) (pertV r c₀ (w 4) - pertV r c₀ (w 0))
           + cross3 (pertV r c₀ (w 1) - pertV r c₀ (w 0)) (valLin w dc 4 - valLin w dc 0)) := by
  have hdiff : DifferentiableAt ℝ (fun c : Coeff => fivePsi r (c, w)) c₀ :=
    DifferentiableAt.comp c₀
      ((contDiff_collMap5.differentiable (by norm_num)).differentiableAt
        (x := valMap r (c₀, w)))
      (hasFDerivAt_valMap_slice r w c₀).differentiableAt
  have h1 := Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv
    (H := fun c : Coeff => fivePsi r (c, w)) (p := c₀) (e := dc) hdiff
  refine h1.unique ?_
  have hP : ∀ i : Fin 5, HasDerivAt (fun s : ℝ => valMap r (c₀ + s • dc, w) i)
      (valLin w dc i) 0 := fun i => hasDerivAt_valMap_axis_apply r w c₀ dc i
  have hv : ∀ i : Fin 5, valMap r (c₀ + (0 : ℝ) • dc, w) i = pertV r c₀ (w i) := by
    intro i
    simp [valMap]
  have hcomp : ∀ k : Fin 5, k ≠ 0 → k ≠ 1 →
      HasDerivAt (fun s : ℝ => cross3 (valMap r (c₀ + s • dc, w) 1 - valMap r (c₀ + s • dc, w) 0)
          (valMap r (c₀ + s • dc, w) k - valMap r (c₀ + s • dc, w) 0))
        (cross3 (valLin w dc 1 - valLin w dc 0) (pertV r c₀ (w k) - pertV r c₀ (w 0))
          + cross3 (pertV r c₀ (w 1) - pertV r c₀ (w 0)) (valLin w dc k - valLin w dc 0)) 0 := by
    intro k _ _
    have hA : HasDerivAt
        (fun s : ℝ => valMap r (c₀ + s • dc, w) 1 - valMap r (c₀ + s • dc, w) 0)
        (valLin w dc 1 - valLin w dc 0) 0 := (hP 1).sub (hP 0)
    have hB : HasDerivAt
        (fun s : ℝ => valMap r (c₀ + s • dc, w) k - valMap r (c₀ + s • dc, w) 0)
        (valLin w dc k - valLin w dc 0) 0 := (hP k).sub (hP 0)
    have h := hasDerivAt_cross3_curves _ _ hA hB
    simpa [hv k, hv 1, hv 0] using h
  exact (hcomp 2 (by decide) (by decide)).prodMk
    ((hcomp 3 (by decide) (by decide)).prodMk (hcomp 4 (by decide) (by decide)))

/-! ## The rank statement -/

/-- **The coefficient derivative of the five-point collinearity map has rank at least `6`.** -/
theorem rank_fivePsi_slice {r : ℝ → Space} (hr : IsSmoothKnot r) (w : Fin 5 → ℝ) (c₀ : Coeff)
    (hJ : Function.Surjective (valLin w))
    (hd : pertV r c₀ (w 1) - pertV r c₀ (w 0) ≠ 0) :
    6 ≤ Module.finrank ℝ
      (LinearMap.range ((fderiv ℝ (fun c : Coeff => fivePsi r (c, w)) c₀).toLinearMap)) := by
  classical
  let D : Coeff →ₗ[ℝ] Space × Space × Space :=
    (fderiv ℝ (fun c : Coeff => fivePsi r (c, w)) c₀).toLinearMap
  have hknob : ∀ j : Fin 5, ∀ u : Space, ∃ dc : Coeff, valLin w dc = knobTgt j u :=
    fun j u => hJ (knobTgt j u)
  choose dir hdir using hknob
  set f : Space →ₗ[ℝ] Space := rpa_crossLin (pertV r c₀ (w 1) - pertV r c₀ (w 0)) with hf
  have h2 : ∀ u : Space, D (dir 2 u) = (f u, 0, 0) := by
    intro u
    show (fderiv ℝ (fun c : Coeff => fivePsi r (c, w)) c₀) (dir 2 u) = _
    rw [fderiv_fivePsi_axis hr w c₀ (dir 2 u), hdir 2 u]
    rw [knobTgt_of_ne (by decide : (0 : Fin 5) ≠ (2 : Fin 5)) u,
      knobTgt_of_ne (by decide : (1 : Fin 5) ≠ (2 : Fin 5)) u, knobTgt_self (2 : Fin 5) u,
      knobTgt_of_ne (by decide : (3 : Fin 5) ≠ (2 : Fin 5)) u,
      knobTgt_of_ne (by decide : (4 : Fin 5) ≠ (2 : Fin 5)) u]
    simp only [sub_zero, zero_sub, cross3_zero_left, cross3_zero_right, zero_add, add_zero,
      cross3_neg_right_eq_swap, hf, rpa_crossLin_apply]
  have h3 : ∀ u : Space, D (dir 3 u) = (0, f u, 0) := by
    intro u
    show (fderiv ℝ (fun c : Coeff => fivePsi r (c, w)) c₀) (dir 3 u) = _
    rw [fderiv_fivePsi_axis hr w c₀ (dir 3 u), hdir 3 u]
    rw [knobTgt_of_ne (by decide : (0 : Fin 5) ≠ (3 : Fin 5)) u,
      knobTgt_of_ne (by decide : (1 : Fin 5) ≠ (3 : Fin 5)) u,
      knobTgt_of_ne (by decide : (2 : Fin 5) ≠ (3 : Fin 5)) u, knobTgt_self (3 : Fin 5) u,
      knobTgt_of_ne (by decide : (4 : Fin 5) ≠ (3 : Fin 5)) u]
    simp only [sub_zero, zero_sub, cross3_zero_left, cross3_zero_right, zero_add, add_zero,
      cross3_neg_right_eq_swap, hf, rpa_crossLin_apply]
  have h4 : ∀ u : Space, D (dir 4 u) = (0, 0, f u) := by
    intro u
    show (fderiv ℝ (fun c : Coeff => fivePsi r (c, w)) c₀) (dir 4 u) = _
    rw [fderiv_fivePsi_axis hr w c₀ (dir 4 u), hdir 4 u]
    rw [knobTgt_of_ne (by decide : (0 : Fin 5) ≠ (4 : Fin 5)) u,
      knobTgt_of_ne (by decide : (1 : Fin 5) ≠ (4 : Fin 5)) u,
      knobTgt_of_ne (by decide : (2 : Fin 5) ≠ (4 : Fin 5)) u,
      knobTgt_of_ne (by decide : (3 : Fin 5) ≠ (4 : Fin 5)) u, knobTgt_self (4 : Fin 5) u]
    simp only [sub_zero, zero_sub, cross3_zero_left, cross3_zero_right, zero_add, add_zero,
      cross3_neg_right_eq_swap, hf, rpa_crossLin_apply]
  have hres := three_knob_rank (D := D) (f₁ := f) (f₂ := f) (f₃ := f)
    (dir 2) (dir 3) (dir 4) h2 h3 h4
  rw [hf, rpa_finrank_range_crossLin hd] at hres
  have hD' : LinearMap.range D
      = LinearMap.range ((fderiv ℝ (fun c : Coeff => fivePsi r (c, w)) c₀).toLinearMap) := rfl
  rw [hD'] at hres
  omega

end

end Work.Drive
