import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `PggAux` — the elementary ingredients of the `gg`-row estimate

This module collects the parts of the proof of `Work.FTS.Nonlinear.Pieces.rl1Pieces.Pgg`
that do not use the nonlinearity: elementary properties of the radial weight
`w = (1+z)²/z²`, the fact that `θ ∈ (0,π/2)` holds a.e. on `Iθ`, and the three *slot*
bounds `w·(D_z^j D_θ^i G)² ≤ HkIntegrand α 4 G` for `(j,i) = (0,0), (0,1), (1,0)` (in
pointwise-interior and a.e. form).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.rl1Pieces

set_option autoImplicit false

/-! ## The weight `w` -/

theorem w_nonneg_aux (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]; positivity

theorem one_le_w_aux {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg z, hz]

/-- `z⁻¹ ≤ w z` for `z > 0` (used to replace the `r⁻¹` weight by the Hardy weight). -/
theorem inv_le_w_aux {z : ℝ} (hz : 0 < z) : z⁻¹ ≤ Work.Spaces.w z := by
  have hz2 : (0 : ℝ) < z ^ 2 := by positivity
  have h1 : (1 : ℝ) / z = z / z ^ 2 := by field_simp
  rw [Work.Spaces.w, inv_eq_one_div, h1, div_le_div_iff_of_pos_right hz2]
  nlinarith [sq_nonneg z, hz]

/-- `θ ∈ (0,π/2)` is an a.e. statement on `Iθ`. -/
theorem ae_mem_Ioo_Iθ_aux :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  have hset : (Set.Ioo (0 : ℝ) (Real.pi / 2)) =ᵐ[MeasureTheory.volume] Work.Spaces.Iθ :=
    MeasureTheory.Ioo_ae_eq_Icc
  have h1 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))),
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := MeasureTheory.ae_restrict_mem measurableSet_Ioo
  rw [MeasureTheory.Measure.restrict_congr_set hset] at h1
  exact h1

theorem sin_two_pos_aux {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) := by
  have h2 : (2 : ℝ) * θ ∈ Set.Ioo 0 Real.pi :=
    ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  exact Real.sin_pos_of_pos_of_lt_pi h2.1 h2.2

theorem sin_two_le_one_aux (θ : ℝ) : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _

/-- `w z ≤ (w z / sin(2θ)^{η/2})²` for `z > 0`, `θ ∈ (0,π/2)`. -/
theorem w_le_div_rpow_sq {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.w z ≤ (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2 := by
  have hs0 : 0 < Real.sin (2 * θ) := sin_two_pos_aux hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := sin_two_le_one_aux θ
  have hη : (0 : ℝ) ≤ Work.Spaces.eta := by rw [Work.Spaces.eta]; norm_num
  have hsη : Real.sin (2 * θ) ^ Work.Spaces.eta ≤ 1 :=
    Real.rpow_le_one (le_of_lt hs0) hs1 hη
  have hden : (0 : ℝ) < Real.sin (2 * θ) ^ Work.Spaces.eta := Real.rpow_pos_of_pos hs0 _
  have hsq2 : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
      = Real.sin (2 * θ) ^ Work.Spaces.eta := by
    rw [sq, ← Real.rpow_add hs0]
    congr 1
    ring
  rw [div_pow, hsq2, le_div_iff₀ hden]
  calc Work.Spaces.w z * Real.sin (2 * θ) ^ Work.Spaces.eta
      ≤ Work.Spaces.w z * 1 := mul_le_mul_of_nonneg_left hsη (w_nonneg_aux z)
    _ = Work.Spaces.w z := mul_one _
    _ ≤ Work.Spaces.w z * Work.Spaces.w z :=
        le_mul_of_one_le_left (w_nonneg_aux z) (one_le_w_aux hz)
    _ = Work.Spaces.w z ^ 2 := (sq _).symm

/-- `w z ≤ Wt α z θ ^ 2` for `0 ≤ α`, `z > 0`, `θ ∈ (0,π/2)`. -/
theorem w_le_Wt_sq (α : ℝ) (hα : 0 ≤ α) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.w z ≤ (Work.Spaces.Wt α z θ) ^ 2 := by
  have hs0 : 0 < Real.sin (2 * θ) := sin_two_pos_aux hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := sin_two_le_one_aux θ
  have hγ : (0 : ℝ) ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hth : 1 ≤ Work.Spaces.wTheta α θ := by
    rw [Work.Spaces.wTheta]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs0 hs1 (by linarith)
  have hth2 : 1 ≤ (Work.Spaces.wTheta α θ) ^ 2 := by nlinarith [hth]
  have h1 : Work.Spaces.w z ≤ (Work.Spaces.w z) ^ 2 := by
    rw [sq]
    exact le_mul_of_one_le_left (w_nonneg_aux z) (one_le_w_aux hz)
  have h2 : (Work.Spaces.w z) ^ 2 ≤ (Work.Spaces.w z) ^ 2 * (Work.Spaces.wTheta α θ) ^ 2 :=
    le_mul_of_one_le_right (by positivity) hth2
  rw [Work.Spaces.Wt, mul_pow]
  exact le_trans h1 h2

/-! ## The three slot bounds -/

theorem w_mul_sq_le_HkIntegrand_self (α : ℝ) {G : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.w z * (G z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 G z θ := by
  have h1 : Work.Spaces.w z * (G z θ) ^ 2
      ≤ (G z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    calc Work.Spaces.w z * (G z θ) ^ 2
        ≤ (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2 * (G z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right (w_le_div_rpow_sq hz hθ) (sq_nonneg _)
      _ = (G z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
  refine le_trans h1 ?_
  simpa only [Work.Spaces.DzIter_zero] using
    Work.Spaces.sq_le_HkIntegrand_z α 4 G z θ 0 (by norm_num)

theorem w_mul_sq_le_HkIntegrand_Dth (α : ℝ) (hα : 0 ≤ α) {G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.w z * (Work.Spaces.Dth G z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 G z θ := by
  have h1 : Work.Spaces.w z * (Work.Spaces.Dth G z θ) ^ 2
      ≤ (Work.Spaces.Dth G z θ * Work.Spaces.Wt α z θ) ^ 2 := by
    calc Work.Spaces.w z * (Work.Spaces.Dth G z θ) ^ 2
        ≤ (Work.Spaces.Wt α z θ) ^ 2 * (Work.Spaces.Dth G z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right (w_le_Wt_sq α hα hz hθ) (sq_nonneg _)
      _ = (Work.Spaces.Dth G z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
  refine le_trans h1 ?_
  simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero]
    using Work.Spaces.sq_le_HkIntegrand_mixed α 4 G z θ 1 0 le_rfl (by norm_num)

theorem w_mul_sq_le_HkIntegrand_Dz (α : ℝ) {G : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.w z * (Work.Spaces.Dz G z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 G z θ := by
  have h1 : Work.Spaces.w z * (Work.Spaces.Dz G z θ) ^ 2
      ≤ (Work.Spaces.Dz G z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    calc Work.Spaces.w z * (Work.Spaces.Dz G z θ) ^ 2
        ≤ (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
            * (Work.Spaces.Dz G z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right (w_le_div_rpow_sq hz hθ) (sq_nonneg _)
      _ = (Work.Spaces.Dz G z θ
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
  refine le_trans h1 ?_
  simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using
    Work.Spaces.sq_le_HkIntegrand_z α 4 G z θ 1 (by norm_num)

/-! ## The a.e.-in-`θ` forms -/

theorem ae_w_mul_sq_self_le_HkIntegrand (α : ℝ) {G : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.w z * (G z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 G z θ := by
  filter_upwards [ae_mem_Ioo_Iθ_aux] with θ hθ
  exact w_mul_sq_le_HkIntegrand_self α hz hθ

theorem ae_w_mul_sq_Dth_le_HkIntegrand (α : ℝ) (hα : 0 ≤ α) {G : ℝ → ℝ → ℝ} {z : ℝ}
    (hz : 0 < z) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.w z * (Work.Spaces.Dth G z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 G z θ := by
  filter_upwards [ae_mem_Ioo_Iθ_aux] with θ hθ
  exact w_mul_sq_le_HkIntegrand_Dth α hα hz hθ

theorem ae_w_mul_sq_Dz_le_HkIntegrand (α : ℝ) {G : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.w z * (Work.Spaces.Dz G z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 G z θ := by
  filter_upwards [ae_mem_Ioo_Iθ_aux] with θ hθ
  exact w_mul_sq_le_HkIntegrand_Dz α hz hθ

/-! ## Continuity and a.e.-measurability of the slots of a `SmoothQuad` function -/

theorem quad_subset : (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))
    ⊆ (Set.Ioi (-1) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  Set.prod_mono (Set.Ioi_subset_Ioi (by norm_num)) (le_refl _)

theorem contOn_uncurry_of_smoothQuad {G : ℝ → ℝ → ℝ} (h : Work.FTS.LocData.SmoothQuad G) :
    ContinuousOn (Function.uncurry G) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
  (h.mono quad_subset).continuousOn

theorem contOn_uncurry_Dth_of_smoothQuad {G : ℝ → ℝ → ℝ}
    (h : Work.FTS.LocData.SmoothQuad G) :
    ContinuousOn (Function.uncurry (Work.Spaces.Dth G))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
  ((Work.FTS.LocData.contDiffOn_Dth Work.FTS.LocData.isOpen_quadU h).mono quad_subset).continuousOn

theorem contOn_uncurry_Dz_of_smoothQuad {G : ℝ → ℝ → ℝ}
    (h : Work.FTS.LocData.SmoothQuad G) :
    ContinuousOn (Function.uncurry (Work.Spaces.Dz G))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
  ((Work.FTS.LocData.contDiffOn_Dz Work.FTS.LocData.isOpen_quadU h).mono quad_subset).continuousOn

theorem aesm_uncurry_of_smoothQuad {G : ℝ → ℝ → ℝ} (h : Work.FTS.LocData.SmoothQuad G) :
    MeasureTheory.AEStronglyMeasurable (Function.uncurry G)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _ (contOn_uncurry_of_smoothQuad h)

theorem aesm_uncurry_Dth_of_smoothQuad {G : ℝ → ℝ → ℝ}
    (h : Work.FTS.LocData.SmoothQuad G) :
    MeasureTheory.AEStronglyMeasurable (Function.uncurry (Work.Spaces.Dth G))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _ (contOn_uncurry_Dth_of_smoothQuad h)

theorem aesm_uncurry_Dz_of_smoothQuad {G : ℝ → ℝ → ℝ}
    (h : Work.FTS.LocData.SmoothQuad G) :
    MeasureTheory.AEStronglyMeasurable (Function.uncurry (Work.Spaces.Dz G))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _ (contOn_uncurry_Dz_of_smoothQuad h)

theorem aesm_slice_of_smoothQuad {G : ℝ → ℝ → ℝ} (h : Work.FTS.LocData.SmoothQuad G) {z : ℝ}
    (hz : 0 < z) :
    MeasureTheory.AEStronglyMeasurable (fun θ => G z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd _ (contOn_uncurry_of_smoothQuad h) hz

theorem aesm_slice_Dth_of_smoothQuad {G : ℝ → ℝ → ℝ} (h : Work.FTS.LocData.SmoothQuad G)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.AEStronglyMeasurable (fun θ => Work.Spaces.Dth G z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd _ (contOn_uncurry_Dth_of_smoothQuad h) hz

theorem aesm_slice_Dz_of_smoothQuad {G : ℝ → ℝ → ℝ} (h : Work.FTS.LocData.SmoothQuad G)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.AEStronglyMeasurable (fun θ => Work.Spaces.Dz G z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd _ (contOn_uncurry_Dz_of_smoothQuad h) hz

end Work.FTS.Nonlinear.Pieces.rl1Pieces
