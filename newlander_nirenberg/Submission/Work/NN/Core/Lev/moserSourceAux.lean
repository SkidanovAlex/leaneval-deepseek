import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.Lev.nnGradBoundPoint

/-!
# Auxiliary lemmas for the sourced Moser mean-value estimate (`moserSource`)

Let `W u Λ := fun z => max ‖u z‖ Λ` be the "shifted modulus" of `u`.  This file collects

* the chain-rule bound `‖fderiv (g ∘ h) x‖ ≤ C ‖fderiv h x‖` for a `C`-Lipschitz `g`,
* `W` is `1`-Lipschitz in `‖·‖`, hence `‖fderiv (W u Λ) z‖ ≤ ‖fderiv u z‖`,
* the same for the truncation `(W u Λ - h)⁺`,

which turn (the level-`1` instance of) the power Caccioppoli hypothesis
`HasPowCaccSource ρ A₀ Λ u` into the *potential* Caccioppoli inequality

`∫ φ² ‖fderiv (W u Λ)‖² ≤ 2·8n·A₀ (∫ ‖fderiv φ‖² W² + ∫ φ² W²)`

and, for every level `h ≥ 0` and every smooth nonnegative `φ` with `tsupport φ ⊆ Pd ρ` and
`tsupport φ ⊆ {h < W}`, the *level-truncated* Caccioppoli inequality

`∫ φ² ‖fderiv ((W - h)⁺)‖² ≤ A₀' (∫ ‖fderiv φ‖² ((W-h)⁺)² + h²∫ ‖fderiv φ‖² + h²∫ φ²)`.

The last one is exactly the hypothesis of `Work.NN.Core.Lev.dgSourceBounded`.
-/

open scoped NNReal ENNReal ContDiff Topology
open MeasureTheory Set Filter
open Work.CR.Flat

noncomputable section

namespace Work.NN.Core.Lev

/-! ## 1. The chain-rule bound for a Lipschitz outer function -/

/-- If `g` is `C`-Lipschitz and `h` is differentiable at `x`, then
`‖fderiv (g ∘ h) x‖ ≤ C ‖fderiv h x‖` (the left side being `0` when `g ∘ h` is not
differentiable at `x`). -/
theorem norm_fderiv_comp_lipschitz_le {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : F → G} {C : NNReal} (hg : LipschitzWith C g) {h : E → F} {x : E}
    (hh : DifferentiableAt ℝ h x) :
    ‖fderiv ℝ (g ∘ h) x‖ ≤ (C : ℝ) * ‖fderiv ℝ h x‖ := by
  by_cases hd : DifferentiableAt ℝ (g ∘ h) x
  · have hfd : HasFDerivAt (g ∘ h) (fderiv ℝ (g ∘ h) x) x := hd.hasFDerivAt
    have hhd : HasFDerivAt h (fderiv ℝ h x) x := hh.hasFDerivAt
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    have hmain : ‖(fderiv ℝ (g ∘ h) x) v‖ ≤ (C:ℝ) * ‖(fderiv ℝ h x) v‖ := by
      have hcurve : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
        have h1 : HasDerivAt (fun t : ℝ => t • v) v (0:ℝ) := by
          simpa using (hasDerivAt_id (0:ℝ)).smul_const (𝕜' := ℝ) v
        simpa using h1.const_add x
      have hh' : HasFDerivAt h (fderiv ℝ h x) ((fun t : ℝ => x + t • v) 0) := by
        simpa using hhd
      have hf' : HasFDerivAt (g ∘ h) (fderiv ℝ (g ∘ h) x) ((fun t : ℝ => x + t • v) 0) := by
        simpa using hfd
      have hslopeh : Tendsto (fun t : ℝ => t⁻¹ • (h (x + t • v) - h x))
          (𝓝[≠] (0:ℝ)) (𝓝 ((fderiv ℝ h x) v)) := by
        have h := HasFDerivAt.comp_hasDerivAt (f := fun t : ℝ => x + t • v) (l := h)
          (l' := fderiv ℝ h x) 0 hh' hcurve
        simpa using h.tendsto_slope_zero
      have hslopeL : Tendsto (fun t : ℝ => t⁻¹ • ((g ∘ h) (x + t • v) - (g ∘ h) x))
          (𝓝[≠] (0:ℝ)) (𝓝 ((fderiv ℝ (g ∘ h) x) v)) := by
        have h := HasFDerivAt.comp_hasDerivAt (f := fun t : ℝ => x + t • v) (l := g ∘ h)
          (l' := fderiv ℝ (g ∘ h) x) 0 hf' hcurve
        simpa [Function.comp_apply] using h.tendsto_slope_zero
      refine le_of_tendsto_of_tendsto ((continuous_norm.tendsto _).comp hslopeL)
        (((continuous_norm.tendsto _).comp hslopeh).const_mul (C:ℝ)) ?_
      filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
      have hY : ‖(g ∘ h) (x + t • v) - (g ∘ h) x‖ ≤ (C:ℝ) * ‖h (x + t • v) - h x‖ :=
        hg.norm_sub_le _ _
      have h1 : ‖t⁻¹ • ((g ∘ h) (x + t • v) - (g ∘ h) x)‖
          = |t|⁻¹ * ‖(g ∘ h) (x + t • v) - (g ∘ h) x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_inv]
      have h2 : (C:ℝ) * ‖t⁻¹ • (h (x + t • v) - h x)‖
          = (C:ℝ) * (|t|⁻¹ * ‖h (x + t • v) - h x‖) := by
        rw [norm_smul, Real.norm_eq_abs, abs_inv]
      simp only [Function.comp_apply] at hY h1 h2 ⊢
      rw [h1, h2]
      rw [show (C:ℝ) * (|t|⁻¹ * ‖h (x + t • v) - h x‖)
          = |t|⁻¹ * ((C:ℝ) * ‖h (x + t • v) - h x‖) from by ring]
      exact mul_le_mul_of_nonneg_left hY (inv_nonneg.mpr (abs_nonneg t))
    calc ‖(fderiv ℝ (g ∘ h) x) v‖ ≤ (C:ℝ) * ‖(fderiv ℝ h x) v‖ := hmain
      _ ≤ (C:ℝ) * (‖fderiv ℝ h x‖ * ‖v‖) :=
          mul_le_mul_of_nonneg_left ((fderiv ℝ h x).le_opNorm v) (by positivity)
      _ = ((C:ℝ) * ‖fderiv ℝ h x‖) * ‖v‖ := by ring
  · rw [fderiv_zero_of_not_differentiableAt hd]
    simp only [norm_zero]
    exact mul_nonneg (by positivity) (norm_nonneg _)

/-! ## 2. The `1`-Lipschitz functions `w ↦ max ‖w‖ c` and `t ↦ max (t - h) 0` -/

lemma lipschitzWith_max_norm (c : ℝ) : LipschitzWith 1 (fun w : ℂ => max ‖w‖ c) := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  rw [Real.dist_eq, Complex.dist_eq, NNReal.coe_one, one_mul]
  calc |max ‖a‖ c - max ‖b‖ c| ≤ |‖a‖ - ‖b‖| := abs_max_sub_max_le_abs _ _ _
    _ ≤ ‖a - b‖ := abs_norm_sub_norm_le a b

lemma lipschitzWith_max_sub_zero (h : ℝ) :
    LipschitzWith 1 (fun t : ℝ => max (t - h) 0) := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
  calc |max (a - h) 0 - max (b - h) 0| ≤ |(a - h) - (b - h)| := abs_max_sub_max_le_abs _ _ _
    _ = |a - b| := by ring_nf

/-! ## 3. The shifted modulus and its derivative bounds -/

/-- The shifted modulus `W u Λ z = max ‖u z‖ Λ`. -/
def srcW {n : ℕ} (u : Work.NN.Core.Cn n → ℂ) (Λ : ℝ) : Work.NN.Core.Cn n → ℝ :=
  fun z => max ‖u z‖ Λ

lemma srcW_eq_comp {n : ℕ} (u : Work.NN.Core.Cn n → ℂ) (Λ : ℝ) :
    srcW u Λ = (fun w : ℂ => max ‖w‖ Λ) ∘ u := rfl

theorem norm_fderiv_srcW_le {n : ℕ} {u : Work.NN.Core.Cn n → ℂ} {Λ : ℝ} {z : Work.NN.Core.Cn n}
    (hu : DifferentiableAt ℝ u z) :
    ‖fderiv ℝ (srcW u Λ) z‖ ≤ ‖fderiv ℝ u z‖ := by
  have h := norm_fderiv_comp_lipschitz_le (g := fun w : ℂ => max ‖w‖ Λ) (C := 1)
    (lipschitzWith_max_norm Λ) hu
  simpa [srcW_eq_comp] using h

theorem norm_fderiv_srcW_trunc_le {n : ℕ} {u : Work.NN.Core.Cn n → ℂ} {Λ h : ℝ}
    {z : Work.NN.Core.Cn n} (hu : DifferentiableAt ℝ u z) :
    ‖fderiv ℝ (fun w => max (srcW u Λ w - h) 0) z‖ ≤ ‖fderiv ℝ u z‖ := by
  have hcomp : (fun w => max (srcW u Λ w - h) 0)
      = (fun t : ℝ => max (t - h) 0) ∘ (fun w : ℂ => max ‖w‖ Λ) ∘ u := rfl
  rw [hcomp]
  have h1 : LipschitzWith 1 ((fun t : ℝ => max (t - h) 0)
      ∘ (fun w : ℂ => max ‖w‖ Λ)) := by
    have hc := (lipschitzWith_max_sub_zero h).comp (lipschitzWith_max_norm Λ)
    simpa using hc
  have := norm_fderiv_comp_lipschitz_le (g := (fun t : ℝ => max (t - h) 0)
      ∘ (fun w : ℂ => max ‖w‖ Λ)) (C := 1) h1 hu
  simpa [Function.comp_apply, Function.comp_def] using this

end Work.NN.Core.Lev
