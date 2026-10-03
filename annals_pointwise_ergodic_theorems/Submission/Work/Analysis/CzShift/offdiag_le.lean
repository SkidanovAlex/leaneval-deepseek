import Mathlib
import Submission.Work.Analysis.CzShift.lacunary_sums
import Submission.Work.Analysis.CzShift.kernel_bounds

/-!
# The off-diagonal estimate for the shifted Calderón–Zygmund kernels

This file proves `Work.Analysis.CzShift.offdiag_le`: the off-diagonal (Hörmander-type)
estimate of Appendix B of Krause–Mirek–Tao, *Pointwise ergodic theorems for
non-conventional bilinear polynomial averages*, Annals of Math. **195** (2022).

For a `lam`-lacunary family of positive scales `σ : ι → ℝ` on `D : Finset ι` and shifts
`t : ι → ℝ` bounded by `2 ^ K` (`K ≥ 1`), the sum over `i ∈ D` of the `L¹(50 L ≤ |x|)`-norms
of the differences `shiftKernel Ψ (σ i) (t i) (· - y) - shiftKernel Ψ (σ i) (t i)` is bounded
by `C B (1 + K)`, where `B` is the size parameter of the seed `Ψ` (`IsCZSeed Ψ Ψ' B`).

The proof proceeds by splitting the scales into three groups, each estimated separately:

* **large scales** `2 |y| ≤ σ i`: the pointwise increment bound `(B.3)` of `kernel_bounds`
  gives, after integrating over `ℝ`, the bound `4 π B |y| / σ i`; the sum over these scales
  is a lacunary **tail** sum, bounded by `2 π B / (1 - lam⁻¹)`;
* **small scales with a near centre** `σ i < 2 |y|`, `|t i * σ i| ≤ 45 L`: the triangle
  inequality, the pointwise seed decay and the tail integrals of the rescaled Cauchy bump
  (the lemmas `bump_Ici_le`, `bump_Iic_le` below) give `4 B σ i / (4.5 L)`; the sum is a
  lacunary **head** sum, bounded by `4 B / (4.5 (1 - lam⁻¹))`;
* **small scales with a far centre** `σ i < 2 |y|`, `45 L < |t i * σ i|`: the `L¹` bound
  `(B.2)` of `kernel_bounds` gives `2 π B` for each such scale, and `|t i| ≤ 2 ^ K` forces
  them into the window `[L / 2 ^ K, L)`, in which a lacunary family has at most
  `1 + K log 2 / log lam` elements.

The arithmetic is collected in `lacunary_offdiag_sum`.
-/

namespace Work.Analysis.CzShift

open MeasureTheory Filter Topology

set_option autoImplicit false

variable {ι : Type*}

/-! ### Tail integrals of the rescaled Cauchy bump -/

/-- `arctan s ≤ s` for `s ≥ 0`. -/
lemma arctan_le_self_of_nonneg {s : ℝ} (hs : 0 ≤ s) : Real.arctan s ≤ s := by
  have hmono : MonotoneOn (fun x : ℝ => x - Real.arctan x) Set.univ := by
    refine monotoneOn_of_deriv_nonneg convex_univ ?_ ?_ ?_
    · exact (continuous_id.sub Real.continuous_arctan).continuousOn
    · rw [interior_univ]
      exact (differentiable_id.sub Real.differentiable_arctan).differentiableOn
    · intro x _
      have hderiv : deriv (fun y : ℝ => y - Real.arctan y) x = 1 - (1 + x ^ 2)⁻¹ := by
        have h : HasDerivAt (fun y : ℝ => y - Real.arctan y) (1 - (1 + x ^ 2)⁻¹) x :=
          (hasDerivAt_id x).sub (Real.hasDerivAt_arctan' x)
        exact h.deriv
      rw [hderiv]
      have h1 : (1 + x ^ 2)⁻¹ ≤ 1 := by
        rw [inv_le_one₀ (by positivity)]
        nlinarith [sq_nonneg x]
      linarith
  have h01 : (0 : ℝ) - Real.arctan 0 ≤ s - Real.arctan s :=
    hmono (Set.mem_univ 0) (Set.mem_univ s) hs
  simp only [Real.arctan_zero, sub_zero] at h01
  linarith

/-- **Right tail integral of the rescaled Cauchy bump.**  If `a < c` then
`∫_{Ici c} σ⁻¹ B (1 + ((x-a)/σ)²)⁻¹ ≤ B σ / (c - a)`. -/
lemma bump_Ici_le {σ a B c : ℝ} (hσ : 0 < σ) (hB : 0 ≤ B) (hac : a < c) :
    ∫ x in Set.Ici c, σ⁻¹ * B * (1 + ((x - a) / σ) ^ 2)⁻¹ ≤ B * σ / (c - a) := by
  have hmain : ∫ x in Set.Ioi c, σ⁻¹ * B * (1 + ((x - a) / σ) ^ 2)⁻¹
      = B * (Real.pi / 2 - Real.arctan ((c - a) / σ)) := by
    have hderiv : ∀ x ∈ Set.Ici c, HasDerivAt (fun y : ℝ => B * Real.arctan ((y - a) / σ))
        (σ⁻¹ * B * (1 + ((x - a) / σ) ^ 2)⁻¹) x := by
      intro x _
      have h1 : HasDerivAt (fun y : ℝ => (y - a) / σ) (1 / σ) x :=
        ((hasDerivAt_id x).sub_const a).div_const σ
      have h2 : HasDerivAt (fun y : ℝ => Real.arctan ((y - a) / σ))
          ((1 + ((x - a) / σ) ^ 2)⁻¹ * (1 / σ)) x :=
        (Real.hasDerivAt_arctan' _).comp x h1
      have h3 : HasDerivAt (fun y : ℝ => B * Real.arctan ((y - a) / σ))
          (B * ((1 + ((x - a) / σ) ^ 2)⁻¹ * (1 / σ))) x := h2.const_mul B
      convert h3 using 1
      ring
    have hint : IntegrableOn (fun x : ℝ => σ⁻¹ * B * (1 + ((x - a) / σ) ^ 2)⁻¹) (Set.Ioi c) :=
      (((integrable_inv_one_add_sq.comp_div hσ.ne').comp_sub_right a).const_mul (σ⁻¹ * B)).integrableOn
    have hlim : Tendsto (fun y : ℝ => B * Real.arctan ((y - a) / σ)) atTop
        (𝓝 (B * (Real.pi / 2))) := by
      have h1 : Tendsto (fun y : ℝ => (y - a) / σ) atTop atTop :=
        (Filter.tendsto_atTop_add_const_right atTop (-a) Filter.tendsto_id).atTop_div_const hσ
      have h2 : Tendsto (fun y : ℝ => Real.arctan ((y - a) / σ)) atTop (𝓝 (Real.pi / 2)) :=
        (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp h1
      simpa using h2.const_mul B
    have key := integral_Ioi_of_hasDerivAt_of_tendsto' (a := c) hderiv hint hlim
    rw [key]
    ring
  rw [integral_Ici_eq_integral_Ioi, hmain]
  have ht : 0 < (c - a) / σ := div_pos (by linarith) hσ
  have hstep : Real.pi / 2 - Real.arctan ((c - a) / σ) = Real.arctan (((c - a) / σ)⁻¹) :=
    (Real.arctan_inv_of_pos ht).symm
  rw [hstep]
  calc B * Real.arctan (((c - a) / σ)⁻¹) ≤ B * ((c - a) / σ)⁻¹ :=
        mul_le_mul_of_nonneg_left (arctan_le_self_of_nonneg (inv_nonneg.mpr ht.le)) hB
    _ = B * σ / (c - a) := by rw [inv_div, mul_div_assoc]

/-- **Left tail integral of the rescaled Cauchy bump.**  If `c < a` then
`∫_{Iic c} σ⁻¹ B (1 + ((x-a)/σ)²)⁻¹ ≤ B σ / (a - c)`. -/
lemma bump_Iic_le {σ a B c : ℝ} (hσ : 0 < σ) (hB : 0 ≤ B) (hca : c < a) :
    ∫ x in Set.Iic c, σ⁻¹ * B * (1 + ((x - a) / σ) ^ 2)⁻¹ ≤ B * σ / (a - c) := by
  have hmain : ∫ x in Set.Iic c, σ⁻¹ * B * (1 + ((x - a) / σ) ^ 2)⁻¹
      = B * Real.arctan ((c - a) / σ) + B * (Real.pi / 2) := by
    have hderiv : ∀ x ∈ Set.Iic c, HasDerivAt (fun y : ℝ => B * Real.arctan ((y - a) / σ))
        (σ⁻¹ * B * (1 + ((x - a) / σ) ^ 2)⁻¹) x := by
      intro x _
      have h1 : HasDerivAt (fun y : ℝ => (y - a) / σ) (1 / σ) x :=
        ((hasDerivAt_id x).sub_const a).div_const σ
      have h2 : HasDerivAt (fun y : ℝ => Real.arctan ((y - a) / σ))
          ((1 + ((x - a) / σ) ^ 2)⁻¹ * (1 / σ)) x :=
        (Real.hasDerivAt_arctan' _).comp x h1
      have h3 : HasDerivAt (fun y : ℝ => B * Real.arctan ((y - a) / σ))
          (B * ((1 + ((x - a) / σ) ^ 2)⁻¹ * (1 / σ))) x := h2.const_mul B
      convert h3 using 1
      ring
    have hint : IntegrableOn (fun x : ℝ => σ⁻¹ * B * (1 + ((x - a) / σ) ^ 2)⁻¹) (Set.Iic c) :=
      (((integrable_inv_one_add_sq.comp_div hσ.ne').comp_sub_right a).const_mul (σ⁻¹ * B)).integrableOn
    have hlim : Tendsto (fun y : ℝ => B * Real.arctan ((y - a) / σ)) atBot
        (𝓝 (-(B * (Real.pi / 2)))) := by
      have h1 : Tendsto (fun y : ℝ => (y - a) / σ) atBot atBot :=
        (Filter.tendsto_atBot_add_const_right atBot (-a) Filter.tendsto_id).atBot_div_const hσ
      have h2 : Tendsto (fun y : ℝ => Real.arctan ((y - a) / σ)) atBot (𝓝 (-(Real.pi / 2))) :=
        (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atBot).comp h1
      simpa using h2.const_mul B
    have key := integral_Iic_of_hasDerivAt_of_tendsto' (a := c) hderiv hint hlim
    rw [key]
    ring
  rw [hmain]
  have ht : 0 < (a - c) / σ := div_pos (by linarith) hσ
  have hca' : (c - a) / σ = -((a - c) / σ) := by ring
  rw [hca', Real.arctan_neg]
  have hstep : Real.pi / 2 - Real.arctan ((a - c) / σ) = Real.arctan (((a - c) / σ)⁻¹) :=
    (Real.arctan_inv_of_pos ht).symm
  have hrew : B * (-Real.arctan ((a - c) / σ)) + B * (Real.pi / 2)
      = B * (Real.pi / 2 - Real.arctan ((a - c) / σ)) := by ring
  rw [hrew, hstep]
  calc B * Real.arctan (((a - c) / σ)⁻¹) ≤ B * ((a - c) / σ)⁻¹ :=
        mul_le_mul_of_nonneg_left (arctan_le_self_of_nonneg (inv_nonneg.mpr ht.le)) hB
    _ = B * σ / (a - c) := by rw [inv_div, mul_div_assoc]

/-! ### Integrability and continuity of the shifted kernels -/

/-- The shifted kernel `shiftKernel Ψ σ t` is continuous as soon as the seed has a
derivative everywhere. -/
lemma continuous_shiftKernel {Ψ Ψ' : ℝ → ℝ} {B : ℝ} (hseed : IsCZSeed Ψ Ψ' B) (σ t : ℝ) :
    Continuous (shiftKernel Ψ σ t) := by
  have hΨ : Continuous Ψ := by
    have hd : Differentiable ℝ Ψ := fun u => (hseed.hasDerivAt u).differentiableAt
    exact hd.continuous
  have h1 : Continuous fun x : ℝ => (Ψ ((x - t * σ) / σ) : ℂ) :=
    Complex.continuous_ofReal.comp (hΨ.comp (by continuity))
  have h2 : Continuous fun x : ℝ => ((σ⁻¹ : ℝ) : ℂ) * (Ψ ((x - t * σ) / σ) : ℂ) :=
    continuous_const.mul h1
  have hgoal : shiftKernel Ψ σ t
      = fun x : ℝ => ((σ⁻¹ : ℝ) : ℂ) * (Ψ ((x - t * σ) / σ) : ℂ) := by
    funext x
    simp only [shiftKernel]
    push_cast
    ring
  rw [hgoal]; exact h2

/-- The shifted kernel is integrable on `ℝ`. -/
lemma integrable_shiftKernel {Ψ Ψ' : ℝ → ℝ} {B : ℝ} (hseed : IsCZSeed Ψ Ψ' B)
    {σ t : ℝ} (hσ : 0 < σ) : Integrable (fun x : ℝ => shiftKernel Ψ σ t x) := by
  have hbump : Integrable (fun x : ℝ => σ⁻¹ * B * (1 + ((x - t * σ) / σ) ^ 2)⁻¹) :=
    (((integrable_inv_one_add_sq.comp_div hσ.ne').comp_sub_right (t * σ)).const_mul (σ⁻¹ * B))
  refine Integrable.mono' hbump (continuous_shiftKernel hseed σ t).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [shiftKernel_norm hσ t x]
  have h1 := hseed.bound ((x - t * σ) / σ)
  rw [div_eq_mul_inv] at h1
  calc σ⁻¹ * |Ψ ((x - t * σ) / σ)| ≤ σ⁻¹ * (B * (1 + ((x - t * σ) / σ) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = σ⁻¹ * B * (1 + ((x - t * σ) / σ) ^ 2)⁻¹ := by ring

/-! ### The three per-scale estimates -/

/-- **Large scales.**  If `2 |y| ≤ σ`, the increment of the shifted kernel is bounded
pointwise by `(B.3)`, and integrating over `ℝ` gives `4 π B |y| / σ`. -/
lemma offdiag_case_large {Ψ Ψ' : ℝ → ℝ} {B : ℝ} (hseed : IsCZSeed Ψ Ψ' B) {σ t y L : ℝ}
    (hσ : 0 < σ) (hy : 2 * |y| ≤ σ) (_hL : 0 < L) :
    ∫⁻ x in {x : ℝ | 50 * L ≤ |x|},
        ENNReal.ofReal ‖shiftKernel Ψ σ t (x - y) - shiftKernel Ψ σ t x‖
      ≤ ENNReal.ofReal (4 * Real.pi * B * |y| / σ) := by
  have hB : 0 ≤ B := le_trans zero_lt_one.le hseed.one_le
  have hys : |y| ≤ σ / 2 := by linarith
  have hpt := (kernel_bounds hseed).2.2.1 σ t y hσ hys
  have hInt : Integrable (fun x : ℝ => (|y| / σ) * (4 * B / σ) * (1 + ((x - t * σ) / σ) ^ 2)⁻¹) :=
    (((integrable_inv_one_add_sq.comp_div hσ.ne').comp_sub_right (t * σ)).const_mul
      ((|y| / σ) * (4 * B / σ)))
  have hnn : 0 ≤ᵐ[volume]
      (fun x : ℝ => (|y| / σ) * (4 * B / σ) * (1 + ((x - t * σ) / σ) ^ 2)⁻¹) :=
    Filter.Eventually.of_forall fun x => by positivity
  calc ∫⁻ x in {x : ℝ | 50 * L ≤ |x|},
        ENNReal.ofReal ‖shiftKernel Ψ σ t (x - y) - shiftKernel Ψ σ t x‖
      ≤ ∫⁻ x in {x : ℝ | 50 * L ≤ |x|},
          ENNReal.ofReal ((|y| / σ) * (4 * B / σ) * (1 + ((x - t * σ) / σ) ^ 2)⁻¹) :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hpt x)
    _ ≤ ∫⁻ x, ENNReal.ofReal ((|y| / σ) * (4 * B / σ) * (1 + ((x - t * σ) / σ) ^ 2)⁻¹) := by
        simpa using lintegral_mono_set (μ := volume)
          (f := fun x : ℝ => ENNReal.ofReal ((|y| / σ) * (4 * B / σ) * (1 + ((x - t * σ) / σ) ^ 2)⁻¹))
          (Set.subset_univ _)
    _ = ENNReal.ofReal (∫ x, (|y| / σ) * (4 * B / σ) * (1 + ((x - t * σ) / σ) ^ 2)⁻¹) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hnn).symm
    _ = ENNReal.ofReal ((|y| / σ) * (4 * B / σ) * (σ * Real.pi)) := by
        rw [MeasureTheory.integral_const_mul, integral_inv_one_add_sq_shift σ t hσ]
    _ = ENNReal.ofReal (4 * Real.pi * B * |y| / σ) := by
        congr 1
        field_simp

/-- **Small scales with a far centre.**  The differences of the two kernels are each bounded
by the `L¹` bound `(B.2)`, giving `2 π B` in total. -/
lemma offdiag_case_far {Ψ Ψ' : ℝ → ℝ} {B : ℝ} (hseed : IsCZSeed Ψ Ψ' B) {σ t y L : ℝ}
    (hσ : 0 < σ) (_hL : 0 < L) :
    ∫⁻ x in {x : ℝ | 50 * L ≤ |x|},
        ENNReal.ofReal ‖shiftKernel Ψ σ t (x - y) - shiftKernel Ψ σ t x‖
      ≤ ENNReal.ofReal (2 * Real.pi * B) := by
  have hB : 0 ≤ B := le_trans zero_lt_one.le hseed.one_le
  have hint : Integrable (fun x : ℝ => shiftKernel Ψ σ t x) := integrable_shiftKernel hseed hσ
  have hint' : Integrable (fun x : ℝ => shiftKernel Ψ σ t (x - y)) := hint.comp_sub_right y
  have hcont : Continuous (fun x : ℝ => shiftKernel Ψ σ t (x - y)) :=
    (continuous_shiftKernel hseed σ t).comp (by continuity)
  have hmeas : Measurable (fun x : ℝ => ENNReal.ofReal ‖shiftKernel Ψ σ t (x - y)‖) :=
    (hcont.norm.measurable).ennreal_ofReal
  have hA : ∫⁻ x in {x : ℝ | 50 * L ≤ |x|}, ENNReal.ofReal ‖shiftKernel Ψ σ t (x - y)‖
      ≤ ENNReal.ofReal (Real.pi * B) := by
    calc ∫⁻ x in {x : ℝ | 50 * L ≤ |x|}, ENNReal.ofReal ‖shiftKernel Ψ σ t (x - y)‖
        ≤ ∫⁻ x, ENNReal.ofReal ‖shiftKernel Ψ σ t (x - y)‖ := by
          simpa using lintegral_mono_set (μ := volume) (Set.subset_univ _)
      _ = ENNReal.ofReal (∫ x, ‖shiftKernel Ψ σ t (x - y)‖) :=
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint'.norm
            (Filter.Eventually.of_forall fun x => norm_nonneg _)).symm
      _ = ENNReal.ofReal (∫ x, ‖shiftKernel Ψ σ t x‖) := by
          rw [MeasureTheory.integral_sub_right_eq_self (fun x : ℝ => ‖shiftKernel Ψ σ t x‖) y]
      _ ≤ ENNReal.ofReal (Real.pi * B) :=
          ENNReal.ofReal_le_ofReal ((kernel_bounds hseed).2.1 σ t hσ)
  have hA' : ∫⁻ x in {x : ℝ | 50 * L ≤ |x|}, ENNReal.ofReal ‖shiftKernel Ψ σ t x‖
      ≤ ENNReal.ofReal (Real.pi * B) := by
    calc ∫⁻ x in {x : ℝ | 50 * L ≤ |x|}, ENNReal.ofReal ‖shiftKernel Ψ σ t x‖
        ≤ ∫⁻ x, ENNReal.ofReal ‖shiftKernel Ψ σ t x‖ := by
          simpa using lintegral_mono_set (μ := volume) (Set.subset_univ _)
      _ = ENNReal.ofReal (∫ x, ‖shiftKernel Ψ σ t x‖) :=
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint.norm
            (Filter.Eventually.of_forall fun x => norm_nonneg _)).symm
      _ ≤ ENNReal.ofReal (Real.pi * B) :=
          ENNReal.ofReal_le_ofReal ((kernel_bounds hseed).2.1 σ t hσ)
  calc ∫⁻ x in {x : ℝ | 50 * L ≤ |x|},
        ENNReal.ofReal ‖shiftKernel Ψ σ t (x - y) - shiftKernel Ψ σ t x‖
      ≤ ∫⁻ x in {x : ℝ | 50 * L ≤ |x|},
          (ENNReal.ofReal ‖shiftKernel Ψ σ t (x - y)‖ + ENNReal.ofReal ‖shiftKernel Ψ σ t x‖) := by
        refine lintegral_mono fun x => ?_
        calc ENNReal.ofReal ‖shiftKernel Ψ σ t (x - y) - shiftKernel Ψ σ t x‖
            ≤ ENNReal.ofReal (‖shiftKernel Ψ σ t (x - y)‖ + ‖shiftKernel Ψ σ t x‖) :=
              ENNReal.ofReal_le_ofReal (norm_sub_le _ _)
          _ = ENNReal.ofReal ‖shiftKernel Ψ σ t (x - y)‖ + ENNReal.ofReal ‖shiftKernel Ψ σ t x‖ :=
              ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)
    _ = (∫⁻ x in {x : ℝ | 50 * L ≤ |x|}, ENNReal.ofReal ‖shiftKernel Ψ σ t (x - y)‖)
        + ∫⁻ x in {x : ℝ | 50 * L ≤ |x|}, ENNReal.ofReal ‖shiftKernel Ψ σ t x‖ :=
        lintegral_add_left hmeas _
    _ ≤ ENNReal.ofReal (Real.pi * B) + ENNReal.ofReal (Real.pi * B) := add_le_add hA hA'
    _ = ENNReal.ofReal (2 * Real.pi * B) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- **Small scales with a near centre.**  If `|t σ| ≤ 45 L` then both kernel bumps are
centred within `45.5 L` of the origin, so at distance `≥ 4.5 L` from the region
`{50 L ≤ |x|}`; the tail integrals `bump_Ici_le`, `bump_Iic_le` give
`4 B σ / (4.5 L)` in total. -/
lemma offdiag_case_near {Ψ Ψ' : ℝ → ℝ} {B : ℝ} (hseed : IsCZSeed Ψ Ψ' B) {σ t y L : ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (hyL : |y| ≤ L / 2) (htL : |t * σ| ≤ 45 * L) :
    ∫⁻ x in {x : ℝ | 50 * L ≤ |x|},
        ENNReal.ofReal ‖shiftKernel Ψ σ t (x - y) - shiftKernel Ψ σ t x‖
      ≤ ENNReal.ofReal (4 * B * σ / (4.5 * L)) := by
  have hB : 0 ≤ B := le_trans zero_lt_one.le hseed.one_le
  have ht1 : t * σ ≤ 45 * L := le_trans (le_abs_self _) htL
  have ht2 : -(t * σ) ≤ 45 * L := le_trans (neg_le_abs _) htL
  have hy1 : y ≤ L / 2 := le_trans (le_abs_self _) hyL
  have hy2 : -y ≤ L / 2 := le_trans (neg_le_abs _) hyL
  let b : ℝ → ℝ := fun z => σ⁻¹ * B * (1 + ((z - t * σ) / σ) ^ 2)⁻¹
  have hb_int : Integrable b :=
    (((integrable_inv_one_add_sq.comp_div hσ.ne').comp_sub_right (t * σ)).const_mul (σ⁻¹ * B))
  have hb_nn : ∀ z, 0 ≤ b z := fun z => by positivity
  have hKb : ∀ z : ℝ, ‖shiftKernel Ψ σ t z‖ ≤ b z := by
    intro z
    rw [shiftKernel_norm hσ t z]
    have h1 := hseed.bound ((z - t * σ) / σ)
    rw [div_eq_mul_inv] at h1
    show σ⁻¹ * |Ψ ((z - t * σ) / σ)| ≤ σ⁻¹ * B * (1 + ((z - t * σ) / σ) ^ 2)⁻¹
    calc σ⁻¹ * |Ψ ((z - t * σ) / σ)| ≤ σ⁻¹ * (B * (1 + ((z - t * σ) / σ) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = σ⁻¹ * B * (1 + ((z - t * σ) / σ) ^ 2)⁻¹ := by ring
  have hstep1 : ∫⁻ x in {x : ℝ | 50 * L ≤ |x|},
        ENNReal.ofReal ‖shiftKernel Ψ σ t (x - y) - shiftKernel Ψ σ t x‖
      ≤ ∫⁻ x in {x : ℝ | 50 * L ≤ |x|}, ENNReal.ofReal (b (x - y) + b x) := by
    refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
    calc ‖shiftKernel Ψ σ t (x - y) - shiftKernel Ψ σ t x‖
        ≤ ‖shiftKernel Ψ σ t (x - y)‖ + ‖shiftKernel Ψ σ t x‖ := norm_sub_le _ _
      _ ≤ b (x - y) + b x := add_le_add (hKb _) (hKb _)
  have hs_eq : {x : ℝ | 50 * L ≤ |x|} = Set.Ici (50 * L) ∪ Set.Iic (-(50 * L)) := by
    ext x
    show 50 * L ≤ |x| ↔ x ∈ Set.Ici (50 * L) ∪ Set.Iic (-(50 * L))
    rw [Set.mem_union, Set.mem_Ici, Set.mem_Iic, le_abs]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by linarith)
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by linarith)
  have hdisj : Disjoint (Set.Ici (50 * L)) (Set.Iic (-(50 * L))) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    rw [Set.mem_Ici] at hx
    rw [Set.mem_Iic] at hx'
    linarith
  have hb_sh_int : Integrable (fun x : ℝ => b (x - y)) := hb_int.comp_sub_right y
  have hsum_int : Integrable (fun x : ℝ => b (x - y) + b x) := hb_sh_int.add hb_int
  have hstep2 : ∫⁻ x in {x : ℝ | 50 * L ≤ |x|}, ENNReal.ofReal (b (x - y) + b x)
      = ENNReal.ofReal ((∫ x in Set.Ici (50 * L), b (x - y)) + (∫ x in Set.Iic (-(50 * L)), b (x - y))
          + ((∫ x in Set.Ici (50 * L), b x) + (∫ x in Set.Iic (-(50 * L)), b x))) := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (μ := volume.restrict {x : ℝ | 50 * L ≤ |x|}) hsum_int.integrableOn
      (Filter.Eventually.of_forall fun x => add_nonneg (hb_nn _) (hb_nn _))]
    rw [integral_add hb_sh_int.integrableOn hb_int.integrableOn, hs_eq,
      setIntegral_union hdisj measurableSet_Iic hb_sh_int.integrableOn hb_sh_int.integrableOn,
      setIntegral_union hdisj measurableSet_Iic hb_int.integrableOn hb_int.integrableOn]
  have hbnd_ici : ∫ x in Set.Ici (50 * L), b x ≤ B * σ / (5 * L) := by
    have h1 : ∫ x in Set.Ici (50 * L), σ⁻¹ * B * (1 + ((x - t * σ) / σ) ^ 2)⁻¹
        ≤ B * σ / (50 * L - t * σ) := bump_Ici_le hσ hB (by linarith)
    refine h1.trans ?_
    exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  have hbnd_iic : ∫ x in Set.Iic (-(50 * L)), b x ≤ B * σ / (5 * L) := by
    have h1 : ∫ x in Set.Iic (-(50 * L)), σ⁻¹ * B * (1 + ((x - t * σ) / σ) ^ 2)⁻¹
        ≤ B * σ / (t * σ - (-(50 * L))) := bump_Iic_le hσ hB (by linarith)
    have h2 : B * σ / (t * σ - (-(50 * L))) = B * σ / (t * σ + 50 * L) := by ring_nf
    rw [h2] at h1
    refine h1.trans ?_
    exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  have hbnd_sici : ∫ x in Set.Ici (50 * L), b (x - y) ≤ B * σ / (4.5 * L) := by
    have h1 : ∫ x in Set.Ici (50 * L), σ⁻¹ * B * (1 + ((x - (t * σ + y)) / σ) ^ 2)⁻¹
        ≤ B * σ / (50 * L - (t * σ + y)) := bump_Ici_le hσ hB (by linarith)
    have h2 : (fun x : ℝ => σ⁻¹ * B * (1 + ((x - (t * σ + y)) / σ) ^ 2)⁻¹)
        = fun x : ℝ => b (x - y) := by
      funext x; simp only [b]; ring_nf
    rw [h2] at h1
    refine h1.trans ?_
    exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  have hbnd_siic : ∫ x in Set.Iic (-(50 * L)), b (x - y) ≤ B * σ / (4.5 * L) := by
    have h1 : ∫ x in Set.Iic (-(50 * L)), σ⁻¹ * B * (1 + ((x - (t * σ + y)) / σ) ^ 2)⁻¹
        ≤ B * σ / ((t * σ + y) - (-(50 * L))) := bump_Iic_le hσ hB (by linarith)
    have h2 : (fun x : ℝ => σ⁻¹ * B * (1 + ((x - (t * σ + y)) / σ) ^ 2)⁻¹)
        = fun x : ℝ => b (x - y) := by
      funext x; simp only [b]; ring_nf
    rw [h2] at h1
    have h3 : B * σ / ((t * σ + y) - (-(50 * L))) = B * σ / (t * σ + y + 50 * L) := by ring_nf
    rw [h3] at h1
    refine h1.trans ?_
    exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  refine hstep1.trans ?_
  rw [hstep2]
  refine ENNReal.ofReal_le_ofReal ?_
  have hZX : B * σ / (5 * L) ≤ B * σ / (4.5 * L) :=
    div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  have hfin : (∫ x in Set.Ici (50 * L), b (x - y)) + (∫ x in Set.Iic (-(50 * L)), b (x - y))
      + ((∫ x in Set.Ici (50 * L), b x) + (∫ x in Set.Iic (-(50 * L)), b x))
      ≤ 4 * (B * σ / (4.5 * L)) := by
    linarith [hbnd_ici, hbnd_iic, hbnd_sici, hbnd_siic, hZX]
  rw [show 4 * B * σ / (4.5 * L) = 4 * (B * σ / (4.5 * L)) by ring]
  exact hfin

/-! ### The lacunary summation bound -/

/-- **Summation over the three groups of scales.**  This is the numerical core of
`offdiag_le`: the three per-scale bounds `4 π B ρ / σ i`, `4 B σ i / (4.5 L)` and `2 π B`
sum, over a `lam`-lacunary family with `|t i| ≤ 2 ^ K`, to at most
`B (1 + K) ((2π+1)/(1 - lam⁻¹) + 2π (1 + log 2 / log lam))`. -/
lemma lacunary_offdiag_sum (lam ρ L B K : ℝ) (hlam : 1 < lam) (hρ : 0 < ρ)
    (hL : 0 < L) (hρL : 2 * ρ ≤ L) (hB : 0 ≤ B) (hK : 1 ≤ K) (D : Finset ι) (σ t : ι → ℝ)
    (hlac : LacunaryFam lam D σ) (ht : ∀ i ∈ D, |t i| ≤ 2 ^ K) :
    ∑ i ∈ D, (if 2 * ρ ≤ σ i then 4 * Real.pi * B * ρ / σ i
              else if |t i * σ i| ≤ 45 * L then 4 * B * σ i / (4.5 * L)
              else 2 * Real.pi * B)
      ≤ B * (1 + K) * ((2 * Real.pi + 1) / (1 - lam⁻¹)
          + 2 * Real.pi * (1 + Real.log 2 / Real.log lam)) := by
  obtain ⟨hcard, htail, hhead⟩ := lacunary_sums D σ hlam hlac
  have hloglam : 0 < Real.log lam := Real.log_pos hlam
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hκ : 0 ≤ Real.log 2 / Real.log lam := div_nonneg hlog2 hloglam.le
  have hu : 0 < 1 - lam⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hlam)
  have h2Kpos : (0 : ℝ) < 2 ^ K := Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) K
  have h2K1 : (1 : ℝ) ≤ 2 ^ K := Real.one_le_rpow (by norm_num : (1:ℝ) ≤ 2) (by linarith)
  set D2 := D.filter (fun i => σ i < 2 * ρ ∧ |t i * σ i| ≤ 45 * L) with hD2
  set D3 := D.filter (fun i => σ i < 2 * ρ ∧ 45 * L < |t i * σ i|) with hD3
  have hsplit : ∑ i ∈ D, (if 2 * ρ ≤ σ i then 4 * Real.pi * B * ρ / σ i
        else if |t i * σ i| ≤ 45 * L then 4 * B * σ i / (4.5 * L)
        else 2 * Real.pi * B)
      = (∑ i ∈ D.filter (fun i => 2 * ρ ≤ σ i), 4 * Real.pi * B * ρ / σ i)
        + (∑ i ∈ D2, 4 * B * σ i / (4.5 * L)) + (∑ i ∈ D3, 2 * Real.pi * B) := by
    rw [Finset.sum_ite]
    rw [Finset.sum_ite]
    have e2 : (D.filter (fun i => ¬ 2 * ρ ≤ σ i)).filter (fun i => |t i * σ i| ≤ 45 * L) = D2 := by
      rw [hD2, Finset.filter_filter]
      refine Finset.filter_congr fun i _ => ?_
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by rwa [not_le] at h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨by rwa [not_le], h2⟩
    have e3 : (D.filter (fun i => ¬ 2 * ρ ≤ σ i)).filter (fun i => ¬ |t i * σ i| ≤ 45 * L) = D3 := by
      rw [hD3, Finset.filter_filter]
      refine Finset.filter_congr fun i _ => ?_
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by rwa [not_le] at h1, by rwa [not_le] at h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨by rwa [not_le], by rwa [not_le]⟩
    rw [e2, e3]
    ring
  rw [hsplit]
  have hb1 : ∑ i ∈ D.filter (fun i => 2 * ρ ≤ σ i), 4 * Real.pi * B * ρ / σ i
      ≤ 2 * Real.pi * B / (1 - lam⁻¹) := by
    have ht1 := htail (2 * ρ) (by linarith)
    have hfun : ∑ i ∈ D.filter (fun i => 2 * ρ ≤ σ i), 4 * Real.pi * B * ρ / σ i
        = (2 * Real.pi * B) * ∑ i ∈ D.filter (fun i => 2 * ρ ≤ σ i), (2 * ρ) / σ i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hfun]
    calc (2 * Real.pi * B) * ∑ i ∈ D.filter (fun i => 2 * ρ ≤ σ i), (2 * ρ) / σ i
        ≤ (2 * Real.pi * B) * (1 / (1 - lam⁻¹)) :=
          mul_le_mul_of_nonneg_left ht1 (by positivity)
      _ = 2 * Real.pi * B / (1 - lam⁻¹) := by ring
  have hb2 : ∑ i ∈ D2, 4 * B * σ i / (4.5 * L) ≤ 4 * B / (4.5 * (1 - lam⁻¹)) := by
    have hfun : ∑ i ∈ D2, 4 * B * σ i / (4.5 * L) = (4 * B / (4.5 * L)) * ∑ i ∈ D2, σ i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hfun]
    have hσsum : ∑ i ∈ D2, σ i ≤ L / (1 - lam⁻¹) := by
      have hsub : D2 ⊆ D.filter (fun i => σ i < L) := by
        intro i hi
        rw [hD2, Finset.mem_filter] at hi
        rw [Finset.mem_filter]
        exact ⟨hi.1, by linarith [hi.2.1, hρL]⟩
      have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ => by
        have hσi : 0 < σ i := hlac.1 i (Finset.mem_filter.mp hi).1
        exact le_of_lt hσi)
      have hh := hhead L hL
      have hstep : ∑ i ∈ D.filter (fun i => σ i < L), σ i
          = L * ∑ i ∈ D.filter (fun i => σ i < L), σ i / L := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        exact (mul_div_cancel₀ (σ i) (ne_of_gt hL)).symm
      calc ∑ i ∈ D2, σ i ≤ ∑ i ∈ D.filter (fun i => σ i < L), σ i := hle
        _ = L * ∑ i ∈ D.filter (fun i => σ i < L), σ i / L := hstep
        _ ≤ L * (1 / (1 - lam⁻¹)) := mul_le_mul_of_nonneg_left hh hL.le
        _ = L / (1 - lam⁻¹) := by ring
    calc (4 * B / (4.5 * L)) * ∑ i ∈ D2, σ i ≤ (4 * B / (4.5 * L)) * (L / (1 - lam⁻¹)) :=
          mul_le_mul_of_nonneg_left hσsum (by positivity)
      _ = 4 * B / (4.5 * (1 - lam⁻¹)) := by field_simp
  have hb3 : ∑ i ∈ D3, 2 * Real.pi * B
      ≤ 2 * Real.pi * (B * (1 + K)) * (1 + Real.log 2 / Real.log lam) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard3 : (D3.card : ℝ) ≤ 1 + K * (Real.log 2 / Real.log lam) := by
      have hsub : D3 ⊆ D.filter (fun i => L / 2 ^ K ≤ σ i ∧ σ i < L) := by
        intro i hi
        rw [hD3, Finset.mem_filter] at hi
        obtain ⟨hiD, hσlt, htbig⟩ := hi
        have hσpos : 0 < σ i := hlac.1 i hiD
        have htle : |t i| ≤ 2 ^ K := ht i hiD
        have hprod : |t i * σ i| = |t i| * σ i := by rw [abs_mul, abs_of_pos hσpos]
        have hprod_le : |t i * σ i| ≤ 2 ^ K * σ i := by
          rw [hprod]
          exact mul_le_mul_of_nonneg_right htle hσpos.le
        have hbig : 45 * L < 2 ^ K * σ i := lt_of_lt_of_le htbig hprod_le
        rw [Finset.mem_filter]
        refine ⟨hiD, ?_, by linarith [hσlt, hρL]⟩
        rw [div_le_iff₀ h2Kpos]
        nlinarith
      have hcardle := Finset.card_le_card hsub
      have hc := hcard (L / 2 ^ K) L (by positivity) (by
        rw [div_le_iff₀ h2Kpos]; nlinarith)
      have h2K : L / (L / 2 ^ K) = 2 ^ K := by field_simp
      have hlogr : Real.log (2 ^ K) = K * Real.log 2 := Real.log_rpow (by norm_num : (0:ℝ) < 2) K
      have hcast1 : ((D.filter (fun i => L / 2 ^ K ≤ σ i ∧ σ i < L)).card : ℝ)
          ≤ 1 + Real.log (L / (L / 2 ^ K)) / Real.log lam := hc
      have hcast2 : (D3.card : ℝ)
          ≤ ((D.filter (fun i => L / 2 ^ K ≤ σ i ∧ σ i < L)).card : ℝ) := by
        exact_mod_cast hcardle
      have hres := hcast2.trans hcast1
      rw [h2K, hlogr] at hres
      rwa [show K * Real.log 2 / Real.log lam = K * (Real.log 2 / Real.log lam) by ring] at hres
    calc (D3.card : ℝ) * (2 * Real.pi * B)
        ≤ (1 + K * (Real.log 2 / Real.log lam)) * (2 * Real.pi * B) :=
          mul_le_mul_of_nonneg_right hcard3 (by positivity)
      _ ≤ 2 * Real.pi * (B * (1 + K)) * (1 + Real.log 2 / Real.log lam) := by
          have h1 : 1 + K * (Real.log 2 / Real.log lam)
              ≤ (1 + K) * (1 + Real.log 2 / Real.log lam) := by
            nlinarith [hκ, hK]
          calc (1 + K * (Real.log 2 / Real.log lam)) * (2 * Real.pi * B)
              ≤ ((1 + K) * (1 + Real.log 2 / Real.log lam)) * (2 * Real.pi * B) :=
                mul_le_mul_of_nonneg_right h1 (by positivity)
            _ = 2 * Real.pi * (B * (1 + K)) * (1 + Real.log 2 / Real.log lam) := by ring
  have hT12 : 2 * Real.pi * B / (1 - lam⁻¹) + 4 * B / (4.5 * (1 - lam⁻¹))
      ≤ B * (1 + K) * ((2 * Real.pi + 1) / (1 - lam⁻¹)) := by
    have h4 : 4 * B / (4.5 * (1 - lam⁻¹)) ≤ B / (1 - lam⁻¹) := by
      rw [div_le_div_iff₀ (by positivity) hu]
      nlinarith [hB]
    have hq : 0 ≤ (2 * Real.pi + 1) / (1 - lam⁻¹) := by positivity
    have hB2 : B ≤ B * (1 + K) := by nlinarith [hB, hK]
    have key : 2 * Real.pi * B / (1 - lam⁻¹) + B / (1 - lam⁻¹)
        ≤ B * (1 + K) * ((2 * Real.pi + 1) / (1 - lam⁻¹)) := by
      calc 2 * Real.pi * B / (1 - lam⁻¹) + B / (1 - lam⁻¹)
          = B * (2 * Real.pi + 1) / (1 - lam⁻¹) := by rw [← add_div]; ring
        _ = B * ((2 * Real.pi + 1) / (1 - lam⁻¹)) := by ring
        _ ≤ (B * (1 + K)) * ((2 * Real.pi + 1) / (1 - lam⁻¹)) :=
            mul_le_mul_of_nonneg_right hB2 hq
        _ = B * (1 + K) * ((2 * Real.pi + 1) / (1 - lam⁻¹)) := by ring
    linarith
  have hT3 : 2 * Real.pi * (B * (1 + K)) * (1 + Real.log 2 / Real.log lam)
      ≤ B * (1 + K) * (2 * Real.pi * (1 + Real.log 2 / Real.log lam)) := by
    rw [show B * (1 + K) * (2 * Real.pi * (1 + Real.log 2 / Real.log lam))
        = 2 * Real.pi * (B * (1 + K)) * (1 + Real.log 2 / Real.log lam) by ring]
  linarith [hb1, hb2, hb3, hT12, hT3]

/-! ### The off-diagonal estimate -/

/-- **Off-diagonal (Hörmander) estimate for the shifted Calderón–Zygmund kernels.**
There is a constant `C = C lam > 0` such that for every finite `lam`-lacunary family of
positive scales `σ` on `D`, every seed `Ψ` with `IsCZSeed Ψ Ψ' B`, every `K ≥ 1` with
`|t i| ≤ 2 ^ K`, every `L > 0` and every `|y| ≤ L / 2`,
`∑_{i ∈ D} ∫⁻_{50 L ≤ |x|} ‖K_i(x - y) - K_i(x)‖ ≤ C B (1 + K)`. -/
theorem offdiag_le {ι : Type*} (lam : ℝ) (hlam : 1 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : Finset ι) (σ t : ι → ℝ) (Ψ Ψ' : ℝ → ℝ) (B K : ℝ),
      LacunaryFam lam D σ → IsCZSeed Ψ Ψ' B → 1 ≤ K → (∀ i ∈ D, |t i| ≤ 2 ^ K) →
      ∀ L : ℝ, 0 < L → ∀ y : ℝ, |y| ≤ L / 2 →
        ∑ i ∈ D, ∫⁻ x in {x : ℝ | 50 * L ≤ |x|},
            ENNReal.ofReal ‖shiftKernel Ψ (σ i) (t i) (x - y) - shiftKernel Ψ (σ i) (t i) x‖
          ≤ ENNReal.ofReal (C * B * (1 + K)) := by
  set C : ℝ := (2 * Real.pi + 1) / (1 - lam⁻¹)
    + 2 * Real.pi * (1 + Real.log 2 / Real.log lam) with hC
  have hCpos : 0 < C := by
    rw [hC]
    have hu : 0 < 1 - lam⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hlam)
    have hl : 0 < Real.log lam := Real.log_pos hlam
    positivity
  refine ⟨C, hCpos, ?_⟩
  intro D σ t Ψ Ψ' B K hlac hseed hK ht L hL y hyL
  have hB : 0 ≤ B := le_trans zero_lt_one.le hseed.one_le
  rcases eq_or_ne y 0 with rfl | hy0
  · have hzero : ∀ i : ι, ∫⁻ x in {x : ℝ | 50 * L ≤ |x|},
        ENNReal.ofReal ‖shiftKernel Ψ (σ i) (t i) (x - 0) - shiftKernel Ψ (σ i) (t i) x‖ = 0 := by
      intro i
      simp
    rw [Finset.sum_eq_zero (fun i _ => hzero i)]
    exact bot_le
  · have hρpos : 0 < |y| := abs_pos.mpr hy0
    have hρL : 2 * |y| ≤ L := by linarith [abs_nonneg y, hyL]
    have hper : ∀ i ∈ D, (∫⁻ x in {x : ℝ | 50 * L ≤ |x|},
          ENNReal.ofReal ‖shiftKernel Ψ (σ i) (t i) (x - y) - shiftKernel Ψ (σ i) (t i) x‖)
        ≤ ENNReal.ofReal (if 2 * |y| ≤ σ i then 4 * Real.pi * B * |y| / σ i
            else if |t i * σ i| ≤ 45 * L then 4 * B * σ i / (4.5 * L)
            else 2 * Real.pi * B) := by
      intro i hi
      have hσi : 0 < σ i := hlac.1 i hi
      by_cases h1 : 2 * |y| ≤ σ i
      · rw [if_pos h1]
        exact offdiag_case_large hseed hσi h1 hL
      · rw [if_neg h1]
        by_cases h2 : |t i * σ i| ≤ 45 * L
        · rw [if_pos h2]
          exact offdiag_case_near hseed hσi hL hyL h2
        · rw [if_neg h2]
          exact offdiag_case_far hseed hσi hL
    have hnn : ∀ i ∈ D, 0 ≤ (if 2 * |y| ≤ σ i then 4 * Real.pi * B * |y| / σ i
        else if |t i * σ i| ≤ 45 * L then 4 * B * σ i / (4.5 * L)
        else 2 * Real.pi * B) := by
      intro i hi
      have hσi : 0 < σ i := hlac.1 i hi
      by_cases h1 : 2 * |y| ≤ σ i
      · rw [if_pos h1]; positivity
      · rw [if_neg h1]
        by_cases h2 : |t i * σ i| ≤ 45 * L
        · rw [if_pos h2]; positivity
        · rw [if_neg h2]; positivity
    calc ∑ i ∈ D, ∫⁻ x in {x : ℝ | 50 * L ≤ |x|},
            ENNReal.ofReal ‖shiftKernel Ψ (σ i) (t i) (x - y) - shiftKernel Ψ (σ i) (t i) x‖
        ≤ ∑ i ∈ D, ENNReal.ofReal (if 2 * |y| ≤ σ i then 4 * Real.pi * B * |y| / σ i
            else if |t i * σ i| ≤ 45 * L then 4 * B * σ i / (4.5 * L)
            else 2 * Real.pi * B) := Finset.sum_le_sum hper
      _ = ENNReal.ofReal (∑ i ∈ D, (if 2 * |y| ≤ σ i then 4 * Real.pi * B * |y| / σ i
            else if |t i * σ i| ≤ 45 * L then 4 * B * σ i / (4.5 * L)
            else 2 * Real.pi * B)) := (ENNReal.ofReal_sum_of_nonneg hnn).symm
      _ ≤ ENNReal.ofReal (C * B * (1 + K)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hsum := lacunary_offdiag_sum lam |y| L B K hlam hρpos hL hρL hB hK D σ t hlac ht
          have hCv : C = (2 * Real.pi + 1) / (1 - lam⁻¹)
              + 2 * Real.pi * (1 + Real.log 2 / Real.log lam) := hC
          have hprod : B * (1 + K) * ((2 * Real.pi + 1) / (1 - lam⁻¹)
                + 2 * Real.pi * (1 + Real.log 2 / Real.log lam)) = C * B * (1 + K) := by
            rw [hCv]; ring
          rw [hprod] at hsum
          exact hsum

end Work.Analysis.CzShift
