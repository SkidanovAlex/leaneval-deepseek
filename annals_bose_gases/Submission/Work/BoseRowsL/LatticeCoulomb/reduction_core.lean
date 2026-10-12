import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Submission.Work.BoseRowsL.LatticeCoulomb.integrable_cosCosBall_prod
import Submission.Work.BoseRowsL.LatticeCoulomb.sum_chat_double
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.LatticeCoulomb.reduction_core`

The **operator-norm core** of the lattice-vs-continuum Coulomb comparison.

The target compares the finite lattice sum `Σ_{n∈T} Ŵ₁(kₙ)Ŵ₂(kₙ)/(2‖kₙ‖²)` with the ball
integral `ℓ³(2π)⁻³∫_{‖p‖≤K} Ŵ₁(p)Ŵ₂(p)/(2‖p‖²)`, `kₙ = ℓ⁻¹ • vec n`, and concludes that the
*matched* difference is bounded by `M‖f₁‖₁‖f₂‖₁`, where `M` is a sup bound for the **kernel**

  `kcal T ℓ K w = Σ_{n∈T} cos⟪kₙ,w⟫/(2‖kₙ‖²) − ℓ³(2π)⁻³∫_{‖p‖≤K} cos⟪p,w⟫/(2‖p‖²)`

on the ball of radius `2r`, the functions `fᵢ` being supported in the ball of radius `r`.

The proof is the standard "expand the two Fourier transforms" argument:

* the lattice side is a double integral of `f₁(x)f₂(y) cos⟪kₙ,x⟫cos⟪kₙ,y⟫/(2‖kₙ‖²)`
  (`sum_chat_double`), and likewise the continuum side with `cosCosBall K x y`
  (`ball_chat_double_self`, `integrable_cosCosBall_prod`);
* subtracting gives the double integral of `f₁(x)f₂(y)·kernel2 x y` with
  `kernel2 x y = cosCosSum T ℓ x y − ℓ³(2π)⁻³·cosCosBall K x y`;
* the product-to-sum identity `cos a cos b = (cos(a+b) + cos(a−b))/2` identifies the kernel:
  `kernel2 x y = ½(kcal (x+y) + kcal (x−y))` (`kernel2_eq_half_kcal`);
* since `‖x ± y‖ ≤ ‖x‖ + ‖y‖ ≤ 2r` on the supports, `|kernel2 x y| ≤ M` there, and the double
  integral is bounded by `M‖f₁‖₁‖f₂‖₁`.

Nothing but `L¹`-integrability, the support condition and the sup bound on the kernel is used:
no positivity of `fᵢ`, no positivity of `ℓ`, `K`, `r` and no decay of the summand.
-/

noncomputable section

open MeasureTheory Metric
open scoped Real BigOperators Topology

namespace Work.BoseRowsL.LatticeCoulomb

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Elementary scalar facts about the cos-cosine kernel -/

/-- `(1/2)(cos(a+b)/d + cos(a-b)/d) = cos a cos b / d`: the product-to-sum identity in the
normalised form used by `kernel2_eq_half_kcal`. -/
theorem half_cos_add_sub_div (a b d : ℝ) :
    (1 / 2) * (Real.cos (a + b) / d + Real.cos (a - b) / d) = Real.cos a * Real.cos b / d := by
  rw [cos_mul_cos]
  ring

/-- `|x y / c| ≤ c⁻¹` when `|x| ≤ 1`, `|y| ≤ 1`, `0 ≤ c`. -/
theorem abs_mul_mul_inv_le {x y c : ℝ} (hc : 0 ≤ c) (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    |x * y / c| ≤ c⁻¹ := by
  rw [abs_div, abs_mul, abs_of_nonneg hc, div_eq_mul_inv]
  have hxy : |x| * |y| ≤ 1 := by
    calc |x| * |y| ≤ 1 * |y| := mul_le_mul_of_nonneg_right hx (abs_nonneg y)
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hy (by norm_num)
      _ = 1 := by ring
  calc |x| * |y| * c⁻¹ ≤ 1 * c⁻¹ := mul_le_mul_of_nonneg_right hxy (inv_nonneg.mpr hc)
    _ = c⁻¹ := by ring

/-- The lattice-side kernel `cosCosSum` is bounded by the sum of the weights — in particular it
is bounded (the sum being finite), which is what makes the double integral of the lattice side
absolutely convergent. -/
theorem abs_cosCosSum_le (T : Finset (Fin 3 → ℤ)) (ℓ : ℝ) (x y : E3) :
    |cosCosSum T ℓ x y| ≤ ∑ n ∈ T, (2 * ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ^ 2)⁻¹ := by
  rw [cosCosSum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun n _ => ?_))
  exact abs_mul_mul_inv_le (by positivity) (Real.abs_cos_le_one _) (Real.abs_cos_le_one _)

/-- The product integrand of the lattice side is integrable on `E3 × E3`. -/
theorem integrable_cosCosSum_prod (T : Finset (Fin 3 → ℤ)) (ℓ : ℝ) {f₁ f₂ : E3 → ℝ}
    (hf1 : MeasureTheory.Integrable f₁) (hf2 : MeasureTheory.Integrable f₂) :
    MeasureTheory.Integrable
      (fun z : E3 × E3 => f₁ z.1 * f₂ z.2 * cosCosSum T ℓ z.1 z.2)
      ((volume : Measure E3).prod (volume : Measure E3)) := by
  have hF : MeasureTheory.Integrable (fun z : E3 × E3 => f₁ z.1 * f₂ z.2)
      ((volume : Measure E3).prod (volume : Measure E3)) :=
    MeasureTheory.Integrable.mul_prod hf1 hf2
  refine hF.mul_bdd (c := ∑ n ∈ T, (2 * ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ^ 2)⁻¹) ?_ ?_
  · have hcont : Continuous (fun z : E3 × E3 => cosCosSum T ℓ z.1 z.2) := by
      rw [show (fun z : E3 × E3 => cosCosSum T ℓ z.1 z.2)
          = (fun z : E3 × E3 => ∑ n ∈ T,
              Real.cos (inner ℝ (ℓ⁻¹ • Work.BoseB4.vec n) z.1)
                * Real.cos (inner ℝ (ℓ⁻¹ • Work.BoseB4.vec n) z.2)
                / (2 * ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ^ 2)) from rfl]
      refine continuous_finsetSum _ (fun n _ => ?_)
      exact ((Real.continuous_cos.comp
          (continuous_const.inner continuous_fst)).mul
        (Real.continuous_cos.comp (continuous_const.inner continuous_snd))).div_const _
    exact hcont.aestronglyMeasurable
  · filter_upwards with z
    rw [Real.norm_eq_abs]
    exact abs_cosCosSum_le T ℓ z.1 z.2

/-- **The kernel identity.**  The matched difference of the two sides is the symmetrised
`kcal`:

`cosCosSum T ℓ x y − ℓ³(2π)⁻³·cosCosBall K x y = ½(kcal T ℓ K (x+y) + kcal T ℓ K (x−y))`.

This is the product-to-sum identity `cos a cos b = (cos(a+b) + cos(a−b))/2` applied to the
`n`-summand and to the `p`-integrand. -/
theorem kernel2_eq_half_kcal (T : Finset (Fin 3 → ℤ)) (ℓ K : ℝ) (x y : E3) :
    kernel2 T ℓ K x y = (1 / 2) * (kcal T ℓ K (x + y) + kcal T ℓ K (x - y)) := by
  have hInt : ∀ w : E3, MeasureTheory.Integrable
      (fun p : E3 => (1 / 2) * (Real.cos (inner ℝ p w) / (2 * ‖p‖ ^ 2)))
      (volume.restrict (Metric.closedBall 0 K)) := by
    intro w
    have h1 : MeasureTheory.Integrable (fun p : E3 => (2 * ‖p‖ ^ 2)⁻¹)
        (volume.restrict (Metric.closedBall 0 K)) := integrableOn_inv_norm_sq K
    refine (h1.bdd_mul (f := fun p : E3 => (1 / 2) * Real.cos (inner ℝ p w))
      (c := 1 / 2) ?_ ?_).congr (Filter.Eventually.of_forall (fun p => by ring))
    · fun_prop
    · filter_upwards with p
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      calc (1 / 2) * |Real.cos (inner ℝ p w)| ≤ (1 / 2) * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by norm_num)
        _ = 1 / 2 := by ring
  rw [kernel2, kcal, kcal]
  set c1 : ℝ := ℓ ^ 3 * ((2 * Real.pi) ^ 3)⁻¹ with hc1
  set S1 : ℝ := ∑ n ∈ T, Real.cos (inner ℝ (ℓ⁻¹ • Work.BoseB4.vec n) (x + y))
        / (2 * ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ^ 2) with hS1
  set S2 : ℝ := ∑ n ∈ T, Real.cos (inner ℝ (ℓ⁻¹ • Work.BoseB4.vec n) (x - y))
        / (2 * ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ^ 2) with hS2
  set J1 : ℝ := ∫ p in Metric.closedBall 0 K,
        Real.cos (inner ℝ p (x + y)) / (2 * ‖p‖ ^ 2) with hJ1
  set J2 : ℝ := ∫ p in Metric.closedBall 0 K,
        Real.cos (inner ℝ p (x - y)) / (2 * ‖p‖ ^ 2) with hJ2
  have hsum : (1 / 2) * (S1 + S2) = cosCosSum T ℓ x y := by
    rw [hS1, hS2, cosCosSum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [inner_add_right, inner_sub_right]
    exact half_cos_add_sub_div _ _ _
  have hint : (1 / 2) * (J1 + J2) = cosCosBall K x y := by
    rw [hJ1, hJ2, cosCosBall, mul_add]
    have h1 : (1 / 2) * (∫ p in Metric.closedBall 0 K,
          Real.cos (inner ℝ p (x + y)) / (2 * ‖p‖ ^ 2))
        = ∫ p in Metric.closedBall 0 K,
            (1 / 2) * (Real.cos (inner ℝ p (x + y)) / (2 * ‖p‖ ^ 2)) :=
      (integral_const_mul (1 / 2) _).symm
    have h2 : (1 / 2) * (∫ p in Metric.closedBall 0 K,
          Real.cos (inner ℝ p (x - y)) / (2 * ‖p‖ ^ 2))
        = ∫ p in Metric.closedBall 0 K,
            (1 / 2) * (Real.cos (inner ℝ p (x - y)) / (2 * ‖p‖ ^ 2)) :=
      (integral_const_mul (1 / 2) _).symm
    have h3 : (∫ p in Metric.closedBall 0 K,
            (1 / 2) * (Real.cos (inner ℝ p (x + y)) / (2 * ‖p‖ ^ 2)))
          + (∫ p in Metric.closedBall 0 K,
            (1 / 2) * (Real.cos (inner ℝ p (x - y)) / (2 * ‖p‖ ^ 2)))
        = ∫ p in Metric.closedBall 0 K,
            ((1 / 2) * (Real.cos (inner ℝ p (x + y)) / (2 * ‖p‖ ^ 2))
              + (1 / 2) * (Real.cos (inner ℝ p (x - y)) / (2 * ‖p‖ ^ 2))) :=
      (integral_add (hInt (x + y)) (hInt (x - y))).symm
    have h4 : (∫ p in Metric.closedBall 0 K,
            ((1 / 2) * (Real.cos (inner ℝ p (x + y)) / (2 * ‖p‖ ^ 2))
              + (1 / 2) * (Real.cos (inner ℝ p (x - y)) / (2 * ‖p‖ ^ 2))))
        = ∫ p in Metric.closedBall 0 K,
            Real.cos (inner ℝ p x) * Real.cos (inner ℝ p y) / (2 * ‖p‖ ^ 2) := by
      refine setIntegral_congr_fun measurableSet_closedBall (fun p _ => ?_)
      rw [inner_add_right, inner_sub_right, cos_mul_cos]
      ring
    rw [h1, h2, h3, h4]
  have hint'' : (1 / 2) * (c1 * J1 + c1 * J2) = c1 * cosCosBall K x y := by
    rw [show c1 * J1 + c1 * J2 = c1 * (J1 + J2) by ring,
      show (1 / 2) * (c1 * (J1 + J2)) = c1 * ((1 / 2) * (J1 + J2)) by ring, hint]
  have hlin : (1 / 2) * ((S1 - c1 * J1) + (S2 - c1 * J2))
      = (1 / 2) * (S1 + S2) - (1 / 2) * (c1 * J1 + c1 * J2) := by ring
  rw [hlin, hsum, hint'']

theorem ball_chat_double_self (K : ℝ) {f₁ f₂ : E3 → ℝ}
    (hf1 : MeasureTheory.Integrable f₁) (hf2 : MeasureTheory.Integrable f₂) :
    ∫ p in Metric.closedBall 0 K,
        Work.BoseFixR.chat f₁ p * Work.BoseFixR.chat f₂ p / (2 * ‖p‖ ^ 2)
      = ∫ x, ∫ y, f₁ x * f₂ y * cosCosBall K x y := by
  -- ## the joint integrand is integrable on `μp × (volume × volume)`
  have hκm : Measurable (fun p : E3 => (2 * ‖p‖ ^ 2)⁻¹) :=
    Measurable.inv (by fun_prop)
  have hJ : MeasureTheory.Integrable
      (fun w : E3 × (E3 × E3) =>
        (f₁ w.2.1 * Real.cos (inner ℝ w.1 w.2.1)) *
            (f₂ w.2.2 * Real.cos (inner ℝ w.1 w.2.2)) / (2 * ‖w.1‖ ^ 2))
      ((volume.restrict (Metric.closedBall 0 K)).prod
        ((volume : Measure E3).prod (volume : Measure E3))) := by
    have hκ : MeasureTheory.Integrable (fun p : E3 => |(2 * ‖p‖ ^ 2)⁻¹|)
        (volume.restrict (Metric.closedBall 0 K)) := (integrableOn_inv_norm_sq K).abs
    have hFz : MeasureTheory.Integrable (fun z : E3 × E3 => |f₁ z.1| * |f₂ z.2|)
        ((volume : Measure E3).prod (volume : Measure E3)) :=
      MeasureTheory.Integrable.mul_prod hf1.norm hf2.norm
    have hGb : MeasureTheory.Integrable
        (fun w : E3 × (E3 × E3) => |(2 * ‖w.1‖ ^ 2)⁻¹| * (|f₁ w.2.1| * |f₂ w.2.2|))
        ((volume.restrict (Metric.closedBall 0 K)).prod
          ((volume : Measure E3).prod (volume : Measure E3))) := hκ.mul_prod hFz
    refine MeasureTheory.Integrable.mono' hGb ?_ ?_
    · -- measurability
      have h1 : AEMeasurable (fun w : E3 × (E3 × E3) => f₁ w.2.1)
          ((volume.restrict (Metric.closedBall 0 K)).prod
            ((volume : Measure E3).prod (volume : Measure E3))) :=
        ((hf1.aemeasurable.comp_fst (ν := (volume : Measure E3))).comp_snd
          (μ := volume.restrict (Metric.closedBall 0 K)))
      have h2 : AEMeasurable (fun w : E3 × (E3 × E3) => f₂ w.2.2)
          ((volume.restrict (Metric.closedBall 0 K)).prod
            ((volume : Measure E3).prod (volume : Measure E3))) :=
        ((hf2.aemeasurable.comp_snd (μ := (volume : Measure E3))
            (ν := (volume : Measure E3))).comp_snd
          (μ := volume.restrict (Metric.closedBall 0 K)))
      have h3 : AEMeasurable
          (fun w : E3 × (E3 × E3) => Real.cos (inner ℝ w.1 w.2.1))
          ((volume.restrict (Metric.closedBall 0 K)).prod
            ((volume : Measure E3).prod (volume : Measure E3))) :=
        (by fun_prop : Continuous
          (fun w : E3 × (E3 × E3) => Real.cos (inner ℝ w.1 w.2.1))).aemeasurable
      have h4 : AEMeasurable
          (fun w : E3 × (E3 × E3) => Real.cos (inner ℝ w.1 w.2.2))
          ((volume.restrict (Metric.closedBall 0 K)).prod
            ((volume : Measure E3).prod (volume : Measure E3))) :=
        (by fun_prop : Continuous
          (fun w : E3 × (E3 × E3) => Real.cos (inner ℝ w.1 w.2.2))).aemeasurable
      have h5 : AEMeasurable (fun w : E3 × (E3 × E3) => (2 * ‖w.1‖ ^ 2)⁻¹)
          ((volume.restrict (Metric.closedBall 0 K)).prod
            ((volume : Measure E3).prod (volume : Measure E3))) :=
        ((hκm.comp measurable_fst)).aemeasurable
      exact (((h1.mul h3).mul (h2.mul h4)).mul h5).aestronglyMeasurable
    · filter_upwards with w
      have hp : (0 : ℝ) ≤ 2 * ‖w.1‖ ^ 2 := by positivity
      rw [Real.norm_eq_abs]
      simp only [abs_div, abs_mul, abs_of_nonneg hp, abs_of_nonneg (inv_nonneg.mpr hp)]
      have key : |f₁ w.2.1| * |Real.cos (inner ℝ w.1 w.2.1)| *
            (|f₂ w.2.2| * |Real.cos (inner ℝ w.1 w.2.2)|) ≤ |f₁ w.2.1| * |f₂ w.2.2| := by
        calc |f₁ w.2.1| * |Real.cos (inner ℝ w.1 w.2.1)| *
              (|f₂ w.2.2| * |Real.cos (inner ℝ w.1 w.2.2)|)
            ≤ |f₁ w.2.1| * 1 * (|f₂ w.2.2| * 1) := by
              gcongr
              · exact Real.abs_cos_le_one _
              · exact Real.abs_cos_le_one _
          _ = |f₁ w.2.1| * |f₂ w.2.2| := by ring
      calc |f₁ w.2.1| * |Real.cos (inner ℝ w.1 w.2.1)| *
            (|f₂ w.2.2| * |Real.cos (inner ℝ w.1 w.2.2)|) * (2 * ‖w.1‖ ^ 2)⁻¹
          ≤ (|f₁ w.2.1| * |f₂ w.2.2|) * (2 * ‖w.1‖ ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right key (inv_nonneg.mpr hp)
        _ = (2 * ‖w.1‖ ^ 2)⁻¹ * (|f₁ w.2.1| * |f₂ w.2.2|) := by ring
  -- ## the joint integrand, transposed
  have hJ' : MeasureTheory.Integrable
      (fun w : (E3 × E3) × E3 =>
        (f₁ w.1.1 * Real.cos (inner ℝ w.2 w.1.1)) *
            (f₂ w.1.2 * Real.cos (inner ℝ w.2 w.1.2)) / (2 * ‖w.2‖ ^ 2))
      (((volume : Measure E3).prod (volume : Measure E3)).prod
        (volume.restrict (Metric.closedBall 0 K))) := hJ.swap
  have hInt : MeasureTheory.Integrable
      (fun z : E3 × E3 => ∫ p, (f₁ z.1 * Real.cos (inner ℝ p z.1)) *
            (f₂ z.2 * Real.cos (inner ℝ p z.2)) / (2 * ‖p‖ ^ 2)
          ∂(volume.restrict (Metric.closedBall 0 K)))
      ((volume : Measure E3).prod (volume : Measure E3)) := hJ'.integral_prod_left
  -- ## step A: expand the two `chat` factors at fixed `p`
  have hA : ∀ p : E3, Work.BoseFixR.chat f₁ p * Work.BoseFixR.chat f₂ p / (2 * ‖p‖ ^ 2)
      = ∫ z : E3 × E3, (f₁ z.1 * Real.cos (inner ℝ p z.1)) *
          (f₂ z.2 * Real.cos (inner ℝ p z.2)) / (2 * ‖p‖ ^ 2)
          ∂((volume : Measure E3).prod (volume : Measure E3)) := by
    intro p
    rw [chat_eq_integral_cos hf1 p, chat_eq_integral_cos hf2 p, div_eq_mul_inv]
    rw [← MeasureTheory.integral_prod_mul (f := fun x : E3 => f₁ x * Real.cos (inner ℝ p x))
      (g := fun y : E3 => f₂ y * Real.cos (inner ℝ p y))]
    rw [← MeasureTheory.integral_mul_const]
    rfl
  -- ## the swap and the iterated form
  have hC : (∫ p, (∫ z : E3 × E3, (f₁ z.1 * Real.cos (inner ℝ p z.1)) *
            (f₂ z.2 * Real.cos (inner ℝ p z.2)) / (2 * ‖p‖ ^ 2)
            ∂((volume : Measure E3).prod (volume : Measure E3)))
          ∂(volume.restrict (Metric.closedBall 0 K)))
      = ∫ z : E3 × E3, (∫ p, (f₁ z.1 * Real.cos (inner ℝ p z.1)) *
            (f₂ z.2 * Real.cos (inner ℝ p z.2)) / (2 * ‖p‖ ^ 2)
              ∂(volume.restrict (Metric.closedBall 0 K)))
          ∂((volume : Measure E3).prod (volume : Measure E3)) :=
    MeasureTheory.integral_integral_swap hJ
  have hD : (∫ z : E3 × E3, (∫ p, (f₁ z.1 * Real.cos (inner ℝ p z.1)) *
            (f₂ z.2 * Real.cos (inner ℝ p z.2)) / (2 * ‖p‖ ^ 2)
              ∂(volume.restrict (Metric.closedBall 0 K)))
          ∂((volume : Measure E3).prod (volume : Measure E3)))
      = ∫ x, ∫ y, (∫ p, (f₁ x * Real.cos (inner ℝ p x)) *
            (f₂ y * Real.cos (inner ℝ p y)) / (2 * ‖p‖ ^ 2)
              ∂(volume.restrict (Metric.closedBall 0 K))) ∂volume ∂volume :=
    MeasureTheory.integral_prod _ hInt
  -- ## step E: the inner integral
  have hE : ∀ x y : E3, (∫ p, (f₁ x * Real.cos (inner ℝ p x)) *
            (f₂ y * Real.cos (inner ℝ p y)) / (2 * ‖p‖ ^ 2)
              ∂(volume.restrict (Metric.closedBall 0 K)))
      = f₁ x * f₂ y * cosCosBall K x y := by
    intro x y
    rw [cosCosBall]
    rw [show (∫ p, (f₁ x * Real.cos (inner ℝ p x)) * (f₂ y * Real.cos (inner ℝ p y))
            / (2 * ‖p‖ ^ 2) ∂(volume.restrict (Metric.closedBall 0 K)))
          = ∫ p, (f₁ x * f₂ y) * (Real.cos (inner ℝ p x) * Real.cos (inner ℝ p y)
              / (2 * ‖p‖ ^ 2)) ∂(volume.restrict (Metric.closedBall 0 K)) from
        integral_congr_ae (Filter.Eventually.of_forall (fun p => by ring))]
    rw [MeasureTheory.integral_const_mul]
  have hstep1 : (∫ p in Metric.closedBall 0 K,
        Work.BoseFixR.chat f₁ p * Work.BoseFixR.chat f₂ p / (2 * ‖p‖ ^ 2))
      = ∫ p, (∫ z : E3 × E3, (f₁ z.1 * Real.cos (inner ℝ p z.1)) *
            (f₂ z.2 * Real.cos (inner ℝ p z.2)) / (2 * ‖p‖ ^ 2)
            ∂((volume : Measure E3).prod (volume : Measure E3)))
          ∂(volume.restrict (Metric.closedBall 0 K)) :=
      integral_congr_ae (Filter.Eventually.of_forall (fun p => hA p))
  have hstep3 : (∫ x, ∫ y, (∫ p, (f₁ x * Real.cos (inner ℝ p x)) *
            (f₂ y * Real.cos (inner ℝ p y)) / (2 * ‖p‖ ^ 2)
              ∂(volume.restrict (Metric.closedBall 0 K))) ∂volume ∂volume)
      = ∫ x, ∫ y, f₁ x * f₂ y * cosCosBall K x y :=
      integral_congr_ae (Filter.Eventually.of_forall (fun x =>
        integral_congr_ae (Filter.Eventually.of_forall (fun y => hE x y))))
  exact hstep1.trans (hC.trans (hD.trans hstep3))

/-! ## The target -/

theorem reduction_core (T : Finset (Fin 3 → ℤ)) (ℓ K r M : ℝ) (f₁ f₂ : E3 → ℝ)
    (hM : 0 ≤ M)
    (hker : ∀ w : E3, ‖w‖ ≤ 2 * r → |kcal T ℓ K w| ≤ M)
    (hf1 : MeasureTheory.Integrable f₁) (hf2 : MeasureTheory.Integrable f₂)
    (hs1 : Function.support f₁ ⊆ Metric.closedBall 0 r)
    (hs2 : Function.support f₂ ⊆ Metric.closedBall 0 r) :
    |(∑ n ∈ T, Work.BoseFixR.chat f₁ (ℓ⁻¹ • Work.BoseB4.vec n)
        * Work.BoseFixR.chat f₂ (ℓ⁻¹ • Work.BoseB4.vec n)
        / (2 * ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ^ 2))
      - ℓ ^ 3 * ((2 * Real.pi) ^ 3)⁻¹ *
          ∫ p in Metric.closedBall 0 K,
            Work.BoseFixR.chat f₁ p * Work.BoseFixR.chat f₂ p / (2 * ‖p‖ ^ 2)|
      ≤ M * (∫ x, |f₁ x|) * (∫ x, |f₂ x|) := by
  -- ## the two halves of the comparison, as product-measure integrals
  have hS : (∑ n ∈ T, Work.BoseFixR.chat f₁ (ℓ⁻¹ • Work.BoseB4.vec n)
        * Work.BoseFixR.chat f₂ (ℓ⁻¹ • Work.BoseB4.vec n)
        / (2 * ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ^ 2))
      = ∫ z : E3 × E3, f₁ z.1 * f₂ z.2 * cosCosSum T ℓ z.1 z.2
          ∂((volume : Measure E3).prod (volume : Measure E3)) := by
    rw [sum_chat_double T ℓ hf1 hf2]
    exact integral_integral (integrable_cosCosSum_prod T ℓ hf1 hf2)
  have hI : (∫ p in Metric.closedBall 0 K,
        Work.BoseFixR.chat f₁ p * Work.BoseFixR.chat f₂ p / (2 * ‖p‖ ^ 2))
      = ∫ z : E3 × E3, f₁ z.1 * f₂ z.2 * cosCosBall K z.1 z.2
          ∂((volume : Measure E3).prod (volume : Measure E3)) := by
    rw [ball_chat_double_self K hf1 hf2]
    exact integral_integral (integrable_cosCosBall_prod K hf1 hf2)
  have hIc : (ℓ ^ 3 * ((2 * Real.pi) ^ 3)⁻¹) *
        (∫ p in Metric.closedBall 0 K,
          Work.BoseFixR.chat f₁ p * Work.BoseFixR.chat f₂ p / (2 * ‖p‖ ^ 2))
      = ∫ z : E3 × E3,
          (ℓ ^ 3 * ((2 * Real.pi) ^ 3)⁻¹) * (f₁ z.1 * f₂ z.2 * cosCosBall K z.1 z.2)
          ∂((volume : Measure E3).prod (volume : Measure E3)) := by
    rw [hI, ← integral_const_mul]
  -- ## the difference is the double integral of the kernel
  have hkey : (∑ n ∈ T, Work.BoseFixR.chat f₁ (ℓ⁻¹ • Work.BoseB4.vec n)
        * Work.BoseFixR.chat f₂ (ℓ⁻¹ • Work.BoseB4.vec n)
        / (2 * ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ^ 2))
      - ℓ ^ 3 * ((2 * Real.pi) ^ 3)⁻¹ *
          ∫ p in Metric.closedBall 0 K,
            Work.BoseFixR.chat f₁ p * Work.BoseFixR.chat f₂ p / (2 * ‖p‖ ^ 2)
      = ∫ z : E3 × E3, f₁ z.1 * f₂ z.2 * kernel2 T ℓ K z.1 z.2
          ∂((volume : Measure E3).prod (volume : Measure E3)) := by
    rw [hS, hIc]
    rw [← integral_sub (integrable_cosCosSum_prod T ℓ hf1 hf2)
      ((integrable_cosCosBall_prod K hf1 hf2).const_mul (ℓ ^ 3 * ((2 * Real.pi) ^ 3)⁻¹))]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    simp only [kernel2]
    ring
  rw [hkey]
  -- ## the kernel bound
  have hG : MeasureTheory.Integrable
      (fun z : E3 × E3 => M * (|f₁ z.1| * |f₂ z.2|))
      ((volume : Measure E3).prod (volume : Measure E3)) :=
    (MeasureTheory.Integrable.mul_prod hf1.norm hf2.norm).const_mul M
  have hpt : ∀ z : E3 × E3,
      ‖f₁ z.1 * f₂ z.2 * kernel2 T ℓ K z.1 z.2‖ ≤ M * (|f₁ z.1| * |f₂ z.2|) := by
    intro z
    rw [Real.norm_eq_abs]
    rcases eq_or_ne (f₁ z.1) 0 with hz | hz
    · rw [show f₁ z.1 * f₂ z.2 * kernel2 T ℓ K z.1 z.2 = 0 by rw [hz, zero_mul, zero_mul],
        abs_zero]
      exact mul_nonneg hM (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    rcases eq_or_ne (f₂ z.2) 0 with hz2 | hz2
    · rw [show f₁ z.1 * f₂ z.2 * kernel2 T ℓ K z.1 z.2 = 0 by rw [hz2, mul_zero, zero_mul],
        abs_zero]
      exact mul_nonneg hM (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hx : ‖z.1‖ ≤ r := by
      have h := hs1 (Function.mem_support.mpr hz)
      rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
    have hy : ‖z.2‖ ≤ r := by
      have h := hs2 (Function.mem_support.mpr hz2)
      rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
    have hb1 : ‖z.1 + z.2‖ ≤ 2 * r := by
      calc ‖z.1 + z.2‖ ≤ ‖z.1‖ + ‖z.2‖ := norm_add_le _ _
        _ ≤ 2 * r := by linarith
    have hb2 : ‖z.1 - z.2‖ ≤ 2 * r := by
      calc ‖z.1 - z.2‖ ≤ ‖z.1‖ + ‖z.2‖ := norm_sub_le _ _
        _ ≤ 2 * r := by linarith
    have hk : |kernel2 T ℓ K z.1 z.2| ≤ M := by
      rw [kernel2_eq_half_kcal]
      have h1 := hker (z.1 + z.2) hb1
      have h2 := hker (z.1 - z.2) hb2
      calc |(1 / 2) * (kcal T ℓ K (z.1 + z.2) + kcal T ℓ K (z.1 - z.2))|
          = (1 / 2) * |kcal T ℓ K (z.1 + z.2) + kcal T ℓ K (z.1 - z.2)| := by
            rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        _ ≤ (1 / 2) * (|kcal T ℓ K (z.1 + z.2)| + |kcal T ℓ K (z.1 - z.2)|) := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            simpa only [Real.norm_eq_abs] using
              norm_add_le (kcal T ℓ K (z.1 + z.2)) (kcal T ℓ K (z.1 - z.2))
        _ ≤ (1 / 2) * (M + M) := mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
        _ = M := by ring
    rw [abs_mul, abs_mul]
    calc |f₁ z.1| * |f₂ z.2| * |kernel2 T ℓ K z.1 z.2|
        ≤ |f₁ z.1| * |f₂ z.2| * M := mul_le_mul_of_nonneg_left hk (by positivity)
      _ = M * (|f₁ z.1| * |f₂ z.2|) := by ring
  calc |∫ z : E3 × E3, f₁ z.1 * f₂ z.2 * kernel2 T ℓ K z.1 z.2
        ∂((volume : Measure E3).prod (volume : Measure E3))|
      = ‖∫ z : E3 × E3, f₁ z.1 * f₂ z.2 * kernel2 T ℓ K z.1 z.2
          ∂((volume : Measure E3).prod (volume : Measure E3))‖ := by
        rw [Real.norm_eq_abs]
    _ ≤ ∫ z : E3 × E3, ‖f₁ z.1 * f₂ z.2 * kernel2 T ℓ K z.1 z.2‖
          ∂((volume : Measure E3).prod (volume : Measure E3)) :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ z : E3 × E3, M * (|f₁ z.1| * |f₂ z.2|)
          ∂((volume : Measure E3).prod (volume : Measure E3)) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z => norm_nonneg _)) hG
          (Filter.Eventually.of_forall hpt)
    _ = M * (∫ x, |f₁ x|) * (∫ x, |f₂ x|) := by
        rw [integral_const_mul,
          integral_prod_mul (f := fun x : E3 => |f₁ x|) (g := fun y : E3 => |f₂ y|)]
        ring

end Work.BoseRowsL.LatticeCoulomb
