import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi

noncomputable section

open MeasureTheory Set Filter Asymptotics
open scoped Real Topology BigOperators

namespace Commons.Analysis.GaussianMeasure

/-! # The second moment of the Gaussian `exp (-π‖x‖²)` in one coordinate

For the standard Gaussian measure on `EuclideanSpace ℝ (Fin n)` with density
`x ↦ exp (-π‖x‖²)` (total mass one), each coordinate is a standard normal
(rescaled) and its second moment is `1 / (2π)`.  We prove it by
1. computing the one-dimensional integral `∫ x, x² exp (-πx²) = 1/(2π)`
   (integration by parts on `(0,∞)` plus evenness),
2. transferring the integral over `EuclideanSpace ℝ (Fin n)` to the product
   measure on `Fin n → ℝ` (`WithLp.toLp` is volume preserving), where the
   Gaussian density splits as a product over coordinates,
3. applying Fubini (`integral_fintype_prod_volume_eq_prod`): every coordinate
   except `i` contributes `∫ exp (-πt²) = 1` and coordinate `i` contributes
   `∫ t² exp (-πt²) = 1/(2π)`.
-/

-- ================= 1D: total mass and second moment =================

private lemma gaussian_mass_one : (∫ x : ℝ, Real.exp (-Real.pi * x ^ 2)) = 1 := by
  rw [integral_gaussian]
  have hsq : Real.sqrt (Real.pi / Real.pi) = 1 := by
    rw [div_self (ne_of_gt Real.pi_pos)]
    simp
  exact hsq

private lemma gaussian_mass_half :
    (∫ x : ℝ in Ioi 0, Real.exp (-Real.pi * x ^ 2)) = 1 / 2 := by
  rw [integral_gaussian_Ioi]
  have hsq : Real.sqrt (Real.pi / Real.pi) = 1 := by
    rw [div_self (ne_of_gt Real.pi_pos)]
    simp
  norm_num [hsq]

private lemma integrableOn_Ioi_x2e :
    IntegrableOn (fun x : ℝ => x ^ 2 * Real.exp (-Real.pi * x ^ 2)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_sq Real.pi_pos (s := (2:ℝ))
    (by norm_num : (-1 : ℝ) < (2 : ℝ))
  simpa using h

private lemma hasDerivAt_xe (x : ℝ) :
    HasDerivAt (fun x : ℝ => x * Real.exp (-Real.pi * x ^ 2))
      ((1 - 2 * Real.pi * x ^ 2) * Real.exp (-Real.pi * x ^ 2)) x := by
  have hq : HasDerivAt (fun t : ℝ => -Real.pi * t ^ 2) (-(2 * Real.pi) * x) x := by
    have hpow := hasDerivAt_pow 2 x
    simpa [pow_one, mul_assoc, mul_comm, mul_left_comm] using hpow.const_mul (-Real.pi)
  have he : HasDerivAt (fun t : ℝ => Real.exp (-Real.pi * t ^ 2))
      (Real.exp (-Real.pi * x ^ 2) * (-(2 * Real.pi) * x)) x := by
    simpa [Function.comp_def] using (Real.hasDerivAt_exp (-Real.pi * x ^ 2)).comp x hq
  have hx : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
  have hmain : HasDerivAt (fun t : ℝ => t * Real.exp (-Real.pi * t ^ 2))
      (1 * Real.exp (-Real.pi * x ^ 2) + x * (Real.exp (-Real.pi * x ^ 2) * (-(2 * Real.pi) * x))) x := by
    change HasDerivAt (((fun t : ℝ => t) * (fun t : ℝ => Real.exp (-Real.pi * t ^ 2))))
      (1 * Real.exp (-Real.pi * x ^ 2) + x * (Real.exp (-Real.pi * x ^ 2) * (-(2 * Real.pi) * x))) x
    exact hx.mul he
  convert hmain using 1
  ring

private lemma tendsto_xe_zero : Tendsto (fun x : ℝ => x * Real.exp (-Real.pi * x ^ 2)) atTop (𝓝 0) := by
  have ho : (fun x : ℝ => x ^ (1 : ℝ) * Real.exp (-Real.pi * x ^ 2))
      =o[atTop] fun x : ℝ => Real.exp (-(1 / 2) * x) := by
    simpa using (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg (b := Real.pi) Real.pi_pos (1 : ℝ))
  have hgz : Tendsto (fun x : ℝ => Real.exp (-(1 / 2) * x)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact (tendsto_id.const_mul_atTop_of_neg (by norm_num : -(1 / 2 : ℝ) < 0))
  have ho' : (fun x : ℝ => x * Real.exp (-Real.pi * x ^ 2)) =o[atTop]
      fun x : ℝ => Real.exp (-(1 / 2) * x) := by
    refine ho.congr' ?_ (EventuallyEq.rfl)
    filter_upwards with x
    rw [Real.rpow_one]
  exact ho'.tendsto_zero_of_tendsto hgz

/-- `∫₀^∞ x² exp (-πx²) = 1/(4π)`: FTC for `d/dx (x exp(-πx²)) = (1-2πx²)exp(-πx²)`. -/
private lemma gaussian_second_moment_half :
    (∫ x : ℝ in Ioi 0, x ^ 2 * Real.exp (-Real.pi * x ^ 2)) = 1 / (4 * Real.pi) := by
  let e : ℝ → ℝ := fun x => Real.exp (-Real.pi * x ^ 2)
  let B : ℝ → ℝ := fun x => x ^ 2 * e x
  let p : ℝ → ℝ := fun x => x * e x
  let f' : ℝ → ℝ := fun x => e x - (2 * Real.pi) * B x
  have hA : IntegrableOn e (Ioi 0) := by
    simpa [e] using (integrable_exp_neg_mul_sq Real.pi_pos).integrableOn
  have hB : IntegrableOn B (Ioi 0) := by
    simpa [B, e] using integrableOn_Ioi_x2e
  have hBc : IntegrableOn (fun x => (2 * Real.pi) * B x) (Ioi 0) := by
    exact hB.const_mul (2 * Real.pi)
  have hderiv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt p (f' x) x := by
    intro x hx
    dsimp [p, f', B, e]
    have hd := hasDerivAt_xe x
    convert hd using 1
    ring
  have hf'int : IntegrableOn f' (Ioi 0) := by
    dsimp [f']
    exact hA.sub hBc
  have hFTC : (∫ x : ℝ in Ioi 0, f' x) = 0 := by
    have hF := integral_Ioi_of_hasDerivAt_of_tendsto' (a := (0 : ℝ)) (f := p) (f' := f')
      hderiv hf'int tendsto_xe_zero
    simpa [p, e] using hF
  have hlin : (∫ x : ℝ in Ioi 0, f' x) =
      (∫ x : ℝ in Ioi 0, e x) - (2 * Real.pi) * (∫ x : ℝ in Ioi 0, B x) := by
    dsimp [f']
    have hsub := integral_sub (μ := volume.restrict (Ioi (0 : ℝ))) hA hBc
    have hconst : (∫ x : ℝ in Ioi 0, (2 * Real.pi) * B x) =
        (2 * Real.pi) * (∫ x : ℝ in Ioi 0, B x) := by
      simpa using (integral_const_mul (2 * Real.pi) B)
    calc
      (∫ x : ℝ in Ioi 0, (e - fun x => (2 * Real.pi) * B x) x)
          = (∫ x : ℝ in Ioi 0, e x) - (∫ x : ℝ in Ioi 0, (2 * Real.pi) * B x) := by
            simpa using hsub
      _ = (∫ x : ℝ in Ioi 0, e x) - (2 * Real.pi) * (∫ x : ℝ in Ioi 0, B x) := by
            rw [hconst]
  have hI0 : (2 * Real.pi) * (∫ x : ℝ in Ioi 0, B x) = 1 / 2 := by
    have hm : (∫ x : ℝ in Ioi 0, e x) - (2 * Real.pi) * (∫ x : ℝ in Ioi 0, B x) = 0 := by
      rw [← hlin]
      exact hFTC
    have hev : (∫ x : ℝ in Ioi 0, e x) = 1 / 2 := by
      simpa [e] using gaussian_mass_half
    linarith
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  calc
    (∫ x : ℝ in Ioi 0, x ^ 2 * Real.exp (-Real.pi * x ^ 2)) = ∫ x : ℝ in Ioi 0, B x := by
      apply MeasureTheory.integral_congr_ae
      exact Eventually.of_forall (fun x => by dsimp [B, e])
    _ = (1 / 2) / (2 * Real.pi) := by
      rw [eq_div_iff hpi]
      rw [mul_comm]
      exact hI0
    _ = 1 / (4 * Real.pi) := by ring

/-- One-dimensional second moment `∫ x² exp (-πx²) = 1/(2π)` (doubling by evenness). -/
private lemma gaussian_second_moment_one :
    (∫ x : ℝ, x ^ 2 * Real.exp (-Real.pi * x ^ 2)) = 1 / (2 * Real.pi) := by
  let g : ℝ → ℝ := fun t => t ^ 2 * Real.exp (-Real.pi * t ^ 2)
  have hfun : (fun x : ℝ => g |x|) = fun x : ℝ => x ^ 2 * Real.exp (-Real.pi * x ^ 2) := by
    funext x
    dsimp [g]
    rw [sq_abs]
  calc
    (∫ x : ℝ, x ^ 2 * Real.exp (-Real.pi * x ^ 2)) = ∫ x : ℝ, g |x| := by
      rw [hfun]
    _ = 2 * (∫ x : ℝ in Ioi 0, g x) := by
      exact integral_comp_abs
    _ = 2 * (∫ x : ℝ in Ioi 0, x ^ 2 * Real.exp (-Real.pi * x ^ 2)) := by
      rfl
    _ = 1 / (2 * Real.pi) := by
      rw [gaussian_second_moment_half]
      ring

-- ================= n-dimensional: density splits over coordinates =================

private lemma exp_norm_sq_prod {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    Real.exp (-Real.pi * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ ι)‖ ^ 2)
      = ∏ j, Real.exp (-Real.pi * (v j) ^ 2) := by
  have hns : ‖(WithLp.toLp 2 v : EuclideanSpace ℝ ι)‖ ^ 2 = ∑ j, (v j) ^ 2 := by
    rw [EuclideanSpace.norm_eq]
    rw [Real.sq_sqrt]
    · congr
      funext j
      rw [Real.norm_eq_abs, sq_abs]
    · exact Finset.sum_nonneg (fun j hj => sq_nonneg _)
  rw [hns]
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]

private lemma gaussian_integrand_coord {n : ℕ} (i : Fin n) (v : Fin n → ℝ) :
    (v i) * (v i) * Real.exp (-Real.pi * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ ^ 2) =
      ∏ j : Fin n,
        ((if j = i then (v j) * (v j) else 1) * Real.exp (-Real.pi * (v j) ^ 2)) := by
  rw [exp_norm_sq_prod v]
  have hprod : (v i) * (v i) = ∏ j : Fin n, (if j = i then (v j) * (v j) else 1) := by
    rw [Finset.prod_ite_eq' Finset.univ i (fun j => (v j) * (v j))]
    simp
  rw [hprod]
  rw [Finset.prod_mul_distrib]

private lemma gaussian_coord_integral {n : ℕ} (i j : Fin n) :
    (∫ t : ℝ, (if j = i then t * t else 1) * Real.exp (-Real.pi * t ^ 2)) =
      (if j = i then 1 / (2 * Real.pi) else 1) := by
  by_cases hji : j = i
  · subst j
    calc
      (∫ t : ℝ, (if i = i then t * t else 1) * Real.exp (-Real.pi * t ^ 2))
          = (∫ t : ℝ, (t * t) * Real.exp (-Real.pi * t ^ 2)) := by
            apply MeasureTheory.integral_congr_ae
            exact Eventually.of_forall (fun t => by
              change (if i = i then t * t else 1) * Real.exp (-Real.pi * t ^ 2)
                  = (t * t) * Real.exp (-Real.pi * t ^ 2)
              simp)
      _ = (∫ t : ℝ, t ^ 2 * Real.exp (-Real.pi * t ^ 2)) := by
            apply MeasureTheory.integral_congr_ae
            exact Eventually.of_forall (fun t => by
              change (t * t) * Real.exp (-Real.pi * t ^ 2) = t ^ 2 * Real.exp (-Real.pi * t ^ 2)
              rw [← pow_two])
      _ = 1 / (2 * Real.pi) := gaussian_second_moment_one
      _ = (if i = i then 1 / (2 * Real.pi) else 1) := by simp
  · calc
      (∫ t : ℝ, (if j = i then t * t else 1) * Real.exp (-Real.pi * t ^ 2))
          = (∫ t : ℝ, Real.exp (-Real.pi * t ^ 2)) := by
            apply MeasureTheory.integral_congr_ae
            exact Eventually.of_forall (fun t => by
              change (if j = i then t * t else 1) * Real.exp (-Real.pi * t ^ 2)
                  = Real.exp (-Real.pi * t ^ 2)
              simp [hji])
      _ = 1 := gaussian_mass_one
      _ = (if j = i then 1 / (2 * Real.pi) else 1) := by simp [hji]

private lemma gaussian_second_moment_fun (n : ℕ) (i : Fin n) :
    (∫ v : (Fin n → ℝ), (v i) * (v i) *
      Real.exp (-Real.pi * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ ^ 2))
      = 1 / (2 * Real.pi) := by
  let f : Fin n → ℝ → ℝ := fun j t =>
    (if j = i then t * t else 1) * Real.exp (-Real.pi * t ^ 2)
  have hconv : (∫ v : Fin n → ℝ, (v i) * (v i) *
      Real.exp (-Real.pi * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ ^ 2))
      = ∫ v : Fin n → ℝ, ∏ j : Fin n, f j (v j) := by
    apply MeasureTheory.integral_congr_ae
    exact Eventually.of_forall (fun v => by
      change (v i) * (v i) * Real.exp (-Real.pi * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ ^ 2)
          = ∏ j : Fin n, f j (v j)
      rw [gaussian_integrand_coord i v])
  rw [hconv]
  rw [integral_fintype_prod_volume_eq_prod]
  have hval : ∀ j : Fin n, (∫ t : ℝ, f j t) = (if j = i then 1 / (2 * Real.pi) else 1) := by
    intro j
    simpa [f] using gaussian_coord_integral i j
  simp_rw [hval]
  rw [Finset.prod_ite_eq' Finset.univ i (fun _ => 1 / (2 * Real.pi))]
  simp

/-- The second moment of a single coordinate of the standard Gaussian measure on
`EuclideanSpace ℝ (Fin n)` (density `exp (-π‖x‖²)`) is `1/(2π)`. -/
lemma second_moment_diagonal {n : ℕ} (i : Fin n) :
    (∫ x : EuclideanSpace ℝ (Fin n), (x i) * (x i) * Real.exp (-Real.pi * ‖x‖ ^ 2)) =
      1 / (2 * Real.pi) := by
  have htr :
      (∫ x : EuclideanSpace ℝ (Fin n), (x i) * (x i) * Real.exp (-Real.pi * ‖x‖ ^ 2)) =
        ∫ v : (Fin n → ℝ),
          (((WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n)) i) *
            ((WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n)) i) *
            Real.exp (-Real.pi * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ ^ 2)) := by
    exact (((PiLp.volume_preserving_toLp (Fin n)).integral_comp
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding
      (fun x : EuclideanSpace ℝ (Fin n) =>
        (x i) * (x i) * Real.exp (-Real.pi * ‖x‖ ^ 2))).symm)
  rw [htr]
  rw [gaussian_second_moment_fun n i]

end Commons.Analysis.GaussianMeasure