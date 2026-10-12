import Mathlib.Analysis.Convolution
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.SqrtKin.heat_ft_p
import Submission.Work.BoseBoxFock.aliasFt
import Submission.Work.BoseFixR.LatGreen.latticeGaussSummable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.AliasAux` — the elementary input of the aliasing identity

The facts about the autocorrelation kernel `autocorr g u = ∫ x, g x · conj (g (x − u))` and the
heat kernel `heatK t` that the Poisson/aliasing identity `aliasIdentity` consumes:

* `autocorr_continuous`, `autocorr_integrable` — `g` smooth with compact support ⟹ `autocorr g`
  is a convolution of two `L¹` functions, hence continuous and integrable;
* `autocorr_norm_le` — the pointwise Cauchy–Schwarz bound `‖autocorr g u‖ ≤ ∫‖g‖²`;
* `autocorr_eq_zero_of_le_norm` — if `tsupport g ⊆ ball 0 (ℓ/2)` then `autocorr g u = 0` for
  `ℓ ≤ ‖u‖` (the ball and its translate by `u` are then disjoint);
* `heatK_fourier` — the `p`-convention Fourier integral of the Gaussian heat kernel,
  `∫_p e^{−t‖p‖²} e^{−I⟪p,u⟫} dp = (2π)³ heatK t u` (the sign-flipped companion of
  `Work.BoseBoxFock.SqrtKin.heat_ft_p`);
* `summable_heatK_latticeShift` — the shifted lattice Gaussian sum
  `Σ_m heatK t (u − ℓ • latVec m)` converges.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000

/-! ## 1. The autocorrelation as a convolution -/

theorem autocorr_eq_convolution (g : E3 → ℂ) :
    autocorr g = convolution g (fun v : E3 => (starRingEnd ℂ) (g (-v)))
      (ContinuousLinearMap.mul ℂ ℂ) volume := by
  funext u
  rw [MeasureTheory.convolution_def]
  simp only [ContinuousLinearMap.mul_apply']
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp [neg_sub]

theorem hasCompactSupport_star_neg {g : E3 → ℂ} (hgc : HasCompactSupport g) :
    HasCompactSupport (fun v : E3 => (starRingEnd ℂ) (g (-v))) :=
  HasCompactSupport.comp_left (f := fun v : E3 => g (-v)) (g := starRingEnd ℂ)
    (hgc.comp_homeomorph (Homeomorph.neg E3)) (by simp)

theorem continuous_star_neg {g : E3 → ℂ} (hg : Continuous g) :
    Continuous (fun v : E3 => (starRingEnd ℂ) (g (-v))) :=
  Complex.continuous_conj.comp (hg.comp continuous_neg)

theorem autocorr_continuous {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) : Continuous (autocorr g) := by
  have hL : LocallyIntegrable g volume := hg.continuous.locallyIntegrable
  have hc := (hasCompactSupport_star_neg hgc).continuous_convolution_right
    (L := ContinuousLinearMap.mul ℂ ℂ) (μ := volume) hL (continuous_star_neg hg.continuous)
  rwa [← autocorr_eq_convolution g] at hc

theorem autocorr_integrable {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) : Integrable (autocorr g) volume := by
  have hg1 : Integrable g volume := hg.continuous.integrable_of_hasCompactSupport hgc
  have h2 : Integrable (fun v : E3 => (starRingEnd ℂ) (g (-v))) volume :=
    (continuous_star_neg hg.continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_star_neg hgc)
  have hconv : Integrable (convolution g (fun v : E3 => (starRingEnd ℂ) (g (-v)))
      (ContinuousLinearMap.mul ℂ ℂ) volume) volume :=
    Integrable.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hg1 h2
  rwa [← autocorr_eq_convolution g] at hconv

/-! ## 2. The pointwise Cauchy–Schwarz bound -/

theorem autocorr_norm_le {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) (u : E3) :
    ‖autocorr g u‖ ≤ ∫ x : E3, ‖g x‖ ^ 2 := by
  have hg2 : MemLp g 2 volume := hg.continuous.memLp_of_hasCompactSupport hgc
  have hgu : MemLp (fun x : E3 => g (x - u)) 2 volume := by
    have h := hg2.comp_measurePreserving
      (MeasureTheory.measurePreserving_add_right volume (-u))
    simpa only [Function.comp_def, sub_eq_add_neg] using h
  have hineq : ‖autocorr g u‖ ≤ ∫ x : E3, ‖g x‖ * ‖g (x - u)‖ := by
    calc ‖autocorr g u‖ = ‖∫ x : E3, g x * starRingEnd ℂ (g (x - u))‖ := rfl
      _ ≤ ∫ x : E3, ‖g x * starRingEnd ℂ (g (x - u))‖ :=
            MeasureTheory.norm_integral_le_integral_norm _
      _ = ∫ x : E3, ‖g x‖ * ‖g (x - u)‖ := by
            congr 1 with x
            rw [norm_mul, Complex.norm_conj]
  refine hineq.trans ?_
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hHolder := integral_mul_norm_le_Lp_mul_Lq (μ := volume) (f := g)
    (g := fun x : E3 => g (x - u)) hpq (by simpa using hg2) (by simpa using hgu)
  have hshift : (∫ x : E3, ‖g (x - u)‖ ^ (2 : ℝ)) = ∫ x : E3, ‖g x‖ ^ (2 : ℝ) := by
    have := integral_sub_right_eq_self (μ := volume) (fun x : E3 => ‖g x‖ ^ (2 : ℝ)) u
    simpa using this
  have hsq : (∫ x : E3, ‖g x‖ ^ (2 : ℝ)) = ∫ x : E3, ‖g x‖ ^ 2 := by
    congr 1 with x
    rw [Real.rpow_two]
  have hnonneg : 0 ≤ ∫ x : E3, ‖g x‖ ^ (2 : ℝ) :=
    integral_nonneg (fun x => by positivity)
  calc ∫ x : E3, ‖g x‖ * ‖g (x - u)‖
      ≤ (∫ x : E3, ‖g x‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
          * (∫ x : E3, ‖g (x - u)‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hHolder
    _ = (∫ x : E3, ‖g x‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
          * (∫ x : E3, ‖g x‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by rw [hshift]
    _ = ∫ x : E3, ‖g x‖ ^ (2 : ℝ) := by
          rw [← Real.sqrt_eq_rpow]
          exact Real.mul_self_sqrt hnonneg
    _ = ∫ x : E3, ‖g x‖ ^ 2 := hsq

/-! ## 3. The support of the autocorrelation -/

theorem autocorr_eq_zero_of_le_norm {ℓ : ℝ} (hℓ : 0 < ℓ)
    {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgsupp : tsupport g ⊆ Metric.ball 0 (ℓ/2)) {u : E3} (hu : ℓ ≤ ‖u‖) :
    autocorr g u = 0 := by
  have hzero : ∀ x, g x * starRingEnd ℂ (g (x - u)) = 0 := by
    intro x
    by_contra h
    have hx : g x ≠ 0 := fun hx0 => h (by simp [hx0])
    have hy : g (x - u) ≠ 0 := fun hy0 => h (by simp [hy0])
    have hxmem : x ∈ Metric.ball (0 : E3) (ℓ/2) :=
      hgsupp (subset_closure (Function.mem_support.mpr hx))
    have hymem : x - u ∈ Metric.ball (0 : E3) (ℓ/2) :=
      hgsupp (subset_closure (Function.mem_support.mpr hy))
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hxmem hymem
    have h1 : ‖u‖ ≤ ‖x - u‖ + ‖x‖ := by
      have h2 : ‖u‖ ≤ ‖u - x‖ + ‖x‖ := by
        have := norm_add_le (u - x) x
        simpa using this
      simpa [norm_sub_rev u x] using h2
    linarith
  rw [autocorr, show (fun x : E3 => g x * starRingEnd ℂ (g (x - u))) = fun _ => 0 from
    funext hzero]
  simp

/-! ## 4. The Fourier integral of the heat kernel (sign-flipped `heat_ft_p`) -/

theorem heatK_fourier {t : ℝ} (ht : 0 < t) (u : E3) :
    ∫ p : E3, (Real.exp (-(t * ‖p‖ ^ 2)) : ℂ)
        * Complex.exp (-(Complex.I * (inner ℝ p u : ℂ)))
      = (((2 * Real.pi) ^ 3 * heatK t u : ℝ) : ℂ) := by
  have h := Work.BoseBoxFock.SqrtKin.heat_ft_p (t := t) ht (-u)
  rw [heatK_even] at h
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [inner_neg_right, Complex.ofReal_neg]
  rw [mul_comm]
  congr 1
  ring

/-! ## 5. The shifted lattice Gaussian sum -/

theorem summable_heatK_latticeShift {ℓ t : ℝ} (hℓ : 0 < ℓ) (ht : 0 < t) (u : E3) :
    Summable (fun m : Fin 3 → ℤ => heatK t (u - ℓ • latVec m)) := by
  have hc : 0 < ℓ ^ 2 / (4 * t) := by positivity
  have h : Summable (fun m : Fin 3 → ℤ =>
      Real.exp (-(ℓ ^ 2 / (4 * t)) * ‖ℓ⁻¹ • u - latVec m‖ ^ 2)) :=
    Work.BoseFixR.LatGreen.latticeGaussSummable (ℓ⁻¹ • u) hc
  refine (h.mul_left ((4 * Real.pi * t) ^ (-(3 : ℝ) / 2))).congr (fun m => ?_)
  rw [heatK]
  have hsm : u - ℓ • latVec m = ℓ • (ℓ⁻¹ • u - latVec m) := by
    rw [smul_sub, smul_inv_smul₀ hℓ.ne']
  rw [hsm, norm_smul, Real.norm_of_nonneg hℓ.le]
  congr 1
  ring_nf

end Work.BoseBoxFock
