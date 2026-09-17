import Mathlib
import Submission.Commons.Probability.Gaussian.stdGaussian_real_tail_le
import Submission.Commons.Probability.Gaussian.sum_tail_div_sqrt_le
import Submission.Commons.Analysis.Exponential.exp_le_one_div_one_sub

/-!
# The one-dimensional shell-weight estimate for Klartag's packing argument

We prove `Commons.Analysis.Gaussian.integral_shell_weight_le`:

    ∃ D, ∀ d ≥ D, ∀ K, (K:ℝ) ≤ 16 d² log d + 1 →
      ∫_1^2 y^{d-1} Σ_{k ≤ K} Φ̄((a₀ - 1/y²) d² / √k) dy ≤ 10^6 d³,

where `a₀ = ((1 - 1/d)²)⁻¹` and `Φ̄` is the standard Gaussian upper tail.

The strategy is
* a sharp bound for the sum of Gaussian tails
  `Σ_{k ≤ K} Φ̄(β/√k) ≤ (√K/β + 2K²√K/β³) e^{-β²/(2K)} / √(2π)`
  (Mills ratio + `sum_exp_neg_div_le`),
* the substitution `y = 1 + u/d`, so that the exponent
  `a₀ - 1/y² = 2(u/d) - 3(u/d)² + O(1/d)` grows linearly in `u`,
* a four-region estimate of `∫_0^d e^{u} e^{-β²/(2K)} (…) du`.
-/

open MeasureTheory
open scoped Real

set_option maxHeartbeats 30000000

namespace Commons.Analysis.Gaussian

/-! ### A sharp bound for the sum of Gaussian tails -/

/-- Sum of the standard Gaussian upper tails `Φ̄(β/√k)`, `k = 1,…,K`, is bounded by
`(√K/β + 2K²√K/β³) · exp(-β²/(2K)) / √(2π)` for `β > 0`, `K ≥ 1`.

This improves on `(4K²/β² + 1) exp(-β²/(2K))` by the extra factor `√K/β` in the regime
`β ≫ √K` that is relevant here. -/
theorem sum_tail_div_sqrt_le_cube {β : ℝ} (hβ : 0 < β) {K : ℕ} (hK : 1 ≤ K) :
    (∑ k ∈ Finset.Icc 1 K,
        (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ | β / Real.sqrt (k : ℝ) ≤ z})
      ≤ (Real.sqrt (K : ℝ) * β⁻¹ + 2 * (K : ℝ) ^ 2 * Real.sqrt (K : ℝ) * (β ^ 3)⁻¹)
          * Real.exp (-(β ^ 2) / (2 * (K : ℝ))) / Real.sqrt (2 * Real.pi) := by
  have hKpos : (0:ℝ) < (K:ℝ) := by exact_mod_cast hK
  have hKne : (K:ℝ) ≠ 0 := ne_of_gt hKpos
  have hβne : β ≠ 0 := ne_of_gt hβ
  have hs2pi : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hs2pine : Real.sqrt (2*Real.pi) ≠ 0 := ne_of_gt hs2pi
  have hterm : ∀ k ∈ Finset.Icc 1 K,
      (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ | β / Real.sqrt (k : ℝ) ≤ z}
        ≤ Real.sqrt (k : ℝ) * Real.exp (-((β^2/2) / (k : ℝ))) / (Real.sqrt (2 * Real.pi) * β) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk1
    have hsq : 0 < Real.sqrt (k:ℝ) := Real.sqrt_pos_of_pos hkpos
    have hz : 0 < β / Real.sqrt (k : ℝ) := div_pos hβ hsq
    refine (Commons.Probability.Gaussian.stdGaussian_real_tail_le _ hz).trans ?_
    rw [min_le_iff]
    right
    have h1 : Real.exp (-((β / Real.sqrt (k:ℝ))^2) / 2) = Real.exp (-((β^2/2)/(k:ℝ))) := by
      rw [div_pow, Real.sq_sqrt hkpos.le]
      congr 1
      ring
    rw [h1]
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < Real.sqrt (2*Real.pi) * (β / Real.sqrt (k:ℝ)))
      (by positivity : (0:ℝ) < Real.sqrt (2*Real.pi) * β)]
    field_simp
    ring_nf
    norm_num
  have hstep2 : (∑ k ∈ Finset.Icc 1 K,
        (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ | β / Real.sqrt (k : ℝ) ≤ z})
      ≤ (∑ k ∈ Finset.Icc 1 K, Real.sqrt (k : ℝ) * Real.exp (-((β^2/2) / (k : ℝ))))
          / (Real.sqrt (2 * Real.pi) * β) := by
    calc _ ≤ ∑ k ∈ Finset.Icc 1 K,
          Real.sqrt (k : ℝ) * Real.exp (-((β^2/2) / (k : ℝ))) / (Real.sqrt (2 * Real.pi) * β) :=
        Finset.sum_le_sum hterm
      _ = _ := by rw [Finset.sum_div]
  have hstep3 : (∑ k ∈ Finset.Icc 1 K, Real.sqrt (k : ℝ) * Real.exp (-((β^2/2) / (k : ℝ))))
      ≤ Real.sqrt (K:ℝ) * (1 + (K:ℝ)^2 / (β^2/2)) * Real.exp (-((β^2/2) / (K:ℝ))) := by
    calc (∑ k ∈ Finset.Icc 1 K, Real.sqrt (k : ℝ) * Real.exp (-((β^2/2) / (k : ℝ))))
        ≤ ∑ k ∈ Finset.Icc 1 K, Real.sqrt (K:ℝ) * Real.exp (-((β^2/2) / (k : ℝ))) := by
          apply Finset.sum_le_sum
          intro k hk
          have hkK : k ≤ K := (Finset.mem_Icc.mp hk).2
          have h1 : Real.sqrt (k:ℝ) ≤ Real.sqrt (K:ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hkK)
          exact mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
      _ = Real.sqrt (K:ℝ) * ∑ k ∈ Finset.Icc 1 K, Real.exp (-((β^2/2) / (k : ℝ))) := by
          rw [Finset.mul_sum]
      _ ≤ Real.sqrt (K:ℝ) * ((1 + (K:ℝ)^2 / (β^2/2)) * Real.exp (-((β^2/2) / (K:ℝ)))) := by
          apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
          exact Commons.Probability.Gaussian.sum_exp_neg_div_le (c := β^2/2) (by positivity) hK
      _ = Real.sqrt (K:ℝ) * (1 + (K:ℝ)^2 / (β^2/2)) * Real.exp (-((β^2/2) / (K:ℝ))) := by ring
  refine hstep2.trans ?_
  have h4 : (∑ k ∈ Finset.Icc 1 K, Real.sqrt (k : ℝ) * Real.exp (-((β^2/2) / (k : ℝ))))
        / (Real.sqrt (2 * Real.pi) * β)
      ≤ Real.sqrt (K:ℝ) * (1 + (K:ℝ)^2 / (β^2/2)) * Real.exp (-((β^2/2) / (K:ℝ)))
        / (Real.sqrt (2 * Real.pi) * β) :=
    div_le_div_of_nonneg_right hstep3 (by positivity)
  refine h4.trans ?_
  have hexp : Real.exp (-((β^2/2) / (K:ℝ))) = Real.exp (-(β ^ 2) / (2 * (K : ℝ))) := by
    congr 1; ring
  rw [hexp]
  apply le_of_eq
  have hden : Real.sqrt (2*Real.pi) * β ≠ 0 := mul_ne_zero hs2pine hβne
  rw [div_eq_div_iff hden hs2pine]
  field_simp

/-! ### Two Gaussian integrals -/

/-- `∫_ℝ exp(-(u-4L)²/(8L)) du = √(8πL)`. -/
theorem integral_gaussian_shift (L : ℝ) (hL : 0 < L) :
    ∫ u : ℝ, Real.exp (-((u - 4*L)^2)/(8*L)) = Real.sqrt (8*Real.pi*L) := by
  have hne : (8:ℝ)*L ≠ 0 := by positivity
  have h := integral_gaussian (1/(8*L))
  have h1 : ∫ x : ℝ, Real.exp (-((x - 4*L)^2)/(8*L))
      = ∫ x : ℝ, Real.exp (-(1/(8*L)) * x^2) := by
    rw [← integral_sub_right_eq_self (f := fun x => Real.exp (-(1/(8*L)) * x^2)) (4*L)]
    apply integral_congr_ae
    filter_upwards with x
    congr 1
    ring
  rw [h1, h]
  congr 1
  field_simp

/-- `∫_ℝ exp(u - u²/(8L)) du = √(8πL) · exp(2L)`. -/
theorem integral_exp_sub_sq_div (L : ℝ) (hL : 0 < L) :
    ∫ u : ℝ, Real.exp (u - u^2/(8*L)) = Real.sqrt (8*Real.pi*L) * Real.exp (2*L) := by
  have hpt : ∀ u : ℝ, Real.exp (u - u^2/(8*L))
      = Real.exp (-((u-4*L)^2)/(8*L)) * Real.exp (2*L) := by
    intro u
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  simp_rw [hpt]
  rw [integral_mul_const, integral_gaussian_shift L hL]

/-! ### The shell argument `a₀ - 1/y²` along `y = 1 + u/d` -/

/-- `a₀ - 1/y²` with `a₀ = ((1 - 1/d)²)⁻¹` and `y = 1 + u/d`. -/
noncomputable def shellA (d : ℕ) (u : ℝ) : ℝ :=
  ((1 - 1/(d:ℝ))^2)⁻¹ - ((1 + u/(d:ℝ))^2)⁻¹

/-- The argument `β = (a₀ - 1/y²)·d²` of the Gaussian tail. -/
noncomputable def shellB (d : ℕ) (u : ℝ) : ℝ := shellA d u * (d:ℝ)^2

/-- `1 - 1/(1+s)² ≥ 2s - 3s²` for `s ≥ 0`. -/
lemma one_sub_inv_sq_ge (s : ℝ) (hs : 0 ≤ s) :
    2*s - 3*s^2 ≤ 1 - ((1+s)^2)⁻¹ := by
  have hkey : 1 - ((1+s)^2)⁻¹ - (2*s - 3*s^2) = (4*s^3 + 3*s^4)/(1+s)^2 := by
    field_simp
    ring
  have hnn : 0 ≤ (4*s^3 + 3*s^4)/(1+s)^2 := by
    apply div_nonneg _ (by positivity)
    nlinarith [sq_nonneg s, mul_nonneg hs (sq_nonneg s)]
  linarith [hkey, hnn]

/-- `((1 - 1/d)²)⁻¹ - 1 ≥ 1/d` for `d ≥ 2`. -/
lemma inv_one_sub_inv_sq_sub_one {d : ℕ} (hd : 2 ≤ d) :
    (d:ℝ)⁻¹ ≤ ((1 - 1/(d:ℝ))^2)⁻¹ - 1 := by
  have hdr : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hdpos : (0:ℝ) < (d:ℝ) := by linarith
  have hdm1 : (0:ℝ) < (d:ℝ) - 1 := by linarith
  have hkey : ((1 - 1/(d:ℝ))^2)⁻¹ - 1 = (2*(d:ℝ)-1)/((d:ℝ)-1)^2 := by
    field_simp
    ring
  rw [hkey, ← one_div]
  rw [div_le_div_iff₀ hdpos (pow_pos hdm1 2)]
  nlinarith

/-- `((1 - 1/d)²)⁻¹ > 1` for `d ≥ 2`. -/
lemma one_lt_inv_one_sub {d : ℕ} (hd : 2 ≤ d) :
    1 < ((1 - 1/(d:ℝ))^2)⁻¹ := by
  have hdr : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hdpos : (0:ℝ) < (d:ℝ) := by linarith
  have h1 : (0:ℝ) < 1 - 1/(d:ℝ) := by rw [sub_pos, div_lt_one hdpos]; linarith
  have h2 : (1 - 1/(d:ℝ))^2 < 1 := by
    have h3 : (0:ℝ) < 1/(d:ℝ) := by positivity
    nlinarith
  have h3 : (0:ℝ) < (1 - 1/(d:ℝ))^2 := by positivity
  exact (one_lt_inv₀ h3).mpr h2

/-- `shellA d u > 0` for `u ≥ 0`, `d ≥ 2`. -/
lemma shellA_pos {d : ℕ} {u : ℝ} (hd : 2 ≤ d) (hu : 0 ≤ u) : 0 < shellA d u := by
  have hdr : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hdpos : (0:ℝ) < (d:ℝ) := by linarith
  have hgt1 := one_lt_inv_one_sub hd
  have hle1 : ((1 + u/(d:ℝ))^2)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity)]
    nlinarith [div_nonneg hu (le_of_lt hdpos)]
  rw [shellA]
  linarith

lemma shellB_nonneg {d : ℕ} {u : ℝ} (hd : 2 ≤ d) (hu : 0 ≤ u) : 0 ≤ shellB d u :=
  le_of_lt (mul_pos (shellA_pos hd hu) (by positivity))

lemma shellB_pos {d : ℕ} {u : ℝ} (hd : 2 ≤ d) (hu : 0 ≤ u) : 0 < shellB d u :=
  mul_pos (shellA_pos hd hu) (by positivity)

/-- Along `y = 1 + u/d`, `a₀ - 1/y² ≥ 1/d + 2(u/d) - 3(u/d)²` for `u ≥ 0`. -/
lemma shellA_lower_linear {d : ℕ} {u : ℝ} (hd : 2 ≤ d) (hu : 0 ≤ u) :
    (d:ℝ)⁻¹ + 2*(u/(d:ℝ)) - 3*(u/(d:ℝ))^2 ≤ shellA d u := by
  have hdr : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hdpos : (0:ℝ) < (d:ℝ) := by linarith
  have hs0 : 0 ≤ u/(d:ℝ) := div_nonneg hu (le_of_lt hdpos)
  have h1 := inv_one_sub_inv_sq_sub_one hd
  have h2 := one_sub_inv_sq_ge (u/(d:ℝ)) hs0
  have h3 : ((1 - 1/(d:ℝ))^2)⁻¹ - ((1 + u/(d:ℝ))^2)⁻¹
      = (((1 - 1/(d:ℝ))^2)⁻¹ - 1) + (1 - ((1 + u/(d:ℝ))^2)⁻¹) := by ring
  rw [shellA, h3]
  linarith

/-- For `u ≥ d/2` the shell argument is at least `5/9`. -/
lemma shellA_ge_five_ninths {d : ℕ} {u : ℝ} (hd : 2 ≤ d) (hu : (d:ℝ)/2 ≤ u) :
    5/9 ≤ shellA d u := by
  have hdr : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hdpos : (0:ℝ) < (d:ℝ) := by linarith
  have hs : (1:ℝ)/2 ≤ u/(d:ℝ) := by
    rw [le_div_iff₀ hdpos]
    linarith
  have h1 : (1:ℝ) ≤ ((1 - 1/(d:ℝ))^2)⁻¹ := le_of_lt (one_lt_inv_one_sub hd)
  have hA : (0:ℝ) < 1 + u/(d:ℝ) := by linarith
  have h5 : (9/4:ℝ) ≤ (1 + u/(d:ℝ))^2 := by nlinarith
  have h6 : ((1 + u/(d:ℝ))^2)⁻¹ ≤ 4/9 := by
    have := (inv_le_inv₀ (by positivity : (0:ℝ) < (1 + u/(d:ℝ))^2)
      (by norm_num : (0:ℝ) < 9/4)).mpr h5
    simpa using this
  rw [shellA]
  linarith

/-- `shellA ≤ 4` for `d ≥ 2`. -/
lemma shellA_le_four {d : ℕ} (hd : 2 ≤ d) (u : ℝ) : shellA d u ≤ 4 := by
  have hdr : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hinv : ((1 - 1/(d:ℝ))^2)⁻¹ ≤ 4 := by
    have hdpos : (0:ℝ) < (d:ℝ) := by linarith
    have hdd : (1:ℝ)/(d:ℝ) ≤ 1/2 := by
      rw [div_le_div_iff₀ hdpos (by norm_num)]
      linarith
    have h2 : (1/4:ℝ) ≤ (1 - 1/(d:ℝ))^2 := by nlinarith
    have := (inv_le_inv₀ (by positivity : (0:ℝ) < (1 - 1/(d:ℝ))^2)
      (by norm_num : (0:ℝ) < 1/4)).mpr h2
    simpa using this
  have hle : 0 ≤ ((1 + u/(d:ℝ))^2)⁻¹ := by positivity
  rw [shellA]
  linarith


lemma integral_Ioc_le_integral_of_nonneg {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x, 0 ≤ f x) (hfi : Integrable f volume) :
    ∫ x in a..b, f x ≤ ∫ x : ℝ, f x := by
  rw [intervalIntegral.integral_of_le hab]
  calc ∫ x in Set.Ioc a b, f x ≤ ∫ x in Set.univ, f x :=
        setIntegral_mono_set hfi.integrableOn (Filter.Eventually.of_forall hf)
          (Filter.Eventually.of_forall (fun x _ => Set.mem_univ x))
    _ = ∫ x : ℝ, f x := setIntegral_univ

lemma integral_mono_of_nonneg_Ioc {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (hf : ∀ x ∈ Set.Ioc a b, 0 ≤ f x) (hg : IntegrableOn g (Set.Ioc a b) volume)
    (hfg : ∀ x ∈ Set.Ioc a b, f x ≤ g x) : ∫ x in a..b, f x ≤ ∫ x in a..b, g x := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  refine MeasureTheory.integral_mono_of_nonneg ?_ hg ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hf x hx
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hfg x hx

lemma integrableOn_Ioc_of_continuousOn {a b : ℝ} {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Icc a b)) :
    IntegrableOn g (Set.Ioc a b) volume :=
  (hg.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self

lemma integrable_exp_sub_sq_div (L : ℝ) (hL : 0 < L) :
    Integrable (fun x : ℝ => Real.exp (x - x^2/(8*L))) volume := by
  have h1 : Integrable (fun x : ℝ => Real.exp (-(1/(8*L)) * x^2)) volume :=
    integrable_exp_neg_mul_sq (by positivity)
  have h2 : Integrable (fun x : ℝ => Real.exp (2*L) * Real.exp (-(1/(8*L)) * x^2)) volume :=
    h1.const_mul _
  have h3 := h2.comp_sub_right (4*L)
  refine h3.congr ?_
  filter_upwards with x
  rw [← Real.exp_add]
  congr 1
  field_simp
  ring

/-- `∫_a^b exp(x - x²/(8L)) dx ≤ √(8πL) · (exp L)²` for `L > 0`, `a ≤ b`. -/
lemma integral_exp_sub_sq_div_Icc_le (L a b : ℝ) (hL : 0 < L) (hab : a ≤ b) :
    ∫ x in a..b, Real.exp (x - x^2/(8*L)) ≤ Real.sqrt (8*Real.pi*L) * (Real.exp L)^2 := by
  have h1 := integral_Ioc_le_integral_of_nonneg hab (fun x => Real.exp_nonneg _)
    (integrable_exp_sub_sq_div L hL)
  refine h1.trans (le_of_eq ?_)
  rw [integral_exp_sub_sq_div L hL]
  have h2 : Real.exp (2*L) = (Real.exp L)^2 := by
    simpa using Real.exp_nat_mul L 2
  rw [h2]

/-- sharp exponent bound on [1,21L] -/
lemma exp_bound_twentyone {d K : ℕ} {L x : ℝ} (hd2 : 2 ≤ d) (hdrpos : 0 < (d:ℝ))
    (hdr2 : (2:ℝ) ≤ (d:ℝ)) (hdr20 : (10:ℝ)^20 ≤ (d:ℝ)) (hLpos : 0 < L) (hL1 : 1 ≤ L)
    (hKpos : (0:ℝ) < (K:ℝ)) (hK : (K:ℝ) ≤ 16*(d:ℝ)^2*L + 1)
    (h126L : 126*L ≤ (d:ℝ)) (h34730L2 : 34730*L^2 ≤ (d:ℝ))
    (hx : x ∈ Set.Icc (1:ℝ) (21*L)) :
    Real.exp (-(shellB d x)^2/(2*(K:ℝ))) ≤ Real.exp 1.1 * Real.exp (-(x^2)/(8*L)) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hSA := shellA_lower_linear (d := d) hd2 hx0
  have hkey : ((d:ℝ)⁻¹ + 2*(x/(d:ℝ)) - 3*(x/(d:ℝ))^2) * (d:ℝ)^2
      = (d:ℝ) + 2*x*(d:ℝ) - 3*x^2 := by field_simp <;> ring
  have hge0 : 0 ≤ 3*x/(2*(d:ℝ)) := by positivity
  have hle_half : 3*x/(2*(d:ℝ)) ≤ 1/2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith [hx.2, h126L]
  have hb : 2*x*(d:ℝ)*(1 - (3*x/(2*(d:ℝ)))) ≤ shellB d x := by
    have h3 : 2*x*(d:ℝ) - 3*x^2 ≤ shellB d x := by
      rw [shellB]
      refine le_trans ?_ (mul_le_mul_of_nonneg_right hSA (by positivity))
      rw [hkey]; linarith [hdrpos]
    have h4 : 2*x*(d:ℝ)*(1 - (3*x/(2*(d:ℝ)))) = 2*x*(d:ℝ) - 3*x^2 := by
      field_simp <;> ring
    rw [h4]; exact h3
  have hb0 : 0 ≤ 2*x*(d:ℝ)*(1 - (3*x/(2*(d:ℝ)))) := by
    apply mul_nonneg (by positivity)
    linarith [hle_half]
  have hβ2 : (2*x*(d:ℝ)*(1 - (3*x/(2*(d:ℝ)))))^2 ≤ (shellB d x)^2 := pow_le_pow_left₀ hb0 hb 2
  -- bound on `1/(2K)`
  have hden1 : (0:ℝ) < 32*(d:ℝ)^2*L := by positivity
  have hKden : 1/(32*(d:ℝ)^2*L) - 1/(256*(d:ℝ)^4*L^2) ≤ 1/(2*(K:ℝ)) := by
    have h2k : (2:ℝ)*(K:ℝ) ≤ 32*(d:ℝ)^2*L + 4 := by nlinarith [hK]
    have h2k' : (0:ℝ) < 2*(K:ℝ) := by positivity
    have hstep : 1/(32*(d:ℝ)^2*L + 4) ≤ 1/(2*(K:ℝ)) :=
      one_div_le_one_div_of_le h2k' h2k
    have hstep2 : 1/(32*(d:ℝ)^2*L) - 1/(256*(d:ℝ)^4*L^2) ≤ 1/(32*(d:ℝ)^2*L + 4) := by
      rw [div_sub_div _ _ (ne_of_gt hden1) (by positivity : (256*(d:ℝ)^4*L^2) ≠ 0)]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hden1]
    exact hstep2.trans hstep
  have hcoef0 : (0:ℝ) ≤ 1/(32*(d:ℝ)^2*L) - 1/(256*(d:ℝ)^4*L^2) := by
    rw [sub_nonneg, div_le_div_iff₀ (by positivity) (by positivity)]
    have h8 : (0:ℝ) ≤ 8*(d:ℝ)^2*L - 1 := by nlinarith [hden1, hdr2, hL1]
    nlinarith [mul_nonneg hden1.le h8]
  have hbnd : x^2*(1-(3*x/(2*(d:ℝ))))^2/(8*L) - x^2*(1-(3*x/(2*(d:ℝ))))^2/(64*(d:ℝ)^2*L^2) ≤ (shellB d x)^2/(2*(K:ℝ)) := by
    have hconv : (2*x*(d:ℝ)*(1-(3*x/(2*(d:ℝ)))))^2 * (1/(32*(d:ℝ)^2*L) - 1/(256*(d:ℝ)^4*L^2))
        = x^2*(1-(3*x/(2*(d:ℝ))))^2/(8*L) - x^2*(1-(3*x/(2*(d:ℝ))))^2/(64*(d:ℝ)^2*L^2) := by
      field_simp <;> ring
    rw [← hconv]
    have hprod := mul_le_mul_of_nonneg_right hβ2 hcoef0
    have hcoef2 := mul_le_mul_of_nonneg_left hKden (sq_nonneg (shellB d x))
    have heq : (shellB d x)^2 * (1/(2*(K:ℝ))) = (shellB d x)^2/(2*(K:ℝ)) := by ring
    rw [heq] at hcoef2
    exact hprod.trans hcoef2
  have hx3 : x^3 ≤ 9261*L^3 := by
    have h := pow_le_pow_left₀ hx0 hx.2 3
    norm_num at h
    linarith [h]
  set ps : ℝ := (1-(3*x/(2*(d:ℝ))))^2 with hps
  have hps_le : ps ≤ 1 := by nlinarith [hge0, hle_half]
  have ha : x^2/(8*L) - x^2*ps/(8*L) ≤ 0.15 := by
    have h1 : (0:ℝ) ≤ 1 - ps := by linarith only [hps_le]
    have h2 : x^2/(8*L) - x^2*ps/(8*L) = x^2/(8*L) * (1 - ps) := by ring
    rw [h2]
    have h3 : (1:ℝ) - ps = 1 - (1-(3*x/(2*(d:ℝ))))^2 := by rw [hps]
    rw [h3]
    have h5 : (1:ℝ) - (1-(3*x/(2*(d:ℝ))))^2 = 2*(3*x/(2*(d:ℝ))) - (3*x/(2*(d:ℝ)))^2 := by ring
    rw [h5]
    have h6 : 2*(3*x/(2*(d:ℝ))) - (3*x/(2*(d:ℝ)))^2 ≤ 2*(3*x/(2*(d:ℝ))) := by
      nlinarith [sq_nonneg (3*x/(2*(d:ℝ)))]
    have h7 : x^2/(8*L) * (2*(3*x/(2*(d:ℝ)))) = 3*x^3/(8*(d:ℝ)*L) := by field_simp <;> ring
    have h8 : 3*x^3/(8*(d:ℝ)*L) ≤ 3473*L^2/(d:ℝ) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hx3, hLpos, hL1]
    have h9 : 3473*L^2/(d:ℝ) ≤ 0.15 := by
      rw [div_le_iff₀ hdrpos]
      nlinarith [h34730L2, hdrpos]
    calc x^2/(8*L) * (2*(3*x/(2*(d:ℝ))) - (3*x/(2*(d:ℝ)))^2)
        ≤ x^2/(8*L) * (2*(3*x/(2*(d:ℝ)))) := mul_le_mul_of_nonneg_left h6 (by positivity)
      _ = 3*x^3/(8*(d:ℝ)*L) := h7
      _ ≤ 3473*L^2/(d:ℝ) := h8
      _ ≤ 0.15 := h9
  have hbk : x^2*ps/(64*(d:ℝ)^2*L^2) ≤ 0.01 := by
    have h8 : x^2/(64*(d:ℝ)^2*L^2) ≤ 0.01 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hx.2, hL1, hdr2, hLpos, hdrpos]
    calc x^2*ps/(64*(d:ℝ)^2*L^2) = x^2/(64*(d:ℝ)^2*L^2) * ps := by ring
      _ ≤ x^2/(64*(d:ℝ)^2*L^2) * 1 := mul_le_mul_of_nonneg_left hps_le (by positivity)
      _ ≤ 0.01 := by rw [mul_one]; exact h8
  have hgoal : -shellB d x^2/(2*(K:ℝ)) ≤ 1.1 + -x^2/(8*L) := by
    have h0 : x^2*ps/(8*L) - x^2*ps/(64*(d:ℝ)^2*L^2) ≤ (shellB d x)^2/(2*(K:ℝ)) := by
      rw [hps]; exact hbnd
    have h3 : x^2/(8*L) - x^2*ps/(8*L) + x^2*ps/(64*(d:ℝ)^2*L^2) ≤ 1.1 := by
      linarith only [ha, hbk]
    have h2 : x^2/(8*L) - 1.1 ≤ x^2*ps/(8*L) - x^2*ps/(64*(d:ℝ)^2*L^2) := by
      linarith only [h3]
    have key : x^2/(8*L) - 1.1 ≤ (shellB d x)^2/(2*(K:ℝ)) := h2.trans h0
    have k2 := neg_le_neg key
    have k3 : -(x^2/(8*L) - 1.1) = 1.1 + -x^2/(8*L) := by ring
    have k4 : -((shellB d x)^2/(2*(K:ℝ))) = -shellB d x^2/(2*(K:ℝ)) := by ring
    rwa [k4, k3] at k2
  exact hgoal


/-- Region `[0,1]` of the four-region estimate. -/
lemma region0_le {d K : ℕ} {L : ℝ} {F : ℝ → ℝ} (hdr1 : 1 ≤ (d:ℝ))
    (hKle : (K:ℝ) ≤ 17*(d:ℝ)^2*L) (hLle : L ≤ 256*(d:ℝ))
    (hpt : ∀ x : ℝ, F ((d:ℝ)⁻¹*x+1) = (1 + x/(d:ℝ))^(d-1) *
        (∑ k ∈ Finset.Icc 1 K, (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ | shellB d x / Real.sqrt (k:ℝ) ≤ z}))
    (hFnn : ∀ x : ℝ, 0 ≤ x → 0 ≤ F ((d:ℝ)⁻¹*x+1))
    (hweight : ∀ x : ℝ, 0 ≤ x → (1 + x/(d:ℝ))^(d-1) ≤ Real.exp x)
    (hsumK : ∀ x : ℝ, (∑ k ∈ Finset.Icc 1 K, (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ | shellB d x / Real.sqrt (k:ℝ) ≤ z}) ≤ (K:ℝ))
    (hsumnn : ∀ x : ℝ, 0 ≤ ∑ k ∈ Finset.Icc 1 K, (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ | shellB d x / Real.sqrt (k:ℝ) ≤ z}) :
    ∫ x in (0:ℝ)..1, F ((d:ℝ)⁻¹ * x + 1) ≤ 5*10^4*(d:ℝ)^4 := by
  have hpoint0 : ∀ x ∈ Set.Ioc (0:ℝ) 1, F ((d:ℝ)⁻¹*x+1) ≤ Real.exp x * (K:ℝ) := by
    intro x hx
    have hx0 : 0 ≤ x := hx.1.le
    rw [hpt x]
    have h1 : (1 + x/(d:ℝ))^(d-1) ≤ Real.exp x := hweight x hx0
    exact mul_le_mul h1 (hsumK x) (hsumnn x) (Real.exp_pos x).le
  have hgi : IntegrableOn (fun x : ℝ => Real.exp x * (K:ℝ)) (Set.Ioc (0:ℝ) 1) volume :=
    integrableOn_Ioc_of_continuousOn (by fun_prop)
  have h1 : ∫ x in (0:ℝ)..1, F ((d:ℝ)⁻¹*x+1) ≤ ∫ x in (0:ℝ)..1, Real.exp x * (K:ℝ) :=
    integral_mono_of_nonneg_Ioc (by norm_num) (fun x hx => hFnn x hx.1.le) hgi hpoint0
  have h2 : ∫ x in (0:ℝ)..1, Real.exp x * (K:ℝ) = (Real.exp 1 - 1)*(K:ℝ) := by
    rw [intervalIntegral.integral_mul_const, integral_exp, Real.exp_zero]
  have h3 : (Real.exp 1 - 1)*(K:ℝ) ≤ 5*10^4*(d:ℝ)^4 := by
    have h4 : Real.exp 1 - 1 ≤ 1.72 := by linarith [Real.exp_one_lt_d9]
    have h5 : (K:ℝ) ≤ 17*(d:ℝ)^2*L := hKle
    have h7 : (Real.exp 1 - 1) * (K:ℝ) ≤ 1.72 * (17*(d:ℝ)^2*L) :=
      mul_le_mul h4 h5 (by positivity) (by norm_num)
    have h6 : 1.72*(17*(d:ℝ)^2*L) ≤ 5*10^4*(d:ℝ)^4 := by
      have h8 : 1.72*(17*(d:ℝ)^2*L) ≤ 1.72*(17*(d:ℝ)^2*(256*(d:ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_left hLle (by positivity)
      have h9 : 1.72*(17*(d:ℝ)^2*(256*(d:ℝ))) ≤ 5*10^4*(d:ℝ)^4 := by
        have hd4 : (d:ℝ)^3 ≤ (d:ℝ)^4 := pow_le_pow_right₀ hdr1 (by norm_num : 3 ≤ 4)
        have hd3 : (0:ℝ) ≤ (d:ℝ)^3 := by positivity
        nlinarith [hd4, hd3]
      linarith only [h8, h9]
    exact h7.trans h6
  exact h1.trans (h2.trans_le h3)

/-- Region `[1, 21 log d]` of the four-region estimate. -/
lemma region1_le {d K : ℕ} {F : ℝ → ℝ} {L : ℝ} (hLdef : L = Real.log (d:ℝ))
    (hdrpos : 0 < (d:ℝ)) (hdr1 : 1 ≤ (d:ℝ)) (hd2 : 2 ≤ d) (hL1 : 1 ≤ L) (h120L : 120*L ≤ (d:ℝ))
    (hLle : L ≤ 256*(d:ℝ)) (hLpos : 0 < L) (hKle : (K:ℝ) ≤ 17*(d:ℝ)^2*L)
    (hA1 : Real.sqrt (K:ℝ) ≤ 4.13*(d:ℝ)*Real.sqrt L)
    (hA2 : 2*(K:ℝ)^2*Real.sqrt (K:ℝ) ≤ 2400*(d:ℝ)^5*L^2*Real.sqrt L)
    (hC13 : (1/Real.sqrt (2*Real.pi)) * Real.exp 1.1 ≤ 1.3)
    (hL3sqL : L^3 * Real.sqrt L ≤ 128*(d:ℝ)) (hL2d : L^2 ≤ 16*Real.sqrt (d:ℝ))
    (hpt : ∀ x : ℝ, F ((d:ℝ)⁻¹ * x + 1) = (1 + x/(d:ℝ))^(d-1) *
        (∑ k ∈ Finset.Icc 1 K, (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ | shellB d x / Real.sqrt (k:ℝ) ≤ z}))
    (hsumnn : ∀ x : ℝ, 0 ≤ ∑ k ∈ Finset.Icc 1 K, (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ | shellB d x / Real.sqrt (k:ℝ) ≤ z})
    (hFnn : ∀ x : ℝ, 0 ≤ x → 0 ≤ F ((d:ℝ)⁻¹ * x + 1))
    (hweight : ∀ x : ℝ, 0 ≤ x → (1 + x/(d:ℝ))^(d-1) ≤ Real.exp x)
    (hshellBpos1 : ∀ x ∈ Set.Icc (1:ℝ) (21*L), 0 < shellB d x)
    (hshellBlow1 : ∀ x ∈ Set.Icc (1:ℝ) (21*L), (3/2)*x*(d:ℝ) ≤ shellB d x)
    (hsumSB : ∀ x : ℝ, 0 < shellB d x →
        (∑ k ∈ Finset.Icc 1 K, (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ | shellB d x / Real.sqrt (k:ℝ) ≤ z})
        ≤ (Real.sqrt (K:ℝ) * (shellB d x)⁻¹ + 2*(K:ℝ)^2*Real.sqrt (K:ℝ) * ((shellB d x)^3)⁻¹)
          * Real.exp (-((shellB d x)^2)/(2*(K:ℝ))) / Real.sqrt (2*Real.pi))
    (hsumK : ∀ x : ℝ, (∑ k ∈ Finset.Icc 1 K, (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ | shellB d x / Real.sqrt (k:ℝ) ≤ z}) ≤ (K:ℝ))
    (hexp1 : ∀ x ∈ Set.Icc (1:ℝ) (21*L),
        Real.exp (-(shellB d x)^2/(2*(K:ℝ))) ≤ Real.exp 1.1 * Real.exp (-(x^2)/(8*L)))
    (hXX4 : (Real.sqrt (Real.sqrt ((d:ℝ))))^4 = (d:ℝ)) :
    ∫ x in (1:ℝ)..(21*L), F ((d:ℝ)⁻¹ * x + 1) ≤ 5*10^5*(d:ℝ)^4 := by
  have hsqrt8 : Real.sqrt (8*Real.pi*L) ≤ 5.02*Real.sqrt L := by
    have h1 : Real.sqrt (8*Real.pi*L) = Real.sqrt (8*Real.pi) * Real.sqrt L := by
      rw [show (8:ℝ)*Real.pi*L = (8*Real.pi)*L by ring, Real.sqrt_mul (by positivity)]
    rw [h1]
    have h2 : Real.sqrt (8*Real.pi) ≤ 5.02 := by
      rw [Real.sqrt_le_iff]
      constructor
      · norm_num
      · nlinarith [Real.pi_lt_d6]
    exact mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg L)
  have hexpL2 : (Real.exp L)^2 = (d:ℝ)^2 := by
    rw [hLdef, Real.exp_log hdrpos]
  have hshellBposany : ∀ x : ℝ, 0 ≤ x → 0 < shellB d x :=
    fun x hx => mul_pos (shellA_pos hd2 hx) (by positivity)
  have hpoint : ∀ x ∈ Set.Ioc (1:ℝ) (21*L),
      F ((d:ℝ)⁻¹*x+1) ≤ 1.3 * (2.76*Real.sqrt L/x + 712*(d:ℝ)^2*L^2*Real.sqrt L/x^3)
        * Real.exp (x - x^2/(8*L)) := by
    intro x hx
    have hxI : x ∈ Set.Icc (1:ℝ) (21*L) := ⟨hx.1.le, hx.2⟩
    have hx0 : 0 ≤ x := by linarith [hx.1]
    rw [hpt x]
    have hw := hweight x hx0
    have hS := hsumSB x (hshellBpos1 x hxI)
    have hs0 := hsumnn x
    have hb := hshellBlow1 x hxI
    have hex := hexp1 x hxI
    have hbpos : (0:ℝ) < shellB d x := hshellBpos1 x hxI
    have hxpos : (0:ℝ) < x := by linarith [hx.1]
    have s1 : (1 + x/(d:ℝ))^(d-1) * (∑ k ∈ Finset.Icc 1 K,
          (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ | shellB d x / Real.sqrt (k:ℝ) ≤ z})
        ≤ Real.exp x * ((Real.sqrt (K:ℝ) * (shellB d x)⁻¹
            + 2*(K:ℝ)^2*Real.sqrt (K:ℝ) * ((shellB d x)^3)⁻¹)
            * Real.exp (-((shellB d x)^2)/(2*(K:ℝ))) / Real.sqrt (2*Real.pi)) :=
      (mul_le_mul_of_nonneg_right hw hs0).trans (mul_le_mul_of_nonneg_left hS (Real.exp_nonneg _))
    have s2 : Real.exp x * ((Real.sqrt (K:ℝ) * (shellB d x)⁻¹
            + 2*(K:ℝ)^2*Real.sqrt (K:ℝ) * ((shellB d x)^3)⁻¹)
            * Real.exp (-((shellB d x)^2)/(2*(K:ℝ))) / Real.sqrt (2*Real.pi))
        = (1/Real.sqrt (2*Real.pi)) * (Real.exp x * Real.exp (-((shellB d x)^2)/(2*(K:ℝ))))
          * (Real.sqrt (K:ℝ) * (shellB d x)⁻¹
            + 2*(K:ℝ)^2*Real.sqrt (K:ℝ) * ((shellB d x)^3)⁻¹) := by ring
    have s3 : Real.exp x * Real.exp (-((shellB d x)^2)/(2*(K:ℝ)))
        ≤ Real.exp 1.1 * Real.exp (x - x^2/(8*L)) := by
      have h1 : Real.exp 1.1 * Real.exp (x - x^2/(8*L))
          = Real.exp x * (Real.exp 1.1 * Real.exp (-(x^2)/(8*L))) := by
        rw [show x - x^2/(8*L) = x + -(x^2/(8*L)) by ring, Real.exp_add]
        ring
      rw [h1]
      exact mul_le_mul_of_nonneg_left hex (Real.exp_nonneg x)
    have s4 : Real.sqrt (K:ℝ) * (shellB d x)⁻¹
          + 2*(K:ℝ)^2*Real.sqrt (K:ℝ) * ((shellB d x)^3)⁻¹
        ≤ 2.76*Real.sqrt L/x + 712*(d:ℝ)^2*L^2*Real.sqrt L/x^3 := by
      have h1 : (shellB d x)⁻¹ ≤ ((3/2)*x*(d:ℝ))⁻¹ := by
        rw [inv_le_inv₀ hbpos (by positivity)]; exact hb
      have h2 : ((shellB d x)^3)⁻¹ ≤ (((3/2)*x*(d:ℝ))^3)⁻¹ := by
        rw [inv_le_inv₀ (by positivity) (by positivity)]
        exact pow_le_pow_left₀ (by positivity) hb 3
      have h3 : Real.sqrt (K:ℝ) * (shellB d x)⁻¹ ≤ 4.13*(d:ℝ)*Real.sqrt L * ((3/2)*x*(d:ℝ))⁻¹ :=
        mul_le_mul hA1 h1 (inv_nonneg.mpr hbpos.le) (by positivity)
      have h4 : 2*(K:ℝ)^2*Real.sqrt (K:ℝ) * ((shellB d x)^3)⁻¹
          ≤ 2400*(d:ℝ)^5*L^2*Real.sqrt L * (((3/2)*x*(d:ℝ))^3)⁻¹ :=
        mul_le_mul hA2 h2 (inv_nonneg.mpr (by positivity)) (by positivity)
      have h5 : 4.13*(d:ℝ)*Real.sqrt L * ((3/2)*x*(d:ℝ))⁻¹ = (4.13/(3/2))*Real.sqrt L/x := by
        field_simp
      have h5' : (4.13/(3/2))*Real.sqrt L/x ≤ 2.76*Real.sqrt L/x := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hxpos)
        have h9 : (4.13/(3/2):ℝ) ≤ 2.76 := by norm_num
        exact mul_le_mul_of_nonneg_right h9 (Real.sqrt_nonneg L)
      have h6 : 2400*(d:ℝ)^5*L^2*Real.sqrt L * (((3/2)*x*(d:ℝ))^3)⁻¹
          = (2400/((3/2)^3))*((d:ℝ)^2*L^2*Real.sqrt L)/x^3 := by
        field_simp
      have h6' : (2400/((3/2)^3))*((d:ℝ)^2*L^2*Real.sqrt L)/x^3
          ≤ 712*(d:ℝ)^2*L^2*Real.sqrt L/x^3 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have h7 : (0:ℝ) ≤ (d:ℝ)^2*L^2*Real.sqrt L :=
          mul_nonneg (mul_nonneg (sq_nonneg (d:ℝ)) (sq_nonneg L)) (Real.sqrt_nonneg L)
        nlinarith only [h7]
      linarith only [h3, h4, h5, h5', h6, h6']
    calc (1 + x/(d:ℝ))^(d-1) * (∑ k ∈ Finset.Icc 1 K,
            (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ | shellB d x / Real.sqrt (k:ℝ) ≤ z})
        ≤ (1/Real.sqrt (2*Real.pi)) * (Real.exp x * Real.exp (-((shellB d x)^2)/(2*(K:ℝ))))
          * (Real.sqrt (K:ℝ) * (shellB d x)⁻¹
            + 2*(K:ℝ)^2*Real.sqrt (K:ℝ) * ((shellB d x)^3)⁻¹) := s1.trans (le_of_eq s2)
      _ ≤ (1/Real.sqrt (2*Real.pi)) * (Real.exp 1.1 * Real.exp (x - x^2/(8*L)))
          * (2.76*Real.sqrt L/x + 712*(d:ℝ)^2*L^2*Real.sqrt L/x^3) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left s3 (by positivity)) s4 (by positivity)
          positivity
      _ = (1/Real.sqrt (2*Real.pi)) * Real.exp 1.1
          * (2.76*Real.sqrt L/x + 712*(d:ℝ)^2*L^2*Real.sqrt L/x^3) * Real.exp (x - x^2/(8*L)) := by ring
      _ ≤ 1.3 * (2.76*Real.sqrt L/x + 712*(d:ℝ)^2*L^2*Real.sqrt L/x^3)
          * Real.exp (x - x^2/(8*L)) := by
          have h2 : (0:ℝ) ≤ 2.76*Real.sqrt L/x + 712*(d:ℝ)^2*L^2*Real.sqrt L/x^3 := by positivity
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC13 h2) (Real.exp_nonneg _)
  have hbnd_int : IntegrableOn (fun x : ℝ => 1.3 * (2.76*Real.sqrt L/x + 712*(d:ℝ)^2*L^2*Real.sqrt L/x^3)
      * Real.exp (x - x^2/(8*L))) (Set.Ioc (1:ℝ) (21*L)) volume := by
    refine IntegrableOn.of_bound (measure_Ioc_lt_top) ?_ (1.3 * (2.76*Real.sqrt L + 712*(d:ℝ)^2*L^2*Real.sqrt L) * (d:ℝ)^2) ?_
    · exact (by fun_prop : Measurable (fun x : ℝ =>
          1.3 * (2.76*Real.sqrt L/x + 712*(d:ℝ)^2*L^2*Real.sqrt L/x^3)
            * Real.exp (x - x^2/(8*L)))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have hx1 : (1:ℝ) ≤ x := hx.1.le
      have hx2 : x ≤ 21*L := hx.2
      have h4 : Real.exp (x - x^2/(8*L)) ≤ (d:ℝ)^2 := by
        have h5 : x - x^2/(8*L) ≤ 2*L := by
          have hid : x - x^2/(8*L) - 2*L = -(((x-4*L)^2)/(8*L)) := by field_simp <;> ring
          have h7 : (0:ℝ) ≤ ((x-4*L)^2)/(8*L) := div_nonneg (sq_nonneg _) (by positivity)
          linarith only [hid, h7]
        have h6 : Real.exp (2*L) = (d:ℝ)^2 := by
          simpa [hexpL2] using Real.exp_nat_mul L 2
        calc Real.exp (x - x^2/(8*L)) ≤ Real.exp (2*L) := Real.exp_le_exp.mpr h5
          _ = (d:ℝ)^2 := h6
      have h7 : 1/x ≤ 1 := by
        rw [div_le_one (by linarith [hx1])]; exact hx1
      have h8 : 1/x^3 ≤ 1 := by
        have hx0 : (0:ℝ) < x := by linarith [hx1]
        rw [div_le_one (by positivity)]
        have hp : (1:ℝ)^3 ≤ x^3 := pow_le_pow_left₀ (by norm_num) hx1 3
        norm_num at hp
        exact hp
      have h9 : (0:ℝ) ≤ 2.76*Real.sqrt L/x + 712*(d:ℝ)^2*L^2*Real.sqrt L/x^3 := by positivity
      have h10 : (0:ℝ) ≤ Real.exp (x - x^2/(8*L)) := Real.exp_nonneg _
      have h11 : Real.sqrt L/x ≤ Real.sqrt L := by
        calc Real.sqrt L/x = Real.sqrt L * (1/x) := by ring
          _ ≤ Real.sqrt L * 1 := mul_le_mul_of_nonneg_left h7 (Real.sqrt_nonneg L)
          _ = Real.sqrt L := by ring
      have h12 : (d:ℝ)^2*L^2*Real.sqrt L/x^3 ≤ (d:ℝ)^2*L^2*Real.sqrt L := by
        calc (d:ℝ)^2*L^2*Real.sqrt L/x^3 = ((d:ℝ)^2*L^2*Real.sqrt L) * (1/x^3) := by ring
          _ ≤ ((d:ℝ)^2*L^2*Real.sqrt L) * 1 := mul_le_mul_of_nonneg_left h8 (by positivity)
          _ = ((d:ℝ)^2*L^2*Real.sqrt L) := by ring
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc 1.3 * (2.76*Real.sqrt L/x + 712*(d:ℝ)^2*L^2*Real.sqrt L/x^3) * Real.exp (x - x^2/(8*L))
          ≤ 1.3 * (2.76*Real.sqrt L + 712*(d:ℝ)^2*L^2*Real.sqrt L) * Real.exp (x - x^2/(8*L)) := by
            apply mul_le_mul_of_nonneg_right _ h10
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            have h13 : 2.76 * (Real.sqrt L/x) ≤ 2.76 * Real.sqrt L :=
              mul_le_mul_of_nonneg_left h11 (by norm_num)
            have h13' : 2.76 * Real.sqrt L/x = 2.76 * (Real.sqrt L/x) := by ring
            have h14 : 712 * ((d:ℝ)^2*L^2*Real.sqrt L/x^3) ≤ 712 * ((d:ℝ)^2*L^2*Real.sqrt L) :=
              mul_le_mul_of_nonneg_left h12 (by norm_num)
            have h14' : 712*(d:ℝ)^2*L^2*Real.sqrt L/x^3 = 712 * ((d:ℝ)^2*L^2*Real.sqrt L/x^3) := by ring
            linarith only [h13, h13', h14, h14']
        _ ≤ 1.3 * (2.76*Real.sqrt L + 712*(d:ℝ)^2*L^2*Real.sqrt L) * (d:ℝ)^2 :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
  have hcontx : ContinuousOn (fun x : ℝ => Real.exp (x - x^2/(8*L))/x) (Set.Icc (1:ℝ) (21*L)) := by
    apply ContinuousOn.div
    · exact Real.continuous_exp.continuousOn.comp (ContinuousOn.sub continuousOn_id
        (ContinuousOn.div_const (continuousOn_id.pow 2) (8*L))) (fun x _ => Set.mem_univ _)
    · exact continuousOn_id
    · intro x hx; exact ne_of_gt (by linarith [hx.1])
  have hcontx3 : ContinuousOn (fun x : ℝ => Real.exp (x - x^2/(8*L))/x^3) (Set.Icc (1:ℝ) (21*L)) := by
    apply ContinuousOn.div
    · exact Real.continuous_exp.continuousOn.comp (ContinuousOn.sub continuousOn_id
        (ContinuousOn.div_const (continuousOn_id.pow 2) (8*L))) (fun x _ => Set.mem_univ _)
    · exact continuousOn_id.pow 3
    · intro x hx; exact pow_ne_zero 3 (by linarith [hx.1] : x ≠ 0)
  have hint1 : IntervalIntegrable (fun x : ℝ => Real.exp (x - x^2/(8*L))/x) volume (1:ℝ) (21*L) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith [hL1])]
    exact hcontx
  have hint3 : IntervalIntegrable (fun x : ℝ => Real.exp (x - x^2/(8*L))/x^3) volume (1:ℝ) (21*L) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith [hL1])]
    exact hcontx3
  have hIx : ∫ x in (1:ℝ)..(21*L), Real.exp (x - x^2/(8*L))/x ≤ L*(d:ℝ) + 5.02*(d:ℝ)^2/Real.sqrt L := by
    have hsp1 : IntervalIntegrable (fun x : ℝ => Real.exp (x - x^2/(8*L))/x) volume (1:ℝ) L :=
      hint1.mono_set (by
        rw [Set.uIcc_of_le (by linarith [hL1]), Set.uIcc_of_le (by linarith [hL1])]
        exact Set.Icc_subset_Icc le_rfl (by linarith [hL1]))
    have hsp2 : IntervalIntegrable (fun x : ℝ => Real.exp (x - x^2/(8*L))/x) volume L (21*L) :=
      hint1.mono_set (by
        rw [Set.uIcc_of_le (by linarith [hL1]), Set.uIcc_of_le (by linarith [hL1])]
        exact Set.Icc_subset_Icc (by linarith [hL1]) le_rfl)
    rw [← intervalIntegral.integral_add_adjacent_intervals hsp1 hsp2]
    have hA : ∫ x in (1:ℝ)..L, Real.exp (x - x^2/(8*L))/x ≤ L*(d:ℝ) := by
      have hb : ∀ x ∈ Set.Ioc (1:ℝ) L, Real.exp (x - x^2/(8*L))/x ≤ (d:ℝ) := by
        intro x hx
        have hx1 : (1:ℝ) ≤ x := hx.1.le
        have h5 : Real.exp (x - x^2/(8*L)) ≤ (d:ℝ) := by
          have h6 : x - x^2/(8*L) ≤ L := by
            have h7 : (0:ℝ) ≤ x^2/(8*L) := by positivity
            linarith only [hx.2, h7]
          calc Real.exp (x - x^2/(8*L)) ≤ Real.exp L := Real.exp_le_exp.mpr h6
            _ = (d:ℝ) := by rw [hLdef, Real.exp_log hdrpos]
        have h7 : 1/x ≤ 1 := by rw [div_le_one (by linarith [hx.1])]; exact hx1
        have h8 : (0:ℝ) ≤ 1/x := by
          have h0 : (0:ℝ) < x := by linarith [hx.1]
          positivity
        calc Real.exp (x - x^2/(8*L))/x = Real.exp (x - x^2/(8*L)) * (1/x) := by ring
          _ ≤ (d:ℝ) * 1 := mul_le_mul h5 h7 h8 (le_of_lt hdrpos)
          _ = (d:ℝ) := by ring
      calc ∫ x in (1:ℝ)..L, Real.exp (x - x^2/(8*L))/x ≤ ∫ x in (1:ℝ)..L, (d:ℝ) :=
            integral_mono_of_nonneg_Ioc (by linarith [hL1])
              (fun x hx => le_of_lt (div_pos (Real.exp_pos _) (by linarith [hx.1])))
              (integrableOn_Ioc_of_continuousOn continuousOn_const) hb
        _ = (L - 1)*(d:ℝ) := by rw [intervalIntegral.integral_const]; simp
        _ ≤ L*(d:ℝ) := by nlinarith [hdrpos]
    have hB : ∫ x in L..(21*L), Real.exp (x - x^2/(8*L))/x ≤ 5.02*(d:ℝ)^2/Real.sqrt L := by
      have hb : ∀ x ∈ Set.Ioc L (21*L), Real.exp (x - x^2/(8*L))/x
          ≤ (1/L) * Real.exp (x - x^2/(8*L)) := by
        intro x hx
        have h1 : (0:ℝ) < x := by linarith [hx.1, hL1]
        have h2 : 1/x ≤ 1/L := by rw [div_le_div_iff₀ h1 hLpos]; linarith [hx.1]
        calc Real.exp (x - x^2/(8*L))/x = Real.exp (x - x^2/(8*L)) * (1/x) := by ring
          _ ≤ Real.exp (x - x^2/(8*L)) * (1/L) := mul_le_mul_of_nonneg_left h2 (Real.exp_nonneg _)
          _ = (1/L) * Real.exp (x - x^2/(8*L)) := by ring
      have h1 : ∫ x in L..(21*L), Real.exp (x - x^2/(8*L))/x
          ≤ ∫ x in L..(21*L), (1/L)*Real.exp (x - x^2/(8*L)) :=
        integral_mono_of_nonneg_Ioc (by linarith [hL1])
          (fun x hx => le_of_lt (div_pos (Real.exp_pos _) (by linarith [hx.1, hL1])))
          (integrableOn_Ioc_of_continuousOn (ContinuousOn.mul continuousOn_const
            (Real.continuous_exp.continuousOn.comp
              (ContinuousOn.sub continuousOn_id
                (ContinuousOn.div_const (continuousOn_id.pow 2) (8*L)))
              (fun x _ => Set.mem_univ _)))) hb
      have h2 : ∫ x in L..(21*L), (1/L)*Real.exp (x - x^2/(8*L))
          ≤ (1/L) * (Real.sqrt (8*Real.pi*L) * (Real.exp L)^2) := by
        rw [intervalIntegral.integral_const_mul]
        exact mul_le_mul_of_nonneg_left (integral_exp_sub_sq_div_Icc_le L L (21*L) hLpos (by linarith [hL1])) (by positivity)
      have h3 : (1/L) * (Real.sqrt (8*Real.pi*L) * (Real.exp L)^2) ≤ 5.02*(d:ℝ)^2/Real.sqrt L := by
        rw [hexpL2]
        have h5 : (1/L) * ((5.02*Real.sqrt L) * (d:ℝ)^2) = 5.02*(d:ℝ)^2/Real.sqrt L := by
          have hLL : Real.sqrt L/L = 1/Real.sqrt L := by
            rw [div_eq_div_iff (ne_of_gt hLpos) (ne_of_gt (Real.sqrt_pos_of_pos hLpos))]
            rw [one_mul]
            simpa [pow_two] using Real.sq_sqrt (le_of_lt hLpos)
          calc (1/L) * ((5.02*Real.sqrt L) * (d:ℝ)^2) = 5.02*(d:ℝ)^2 * (Real.sqrt L/L) := by ring
            _ = 5.02*(d:ℝ)^2 * (1/Real.sqrt L) := by rw [hLL]
            _ = 5.02*(d:ℝ)^2/Real.sqrt L := by ring
        calc (1/L) * (Real.sqrt (8*Real.pi*L) * (d:ℝ)^2)
            ≤ (1/L) * ((5.02*Real.sqrt L) * (d:ℝ)^2) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact mul_le_mul_of_nonneg_right hsqrt8 (by positivity)
          _ = 5.02*(d:ℝ)^2/Real.sqrt L := h5
      linarith only [h1, h2, h3]
    linarith only [hA, hB]
  have hIx3 : ∫ x in (1:ℝ)..(21*L), Real.exp (x - x^2/(8*L))/x^3
      ≤ L*(d:ℝ) + 5.02*(d:ℝ)^2/(L^2*Real.sqrt L) := by
    have hsp1 : IntervalIntegrable (fun x : ℝ => Real.exp (x - x^2/(8*L))/x^3) volume (1:ℝ) L :=
      hint3.mono_set (by
        rw [Set.uIcc_of_le (by linarith [hL1]), Set.uIcc_of_le (by linarith [hL1])]
        exact Set.Icc_subset_Icc le_rfl (by linarith [hL1]))
    have hsp2 : IntervalIntegrable (fun x : ℝ => Real.exp (x - x^2/(8*L))/x^3) volume L (21*L) :=
      hint3.mono_set (by
        rw [Set.uIcc_of_le (by linarith [hL1]), Set.uIcc_of_le (by linarith [hL1])]
        exact Set.Icc_subset_Icc (by linarith [hL1]) le_rfl)
    rw [← intervalIntegral.integral_add_adjacent_intervals hsp1 hsp2]
    have hA : ∫ x in (1:ℝ)..L, Real.exp (x - x^2/(8*L))/x^3 ≤ L*(d:ℝ) := by
      have hb : ∀ x ∈ Set.Ioc (1:ℝ) L, Real.exp (x - x^2/(8*L))/x^3 ≤ (d:ℝ) := by
        intro x hx
        have hx1 : (1:ℝ) ≤ x := hx.1.le
        have h5 : Real.exp (x - x^2/(8*L)) ≤ (d:ℝ) := by
          have h6 : x - x^2/(8*L) ≤ L := by
            have h7 : (0:ℝ) ≤ x^2/(8*L) := by positivity
            linarith only [hx.2, h7]
          calc Real.exp (x - x^2/(8*L)) ≤ Real.exp L := Real.exp_le_exp.mpr h6
            _ = (d:ℝ) := by rw [hLdef, Real.exp_log hdrpos]
        have h7 : 1/x^3 ≤ 1 := by
          have h0 : (0:ℝ) < x := by linarith [hx.1]
          rw [div_le_one (by positivity)]
          have hp : (1:ℝ)^3 ≤ x^3 := pow_le_pow_left₀ (by norm_num) hx1 3
          simpa using hp
        have h8 : (0:ℝ) ≤ 1/x^3 := by
          have h0 : (0:ℝ) < x := by linarith [hx.1]
          positivity
        calc Real.exp (x - x^2/(8*L))/x^3 = Real.exp (x - x^2/(8*L)) * (1/x^3) := by ring
          _ ≤ (d:ℝ) * 1 := mul_le_mul h5 h7 h8 (le_of_lt hdrpos)
          _ = (d:ℝ) := by ring
      calc ∫ x in (1:ℝ)..L, Real.exp (x - x^2/(8*L))/x^3 ≤ ∫ x in (1:ℝ)..L, (d:ℝ) :=
            integral_mono_of_nonneg_Ioc (by linarith [hL1])
              (fun x hx => le_of_lt (div_pos (Real.exp_pos _)
                (pow_pos (by linarith [hx.1]) 3)))
              (integrableOn_Ioc_of_continuousOn continuousOn_const) hb
        _ = (L - 1)*(d:ℝ) := by rw [intervalIntegral.integral_const]; simp
        _ ≤ L*(d:ℝ) := by nlinarith [hdrpos]
    have hB : ∫ x in L..(21*L), Real.exp (x - x^2/(8*L))/x^3 ≤ 5.02*(d:ℝ)^2/(L^2*Real.sqrt L) := by
      have hb : ∀ x ∈ Set.Ioc L (21*L), Real.exp (x - x^2/(8*L))/x^3
          ≤ (1/L^3) * Real.exp (x - x^2/(8*L)) := by
        intro x hx
        have h1 : (0:ℝ) < x := by linarith [hx.1, hL1]
        have h2 : 1/x^3 ≤ 1/L^3 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          simpa using pow_le_pow_left₀ (le_of_lt hLpos) (le_of_lt hx.1) 3
        calc Real.exp (x - x^2/(8*L))/x^3 = Real.exp (x - x^2/(8*L)) * (1/x^3) := by ring
          _ ≤ Real.exp (x - x^2/(8*L)) * (1/L^3) := mul_le_mul_of_nonneg_left h2 (Real.exp_nonneg _)
          _ = (1/L^3) * Real.exp (x - x^2/(8*L)) := by ring
      have h1 : ∫ x in L..(21*L), Real.exp (x - x^2/(8*L))/x^3
          ≤ ∫ x in L..(21*L), (1/L^3)*Real.exp (x - x^2/(8*L)) :=
        integral_mono_of_nonneg_Ioc (by linarith [hL1])
          (fun x hx => le_of_lt (div_pos (Real.exp_pos _) (pow_pos (by linarith [hx.1]) 3)))
          (integrableOn_Ioc_of_continuousOn (ContinuousOn.mul continuousOn_const
            (Real.continuous_exp.continuousOn.comp
              (ContinuousOn.sub continuousOn_id
                (ContinuousOn.div_const (continuousOn_id.pow 2) (8*L)))
              (fun x _ => Set.mem_univ _)))) hb
      have h2 : ∫ x in L..(21*L), (1/L^3)*Real.exp (x - x^2/(8*L))
          ≤ (1/L^3) * (Real.sqrt (8*Real.pi*L) * (Real.exp L)^2) := by
        rw [intervalIntegral.integral_const_mul]
        exact mul_le_mul_of_nonneg_left (integral_exp_sub_sq_div_Icc_le L L (21*L) hLpos (by linarith [hL1])) (by positivity)
      have h3 : (1/L^3) * (Real.sqrt (8*Real.pi*L) * (Real.exp L)^2) ≤ 5.02*(d:ℝ)^2/(L^2*Real.sqrt L) := by
        rw [hexpL2]
        have h5 : (1/L^3) * ((5.02*Real.sqrt L) * (d:ℝ)^2) = 5.02*(d:ℝ)^2/(L^2*Real.sqrt L) := by
          have hLL : Real.sqrt L/L = 1/Real.sqrt L := by
            rw [div_eq_div_iff (ne_of_gt hLpos) (ne_of_gt (Real.sqrt_pos_of_pos hLpos))]
            rw [one_mul]
            simpa [pow_two] using Real.sq_sqrt (le_of_lt hLpos)
          calc (1/L^3) * ((5.02*Real.sqrt L) * (d:ℝ)^2)
              = 5.02*(d:ℝ)^2 * (Real.sqrt L/L) / L^2 := by ring
            _ = 5.02*(d:ℝ)^2 * (1/Real.sqrt L) / L^2 := by rw [hLL]
            _ = 5.02*(d:ℝ)^2/(L^2*Real.sqrt L) := by ring
        calc (1/L^3) * (Real.sqrt (8*Real.pi*L) * (d:ℝ)^2)
            ≤ (1/L^3) * ((5.02*Real.sqrt L) * (d:ℝ)^2) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact mul_le_mul_of_nonneg_right hsqrt8 (by positivity)
          _ = 5.02*(d:ℝ)^2/(L^2*Real.sqrt L) := h5
      linarith only [h1, h2, h3]
    linarith only [hA, hB]
  have hstep1 : ∫ x in (1:ℝ)..(21*L), F ((d:ℝ)⁻¹*x+1)
      ≤ ∫ x in (1:ℝ)..(21*L), 1.3 * (2.76*Real.sqrt L/x + 712*(d:ℝ)^2*L^2*Real.sqrt L/x^3)
          * Real.exp (x - x^2/(8*L)) :=
    integral_mono_of_nonneg_Ioc (by linarith [hL1]) (fun x hx => hFnn x (by linarith [hx.1]))
      hbnd_int hpoint
  have hlin : ∫ x in (1:ℝ)..(21*L), 1.3 * (2.76*Real.sqrt L/x + 712*(d:ℝ)^2*L^2*Real.sqrt L/x^3) * Real.exp (x - x^2/(8*L))
      = 1.3 * (2.76*Real.sqrt L * (∫ x in (1:ℝ)..(21*L), Real.exp (x - x^2/(8*L))/x)
          + 712*(d:ℝ)^2*L^2*Real.sqrt L * (∫ x in (1:ℝ)..(21*L), Real.exp (x - x^2/(8*L))/x^3)) := by
    have hEq : ∫ x in (1:ℝ)..(21*L), 1.3 * (2.76*Real.sqrt L/x + 712*(d:ℝ)^2*L^2*Real.sqrt L/x^3) * Real.exp (x - x^2/(8*L))
        = ∫ x in (1:ℝ)..(21*L), 1.3 * (2.76*Real.sqrt L * (Real.exp (x - x^2/(8*L))/x)
            + 712*(d:ℝ)^2*L^2*Real.sqrt L * (Real.exp (x - x^2/(8*L))/x^3)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      ring
    have hiX : IntervalIntegrable (fun x : ℝ => 2.76*Real.sqrt L * (Real.exp (x - x^2/(8*L))/x))
        volume (1:ℝ) (21*L) := hint1.const_mul _
    have hiY : IntervalIntegrable (fun x : ℝ => 712*(d:ℝ)^2*L^2*Real.sqrt L * (Real.exp (x - x^2/(8*L))/x^3))
        volume (1:ℝ) (21*L) := hint3.const_mul _
    rw [hEq, intervalIntegral.integral_const_mul, intervalIntegral.integral_add hiX hiY,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hstep2 : ∫ x in (1:ℝ)..(21*L), 1.3 * (2.76*Real.sqrt L/x + 712*(d:ℝ)^2*L^2*Real.sqrt L/x^3) * Real.exp (x - x^2/(8*L))
      ≤ 1.3 * (2.76*Real.sqrt L * (L*(d:ℝ) + 5.02*(d:ℝ)^2/Real.sqrt L)
          + 712*(d:ℝ)^2*L^2*Real.sqrt L * (L*(d:ℝ) + 5.02*(d:ℝ)^2/(L^2*Real.sqrt L))) := by
    rw [hlin]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left hIx (by positivity)
    · exact mul_le_mul_of_nonneg_left hIx3 (by positivity)
  have hstep3 : 1.3 * (2.76*Real.sqrt L * (L*(d:ℝ) + 5.02*(d:ℝ)^2/Real.sqrt L)
          + 712*(d:ℝ)^2*L^2*Real.sqrt L * (L*(d:ℝ) + 5.02*(d:ℝ)^2/(L^2*Real.sqrt L))) ≤ 5*10^5*(d:ℝ)^4 := by
    have h2 : Real.sqrt L * (5.02*(d:ℝ)^2/Real.sqrt L) = 5.02*(d:ℝ)^2 := by
      have h9 : Real.sqrt L ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos hLpos)
      field_simp
    have h4 : (d:ℝ)^2*L^2*Real.sqrt L * (5.02*(d:ℝ)^2/(L^2*Real.sqrt L)) = 5.02*(d:ℝ)^4 := by
      have h9 : Real.sqrt L ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos hLpos)
      have h10 : L ≠ 0 := ne_of_gt hLpos
      field_simp
    have hAd : Real.sqrt L * (L*(d:ℝ)) ≤ 16*(d:ℝ)^2 := by
      have h1 : Real.sqrt L * (L*(d:ℝ)) ≤ L^2*(d:ℝ) := by
        have h3 : Real.sqrt L ≤ L := by
          nlinarith [Real.sq_sqrt (le_of_lt hLpos), Real.sqrt_nonneg L, hLpos, hL1]
        calc Real.sqrt L * (L*(d:ℝ)) ≤ L * (L*(d:ℝ)) := mul_le_mul_of_nonneg_right h3 (by positivity)
          _ = L^2*(d:ℝ) := by ring
      have hA : L^2*(d:ℝ) ≤ 16*(Real.sqrt (d:ℝ))*(d:ℝ) := mul_le_mul_of_nonneg_right hL2d hdrpos.le
      have hB : (16:ℝ)*(Real.sqrt (d:ℝ))*(d:ℝ) ≤ 16*(Real.sqrt (d:ℝ))*(Real.sqrt (d:ℝ))*(d:ℝ) := by
        have h1d : (1:ℝ) ≤ Real.sqrt (d:ℝ) := Real.one_le_sqrt.mpr hdr1
        have hpos : (0:ℝ) ≤ (16:ℝ)*(Real.sqrt (d:ℝ))*(d:ℝ) := by positivity
        have h2' : (16:ℝ)*(Real.sqrt (d:ℝ))*(d:ℝ) * 1 ≤ (16:ℝ)*(Real.sqrt (d:ℝ))*(d:ℝ) * Real.sqrt (d:ℝ) :=
          mul_le_mul_of_nonneg_left h1d hpos
        linarith only [h2']
      have hsdd : Real.sqrt (d:ℝ) * Real.sqrt (d:ℝ) = (d:ℝ) := by
        rw [show Real.sqrt (d:ℝ)*Real.sqrt (d:ℝ) = (Real.sqrt (d:ℝ))^2 by ring,
          Real.sq_sqrt (le_of_lt hdrpos)]
      calc Real.sqrt L * (L*(d:ℝ)) ≤ L^2*(d:ℝ) := h1
        _ ≤ 16*(Real.sqrt (d:ℝ))*(Real.sqrt (d:ℝ))*(d:ℝ) := by linarith only [hA, hB]
        _ = 16*(d:ℝ)^2 := by
            rw [show (16:ℝ)*(Real.sqrt (d:ℝ))*(Real.sqrt (d:ℝ))*(d:ℝ)
              = 16*((Real.sqrt (d:ℝ))*(Real.sqrt (d:ℝ)))*(d:ℝ) by ring, hsdd]
            ring
    have hBd : L^3 * Real.sqrt L * (d:ℝ)^3 ≤ 128*(d:ℝ)^4 := by
      have h5 : L^3 * Real.sqrt L * (d:ℝ) ≤ 128*(d:ℝ)^2 := by
        calc L^3 * Real.sqrt L * (d:ℝ) ≤ (128*(d:ℝ)) * (d:ℝ) := mul_le_mul_of_nonneg_right hL3sqL hdrpos.le
          _ = 128*(d:ℝ)^2 := by ring
      have h6 : L^3 * Real.sqrt L * (d:ℝ) * (d:ℝ)^2 ≤ 128*(d:ℝ)^2 * (d:ℝ)^2 :=
        mul_le_mul_of_nonneg_right h5 (by positivity)
      calc L^3 * Real.sqrt L * (d:ℝ)^3 = L^3 * Real.sqrt L * (d:ℝ) * (d:ℝ)^2 := by ring
        _ ≤ 128*(d:ℝ)^2 * (d:ℝ)^2 := h6
        _ = 128*(d:ℝ)^4 := by ring
    have hd2 : (d:ℝ)^2*L^2*Real.sqrt L * (L*(d:ℝ)) = L^3 * Real.sqrt L * (d:ℝ)^3 := by ring
    have hexp : 1.3 * (2.76 * Real.sqrt L * (L*(d:ℝ) + 5.02*(d:ℝ)^2/Real.sqrt L)
        + 712*(d:ℝ)^2*L^2*Real.sqrt L * (L*(d:ℝ) + 5.02*(d:ℝ)^2/(L^2*Real.sqrt L)))
        = 1.3 * (2.76*(Real.sqrt L * (L*(d:ℝ))) + 2.76*(Real.sqrt L * (5.02*(d:ℝ)^2/Real.sqrt L))
          + 712*((d:ℝ)^2*L^2*Real.sqrt L * (L*(d:ℝ)))
          + 712*((d:ℝ)^2*L^2*Real.sqrt L * (5.02*(d:ℝ)^2/(L^2*Real.sqrt L)))) := by ring
    rw [hexp, h2, h4, hd2]
    have hd2le : (d:ℝ)^2 ≤ (d:ℝ)^4 := by
      have hsq : (1:ℝ) ≤ (d:ℝ)^2 := by nlinarith [hdr1]
      calc (d:ℝ)^2 = (d:ℝ)^2 * 1 := by ring
        _ ≤ (d:ℝ)^2 * (d:ℝ)^2 := mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = (d:ℝ)^4 := by ring
    have h6 : 5.02*(d:ℝ)^2 ≤ 5.02*(d:ℝ)^4 := mul_le_mul_of_nonneg_left hd2le (by norm_num)
    nlinarith only [hAd, hBd, h6, hd2le, hdrpos]
  linarith only [hstep1, hstep2, hstep3]

lemma region2_le {d K : ℕ} {L : ℝ} {F : ℝ → ℝ} (hdrpos : 0 < (d:ℝ)) (hdr1 : 1 ≤ (d:ℝ))
    (hLpos : 0 < L) (hL1 : 1 ≤ L) (h120L : 120*L ≤ (d:ℝ))
    (hA1 : Real.sqrt (K:ℝ) ≤ 4.13*(d:ℝ)*Real.sqrt L)
    (hA2 : 2*(K:ℝ)^2*Real.sqrt (K:ℝ) ≤ 2400*(d:ℝ)^5*L^2*Real.sqrt L)
    (hpt : ∀ x : ℝ, F ((d:ℝ)⁻¹*x+1) = (1 + x/(d:ℝ))^(d-1) *
        (∑ k ∈ Finset.Icc 1 K, (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ | shellB d x / Real.sqrt (k:ℝ) ≤ z}))
    (hFnn : ∀ x : ℝ, 0 ≤ x → 0 ≤ F ((d:ℝ)⁻¹*x+1))
    (hweight : ∀ x : ℝ, 0 ≤ x → (1 + x/(d:ℝ))^(d-1) ≤ Real.exp x)
    (hsumnn : ∀ x : ℝ, 0 ≤ ∑ k ∈ Finset.Icc 1 K, (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ | shellB d x / Real.sqrt (k:ℝ) ≤ z})
    (hsumSB : ∀ x : ℝ, 0 < shellB d x →
        (∑ k ∈ Finset.Icc 1 K, (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ | shellB d x / Real.sqrt (k:ℝ) ≤ z})
        ≤ (Real.sqrt (K:ℝ) * (shellB d x)⁻¹ + 2*(K:ℝ)^2*Real.sqrt (K:ℝ) * ((shellB d x)^3)⁻¹)
          * Real.exp (-((shellB d x)^2)/(2*(K:ℝ))) / Real.sqrt (2*Real.pi))
    (hshellBposany : ∀ x : ℝ, 0 ≤ x → 0 < shellB d x)
    (hshellBlow2c : ∀ x ∈ Set.Icc (21*L) ((d:ℝ)/2), 10*L*(d:ℝ) ≤ shellB d x)
    (hexp2 : ∀ x ∈ Set.Icc (21*L) ((d:ℝ)/2), x ≤ (shellB d x)^2/(2*(K:ℝ))) :
    ∫ x in (21*L)..((d:ℝ)/2), F ((d:ℝ)⁻¹ * x + 1) ≤ 5*10^4*(d:ℝ)^4 := by
  have hpoint : ∀ x ∈ Set.Ioc (21*L) ((d:ℝ)/2),
      F ((d:ℝ)⁻¹*x+1) ≤ (1/Real.sqrt (2*Real.pi)) * (0.413 + 2.4*(d:ℝ)^2) := by
    intro x hx
    have hxI : x ∈ Set.Icc (21*L) ((d:ℝ)/2) := ⟨hx.1.le, hx.2⟩
    have hx0 : 0 ≤ x := by linarith [hx.1, hL1]
    rw [hpt x]
    have hw := hweight x hx0
    have hs0 := hsumnn x
    have hS := hsumSB x (hshellBposany x hx0)
    have hex := hexp2 x hxI
    have hb := hshellBlow2c x hxI
    have hbpos : (0:ℝ) < shellB d x := hshellBposany x hx0
    have s1 : (1 + x/(d:ℝ))^(d-1) * (∑ k ∈ Finset.Icc 1 K,
          (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ | shellB d x / Real.sqrt (k:ℝ) ≤ z})
        ≤ Real.exp x * ((Real.sqrt (K:ℝ) * (shellB d x)⁻¹
            + 2*(K:ℝ)^2*Real.sqrt (K:ℝ) * ((shellB d x)^3)⁻¹)
            * Real.exp (-((shellB d x)^2)/(2*(K:ℝ))) / Real.sqrt (2*Real.pi)) :=
      (mul_le_mul_of_nonneg_right hw hs0).trans (mul_le_mul_of_nonneg_left hS (Real.exp_nonneg _))
    have s2 : Real.exp x * ((Real.sqrt (K:ℝ) * (shellB d x)⁻¹
            + 2*(K:ℝ)^2*Real.sqrt (K:ℝ) * ((shellB d x)^3)⁻¹)
            * Real.exp (-((shellB d x)^2)/(2*(K:ℝ))) / Real.sqrt (2*Real.pi))
        = (1/Real.sqrt (2*Real.pi)) * (Real.exp x * Real.exp (-((shellB d x)^2)/(2*(K:ℝ))))
          * (Real.sqrt (K:ℝ) * (shellB d x)⁻¹
            + 2*(K:ℝ)^2*Real.sqrt (K:ℝ) * ((shellB d x)^3)⁻¹) := by ring
    have s3 : Real.exp x * Real.exp (-((shellB d x)^2)/(2*(K:ℝ))) ≤ 1 := by
      have h2 : (-((shellB d x)^2))/(2*(K:ℝ)) = -((shellB d x)^2/(2*(K:ℝ))) := by ring
      rw [h2, ← Real.exp_add, Real.exp_le_one_iff]
      linarith only [hex]
    have s4 : Real.sqrt (K:ℝ) * (shellB d x)⁻¹
          + 2*(K:ℝ)^2*Real.sqrt (K:ℝ) * ((shellB d x)^3)⁻¹
        ≤ 0.413 + 2.4*(d:ℝ)^2 := by
      have h1 : (shellB d x)⁻¹ ≤ (10*L*(d:ℝ))⁻¹ := by
        rw [inv_le_inv₀ hbpos (by positivity)]; exact hb
      have h2 : ((shellB d x)^3)⁻¹ ≤ ((10*L*(d:ℝ))^3)⁻¹ := by
        rw [inv_le_inv₀ (by positivity) (by positivity)]
        exact pow_le_pow_left₀ (by positivity) hb 3
      have h3 : Real.sqrt (K:ℝ) * (shellB d x)⁻¹ ≤ 4.13*(d:ℝ)*Real.sqrt L * (10*L*(d:ℝ))⁻¹ :=
        mul_le_mul hA1 h1 (inv_nonneg.mpr hbpos.le) (by positivity)
      have h4 : 2*(K:ℝ)^2*Real.sqrt (K:ℝ) * ((shellB d x)^3)⁻¹
          ≤ 2400*(d:ℝ)^5*L^2*Real.sqrt L * ((10*L*(d:ℝ))^3)⁻¹ :=
        mul_le_mul hA2 h2 (inv_nonneg.mpr (by positivity)) (by positivity)
      have hsL : Real.sqrt L ≤ L := by
        nlinarith [Real.sq_sqrt (le_of_lt hLpos), Real.sqrt_nonneg L, hL1]
      have h3' : 4.13*(d:ℝ)*Real.sqrt L * (10*L*(d:ℝ))⁻¹ ≤ 0.413 := by
        have he : 4.13*(d:ℝ)*Real.sqrt L * (10*L*(d:ℝ))⁻¹ = 4.13*Real.sqrt L/(10*L) := by
          field_simp <;> ring
        rw [he, div_le_iff₀ (by positivity)]
        nlinarith [hsL]
      have h4' : 2400*(d:ℝ)^5*L^2*Real.sqrt L * ((10*L*(d:ℝ))^3)⁻¹ ≤ 2.4*(d:ℝ)^2 := by
        have he : 2400*(d:ℝ)^5*L^2*Real.sqrt L * ((10*L*(d:ℝ))^3)⁻¹
            = 2.4*(d:ℝ)^2*(Real.sqrt L/L) := by
          field_simp <;> ring
        rw [he]
        have h : Real.sqrt L/L ≤ 1 := by rw [div_le_one hLpos]; exact hsL
        calc 2.4*(d:ℝ)^2*(Real.sqrt L/L) ≤ 2.4*(d:ℝ)^2*1 :=
              mul_le_mul_of_nonneg_left h (by positivity)
          _ = 2.4*(d:ℝ)^2 := by ring
      linarith [h3, h4, h3', h4']
    calc (1 + x/(d:ℝ))^(d-1) * (∑ k ∈ Finset.Icc 1 K,
            (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ | shellB d x / Real.sqrt (k:ℝ) ≤ z})
        ≤ (1/Real.sqrt (2*Real.pi)) * (Real.exp x * Real.exp (-((shellB d x)^2)/(2*(K:ℝ))))
          * (Real.sqrt (K:ℝ) * (shellB d x)⁻¹
            + 2*(K:ℝ)^2*Real.sqrt (K:ℝ) * ((shellB d x)^3)⁻¹) := s1.trans (le_of_eq s2)
      _ ≤ (1/Real.sqrt (2*Real.pi)) * 1 * (0.413 + 2.4*(d:ℝ)^2) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left s3 (by positivity)) s4 (by positivity)
          positivity
      _ = (1/Real.sqrt (2*Real.pi)) * (0.413 + 2.4*(d:ℝ)^2) := by ring
  have hbnd_int2 : IntegrableOn (fun _ : ℝ => (1/Real.sqrt (2*Real.pi)) * (0.413 + 2.4*(d:ℝ)^2))
      (Set.Ioc (21*L) ((d:ℝ)/2)) volume :=
    integrableOn_Ioc_of_continuousOn (by fun_prop)
  have hab : 21*L ≤ (d:ℝ)/2 := by linarith [h120L]
  have h1 : ∫ x in (21*L)..((d:ℝ)/2), F ((d:ℝ)⁻¹*x+1)
      ≤ (1/Real.sqrt (2*Real.pi)) * (0.413 + 2.4*(d:ℝ)^2) * ((d:ℝ)/2 - 21*L) := by
    calc ∫ x in (21*L)..((d:ℝ)/2), F ((d:ℝ)⁻¹*x+1)
        ≤ ∫ x in (21*L)..((d:ℝ)/2), (fun _ : ℝ => (1/Real.sqrt (2*Real.pi)) * (0.413 + 2.4*(d:ℝ)^2)) x :=
          integral_mono_of_nonneg_Ioc hab (fun x hx => hFnn x (by linarith [hx.1, hL1]))
            hbnd_int2 (fun x hx => hpoint x hx)
      _ = (1/Real.sqrt (2*Real.pi)) * (0.413 + 2.4*(d:ℝ)^2) * ((d:ℝ)/2 - 21*L) := by
          rw [intervalIntegral.integral_const]; ring
  have h2 : (1/Real.sqrt (2*Real.pi)) * (0.413 + 2.4*(d:ℝ)^2) * ((d:ℝ)/2 - 21*L)
      ≤ 5*10^4*(d:ℝ)^4 := by
    have h6 : (1/Real.sqrt (2*Real.pi)) ≤ 1 := by
      rw [div_le_one (by positivity), Real.one_le_sqrt]
      nlinarith [Real.pi_gt_three]
    have h7 : (0:ℝ) ≤ (d:ℝ)/2 - 21*L := by linarith [h120L]
    have h8 : (0:ℝ) ≤ 0.413 + 2.4*(d:ℝ)^2 := by positivity
    have h9 : (1/Real.sqrt (2*Real.pi)) * (0.413 + 2.4*(d:ℝ)^2) * ((d:ℝ)/2 - 21*L)
        ≤ (0.413 + 2.4*(d:ℝ)^2) * ((d:ℝ)/2) := by
      calc (1/Real.sqrt (2*Real.pi)) * (0.413 + 2.4*(d:ℝ)^2) * ((d:ℝ)/2 - 21*L)
          ≤ 1 * (0.413 + 2.4*(d:ℝ)^2) * ((d:ℝ)/2 - 21*L) := by
            apply mul_le_mul_of_nonneg_right _ h7
            exact mul_le_mul_of_nonneg_right h6 h8
        _ ≤ 1 * (0.413 + 2.4*(d:ℝ)^2) * ((d:ℝ)/2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            linarith [h120L]
        _ = (0.413 + 2.4*(d:ℝ)^2) * ((d:ℝ)/2) := by ring
    have h10 : (0.413 + 2.4*(d:ℝ)^2) * ((d:ℝ)/2) ≤ 5*10^4*(d:ℝ)^4 := by
      have hd4 : (d:ℝ)^3 ≤ (d:ℝ)^4 := pow_le_pow_right₀ hdr1 (by norm_num : 3 ≤ 4)
      have hd1 : (d:ℝ)^1 ≤ (d:ℝ)^4 := pow_le_pow_right₀ hdr1 (by norm_num : 1 ≤ 4)
      nlinarith [hd4, hd1, pow_nonneg (by linarith : (0:ℝ) ≤ (d:ℝ)) 4]
    linarith [h9, h10]
  linarith [h1, h2]

lemma region3_le {d K : ℕ} {L : ℝ} {F : ℝ → ℝ} (hdrpos : 0 < (d:ℝ)) (hdr1 : 1 ≤ (d:ℝ))
    (hdr20 : (10:ℝ)^20 ≤ (d:ℝ))
    (hLpos : 0 < L) (hL1 : 1 ≤ L) (hL2 : L^2 ≤ 16*Real.sqrt (d:ℝ)) (hsqL : Real.sqrt L ≤ 16*(d:ℝ))
    (hA1 : Real.sqrt (K:ℝ) ≤ 4.13*(d:ℝ)*Real.sqrt L)
    (hA2 : 2*(K:ℝ)^2*Real.sqrt (K:ℝ) ≤ 2400*(d:ℝ)^5*L^2*Real.sqrt L)
    (hpt : ∀ x : ℝ, F ((d:ℝ)⁻¹*x+1) = (1 + x/(d:ℝ))^(d-1) *
        (∑ k ∈ Finset.Icc 1 K, (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ | shellB d x / Real.sqrt (k:ℝ) ≤ z}))
    (hFnn : ∀ x : ℝ, 0 ≤ x → 0 ≤ F ((d:ℝ)⁻¹*x+1))
    (hweight : ∀ x : ℝ, 0 ≤ x → (1 + x/(d:ℝ))^(d-1) ≤ Real.exp x)
    (hsumnn : ∀ x : ℝ, 0 ≤ ∑ k ∈ Finset.Icc 1 K, (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ | shellB d x / Real.sqrt (k:ℝ) ≤ z})
    (hsumSB : ∀ x : ℝ, 0 < shellB d x →
        (∑ k ∈ Finset.Icc 1 K, (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ | shellB d x / Real.sqrt (k:ℝ) ≤ z})
        ≤ (Real.sqrt (K:ℝ) * (shellB d x)⁻¹ + 2*(K:ℝ)^2*Real.sqrt (K:ℝ) * ((shellB d x)^3)⁻¹)
          * Real.exp (-((shellB d x)^2)/(2*(K:ℝ))) / Real.sqrt (2*Real.pi))
    (hshellBposany : ∀ x : ℝ, 0 ≤ x → 0 < shellB d x)
    (hshellB_low3 : ∀ x ∈ Set.Icc ((d:ℝ)/2) (d:ℝ), (5/9)*(d:ℝ)^2 ≤ shellB d x)
    (hexp3 : ∀ x ∈ Set.Icc ((d:ℝ)/2) (d:ℝ), x ≤ (shellB d x)^2/(2*(K:ℝ))) :
    ∫ x in ((d:ℝ)/2)..(d:ℝ), F ((d:ℝ)⁻¹ * x + 1) ≤ 5*10^4*(d:ℝ)^4 := by
  have hpoint : ∀ x ∈ Set.Ioc ((d:ℝ)/2) (d:ℝ),
      F ((d:ℝ)⁻¹*x+1) ≤ (1/Real.sqrt (2*Real.pi)) * (7.44*Real.sqrt L/(d:ℝ) + 14000*L^2*Real.sqrt L/(d:ℝ)) := by
    intro x hx
    have hxI : x ∈ Set.Icc ((d:ℝ)/2) (d:ℝ) := ⟨hx.1.le, hx.2⟩
    have hx0 : 0 ≤ x := by linarith [hx.1, hdrpos]
    rw [hpt x]
    have hw := hweight x hx0
    have hs0 := hsumnn x
    have hS := hsumSB x (hshellBposany x hx0)
    have hex := hexp3 x hxI
    have hb := hshellB_low3 x hxI
    have hbpos : (0:ℝ) < shellB d x := hshellBposany x hx0
    have s1 : (1 + x/(d:ℝ))^(d-1) * (∑ k ∈ Finset.Icc 1 K,
          (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ | shellB d x / Real.sqrt (k:ℝ) ≤ z})
        ≤ Real.exp x * ((Real.sqrt (K:ℝ) * (shellB d x)⁻¹
            + 2*(K:ℝ)^2*Real.sqrt (K:ℝ) * ((shellB d x)^3)⁻¹)
            * Real.exp (-((shellB d x)^2)/(2*(K:ℝ))) / Real.sqrt (2*Real.pi)) :=
      (mul_le_mul_of_nonneg_right hw hs0).trans (mul_le_mul_of_nonneg_left hS (Real.exp_nonneg _))
    have s2 : Real.exp x * ((Real.sqrt (K:ℝ) * (shellB d x)⁻¹
            + 2*(K:ℝ)^2*Real.sqrt (K:ℝ) * ((shellB d x)^3)⁻¹)
            * Real.exp (-((shellB d x)^2)/(2*(K:ℝ))) / Real.sqrt (2*Real.pi))
        = (1/Real.sqrt (2*Real.pi)) * (Real.exp x * Real.exp (-((shellB d x)^2)/(2*(K:ℝ))))
          * (Real.sqrt (K:ℝ) * (shellB d x)⁻¹
            + 2*(K:ℝ)^2*Real.sqrt (K:ℝ) * ((shellB d x)^3)⁻¹) := by ring
    have s3 : Real.exp x * Real.exp (-((shellB d x)^2)/(2*(K:ℝ))) ≤ 1 := by
      have h2 : (-((shellB d x)^2))/(2*(K:ℝ)) = -((shellB d x)^2/(2*(K:ℝ))) := by ring
      rw [h2, ← Real.exp_add, Real.exp_le_one_iff]
      linarith only [hex]
    have s4 : Real.sqrt (K:ℝ) * (shellB d x)⁻¹
          + 2*(K:ℝ)^2*Real.sqrt (K:ℝ) * ((shellB d x)^3)⁻¹
        ≤ 7.44*Real.sqrt L/(d:ℝ) + 14000*L^2*Real.sqrt L/(d:ℝ) := by
      have h1 : (shellB d x)⁻¹ ≤ (((5/9)*(d:ℝ)^2))⁻¹ := by
        rw [inv_le_inv₀ hbpos (by positivity)]; exact hb
      have h2 : ((shellB d x)^3)⁻¹ ≤ (((5/9)*(d:ℝ)^2)^3)⁻¹ := by
        rw [inv_le_inv₀ (by positivity) (by positivity)]
        exact pow_le_pow_left₀ (by positivity) hb 3
      have h3 : Real.sqrt (K:ℝ) * (shellB d x)⁻¹ ≤ 4.13*(d:ℝ)*Real.sqrt L * (((5/9)*(d:ℝ)^2))⁻¹ :=
        mul_le_mul hA1 h1 (inv_nonneg.mpr hbpos.le) (by positivity)
      have h4 : 2*(K:ℝ)^2*Real.sqrt (K:ℝ) * ((shellB d x)^3)⁻¹
          ≤ 2400*(d:ℝ)^5*L^2*Real.sqrt L * (((5/9)*(d:ℝ)^2)^3)⁻¹ :=
        mul_le_mul hA2 h2 (inv_nonneg.mpr (by positivity)) (by positivity)
      have h3' : 4.13*(d:ℝ)*Real.sqrt L * (((5/9)*(d:ℝ)^2))⁻¹ ≤ 7.44*Real.sqrt L/(d:ℝ) := by
        have he : 4.13*(d:ℝ)*Real.sqrt L * (((5/9)*(d:ℝ)^2))⁻¹ = 7.434*Real.sqrt L/(d:ℝ) := by
          field_simp <;> ring
        rw [he]
        apply div_le_div_of_nonneg_right _ (le_of_lt hdrpos)
        nlinarith [Real.sqrt_nonneg L]
      have h4' : 2400*(d:ℝ)^5*L^2*Real.sqrt L * (((5/9)*(d:ℝ)^2)^3)⁻¹
          ≤ 14000*L^2*Real.sqrt L/(d:ℝ) := by
        have he : 2400*(d:ℝ)^5*L^2*Real.sqrt L * (((5/9)*(d:ℝ)^2)^3)⁻¹
            = 13996.8*L^2*Real.sqrt L/(d:ℝ) := by
          field_simp <;> ring
        rw [he]
        apply div_le_div_of_nonneg_right _ (le_of_lt hdrpos)
        nlinarith [sq_nonneg L, Real.sqrt_nonneg L]
      linarith [h3, h4, h3', h4']
    calc (1 + x/(d:ℝ))^(d-1) * (∑ k ∈ Finset.Icc 1 K,
            (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ | shellB d x / Real.sqrt (k:ℝ) ≤ z})
        ≤ (1/Real.sqrt (2*Real.pi)) * (Real.exp x * Real.exp (-((shellB d x)^2)/(2*(K:ℝ))))
          * (Real.sqrt (K:ℝ) * (shellB d x)⁻¹
            + 2*(K:ℝ)^2*Real.sqrt (K:ℝ) * ((shellB d x)^3)⁻¹) := s1.trans (le_of_eq s2)
      _ ≤ (1/Real.sqrt (2*Real.pi)) * 1 * (7.44*Real.sqrt L/(d:ℝ) + 14000*L^2*Real.sqrt L/(d:ℝ)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left s3 (by positivity)) s4 (by positivity)
          positivity
      _ = (1/Real.sqrt (2*Real.pi)) * (7.44*Real.sqrt L/(d:ℝ) + 14000*L^2*Real.sqrt L/(d:ℝ)) := by ring
  have hbnd_int3 : IntegrableOn (fun _ : ℝ => (1/Real.sqrt (2*Real.pi)) * (7.44*Real.sqrt L/(d:ℝ) + 14000*L^2*Real.sqrt L/(d:ℝ)))
      (Set.Ioc ((d:ℝ)/2) (d:ℝ)) volume :=
    integrableOn_Ioc_of_continuousOn (by fun_prop)
  have hab : (d:ℝ)/2 ≤ (d:ℝ) := by linarith [hdrpos]
  have h1 : ∫ x in ((d:ℝ)/2)..(d:ℝ), F ((d:ℝ)⁻¹*x+1)
      ≤ (1/Real.sqrt (2*Real.pi)) * (7.44*Real.sqrt L/(d:ℝ) + 14000*L^2*Real.sqrt L/(d:ℝ)) * ((d:ℝ) - (d:ℝ)/2) := by
    calc ∫ x in ((d:ℝ)/2)..(d:ℝ), F ((d:ℝ)⁻¹*x+1)
        ≤ ∫ x in ((d:ℝ)/2)..(d:ℝ), (fun _ : ℝ => (1/Real.sqrt (2*Real.pi)) * (7.44*Real.sqrt L/(d:ℝ) + 14000*L^2*Real.sqrt L/(d:ℝ))) x :=
          integral_mono_of_nonneg_Ioc hab (fun x hx => hFnn x (by linarith [hx.1, hdrpos]))
            hbnd_int3 (fun x hx => hpoint x hx)
      _ = (1/Real.sqrt (2*Real.pi)) * (7.44*Real.sqrt L/(d:ℝ) + 14000*L^2*Real.sqrt L/(d:ℝ)) * ((d:ℝ) - (d:ℝ)/2) := by
          rw [intervalIntegral.integral_const]; ring
  have h2 : (1/Real.sqrt (2*Real.pi)) * (7.44*Real.sqrt L/(d:ℝ) + 14000*L^2*Real.sqrt L/(d:ℝ)) * ((d:ℝ) - (d:ℝ)/2)
      ≤ 5*10^4*(d:ℝ)^4 := by
    have h6 : (1/Real.sqrt (2*Real.pi)) ≤ 1 := by
      rw [div_le_one (by positivity), Real.one_le_sqrt]
      nlinarith [Real.pi_gt_three]
    have he : (7.44*Real.sqrt L/(d:ℝ) + 14000*L^2*Real.sqrt L/(d:ℝ)) * ((d:ℝ) - (d:ℝ)/2)
        = 3.72*Real.sqrt L + 7000*L^2*Real.sqrt L := by
      field_simp <;> ring
    rw [show (1/Real.sqrt (2*Real.pi)) * (7.44*Real.sqrt L/(d:ℝ) + 14000*L^2*Real.sqrt L/(d:ℝ)) * ((d:ℝ) - (d:ℝ)/2)
        = (1/Real.sqrt (2*Real.pi)) * ((7.44*Real.sqrt L/(d:ℝ) + 14000*L^2*Real.sqrt L/(d:ℝ)) * ((d:ℝ) - (d:ℝ)/2)) by ring, he]
    have hbr : (0:ℝ) ≤ 3.72*Real.sqrt L + 7000*L^2*Real.sqrt L := by positivity
    have hm := mul_le_mul_of_nonneg_right h6 hbr
    have hL2s : L^2*Real.sqrt L ≤ 256*(d:ℝ)^2 := by
      have h7 : L^2 ≤ 16*(d:ℝ) := by
        have h8 : Real.sqrt (d:ℝ) ≤ (d:ℝ) := by
          nlinarith [Real.sq_sqrt (le_of_lt hdrpos), Real.sqrt_nonneg (d:ℝ), hdr1]
        linarith [hL2, h8]
      have h := mul_le_mul h7 hsqL (Real.sqrt_nonneg L) (by positivity : (0:ℝ) ≤ 16*(d:ℝ))
      linarith [h]
    have h37 : (37:ℝ) <= (d:ℝ)^2 := by nlinarith [hdr20]
    nlinarith [hm, hL2s, hsqL, h37, hdr1, hdrpos]
  linarith [h1, h2]


theorem integral_shell_weight_le :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d → ∀ K : ℕ, (K : ℝ) ≤ 16 * (d : ℝ) ^ 2 * Real.log (d : ℝ) + 1 →
      ∫ y in (1 : ℝ)..2, y ^ (d - 1) *
        (∑ k ∈ Finset.Icc 1 K,
          (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ |
            (((1 - 1 / (d : ℝ)) ^ 2)⁻¹ - 1 / y ^ 2) * (d : ℝ) ^ 2 / Real.sqrt (k : ℝ) ≤ z})
      ≤ 10 ^ 6 * (d : ℝ) ^ 3 := by
  refine ⟨10^20, ?_⟩
  intro d hd K hK
  by_cases hK0 : K = 0
  · subst hK0
    simp
  have hK1 : 1 ≤ K := Nat.pos_of_ne_zero hK0
  have hKposR : (0:ℝ) < (K:ℝ) := by exact_mod_cast hK1
  set L : ℝ := Real.log (d:ℝ) with hLdef
  have hd20 : (10:ℕ)^20 ≤ d := hd
  have hdr20 : (10:ℝ)^20 ≤ (d:ℝ) := by exact_mod_cast hd20
  have hdrpos : (0:ℝ) < (d:ℝ) := by linarith
  have hdr1 : (1:ℝ) ≤ (d:ℝ) := by linarith
  have hdr2 : (2:ℝ) ≤ (d:ℝ) := by linarith
  have hd2 : 2 ≤ d := by omega
  have hLpos : 0 < L := by rw [hLdef]; exact Real.log_pos (by linarith)
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    have h2 : (2:ℝ) ≤ Real.log 10 := by
      rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 10)]
      have he : Real.exp (2:ℝ) = (Real.exp 1)^2 := by rw [← Real.exp_nat_mul]; norm_num
      rw [he]
      nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
    have h3 : Real.log 10 ≤ Real.log (d:ℝ) := by
      apply Real.log_le_log (by norm_num)
      linarith [hdr20]
    have h4 : Real.log ((10:ℝ)^20) = 20 * Real.log 10 := Real.log_pow 10 20
    have h5 : Real.log 10 ≤ Real.log ((10:ℝ)^20) := by
      rw [h4]; linarith
    linarith
  -- the log bound
  have hL_le : L ≤ 4 * Real.sqrt (Real.sqrt (d:ℝ)) := by
    rw [hLdef]
    have hss : Real.sqrt (Real.sqrt (d:ℝ)) = (d:ℝ) ^ (1/4:ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hdrpos)]
      norm_num
    rw [hss]
    have h := Real.log_le_rpow_div (le_of_lt hdrpos) (by norm_num : (0:ℝ) < 1/4)
    have h4 : (d:ℝ) ^ (1/4:ℝ) / (1/4) = 4 * (d:ℝ)^(1/4:ℝ) := by ring
    rw [h4] at h
    exact h
  have hL4 : L^4 ≤ 256 * (d:ℝ) := by
    have h4 : L^4 ≤ (4*Real.sqrt (Real.sqrt (d:ℝ)))^4 :=
      pow_le_pow_left₀ (by positivity) hL_le 4
    have h4' : (4*Real.sqrt (Real.sqrt (d:ℝ)))^4 = 256*(d:ℝ) := by
      have h1 : (Real.sqrt (Real.sqrt (d:ℝ)))^2 = Real.sqrt (d:ℝ) := Real.sq_sqrt (Real.sqrt_nonneg _)
      calc (4*Real.sqrt (Real.sqrt (d:ℝ)))^4
          = 256 * ((Real.sqrt (Real.sqrt (d:ℝ)))^2)^2 := by ring
        _ = 256 * (Real.sqrt (d:ℝ))^2 := by rw [h1]
        _ = 256 * (d:ℝ) := by rw [Real.sq_sqrt (le_of_lt hdrpos)]
    linarith [h4, h4'.le, h4'.ge]
  have hL3 : L^3 ≤ 256*(d:ℝ) := by nlinarith [hL4, hL1]
  have hL2 : L^2 ≤ 256*(d:ℝ) := by nlinarith [hL4, hL1]
  have hLle : L ≤ 256*(d:ℝ) := by nlinarith [hL4, hL1]
  have hsqL : Real.sqrt L ≤ 16*(d:ℝ) := by
    have h : Real.sqrt L ≤ Real.sqrt (256*(d:ℝ)) := Real.sqrt_le_sqrt hLle
    have h2 : Real.sqrt (256*(d:ℝ)) = 16*Real.sqrt (d:ℝ) := by
      rw [show (256:ℝ)*(d:ℝ) = 16^2*(d:ℝ) by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    rw [h2] at h
    have h3 : Real.sqrt (d:ℝ) ≤ (d:ℝ) := by
      have h1 : 1 ≤ Real.sqrt (d:ℝ) := Real.one_le_sqrt.mpr hdr1
      nlinarith [Real.sq_sqrt (le_of_lt hdrpos), Real.sqrt_nonneg (d:ℝ), h1]
    linarith
  have hsqL1 : 1 ≤ Real.sqrt L := Real.one_le_sqrt.mpr hL1
  -- bounds on K
  have hKle : (K:ℝ) ≤ 17 * (d:ℝ)^2 * L := by
    have h1 : (1:ℝ) ≤ (d:ℝ)^2 * L := by nlinarith [hdr2, hL1]
    nlinarith [hK, h1]
  -- the integrand
  set F : ℝ → ℝ := fun y => y ^ (d - 1) *
        (∑ k ∈ Finset.Icc 1 K,
          (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ |
            (((1 - 1 / (d : ℝ)) ^ 2)⁻¹ - 1 / y ^ 2) * (d : ℝ) ^ 2 / Real.sqrt (k : ℝ) ≤ z}) with hF
  -- the substitution y = 1 + x/d
  have hsubst : ∫ y in (1:ℝ)..2, F y
      = ((d:ℝ))⁻¹ * ∫ x in (0:ℝ)..(d:ℝ), F ((d:ℝ)⁻¹ * x + 1) := by
    have h := intervalIntegral.integral_comp_mul_add (f := F) (a := (0:ℝ)) (b := (d:ℝ))
      (c := ((d:ℝ))⁻¹) (by positivity) (1:ℝ)
    have h2 : ∫ x in (0:ℝ)..(d:ℝ), F ((d:ℝ)⁻¹ * x + 1) = (d:ℝ) * ∫ y in (1:ℝ)..2, F y := by
      have h' := h
      simp only [mul_zero, zero_add, inv_mul_cancel₀ (by positivity : ((d:ℝ)) ≠ 0), inv_inv,
        smul_eq_mul] at h'
      rw [show (1:ℝ) + 1 = 2 by norm_num] at h'
      exact h'
    rw [h2]
    field_simp
  -- pointwise identification of the integrand
  have hpt : ∀ x : ℝ, F ((d:ℝ)⁻¹ * x + 1)
      = (1 + x/(d:ℝ))^(d-1) *
        (∑ k ∈ Finset.Icc 1 K,
          (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ | shellB d x / Real.sqrt (k:ℝ) ≤ z}) := by
    intro x
    have hbase : (d:ℝ)⁻¹ * x + 1 = 1 + x/(d:ℝ) := by ring
    rw [hF]
    simp only []
    rw [hbase]
    have harg : ∀ k : ℕ,
        (((1 - 1/(d:ℝ))^2)⁻¹ - 1/(1+x/(d:ℝ))^2) * (d:ℝ)^2 / Real.sqrt (k:ℝ)
          = shellB d x / Real.sqrt (k:ℝ) := by
      intro k; rw [shellB, shellA]; ring
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    ext z
    simp only [Set.mem_ofPred_eq]
    rw [harg k]

  -- the constant `(1/√(2π))·e ≤ 1.2`
  have hC12 : (1/Real.sqrt (2*Real.pi)) * Real.exp 1 ≤ 1.2 := by
    have h1 : (2.44:ℝ) ≤ Real.sqrt (2*Real.pi) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      nlinarith [Real.pi_gt_three]
    have h2 : Real.exp 1 ≤ 2.72 := by linarith [Real.exp_one_lt_d9]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  -- bounds on `√K` and `2K²√K`
  have hA1 : Real.sqrt (K:ℝ) ≤ 4.13*(d:ℝ)*Real.sqrt L := by
    have h1 : Real.sqrt (K:ℝ) ≤ Real.sqrt (17*(d:ℝ)^2*L) := Real.sqrt_le_sqrt hKle
    have h2 : Real.sqrt (17*(d:ℝ)^2*L) = Real.sqrt 17 * ((d:ℝ)*Real.sqrt L) := by
      have h3 : (17:ℝ)*(d:ℝ)^2*L = (17*(d:ℝ)^2)*L := by ring
      rw [h3, Real.sqrt_mul (by positivity : (0:ℝ) ≤ 17*(d:ℝ)^2)]
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 17), Real.sqrt_sq (le_of_lt hdrpos)]
      ring
    have h4 : Real.sqrt 17 ≤ 4.13 := by
      rw [Real.sqrt_le_iff]; norm_num
    rw [h2] at h1
    calc Real.sqrt (K:ℝ) ≤ Real.sqrt 17 * ((d:ℝ)*Real.sqrt L) := h1
      _ ≤ 4.13 * ((d:ℝ)*Real.sqrt L) := by
          apply mul_le_mul_of_nonneg_right h4; positivity
      _ = 4.13*(d:ℝ)*Real.sqrt L := by ring
  have hA2 : 2*(K:ℝ)^2*Real.sqrt (K:ℝ) ≤ 2400*(d:ℝ)^5*L^2*Real.sqrt L := by
    have h2 : (K:ℝ)^2 ≤ (17*(d:ℝ)^2*L)^2 := by nlinarith [hKle, hKposR]
    have h4 : 2*(K:ℝ)^2*Real.sqrt (K:ℝ) ≤ 2*(17*(d:ℝ)^2*L)^2*(4.13*(d:ℝ)*Real.sqrt L) := by
      apply mul_le_mul (by linarith) hA1 (Real.sqrt_nonneg _) (by positivity)
    have h5 : 2*(17*(d:ℝ)^2*L)^2*(4.13*(d:ℝ)*Real.sqrt L)
        = (2*(17:ℝ)^2*4.13) * ((d:ℝ)^5*L^2*Real.sqrt L) := by ring
    have h6 : (2*(17:ℝ)^2*4.13) ≤ 2400 := by norm_num
    have h7 : (2*(17:ℝ)^2*4.13) * ((d:ℝ)^5*L^2*Real.sqrt L)
        ≤ 2400 * ((d:ℝ)^5*L^2*Real.sqrt L) :=
      mul_le_mul_of_nonneg_right h6 (by positivity)
    linarith [h4, h5.le, h5.ge, h7]
  -- `120 L ≤ d`
  have hXX4 : (Real.sqrt (Real.sqrt (d:ℝ)))^4 = (d:ℝ) := by
    have h1 : (Real.sqrt (Real.sqrt (d:ℝ)))^2 = Real.sqrt (d:ℝ) := Real.sq_sqrt (Real.sqrt_nonneg _)
    calc (Real.sqrt (Real.sqrt (d:ℝ)))^4 = ((Real.sqrt (Real.sqrt (d:ℝ)))^2)^2 := by ring
      _ = (Real.sqrt (d:ℝ))^2 := by rw [h1]
      _ = (d:ℝ) := Real.sq_sqrt (le_of_lt hdrpos)
  have hXX20 : (20:ℝ) ≤ Real.sqrt (Real.sqrt (d:ℝ)) := by
    rw [Real.le_sqrt (by norm_num) (by positivity), Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith [hdr20]
  have hXL0 : (0:ℝ) ≤ Real.sqrt (Real.sqrt (d:ℝ)) := Real.sqrt_nonneg _
  have hX3 : (5496:ℝ) ≤ (Real.sqrt (Real.sqrt (d:ℝ)))^3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 20) hXX20 3
    norm_num at h
    linarith [h]
  have h120L : 120*L ≤ (d:ℝ) := by
    have h1 : 120*L ≤ 120*(4*Real.sqrt (Real.sqrt (d:ℝ))) := by linarith [hL_le]
    have h2 : (480:ℝ)*Real.sqrt (Real.sqrt (d:ℝ)) ≤ (d:ℝ) := by
      have h3 := mul_le_mul_of_nonneg_right hX3 (by positivity : (0:ℝ) ≤ Real.sqrt (Real.sqrt (d:ℝ)))
      have h4 : (Real.sqrt (Real.sqrt (d:ℝ)))^3 * Real.sqrt (Real.sqrt (d:ℝ))
          = (Real.sqrt (Real.sqrt (d:ℝ)))^4 := by ring
      rw [h4, hXX4] at h3
      linarith [h3]
    linarith [h1, h2]
  have h3000L2 : 3000*L^2 ≤ (d:ℝ) := by
    have h1 : L^2 ≤ (4*Real.sqrt (Real.sqrt (d:ℝ)))^2 := pow_le_pow_left₀ (by positivity) hL_le 2
    have h2 : (4*Real.sqrt (Real.sqrt (d:ℝ)))^2 = 16*Real.sqrt (d:ℝ) := by
      rw [mul_pow]; rw [Real.sq_sqrt (Real.sqrt_nonneg _)]; ring
    rw [h2] at h1
    have h7 : 3000*L^2 ≤ 3000*(16*Real.sqrt (d:ℝ)) := by linarith
    have h8 : 3000*(16*Real.sqrt (d:ℝ)) ≤ (d:ℝ) := by
      have h5 : (48000:ℝ) ≤ Real.sqrt (d:ℝ) := by
        rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [hdr20]
      have h6 : (48000:ℝ)*Real.sqrt (d:ℝ) ≤ (Real.sqrt (d:ℝ))^2 := by
        rw [Real.sq_sqrt (le_of_lt hdrpos)]
        nlinarith [h5, Real.sqrt_nonneg (d:ℝ)]
      rw [Real.sq_sqrt (le_of_lt hdrpos)] at h6
      linarith [h6]
    linarith [h7, h8]
  have h1374L : 1374*L ≤ (d:ℝ) := by
    have h1 : 1374*L ≤ 1374*(4*Real.sqrt (Real.sqrt (d:ℝ))) := by linarith [hL_le]
    have h2 : (5496:ℝ)*Real.sqrt (Real.sqrt (d:ℝ)) ≤ (d:ℝ) := by
      have h4 := mul_le_mul_of_nonneg_right hX3 (by positivity : (0:ℝ) ≤ Real.sqrt (Real.sqrt (d:ℝ)))
      have h5 : (Real.sqrt (Real.sqrt (d:ℝ)))^3 * Real.sqrt (Real.sqrt (d:ℝ))
          = (Real.sqrt (Real.sqrt (d:ℝ)))^4 := by ring
      rw [h5, hXX4] at h4
      linarith [h4]
    linarith [h1, h2]

  -- `126 L ≤ d` and `648 L ≤ d`
  have h126L : 126*L ≤ (d:ℝ) := by
    have h1 : 126*L ≤ 126*(4*Real.sqrt (Real.sqrt (d:ℝ))) := by linarith [hL_le]
    have h2 : (504:ℝ)*Real.sqrt (Real.sqrt (d:ℝ)) ≤ (d:ℝ) := by
      have h3 : (504:ℝ) ≤ (Real.sqrt (Real.sqrt (d:ℝ)))^3 := by
        have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 20) hXX20 3
        norm_num at h; linarith [h]
      have h4 := mul_le_mul_of_nonneg_right h3 (by positivity : (0:ℝ) ≤ Real.sqrt (Real.sqrt (d:ℝ)))
      have h5 : (Real.sqrt (Real.sqrt (d:ℝ)))^3 * Real.sqrt (Real.sqrt (d:ℝ))
          = (Real.sqrt (Real.sqrt (d:ℝ)))^4 := by ring
      rw [h5, hXX4] at h4
      linarith [h4]
    linarith [h1, h2]
  have h648L : 648*L ≤ (d:ℝ) := by
    have h1 : 648*L ≤ 648*(4*Real.sqrt (Real.sqrt (d:ℝ))) := by linarith [hL_le]
    have h2 : (2592:ℝ)*Real.sqrt (Real.sqrt (d:ℝ)) ≤ (d:ℝ) := by
      have h3 : (2592:ℝ) ≤ (Real.sqrt (Real.sqrt (d:ℝ)))^3 := by
        have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 20) hXX20 3
        norm_num at h; linarith [h]
      have h4 := mul_le_mul_of_nonneg_right h3 (by positivity : (0:ℝ) ≤ Real.sqrt (Real.sqrt (d:ℝ)))
      have h5 : (Real.sqrt (Real.sqrt (d:ℝ)))^3 * Real.sqrt (Real.sqrt (d:ℝ))
          = (Real.sqrt (Real.sqrt (d:ℝ)))^4 := by ring
      rw [h5, hXX4] at h4
      linarith [h4]
    linarith [h1, h2]
  -- `2K ≤ 36 d² L`
  have hK36 : 2*(K:ℝ) ≤ 36*(d:ℝ)^2*L := by nlinarith [hKle, hdr1, hL1]
  -- shellA/B lower bounds
  have hshellBpos1 : ∀ x ∈ Set.Icc (1:ℝ) (21*L), 0 < shellB d x := by
    intro x hx
    exact mul_pos (shellA_pos hd2 (by linarith [hx.1])) (by positivity)
  have hshellBlow1 : ∀ x ∈ Set.Icc (1:ℝ) (21*L), (3/2)*x*(d:ℝ) ≤ shellB d x := by
    intro x hx
    have hx0 : 0 ≤ x := by linarith [hx.1]
    have h1 := shellA_lower_linear (d := d) hd2 hx0
    have hkey : ((d:ℝ)⁻¹ + 2*(x/(d:ℝ)) - 3*(x/(d:ℝ))^2) * (d:ℝ)^2
        = (d:ℝ) + 2*x*(d:ℝ) - 3*x^2 := by
      field_simp <;> ring
    rw [shellB]
    have h4 : x ≤ (d:ℝ)/6 := by linarith [hx.2, h126L]
    calc (3/2)*x*(d:ℝ) ≤ ((d:ℝ)⁻¹ + 2*(x/(d:ℝ)) - 3*(x/(d:ℝ))^2) * (d:ℝ)^2 := by
          rw [hkey]; nlinarith [h4, hx0]
      _ ≤ shellA d x * (d:ℝ)^2 := mul_le_mul_of_nonneg_right h1 (by positivity)
  have hshellBpos2 : ∀ x ∈ Set.Icc (0:ℝ) (d:ℝ), 0 < shellB d x := by
    intro x hx
    exact mul_pos (shellA_pos hd2 hx.1) (by positivity)
  have hshellB_low2 : ∀ x ∈ Set.Icc (144*L) ((d:ℝ)/2), (1/2)*x*(d:ℝ) ≤ shellB d x := by
    intro x hx
    have hx0 : 0 ≤ x := by linarith [hx.1, hL1]
    have h1 := shellA_lower_linear (d := d) hd2 hx0
    have hkey : ((d:ℝ)⁻¹ + 2*(x/(d:ℝ)) - 3*(x/(d:ℝ))^2) * (d:ℝ)^2
        = (d:ℝ) + 2*x*(d:ℝ) - 3*x^2 := by
      field_simp <;> ring
    rw [shellB]
    have h4 : x ≤ (d:ℝ)/2 := hx.2
    calc (1/2)*x*(d:ℝ) ≤ ((d:ℝ)⁻¹ + 2*(x/(d:ℝ)) - 3*(x/(d:ℝ))^2) * (d:ℝ)^2 := by
          rw [hkey]; nlinarith [h4, hx0]
      _ ≤ shellA d x * (d:ℝ)^2 := mul_le_mul_of_nonneg_right h1 (by positivity)
  have hshellB_low2b : ∀ x ∈ Set.Icc (21*L) (144*L), (4/3)*x*(d:ℝ) ≤ shellB d x := by
    intro x hx
    have hx0 : 0 ≤ x := by linarith [hx.1, hL1]
    have h1 := shellA_lower_linear (d := d) hd2 hx0
    have hkey : ((d:ℝ)⁻¹ + 2*(x/(d:ℝ)) - 3*(x/(d:ℝ))^2) * (d:ℝ)^2
        = (d:ℝ) + 2*x*(d:ℝ) - 3*x^2 := by
      field_simp <;> ring
    rw [shellB]
    have h4 : x ≤ 2*(d:ℝ)/9 := by linarith [hx.2, h648L]
    calc (4/3)*x*(d:ℝ) ≤ ((d:ℝ)⁻¹ + 2*(x/(d:ℝ)) - 3*(x/(d:ℝ))^2) * (d:ℝ)^2 := by
          rw [hkey]; nlinarith [h4, hx0]
      _ ≤ shellA d x * (d:ℝ)^2 := mul_le_mul_of_nonneg_right h1 (by positivity)
  have hshellB_low3 : ∀ x ∈ Set.Icc ((d:ℝ)/2) (d:ℝ), (5/9)*(d:ℝ)^2 ≤ shellB d x := by
    intro x hx
    rw [shellB]
    have h1 := shellA_ge_five_ninths (d := d) hd2 hx.1
    calc (5/9)*(d:ℝ)^2 = (5/9) * (d:ℝ)^2 := by ring
      _ ≤ shellA d x * (d:ℝ)^2 := mul_le_mul_of_nonneg_right h1 (by positivity)
  -- exponent bounds
  have hKey1 : ∀ x : ℝ, (shellB d x)^2/(36*(d:ℝ)^2*L) ≤ (shellB d x)^2/(2*(K:ℝ)) := by
    intro x
    have hpos : (0:ℝ) < 36*(d:ℝ)^2*L := by positivity
    have h2' : (shellB d x)^2 * (2*(K:ℝ)) ≤ (shellB d x)^2 * (36*(d:ℝ)^2*L) :=
      mul_le_mul_of_nonneg_left hK36 (sq_nonneg _)
    rw [div_le_div_iff₀ hpos (by positivity)]
    linarith [h2']
  have hexp2 : ∀ x ∈ Set.Icc (21*L) ((d:ℝ)/2), x ≤ (shellB d x)^2/(2*(K:ℝ)) := by
    intro x hx
    have hx0 : 0 ≤ x := by linarith [hx.1, hL1]
    have hpos : (0:ℝ) < 36*(d:ℝ)^2*L := by positivity
    rcases le_or_gt x (144*L) with hxle | hxgt
    · have hb := hshellB_low2b x ⟨hx.1, hxle⟩
      have hb2 : ((4/3)*x*(d:ℝ))^2 ≤ (shellB d x)^2 := pow_le_pow_left₀ (by positivity) hb 2
      have h1 : ((4/3)*x*(d:ℝ))^2/(36*(d:ℝ)^2*L) ≤ (shellB d x)^2/(36*(d:ℝ)^2*L) := by
        rw [div_le_div_iff₀ hpos hpos]
        have := mul_le_mul_of_nonneg_right hb2 hpos.le
        nlinarith [this]
      have h2 : ((4/3)*x*(d:ℝ))^2/(36*(d:ℝ)^2*L) = (4*x^2)/(81*L) := by
        field_simp <;> ring
      have h4 : x ≤ (4*x^2)/(81*L) := by
        rw [le_div_iff₀ (by positivity)]
        have h5 : (81:ℝ)*L ≤ 4*x := by linarith [hx.1]
        nlinarith [mul_le_mul_of_nonneg_right h5 hx0]
      calc x ≤ (4*x^2)/(81*L) := h4
        _ = ((4/3)*x*(d:ℝ))^2/(36*(d:ℝ)^2*L) := h2.symm
        _ ≤ (shellB d x)^2/(36*(d:ℝ)^2*L) := h1
        _ ≤ (shellB d x)^2/(2*(K:ℝ)) := hKey1 x
    · have hb := hshellB_low2 x ⟨le_of_lt hxgt, hx.2⟩
      have hb2 : ((1/2)*x*(d:ℝ))^2 ≤ (shellB d x)^2 := pow_le_pow_left₀ (by positivity) hb 2
      have h1 : ((1/2)*x*(d:ℝ))^2/(36*(d:ℝ)^2*L) ≤ (shellB d x)^2/(36*(d:ℝ)^2*L) := by
        rw [div_le_div_iff₀ hpos hpos]
        have := mul_le_mul_of_nonneg_right hb2 hpos.le
        nlinarith [this]
      have h2 : ((1/2)*x*(d:ℝ))^2/(36*(d:ℝ)^2*L) = x^2/(144*L) := by
        field_simp <;> ring
      have h4 : x ≤ x^2/(144*L) := by
        rw [le_div_iff₀ (by positivity)]
        have h5 : (144:ℝ)*L ≤ x := by linarith [hxgt]
        nlinarith [mul_le_mul_of_nonneg_right h5 hx0]
      calc x ≤ x^2/(144*L) := h4
        _ = ((1/2)*x*(d:ℝ))^2/(36*(d:ℝ)^2*L) := h2.symm
        _ ≤ (shellB d x)^2/(36*(d:ℝ)^2*L) := h1
        _ ≤ (shellB d x)^2/(2*(K:ℝ)) := hKey1 x
  have hexp3 : ∀ x ∈ Set.Icc ((d:ℝ)/2) (d:ℝ), x ≤ (shellB d x)^2/(2*(K:ℝ)) := by
    intro x hx
    have hpos : (0:ℝ) < 36*(d:ℝ)^2*L := by positivity
    have hb := hshellB_low3 x hx
    have hb2 : ((5/9)*(d:ℝ)^2)^2 ≤ (shellB d x)^2 := pow_le_pow_left₀ (by positivity) hb 2
    have h1 : ((5/9)*(d:ℝ)^2)^2/(36*(d:ℝ)^2*L) ≤ (shellB d x)^2/(36*(d:ℝ)^2*L) := by
      rw [div_le_div_iff₀ hpos hpos]
      have := mul_le_mul_of_nonneg_right hb2 hpos.le
      nlinarith [this]
    have h2 : ((5/9)*(d:ℝ)^2)^2/(36*(d:ℝ)^2*L) = 25*(d:ℝ)^2/(2916*L) := by
      field_simp <;> ring
    have h4 : x ≤ 25*(d:ℝ)^2/(2916*L) := by
      rw [le_div_iff₀ (by positivity)]
      have h5 : (2916:ℝ)*L ≤ 25*(d:ℝ) := by linarith [h120L]
      nlinarith [h5, hx.2, hdrpos]
    calc x ≤ 25*(d:ℝ)^2/(2916*L) := h4
      _ = ((5/9)*(d:ℝ)^2)^2/(36*(d:ℝ)^2*L) := h2.symm
      _ ≤ (shellB d x)^2/(36*(d:ℝ)^2*L) := h1
      _ ≤ (shellB d x)^2/(2*(K:ℝ)) := hKey1 x

  -- `L² ≤ 16√d`
  have hL2d : L^2 ≤ 16*Real.sqrt (d:ℝ) := by
    have h1 : L^2 ≤ (4*Real.sqrt (Real.sqrt (d:ℝ)))^2 := pow_le_pow_left₀ (by positivity) hL_le 2
    have h2 : (4*Real.sqrt (Real.sqrt (d:ℝ)))^2 = 16*Real.sqrt (d:ℝ) := by
      rw [mul_pow]; rw [Real.sq_sqrt (Real.sqrt_nonneg _)]; ring
    rwa [h2] at h1
  have h34730L2 : 34730*L^2 ≤ (d:ℝ) := by
    have h2 : 34730*L^2 ≤ 34730*(16*Real.sqrt (d:ℝ)) := by linarith
    have h3 : 34730*(16*Real.sqrt (d:ℝ)) ≤ (d:ℝ) := by
      have h5 : (555680:ℝ) ≤ Real.sqrt (d:ℝ) := by
        rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [hdr20]
      have h68 : Real.sqrt (d:ℝ) * Real.sqrt (d:ℝ) = (d:ℝ) := by
        rw [← sq, Real.sq_sqrt (le_of_lt hdrpos)]
      have h6 : (555680:ℝ)*Real.sqrt (d:ℝ) ≤ (d:ℝ) := by
        have h7 := mul_le_mul_of_nonneg_right h5 (Real.sqrt_nonneg (d:ℝ))
        rwa [h68] at h7
      linarith [h6]
    linarith [h2, h3]
  -- nonnegativity of the sum and of `F`
  have hsumnn : ∀ x : ℝ, 0 ≤ ∑ k ∈ Finset.Icc 1 K,
      (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ | shellB d x / Real.sqrt (k:ℝ) ≤ z} := by
    intro x
    apply Finset.sum_nonneg
    intro k hk
    exact measureReal_nonneg
  have hFnn : ∀ x : ℝ, 0 ≤ x → 0 ≤ F ((d:ℝ)⁻¹ * x + 1) := by
    intro x hx
    rw [hpt x]
    apply mul_nonneg (by positivity) (hsumnn x)
  have hweight : ∀ x : ℝ, 0 ≤ x → (1 + x/(d:ℝ))^(d-1) ≤ Real.exp x := by
    intro x hx
    have hpos : (0:ℝ) < 1 + x/(d:ℝ) := by positivity
    have h1 : (1 + x/(d:ℝ)) ≤ Real.exp (x/(d:ℝ)) := by
      have := Real.add_one_le_exp (x/(d:ℝ))
      linarith [this]
    have h2 : (1 + x/(d:ℝ))^d ≤ (Real.exp (x/(d:ℝ)))^d := pow_le_pow_left₀ (le_of_lt hpos) h1 d
    have h3 : (Real.exp (x/(d:ℝ)))^d = Real.exp x := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp
    have h4 : (1 + x/(d:ℝ))^(d-1) ≤ (1 + x/(d:ℝ))^d :=
      pow_le_pow_right₀ (by have := div_nonneg hx (le_of_lt hdrpos); linarith) (by omega : d - 1 ≤ d)
    rw [h3] at h2
    exact h4.trans h2
  -- sum bound (sharp)
  have hsumSB : ∀ x : ℝ, 0 < shellB d x →
      (∑ k ∈ Finset.Icc 1 K, (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ | shellB d x / Real.sqrt (k:ℝ) ≤ z})
      ≤ (Real.sqrt (K:ℝ) * (shellB d x)⁻¹ + 2*(K:ℝ)^2*Real.sqrt (K:ℝ) * ((shellB d x)^3)⁻¹)
        * Real.exp (-((shellB d x)^2)/(2*(K:ℝ))) / Real.sqrt (2*Real.pi) := by
    intro x hx
    exact sum_tail_div_sqrt_le_cube hx hK1
  -- sharp exponent bound on `[1, 21L]`
  -- sharp exponent bound on `[1, 21L]` (isolated: this is `exp_bound_twentyone`)
  have hK16 : (K:ℝ) ≤ 16*(d:ℝ)^2*L + 1 := by
    simpa [hLdef] using hK
  have hexp1 : ∀ x ∈ Set.Icc (1:ℝ) (21*L),
      Real.exp (-(shellB d x)^2/(2*(K:ℝ))) ≤ Real.exp 1.1 * Real.exp (-(x^2)/(8*L)) :=
    fun x hx => exp_bound_twentyone hd2 hdrpos hdr2 hdr20 hLpos hL1 hKposR hK16 h126L h34730L2 hx

  -- `L³√L ≤ 128 d`
  have hY1 : (1:ℝ) ≤ Real.sqrt (Real.sqrt (d:ℝ)) := by linarith [hXX20]
  have hL3' : L^3 ≤ 64 * (Real.sqrt (Real.sqrt (d:ℝ)))^3 := by
    have h := pow_le_pow_left₀ (by positivity) hL_le 3
    have h2 : (4 * Real.sqrt (Real.sqrt (d:ℝ)))^3 = 64 * (Real.sqrt (Real.sqrt (d:ℝ)))^3 := by ring
    rwa [h2] at h
  have hsqL2 : Real.sqrt L ≤ 2 * Real.sqrt (Real.sqrt (d:ℝ)) := by
    have h := Real.sqrt_le_sqrt hL_le
    have h2 : Real.sqrt (4 * Real.sqrt (Real.sqrt (d:ℝ)))
        = 2 * Real.sqrt (Real.sqrt (Real.sqrt (d:ℝ))) := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
      congr 1
      rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    rw [h2] at h
    set Y : ℝ := Real.sqrt (Real.sqrt (d:ℝ)) with hY
    have hY1 : (1:ℝ) ≤ Y := by rw [hY]; linarith [hXX20]
    have h3 : Real.sqrt Y ≤ Y := by
      have hYpos : (0:ℝ) < Y := by linarith [hY1]
      have hYY : Y ≤ Y * Y := by
        calc Y = Y*1 := by ring
          _ ≤ Y*Y := mul_le_mul_of_nonneg_left hY1 (le_of_lt hYpos)
      calc Real.sqrt Y ≤ Real.sqrt (Y*Y) := Real.sqrt_le_sqrt hYY
        _ = Y := Real.sqrt_mul_self hYpos.le
    have h4 : Real.sqrt (Real.sqrt (Real.sqrt (d:ℝ))) = Real.sqrt Y := by rw [hY]
    rw [h4] at h
    linarith [h, h3]
  have hL3sqL : L^3 * Real.sqrt L ≤ 128*(d:ℝ) := by
    set Y : ℝ := Real.sqrt (Real.sqrt (d:ℝ)) with hY
    have hY4 : Y^4 = (d:ℝ) := by rw [hY]; exact hXX4
    have h1 : L^3 * Real.sqrt L ≤ (64*Y^3) * (2*Y) :=
      mul_le_mul hL3' hsqL2 (Real.sqrt_nonneg _) (by positivity)
    have h2 : (64*Y^3) * (2*Y) = 128 * (Y^3 * Y) := by ring
    have h3 : Y^3 * Y = Y^4 := by ring
    rw [h2, h3, hY4] at h1
    linarith [h1]
  -- sum bound `≤ K`
  have hsumK : ∀ x : ℝ, (∑ k ∈ Finset.Icc 1 K,
      (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ | shellB d x / Real.sqrt (k:ℝ) ≤ z}) ≤ (K:ℝ) := by
    intro x
    calc _ ≤ ∑ k ∈ Finset.Icc 1 K, (1:ℝ) := by
          apply Finset.sum_le_sum
          intro k hk
          exact measureReal_le_one
      _ = (K:ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
          congr 1
          rw [Nat.card_Icc]
          omega
  -- the constant `(1/√(2π))·e^{1.1} ≤ 1.3`
  have hC13 : (1/Real.sqrt (2*Real.pi)) * Real.exp 1.1 ≤ 1.3 := by
    have h1 : (2.44:ℝ) ≤ Real.sqrt (2*Real.pi) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      nlinarith [Real.pi_gt_three]
    have h4 : Real.exp (0.1:ℝ) ≤ 1.12 := by
      have h5 : Real.exp (0.1:ℝ) ≤ 1/(1-(0.1:ℝ)) :=
        Commons.Analysis.Exponential.exp_le_one_div_one_sub (by norm_num)
      have h5' : (1/(1-(0.1:ℝ))) ≤ 1.12 := by norm_num
      linarith only [h5, h5']
    have h6 : Real.exp 1 ≤ 2.72 := by linarith [Real.exp_one_lt_d9]
    have h2 : Real.exp 1.1 ≤ 3.05 := by
      have h3 : Real.exp 1.1 = Real.exp 1 * Real.exp (0.1:ℝ) := by
        rw [← Real.exp_add]; norm_num
      rw [h3]
      calc Real.exp 1 * Real.exp (0.1:ℝ) ≤ 2.72 * 1.12 :=
            mul_le_mul h6 h4 (Real.exp_pos _).le (by norm_num)
        _ ≤ 3.05 := by norm_num
    have h8 : 1.3 * (2.44:ℝ) ≤ 1.3 * Real.sqrt (2*Real.pi) :=
      mul_le_mul_of_nonneg_left h1 (by norm_num)
    have h9 : Real.exp 1.1 ≤ 1.3 * Real.sqrt (2*Real.pi) := by linarith only [h2, h8]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < Real.sqrt (2*Real.pi))]
    simpa using h9
  -- region 0 (isolated lemma `region0_le`)
  have hreg0 : ∫ x in (0:ℝ)..1, F ((d:ℝ)⁻¹ * x + 1) ≤ 5*10^4*(d:ℝ)^4 :=
    region0_le (d := d) (K := K) (L := L) (F := F) hdr1 hKle hLle hpt hFnn hweight hsumK hsumnn

  -- region 1
  -- region 1 (isolated lemma `region1_le`)
  have hreg1 : ∫ x in (1:ℝ)..(21*L), F ((d:ℝ)⁻¹ * x + 1) ≤ 5*10^5*(d:ℝ)^4 :=
    region1_le (d := d) (K := K) (L := L) (F := F) hLdef hdrpos hdr1 hd2 hL1 h120L hLle hLpos hKle hA1 hA2 hC13 hL3sqL hL2d hpt hsumnn hFnn hweight hshellBpos1 hshellBlow1 hsumSB hsumK hexp1 hXX4

  -- helper: `shellB > 0` on `x ≥ 0`
  have hshellBposany : ∀ x : ℝ, 0 ≤ x → 0 < shellB d x :=
    fun x hx => mul_pos (shellA_pos hd2 hx) (by positivity)
  have hshellBlow2c : ∀ x ∈ Set.Icc (21*L) ((d:ℝ)/2), 10*L*(d:ℝ) ≤ shellB d x := by
    intro x hxx
    rcases le_or_gt x (144*L) with h | h
    · have hb := hshellB_low2b x ⟨hxx.1, h⟩
      nlinarith [hb, hxx.1, hdrpos, hLpos]
    · have hb := hshellB_low2 x ⟨le_of_lt h, hxx.2⟩
      nlinarith [hb, hxx.1, hdrpos, hLpos]
  -- region 2 (isolated lemma `region2_le`)
  have hreg2 : ∫ x in (21*L)..((d:ℝ)/2), F ((d:ℝ)⁻¹ * x + 1) ≤ 5*10^4*(d:ℝ)^4 :=
    region2_le (d := d) (K := K) (L := L) (F := F) hdrpos hdr1 hLpos hL1 h120L hA1 hA2 hpt hFnn hweight hsumnn hsumSB hshellBposany hshellBlow2c hexp2

  -- region 3
  -- region 3 (isolated lemma `region3_le`)
  have hreg3 : ∫ x in ((d:ℝ)/2)..(d:ℝ), F ((d:ℝ)⁻¹ * x + 1) ≤ 5*10^4*(d:ℝ)^4 :=
    region3_le (d := d) (K := K) (L := L) (F := F) hdrpos hdr1 hdr20 hLpos hL1 hL2d hsqL hA1 hA2 hpt hFnn hweight hsumnn hsumSB hshellBposany hshellB_low3 hexp3

  -- measurability of `F`
  have hFmeas : Measurable F := by
    rw [hF]
    apply Measurable.mul
    · fun_prop
    · apply Finset.measurable_sum
      intro k hk
      have hanti : Antitone (fun a : ℝ => (ProbabilityTheory.stdGaussian ℝ).real (Set.Ici a)) :=
        fun a b hab => measureReal_mono (Set.Ici_subset_Ici.mpr hab) (measure_ne_top _ _)
      exact hanti.measurable.comp (by fun_prop)
  -- integrability of the integrand on `[0,d]`
  have hIntF0 : IntervalIntegrable (fun x : ℝ => F ((d:ℝ)⁻¹*x+1)) volume (0:ℝ) (d:ℝ) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (le_of_lt hdrpos)]
    refine IntegrableOn.of_bound (measure_Ioc_lt_top) ?_ ((K:ℝ) * 2^(d-1)) ?_
    · exact ((hFmeas.comp (by fun_prop)).aestronglyMeasurable)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have hx0 : 0 ≤ x := hx.1.le
      have hxd : x ≤ (d:ℝ) := hx.2
      have hFb : F ((d:ℝ)⁻¹*x+1) ≤ (K:ℝ) * 2^(d-1) := by
        rw [hpt x]
        have hww : (1 + x/(d:ℝ))^(d-1) ≤ 2^(d-1) := by
          apply pow_le_pow_left₀ (by positivity)
          have hxd2 : x/(d:ℝ) ≤ 1 := by rw [div_le_one hdrpos]; exact hxd
          linarith
        calc (1 + x/(d:ℝ))^(d-1) * (∑ k ∈ Finset.Icc 1 K, (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ | shellB d x / Real.sqrt (k:ℝ) ≤ z})
            ≤ 2^(d-1) * (∑ k ∈ Finset.Icc 1 K, (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ | shellB d x / Real.sqrt (k:ℝ) ≤ z}) :=
              mul_le_mul_of_nonneg_right hww (hsumnn x)
          _ ≤ 2^(d-1) * (K:ℝ) := mul_le_mul_of_nonneg_left (hsumK x) (by positivity)
          _ = (K:ℝ) * 2^(d-1) := by ring
      have hF0 : 0 ≤ F ((d:ℝ)⁻¹*x+1) := hFnn x hx0
      rw [Real.norm_eq_abs, abs_of_nonneg hF0]
      exact hFb
  have hIcc01 : Set.Icc (0:ℝ) 1 ⊆ Set.Icc (0:ℝ) (d:ℝ) :=
    Set.Icc_subset_Icc (le_refl 0) (by linarith)
  have hIcc121 : Set.Icc (1:ℝ) (21*L) ⊆ Set.Icc (0:ℝ) (d:ℝ) :=
    Set.Icc_subset_Icc (by norm_num) (by linarith [h120L, hL1])
  have hIcc21d2 : Set.Icc (21*L) ((d:ℝ)/2) ⊆ Set.Icc (0:ℝ) (d:ℝ) :=
    Set.Icc_subset_Icc (by linarith [hL1]) (by linarith [hdrpos])
  have hIccd2d : Set.Icc ((d:ℝ)/2) (d:ℝ) ⊆ Set.Icc (0:ℝ) (d:ℝ) :=
    Set.Icc_subset_Icc (by linarith [hdrpos]) (le_refl _)
  have h01 : IntervalIntegrable (fun x : ℝ => F ((d:ℝ)⁻¹*x+1)) volume (0:ℝ) 1 := by
    apply hIntF0.mono_set
    rwa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1), Set.uIcc_of_le (le_of_lt hdrpos)]
  have h121 : IntervalIntegrable (fun x : ℝ => F ((d:ℝ)⁻¹*x+1)) volume (1:ℝ) (21*L) := by
    apply hIntF0.mono_set
    rwa [Set.uIcc_of_le (by linarith [hL1]), Set.uIcc_of_le (le_of_lt hdrpos)]
  have h21d2 : IntervalIntegrable (fun x : ℝ => F ((d:ℝ)⁻¹*x+1)) volume (21*L) ((d:ℝ)/2) := by
    apply hIntF0.mono_set
    rwa [Set.uIcc_of_le (by linarith [h120L]), Set.uIcc_of_le (le_of_lt hdrpos)]
  have hd2d : IntervalIntegrable (fun x : ℝ => F ((d:ℝ)⁻¹*x+1)) volume ((d:ℝ)/2) (d:ℝ) := by
    apply hIntF0.mono_set
    rwa [Set.uIcc_of_le (by linarith [hdrpos]), Set.uIcc_of_le (le_of_lt hdrpos)]
  have h0_21L : IntervalIntegrable (fun x : ℝ => F ((d:ℝ)⁻¹*x+1)) volume (0:ℝ) (21*L) :=
    hIntF0.mono_set (by
      rw [Set.uIcc_of_le (by linarith [hL1]), Set.uIcc_of_le (le_of_lt hdrpos)]
      exact Set.Icc_subset_Icc le_rfl (by linarith [h120L, hL1]))
  have h0d2 : IntervalIntegrable (fun x : ℝ => F ((d:ℝ)⁻¹*x+1)) volume (0:ℝ) ((d:ℝ)/2) :=
    hIntF0.mono_set (by
      rw [Set.uIcc_of_le (by linarith [hdrpos]), Set.uIcc_of_le (le_of_lt hdrpos)]
      exact Set.Icc_subset_Icc le_rfl (by linarith [hdrpos]))
  have hdecomp : ∫ x in (0:ℝ)..(d:ℝ), F ((d:ℝ)⁻¹ * x + 1)
      = (∫ x in (0:ℝ)..1, F ((d:ℝ)⁻¹ * x + 1))
        + (∫ x in (1:ℝ)..(21*L), F ((d:ℝ)⁻¹ * x + 1))
        + (∫ x in (21*L)..((d:ℝ)/2), F ((d:ℝ)⁻¹ * x + 1))
        + (∫ x in ((d:ℝ)/2)..(d:ℝ), F ((d:ℝ)⁻¹ * x + 1)) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals h0d2 hd2d,
        ← intervalIntegral.integral_add_adjacent_intervals h0_21L h21d2,
        ← intervalIntegral.integral_add_adjacent_intervals h01 h121]
    try ring
  have htotal : ∫ x in (0:ℝ)..(d:ℝ), F ((d:ℝ)⁻¹ * x + 1) ≤ 10^6*(d:ℝ)^4 := by
    rw [hdecomp]
    have hd4nn : (0:ℝ) ≤ (d:ℝ)^4 := by positivity
    linarith [hreg0, hreg1, hreg2, hreg3, hd4nn]
  rw [hsubst]
  calc ((d:ℝ))⁻¹ * ∫ x in (0:ℝ)..(d:ℝ), F ((d:ℝ)⁻¹ * x + 1)
      ≤ ((d:ℝ))⁻¹ * (10^6*(d:ℝ)^4) := mul_le_mul_of_nonneg_left htotal (by positivity)
    _ = 10^6 * (d:ℝ)^3 := by
        field_simp



end Commons.Analysis.Gaussian
