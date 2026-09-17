import Mathlib
import Submission.Commons.Measure.EuclideanSpace.volume_ball_succ_integral

/-!
# The unit ball of `ℝ^d` has volume at most `1` for `d ≥ 29`

For the q-ary construction of the starting lattice we need `ω_d ≤ 1` in large dimensions, where
`ω_d` is the volume of the unit ball of `ℝ^d`.

The proof uses the Fubini recursion `ω_{n+1} = c_n · ω_n` with
`c_n = ∫_{-1}^1 (1-u²)^{n/2}du` (`Commons.Measure.EuclideanSpace.volume_ball_succ_integral`) and
the elementary estimate `c_n ≤ √(2π/n) ≤ 1/2` for `n ≥ 26`; the base case `ω_28 = π^14/14!`
is evaluated with `EuclideanSpace.volume_ball`.
-/

open MeasureTheory Metric
open scoped ENNReal

namespace Submission.OmBound

noncomputable section

/-- The volume of the unit ball of `ℝ^d`. -/
def omega (d : ℕ) : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal

/-- The one-dimensional section integral `c_n = ∫_{-1}^1 (1-u²)^{n/2}du`. -/
def cn (n : ℕ) : ℝ := ∫ u in (-1:ℝ)..1, (1 - u ^ 2) ^ ((n : ℝ) / 2)

lemma omega_succ (n : ℕ) : omega (n + 1) = cn n * omega n :=
  Commons.Measure.EuclideanSpace.volume_ball_succ_integral n

lemma one_sub_sq_nonneg {u : ℝ} (hu : u ∈ Set.Icc (-1:ℝ) 1) : 0 ≤ 1 - u ^ 2 := by
  have h : u ^ 2 ≤ 1 := by
    have h1 : |u| ≤ 1 := abs_le.mpr ⟨hu.1, hu.2⟩
    have h2 := pow_le_one₀ (n := 2) (abs_nonneg u) h1
    rwa [sq_abs] at h2
  linarith

lemma cn_nonneg (n : ℕ) : 0 ≤ cn n := by
  rw [cn]
  refine intervalIntegral.integral_nonneg (by norm_num) fun u hu => ?_
  exact Real.rpow_nonneg (one_sub_sq_nonneg ⟨hu.1, hu.2⟩) _

lemma one_sub_sq_rpow_le_exp {n : ℕ} {u : ℝ} (hu : u ∈ Set.Icc (-1:ℝ) 1) :
    (1 - u ^ 2) ^ ((n : ℝ) / 2) ≤ Real.exp (-((n : ℝ) / 2) * u ^ 2) := by
  have h0 := one_sub_sq_nonneg hu
  rcases lt_or_eq_of_le h0 with h1 | h1
  · have h2 : Real.log (1 - u ^ 2) ≤ -u ^ 2 := by
      have := Real.log_le_sub_one_of_pos h1
      linarith
    calc (1 - u ^ 2) ^ ((n : ℝ) / 2)
        = Real.exp (((n : ℝ) / 2) * Real.log (1 - u ^ 2)) := by
          rw [Real.rpow_def_of_pos h1, mul_comm]
      _ ≤ Real.exp (((n : ℝ) / 2) * (-u ^ 2)) := by
          refine Real.exp_le_exp.mpr ?_
          have : (0 : ℝ) ≤ (n : ℝ) / 2 := by positivity
          nlinarith [h2, this]
      _ = Real.exp (-((n : ℝ) / 2) * u ^ 2) := by ring_nf
  · have hu2 : u ^ 2 = 1 := by linarith
    have hmain : (0:ℝ) ^ ((n : ℝ) / 2) ≤ Real.exp (-((n : ℝ) / 2) * 1) := by
      rcases eq_or_ne ((n : ℝ) / 2) 0 with h | h
      · rw [h, Real.rpow_zero]
        norm_num
      · rw [Real.zero_rpow h]
        exact Real.exp_nonneg _
    rw [h1.symm, hu2]
    exact hmain

lemma integral_exp_neg_mul_sq {n : ℕ} (hn : 1 ≤ n) :
    (∫ u : ℝ, Real.exp (-((n : ℝ) / 2) * u ^ 2)) = Real.sqrt (2 * Real.pi / n) := by
  have hb : (0 : ℝ) < (n : ℝ) / 2 := by
    have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  have h := integral_gaussian ((n : ℝ) / 2)
  have h2 : Real.pi / ((n:ℝ)/2) = 2 * Real.pi / n := by
    rw [div_div_eq_mul_div]
    ring
  rw [h, h2]

lemma cn_le {n : ℕ} (hn : 1 ≤ n) : cn n ≤ Real.sqrt (2 * Real.pi / n) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hb : (0 : ℝ) < (n : ℝ) / 2 := by linarith
  have hgint : Integrable (fun u : ℝ => Real.exp (-((n : ℝ) / 2) * u ^ 2)) volume :=
    integrable_exp_neg_mul_sq hb
  have h1 : cn n ≤ ∫ u in (-1:ℝ)..1, Real.exp (-((n : ℝ) / 2) * u ^ 2) := by
    rw [cn]
    refine intervalIntegral.integral_mono_on (by norm_num) ?_ hgint.intervalIntegrable ?_
    · exact (by fun_prop : ContinuousOn (fun u : ℝ => 1 - u ^ 2) (Set.uIcc (-1:ℝ) 1)).rpow_const
        (fun x _ => Or.inr (by positivity)) |>.intervalIntegrable
    · intro u hu
      exact one_sub_sq_rpow_le_exp ⟨hu.1, hu.2⟩
  refine h1.trans ?_
  rw [intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1)]
  calc ∫ u in Set.Ioc (-1:ℝ) 1, Real.exp (-((n : ℝ) / 2) * u ^ 2)
      ≤ ∫ u in Set.univ, Real.exp (-((n : ℝ) / 2) * u ^ 2) :=
        setIntegral_mono_set hgint.integrableOn
          (Filter.Eventually.of_forall fun x => Real.exp_nonneg _)
          (Filter.Eventually.of_forall fun x _ => Set.mem_univ x)
    _ = ∫ u : ℝ, Real.exp (-((n : ℝ) / 2) * u ^ 2) := setIntegral_univ
    _ = Real.sqrt (2 * Real.pi / n) := integral_exp_neg_mul_sq hn

lemma sqrt_two_pi_div_le_half {n : ℕ} (hn : 26 ≤ n) : Real.sqrt (2 * Real.pi / n) ≤ 1 / 2 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hnR : (26 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpi : Real.pi < 3.15 := lt_trans Real.pi_lt_d20 (by norm_num)
  have hle : 2 * Real.pi / n ≤ 1 / 4 := by
    rw [div_le_iff₀ hnpos]
    linarith
  calc Real.sqrt (2 * Real.pi / n) ≤ Real.sqrt (1 / 4) := Real.sqrt_le_sqrt hle
    _ = 1 / 2 := by rw [show (1:ℝ)/4 = (1/2)^2 by norm_num, Real.sqrt_sq (by norm_num)]

lemma cn_le_half {n : ℕ} (hn : 26 ≤ n) : cn n ≤ 1 / 2 :=
  (cn_le (by omega)).trans (sqrt_two_pi_div_le_half hn)

lemma omega_nonneg (d : ℕ) : 0 ≤ omega d := by
  rw [omega]; exact ENNReal.toReal_nonneg

lemma omega_mul_two_pow (d : ℕ) (hd : 28 ≤ d) :
    omega d * 2 ^ (d - 28) ≤ omega 28 := by
  induction d, hd using Nat.le_induction with
  | base => simp
  | succ d hd ih =>
    have hrec := omega_succ d
    have hc : cn d ≤ 1 / 2 := cn_le_half (by omega)
    have hnn := omega_nonneg d
    have h1 : omega (d + 1) ≤ omega d / 2 := by
      rw [hrec]
      nlinarith [hc, hnn, cn_nonneg d]
    have hpow : (2:ℝ) ^ (d + 1 - 28) = 2 ^ (d - 28) * 2 := by
      rw [show d + 1 - 28 = (d - 28) + 1 by omega, pow_succ]
    rw [hpow]
    calc omega (d + 1) * (2 ^ (d - 28) * 2) ≤ (omega d / 2) * (2 ^ (d - 28) * 2) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = omega d * 2 ^ (d - 28) := by ring
      _ ≤ omega 28 := ih

lemma omega_twenty_eight_le_two : omega 28 ≤ 2 := by
  have h := EuclideanSpace.volume_ball (ι := Fin 28) (0 : EuclideanSpace ℝ (Fin 28)) 1
  have hcard : Fintype.card (Fin 28) = 28 := Fintype.card_fin 28
  rw [hcard] at h
  have hsimp : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 28)) 1))
      = ENNReal.ofReal ((Real.sqrt Real.pi) ^ 28 / Real.Gamma ((28:ℝ)/2 + 1)) := by
    rw [h]; simp
  have hgamma : Real.Gamma ((28:ℝ)/2 + 1) = ((Nat.factorial 14 : ℕ) : ℝ) := by
    rw [show (28:ℝ)/2 + 1 = ((14:ℕ):ℝ) + 1 by norm_num]
    exact Real.Gamma_nat_eq_factorial 14
  have harg : (0:ℝ) ≤ (Real.sqrt Real.pi) ^ 28 / Real.Gamma ((28:ℝ)/2 + 1) := by
    refine div_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) ?_
    rw [hgamma]; norm_num
  rw [omega, hsimp, ENNReal.toReal_ofReal harg, hgamma]
  have hsq : (Real.sqrt Real.pi) ^ 28 = Real.pi ^ 14 := by
    rw [show (28:ℕ) = 2 * 14 from rfl, pow_mul, Real.sq_sqrt Real.pi_nonneg]
  rw [hsq]
  have hpi2 : Real.pi ^ 14 ≤ (3.15:ℝ) ^ 14 :=
    pow_le_pow_left₀ Real.pi_nonneg (le_of_lt (lt_trans Real.pi_lt_d20 (by norm_num))) 14
  have hfact : ((Nat.factorial 14 : ℕ) : ℝ) = 87178291200 := by norm_num
  rw [hfact]
  have hnum : (3.15:ℝ) ^ 14 ≤ 2 * 87178291200 := by norm_num
  linarith

/-- **The volume of the unit ball of `ℝ^d` is at most `1` for `d ≥ 29`.** -/
theorem omega_le_one {d : ℕ} (hd : 29 ≤ d) : omega d ≤ 1 := by
  have h1 := omega_mul_two_pow d (by omega)
  have h2 : omega d * 2 ≤ omega 28 := by
    have : (2:ℝ) ≤ 2 ^ (d - 28) := by
      have : (1:ℕ) ≤ d - 28 := by omega
      calc (2:ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (d - 28) := pow_le_pow_right₀ (by norm_num) this
    nlinarith [h1, this, omega_nonneg d]
  nlinarith [h2, omega_twenty_eight_le_two]

end

end Submission.OmBound
