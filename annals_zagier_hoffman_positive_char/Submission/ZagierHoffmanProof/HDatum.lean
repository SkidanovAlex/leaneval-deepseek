import Submission.ZagierHoffmanProof.ATInterp
import Submission.ZagierHoffmanProof.GenOmega
import Submission.ZagierHoffmanProof.ACMplDatum
import Submission.ZagierHoffmanProof.NestP

/-!
# The Anderson–Thakur datum `(s, H_s)`: the analytic hypotheses

For the proof of Theorem D (Ngo Dac §6) Steps 1–2 run the merged dual `t`-motive of the datum
`(s_j, H_{s_j})` — the tuple entries are the Anderson–Thakur polynomials `H_n = ambH F n`
(`ATPoly.lean`), *not* `1`.  This file supplies the analytic inputs needed by
`LinearIndependence.linear_independence` for that datum:

* `ambH_coeff_mem` — the coefficients of `H_n` lie in `A_0 = F_q[θ]`;
* `gSuperEntire_ambH` — `H_n ∈ ε`;
* ★★★ `gIsSmall_ambOmega_pow_mul_ambH` — `GIsSmall γ (Ω^s·H_s)`, the smallness of the datum.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
open Polynomial PowerSeries Finset
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## §1. `A_0`-coefficients of `H_n` -/

lemma coeff_one_mem_ambA0 (m : ℕ) : (1 : Polynomial (Ambient F)).coeff m ∈ ambA F 0 := by
  rw [Polynomial.coeff_one]
  split_ifs
  · exact ambA_one_mem F 0
  · exact ambA_zero_mem 0

lemma coeff_X_pow_mem_ambA0 (k m : ℕ) : ((Polynomial.X ^ k : Polynomial (Ambient F)).coeff m)
    ∈ ambA F 0 := by
  rw [Polynomial.coeff_X_pow]
  split_ifs
  · exact ambA_one_mem F 0
  · exact ambA_zero_mem 0

lemma coeff_X_mem_ambA0 (m : ℕ) : (Polynomial.X : Polynomial (Ambient F)).coeff m ∈ ambA F 0 := by
  rw [Polynomial.coeff_X]
  split_ifs
  · exact ambA_one_mem F 0
  · exact ambA_zero_mem 0

lemma coeff_C_mem_ambA0 {c : Ambient F} (hc : c ∈ ambA F 0) (m : ℕ) :
    (Polynomial.C c).coeff m ∈ ambA F 0 := by
  rw [Polynomial.coeff_C]
  split_ifs
  · exact hc
  · exact ambA_zero_mem 0

lemma ambTheta_pow_mem_ambA0 : (ambTheta F) ^ Nat.card F ∈ ambA F 0 :=
  ambA_pow_mem F 0 ambTheta_mem_ambA_zero (Nat.card F)

/-- The coefficients of `X^q - C (θ^q)` lie in `A_0`. -/
lemma coeff_X_pow_sub_C_mem_ambA0 (m : ℕ) :
    ((Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F)
      : Polynomial (Ambient F))).coeff m ∈ ambA F 0 := by
  rw [Polynomial.coeff_sub]
  exact ambA_sub_mem F (coeff_X_pow_mem_ambA0 F _ m) (coeff_C_mem_ambA0 F (ambTheta_pow_mem_ambA0 F) m)

/-- **The coefficients of `H_n` lie in `A_0 = F_q[θ]`.** -/
theorem ambH_coeff_mem (n m : ℕ) : ((ambH F n).coeff m) ∈ ambA F 0 := by
  rcases le_or_gt n (Nat.card F) with hn | hn
  · rw [ambH_of_le F hn]
    exact coeff_one_mem_ambA0 F m
  · rw [ambH_of_gt F hn, Polynomial.coeff_add, Polynomial.coeff_sub]
    refine ambA_add_mem F (ambA_sub_mem F (coeff_X_pow_mem_ambA0 F _ _)
      (coeff_X_mem_ambA0 F _)) ?_
    exact coeff_mul_mem_ambA0 (fun m => coeff_C_mem_ambA0 F (ambA_natCast_mem 0 _) m)
      (coeff_X_pow_sub_C_mem_ambA0 F) m

/-! ## §2. `H_n` is entire -/

/-- `H_n` is a polynomial, hence super-entire. -/
theorem gSuperEntire_ambH (n : ℕ) :
    GSuperEntire ambGamma ((ambH F n : Polynomial (Ambient F)) : PowerSeries (Ambient F)) :=
  GSuperEntire.polynomial ambGamma_pos ambGamma_le_one _

/-! ## §3. The coefficient bounds for the powers of `Ω` -/

/-- `δ = (v θ)^{-1} = exp (-(q-1))`. -/
noncomputable def ambDelta (F : Type*) [Field F] [Finite F] : ℚᵐ⁰ := (Valued.v (ambTheta F))⁻¹

lemma ambDelta_eq : ambDelta F = WithZero.exp (-((Nat.card F : ℚ) - 1)) := by
  rw [ambDelta, v_ambTheta, ← WithZero.exp_neg]

lemma ambDelta_le_one : ambDelta F ≤ 1 := by
  rw [ambDelta_eq, ← WithZero.exp_zero, WithZero.exp_le_exp]
  have h : (2 : ℚ) ≤ (Nat.card F : ℚ) := by exact_mod_cast two_le_card_field F
  linarith

lemma ambDelta_pos : 0 < ambDelta F := by rw [ambDelta_eq]; exact WithZero.exp_pos

/-- `sharpExpGen q m ≥ q` for `m ≥ 1`. -/
lemma le_sharpExpGen {q m : ℕ} (hm : 1 ≤ m) : q ≤ sharpExpGen q m := by
  have hnz : m ≠ 0 := by omega
  have h1 : sharpExpGen q m = sharpExpGen q (m - 1) + q ^ ((m - 1) + 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hm]
    exact sharpExpGen_succ q (m - 1)
  rw [h1, Nat.sub_add_cancel hm]
  exact le_trans (Nat.le_self_pow hnz q) (Nat.le_add_left _ _)

/-- **The coefficient bound for `Ω̃ = atOmegaGen`**: level `0` is bounded by `1`, levels `≥ 1` by
`δ^q`. -/
theorem v_coeff_atOmegaGen_le_delta (m : ℕ) :
    Valued.v (PowerSeries.coeff m (atOmegaGen (Nat.card F) (ambTheta F)))
      ≤ if m = 0 then 1 else (ambDelta F) ^ Nat.card F := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · rw [if_neg hm]
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    have hne1 : ambDelta F ≠ 1 := by
      intro h1
      rw [ambDelta_eq, WithZero.exp_eq_one] at h1
      have h2 : ((Nat.card F : ℚ) - 1) = 0 := by linarith [neg_eq_zero.mp h1]
      have h3 : (2 : ℚ) ≤ Nat.card F := by exact_mod_cast two_le_card_field F
      linarith
    have hδ1 : ambDelta F < 1 := lt_of_le_of_ne (ambDelta_le_one F) hne1
    have h := v_coeff_atOmegaGen_le_sharp_gen (q := Nat.card F) (θ := ambTheta F)
      (γ := ambDelta F) (ambDelta_pos F) le_rfl hδ1 gammaArchimedean_rat
      (two_le_ambCard F) m
    refine le_trans h ?_
    exact pow_le_pow_of_le_one (zero_le) (ambDelta_le_one F) (le_sharpExpGen hm1)

/-- **A power of a series whose level-`0` coefficient is bounded by `b₀ ≤ 1` and whose other
coefficients are bounded by `B ≤ 1` again satisfies the same bounds.** -/
lemma v_coeff_pow_split {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] {f : PowerSeries K} {B b₀ : Γ₀} (hB : B ≤ 1) (hb₀ : b₀ ≤ 1)
    (hf : ∀ m : ℕ, Valued.v (PowerSeries.coeff m f) ≤ if m = 0 then b₀ else B) (s : ℕ) :
    ∀ m : ℕ, Valued.v (PowerSeries.coeff m (f ^ s)) ≤ if m = 0 then b₀ ^ s else B := by
  induction s with
  | zero =>
    intro m
    rw [pow_zero, PowerSeries.coeff_one]
    split_ifs with hm
    · rw [pow_zero]; exact le_of_eq (map_one _)
    · rw [map_zero]; exact zero_le
  | succ s ih =>
    intro m
    rw [pow_succ]
    rcases eq_or_ne m 0 with rfl | hm
    · rw [if_pos rfl]
      have hcoeff : PowerSeries.coeff 0 (f ^ s * f)
          = PowerSeries.coeff 0 (f ^ s) * PowerSeries.coeff 0 f := by
        rw [PowerSeries.coeff_mul]
        refine Finset.sum_eq_single (0, 0) (fun b hb hne => ?_)
          (fun h => absurd (by simp) h)
        have hsum : b.1 + b.2 = 0 := HasAntidiagonal.mem_antidiagonal.mp hb
        exact absurd (Prod.ext (by omega) (by omega)) hne
      rw [hcoeff, Valuation.map_mul]
      have hA : Valued.v (PowerSeries.coeff 0 (f ^ s)) ≤ b₀ ^ s := by
        have hh := ih 0
        rwa [if_pos rfl] at hh
      have hB' : Valued.v (PowerSeries.coeff 0 f) ≤ b₀ := by
        have hh := hf 0
        rwa [if_pos rfl] at hh
      calc Valued.v (PowerSeries.coeff 0 (f ^ s)) * Valued.v (PowerSeries.coeff 0 f)
          ≤ b₀ ^ s * b₀ := mul_le_mul' hA hB'
        _ = b₀ ^ (s + 1) := (pow_succ b₀ s).symm
    · rw [if_neg hm, PowerSeries.coeff_mul]
      refine Valuation.map_sum_le _ fun p hp => ?_
      rw [Valuation.map_mul]
      have hsum : p.1 + p.2 = m := HasAntidiagonal.mem_antidiagonal.mp hp
      by_cases hj : p.2 = 0
      · have h1' : Valued.v (PowerSeries.coeff p.1 (f ^ s)) ≤ B := by
          have hh := ih p.1
          rwa [if_neg (by omega : p.1 ≠ 0)] at hh
        have h2' : Valued.v (PowerSeries.coeff 0 f) ≤ b₀ := by
          have hh := hf 0
          rwa [if_pos rfl] at hh
        rw [hj]
        calc Valued.v (PowerSeries.coeff p.1 (f ^ s)) * Valued.v (PowerSeries.coeff 0 f)
            ≤ B * b₀ := mul_le_mul' h1' h2'
          _ ≤ B * 1 := mul_le_mul_of_nonneg_left hb₀ zero_le
          _ = B := mul_one B
      · have h2' : Valued.v (PowerSeries.coeff p.2 f) ≤ B := by
          have hh := hf p.2
          rwa [if_neg hj] at hh
        have h1'' : Valued.v (PowerSeries.coeff p.1 (f ^ s)) ≤ 1 := by
          by_cases hi : p.1 = 0
          · rw [hi]
            have hh := ih 0
            rw [if_pos rfl] at hh
            exact le_trans hh (pow_le_one₀ (zero_le) hb₀)
          · have hh := ih p.1
            rw [if_neg hi] at hh
            exact le_trans hh hB
        calc Valued.v (PowerSeries.coeff p.1 (f ^ s)) * Valued.v (PowerSeries.coeff p.2 f)
            ≤ 1 * B := mul_le_mul' h1'' h2'
          _ = B := one_mul B

/-- **The coefficient bound for `Ω̃^s`**: level `0` is `≤ 1`, levels `≥ 1` are `≤ δ^q`. -/
theorem v_coeff_atOmegaGen_pow_le (s m : ℕ) :
    Valued.v (PowerSeries.coeff m (atOmegaGen (Nat.card F) (ambTheta F) ^ s))
      ≤ if m = 0 then 1 else (ambDelta F) ^ Nat.card F := by
  have h := v_coeff_pow_split (f := atOmegaGen (Nat.card F) (ambTheta F))
    (B := (ambDelta F) ^ Nat.card F) (b₀ := 1)
    (pow_le_one₀ (zero_le) (ambDelta_le_one F)) le_rfl
    (fun m => v_coeff_atOmegaGen_le_delta F m)
    s m
  rw [one_pow] at h
  exact h

/-- `Ω^s = C (μ^s)·Ω̃^s`. -/
lemma ambOmega_pow_eq (s : ℕ) :
    (ambOmega F) ^ s = PowerSeries.C ((ambMu F) ^ s)
      * (atOmegaGen (Nat.card F) (ambTheta F)) ^ s := by
  rw [ambOmega, mul_pow, map_pow]

/-- **The coefficient bound for `Ω^s`, level `0`**: `v (coeff 0 (Ω^s)) ≤ exp (-q·s)`. -/
theorem v_coeff_ambOmega_pow_zero (s : ℕ) :
    Valued.v (PowerSeries.coeff 0 ((ambOmega F) ^ s))
      ≤ WithZero.exp (-(Nat.card F : ℚ) * s) := by
  have h1 : Valued.v (PowerSeries.coeff 0 (atOmegaGen (Nat.card F) (ambTheta F) ^ s)) ≤ 1 := by
    have hh := v_coeff_atOmegaGen_pow_le F s 0
    rwa [if_pos rfl] at hh
  rw [ambOmega_pow_eq F s, PowerSeries.coeff_C_mul, map_mul, map_pow, v_ambMu,
    ← WithZero.exp_nsmul, nsmul_eq_mul]
  calc WithZero.exp (s * -(Nat.card F : ℚ))
        * Valued.v (PowerSeries.coeff 0 (atOmegaGen (Nat.card F) (ambTheta F) ^ s))
      ≤ WithZero.exp (s * -(Nat.card F : ℚ)) * 1 := mul_le_mul_of_nonneg_left h1 zero_le
    _ = WithZero.exp (-(Nat.card F : ℚ) * s) := by
        rw [mul_one, mul_comm]

/-- **The coefficient bound for `Ω^s`, levels `≥ 1`**:
`v (coeff m (Ω^s)) ≤ exp (-q·s - q(q-1))`. -/
theorem v_coeff_ambOmega_pow_succ {s m : ℕ} (hm : 1 ≤ m) :
    Valued.v (PowerSeries.coeff m ((ambOmega F) ^ s))
      ≤ WithZero.exp (-(Nat.card F : ℚ) * s - (Nat.card F : ℚ) * ((Nat.card F : ℚ) - 1)) := by
  have hδ : (ambDelta F) ^ Nat.card F
      = WithZero.exp (-((Nat.card F : ℚ) * ((Nat.card F : ℚ) - 1))) := by
    rw [ambDelta_eq, ← WithZero.exp_nsmul, nsmul_eq_mul]
    congr 1
    ring
  have h1 : Valued.v (PowerSeries.coeff m (atOmegaGen (Nat.card F) (ambTheta F) ^ s))
      ≤ (ambDelta F) ^ Nat.card F := by
    have hh := v_coeff_atOmegaGen_pow_le F s m
    rwa [if_neg (by omega : m ≠ 0)] at hh
  rw [hδ] at h1
  rw [ambOmega_pow_eq F s, PowerSeries.coeff_C_mul, map_mul, map_pow, v_ambMu,
    ← WithZero.exp_nsmul, nsmul_eq_mul]
  calc WithZero.exp (s * -(Nat.card F : ℚ))
        * Valued.v (PowerSeries.coeff m (atOmegaGen (Nat.card F) (ambTheta F) ^ s))
      ≤ WithZero.exp (s * -(Nat.card F : ℚ))
          * WithZero.exp (-((Nat.card F : ℚ) * ((Nat.card F : ℚ) - 1))) :=
        mul_le_mul_of_nonneg_left h1 zero_le
    _ = WithZero.exp (-(Nat.card F : ℚ) * s - (Nat.card F : ℚ) * ((Nat.card F : ℚ) - 1)) := by
        rw [← WithZero.exp_add]
        congr 1
        ring


/-! ## §4. The `γ`-bounds for the powers of `Ω` -/

/-- `v (coeff m (Ω^s)) ≤ γ` for every `m` (`s ≥ 1`). -/
theorem v_coeff_ambOmega_pow_le_gamma {s : ℕ} (hs : 1 ≤ s) (m : ℕ) :
    Valued.v (PowerSeries.coeff m ((ambOmega F) ^ s)) ≤ ambGamma := by
  rw [ambGamma]
  have hq : (1 : ℚ) ≤ Nat.card F := by
    exact_mod_cast (le_trans (by norm_num) (two_le_card_field F))
  have hs' : (1 : ℚ) ≤ s := by exact_mod_cast hs
  have hqm1 : (0 : ℚ) ≤ (Nat.card F : ℚ) - 1 := by linarith
  rcases eq_or_ne m 0 with rfl | hm
  · refine le_trans (v_coeff_ambOmega_pow_zero F s) (WithZero.exp_le_exp.mpr ?_)
    nlinarith
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    refine le_trans (v_coeff_ambOmega_pow_succ F hm1) (WithZero.exp_le_exp.mpr ?_)
    nlinarith [mul_nonneg hqm1 (by positivity : (0:ℚ) ≤ s)]

/-- `v (coeff m (Ω^s))·v (θ^q) ≤ γ` for every `m` (`s ≥ q`). -/
theorem v_coeff_ambOmega_pow_mul_theta_le_gamma {s : ℕ} (hs : Nat.card F ≤ s) (m : ℕ) :
    Valued.v (PowerSeries.coeff m ((ambOmega F) ^ s)) * Valued.v ((ambTheta F) ^ Nat.card F)
      ≤ ambGamma := by
  have hq2 : 2 ≤ Nat.card F := two_le_card_field F
  have hs' : (Nat.card F : ℚ) ≤ s := by exact_mod_cast hs
  have hqm1 : (0 : ℚ) ≤ (Nat.card F : ℚ) - 1 := by
    have : (1 : ℚ) ≤ Nat.card F := by exact_mod_cast (le_trans (by norm_num) hq2)
    linarith
  have hexp : Valued.v ((ambTheta F) ^ Nat.card F)
      = WithZero.exp ((Nat.card F : ℚ) * ((Nat.card F : ℚ) - 1)) := by
    rw [Valuation.map_pow, v_ambTheta, ← WithZero.exp_nsmul, nsmul_eq_mul]
  rw [ambGamma, hexp]
  rcases eq_or_ne m 0 with rfl | hm
  · refine le_trans (mul_le_mul_of_nonneg_right (v_coeff_ambOmega_pow_zero F s)
      (le_of_lt WithZero.exp_pos)) ?_
    rw [← WithZero.exp_add]
    exact WithZero.exp_le_exp.mpr (by nlinarith [mul_nonneg hqm1 (by positivity : (0:ℚ) ≤ s)])
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    refine le_trans (mul_le_mul_of_nonneg_right (v_coeff_ambOmega_pow_succ F hm1)
      (le_of_lt WithZero.exp_pos)) ?_
    rw [← WithZero.exp_add]
    exact WithZero.exp_le_exp.mpr (by nlinarith)

/-! ## §5. The coefficient bounds for `H_n` -/

/-- Natural numbers in the ambient field have valuation `≤ 1`. -/
lemma v_natCast_le_one (k : ℕ) : Valued.v ((k : Ambient F)) ≤ 1 :=
  v_le_one_of_mem_ambF (show ((k : Ambient F)) ∈ ambF F from by
    rw [mem_ambF_iff]
    simpa using natCast_ambient_pow_card_pow F k 1)

/-- `v (θ^q) ≥ 1`. -/
lemma one_le_v_theta_pow : (1 : ℚᵐ⁰) ≤ Valued.v ((ambTheta F) ^ Nat.card F) := by
  rw [Valuation.map_pow, v_ambTheta, ← WithZero.exp_nsmul, ← WithZero.exp_zero,
    WithZero.exp_le_exp, nsmul_eq_mul]
  have hq : (1 : ℚ) ≤ Nat.card F := by
    exact_mod_cast (le_trans (by norm_num) (two_le_card_field F))
  have hq1 : (0 : ℚ) ≤ (Nat.card F : ℚ) - 1 := by linarith
  nlinarith

lemma v_coeff_X_pow_sub_X_le (m : ℕ) :
    Valued.v ((Polynomial.X ^ Nat.card F - Polynomial.X : Polynomial (Ambient F)).coeff m) ≤ 1 := by
  rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  split_ifs with h1 h2
  · exfalso
    have := two_le_card_field F
    omega
  · simp
  · simp
  · simp

lemma v_coeff_X_pow_sub_C_le (m : ℕ) :
    Valued.v ((Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F)
      : Polynomial (Ambient F)).coeff m)
      ≤ if m = 0 then Valued.v ((ambTheta F) ^ Nat.card F) else 1 := by
  have hq1 : (1 : ℕ) < Nat.card F := two_le_card_field F
  rcases eq_or_ne m 0 with rfl | hm
  · rw [if_pos rfl, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C,
      if_neg (by omega : ¬ (0 = Nat.card F)), if_pos rfl]
    simp
  · rw [if_neg hm, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C,
      if_neg hm]
    by_cases hmq : m = Nat.card F
    · rw [if_pos hmq]
      simp
    · rw [if_neg hmq]
      simp

/-- **The coefficient bound for `H_n`** (as a power series): levels `≠ 0` are bounded by `1`, level
`0` by `v (θ^q)`. -/
theorem v_coeff_ambH_le (n m : ℕ) :
    Valued.v (PowerSeries.coeff m ((ambH F n : Polynomial (Ambient F)) : PowerSeries (Ambient F)))
      ≤ if m = 0 then Valued.v ((ambTheta F) ^ Nat.card F) else 1 := by
  rw [Polynomial.coeff_coe]
  rcases le_or_gt n (Nat.card F) with hn | hn
  · rw [ambH_of_le F hn, Polynomial.coeff_one]
    by_cases hm : m = 0
    · rw [if_pos hm, if_pos hm]
      exact le_trans (le_of_eq (map_one _)) (one_le_v_theta_pow F)
    · rw [if_neg hm, if_neg hm, map_zero]
      exact zero_le
  · rw [ambH_of_gt F hn, Polynomial.coeff_add]
    refine le_trans (Valuation.map_add_le_max' _ _ _) (max_le ?_ ?_)
    · refine le_trans (v_coeff_X_pow_sub_X_le F m) ?_
      by_cases hm : m = 0
      · rw [if_pos hm]; exact one_le_v_theta_pow F
      · rw [if_neg hm]
    · rw [Polynomial.coeff_C_mul]
      calc Valued.v (((n - Nat.card F : ℕ) : Ambient F)
            * (Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F)
              : Polynomial (Ambient F)).coeff m)
          = Valued.v (((n - Nat.card F : ℕ) : Ambient F))
            * Valued.v ((Polynomial.X ^ Nat.card F
              - Polynomial.C ((ambTheta F) ^ Nat.card F) : Polynomial (Ambient F)).coeff m) :=
            map_mul _ _ _
        _ ≤ 1 * (if m = 0 then Valued.v ((ambTheta F) ^ Nat.card F) else 1) :=
            mul_le_mul' (v_natCast_le_one F _) (v_coeff_X_pow_sub_C_le F m)
        _ = (if m = 0 then Valued.v ((ambTheta F) ^ Nat.card F) else 1) := one_mul _

/-! ## §6. The smallness of the Anderson–Thakur datum -/

/-- **★★★ The smallness of the Anderson–Thakur datum**: `GIsSmall γ (Ω^s·H_s)` for every `s ≥ 1`. -/
theorem gIsSmall_ambOmega_pow_mul_ambH {s : ℕ} (hs : 1 ≤ s) :
    GIsSmall ambGamma ((ambOmega F) ^ s
      * ((ambH F s : Polynomial (Ambient F)) : PowerSeries (Ambient F))) := by
  intro n
  rw [PowerSeries.coeff_mul]
  refine Valuation.map_sum_le _ fun p hp => ?_
  rw [Valuation.map_mul]
  have hsum : p.1 + p.2 = n := HasAntidiagonal.mem_antidiagonal.mp hp
  by_cases hsq : s ≤ Nat.card F
  · rw [ambH_of_le F hsq, Polynomial.coe_one, PowerSeries.coeff_one]
    by_cases hp0 : p.2 = 0
    · rw [if_pos hp0, map_one, mul_one]
      exact v_coeff_ambOmega_pow_le_gamma F hs p.1
    · rw [if_neg hp0, map_zero, mul_zero]
      exact zero_le
  · push_neg at hsq
    have hH := v_coeff_ambH_le F s p.2
    by_cases hp0 : p.2 = 0
    · rw [hp0] at hH
      rw [if_pos rfl] at hH
      have hp1 : p.1 = n := by omega
      rw [hp0, hp1]
      exact le_trans (mul_le_mul' le_rfl hH)
        (v_coeff_ambOmega_pow_mul_theta_le_gamma F (le_of_lt hsq) n)
    · rw [if_neg hp0] at hH
      refine le_trans (mul_le_mul' (v_coeff_ambOmega_pow_le_gamma F hs p.1) hH) ?_
      rw [mul_one]


end ZagierHoffmanPositiveChar
