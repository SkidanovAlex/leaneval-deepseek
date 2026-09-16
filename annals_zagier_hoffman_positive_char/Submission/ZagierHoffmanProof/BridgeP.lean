import Submission.ZagierHoffmanProof.HDatum
import Submission.ZagierHoffmanProof.ATBridge2
import Submission.ZagierHoffmanProof.AmbPeriodEll

/-!
# The per-factor identity of the bridge (4.2) for the Anderson–Thakur datum

For the datum `(s, H_s)` the `d`-th Frobenius twist of the factor `Ω^s·H_s` evaluates at `θ` to

  `(Ω^s·H_s)^{(d)}(θ) = Ω(θ)^s · Γ_s · P_d(s)`,   `Γ_s = 1` (`s ≤ q`), `= θ^q - θ` (`q < s`),

the per-factor content of Ngo Dac's (4.2) `L(𝔰;Q)(θ) = Γ_𝔰·ζ_A(𝔰)·π̃^{-w}` after the chain
regrouping of `ζ_A` (`NestP.ambInfHom_zeta_A_eq_nestLvlP`) and the cancellation of the `Ω(θ)^w`
factor against `π̃^w`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
open Polynomial PowerSeries Finset
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- `v (x - y) ≤ max (v x) (v y)`. -/
lemma valuation_map_sub_le_max {R : Type*} [Ring R] {Γ₀ : Type*}
    [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀) (x y : R) :
    v (x - y) ≤ max (v x) (v y) :=
  Valuation.map_sub_le v (le_max_left _ _) (le_max_right _ _)

/-! ## §1. The exact valuation of `ℓ_d` -/

/-- The geometric sum `∑_{i<d} (q-1)·q^{i+1} = q^{d+1} - q`. -/
lemma geom_sum_card (d : ℕ) :
    (∑ i ∈ Finset.range d, ((Nat.card F : ℚ) - 1) * (Nat.card F : ℚ) ^ (i + 1))
      = (Nat.card F : ℚ) ^ (d + 1) - (Nat.card F : ℚ) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

/-- **The exact valuation of `ℓ_d = ∏_{i<d} (θ - θ^{q^{i+1}})`**: `v ℓ_d = exp (q^{d+1} - q)`. -/
lemma v_ambEll_eq (d : ℕ) :
    Valued.v (ambEll F d)
      = WithZero.exp ((Nat.card F : ℚ) ^ (d + 1) - (Nat.card F : ℚ)) := by
  rw [ambEll_eq_prod, map_prod,
    Finset.prod_congr rfl (fun i _ => v_ambTheta_sub_pow F i),
    withZero_exp_finset_sum, geom_sum_card F d]

/-- **The sharp valuation of the `ℓ`-powers**: `v (ℓ_d^{-s}) = exp (-s·(q^{d+1} - q))`. -/
lemma v_ambEll_zpow_eq (d s : ℕ) :
    Valued.v ((ambEll F d) ^ (-(s : ℤ)))
      = WithZero.exp (-(s : ℚ) * ((Nat.card F : ℚ) ^ (d + 1) - (Nat.card F : ℚ))) := by
  have h1 : (ambEll F d) ^ (-(s : ℤ)) = ((ambEll F d)⁻¹) ^ s := by
    rw [zpow_neg, zpow_natCast, inv_pow]
  rw [h1, map_pow, map_inv₀, v_ambEll_eq F d, ← WithZero.exp_neg, ← WithZero.exp_nsmul,
    nsmul_eq_mul]
  congr 1
  ring

/-- `d ≤ 2^d`. -/
lemma le_two_pow' : ∀ d : ℕ, d ≤ 2 ^ d := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ]
    have h1 : 1 ≤ 2 ^ d := Nat.one_le_pow d 2 (by norm_num)
    omega

/-- `2·q^d ≥ d` for `q ≥ 2`. -/
lemma two_mul_pow_ge (q : ℕ) (hq : 2 ≤ q) (d : ℕ) : d ≤ 2 * q ^ d := by
  have h1 : 2 ^ d ≤ q ^ d := Nat.pow_le_pow_left hq d
  have h2 : 1 ≤ q ^ d := Nat.one_le_pow d q (by omega)
  have h3 : d ≤ 2 ^ d := le_two_pow' d
  omega

/-! ## §2. The per-factor identity -/

/-- `Γ_s`: the Carlitz `Γ`-factor of the Anderson–Thakur datum at the entry `s`. -/
noncomputable def ambGammaF (s : ℕ) : Ambient F :=
  if s ≤ Nat.card F then 1 else (ambTheta F) ^ Nat.card F - ambTheta F

lemma ambGammaF_of_le {s : ℕ} (hs : s ≤ Nat.card F) : ambGammaF F s = 1 := if_pos hs

lemma ambGammaF_of_gt {s : ℕ} (hs : Nat.card F < s) :
    ambGammaF F s = (ambTheta F) ^ Nat.card F - ambTheta F := if_neg (by omega)

/-- The evaluation of the twist of `Ω^s`. -/
lemma evalSeriesGen_frobTwist_ambOmega_pow (s d : ℕ) :
    evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) d ((ambOmega F) ^ s))
        (ambTheta F)
      = (evalSeriesGen (ambOmega F) (ambTheta F)) ^ s
        * (ambEll F d) ^ (-(s : ℤ)) := by
  rw [frobTwist_pow,
    evalSeriesGen_pow ambGamma_lt_one gammaArchimedean_rat
      (GSuperEntire.frobTwist (f := ambOmega F) ambGamma_le_one (gSuperEntire_ambOmega F) d),
    ambOmega_twist_eval F d (by rw [← ambEll_eq_prod]; exact ambEll_ne_zero F d)]
  rw [show (ambEll F d) ^ (-(s : ℤ)) = ((ambEll F d) ^ s)⁻¹ by rw [zpow_neg, zpow_natCast]]
  rw [ambEll_eq_prod, div_eq_mul_inv, mul_pow, inv_pow]

/-- **★★★ The per-factor identity of the bridge (4.2)**: for `1 ≤ n ≤ 2q-2` and every `d`,
`(Ω^n·H_n)^{(d)}(θ) = Ω(θ)^n·Γ_n·P_d(n)`. -/
theorem evalSeriesGen_frobTwist_ambOmega_pow_ambH (n : ℕ+) (d : ℕ)
    (hn : (n : ℕ) ≤ 2 * Nat.card F - 2) :
    evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) d
        ((ambOmega F) ^ (n : ℕ) * ((ambH F (n : ℕ) : Polynomial (Ambient F))
          : PowerSeries (Ambient F)))) (ambTheta F)
      = (evalSeriesGen (ambOmega F) (ambTheta F)) ^ (n : ℕ) * ambGammaF F (n : ℕ)
        * ambInfHom F (P F d n) := by
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  have hn1 : 1 ≤ (n : ℕ) := n.2
  rcases le_or_gt (n : ℕ) (Nat.card F) with hsq | hsq
  · rw [ambGammaF_of_le F hsq, mul_one, frobTwist_mul, ambH_of_le F hsq, Polynomial.coe_one,
      frobTwist_one, mul_one, evalSeriesGen_frobTwist_ambOmega_pow F (n : ℕ) d]
    have hpure := ambH_interp_le F n hsq (d := d)
    rw [ambH_of_le F hsq, Polynomial.coe_one, frobTwist_one, evalSeriesGen_one] at hpure
    have h3 : ambInfHom F (P F d n) = (ambEll F d) ^ (-((n : ℕ) : ℤ)) := by
      rw [show (ambEll F d) ^ (-((n : ℕ) : ℤ)) = (((ambEll F d) ^ (n : ℕ))⁻¹) from
        by rw [zpow_neg, zpow_natCast]]
      exact eq_inv_of_mul_eq_one_right hpure.symm
    rw [h3]
  · have hk : 2 ≤ (n : ℕ) - Nat.card F + 1 := by omega
    have hk2 : (n : ℕ) - Nat.card F + 1 ≤ Nat.card F - 1 := by omega
    have hnat : Nat.card F + ((n : ℕ) - Nat.card F + 1) - 1 = (n : ℕ) := by omega
    have hidx : (⟨Nat.card F + ((n : ℕ) - Nat.card F + 1) - 1, by omega⟩ : ℕ+) = n :=
      Subtype.ext hnat
    have hpure := ambH_interp F (k := (n : ℕ) - Nat.card F + 1) (d := d) hk hk2
    rw [hidx, hnat] at hpure
    have hse1 : GSuperEntire ambGamma
        ((ambOmega F) ^ (n : ℕ) : PowerSeries (Ambient F)) :=
      (gSuperEntire_ambOmega F).pow ambGamma_le_one (n : ℕ)
    have hse2 : GSuperEntire ambGamma
        (((ambH F (n : ℕ) : Polynomial (Ambient F)) : PowerSeries (Ambient F))) :=
      GSuperEntire.polynomial ambGamma_pos ambGamma_le_one _
    calc evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) d
          ((ambOmega F) ^ (n : ℕ) * ((ambH F (n : ℕ) : Polynomial (Ambient F))
            : PowerSeries (Ambient F)))) (ambTheta F)
        = evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) d
              ((ambOmega F) ^ (n : ℕ))) (ambTheta F)
          * evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) d
              (((ambH F (n : ℕ) : Polynomial (Ambient F)) : PowerSeries (Ambient F))))
              (ambTheta F) := by
          rw [frobTwist_mul, evalSeriesGen_mul ambGamma_lt_one gammaArchimedean_rat
            (hse1.frobTwist ambGamma_le_one d) (hse2.frobTwist ambGamma_le_one d) (ambTheta F)]
      _ = ((evalSeriesGen (ambOmega F) (ambTheta F)) ^ (n : ℕ)
              * (ambEll F d) ^ (-((n : ℕ) : ℤ)))
            * (((ambTheta F) ^ Nat.card F - (ambTheta F)) * (ambEll F d) ^ (n : ℕ)
              * ambInfHom F (P F d n)) := by
          rw [evalSeriesGen_frobTwist_ambOmega_pow F (n : ℕ) d, hpure]
      _ = (evalSeriesGen (ambOmega F) (ambTheta F)) ^ (n : ℕ)
            * ((ambTheta F) ^ Nat.card F - (ambTheta F)) * ambInfHom F (P F d n) := by
          have hcancel : (ambEll F d) ^ (-((n : ℕ) : ℤ))
              * (((ambTheta F) ^ Nat.card F - (ambTheta F)) * ((ambEll F d) ^ (n : ℕ)
                * ambInfHom F (P F d n)))
              = ((ambTheta F) ^ Nat.card F - (ambTheta F)) * ambInfHom F (P F d n) := by
            rw [show (ambEll F d) ^ (-((n : ℕ) : ℤ)) = (((ambEll F d) ^ (n : ℕ)))⁻¹ by
              rw [zpow_neg, zpow_natCast]]
            rw [inv_mul_eq_iff_eq_mul₀ (pow_ne_zero _ (ambEll_ne_zero F d))]
            ring
          rw [show (evalSeriesGen (ambOmega F) (ambTheta F)) ^ (n : ℕ)
                * (ambEll F d) ^ (-((n : ℕ) : ℤ))
                * (((ambTheta F) ^ Nat.card F - (ambTheta F)) * (ambEll F d) ^ (n : ℕ)
                  * ambInfHom F (P F d n))
              = (evalSeriesGen (ambOmega F) (ambTheta F)) ^ (n : ℕ)
                * ((ambEll F d) ^ (-((n : ℕ) : ℤ))
                  * (((ambTheta F) ^ Nat.card F - (ambTheta F)) * ((ambEll F d) ^ (n : ℕ)
                    * ambInfHom F (P F d n)))) from by ring,
            hcancel]
          ring
      _ = (evalSeriesGen (ambOmega F) (ambTheta F)) ^ (n : ℕ) * ambGammaF F (n : ℕ)
            * ambInfHom F (P F d n) := by
          rw [ambGammaF_of_gt F hsq]

/-! ## §3. The geometric decay -/

/-- `v (θ^q) = exp (q(q-1))`. -/
lemma v_theta_pow_eq :
    Valued.v ((ambTheta F) ^ Nat.card F)
      = WithZero.exp ((Nat.card F : ℚ) * ((Nat.card F : ℚ) - 1)) := by
  rw [Valuation.map_pow, v_ambTheta, ← WithZero.exp_nsmul, nsmul_eq_mul]

/-- The valuation of the twisted `H`-factor: for `q < s` and every `d`,
`v ((H_s)^{(d)}(θ)) ≤ exp ((q-1)·q^{d+1})`. -/
lemma v_frobTwist_ambH_le {s d : ℕ} (hs : Nat.card F < s) :
    Valued.v (evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) d
        ((ambH F s : Polynomial (Ambient F)) : PowerSeries (Ambient F))) (ambTheta F))
      ≤ WithZero.exp (((Nat.card F : ℚ) - 1) * (Nat.card F : ℚ) ^ (d + 1)) := by
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  have hq1 : (1 : ℚ) ≤ Nat.card F := by exact_mod_cast (le_trans (by norm_num) hq2)
  have hqd : (Nat.card F : ℚ) ≤ (Nat.card F : ℚ) ^ (d + 1) := by
    rw [pow_succ]
    have h1 : (1 : ℚ) ≤ (Nat.card F : ℚ) ^ d := one_le_pow₀ hq1
    nlinarith [hq1, h1]
  have hqm1 : (0 : ℚ) ≤ (Nat.card F : ℚ) - 1 := by linarith
  rw [evalSeriesGen_frobTwist_ambH F hs]
  refine le_trans (valuation_map_sub_le_max Valued.v _ _) ?_
  refine max_le ?_ ?_
  · refine le_trans (valuation_map_sub_le_max Valued.v _ _) ?_
    refine max_le ?_ ?_
    · calc Valued.v (((s - Nat.card F + 1 : ℕ) : Ambient F) * (ambTheta F) ^ Nat.card F)
          = Valued.v (((s - Nat.card F + 1 : ℕ) : Ambient F))
            * Valued.v ((ambTheta F) ^ Nat.card F) := map_mul _ _ _
        _ ≤ 1 * WithZero.exp ((Nat.card F : ℚ) * ((Nat.card F : ℚ) - 1)) :=
            mul_le_mul' (v_natCast_le_one F _) (le_of_eq (v_theta_pow_eq F))
        _ = WithZero.exp ((Nat.card F : ℚ) * ((Nat.card F : ℚ) - 1)) := one_mul _
        _ ≤ WithZero.exp (((Nat.card F : ℚ) - 1) * (Nat.card F : ℚ) ^ (d + 1)) :=
            WithZero.exp_le_exp.mpr (by nlinarith [hqd, hqm1])
    · calc Valued.v (ambTheta F) = WithZero.exp ((Nat.card F : ℚ) - 1) := v_ambTheta F
        _ ≤ WithZero.exp (((Nat.card F : ℚ) - 1) * (Nat.card F : ℚ) ^ (d + 1)) :=
            WithZero.exp_le_exp.mpr (by nlinarith [hqd, hqm1])
  · calc Valued.v (((s - Nat.card F : ℕ) : Ambient F)
          * (ambTheta F) ^ (Nat.card F ^ (d + 1)))
        = Valued.v (((s - Nat.card F : ℕ) : Ambient F))
          * Valued.v ((ambTheta F) ^ (Nat.card F ^ (d + 1))) := map_mul _ _ _
      _ ≤ 1 * WithZero.exp (((Nat.card F : ℚ) - 1) * (Nat.card F : ℚ) ^ (d + 1)) := by
          refine mul_le_mul' (v_natCast_le_one F _) (le_of_eq ?_)
          rw [Valuation.map_pow, v_ambTheta, ← WithZero.exp_nsmul, nsmul_eq_mul]
          congr 1
          push_cast
          ring
      _ = WithZero.exp (((Nat.card F : ℚ) - 1) * (Nat.card F : ℚ) ^ (d + 1)) := one_mul _

/-- The valuation of the twisted `Ω^s`: for `s ≥ 1`, `v ((Ω^s)^{(d)}(θ)) ≤ exp (-s·q^{d+1})`. -/
lemma v_frobTwist_ambOmega_pow_le (s d : ℕ) (_hs : 1 ≤ s) :
    Valued.v (evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) d ((ambOmega F) ^ s))
        (ambTheta F))
      ≤ WithZero.exp (-(s : ℚ) * (Nat.card F : ℚ) ^ (d + 1)) := by
  rw [evalSeriesGen_frobTwist_ambOmega_pow F s d, map_mul, map_pow, v_evalSeriesGen_ambOmega,
    v_ambEll_zpow_eq F d s, ← WithZero.exp_nsmul, nsmul_eq_mul, ← WithZero.exp_add]
  refine WithZero.exp_le_exp.mpr ?_
  rw [show (s : ℚ) * -(Nat.card F : ℚ) = -(s : ℚ) * (Nat.card F : ℚ) by ring]
  nlinarith [mul_nonneg (by positivity : (0:ℚ) ≤ s)
    (pow_nonneg (by positivity : (0:ℚ) ≤ (Nat.card F : ℚ)) (d + 1))]

/-- **The geometric decay of the twisted factors**:
`v ((Ω^s·H_s)^{(d)}(θ)) ≤ exp (-q·d)` for `1 ≤ s ≤ 2q-2` and every `d`. -/
theorem v_evalSeriesGen_frobTwist_ambOmega_pow_ambH_le {s d : ℕ} (hs : 1 ≤ s)
    (hs2 : s ≤ 2 * Nat.card F - 2) :
    Valued.v (evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) d
        ((ambOmega F) ^ s * ((ambH F s : Polynomial (Ambient F)) : PowerSeries (Ambient F))))
        (ambTheta F))
      ≤ 1 * WithZero.exp (-(Nat.card F : ℚ) * d) := by
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  have hq1 : (1 : ℚ) ≤ Nat.card F := by exact_mod_cast (le_trans (by norm_num) hq2)
  have hqd : (1 : ℚ) ≤ (Nat.card F : ℚ) ^ d := one_le_pow₀ hq1
  have hdle : (d : ℚ) ≤ (Nat.card F : ℚ) ^ d := by
    have h1 : d ≤ (2 : ℕ) ^ d := le_two_pow' d
    have h2 : (2 : ℕ) ^ d ≤ (Nat.card F) ^ d := Nat.pow_le_pow_left hq2 d
    exact_mod_cast le_trans h1 h2
  have hspos : (0 : ℚ) < (Nat.card F : ℚ) := by linarith
  have hp : (Nat.card F : ℚ) ^ (d + 1) = (Nat.card F : ℚ) ^ d * (Nat.card F : ℚ) :=
    pow_succ _ _
  rcases le_or_gt s (Nat.card F) with hsq | hsq
  · rw [ambH_of_le F hsq, Polynomial.coe_one, mul_one, one_mul]
    refine le_trans (v_frobTwist_ambOmega_pow_le F s d hs) (WithZero.exp_le_exp.mpr ?_)
    have hs' : (1 : ℚ) ≤ s := by exact_mod_cast hs
    have hA : (Nat.card F : ℚ) * (d : ℚ) ≤ (Nat.card F : ℚ) * (Nat.card F : ℚ) ^ d :=
      mul_le_mul_of_nonneg_left hdle (le_of_lt hspos)
    have hB : (Nat.card F : ℚ) * (Nat.card F : ℚ) ^ d
        ≤ s * ((Nat.card F : ℚ) ^ d * (Nat.card F : ℚ)) := by
      have hpos : (0 : ℚ) ≤ (Nat.card F : ℚ) ^ d * (Nat.card F : ℚ) :=
        mul_nonneg (pow_nonneg (le_of_lt hspos) d) (le_of_lt hspos)
      calc (Nat.card F : ℚ) * (Nat.card F : ℚ) ^ d
          = (Nat.card F : ℚ) ^ d * (Nat.card F : ℚ) := by ring
        _ = 1 * ((Nat.card F : ℚ) ^ d * (Nat.card F : ℚ)) := (one_mul _).symm
        _ ≤ s * ((Nat.card F : ℚ) ^ d * (Nat.card F : ℚ)) := mul_le_mul_of_nonneg_right hs' hpos
    rw [hp]
    nlinarith [hA, hB]
  · have hse1 : GSuperEntire ambGamma ((ambOmega F) ^ s : PowerSeries (Ambient F)) :=
      (gSuperEntire_ambOmega F).pow ambGamma_le_one s
    have hse2 : GSuperEntire ambGamma
        (((ambH F s : Polynomial (Ambient F)) : PowerSeries (Ambient F))) :=
      GSuperEntire.polynomial ambGamma_pos ambGamma_le_one _
    have hsplit : evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) d
          ((ambOmega F) ^ s * ((ambH F s : Polynomial (Ambient F))
            : PowerSeries (Ambient F)))) (ambTheta F)
        = evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) d ((ambOmega F) ^ s))
            (ambTheta F)
          * evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) d
              (((ambH F s : Polynomial (Ambient F)) : PowerSeries (Ambient F))))
              (ambTheta F) := by
      rw [frobTwist_mul, evalSeriesGen_mul ambGamma_lt_one gammaArchimedean_rat
        (hse1.frobTwist ambGamma_le_one d) (hse2.frobTwist ambGamma_le_one d) (ambTheta F)]
    rw [hsplit, map_mul]
    refine le_trans (mul_le_mul' (v_frobTwist_ambOmega_pow_le F s d hs)
      (v_frobTwist_ambH_le F hsq)) ?_
    rw [← WithZero.exp_add, one_mul]
    change WithZero.exp (-(s : ℚ) * (Nat.card F : ℚ) ^ (d + 1)
        + ((Nat.card F : ℚ) - 1) * (Nat.card F : ℚ) ^ (d + 1))
      ≤ WithZero.exp (-(Nat.card F : ℚ) * d)
    refine WithZero.exp_le_exp.mpr ?_
    have hsq' : ((Nat.card F : ℚ) + 1) ≤ s := by exact_mod_cast hsq
    have h2 : (Nat.card F : ℚ) * (d : ℚ) ≤ 2 * (Nat.card F : ℚ) ^ (d + 1) := by
      have h1 : (d : ℚ) ≤ (2 : ℚ) ^ d := by exact_mod_cast le_two_pow' d
      have h3 : (2 : ℚ) ^ d ≤ (Nat.card F : ℚ) ^ d := by
        exact_mod_cast Nat.pow_le_pow_left hq2 d
      rw [hp]
      nlinarith [h1, h3, hq1, pow_pos hspos d]
    have h3 : 2 * (Nat.card F : ℚ) ^ (d + 1)
        ≤ (s - (Nat.card F : ℚ) + 1) * (Nat.card F : ℚ) ^ (d + 1) := by
      have h4 : (2 : ℚ) ≤ s - (Nat.card F : ℚ) + 1 := by linarith
      exact mul_le_mul_of_nonneg_right h4 (pow_nonneg (le_of_lt hspos) _)
    have hgoal : -(s : ℚ) * (Nat.card F : ℚ) ^ (d + 1)
        + ((Nat.card F : ℚ) - 1) * (Nat.card F : ℚ) ^ (d + 1)
        = -((s - (Nat.card F : ℚ) + 1) * (Nat.card F : ℚ) ^ (d + 1)) := by ring
    rw [hgoal]
    linarith [h2, h3]

/-! ## §4. The decay of the power sums `P_d(n)` -/

/-- `1 ≤ v (θ^q - θ)`. -/
lemma one_le_v_ambTheta_sub : (1 : ℚᵐ⁰) ≤ Valued.v ((ambTheta F) ^ Nat.card F - ambTheta F) := by
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  have hlt : Valued.v (ambTheta F) < Valued.v ((ambTheta F) ^ Nat.card F) := by
    rw [Valuation.map_pow, v_ambTheta, ← WithZero.exp_nsmul,
      WithZero.exp_lt_exp, nsmul_eq_mul]
    have h1 : (1 : ℚ) < (Nat.card F : ℚ) := by exact_mod_cast (lt_of_lt_of_le one_lt_two hq2)
    nlinarith [mul_pos (by linarith : (0:ℚ) < (Nat.card F : ℚ) - 1) (by linarith)]
  have h1 : Valued.v ((ambTheta F) ^ Nat.card F - ambTheta F)
      = Valued.v ((ambTheta F) - (ambTheta F) ^ Nat.card F) := by
    rw [show (ambTheta F) ^ Nat.card F - ambTheta F
      = -((ambTheta F) - (ambTheta F) ^ Nat.card F) by ring, Valuation.map_neg]
  rw [h1, Valuation.map_sub_eq_of_lt_right (v := Valued.v) hlt, v_theta_pow_eq,
    ← WithZero.exp_zero, WithZero.exp_le_exp]
  have h1 : (0 : ℚ) ≤ (Nat.card F : ℚ) - 1 := by
    have : (1 : ℚ) ≤ Nat.card F := by exact_mod_cast (le_trans (by norm_num) hq2)
    linarith
  nlinarith [h1]

/-- `v (Γ_n) ≥ 1`. -/
lemma one_le_v_ambGammaF (n : ℕ) : (1 : ℚᵐ⁰) ≤ Valued.v (ambGammaF F n) := by
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  by_cases hn : n ≤ Nat.card F
  · rw [ambGammaF_of_le F hn, map_one]
  · rw [ambGammaF_of_gt F (by omega)]
    exact one_le_v_ambTheta_sub F

lemma v_ambGammaF_ne_zero_lt (n : ℕ) : Valued.v (ambGammaF F n) ≠ 0 := by
  intro h
  have h1 := one_le_v_ambGammaF F n
  rw [h] at h1
  exact absurd h1 (not_le.mpr zero_lt_one)

lemma v_evalSeriesGen_ambOmega_pos :
    (0 : ℚᵐ⁰) < Valued.v (evalSeriesGen (ambOmega F) (ambTheta F)) := by
  rw [v_evalSeriesGen_ambOmega]
  exact WithZero.exp_pos

/-- **The geometric decay of the power sums**: for `1 ≤ n ≤ 2q-2`,
`v (ambInfHom (P_d(n))) ≤ exp (q·n)·exp (-q·d)`. -/
theorem v_ambInfHom_P_le (n : ℕ+) (hn : (n : ℕ) ≤ 2 * Nat.card F - 2) (d : ℕ) :
    Valued.v (ambInfHom F (P F d n))
      ≤ WithZero.exp ((Nat.card F : ℚ) * (n : ℕ)) * WithZero.exp (-(Nat.card F : ℚ) * d) := by
  have h := evalSeriesGen_frobTwist_ambOmega_pow_ambH F n d hn
  have hd := v_evalSeriesGen_frobTwist_ambOmega_pow_ambH_le F (d := d) n.2 hn
  have hd' : Valued.v (evalSeriesGen (ambOmega F) (ambTheta F) ^ (n : ℕ) * ambGammaF F (n : ℕ)
        * ambInfHom F (P F d n)) ≤ 1 * WithZero.exp (-(Nat.card F : ℚ) * d) := by
    rw [← h]
    exact hd
  rw [one_mul] at hd'
  rw [map_mul, map_mul, map_pow, v_evalSeriesGen_ambOmega] at hd'
  set ρ : ℚᵐ⁰ := WithZero.exp (-(Nat.card F : ℚ)) with hρdef
  set Γ : ℚᵐ⁰ := Valued.v (ambGammaF F (n : ℕ)) with hΓdef
  set Pv : ℚᵐ⁰ := Valued.v (ambInfHom F (P F d n)) with hPvdef
  have hρpos : (0 : ℚᵐ⁰) < ρ := WithZero.exp_pos
  have hΓ1 : (1 : ℚᵐ⁰) ≤ Γ := one_le_v_ambGammaF F (n : ℕ)
  have hdρ : ρ ^ d = WithZero.exp (-(Nat.card F : ℚ) * d) := by
    rw [hρdef, ← WithZero.exp_nsmul, nsmul_eq_mul]
    congr 1
    ring
  have hmain : Pv * (ρ ^ (n : ℕ) * Γ) ≤ ρ ^ d := by
    calc Pv * (ρ ^ (n : ℕ) * Γ)
        = ρ ^ (n : ℕ) * Γ * Pv := by rw [mul_comm]
      _ ≤ ρ ^ d := by rw [hdρ]; exact hd'
  have hle : Pv ≤ ρ ^ d / ρ ^ (n : ℕ) := by
    rw [le_div_iff₀ (pow_pos hρpos _)]
    calc Pv * ρ ^ (n : ℕ) ≤ Pv * (ρ ^ (n : ℕ) * Γ) := by
          refine mul_le_mul_of_nonneg_left ?_ zero_le
          calc ρ ^ (n : ℕ) = ρ ^ (n : ℕ) * 1 := (mul_one _).symm
            _ ≤ ρ ^ (n : ℕ) * Γ := mul_le_mul_of_nonneg_left hΓ1 zero_le
      _ ≤ ρ ^ d := hmain
  have hdiv : ρ ^ d / ρ ^ (n : ℕ)
      = WithZero.exp (-(Nat.card F : ℚ) * d) * WithZero.exp ((Nat.card F : ℚ) * (n : ℕ)) := by
    rw [hρdef, div_eq_mul_inv,
      show WithZero.exp (-(Nat.card F : ℚ)) ^ d
        = WithZero.exp (-(Nat.card F : ℚ) * d) from by
          rw [← WithZero.exp_nsmul, nsmul_eq_mul]
          congr 1
          ring,
      show WithZero.exp (-(Nat.card F : ℚ)) ^ (n : ℕ)
        = WithZero.exp (-(Nat.card F : ℚ) * (n : ℕ)) from by
          rw [← WithZero.exp_nsmul, nsmul_eq_mul]
          congr 1
          ring,
      show (WithZero.exp (-(Nat.card F : ℚ) * (n : ℕ)))⁻¹
        = WithZero.exp ((Nat.card F : ℚ) * (n : ℕ)) from by
          rw [← WithZero.exp_neg]
          congr 1
          ring]
  rw [hdiv, mul_comm] at hle
  exact hle
end ZagierHoffmanPositiveChar
