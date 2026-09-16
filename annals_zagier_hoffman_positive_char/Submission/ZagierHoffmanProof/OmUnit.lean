import Submission.ZagierHoffmanProof.AmbPeriod
import Submission.Commons.Combinatorics.Nat.geom_sum_mul_pow_ge

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Polynomial PowerSeries Finset
open scoped WithZero Topology

/-!
# N2a, first sub-lemma: the factors of the partial products of `Ω` are units

`Ω = C μ · atOmegaGen q θ` with `atOmegaGen q θ = ∏_{i ≥ 1}(1 - t/θ^{q^i})`; evaluating the partial
products `omPartial q θ N` at `θ` produces the factors `1 - θ^{1-q^{i+1}}`, and this file shows that
each of them is a **unit** (`v = 1`) in the ambient field:

* `v_inv_ambTheta_pow` — `v ((θ ^ (q^(i+1) - 1))⁻¹) < 1`, i.e. `v (θ^(1-q^(i+1))) < 1`;
* ★★ `v_one_sub_inv_ambTheta_pow` — `v (1 - θ^(1-q^(i+1))) = 1`.

The proof is the standard nonarchimedean computation: `v(1-x) ≤ max(v 1, v x) = 1` and
`1 = v((1-x) + x) ≤ max(v(1-x), v x)`, so `v x < 1` forces `v(1-x) = 1`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

/-- `v (θ ^ (1 - q^(i+1))) < 1`: the "small" factor. -/
lemma v_inv_ambTheta_pow (i : ℕ) :
    Valued.v (((ambTheta F) ^ ((Nat.card F) ^ (i + 1) - 1))⁻¹) < 1 := by
  have hq : 2 ≤ Nat.card F := two_le_ambCard F
  have hm : 1 ≤ (Nat.card F) ^ (i + 1) - 1 := by
    have h2 : 2 ≤ (Nat.card F) ^ (i + 1) := by
      calc 2 ≤ (Nat.card F) ^ 1 := by simpa using hq
        _ ≤ (Nat.card F) ^ (i + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hvθ : Valued.v (ambTheta F) = WithZero.exp ((Nat.card F : ℚ) - 1) := v_ambTheta F
  have hlt : 1 < (Valued.v (ambTheta F)) ^ ((Nat.card F) ^ (i + 1) - 1) := by
    rw [hvθ, ← WithZero.exp_nsmul, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    rw [nsmul_eq_mul]
    have h1 : (0 : ℚ) < (Nat.card F : ℚ) - 1 := by
      have h2 : (2 : ℚ) ≤ (Nat.card F : ℚ) := by exact_mod_cast hq
      linarith
    have h2 : (0 : ℚ) < (((Nat.card F) ^ (i + 1) - 1 : ℕ) : ℚ) := by
      exact_mod_cast hm
    positivity
  calc Valued.v (((ambTheta F) ^ ((Nat.card F) ^ (i + 1) - 1))⁻¹)
      = (Valued.v ((ambTheta F) ^ ((Nat.card F) ^ (i + 1) - 1)))⁻¹ := map_inv₀ _ _
    _ = ((Valued.v (ambTheta F)) ^ ((Nat.card F) ^ (i + 1) - 1))⁻¹ := by rw [map_pow]
    _ < 1 := inv_lt_one_of_one_lt₀ hlt

/-- ★★ **Each factor `1 - θ^(1 - q^(i+1))` of the partial products of `Ω` is a unit.** -/
lemma v_one_sub_inv_ambTheta_pow (i : ℕ) :
    Valued.v (1 - ((ambTheta F) ^ ((Nat.card F) ^ (i + 1) - 1))⁻¹) = 1 := by
  set x : Ambient F := ((ambTheta F) ^ ((Nat.card F) ^ (i + 1) - 1))⁻¹ with hx
  have hlt : Valued.v x < 1 := v_inv_ambTheta_pow F i
  refine le_antisymm ?_ ?_
  · calc Valued.v (1 - x) ≤ max (Valued.v (1 : Ambient F)) (Valued.v x) := Valuation.map_sub _ _ _
      _ = 1 := by rw [map_one, max_eq_left hlt.le]
  · have h := Valuation.map_add (Valued.v) (1 - x) x
    rw [sub_add_cancel, map_one] at h
    by_contra hc
    rw [not_le] at hc
    have : max (Valued.v (1 - x)) (Valued.v x) < 1 := max_lt hc hlt
    exact absurd (lt_of_le_of_lt h this) (lt_irrefl 1)

section Partial

variable (q : ℕ) (hγ : WithZero.exp (-1 : ℚ) < 1)

/-- The partial products are super-entire. -/
theorem gSuperEntire_omPartial (N : ℕ) :
    GSuperEntire (WithZero.exp (-1 : ℚ)) (omPartial (Nat.card F) (ambTheta F) N) := by
  rw [omPartial]
  refine GSuperEntire.prod ambGamma_lt_one.le _ _ fun i _ => ?_
  exact (GSuperEntire.one _).sub ((GSuperEntire.C _ _).mul ambGamma_lt_one.le
    (GSuperEntire.X (K := Ambient F) (γ := WithZero.exp (-1 : ℚ)) ambGamma_pos))

/-- ★★ **The partial products of `Ω`, evaluated at `θ`**: the finite product of the "small"
factors `1 - θ^(1-q^(i+1))`. -/
theorem evalSeriesGen_omPartial (N : ℕ) :
    evalSeriesGen (omPartial (Nat.card F) (ambTheta F) N) (ambTheta F)
      = ∏ i ∈ Finset.range N,
          (1 - ((ambTheta F) ^ ((Nat.card F) ^ (i + 1) - 1))⁻¹) := by
  have hθ : (ambTheta F) ≠ 0 := ambTheta_ne_zero F
  have hfac : ∀ i : ℕ, omX (Nat.card F) (ambTheta F) (i + 1) * (ambTheta F)
      = ((ambTheta F) ^ ((Nat.card F) ^ (i + 1) - 1))⁻¹ := by
    intro i
    rw [omX]
    have hm : (Nat.card F) ^ (i + 1) ≠ 0 := pow_ne_zero _ (by have := two_le_ambCard F; omega)
    have h1 : (ambTheta F) ^ ((Nat.card F) ^ (i + 1))
        = (ambTheta F) * (ambTheta F) ^ ((Nat.card F) ^ (i + 1) - 1) := by
      conv_lhs => rw [← Nat.sub_one_add_one hm]
      rw [pow_succ']
    rw [h1, mul_inv_rev]
    field_simp
  induction N with
  | zero => rw [omPartial, Finset.range_zero, Finset.prod_empty, evalSeriesGen_one]; simp
  | succ N ih =>
    have hunf : omPartial (Nat.card F) (ambTheta F) (N + 1)
        = (∏ i ∈ Finset.range N,
            (1 - PowerSeries.C (omX (Nat.card F) (ambTheta F) (i + 1)) * PowerSeries.X :
              PowerSeries (Ambient F)))
          * (1 - PowerSeries.C (omX (Nat.card F) (ambTheta F) (N + 1)) * PowerSeries.X :
              PowerSeries (Ambient F)) := by
      rw [omPartial, Finset.prod_range_succ]
    rw [hunf]
    have hgse : GSuperEntire (WithZero.exp (-1 : ℚ))
        (∏ i ∈ Finset.range N,
          (1 - PowerSeries.C (omX (Nat.card F) (ambTheta F) (i + 1)) * PowerSeries.X :
            PowerSeries (Ambient F))) := by
      rw [← omPartial]; exact gSuperEntire_omPartial F N
    have hgse2 : GSuperEntire (WithZero.exp (-1 : ℚ))
        (1 - PowerSeries.C (omX (Nat.card F) (ambTheta F) (N + 1)) * PowerSeries.X :
          PowerSeries (Ambient F)) :=
      (GSuperEntire.one _).sub ((GSuperEntire.C _ _).mul ambGamma_lt_one.le
        (GSuperEntire.X (K := Ambient F) (γ := WithZero.exp (-1 : ℚ)) ambGamma_pos))
    rw [evalSeriesGen_mul ambGamma_lt_one gammaArchimedean_rat hgse hgse2 (ambTheta F),
      ← omPartial, ih,
      evalSeriesGen_one_sub_C_mul_X (K := Ambient F) (γ := WithZero.exp (-1 : ℚ))
        ambGamma_pos ambGamma_lt_one gammaArchimedean_rat (omX (Nat.card F) (ambTheta F) (N + 1))
        (ambTheta F),
      hfac N, Finset.prod_range_succ]

/-- ★★★ **The value of the partial products at `θ` is a unit.** -/
theorem v_evalSeriesGen_omPartial (N : ℕ) :
    Valued.v (evalSeriesGen (omPartial (Nat.card F) (ambTheta F) N) (ambTheta F)) = 1 := by
  rw [evalSeriesGen_omPartial F N, map_prod]
  exact Finset.prod_eq_one fun i _ => v_one_sub_inv_ambTheta_pow F i

end Partial

section Clopen

/-- **The units are clopen, quantitatively**: if `v (x - 1) < 1` then `v x = 1`.
This is the form of the statement that the unit group `{x | v x = 1}` contains the ball `1 + 𝔪`
(and is closed), used to pass from the tail estimate `v (T_N - 1) < 1` to `v T_N = 1`. -/
lemma v_eq_one_of_v_sub_one_lt {x : Ambient F} (h : Valued.v (x - 1) < 1) :
    Valued.v x = 1 := by
  refine le_antisymm ?_ ?_
  · calc Valued.v x = Valued.v ((x - 1) + 1) := by rw [sub_add_cancel]
      _ ≤ max (Valued.v (x - 1)) (Valued.v (1 : Ambient F)) :=
          Valuation.map_add (Valued.v : Valuation (Ambient F) ℚᵐ⁰) _ _
      _ = 1 := by rw [map_one, max_eq_right h.le]
  · have h1 : Valued.v (1 : Ambient F) ≤ max (Valued.v x) (Valued.v (x - 1)) := by
      have hx : x - (x - 1) = (1 : Ambient F) := by ring
      simpa only [hx] using Valuation.map_sub (Valued.v : Valuation (Ambient F) ℚᵐ⁰) x (x - 1)
    rw [map_one] at h1
    by_contra hc
    rw [not_le] at hc
    exact absurd h1 (not_le.mpr (max_lt hc h))

end Clopen

section Tail

/-- **N2a, step 1: the tsum splitting for the twisted `Ω`.**  Since `coeff 0 Ω = 1`, the value of a
Frobenius twist of `Ω` at `θ` exceeds `1` by the sum of the coefficients of positive index raised to
the `q^N`-th power:

`(Ω^{(N)})(θ) - 1 = ∑'_m (coeff (m+1) Ω)^(q^N) · θ^(m+1)`. -/
theorem evalSeriesGen_frobTwistAtOmegaGen_sub_one (N : ℕ) :
    evalSeriesGen
        (frobTwist (R := Ambient F) (p := Nat.card F) N
          (atOmegaGen (Nat.card F) (ambTheta F))) (ambTheta F) - 1
      = ∑' m : ℕ, (PowerSeries.coeff (m + 1) (atOmegaGen (Nat.card F) (ambTheta F)))
            ^ (Nat.card F ^ N) * (ambTheta F) ^ (m + 1) := by
  have _ : NonarchimedeanRing (Ambient F) :=
    Commons.Topology.Algebra.Valued.nonarchimedeanRing
  have hq : 2 ≤ Nat.card F := two_le_ambCard F
  have hse : GSuperEntire (WithZero.exp (-1 : ℚ))
      (frobTwist (R := Ambient F) (p := Nat.card F) N
        (atOmegaGen (Nat.card F) (ambTheta F))) :=
    (gSuperEntire_atOmegaGen (K := Ambient F) (q := Nat.card F) (θ := ambTheta F)
      ambGamma_pos (v_ambTheta_inv_le F) ambGamma_lt_one gammaArchimedean_rat hq).frobTwist
      ambGamma_lt_one.le N
  have hsum := hse.summable_eval (K := Ambient F) ambGamma_lt_one gammaArchimedean_rat (ambTheta F)
  have h0 : PowerSeries.coeff 0 (frobTwist (R := Ambient F) (p := Nat.card F) N
      (atOmegaGen (Nat.card F) (ambTheta F))) = 1 := by
    rw [frobTwist_coeff, coeff_zero_atOmegaGen, one_pow]
  rw [evalSeriesGen_def, Summable.tsum_eq_zero_add hsum, h0, pow_zero, mul_one]
  have : (1 : Ambient F) + ∑' m : ℕ,
      PowerSeries.coeff (m + 1) (frobTwist (R := Ambient F) (p := Nat.card F) N
        (atOmegaGen (Nat.card F) (ambTheta F))) * (ambTheta F) ^ (m + 1) - 1
      = ∑' m : ℕ, PowerSeries.coeff (m + 1) (frobTwist (R := Ambient F) (p := Nat.card F) N
        (atOmegaGen (Nat.card F) (ambTheta F))) * (ambTheta F) ^ (m + 1) := by ring
  rw [this]
  refine tsum_congr fun m => ?_
  rw [frobTwist_coeff]

end Tail


section Factorisation

/-- **N2a, step 4(a): the factorisation of the value of `Ω` at `θ`** (small atoms: the two
super-entire hypotheses are stated first, and the telescoping identity is applied with `conv_lhs`
so that only the left-hand side is rewritten). -/
theorem evalSeriesGen_atOmegaGen_eq_mul (N : ℕ) :
    evalSeriesGen (atOmegaGen (Nat.card F) (ambTheta F)) (ambTheta F)
      = evalSeriesGen (omPartial (Nat.card F) (ambTheta F) N) (ambTheta F)
        * evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) N
            (atOmegaGen (Nat.card F) (ambTheta F))) (ambTheta F) := by
  have hseP : GSuperEntire ambGamma (omPartial (Nat.card F) (ambTheta F) N) :=
    gSuperEntire_omPartial F N
  have hseT : GSuperEntire ambGamma
      (frobTwist (R := Ambient F) (p := Nat.card F) N (atOmegaGen (Nat.card F) (ambTheta F))) :=
    (gSuperEntire_atOmegaGen (K := Ambient F) (q := Nat.card F) (θ := ambTheta F)
      ambGamma_pos (v_ambTheta_inv_le F) ambGamma_lt_one gammaArchimedean_rat
      (two_le_ambCard F)).frobTwist ambGamma_lt_one.le N
  have htel := atOmegaGen_eq_omPartial_mul_frobTwist (K := Ambient F) (q := Nat.card F)
    (θ := ambTheta F) (γ := ambGamma) ambGamma_pos (v_ambTheta_inv_le F) ambGamma_lt_one
    gammaArchimedean_rat (two_le_ambCard F) N
  conv_lhs => rw [htel]
  rw [evalSeriesGen_mul ambGamma_lt_one gammaArchimedean_rat hseP hseT (ambTheta F)]

end Factorisation

section GammaPow

/-- **N2a, step 4(b): `ambGamma` is strictly smaller than `1` in every positive power.** -/
lemma ambGamma_pow_lt_one {k : ℕ} (hk : 1 ≤ k) : ambGamma ^ k < 1 := by
  rw [show ambGamma = WithZero.exp (-1 : ℚ) from rfl, ← WithZero.exp_nsmul,
    ← WithZero.exp_zero, WithZero.exp_lt_exp, nsmul_eq_mul]
  have hk' : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hk
  linarith

/-- The uniform bound used in the tail estimate: `ambGamma^((q-1)^2) < 1`. -/
lemma ambGamma_pow_pred_sq_lt_one : ambGamma ^ ((Nat.card F - 1) * (Nat.card F - 1)) < 1 := by
  refine ambGamma_pow_lt_one ?_
  have h := two_le_ambCard F
  have h1 : 1 ≤ Nat.card F - 1 := by omega
  exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))

end GammaPow

section TailBound

set_option maxHeartbeats 800000 in
/-- **N2a, step 4(c): the tail bound.**  From the pointwise bound `hb` (the sharp coefficient bound
`v_coeff_atOmegaGen_le_sharp_gen` combined with the ℕ core
`Commons.Combinatorics.Nat.geom_sum_mul_pow_ge`), the *tail* of the twisted period differs from `1`
by something of value `< 1`:

`v ((Ω^{(N)})(θ) - 1) < 1`. -/
theorem v_frobTwistAtOmegaGen_sub_one_lt_one (N : ℕ)
    (hb : ∀ m : ℕ, Valued.v (PowerSeries.coeff (m + 1)
        (frobTwist (R := Ambient F) (p := Nat.card F) N (atOmegaGen (Nat.card F) (ambTheta F)))
          * (ambTheta F) ^ (m + 1)) ≤ ambGamma ^ ((Nat.card F - 1) * (Nat.card F - 1))) :
    Valued.v (evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) N
      (atOmegaGen (Nat.card F) (ambTheta F))) (ambTheta F) - 1) < 1 := by
  have hse : GSuperEntire ambGamma (atOmegaGen (Nat.card F) (ambTheta F)) :=
    gSuperEntire_atOmegaGen (K := Ambient F) (q := Nat.card F) (θ := ambTheta F)
      ambGamma_pos (v_ambTheta_inv_le F) ambGamma_lt_one gammaArchimedean_rat (two_le_ambCard F)
  have hseT : GSuperEntire ambGamma
      (frobTwist (R := Ambient F) (p := Nat.card F) N (atOmegaGen (Nat.card F) (ambTheta F))) :=
    hse.frobTwist ambGamma_lt_one.le N
  have hsum : Summable fun m : ℕ => PowerSeries.coeff (m + 1)
      (frobTwist (R := Ambient F) (p := Nat.card F) N (atOmegaGen (Nat.card F) (ambTheta F)))
        * (ambTheta F) ^ (m + 1) :=
    (summable_nat_add_iff 1).mpr
      (hseT.summable_eval (K := Ambient F) ambGamma_lt_one gammaArchimedean_rat (ambTheta F))
  rw [evalSeriesGen_frobTwistAtOmegaGen_sub_one F N]
  rw [tsum_congr (fun m => by rw [← frobTwist_coeff])]
  exact lt_of_le_of_lt
    (Commons.Topology.Algebra.Valued.v_tsum_le_of_forall_le_general hsum hb)
    (ambGamma_pow_pred_sq_lt_one F)

end TailBound



section Hinge

/-- **N2a, the hinge**: `(v θ)⁻¹ = ambGamma^(q-1)`. -/
lemma v_ambTheta_inv_eq_ambGamma_pow :
    (Valued.v (ambTheta F))⁻¹ = ambGamma ^ (Nat.card F - 1) := by
  have hq1 : 1 ≤ Nat.card F := by have := two_le_ambCard F; omega
  rw [v_ambTheta]
  conv_rhs => rw [show ambGamma = WithZero.exp (-1 : ℚ) from rfl]
  rw [← WithZero.exp_neg, ← WithZero.exp_nsmul]
  congr 1
  rw [nsmul_eq_mul, Nat.cast_sub hq1, Nat.cast_one]
  ring

end Hinge


section HB

/-- **N2a, `hb`, part 1**: the inverse of `(v θ)^k` in terms of positive powers of `ambGamma`
(via the hinge), so that no negative exponents are ever needed. -/
lemma inv_v_ambTheta_pow (k : ℕ) :
    ((Valued.v (ambTheta F)) ^ k)⁻¹ = ambGamma ^ ((Nat.card F - 1) * k) := by
  rw [← inv_pow, v_ambTheta_inv_eq_ambGamma_pow, ← pow_mul]

/-- **N2a, `hb`, part 2**: the exponent comparison, from the delegated ℕ core
`Commons.Combinatorics.Nat.geom_sum_mul_pow_ge`. -/
lemma pred_mul_sharp_ge (N m : ℕ) :
    (Nat.card F - 1) * (Nat.card F - 1) + (Nat.card F - 1) * (m + 1)
      ≤ (Nat.card F - 1) * (sharpExpGen (Nat.card F) (m + 1) * Nat.card F ^ N) := by
  have h := Commons.Combinatorics.Nat.geom_sum_mul_pow_ge (q := Nat.card F) (m := m) (N := N)
    (two_le_ambCard F)
  have h' : (Nat.card F - 1) + (m + 1)
      ≤ (∑ i ∈ Finset.range (m + 1), Nat.card F ^ (i + 1)) * Nat.card F ^ N := by
    rw [Nat.add_comm]; exact h
  rw [sharpExpGen]
  calc (Nat.card F - 1) * (Nat.card F - 1) + (Nat.card F - 1) * (m + 1)
      = (Nat.card F - 1) * ((Nat.card F - 1) + (m + 1)) := by ring
    _ ≤ (Nat.card F - 1) * ((∑ i ∈ Finset.range (m + 1), Nat.card F ^ (i + 1)) * Nat.card F ^ N) :=
        Nat.mul_le_mul_left _ h'

end HB

section Assembly

/-- **N2a, step 4(d): the assembly.**  From the pointwise tail bound `hb` (which `hb`'s own lemma
discharges from the sharp coefficient bound and `geom_sum_mul_pow_ge`), the value of `Ω` at `θ` is a
**unit**: `v (Ω(θ)) = 1`. -/
theorem v_evalSeriesGen_atOmegaGen_of_tail (N : ℕ)
    (hb : ∀ m : ℕ, Valued.v (PowerSeries.coeff (m + 1)
        (frobTwist (R := Ambient F) (p := Nat.card F) N (atOmegaGen (Nat.card F) (ambTheta F)))
          * (ambTheta F) ^ (m + 1)) ≤ ambGamma ^ ((Nat.card F - 1) * (Nat.card F - 1))) :
    Valued.v (evalSeriesGen (atOmegaGen (Nat.card F) (ambTheta F)) (ambTheta F)) = 1 := by
  have hP := evalSeriesGen_atOmegaGen_eq_mul F N
  have htail := v_frobTwistAtOmegaGen_sub_one_lt_one F N hb
  have hT : Valued.v (evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) N
      (atOmegaGen (Nat.card F) (ambTheta F))) (ambTheta F)) = 1 :=
    v_eq_one_of_v_sub_one_lt F htail
  rw [hP, map_mul, v_evalSeriesGen_omPartial F N, hT, mul_one]

end Assembly


section HBLemma

set_option maxHeartbeats 800000 in
/-- ★★★ **N2a, `hb`**: the pointwise bound for the tail terms,
`v (coeff (m+1) (Ω^{(N)}) · θ^(m+1)) ≤ ambGamma^((q-1)^2)`. -/
theorem v_frobTwistAtOmegaGen_term_le (N m : ℕ) :
    Valued.v (PowerSeries.coeff (m + 1)
        (frobTwist (R := Ambient F) (p := Nat.card F) N (atOmegaGen (Nat.card F) (ambTheta F)))
          * (ambTheta F) ^ (m + 1))
      ≤ ambGamma ^ ((Nat.card F - 1) * (Nat.card F - 1)) := by
  have hγ0 : (0 : ℚᵐ⁰) < ambGamma := ambGamma_pos
  have hγ1 : ambGamma ≤ 1 := ambGamma_lt_one.le
  have hγne : ambGamma ≠ 0 := ne_of_gt hγ0
  have hθinv : (Valued.v (ambTheta F))⁻¹ ≤ ambGamma := by
    rw [v_ambTheta_inv_eq_ambGamma_pow]
    calc ambGamma ^ (Nat.card F - 1) ≤ ambGamma ^ 1 :=
          pow_le_pow_of_le_one (zero_le) hγ1 (by have := two_le_ambCard F; omega)
      _ = ambGamma := pow_one _
  have hsharp := v_coeff_atOmegaGen_le_sharp_gen (K := Ambient F) (q := Nat.card F)
    (θ := ambTheta F) (γ := ambGamma) hγ0 hθinv ambGamma_lt_one gammaArchimedean_rat
    (two_le_ambCard F) (m + 1)
  have hval : Valued.v (PowerSeries.coeff (m + 1)
        (frobTwist (R := Ambient F) (p := Nat.card F) N (atOmegaGen (Nat.card F) (ambTheta F)))
          * (ambTheta F) ^ (m + 1))
      = (Valued.v (PowerSeries.coeff (m + 1)
            (atOmegaGen (Nat.card F) (ambTheta F)))) ^ (Nat.card F ^ N)
        * (Valued.v (ambTheta F)) ^ (m + 1) := by
    rw [map_mul, frobTwist_coeff, map_pow, map_pow]
  have hA : (Valued.v (PowerSeries.coeff (m + 1)
        (atOmegaGen (Nat.card F) (ambTheta F)))) ^ (Nat.card F ^ N)
      ≤ ambGamma ^ ((Nat.card F - 1) * (sharpExpGen (Nat.card F) (m + 1) * Nat.card F ^ N)) := by
    calc (Valued.v (PowerSeries.coeff (m + 1)
            (atOmegaGen (Nat.card F) (ambTheta F)))) ^ (Nat.card F ^ N)
        ≤ (((Valued.v (ambTheta F))⁻¹) ^ (sharpExpGen (Nat.card F) (m + 1)))
            ^ (Nat.card F ^ N) :=
          pow_le_pow_left₀ (zero_le) hsharp _
      _ = ((Valued.v (ambTheta F))⁻¹) ^ (sharpExpGen (Nat.card F) (m + 1) * Nat.card F ^ N) := by
          rw [← pow_mul]
      _ = (ambGamma ^ (Nat.card F - 1))
            ^ (sharpExpGen (Nat.card F) (m + 1) * Nat.card F ^ N) := by
          rw [v_ambTheta_inv_eq_ambGamma_pow]
      _ = ambGamma ^ ((Nat.card F - 1) * (sharpExpGen (Nat.card F) (m + 1) * Nat.card F ^ N)) := by
          rw [← pow_mul]
  have hmono : ambGamma ^ ((Nat.card F - 1) * (sharpExpGen (Nat.card F) (m + 1) * Nat.card F ^ N))
      ≤ ambGamma ^ ((Nat.card F - 1) * (Nat.card F - 1) + (Nat.card F - 1) * (m + 1)) :=
    pow_le_pow_of_le_one (zero_le) hγ1 (pred_mul_sharp_ge F N m)
  have hB : (Valued.v (ambTheta F)) ^ (m + 1)
      = (ambGamma ^ ((Nat.card F - 1) * (m + 1)))⁻¹ := by
    rw [← inv_v_ambTheta_pow F (m + 1), inv_inv]
  calc Valued.v (PowerSeries.coeff (m + 1)
        (frobTwist (R := Ambient F) (p := Nat.card F) N (atOmegaGen (Nat.card F) (ambTheta F)))
          * (ambTheta F) ^ (m + 1))
      = (Valued.v (PowerSeries.coeff (m + 1)
            (atOmegaGen (Nat.card F) (ambTheta F)))) ^ (Nat.card F ^ N)
          * (Valued.v (ambTheta F)) ^ (m + 1) := hval
    _ ≤ ambGamma ^ ((Nat.card F - 1) * (sharpExpGen (Nat.card F) (m + 1) * Nat.card F ^ N))
          * (Valued.v (ambTheta F)) ^ (m + 1) :=
        mul_le_mul_of_nonneg_right hA (zero_le)
    _ ≤ ambGamma ^ ((Nat.card F - 1) * (Nat.card F - 1) + (Nat.card F - 1) * (m + 1))
          * (Valued.v (ambTheta F)) ^ (m + 1) :=
        mul_le_mul_of_nonneg_right hmono (zero_le)
    _ = ambGamma ^ ((Nat.card F - 1) * (Nat.card F - 1)) := by
        rw [hB, pow_add, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hγne), mul_one]

end HBLemma

section Unconditional

/-- ★★★ **N2a COMPLETE: the value of `Ω` at `θ` is a unit** — `v (evalSeriesGen (atOmegaGen q θ) θ) = 1`,
unconditionally (the pointwise bound is `v_frobTwistAtOmegaGen_term_le`). -/
theorem v_evalSeriesGen_atOmegaGen (N : ℕ) :
    Valued.v (evalSeriesGen (atOmegaGen (Nat.card F) (ambTheta F)) (ambTheta F)) = 1 :=
  v_evalSeriesGen_atOmegaGen_of_tail F N (fun m => v_frobTwistAtOmegaGen_term_le F N m)

end Unconditional

end ZagierHoffmanPositiveChar
