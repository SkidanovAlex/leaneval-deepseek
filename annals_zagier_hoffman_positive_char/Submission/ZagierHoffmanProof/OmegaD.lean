import Submission.ZagierHoffmanProof.LSeries

/-!
# The Anderson–Thakur period function for a general normalisation `v θ = exp d`

`Omega.lean` develops the period function `Ω = ∏_{i ≥ 1}(1 - t/θ^{q^i})` under the normalisation
`v θ = exp 1` (i.e. `θ` is a uniformiser of the base field, as for `θ = X ∈ K∞ = F((1/X))`).

This file redoes the *quantitative* part of that development for a general normalisation
`v θ = exp d` with `1 ≤ d`.  The motivation (see `PLAN.md` SESSION 302 LOG §4) is that the period
constant `μ = (-θ)^{-q/(q-1)}` (with `μ^{q-1} = -θ^{-q}`) cannot live in a field where `v θ = 1`
since then `v μ = -q/(q-1) ∉ ℤ`; the concrete model is `L = F((y))` with
`θ = -y^{-(q-1)}` and `d = q - 1` (`KummerField.lean`).  The *algebraic* identities
(`atOmega_twist`, `atOmega_eq_omPartial_mul_frobTwist`, …) are proved in `Omega.lean` and are
normalisation-independent; only the coefficient bounds acquire the factor `d`.

## Main results

* `v_omX_d` — `v (omX q θ i) = exp (-(d * q^i))`.
* `v_coeff_omPartial_le_d` — `v (coeff m (omPartial N)) ≤ exp (-(d*m))`.
* `v_coeff_telescope_le_d`, `summable_telescope_d`, `tendsto_coeff_omPartial_d`.
* ★ `v_coeff_atOmega_le_d` — `v (coeff m Ω) ≤ exp (-(d*m))`.
* ★ `isSmall_atOmega_d` — `IsSmall Ω` whenever `d ≥ 1`.
* `atOmega_bounded_d`, `atOmega_entire_d`, `atOmega_twist_d`.
* ★ `v_coeff_pow_atOmega_le_d` — `v (coeff n (Ω^s)) ≤ exp (-d)` for `n ≥ 1`, hence
  `isSmall_pow_atOmega_d`.
-/

set_option autoImplicit false
open Filter Polynomial RatFunc
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] [Valued K ℤᵐ⁰]

section basic

/-- `v_omX` for the normalisation `v θ = exp d`. -/
lemma v_omX_d (q : ℕ) (θ : K) (d : ℤ) (hθ : Valued.v θ = WithZero.exp d) (i : ℕ) :
    Valued.v (omX q θ i) = WithZero.exp (-(d * (((q ^ i : ℕ)) : ℤ))) := by
  rw [omX, Valuation.map_inv, Valuation.map_pow, hθ, expmul d (q ^ i),
    ← WithZero.exp_neg]

/-- The uniform coefficient bound `v (coeff m (omPartial N)) ≤ exp (-(d*m))`. -/
lemma v_coeff_omPartial_le_d (q : ℕ) (θ : K) (d : ℤ) (hd : 1 ≤ d)
    (hθ : Valued.v θ = WithZero.exp d) (hq : 2 ≤ q) :
    ∀ (N m : ℕ), Valued.v (PowerSeries.coeff m (omPartial q θ N))
      ≤ WithZero.exp (-(d * (m : ℤ))) := by
  intro N
  induction N with
  | zero =>
    intro m
    rw [omPartial_zero, PowerSeries.coeff_one]
    by_cases h : m = 0
    · subst h
      rw [if_pos rfl, map_one]
      simp
    · rw [if_neg h, map_zero]
      exact bot_le
  | succ N ih =>
    intro m
    rw [coeff_omPartial_succ]
    refine Valuation.map_sub_le _ (ih m) ?_
    by_cases h : 1 ≤ m
    · rw [if_pos h, Valuation.map_mul, v_omX_d q θ d hθ (N + 1)]
      have hm : (((m - 1 : ℕ)) : ℤ) = (m : ℤ) - 1 := Nat.cast_sub h
      calc Valued.v ((PowerSeries.coeff (m - 1)) (omPartial q θ N))
              * WithZero.exp (-(d * (((q ^ (N + 1) : ℕ)) : ℤ)))
          ≤ WithZero.exp (-(d * (((m - 1 : ℕ)) : ℤ)))
              * WithZero.exp (-(d * (((q ^ (N + 1) : ℕ)) : ℤ))) :=
            mul_le_mul' (ih (m - 1)) le_rfl
        _ = WithZero.exp (-(d * (((m - 1 : ℕ)) : ℤ))
              + -(d * (((q ^ (N + 1) : ℕ)) : ℤ))) := by rw [← WithZero.exp_add]
        _ ≤ WithZero.exp (-(d * (m : ℤ))) := by
            apply WithZero.exp_le_exp.mpr
            rw [hm]
            have h1 : (1 : ℤ) ≤ ((q ^ (N + 1) : ℕ) : ℤ) := by
              have := Nat.one_le_pow (N + 1) q (by omega : 1 ≤ q)
              exact_mod_cast this
            have hm1 : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast h
            have hd0 : (0 : ℤ) ≤ d := by omega
            nlinarith [mul_nonneg hd0 (sub_nonneg.mpr h1), mul_nonneg hd0 (by omega : (0:ℤ) ≤ (m:ℤ))]
    · rw [if_neg h, map_zero]
      exact bot_le

lemma v_coeff_telescope_le_d (q : ℕ) (θ : K) (d : ℤ) (hd : 1 ≤ d)
    (hθ : Valued.v θ = WithZero.exp d) (hq : 2 ≤ q) (m N : ℕ) (hm : 1 ≤ m) :
    Valued.v (PowerSeries.coeff m (omPartial q θ (N + 1)) - PowerSeries.coeff m (omPartial q θ N))
      ≤ WithZero.exp (-(d * (((q ^ (N + 1) : ℕ)) : ℤ)) + -(d * (((m - 1 : ℕ)) : ℤ))) := by
  rw [coeff_telescope_eq, if_pos hm, Valuation.map_neg, Valuation.map_mul,
    v_omX_d q θ d hθ (N + 1)]
  calc Valued.v ((PowerSeries.coeff (m - 1)) (omPartial q θ N))
          * WithZero.exp (-(d * (((q ^ (N + 1) : ℕ)) : ℤ)))
      ≤ WithZero.exp (-(d * (((m - 1 : ℕ)) : ℤ)))
          * WithZero.exp (-(d * (((q ^ (N + 1) : ℕ)) : ℤ))) :=
        mul_le_mul' (v_coeff_omPartial_le_d q θ d hd hθ hq N (m - 1)) le_rfl
    _ = WithZero.exp (-(d * (((m - 1 : ℕ)) : ℤ))
          + -(d * (((q ^ (N + 1) : ℕ)) : ℤ))) := by rw [← WithZero.exp_add]
    _ = WithZero.exp (-(d * (((q ^ (N + 1) : ℕ)) : ℤ))
          + -(d * (((m - 1 : ℕ)) : ℤ))) := by rw [add_comm]

end basic

section omegaCont

variable (q : ℕ) (θ : K) [CompleteSpace K] [NonarchimedeanAddGroup K]

lemma summable_telescope_d (d : ℤ) (hd : 1 ≤ d) (hθ : Valued.v θ = WithZero.exp d)
    (hq : 2 ≤ q) (m : ℕ) :
    Summable (fun N : ℕ => PowerSeries.coeff m (omPartial q θ (N + 1))
      - PowerSeries.coeff m (omPartial q θ N)) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    refine (summable_zero : Summable (fun _ : ℕ => (0 : K))).congr fun N => ?_
    simp [constantCoeff_omPartial]
  · refine Commons.Topology.Algebra.Valued.summable_of_tendsto_v_zero (fun n => ?_)
    rw [Filter.eventually_atTop]
    refine ⟨(n.natAbs + m + 1), fun N hN => ?_⟩
    refine lt_of_le_of_lt (v_coeff_telescope_le_d q θ d hd hθ hq m N hm) ?_
    rw [WithZero.exp_lt_exp]
    have hN' : n.natAbs + m + 1 ≤ q ^ N := by
      have h1 : N < q ^ N := Nat.lt_pow_self (by omega : 1 < q)
      omega
    have hN'' : q ^ N ≤ q ^ (N + 1) := Nat.pow_le_pow_right (by omega : 1 ≤ q) (by omega)
    have hcast : ((n.natAbs + m + 1 : ℕ) : ℤ) ≤ ((q ^ (N + 1) : ℕ) : ℤ) := by
      exact_mod_cast le_trans hN' hN''
    have hn : (n : ℤ) ≤ (n.natAbs : ℤ) := Int.le_natAbs
    have hm1 : (((m - 1 : ℕ)) : ℤ) = (m : ℤ) - 1 := Nat.cast_sub hm
    have hd0 : (0 : ℤ) ≤ d := by omega
    have hA : d * (((n.natAbs + m + 1 : ℕ)) : ℤ) ≤ d * (((q ^ (N + 1) : ℕ)) : ℤ) :=
      mul_le_mul_of_nonneg_left hcast hd0
    have hB : (((n.natAbs + m + 1 : ℕ)) : ℤ) = (n.natAbs : ℤ) + (m : ℤ) + 1 := by push_cast; ring
    rw [hB] at hA
    have hC : d * (((m - 1 : ℕ)) : ℤ) = d * (m : ℤ) - d := by rw [hm1]; ring
    have hE : (n.natAbs : ℤ) ≤ d * (n.natAbs : ℤ) := le_mul_of_one_le_left (by positivity) hd
    have hF : -(n : ℤ) ≤ (n.natAbs : ℤ) := by
      have := Int.le_natAbs (a := -n); simpa [Int.natAbs_neg] using this
    have hm1'' : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
    nlinarith [hA, hC, hE, hF, hm1'']

/-- The coefficients of the partial products converge to those of `Ω` (general `d`). -/
lemma tendsto_coeff_omPartial_d (d : ℤ) (hd : 1 ≤ d) (hθ : Valued.v θ = WithZero.exp d)
    (hq : 2 ≤ q) (m : ℕ) :
    Tendsto (fun N => PowerSeries.coeff m (omPartial q θ N)) atTop (𝓝 (omCoeff q θ m)) := by
  have hs := (summable_telescope_d q θ d hd hθ hq m).hasSum
  have h1 := hs.tendsto_sum_nat
  have h2 : ∀ N : ℕ, ∑ i ∈ Finset.range N,
        (PowerSeries.coeff m (omPartial q θ (i + 1)) - PowerSeries.coeff m (omPartial q θ i))
      = PowerSeries.coeff m (omPartial q θ N) - PowerSeries.coeff m (omPartial q θ 0) :=
    fun N => Finset.sum_range_sub (fun i => PowerSeries.coeff m (omPartial q θ i)) N
  have h3 : Tendsto (fun N => PowerSeries.coeff m (omPartial q θ N)
        - PowerSeries.coeff m (omPartial q θ 0)) atTop
      (𝓝 (∑' N : ℕ, (PowerSeries.coeff m (omPartial q θ (N + 1))
        - PowerSeries.coeff m (omPartial q θ N)))) :=
    Tendsto.congr' (Eventually.of_forall h2) h1
  have h4 := h3.add_const (PowerSeries.coeff m (omPartial q θ 0))
  have h5 : Tendsto (fun N => PowerSeries.coeff m (omPartial q θ N)) atTop
      (𝓝 ((∑' N : ℕ, (PowerSeries.coeff m (omPartial q θ (N + 1))
        - PowerSeries.coeff m (omPartial q θ N))) + PowerSeries.coeff m (omPartial q θ 0))) :=
    Tendsto.congr' (Eventually.of_forall (fun N => sub_add_cancel _ _)) h4
  exact h5

lemma tendsto_coeff_omPartial_succ_d (d : ℤ) (hd : 1 ≤ d) (hθ : Valued.v θ = WithZero.exp d)
    (hq : 2 ≤ q) (m : ℕ) :
    Tendsto (fun N => PowerSeries.coeff m (omPartial q θ (N + 1))) atTop
      (𝓝 (PowerSeries.coeff m (atOmega q θ))) := by
  rw [coeff_atOmega]
  exact (tendsto_coeff_omPartial_d q θ d hd hθ hq m).comp (tendsto_add_atTop_nat 1)

end omegaCont

section main

variable (q : ℕ) [FrobPow K q] (θ : K) [CompleteSpace K] [NonarchimedeanAddGroup K]

/-- **The functional equation of `Ω` for a general normalisation**. -/
theorem atOmega_twist_d (d : ℤ) (hd : 1 ≤ d) (hθ : Valued.v θ = WithZero.exp d) (hq : 2 ≤ q) :
    (1 - PowerSeries.C (omX q θ 1) * PowerSeries.X)
        * frobTwist (R := K) (p := q) 1 (atOmega q θ)
      = atOmega q θ := by
  have hlim1 : ∀ m : ℕ, Tendsto (fun N => PowerSeries.coeff m
        ((1 - PowerSeries.C (omX q θ 1) * PowerSeries.X)
          * frobTwist (R := K) (p := q) 1 (omPartial q θ N)))
      atTop (𝓝 (PowerSeries.coeff m ((1 - PowerSeries.C (omX q θ 1) * PowerSeries.X)
        * frobTwist (R := K) (p := q) 1 (atOmega q θ)))) := by
    intro m
    have h := tendsto_coeff_mul_right
      (fun k => tendsto_coeff_frobTwist (q := q) (g := atOmega q θ)
        (fun k => by rw [coeff_atOmega]; exact tendsto_coeff_omPartial_d q θ d hd hθ hq k) k)
      (1 - PowerSeries.C (omX q θ 1) * PowerSeries.X) m
    simpa only [mul_comm] using h
  have hlim2 : ∀ m : ℕ, Tendsto (fun N => PowerSeries.coeff m
        ((1 - PowerSeries.C (omX q θ 1) * PowerSeries.X)
          * frobTwist (R := K) (p := q) 1 (omPartial q θ N)))
      atTop (𝓝 (PowerSeries.coeff m (atOmega q θ))) := by
    intro m
    refine Tendsto.congr' (Eventually.of_forall (fun N => ?_))
      (tendsto_coeff_omPartial_succ_d q θ d hd hθ hq m)
    simp only [omPartial_twist_succ]
  exact powerSeries_eq_of_tendsto_coeff hlim1 hlim2

/-- **The general functional equation of `Ω` for a general normalisation**:
`Ω = (∏_{i=1}^{N}(1 - t/θ^{q^i})) · Ω^{(N)}`. -/
theorem atOmega_eq_omPartial_mul_frobTwist_d (d : ℤ) (hd : 1 ≤ d)
    (hθ : Valued.v θ = WithZero.exp d) (hq : 2 ≤ q) (N : ℕ) :
    atOmega q θ = omPartial q θ N * frobTwist (R := K) (p := q) N (atOmega q θ) := by
  induction N with
  | zero => rw [omPartial_zero, frobTwist_zero_iter, one_mul]
  | succ N ih =>
    have h1 : frobTwist (R := K) (p := q) 1 (atOmega q θ)
        = frobTwist (R := K) (p := q) 1 (omPartial q θ N)
          * frobTwist (R := K) (p := q) (N + 1) (atOmega q θ) := by
      have h2 := congrArg (frobTwist (R := K) (p := q) 1) ih
      rw [frobTwist_mul, frobTwist_comp, Nat.one_add] at h2
      exact h2
    calc atOmega q θ
        = (1 - PowerSeries.C (omX q θ 1) * PowerSeries.X)
            * frobTwist (R := K) (p := q) 1 (atOmega q θ) :=
          (atOmega_twist_d q θ d hd hθ hq).symm
      _ = (1 - PowerSeries.C (omX q θ 1) * PowerSeries.X)
            * (frobTwist (R := K) (p := q) 1 (omPartial q θ N)
              * frobTwist (R := K) (p := q) (N + 1) (atOmega q θ)) := by rw [h1]
      _ = ((1 - PowerSeries.C (omX q θ 1) * PowerSeries.X)
            * frobTwist (R := K) (p := q) 1 (omPartial q θ N))
            * frobTwist (R := K) (p := q) (N + 1) (atOmega q θ) := by ring
      _ = omPartial q θ (N + 1) * frobTwist (R := K) (p := q) (N + 1) (atOmega q θ) := by
          rw [omPartial_twist_succ]

end main

section bounds

variable (q : ℕ) (θ : K) [CompleteSpace K] [NonarchimedeanAddGroup K]

/-- **The coefficientwise bound `v (coeff m Ω) ≤ exp (-(d*m))`.** -/
lemma v_coeff_atOmega_le_d (d : ℤ) (hd : 1 ≤ d) (hθ : Valued.v θ = WithZero.exp d)
    (hq : 2 ≤ q) (m : ℕ) :
    Valued.v (PowerSeries.coeff m (atOmega q θ)) ≤ WithZero.exp (-(d * (m : ℤ))) := by
  rw [coeff_atOmega, omCoeff]
  refine Valuation.map_add_le _ ?_ (v_coeff_omPartial_le_d q θ d hd hθ hq 0 m)
  refine Commons.Topology.Algebra.Valued.v_tsum_le_of_forall_le
    (summable_telescope_d q θ d hd hθ hq m) (fun N => ?_)
  by_cases hm : 1 ≤ m
  · refine le_trans (v_coeff_telescope_le_d q θ d hd hθ hq m N hm) ?_
    apply WithZero.exp_le_exp.mpr
    have h1 : (1 : ℤ) ≤ ((q ^ (N + 1) : ℕ) : ℤ) := by
      have := Nat.one_le_pow (N + 1) q (by omega : 1 ≤ q)
      exact_mod_cast this
    have hm1 : (((m - 1 : ℕ)) : ℤ) = (m : ℤ) - 1 := Nat.cast_sub hm
    have hd0 : (0 : ℤ) ≤ d := by omega
    have hm1' : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
    nlinarith [mul_nonneg hd0 (sub_nonneg.mpr h1), mul_nonneg hd0 (by omega : (0:ℤ) ≤ (m:ℤ))]
  · have h0 : m = 0 := by omega
    subst h0
    have hz : PowerSeries.coeff 0 (omPartial q θ (N + 1))
        - PowerSeries.coeff 0 (omPartial q θ N) = 0 := by
      simp only [coeff_zero_omPartial, sub_self]
    rw [hz, map_zero]
    exact bot_le

/-- The coefficients of `Ω` are bounded by `1` (the constant term is `1`). -/
lemma v_coeff_atOmega_le_one_d (d : ℤ) (hd : 1 ≤ d) (hθ : Valued.v θ = WithZero.exp d)
    (hq : 2 ≤ q) : ∀ n : ℕ, Valued.v (PowerSeries.coeff n (atOmega q θ)) ≤ 1 := by
  intro n
  refine le_trans (v_coeff_atOmega_le_d q θ d hd hθ hq n) (WithZero.exp_le_exp.mpr ?_)
  have hd0 : (0 : ℤ) ≤ d := by omega
  have : (0 : ℤ) ≤ d * (n : ℤ) := mul_nonneg hd0 (by positivity)
  omega

/-- **`c·Ω` is small** whenever `v c ≤ exp (-1)`: multiplying the period function by a small
constant puts it in the maximal ideal of the Tate algebra.  (This is the normalisation used by
`omegaSmall`; over the Kummer field the period constant `μ` itself is small, `v μ = exp (-q)`.) -/
lemma isSmall_C_mul_atOmega_d (d : ℤ) (hd : 1 ≤ d) (hθ : Valued.v θ = WithZero.exp d)
    (hq : 2 ≤ q) {c : K} (hc : Valued.v c ≤ WithZero.exp (-1)) :
    IsSmall (PowerSeries.C c * atOmega q θ) := by
  intro n
  rw [PowerSeries.coeff_C_mul, Valuation.map_mul]
  calc Valued.v c * Valued.v (PowerSeries.coeff n (atOmega q θ))
      ≤ WithZero.exp (-1) * 1 := mul_le_mul' hc (v_coeff_atOmega_le_one_d q θ d hd hθ hq n)
    _ = WithZero.exp (-1) := mul_one _

/-- The coefficients of every power of `Ω` are bounded by `1`. -/
lemma v_coeff_pow_atOmega_le_one_d (d : ℤ) (hd : 1 ≤ d) (hθ : Valued.v θ = WithZero.exp d)
    (hq : 2 ≤ q) : ∀ (s n : ℕ),
      Valued.v (PowerSeries.coeff n (atOmega q θ ^ s)) ≤ 1 := by
  intro s
  induction s with
  | zero =>
    intro n
    rw [pow_zero, PowerSeries.coeff_one]
    by_cases h : n = 0
    · subst h; rw [if_pos rfl, map_one]
    · rw [if_neg h, map_zero]; exact bot_le
  | succ s ih =>
    intro n
    rw [pow_succ, PowerSeries.coeff_mul]
    refine Valuation.map_sum_le (v := Valued.v) (fun p hp => ?_)
    rw [Valuation.map_mul]
    calc Valued.v (PowerSeries.coeff p.1 (atOmega q θ ^ s))
          * Valued.v (PowerSeries.coeff p.2 (atOmega q θ))
        ≤ 1 * 1 := mul_le_mul (ih p.1) (v_coeff_atOmega_le_one_d q θ d hd hθ hq p.2)
                      bot_le bot_le
      _ = 1 := one_mul _

/-- **The basic smallness input of the `L`-series**: for `1 ≤ s`, a small constant times a power of
`Ω` times a series with coefficients bounded by `1` is small. -/
lemma isSmall_C_mul_pow_atOmega_mul_d (d : ℤ) (hd : 1 ≤ d) (hθ : Valued.v θ = WithZero.exp d)
    (hq : 2 ≤ q) {c : K} (hc : Valued.v c ≤ WithZero.exp (-1)) {Q : PowerSeries K}
    (hQ : ∀ n : ℕ, Valued.v (PowerSeries.coeff n Q) ≤ 1) (s : ℕ) (_hs : 1 ≤ s) :
    IsSmall (PowerSeries.C c * atOmega q θ ^ s * Q) := by
  intro n
  rw [PowerSeries.coeff_mul]
  refine Valuation.map_sum_le (v := Valued.v) (fun p hp => ?_)
  rw [PowerSeries.coeff_C_mul, Valuation.map_mul, Valuation.map_mul]
  calc Valued.v c * Valued.v (PowerSeries.coeff p.1 (atOmega q θ ^ s))
        * Valued.v (PowerSeries.coeff p.2 Q)
      ≤ (WithZero.exp (-1) * 1) * 1 :=
        mul_le_mul (mul_le_mul hc (v_coeff_pow_atOmega_le_one_d q θ d hd hθ hq s p.1) bot_le bot_le)
          (hQ p.2) bot_le bot_le
    _ = WithZero.exp (-1) := by rw [mul_one, mul_one]

lemma atOmega_bounded_d (d : ℤ) (hd : 1 ≤ d) (hθ : Valued.v θ = WithZero.exp d)
    (hq : 2 ≤ q) : SeriesBounded (atOmega q θ) :=
  ⟨0, fun m => le_trans (v_coeff_atOmega_le_d q θ d hd hθ hq m)
    (WithZero.exp_le_exp.mpr (by
      have : (0 : ℤ) ≤ d * (m : ℤ) := mul_nonneg (by omega) (by positivity)
      omega))⟩

lemma atOmega_entire_d (d : ℤ) (hd : 1 ≤ d) (hθ : Valued.v θ = WithZero.exp d)
    (hq : 2 ≤ q) : Entire (atOmega q θ) := by
  intro N
  refine Filter.eventually_atTop.mpr ⟨N.natAbs + 2, fun m hm => ?_⟩
  refine lt_of_le_of_lt (v_coeff_atOmega_le_d q θ d hd hθ hq m)
    (WithZero.exp_lt_exp.mpr ?_)
  have h2 : ((N.natAbs : ℤ)) + 2 ≤ (m : ℤ) := by exact_mod_cast hm
  have h3 : N ≤ (N.natAbs : ℤ) := Int.le_natAbs
  have h4 : (1 : ℤ) ≤ d := hd
  nlinarith

end bounds

section inverse

variable (q : ℕ) (θ : K) [CompleteSpace K] [NonarchimedeanAddGroup K]

/-- The coefficients of the inverse of `Ω` are bounded by `1` in the general normalisation
`v θ = exp d`. -/
lemma v_omInvCoeff_le_d (d : ℤ) (hd : 1 ≤ d) (hθ : Valued.v θ = WithZero.exp d)
    (hq : 2 ≤ q) (m : ℕ) :
    Valued.v (omInvCoeff q θ m) ≤ WithZero.exp 0 := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero => rw [omInvCoeff_zero, map_one, WithZero.exp_zero]
    | succ m' =>
      rw [omInvCoeff_succ, Valuation.map_neg]
      refine Valued.v.map_sum_le (fun k hk => ?_)
      rw [Valuation.map_mul]
      calc Valued.v (PowerSeries.coeff (k + 1) (atOmega q θ))
              * Valued.v (omInvCoeff q θ (m' - k))
          ≤ WithZero.exp (-(d * (((k + 1 : ℕ)) : ℤ))) * WithZero.exp 0 :=
            mul_le_mul' (v_coeff_atOmega_le_d q θ d hd hθ hq (k + 1)) (ih (m' - k) (by omega))
        _ = WithZero.exp (-(d * (((k + 1 : ℕ)) : ℤ)) + 0) := by rw [← WithZero.exp_add]
        _ ≤ WithZero.exp 0 := WithZero.exp_le_exp.mpr (by
            have hd0 : (0 : ℤ) ≤ d := by omega
            have : (0 : ℤ) ≤ d * (((k + 1 : ℕ)) : ℤ) := mul_nonneg hd0 (by positivity)
            omega)

/-- `mk (omInvCoeff)` is a Tate series in the general normalisation. -/
lemma omInvCoeff_bounded_d (d : ℤ) (hd : 1 ≤ d) (hθ : Valued.v θ = WithZero.exp d)
    (hq : 2 ≤ q) : SeriesBounded (PowerSeries.mk (omInvCoeff q θ)) :=
  ⟨0, fun m => by rw [PowerSeries.coeff_mk]; exact v_omInvCoeff_le_d q θ d hd hθ hq m⟩

end inverse

end ZagierHoffmanPositiveChar
