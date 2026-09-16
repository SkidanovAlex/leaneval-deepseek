import Submission.ZagierHoffmanProof.MZProperty

/-!
# Specialisation of `L`-series relations at the points `t = c^{q^j}` (Step 2 of the paper)

This file formalises the **specialisation step** of the proof of Ngo Dac's Theorems B/D (paper §5,
"Step 2", the part of the argument that happens *after* the Anderson–Brownawell–Papanikolas
criterion has produced a relation between `L`-series with coefficients in `K̄(t)`).

The input is a relation

  `∑_k B_k(t)·𝓛_k(t)·Ω(t)^{w-w_k} = 0`

between `L`-series of weights `w_k ≤ w`, with coefficients `B_k = P_k/Q_k ∈ K̄(t)`.  Clearing the
denominators gives an identity between elements of `ε` (all factors are super-entire), so the
*ring homomorphism* `evalSeriesRingHom c : ε → K` can be applied to it; this is the algebraic core
(`specialise_sum_div`).  Specialising at `t = c^{q^j}` and using

* the MZ property `𝓛_k(c^{q^j}) = (𝓛_k(c))^{q^j}` (Chang, `MZProperty.lean`), and
* the vanishing `Ω(c^{q^j}) = 0` for `j ≥ 1` (the "simple zero" of `Ω` at its Frobenius orbit),

kills all the terms of weight `< w` and leaves the relation

  `∑_{k : w_k = w} B_k(c^{q^j})·(𝓛_k(c))^{q^j} = 0`

between the *values* of the maximal-weight `L`-series (`step2_specialisation`).  This is the
relation that the paper then combines with the lower-weight hypothesis `(LW)` and the MZ property
(Chang's Proposition 4.3.1) to conclude `B_k = 0`.

## Main results

* `lseriesWeight` — the weight `s_1+⋯+s_r` attached to a tuple of `L`-series data.
* `evalSeries_zero`.
* ★★ `specialise_sum_div` — clearing denominators and evaluating.
* ★★★ `step2_specialisation` — the specialisation of the paper's relation at `c^{q^j}`.
-/

set_option autoImplicit false
open Filter Polynomial RatFunc
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] [Valued K ℤᵐ⁰]
variable [CompleteSpace K] [NonarchimedeanAddGroup K]

/-- The weight `s_1 + ⋯ + s_r` attached to a tuple `[(s_1,Q_1),…,(s_r,Q_r)]` of `L`-series data. -/
def lseriesWeight (L : List (ℕ × PowerSeries K)) : ℕ := (L.map Prod.fst).sum

lemma evalSeries_zero (c : K) : evalSeries (0 : PowerSeries K) c = 0 := by
  simp [evalSeries_def]

/-- **Clearing denominators and evaluating.**  If the identity `∑_i (P_i/Q_i)·S_i = 0` holds (given
in the cleared form `∑_i (P_i ∏_{j≠i}Q_j)·S_i = 0` between power series, all factors super-entire)
and no denominator `Q_i` vanishes at `c`, then `∑_i (P_i(c)/Q_i(c))·S_i(c) = 0`. -/
theorem specialise_sum_div {ι : Type*} [DecidableEq ι] (s : Finset ι) (P Q : ι → Polynomial K)
    (S : ι → PowerSeries K) (c : K) (hS : ∀ i ∈ s, SuperEntire (S i))
    (hQ : ∀ i ∈ s, (Q i).eval c ≠ 0)
    (h : ∑ i ∈ s, ((P i * ∏ j ∈ s.erase i, Q j : Polynomial K) : PowerSeries K) * S i = 0) :
    ∑ i ∈ s, ((P i).eval c / (Q i).eval c) * evalSeries (S i) c = 0 := by
  have hterm : ∀ i ∈ s,
      SuperEntire (((P i * ∏ j ∈ s.erase i, Q j : Polynomial K) : PowerSeries K) * S i) :=
    fun i hi => (SuperEntire.polynomial _).mul (hS i hi)
  have h1 : evalSeries (∑ i ∈ s,
      ((P i * ∏ j ∈ s.erase i, Q j : Polynomial K) : PowerSeries K) * S i) c = 0 := by
    rw [h, evalSeries_zero]
  rw [evalSeries_finset_sum _ _ hterm c] at h1
  have h2 : ∑ i ∈ s, ((P i).eval c * ∏ j ∈ s.erase i, (Q j).eval c) * evalSeries (S i) c = 0 := by
    rw [← h1]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [evalSeries_mul (SuperEntire.polynomial _) (hS i hi) c, evalSeries_polynomial,
      Polynomial.eval_mul, Polynomial.eval_prod]
  have h3 : (∏ i ∈ s, (Q i).eval c)
      * (∑ i ∈ s, ((P i).eval c / (Q i).eval c) * evalSeries (S i) c) = 0 := by
    rw [Finset.mul_sum]
    rw [← h2]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Finset.mul_prod_erase s (fun i => (Q i).eval c) hi]
    have hq : (Q i).eval c ≠ 0 := hQ i hi
    field_simp
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact absurd h4 (Finset.prod_ne_zero_iff.mpr hQ)
  · exact h4

section step2

variable (q : ℕ) [FrobPow K q]

/-- The Frobenius orbit `j ↦ θ^{q^j}` is injective as soon as `1 ≤ v θ`. -/
lemma pow_q_injective {θ : K} {d : ℤ} (hd : 1 ≤ d) (hθ : Valued.v θ = WithZero.exp d)
    (hq : 2 ≤ q) : Function.Injective fun j : ℕ => θ ^ (q ^ j) := by
  have hmono : StrictMono fun j : ℕ => Valued.v (θ ^ (q ^ j)) := by
    intro i j hij
    show Valued.v (θ ^ (q ^ i)) < Valued.v (θ ^ (q ^ j))
    have h1 : Valued.v (θ ^ (q ^ i)) = WithZero.exp (d * ((q ^ i : ℕ) : ℤ)) := by
      rw [Valuation.map_pow, hθ, expmul]
    have h2 : Valued.v (θ ^ (q ^ j)) = WithZero.exp (d * ((q ^ j : ℕ) : ℤ)) := by
      rw [Valuation.map_pow, hθ, expmul]
    rw [h1, h2]
    refine WithZero.exp_lt_exp.mpr ?_
    have hlt : ((q ^ i : ℕ) : ℤ) < ((q ^ j : ℕ) : ℤ) := by
      exact_mod_cast Nat.pow_lt_pow_right (by omega : 1 < q) hij
    nlinarith [hd]
  intro i j hij
  exact hmono.injective (congrArg Valued.v hij)

/-- **A polynomial vanishing at `θ^{q^j}` for all large `j` is zero** (the paper's
"since `B_0 ∈ K̄(t)`, it follows that `B_0 = 0`"): the Frobenius orbit of `θ` is infinite, while a
non-zero polynomial has only finitely many roots. -/
theorem polynomial_eq_zero_of_eventually_eval_eq_zero {θ : K} {d : ℤ} (hd : 1 ≤ d)
    (hθ : Valued.v θ = WithZero.exp d) (hq : 2 ≤ q) {B : Polynomial K}
    (h : ∀ᶠ j : ℕ in Filter.atTop, B.eval (θ ^ (q ^ j)) = 0) : B = 0 := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
  have hinj : Function.Injective fun k : ℕ => θ ^ (q ^ (N + k)) := fun a b hab =>
    Nat.add_left_cancel (pow_q_injective (q := q) hd hθ hq hab)
  have hinf : Set.Infinite (Set.range fun k : ℕ => θ ^ (q ^ (N + k))) :=
    Set.infinite_range_of_injective hinj
  refine Polynomial.eq_zero_of_infinite_isRoot B ?_
  refine hinf.mono fun x hx => ?_
  obtain ⟨k, rfl⟩ := hx
  exact Polynomial.IsRoot.def.mpr (hN _ (Nat.le_add_right N k))

/-- **Step 2 of the paper: specialising a relation between `L`-series at `t = c^{q^j}`.**

Suppose `ω` is a "period datum" vanishing at the Frobenius orbit of `c` (`ω(c^{q^k}) = 0` for
`k ≥ 1`), `L k` are tuples of `L`-series data of weights `lseriesWeight (L k) ≤ W`, and the cleared
relation `∑_k (P_k ∏_{l≠k}Q_l)·(𝓛_k·ω^{W-w_k}) = 0` holds.  Then for every `j ≥ 1` and every point
at which all the `Q_k` are defined,

  `∑_{k : w_k = W} (P_k(c^{q^j})/Q_k(c^{q^j}))·(𝓛_k(c))^{q^j} = 0`.

(The terms of weight `< W` carry a *positive* power of `ω(c^{q^j}) = 0` and drop out; the
maximal-weight terms are evaluated by the MZ property of the `L`-series.) -/
theorem step2_specialisation {ω : PowerSeries K} (hq : 2 ≤ q) (hω : IsSmall ω)
    (hωse : SuperEntire ω) {c : K}
    (hc : ∀ k : ℕ, 1 ≤ k → evalSeries ω (c ^ (q ^ k)) = 0)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (L : ι → List (ℕ × PowerSeries K))
    (hne : ∀ k ∈ s, L k ≠ [])
    (hL : ∀ k ∈ s, ∀ x ∈ L k, IsSmall x.2)
    (hLse : ∀ k ∈ s, ∀ x ∈ L k, SuperEntire x.2)
    (hs : ∀ k ∈ s, ∀ x ∈ L k, 1 ≤ x.1)
    (P Q : ι → Polynomial K) (W : ℕ) (hW : ∀ k ∈ s, lseriesWeight (L k) ≤ W) {j : ℕ} (hj : 1 ≤ j)
    (hQc : ∀ k ∈ s, (Q k).eval (c ^ (q ^ j)) ≠ 0)
    (h : ∑ k ∈ s, ((P k * ∏ l ∈ s.erase k, Q l : Polynomial K) : PowerSeries K)
          * (atLrPaper q ω (L k) * ω ^ (W - lseriesWeight (L k))) = 0) :
    ∑ k ∈ s.filter (fun k => lseriesWeight (L k) = W),
        ((P k).eval (c ^ (q ^ j)) / (Q k).eval (c ^ (q ^ j)))
          * (evalSeries (atLrPaper q ω (L k)) c) ^ (q ^ j) = 0 := by
  have hS : ∀ k ∈ s, SuperEntire (atLrPaper q ω (L k) * ω ^ (W - lseriesWeight (L k))) :=
    fun k hk => (superEntire_atLrPaper q hq hω hωse (hL k hk) (hLse k hk)).mul (hωse.pow _)
  have hmain := specialise_sum_div s P Q
    (fun k => atLrPaper q ω (L k) * ω ^ (W - lseriesWeight (L k))) (c ^ (q ^ j)) hS hQc h
  rw [Finset.sum_filter]
  have hkey : ∀ k ∈ s,
      (if lseriesWeight (L k) = W then
          ((P k).eval (c ^ (q ^ j)) / (Q k).eval (c ^ (q ^ j)))
            * (evalSeries (atLrPaper q ω (L k)) c) ^ (q ^ j)
        else 0)
      = ((P k).eval (c ^ (q ^ j)) / (Q k).eval (c ^ (q ^ j)))
          * evalSeries (atLrPaper q ω (L k) * ω ^ (W - lseriesWeight (L k)))
              (c ^ (q ^ j)) := by
    intro k hk
    by_cases hkw : lseriesWeight (L k) = W
    · rw [if_pos hkw,
        evalSeries_mul (superEntire_atLrPaper q hq hω hωse (hL k hk) (hLse k hk)) (hωse.pow _) _,
        evalSeries_pow hωse _ _, hkw, Nat.sub_self, pow_zero, mul_one,
        evalSeries_atLrPaper_frobenius_pow_of_ne q hq hω hωse (hne k hk) (hL k hk) (hLse k hk)
          (hs k hk _ (List.getLast_mem (hne k hk))) hc j]
    · rw [if_neg hkw]
      have hlt : lseriesWeight (L k) < W := lt_of_le_of_ne (hW k hk) hkw
      rw [evalSeries_mul (superEntire_atLrPaper q hq hω hωse (hL k hk) (hLse k hk)) (hωse.pow _) _,
        evalSeries_pow hωse _ _, hc j hj,
        zero_pow (by omega : W - lseriesWeight (L k) ≠ 0), mul_zero, mul_zero]
  rw [Finset.sum_congr rfl hkey]
  exact hmain

/-- **Step 2 of the paper for the Anderson–Thakur period datum** `Ω = μ·Ω̃` and the point
`c = θ`: the relation between `L`-series of the dual `t`-motive, specialised at `θ^{q^j}`,
becomes a relation between the `q^j`-th powers of the values of the maximal-weight `L`-series. -/
theorem step2_specialisation_period (θ : K) (d : ℤ) (hd : 1 ≤ d)
    (hθ : Valued.v θ = WithZero.exp d) (hq : 2 ≤ q) {μ : K}
    (hμ : Valued.v μ ≤ WithZero.exp (-1))
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (L : ι → List (ℕ × PowerSeries K))
    (hne : ∀ k ∈ s, L k ≠ [])
    (hL : ∀ k ∈ s, ∀ x ∈ L k, IsSmall x.2)
    (hLse : ∀ k ∈ s, ∀ x ∈ L k, SuperEntire x.2)
    (hs : ∀ k ∈ s, ∀ x ∈ L k, 1 ≤ x.1)
    (P Q : ι → Polynomial K) (W : ℕ) (hW : ∀ k ∈ s, lseriesWeight (L k) ≤ W) {j : ℕ} (hj : 1 ≤ j)
    (hQc : ∀ k ∈ s, (Q k).eval (θ ^ (q ^ j)) ≠ 0)
    (h : ∑ k ∈ s, ((P k * ∏ l ∈ s.erase k, Q l : Polynomial K) : PowerSeries K)
          * (atLrPaper q (PowerSeries.C μ * atOmega q θ) (L k)
              * (PowerSeries.C μ * atOmega q θ) ^ (W - lseriesWeight (L k))) = 0) :
    ∑ k ∈ s.filter (fun k => lseriesWeight (L k) = W),
        ((P k).eval (θ ^ (q ^ j)) / (Q k).eval (θ ^ (q ^ j)))
          * (evalSeries (atLrPaper q (PowerSeries.C μ * atOmega q θ) (L k)) θ) ^ (q ^ j) = 0 :=
  step2_specialisation q hq (isSmall_periodDatum q θ d hd hθ hq hμ)
    ((SuperEntire.C μ).mul (superEntire_atOmega q θ d hd hθ hq))
    (fun _ hk => evalSeries_C_mul_atOmega_frobenius_orbit q θ d hd hθ hq μ hk)
    s L hne hL hLse hs P Q W hW hj hQc h

end step2

end ZagierHoffmanPositiveChar
