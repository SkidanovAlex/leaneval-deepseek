import Submission.ZagierHoffmanProof.LSeriesDepth
import Submission.ZagierHoffmanProof.SuperOmega
import Submission.Commons.Topology.Algebra.Valued.v_tsum_le_of_forall_le

/-!
# Chang's Lemma 5.3.1: the `L`-series converges everywhere

`SuperOmega.lean` proves that the depth-one `L`-series of a super-entire small series is
super-entire.  This file proves the general depth-`p` statement for the cutoff `L`-series
`atLrFold`/`atLrcut` of `LSeriesDepth.lean`:

  ★★★ `superEntire_atLrcut_bound` — if `ω` and the factors `Q` are small and super-entire, then
  the cutoff `L`-series has coefficients decaying like `exp (a - M·n)` for *every* `M` and with a
  constant `a` **uniform in the cutoff `N`**;
  ★★★ `superEntire_atLrcut`, `superEntire_atLr` — Chang's Lemma 5.3.1 (all depths):
  `𝓛(𝔰;Q) ∈ ε`.

The proof is the same observation as in depth one: twisting a coefficient to its `q^k`-th power
*decreases* its valuation (the coefficients are small), so the twisted factors are dominated
termwise by the untwisted ones, and super-entireness is closed under products and infinite sums.
The uniformity in the cutoff is what makes the induction go through (and it is also what the
`t`-motive induction of the ABP criterion needs).

## Main results

* `IsSmall.frobTwist_coeff_le` — twisting a small series only decreases the coefficient
  valuations.
* ★★★ `superEntire_atLrcut_bound` — the uniform bound for `atLrcut`.
* ★★★ `superEntire_atLrcut`, `superEntire_atLr`, `superEntire_atLrPaper` — `𝓛 ∈ ε`.
-/

set_option autoImplicit false
open Filter Polynomial RatFunc
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] [Valued K ℤᵐ⁰] [CompleteSpace K] [NonarchimedeanAddGroup K]

section basic

variable (q : ℕ) [FrobPow K q]

/-- The coefficients of a Frobenius twist of a small series are bounded by `exp (-(q^k))`. -/
lemma IsSmall.frobTwist_coeff_le (hq : 2 ≤ q) {F : PowerSeries K} (hF : IsSmall F) (k m : ℕ) :
    Valued.v (PowerSeries.coeff m (frobTwist (R := K) (p := q) k F))
      ≤ WithZero.exp (-(((q ^ k : ℕ)) : ℤ)) := by
  rw [frobTwist_coeff, map_pow]
  calc (Valued.v (PowerSeries.coeff m F)) ^ (q ^ k)
      ≤ (WithZero.exp (-1)) ^ (q ^ k) := pow_le_pow_left' (hF m) _
    _ = WithZero.exp (-1 * (((q ^ k : ℕ)) : ℤ)) := expmul (-1) (q ^ k)
    _ = WithZero.exp (-(((q ^ k : ℕ)) : ℤ)) := by rw [neg_one_mul]

/-- Twisting a small series decreases (weakly) every coefficient valuation. -/
lemma IsSmall.frobTwist_coeff_le_self (hq : 2 ≤ q) {F : PowerSeries K} (hF : IsSmall F)
    (k m : ℕ) :
    Valued.v (PowerSeries.coeff m (frobTwist (R := K) (p := q) k F))
      ≤ Valued.v (PowerSeries.coeff m F) := by
  rw [frobTwist_coeff, map_pow]
  simpa using pow_le_pow_of_le_one bot_le (le_trans (hF m) exp_neg_one_le_one)
    (Nat.one_le_pow k q (by omega))

end basic

section main

variable (q : ℕ) [FrobPow K q]

/-- The coefficient bound for a single term of the recursion: a twisted small factor times a
super-entire factor enjoys the product bound. -/
lemma coeff_twist_mul_le (hq : 2 ≤ q) {F : PowerSeries K} (hF : IsSmall F) (M : ℕ)
    {aF : ℤ} (haF : ∀ m : ℕ, Valued.v (PowerSeries.coeff m F)
      ≤ WithZero.exp (aF - (M : ℤ) * (m : ℤ)))
    {g : ℕ → PowerSeries K} {ar : ℤ} (har : ∀ j m : ℕ, Valued.v (PowerSeries.coeff m (g j))
      ≤ WithZero.exp (ar - (M : ℤ) * (m : ℤ))) (N i n : ℕ) :
    Valued.v (PowerSeries.coeff n (frobTwist (R := K) (p := q) (N + i) F * g i))
      ≤ WithZero.exp (aF + ar - (M : ℤ) * (n : ℤ)) := by
  rw [PowerSeries.coeff_mul]
  refine Valued.v.map_sum_le (fun p hp => ?_)
  rw [Valuation.map_mul]
  have hp' : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
  have h1 : Valued.v (PowerSeries.coeff p.1
      (frobTwist (R := K) (p := q) (N + i) F)) ≤ WithZero.exp (aF - (M : ℤ) * (p.1 : ℤ)) :=
    le_trans (IsSmall.frobTwist_coeff_le_self q hq hF (N + i) p.1) (haF p.1)
  calc Valued.v (PowerSeries.coeff p.1 (frobTwist (R := K) (p := q) (N + i) F))
        * Valued.v (PowerSeries.coeff p.2 (g i))
      ≤ WithZero.exp (aF - (M : ℤ) * (p.1 : ℤ))
          * WithZero.exp (ar - (M : ℤ) * (p.2 : ℤ)) := mul_le_mul' h1 (har i p.2)
    _ = WithZero.exp ((aF - (M : ℤ) * (p.1 : ℤ)) + (ar - (M : ℤ) * (p.2 : ℤ))) := by
        rw [← WithZero.exp_add]
    _ = WithZero.exp (aF + ar - (M : ℤ) * (n : ℤ)) := by
        rw [← hp']
        congr 1
        push_cast
        ring

/-- The defining family of the recursion is summable: its `i`-th term is bounded by
`exp (ar - q^(N+i))`. -/
lemma summable_twist_mul (hq : 2 ≤ q) {F : PowerSeries K} (hF : IsSmall F) (M : ℕ)
    {g : ℕ → PowerSeries K} {ar : ℤ} (har : ∀ j m : ℕ, Valued.v (PowerSeries.coeff m (g j))
      ≤ WithZero.exp (ar - (M : ℤ) * (m : ℤ))) (N n : ℕ) :
    Summable fun i : ℕ => PowerSeries.coeff n
      (frobTwist (R := K) (p := q) (N + i) F * g i) := by
  refine Commons.Topology.Algebra.Valued.summable_of_tendsto_v_zero (fun k => ?_)
  rw [Filter.eventually_atTop]
  refine ⟨(ar - k).natAbs + 1, fun i hi => ?_⟩
  rw [PowerSeries.coeff_mul]
  have hbound : Valued.v (∑ p ∈ Finset.antidiagonal n,
      PowerSeries.coeff p.1 (frobTwist (R := K) (p := q) (N + i) F)
        * PowerSeries.coeff p.2 (g i))
      ≤ WithZero.exp (-(((q ^ (N + i) : ℕ)) : ℤ) + ar) := by
    refine Valued.v.map_sum_le (fun p hp => ?_)
    rw [Valuation.map_mul]
    have h1 := IsSmall.frobTwist_coeff_le q hq hF (N + i) p.1
    have h2 : Valued.v (PowerSeries.coeff p.2 (g i)) ≤ WithZero.exp ar := by
      refine le_trans (har i p.2) (WithZero.exp_le_exp.mpr ?_)
      have : (0 : ℤ) ≤ (M : ℤ) * (p.2 : ℤ) := by positivity
      omega
    calc Valued.v (PowerSeries.coeff p.1 (frobTwist (R := K) (p := q) (N + i) F))
          * Valued.v (PowerSeries.coeff p.2 (g i))
        ≤ WithZero.exp (-(((q ^ (N + i) : ℕ)) : ℤ)) * WithZero.exp ar := mul_le_mul' h1 h2
      _ = WithZero.exp (-(((q ^ (N + i) : ℕ)) : ℤ) + ar) := by rw [← WithZero.exp_add]
  refine lt_of_le_of_lt hbound (WithZero.exp_lt_exp.mpr ?_)
  have h1 : N + i < q ^ (N + i) := Nat.lt_pow_self (by omega : 1 < q)
  have h2 : (ar - k).natAbs + 1 ≤ i := by omega
  have h3 : ((ar - k).natAbs : ℤ) < ((q ^ (N + i) : ℕ) : ℤ) := by
    have h4 : (ar - k).natAbs < q ^ (N + i) := by
      calc (ar - k).natAbs < (ar - k).natAbs + 1 := Nat.lt_succ_self _
        _ ≤ i := h2
        _ ≤ N + i := by omega
        _ < q ^ (N + i) := h1
    exact_mod_cast h4
  have h5 : ar - k ≤ ((ar - k).natAbs : ℤ) := Int.le_natAbs
  linarith

/-- **The uniform-in-the-cutoff super-entireness of the `L`-series.**  For every `M` the
coefficients of `atLrcut q ω L N` decay at least as fast as `exp (-M·n)`, with a constant
independent of the cutoff `N`. -/
theorem superEntire_atLrcut_bound (hq : 2 ≤ q) {ω : PowerSeries K} (hω : IsSmall ω)
    (hωse : SuperEntire ω) (M : ℕ) :
    ∀ (L : List (ℕ × PowerSeries K)), (∀ x ∈ L, IsSmall x.2) → (∀ x ∈ L, SuperEntire x.2) →
      ∃ a : ℤ, ∀ (N n : ℕ),
        Valued.v (PowerSeries.coeff n (atLrcut q ω L N))
          ≤ WithZero.exp (a - (M : ℤ) * (n : ℤ)) := by
  intro L
  induction L with
  | nil =>
    intro _ _
    refine ⟨0, fun N n => ?_⟩
    rw [atLrcut_nil, PowerSeries.coeff_one]
    by_cases h : n = 0
    · subst h
      rw [if_pos rfl, map_one]
      simp
    · rw [if_neg h, map_zero]
      exact bot_le
  | cons a rest ih =>
    obtain ⟨s, Q⟩ := a
    intro hL hLse
    have hQ : IsSmall Q := hL (s, Q) (by simp)
    have hQse : SuperEntire Q := hLse (s, Q) (by simp)
    have hrest : ∀ x ∈ rest, IsSmall x.2 := fun x hx => hL x (List.mem_cons_of_mem _ hx)
    have hrestse : ∀ x ∈ rest, SuperEntire x.2 := fun x hx => hLse x (List.mem_cons_of_mem _ hx)
    obtain ⟨ar, har⟩ := ih hrest hrestse
    have hFsmall : IsSmall (ω ^ s * Q) := IsSmall.pow_mul hω hQ s
    obtain ⟨aF, haF⟩ := ((hωse.pow s).mul hQse) M
    refine ⟨aF + ar, fun N n => ?_⟩
    rw [atLrcut_cons, PowerSeries.coeff_mk]
    refine Commons.Topology.Algebra.Valued.v_tsum_le_of_forall_le
      (summable_twist_mul q hq hFsmall M
        (fun j m => har (N + j + 1) m) N n) (fun i => ?_)
    exact coeff_twist_mul_le q hq hFsmall M haF (fun j m => har (N + j + 1) m) N i n

end main

section conclude

variable (q : ℕ) [FrobPow K q]

/-- **Chang's Lemma 5.3.1 for the cutoff `L`-series**: `atLrcut q ω L N ∈ ε`. -/
theorem superEntire_atLrcut (hq : 2 ≤ q) {ω : PowerSeries K} (hω : IsSmall ω)
    (hωse : SuperEntire ω) {L : List (ℕ × PowerSeries K)}
    (hL : ∀ x ∈ L, IsSmall x.2) (hLse : ∀ x ∈ L, SuperEntire x.2) (N : ℕ) :
    SuperEntire (atLrcut q ω L N) := fun M =>
  let ⟨a, ha⟩ := superEntire_atLrcut_bound q hq hω hωse M L hL hLse
  ⟨a, fun n => ha N n⟩

/-- **Chang's Lemma 5.3.1**: the `L`-series `𝓛(𝔰;Q) = atLr q ω L` lies in `ε`. -/
theorem superEntire_atLr (hq : 2 ≤ q) {ω : PowerSeries K} (hω : IsSmall ω)
    (hωse : SuperEntire ω) {L : List (ℕ × PowerSeries K)}
    (hL : ∀ x ∈ L, IsSmall x.2) (hLse : ∀ x ∈ L, SuperEntire x.2) :
    SuperEntire (atLr q ω L) :=
  superEntire_atLrcut q hq hω hωse hL hLse 0

/-- Chang's `L`-series in the paper's ordering convention is super-entire. -/
theorem superEntire_atLrPaper (hq : 2 ≤ q) {ω : PowerSeries K} (hω : IsSmall ω)
    (hωse : SuperEntire ω) {L : List (ℕ × PowerSeries K)}
    (hL : ∀ x ∈ L, IsSmall x.2) (hLse : ∀ x ∈ L, SuperEntire x.2) :
    SuperEntire (atLrPaper q ω L) := by
  rw [atLrPaper]
  exact superEntire_atLr q hq hω hωse (fun x hx => hL x (List.mem_reverse.mp hx))
    (fun x hx => hLse x (List.mem_reverse.mp hx))

/-- **The entries of the rigid analytic trivialisation matrix lie in `ε`**: the products
`𝓛(𝔰_{≥j};Q)·Ω^{w - w_j}` of the `L`-series with powers of the period function. -/
theorem superEntire_atLr_mul_pow (hq : 2 ≤ q) {ω : PowerSeries K} (hω : IsSmall ω)
    (hωse : SuperEntire ω) {L : List (ℕ × PowerSeries K)}
    (hL : ∀ x ∈ L, IsSmall x.2) (hLse : ∀ x ∈ L, SuperEntire x.2) (s : ℕ) :
    SuperEntire (atLr q ω L * ω ^ s) :=
  (superEntire_atLr q hq hω hωse hL hLse).mul (hωse.pow s)

end conclude

end ZagierHoffmanPositiveChar
