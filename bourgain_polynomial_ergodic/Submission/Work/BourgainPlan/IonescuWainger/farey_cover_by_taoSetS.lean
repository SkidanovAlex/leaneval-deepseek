import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.TaoDefs

/-!
# The Farey cover: Tao's major-arc set `S` covers the classical arcs (Lemma `iwac`(i))

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066.
With `S = taoSetS ρ N = {∏_{p ≤ N^{ρ/2}} p^{⌊log N/log p⌋}} ∪ {p^{⌊log N/log p⌋} : N^{ρ/2} < p ≤ N}`
we show that for `N ≥ 2^{⌊2/ρ⌋+1}` every `1 ≤ q ≤ N` divides the product of at most
`⌊2/ρ⌋ + 1` elements of `S`.

The proof is elementary, and is exactly the argument in the paper:

* a prime power `p^k` with `p^k ≤ N` (and `k ≥ 1`) satisfies
  `k ≤ ⌊log N / log p⌋` (helper `le_floor_log_div_log`), the exponent occurring in `S`;
* every prime power dividing `q` is therefore either covered by the single element
  `smallPrimePowerProd ρ N` (the primes `p ≤ N^{ρ/2}`, helper `pow_dvd_smallPrimePowerProd`)
  or else by the individual element `p^{⌊log N/log p⌋}` (the primes `N^{ρ/2} < p ≤ N`);
* at most `⌊2/ρ⌋` primes `p > N^{ρ/2}` divide `q`: their product exceeds
  `(N^{ρ/2})^{m}` and is at most `q ≤ N`, so `m < 2/ρ`.

So the covering set is `{smallPrimePowerProd ρ N} ∪ {p^{⌊log N/log p⌋} : p > N^{ρ/2}, p ∣ q}`,
which has at most `⌊2/ρ⌋ + 1` elements.  The divisibility is checked through the criterion
`Nat.dvd_iff_prime_pow_dvd_dvd`: it suffices that every prime power `p^k` dividing `q` divides the
product, and each such `p^k` divides one of the two kinds of elements of `S` above.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-- **Exponent bound.**  If `p` is prime and `p ^ k ≤ N`, then `k` is at most the exponent
`⌊log N / log p⌋` attached to the prime `p` in Tao's set `taoSetS ρ N`. -/
lemma le_floor_log_div_log {N p k : ℕ} (hp : Nat.Prime p) (h : p ^ k ≤ N) :
    k ≤ ⌊Real.log N / Real.log p⌋₊ := by
  apply Nat.le_floor
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by linarith)
  have h1 : Real.log ((p : ℝ) ^ k) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast h)
  rw [Real.log_pow] at h1
  exact (le_div_iff₀ hlogp).mpr h1

/-- The `p`-th element of the "large" part of `taoSetS ρ N`: for a prime `N^{ρ/2} < p ≤ N` the
number `p ^ ⌊log N / log p⌋` belongs to `largePrimePowers ρ N`. -/
lemma largePrimePowers_mem {ρ : ℝ} {N p : ℕ} (hp : Nat.Prime p)
    (hlow : ⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1 ≤ p) (hhigh : p ≤ N) :
    p ^ ⌊Real.log N / Real.log p⌋₊ ∈ largePrimePowers ρ N := by
  rw [largePrimePowers, Finset.mem_image]
  refine ⟨p, ?_, rfl⟩
  rw [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨hlow, hhigh⟩, hp⟩

/-- **Small primes are covered by `smallPrimePowerProd`.**  If `p ≤ N^{ρ/2}` is prime and
`p ^ k ≤ N`, then `p ^ k` divides the single element `smallPrimePowerProd ρ N` of `taoSetS ρ N`. -/
lemma pow_dvd_smallPrimePowerProd {ρ : ℝ} {N p k : ℕ} (hp : Nat.Prime p)
    (hpN : (p : ℝ) ≤ (N : ℝ) ^ (ρ / 2)) (hkN : p ^ k ≤ N) :
    p ^ k ∣ smallPrimePowerProd ρ N := by
  have hke : k ≤ ⌊Real.log N / Real.log p⌋₊ := le_floor_log_div_log hp hkN
  have hmem : p ∈ (Finset.Icc 2 ⌊(N : ℝ) ^ (ρ / 2)⌋₊).filter Nat.Prime := by
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hp.two_le, Nat.le_floor hpN⟩, hp⟩
  rw [smallPrimePowerProd]
  exact dvd_trans (pow_dvd_pow p hke) (Finset.dvd_prod_of_mem _ hmem)

/-- **The classical Farey arcs are covered by the major arcs of depth `k = ⌊2/ρ⌋ + 1` of Tao's set** (Tao, arXiv:2008.05066, Lemma `iwac`(i)): if `N ≥ 2^{⌊2/ρ⌋+1}` then every `1 ≤ q ≤ N` divides the product of at most `⌊2/ρ⌋ + 1` elements of `taoSetS ρ N` (Tao's set `S = {∏_{p ≤ N^{ρ/2}} p^{⌊log N/log p⌋}} ∪ {p^{⌊log N/log p⌋} : N^{ρ/2} < p ≤ N}`). Proof: write `q`'s prime factorisation; at most `⌊2/ρ⌋` of its primes exceed `N^{ρ/2}` (from `p^r ≤ q ≤ N` one gets `r < 2/ρ`), and each `p^{a}` divides the corresponding element `p^{⌊log N/log p⌋}`; the product of the remaining prime powers divides `∏_{p ≤ N^{ρ/2}} p^{⌊log N/log p⌋}`. -/
theorem farey_cover_by_taoSetS (ρ : ℝ) (hρ : 0 < ρ) (N : ℕ)
    (hN : 2 ^ (⌊2 / ρ⌋₊ + 1) ≤ N) :
    ∀ q : ℕ, 1 ≤ q → q ≤ N →
      ∃ A : Finset ℕ, A ⊆ Work.BourgainPlan.IonescuWainger.taoSetS ρ N ∧
        A.card ≤ ⌊2 / ρ⌋₊ + 1 ∧ q ∣ ∏ a ∈ A, a := by
  intro q hq1 hqN
  -- from the hypothesis we get `N ≥ 2`
  have hN2 : 2 ≤ N := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (⌊2 / ρ⌋₊ + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ N := hN
  have hqpos : 0 < q := hq1
  have hq0 : q ≠ 0 := by omega
  -- the exponent of the prime `p` in Tao's set, and the "small" element of the set
  set e : ℕ → ℕ := fun p => ⌊Real.log N / Real.log p⌋₊ with he
  set c : ℕ := smallPrimePowerProd ρ N with hc
  -- the primes `> N^{ρ/2}` dividing `q`
  set L : Finset ℕ := q.primeFactors.filter (fun p => ¬ ((p : ℝ) ≤ (N : ℝ) ^ (ρ / 2))) with hL
  refine ⟨insert c (L.image fun p => p ^ e p), ?_, ?_, ?_⟩
  · -- the covering set is contained in `taoSetS ρ N`
    intro a ha
    rw [Finset.mem_insert] at ha
    rcases ha with rfl | ha
    · rw [hc, taoSetS]
      exact Finset.mem_insert_self _ _
    · rw [Finset.mem_image] at ha
      obtain ⟨p, hpL, rfl⟩ := ha
      rw [hL, Finset.mem_filter] at hpL
      obtain ⟨hpq, hpnot⟩ := hpL
      have hpprime : Nat.Prime p := (Nat.mem_primeFactors.mp hpq).1
      have hpdvd : p ∣ q := (Nat.mem_primeFactors.mp hpq).2.1
      have hp_le_N : p ≤ N := le_trans (Nat.le_of_dvd hqpos hpdvd) hqN
      have hlow : ⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1 ≤ p := by
        have hx : ((⌊(N : ℝ) ^ (ρ / 2)⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) ^ (ρ / 2) :=
          Nat.floor_le (by positivity)
        have hlt : ((⌊(N : ℝ) ^ (ρ / 2)⌋₊ : ℕ) : ℝ) < (p : ℝ) :=
          lt_of_le_of_lt hx (lt_of_not_ge hpnot)
        exact Nat.succ_le_of_lt (by exact_mod_cast hlt)
      rw [taoSetS, he]
      exact Finset.mem_insert_of_mem (largePrimePowers_mem hpprime hlow hp_le_N)
  · -- the covering set has at most `⌊2/ρ⌋ + 1` elements
    have hLsub : L ⊆ q.primeFactors := by
      rw [hL]; exact Finset.filter_subset _ _
    have hLcard : L.card ≤ ⌊2 / ρ⌋₊ := by
      rcases L.eq_empty_or_nonempty with hemp | hne
      · rw [hemp]; simp
      · -- the product of the primes of `L` is at most `q ≤ N`, while each of them exceeds
        -- `N^{ρ/2}`; hence `(N^{ρ/2})^{|L|} < N`, so `|L| < 2/ρ`
        have hprod_le : ∏ p ∈ L, p ≤ N := by
          have hdvd1 : ∏ p ∈ L, p ∣ ∏ p ∈ q.primeFactors, p :=
            Finset.prod_dvd_prod_of_subset L q.primeFactors (fun p => p) hLsub
          exact le_trans (Nat.le_of_dvd hqpos (dvd_trans hdvd1 (Nat.prod_primeFactors_dvd q))) hqN
        have hlt : ((N : ℝ) ^ (ρ / 2)) ^ L.card < ((∏ p ∈ L, p : ℕ) : ℝ) := by
          rw [Nat.cast_prod, ← Finset.prod_const]
          refine Finset.prod_lt_prod_of_nonempty₀ (fun p _ => Real.rpow_pos_of_pos (by positivity) _)
            (fun p hp => ?_) hne
          rw [hL, Finset.mem_filter] at hp
          exact lt_of_not_ge hp.2
        have hlt' : ((N : ℝ) ^ (ρ / 2)) ^ L.card < (N : ℝ) :=
          lt_of_lt_of_le hlt (by exact_mod_cast hprod_le)
        have hcast : ((N : ℝ) ^ (ρ / 2)) ^ L.card = (N : ℝ) ^ ((ρ / 2) * (L.card : ℝ)) := by
          rw [Real.rpow_mul (by positivity), Real.rpow_natCast]
        have hgoal : (N : ℝ) ^ ((ρ / 2) * (L.card : ℝ)) < (N : ℝ) ^ (1 : ℝ) := by
          rw [Real.rpow_one, ← hcast]
          exact hlt'
        have h1N : (1 : ℝ) < N := by exact_mod_cast hN2
        have hexp : (ρ / 2) * (L.card : ℝ) < 1 := (Real.rpow_lt_rpow_left_iff h1N).mp hgoal
        have hm : (L.card : ℝ) < 2 / ρ := by
          have hρ2 : 0 < ρ / 2 := by linarith
          have hkey : (L.card : ℝ) * (ρ / 2) < 1 := by nlinarith [hexp]
          have h2 := (lt_div_iff₀ hρ2).mpr hkey
          rwa [one_div, inv_div] at h2
        exact Nat.le_floor (le_of_lt hm)
    calc (insert c (L.image fun p => p ^ e p)).card
        ≤ (L.image fun p => p ^ e p).card + 1 := Finset.card_insert_le _ _
      _ ≤ L.card + 1 := by have := Finset.card_image_le (s := L) (f := fun p => p ^ e p); omega
      _ ≤ ⌊2 / ρ⌋₊ + 1 := by omega
  · -- divisibility: every prime power dividing `q` divides an element of the covering set
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p k hp hpk
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    have hk0 : k ≠ 0 := by omega
    have hpdvd : p ∣ q := dvd_trans (dvd_pow_self p hk0) hpk
    have hpq : p ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvd, hq0⟩
    have hpk_le : p ^ k ≤ N := le_trans (Nat.le_of_dvd hqpos hpk) hqN
    have hke : k ≤ e p := by
      rw [he]
      exact le_floor_log_div_log hp hpk_le
    by_cases hsmall : (p : ℝ) ≤ (N : ℝ) ^ (ρ / 2)
    · -- `p` is a small prime: `p ^ k` divides the single element `c`
      have hdiv : p ^ k ∣ c := by
        rw [hc]
        exact pow_dvd_smallPrimePowerProd hp hsmall hpk_le
      exact dvd_trans hdiv (Finset.dvd_prod_of_mem _ (Finset.mem_insert_self _ _))
    · -- `p` is a large prime: `p ^ k` divides `p ^ e p`, an element of the set
      have hmemL : p ∈ L := by
        rw [hL, Finset.mem_filter]
        exact ⟨hpq, hsmall⟩
      have hmemA : p ^ e p ∈ L.image (fun p => p ^ e p) :=
        Finset.mem_image.mpr ⟨p, hmemL, rfl⟩
      exact dvd_trans (pow_dvd_pow p hke)
        (Finset.dvd_prod_of_mem _ (Finset.mem_insert_of_mem hmemA))

end Work.BourgainPlan.IonescuWainger
