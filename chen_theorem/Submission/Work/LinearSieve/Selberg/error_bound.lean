import Mathlib
import Submission.Work.ChenPlan.LinearSieve.basic

/-!
# The Selberg `Λ²` error term

If the `Λ²` weights `w` vanish for `d ≥ ξ` and satisfy `|w d| ≤ 1`, then the error sum of the `Λ²`
sieve is dominated by the truncated remainder sum, in which only the divisors `d < ξ²` contribute
and the `d`-th term carries Selberg's weight `3^{ω(d)}`.

The two ingredients are

* for `d ≥ ξ²` the coefficient `λ_d = Σ_{lcm(d1,d2)=d} w d1 w d2` vanishes: a non-zero term would
  force `d = lcm d1 d2 < ξ²`;
* a squarefree `d` (in particular every `d ∣ s.prodPrimes`) has at most `3^{ω(d)}` pairs of divisors
  `(d1, d2)` with `lcm d1 d2 = d`, since each prime `p ∣ d` has to divide `d1`, `d2`, or both.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.LinearSieve.Selberg

/-- The three possible ways in which a prime of `d` can be distributed among the pair `(d1, d2)`. -/
private def triState : Finset (Bool × Bool) := {(true, true), (true, false), (false, true)}

private lemma triState_card : triState.card = 3 := by decide

/-- If `a, b` are natural numbers below `ξ ≥ 0` with `lcm a b ≠ 0`, then `lcm a b < ξ ^ 2`. -/
private lemma lcm_cast_lt_sq {ξ : ℝ} (hξ : 0 ≤ ξ) {a b : ℕ}
    (ha : (a : ℝ) < ξ) (hb : (b : ℝ) < ξ) (hne : a.lcm b ≠ 0) :
    ((a.lcm b : ℕ) : ℝ) < ξ ^ 2 := by
  have ha0 : a ≠ 0 := fun h => hne (Nat.lcm_eq_zero_iff.mpr (Or.inl h))
  have hb0 : b ≠ 0 := fun h => hne (Nat.lcm_eq_zero_iff.mpr (Or.inr h))
  have ha1 : 0 < a := Nat.pos_of_ne_zero ha0
  have hb1 : 0 < b := Nat.pos_of_ne_zero hb0
  have h1 : ((a.lcm b : ℕ) : ℝ) ≤ (a : ℝ) * (b : ℝ) := by
    have := Nat.lcm_le_mul ha1 hb1
    exact_mod_cast this
  have h2 : (a : ℝ) * (b : ℝ) < ξ * ξ := by
    have hbpos : (0 : ℝ) < b := by exact_mod_cast hb1
    have h3 : (a : ℝ) * (b : ℝ) < ξ * (b : ℝ) := mul_lt_mul_of_pos_right ha hbpos
    have h4 : ξ * (b : ℝ) ≤ ξ * ξ := mul_le_mul_of_nonneg_left (le_of_lt hb) hξ
    linarith
  calc ((a.lcm b : ℕ) : ℝ) ≤ (a : ℝ) * (b : ℝ) := h1
    _ < ξ * ξ := h2
    _ = ξ ^ 2 := by ring

/-- A squarefree `d` has at most `3 ^ ω(d)` pairs of divisors `(d1, d2)` with `lcm d1 d2 = d`. -/
private theorem card_lcm_pairs_le (d : ℕ) (hd : Squarefree d) :
    ((d.divisors ×ˢ d.divisors).filter (fun q : ℕ × ℕ => q.1.lcm q.2 = d)).card
      ≤ 3 ^ d.primeFactors.card := by
  have hdne : d ≠ 0 := hd.ne_zero
  set φ : ℕ × ℕ → ((a : ℕ) → a ∈ d.primeFactors → Bool × Bool) :=
    fun q a _ => (a ∣ q.1, a ∣ q.2) with hφ
  have hmem : Set.MapsTo φ
      ↑((d.divisors ×ˢ d.divisors).filter (fun q : ℕ × ℕ => q.1.lcm q.2 = d))
      ↑(d.primeFactors.pi (fun _ => triState)) := by
    intro q hq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hq
    obtain ⟨⟨hd1, hd2⟩, hlcm⟩ := hq
    change φ q ∈ d.primeFactors.pi (fun _ => triState)
    rw [Finset.mem_pi]
    intro a ha
    show (decide (a ∣ q.1), decide (a ∣ q.2)) ∈ triState
    have hp : Nat.Prime a := (Nat.mem_primeFactors.mp ha).1
    have had : a ∣ d := (Nat.mem_primeFactors.mp ha).2.1
    rw [← hlcm] at had
    rcases (hp.dvd_lcm.mp had) with h | h
    · by_cases h2 : a ∣ q.2 <;> simp [triState, h, h2]
    · by_cases h1 : a ∣ q.1 <;> simp [triState, h1, h]
  have hinj : Set.InjOn φ
      ↑((d.divisors ×ˢ d.divisors).filter (fun q : ℕ × ℕ => q.1.lcm q.2 = d)) := by
    intro q hq q' hq' heq
    obtain ⟨d1, d2⟩ := q
    obtain ⟨d1', d2'⟩ := q'
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hq hq'
    obtain ⟨⟨hd1, hd2⟩, hlcm⟩ := hq
    obtain ⟨⟨hd1', hd2'⟩, hlcm'⟩ := hq'
    have hbits1 : ∀ a ∈ d.primeFactors, (a ∣ d1) ↔ (a ∣ d1') := by
      intro a ha
      have h := congrArg Prod.fst (congrFun (congrFun heq a) ha)
      simpa [hφ] using h
    have hbits2 : ∀ a ∈ d.primeFactors, (a ∣ d2) ↔ (a ∣ d2') := by
      intro a ha
      have h := congrArg Prod.snd (congrFun (congrFun heq a) ha)
      simpa [hφ] using h
    have hdvd1 : d1 ∣ d := (Nat.mem_divisors.mp hd1).1
    have hdvd1' : d1' ∣ d := (Nat.mem_divisors.mp hd1').1
    have hdvd2 : d2 ∣ d := (Nat.mem_divisors.mp hd2).1
    have hdvd2' : d2' ∣ d := (Nat.mem_divisors.mp hd2').1
    have hd1ne : d1 ≠ 0 := ne_zero_of_dvd_ne_zero hdne hdvd1
    have hd1'ne : d1' ≠ 0 := ne_zero_of_dvd_ne_zero hdne hdvd1'
    have hd2ne : d2 ≠ 0 := ne_zero_of_dvd_ne_zero hdne hdvd2
    have hd2'ne : d2' ≠ 0 := ne_zero_of_dvd_ne_zero hdne hdvd2'
    have hfac1 : d1.primeFactors = d1'.primeFactors := by
      apply Finset.ext
      intro p
      rw [Nat.mem_primeFactors_of_ne_zero hd1ne, Nat.mem_primeFactors_of_ne_zero hd1'ne]
      constructor
      · rintro ⟨hp, hpd⟩
        have hpmem : p ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpd.trans hdvd1, hdne⟩
        exact ⟨hp, (hbits1 p hpmem).mp hpd⟩
      · rintro ⟨hp, hpd⟩
        have hpmem : p ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpd.trans hdvd1', hdne⟩
        exact ⟨hp, (hbits1 p hpmem).mpr hpd⟩
    have hfac2 : d2.primeFactors = d2'.primeFactors := by
      apply Finset.ext
      intro p
      rw [Nat.mem_primeFactors_of_ne_zero hd2ne, Nat.mem_primeFactors_of_ne_zero hd2'ne]
      constructor
      · rintro ⟨hp, hpd⟩
        have hpmem : p ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpd.trans hdvd2, hdne⟩
        exact ⟨hp, (hbits2 p hpmem).mp hpd⟩
      · rintro ⟨hp, hpd⟩
        have hpmem : p ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpd.trans hdvd2', hdne⟩
        exact ⟨hp, (hbits2 p hpmem).mpr hpd⟩
    have hd1eq : d1 = d1' := by
      rw [← Nat.prod_primeFactors_of_squarefree (Squarefree.squarefree_of_dvd hdvd1 hd),
        ← Nat.prod_primeFactors_of_squarefree (Squarefree.squarefree_of_dvd hdvd1' hd), hfac1]
    have hd2eq : d2 = d2' := by
      rw [← Nat.prod_primeFactors_of_squarefree (Squarefree.squarefree_of_dvd hdvd2 hd),
        ← Nat.prod_primeFactors_of_squarefree (Squarefree.squarefree_of_dvd hdvd2' hd), hfac2]
    rw [hd1eq, hd2eq]
  have hcard := Finset.card_le_card_of_injOn φ hmem hinj
  calc ((d.divisors ×ˢ d.divisors).filter (fun q : ℕ × ℕ => q.1.lcm q.2 = d)).card
      ≤ (d.primeFactors.pi (fun _ => triState)).card := hcard
    _ = ∏ _a ∈ d.primeFactors, triState.card := Finset.card_pi _ _
    _ = ∏ _a ∈ d.primeFactors, 3 := by simp [triState_card]
    _ = 3 ^ d.primeFactors.card := Finset.prod_const 3

theorem error_bound (s : BoundingSieve) {ξ : ℝ} (hξ : 0 ≤ ξ) {w : ℕ → ℝ}
    (hw : ∀ d : ℕ, |w d| ≤ 1) (hsupp : ∀ d : ℕ, ξ ≤ (d : ℝ) → w d = 0) :
    Work.ChenPlan.LinearSieve.lambdaErrSum s w ≤ Work.ChenPlan.LinearSieve.remSelberg s ξ := by
  have key : ∀ d ∈ s.prodPrimes.divisors,
      |BoundingSieve.lambdaSquared w d|
        ≤ if (d : ℝ) < ξ ^ 2 then (3 : ℝ) ^ d.primeFactors.card else 0 := by
    intro d hd
    have hdne : d ≠ 0 :=
      ne_zero_of_dvd_ne_zero (Nat.mem_divisors.mp hd).2 (Nat.mem_divisors.mp hd).1
    by_cases hcase : (d : ℝ) < ξ ^ 2
    · rw [if_pos hcase]
      have hdsq : Squarefree d := BoundingSieve.squarefree_of_mem_divisors_prodPrimes hd
      have hcount := card_lcm_pairs_le d hdsq
      have hsum : (∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
            (if d1.lcm d2 = d then (1 : ℝ) else 0))
          = ∑ q ∈ d.divisors ×ˢ d.divisors, (if q.1.lcm q.2 = d then (1 : ℝ) else 0) :=
        (Finset.sum_product d.divisors d.divisors
          (fun q : ℕ × ℕ => if q.1.lcm q.2 = d then (1 : ℝ) else 0)).symm
      rw [BoundingSieve.lambdaSquared]
      calc |∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
              (if d = d1.lcm d2 then w d1 * w d2 else 0)|
          ≤ ∑ d1 ∈ d.divisors, |∑ d2 ∈ d.divisors,
              (if d = d1.lcm d2 then w d1 * w d2 else 0)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
              |if d = d1.lcm d2 then w d1 * w d2 else 0| :=
            Finset.sum_le_sum fun d1 _ => Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
              (if d1.lcm d2 = d then (1 : ℝ) else 0) := by
            apply Finset.sum_le_sum; intro d1 _
            apply Finset.sum_le_sum; intro d2 _
            by_cases h : d1.lcm d2 = d
            · rw [if_pos h, if_pos h.symm, abs_mul]
              nlinarith [hw d1, hw d2, abs_nonneg (w d1), abs_nonneg (w d2)]
            · rw [if_neg h, if_neg (Ne.symm h)]; simp
        _ = (↑((d.divisors ×ˢ d.divisors).filter
              (fun q : ℕ × ℕ => q.1.lcm q.2 = d)).card : ℝ) := by
            rw [hsum, Finset.sum_boole]
        _ ≤ (3 : ℝ) ^ d.primeFactors.card := by
            exact_mod_cast hcount
    · rw [if_neg hcase]
      have hge : ξ ^ 2 ≤ (d : ℝ) := not_lt.mp hcase
      have hzero : BoundingSieve.lambdaSquared w d = 0 := by
        rw [BoundingSieve.lambdaSquared]
        apply Finset.sum_eq_zero
        intro d1 _
        apply Finset.sum_eq_zero
        intro d2 _
        by_cases h : d = d1.lcm d2
        · rw [if_pos h]
          by_contra hne
          have h1 : w d1 ≠ 0 := fun hh => hne (by rw [hh, zero_mul])
          have h2 : w d2 ≠ 0 := fun hh => hne (by rw [hh, mul_zero])
          have hd1lt : (d1 : ℝ) < ξ := by
            by_contra hh; exact h1 (hsupp d1 (not_lt.mp hh))
          have hd2lt : (d2 : ℝ) < ξ := by
            by_contra hh; exact h2 (hsupp d2 (not_lt.mp hh))
          have hlcmne : d1.lcm d2 ≠ 0 := by rw [← h]; exact hdne
          have hlt : (d : ℝ) < ξ ^ 2 := by
            rw [h]
            exact lcm_cast_lt_sq hξ hd1lt hd2lt hlcmne
          exact absurd hlt (not_lt.mpr hge)
        · rw [if_neg h]
      rw [hzero, abs_zero]
  rw [Work.ChenPlan.LinearSieve.lambdaErrSum, Work.ChenPlan.LinearSieve.remSelberg,
    Finset.sum_filter]
  refine Finset.sum_le_sum fun d hd => ?_
  have h := key d hd
  calc |BoundingSieve.lambdaSquared w d| * |s.rem d|
      ≤ (if (d : ℝ) < ξ ^ 2 then (3 : ℝ) ^ d.primeFactors.card else 0) * |s.rem d| :=
        mul_le_mul_of_nonneg_right h (abs_nonneg _)
    _ = (if (d : ℝ) < ξ ^ 2 then (3 : ℝ) ^ d.primeFactors.card * |s.rem d| else 0) := by
        by_cases hh : (d : ℝ) < ξ ^ 2 <;> simp [hh]

end Work.LinearSieve.Selberg
