import Mathlib
import Submission.Work.BW.card_filter_ap_dvd_ge

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-! ## Divisibility of `n!` into `q^n * ∏_{j<n} (x - j*q)`

The main result is `ap_factorial_dvd`.  The proof reduces the integer statement to a natural
number statement via `Int.natAbs`, and then compares the `p`-adic valuations of both sides for
every prime `p`, using Legendre's formula `v_p(n!) = ∑_{i ≥ 1} ⌊n / p^i⌋` and the counting fact
`card_filter_ap_dvd_ge` that, for `p ∤ q`, the indices `j < n` with `p ^ m ∣ x - j * q` form a
single residue class mod `p ^ m` and hence number at least `⌊n / p ^ m⌋`. -/

/-- For a natural number `n` and an integer `z`: `n ∣ z` (in `ℤ`) iff `n ∣ z.natAbs`. -/
lemma ap_int_dvd_iff_natAbs_dvd (n : ℕ) (z : ℤ) : (n : ℤ) ∣ z ↔ n ∣ z.natAbs := by
  simpa using (Int.natAbs_dvd_natAbs (a := (n : ℤ)) (b := z)).symm

/-- `(p : ℤ) ^ i ∣ z` iff `p ^ i ∣ z.natAbs`. -/
lemma ap_int_pow_dvd_iff_natAbs (p i : ℕ) (z : ℤ) :
    ((p : ℤ) ^ i) ∣ z ↔ p ^ i ∣ z.natAbs := by
  rw [← Nat.cast_pow]
  exact ap_int_dvd_iff_natAbs_dvd (p ^ i) z

/-- The `p`-adic valuation of a product of nonzero naturals is the sum of the valuations. -/
lemma ap_padicValNat_prod_of_ne_zero {p : ℕ} [Fact p.Prime] {ι : Type*} {s : Finset ι}
    {g : ι → ℕ} (h : ∀ x ∈ s, g x ≠ 0) :
    padicValNat p (∏ x ∈ s, g x) = ∑ x ∈ s, padicValNat p (g x) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro h
    simp
  · intro a s ha ih h
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      padicValNat.mul (h a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr (fun x hx => h x (Finset.mem_insert_of_mem hx))),
      ih (fun x hx => h x (Finset.mem_insert_of_mem hx))]

/-- If `a ≠ 0`, the number of exponents `i ∈ [1, b)` with `p ^ i ∣ a` is at most
`padicValNat p a`. -/
lemma ap_card_filter_pow_dvd_le {p : ℕ} [Fact p.Prime] (b a : ℕ) (ha : a ≠ 0) :
    ((Finset.Ico 1 b).filter (fun i => p ^ i ∣ a)).card ≤ padicValNat p a := by
  calc ((Finset.Ico 1 b).filter (fun i => p ^ i ∣ a)).card
      ≤ (Finset.Ico 1 (padicValNat p a + 1)).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_Ico] at hi ⊢
        exact ⟨hi.1.1, Nat.lt_succ_of_le ((padicValNat_dvd_iff_le ha).mp hi.2)⟩
    _ = padicValNat p a := by rw [Nat.card_Ico]; omega

/-- Interchange of the two counting sums (Mertens' swap). -/
lemma ap_sum_card_filter_swap (p b n : ℕ) (g : ℕ → ℕ) :
    ∑ j ∈ Finset.range n, ((Finset.Ico 1 b).filter (fun i => p ^ i ∣ g j)).card
      = ∑ i ∈ Finset.Ico 1 b, ((Finset.range n).filter (fun j => p ^ i ∣ g j)).card := by
  classical
  simp_rw [Finset.card_filter]
  exact Finset.sum_comm

/-- The natural-number form of the main divisibility statement: `n ! ∣ q ^ n * ∏_{j<n} |x - j*q|`. -/
theorem ap_factorial_dvd_nat (n q : ℕ) (x : ℤ) :
    n.factorial ∣ q ^ n * ∏ j ∈ Finset.range n, (x - (j : ℤ) * q).natAbs := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    have : (0 : ℕ) ^ n = 0 := by simp [hn.ne']
    rw [this, zero_mul]
    exact dvd_zero _
  by_cases hprod : ∏ j ∈ Finset.range n, (x - (j : ℤ) * q).natAbs = 0
  · rw [hprod, mul_zero]
    exact dvd_zero _
  · refine (Nat.factorization_le_iff_dvd (Nat.factorial_ne_zero n)
      (mul_ne_zero (pow_ne_zero n hq.ne') hprod)).mp ?_
    rw [Finsupp.le_def]
    intro p
    by_cases hp : p.Prime
    · haveI : Fact p.Prime := ⟨hp⟩
      rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
      have hg : ∀ j ∈ Finset.range n, (x - (j : ℤ) * q).natAbs ≠ 0 :=
        Finset.prod_ne_zero_iff.mp hprod
      have hfac : padicValNat p (q ^ n * ∏ j ∈ Finset.range n, (x - (j : ℤ) * q).natAbs)
          = n * padicValNat p q
            + ∑ j ∈ Finset.range n, padicValNat p ((x - (j : ℤ) * q).natAbs) := by
        rw [padicValNat.mul (pow_ne_zero n hq.ne') hprod, padicValNat.pow,
          ap_padicValNat_prod_of_ne_zero hg]
      rw [hfac]
      by_cases hpq : p ∣ q
      · have h1 : 1 ≤ padicValNat p q := one_le_padicValNat_of_dvd hq.ne' hpq
        have h2 : padicValNat p n.factorial ≤ n := padicValNat_factorial_le p n
        have h3 : n ≤ n * padicValNat p q := by
          simpa using Nat.mul_le_mul_left n h1
        omega
      · have hLeg : padicValNat p n.factorial
            = ∑ i ∈ Finset.Ico 1 (Nat.log p n + 1), n / p ^ i :=
          padicValNat_factorial (Nat.lt_succ_self _)
        rw [hLeg]
        have h₁ : ∑ i ∈ Finset.Ico 1 (Nat.log p n + 1), n / p ^ i
            ≤ ∑ i ∈ Finset.Ico 1 (Nat.log p n + 1),
                ((Finset.range n).filter
                  (fun (j : ℕ) => p ^ i ∣ (x - (j : ℤ) * q).natAbs)).card := by
          apply Finset.sum_le_sum
          intro i hi
          have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
          have hc := card_filter_ap_dvd_ge p i n q x hp hi1 hpq
          rwa [Finset.filter_congr
            (fun (j : ℕ) _ => ap_int_pow_dvd_iff_natAbs p i (x - (j : ℤ) * (q : ℤ)))] at hc
        have h₂ : ∑ i ∈ Finset.Ico 1 (Nat.log p n + 1),
                ((Finset.range n).filter
                  (fun (j : ℕ) => p ^ i ∣ (x - (j : ℤ) * q).natAbs)).card
            = ∑ j ∈ Finset.range n,
                ((Finset.Ico 1 (Nat.log p n + 1)).filter
                  (fun (i : ℕ) => p ^ i ∣ (x - (j : ℤ) * q).natAbs)).card :=
          (ap_sum_card_filter_swap p (Nat.log p n + 1) n
            (fun (j : ℕ) => (x - (j : ℤ) * q).natAbs)).symm
        have h₃ : ∑ j ∈ Finset.range n,
                ((Finset.Ico 1 (Nat.log p n + 1)).filter
                  (fun (i : ℕ) => p ^ i ∣ (x - (j : ℤ) * q).natAbs)).card
            ≤ ∑ j ∈ Finset.range n, padicValNat p ((x - (j : ℤ) * q).natAbs) :=
          Finset.sum_le_sum
            (fun (j : ℕ) hj => ap_card_filter_pow_dvd_le (Nat.log p n + 1) _ (hg j hj))
        refine le_trans h₁ ?_
        rw [h₂]
        exact le_trans h₃ (Nat.le_add_left _ _)
    · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
      omega

/-- A product of `n` terms of an arithmetic progression with difference `q`, scaled by `q ^ n`,
is divisible by `n!`: `n ! ∣ q ^ n * ∏_{j < n} (x - j * q)`.  Equivalently, `q ^ (2 * n)` times
the `n`-th binomial coefficient of the rational `x / q` is an integer.  Standard
Tijdeman/Bhargava integrality fact: for a prime `p` with `p ∤ q` the indices `j < n` with
`p ^ m ∣ x - j * q` form a single residue class mod `p ^ m`, hence number at least
`⌊n / p ^ m⌋`, giving `v_p (∏_{j<n} (x - j*q)) ≥ v_p (n!)`; and if `p ∣ q` then
`n * v_p q ≥ n ≥ v_p (n!)`. -/
theorem ap_factorial_dvd (n q : ℕ) (x : ℤ) :
    (n.factorial : ℤ) ∣ (q : ℤ) ^ n * ∏ j ∈ Finset.range n, (x - (j : ℤ) * q) := by
  refine Int.natAbs_dvd_natAbs.mp ?_
  have h : (∏ j ∈ Finset.range n, (x - (j : ℤ) * (q : ℤ))).natAbs
      = ∏ j ∈ Finset.range n, (x - (j : ℤ) * q).natAbs :=
    map_prod Int.natAbsHom (fun (j : ℕ) => x - (j : ℤ) * (q : ℤ)) (Finset.range n)
  simp only [Int.natAbs_natCast, Int.natAbs_mul, Int.natAbs_pow, h]
  exact ap_factorial_dvd_nat n q x

end Work.BW
