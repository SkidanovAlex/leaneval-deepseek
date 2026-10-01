import Mathlib
import Submission.Work.LinnikBurgess.frame_step_defs

open scoped BigOperators

namespace Work.LinnikAreas

open Work.LinnikBurgess

/-! ## 1. `frameMod` arithmetic with the sharp factor `2`

The sibling development (`Work.LinnikBurgess.frameMod_arith`) proves
`H / frameMod d a0 a1 + 1 ≤ H · gcd(d,|a0-a1|) · 2^ω(d) / d + 1`.  For the Case-I assembly of
`sumI` the extra factor `2^ω(d)` is fatal (the closing `τ`-comparison has only the budget
`τ(m d g)^8`), and one can do with a factor `2`: indeed `frameMod d a0 a1 · gcd(d, 2|a0-a1|) = d`
sharply, and `gcd(d, 2n) ≤ 2 gcd(d, n)`.  Those two facts are reproved here (they are `private`
upstream). -/

private lemma frameMod_eq_prod_own (d a0 a1 : ℕ) :
    frameMod d a0 a1
      = ∏ p ∈ d.primeFactors, p ^ (max 0 (d.factorization p
          - (2 : ℕ).factorization p
          - (((a0 : ℤ) - (a1 : ℤ)).natAbs).factorization p)) := by
  unfold frameMod
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp' : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  congr 1
  rw [← Nat.factorization_def 2 hp', ← Nat.factorization_def (((a0 : ℤ) - (a1 : ℤ)).natAbs) hp']

private lemma frameMod_factorization_own (d a0 a1 q : ℕ) :
    (frameMod d a0 a1).factorization q
      = if q ∈ d.primeFactors then
          max 0 (d.factorization q - (2 : ℕ).factorization q
            - (((a0 : ℤ) - (a1 : ℤ)).natAbs).factorization q)
        else 0 := by
  rw [frameMod_eq_prod_own]
  rw [Nat.factorization_prod_apply (S := d.primeFactors)
        (g := fun p => p ^ (max 0 (d.factorization p - (2 : ℕ).factorization p
              - (((a0 : ℤ) - (a1 : ℤ)).natAbs).factorization p)))
        (fun p hp => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero)]
  rw [Finset.sum_congr rfl (fun p hp => by
        rw [Nat.Prime.factorization_pow (Nat.prime_of_mem_primeFactors hp),
          Finsupp.single_apply])]
  rw [Finset.sum_ite_eq']

private lemma frameMod_mul_gcd_two_mul_own {d a0 a1 : ℕ} (hd : 0 < d) (h01 : a0 ≠ a1) :
    frameMod d a0 a1 * Nat.gcd d (2 * ((a0 : ℤ) - (a1 : ℤ)).natAbs) = d := by
  set n : ℕ := ((a0 : ℤ) - (a1 : ℤ)).natAbs with hn
  have hn0 : n ≠ 0 := by
    rw [hn, Int.natAbs_ne_zero]
    omega
  have hfac : ∀ q, (frameMod d a0 a1).factorization q
      = if q ∈ d.primeFactors then max 0 (d.factorization q
          - (2 : ℕ).factorization q - n.factorization q) else 0 := by
    intro q
    rw [frameMod_factorization_own d a0 a1 q, ← hn]
  have hm0 : frameMod d a0 a1 ≠ 0 := by
    rw [frameMod_eq_prod_own]
    exact Finset.prod_ne_zero_iff.mpr fun p hp =>
      pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hg0 : Nat.gcd d (2 * n) ≠ 0 := by
    have h := Nat.gcd_pos_of_pos_left (2 * n) hd
    omega
  rw [Nat.eq_of_factorization_eq (mul_ne_zero hm0 hg0) (Nat.ne_of_gt hd)]
  intro q
  rw [Nat.factorization_mul hm0 hg0, Finsupp.add_apply, hfac q,
      Nat.factorization_gcd (Nat.ne_of_gt hd) (by positivity : 2 * n ≠ 0),
      Finsupp.inf_apply, Nat.factorization_mul (by norm_num : (2:ℕ) ≠ 0) hn0,
      Finsupp.add_apply]
  by_cases hq : q ∈ d.primeFactors
  · rw [if_pos hq]
    omega
  · rw [if_neg hq]
    have hA : d.factorization q = 0 := by
      rw [Nat.factorization_eq_zero_iff]
      by_cases hqp : q.Prime
      · refine Or.inr (Or.inl fun hqd => hq ?_)
        exact Nat.mem_primeFactors.mpr ⟨hqp, hqd, Nat.ne_of_gt hd⟩
      · exact Or.inl hqp
    rw [hA]
    simp

/-- `gcd d (2 n) ≤ 2 * gcd d n`. -/
private lemma gcd_two_mul_le_two (d n : ℕ) (hd : 0 < d) :
    Nat.gcd d (2 * n) ≤ Nat.gcd d n * 2 := by
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    simp only [mul_zero, Nat.gcd_zero_right]
    omega
  · have hdiv : Nat.gcd d (2 * n) ∣ Nat.gcd d n * 2 := by
      rw [← Nat.factorization_le_iff_dvd (by positivity) (by positivity)]
      intro q
      rw [Nat.factorization_mul (Nat.gcd_pos_of_pos_left n hd).ne' (by norm_num : (2:ℕ) ≠ 0),
          Finsupp.add_apply,
          Nat.factorization_gcd (Nat.ne_of_gt hd) hn, Finsupp.inf_apply,
          Nat.factorization_gcd (Nat.ne_of_gt hd)
            (mul_ne_zero (by norm_num : (2:ℕ) ≠ 0) hn), Finsupp.inf_apply,
          Nat.factorization_mul (by norm_num : (2:ℕ) ≠ 0) hn, Finsupp.add_apply]
      omega
    exact Nat.le_of_dvd (Nat.mul_pos (Nat.gcd_pos_of_pos_left n hd) (by norm_num)) hdiv

/-- **Sharp `frameMod` bound**: `d ≤ frameMod d a0 a1 · gcd(d,|a0-a1|) · 2`. -/
theorem frameMod_mul_gcd_ge_two {d a0 a1 : ℕ} (hd : 0 < d) :
    d ≤ frameMod d a0 a1 * Nat.gcd d (((a0 : ℤ) - (a1 : ℤ)).natAbs) * 2 := by
  by_cases h01 : a0 = a1
  · have hn : (((a0 : ℤ) - (a1 : ℤ)).natAbs) = 0 := by rw [h01]; simp
    rw [hn, Nat.gcd_zero_right]
    have hM : 1 ≤ frameMod d a0 a1 := by
      rw [frameMod_eq_prod_own]
      exact Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun p hp =>
        pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero)
    calc d = d * 1 := (mul_one d).symm
      _ ≤ d * (frameMod d a0 a1 * 2) := Nat.mul_le_mul (le_refl d) (by omega)
      _ = frameMod d a0 a1 * d * 2 := by ring
  · have hexact := frameMod_mul_gcd_two_mul_own (a0 := a0) (a1 := a1) hd h01
    have hle := gcd_two_mul_le_two d (((a0 : ℤ) - (a1 : ℤ)).natAbs) hd
    calc d = frameMod d a0 a1 * Nat.gcd d (2 * (((a0 : ℤ) - (a1 : ℤ)).natAbs)) := hexact.symm
      _ ≤ frameMod d a0 a1 * (Nat.gcd d (((a0 : ℤ) - (a1 : ℤ)).natAbs) * 2) :=
          Nat.mul_le_mul_left _ hle
      _ = frameMod d a0 a1 * Nat.gcd d (((a0 : ℤ) - (a1 : ℤ)).natAbs) * 2 := by ring

/-- **Sharp `frameMod` bridge, real form.** -/
theorem frameMod_arith_two {d H a0 a1 : ℕ} (hd : 0 < d) :
    (H : ℝ) / (frameMod d a0 a1 : ℝ) + 1
      ≤ (H : ℝ) * (Nat.gcd d (((a0 : ℤ) - (a1 : ℤ)).natAbs) : ℝ) * 2 / (d : ℝ) + 1 := by
  set n : ℕ := ((a0 : ℤ) - (a1 : ℤ)).natAbs with hn
  set mm : ℕ := frameMod d a0 a1 with hm
  set gg : ℕ := Nat.gcd d n with hg
  have hm0 : 0 < mm := by
    rw [hm, frameMod_eq_prod_own]
    exact Finset.prod_pos (fun p hp => pow_pos (Nat.prime_of_mem_primeFactors hp).pos _)
  have hcore : d ≤ mm * gg * 2 := by
    rw [hm, hg, hn]
    exact frameMod_mul_gcd_ge_two (a0 := a0) (a1 := a1) hd
  have hmR : (0 : ℝ) < (mm : ℝ) := by exact_mod_cast hm0
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hcoreR : (d : ℝ) ≤ (mm : ℝ) * (gg : ℝ) * 2 := by exact_mod_cast hcore
  have hkey : (1 : ℝ) / (mm : ℝ) ≤ ((gg : ℝ) * 2) / (d : ℝ) := by
    rw [div_le_div_iff₀ hmR hdR]
    nlinarith [hcoreR]
  calc (H : ℝ) / (mm : ℝ) + 1 = (H : ℝ) * ((1 : ℝ) / (mm : ℝ)) + 1 := by rw [mul_one_div]
    _ ≤ (H : ℝ) * (((gg : ℝ) * 2) / (d : ℝ)) + 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hkey (Nat.cast_nonneg H)) le_rfl
    _ = (H : ℝ) * (gg : ℝ) * 2 / (d : ℝ) + 1 := by ring

/-! ## 2. The `τ`-comparison closing Case I -/

private def Ffun (m d g : ℕ) (p : ℕ) : ℕ :=
  (if p ∈ d.primeFactors then 3 else 1)
    * (if p ∈ d.primeFactors then d.factorization p + 1 else 1)
    * (if p ∈ g.primeFactors then g.factorization p + 1 else 1) ^ 2
    * (if p ∈ m.primeFactors then m.factorization p + 1 else 1) ^ 4

private def Gfun (m d g p : ℕ) : ℕ := ((m * d * g).factorization p + 1) ^ 8

private lemma core_le (a b c : ℕ) :
    (if a = 0 then 1 else 3) * (a + 1) * (b + 1) ^ 2 * (c + 1) ^ 4
      ≤ (a + b + c + 1) ^ 8 := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    rw [if_pos rfl]
    simp only [zero_add, one_mul]
    have h1 : b + 1 ≤ b + c + 1 := by omega
    have h2 : c + 1 ≤ b + c + 1 := by omega
    calc (b + 1) ^ 2 * (c + 1) ^ 4
        ≤ (b + c + 1) ^ 2 * (b + c + 1) ^ 4 :=
          Nat.mul_le_mul (Nat.pow_le_pow_left h1 2) (Nat.pow_le_pow_left h2 4)
      _ = (b + c + 1) ^ 6 := by ring
      _ ≤ (b + c + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
  · rw [if_neg (Nat.pos_iff_ne_zero.mp ha)]
    rcases Nat.eq_zero_or_pos (b + c) with hbc | hbc
    · have hb : b = 0 := by omega
      have hc : c = 0 := by omega
      subst hb; subst hc
      have ha1 : 2 ≤ a + 1 := by omega
      have h7 : 3 ≤ (a + 1) ^ 7 := by
        calc (3:ℕ) ≤ 2 ^ 7 := by norm_num
          _ ≤ (a + 1) ^ 7 := Nat.pow_le_pow_left ha1 7
      have key : 3 * (a + 1) ≤ (a + 1) ^ 8 := by
        calc 3 * (a + 1) ≤ (a + 1) ^ 7 * (a + 1) := Nat.mul_le_mul_right _ h7
          _ = (a + 1) ^ 8 := by ring
      simpa using key
    · have hX : 3 ≤ a + b + c + 1 := by omega
      have h2 : a + 1 ≤ a + b + c + 1 := by omega
      have h3 : (b + 1) ^ 2 ≤ (a + b + c + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have h4 : (c + 1) ^ 4 ≤ (a + b + c + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
      calc 3 * (a + 1) * (b + 1) ^ 2 * (c + 1) ^ 4
          ≤ (a + b + c + 1) * (a + b + c + 1) * (a + b + c + 1) ^ 2
              * (a + b + c + 1) ^ 4 :=
            Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hX h2) h3) h4
        _ = (a + b + c + 1) ^ 8 := by ring

/-- `3^ω(d) · τ(d) · τ(g)^2 · τ(m)^4 ≤ τ(m d g)^8`. -/
theorem tau_three_pow_le_nat {m d g : ℕ} (hm : 0 < m) (hd : 0 < d) (hg : 0 < g) :
    3 ^ d.primeFactors.card * d.divisors.card * g.divisors.card ^ 2 * m.divisors.card ^ 4
      ≤ (m * d * g).divisors.card ^ 8 := by
  have hmd0 : m * d ≠ 0 := by positivity
  have hmdg0 : m * d * g ≠ 0 := by positivity
  have hpf : (m * d * g).primeFactors = m.primeFactors ∪ d.primeFactors ∪ g.primeFactors := by
    rw [Nat.primeFactors_mul hmd0 (ne_of_gt hg),
      Nat.primeFactors_mul (ne_of_gt hm) (ne_of_gt hd)]
  have hdsub : d.primeFactors ⊆ (m * d * g).primeFactors := by
    rw [hpf]
    intro p hp
    simp only [Finset.mem_union]
    exact Or.inl (Or.inr hp)
  have hgsub : g.primeFactors ⊆ (m * d * g).primeFactors := by
    rw [hpf]
    intro p hp
    simp only [Finset.mem_union]
    exact Or.inr hp
  have hmsub : m.primeFactors ⊆ (m * d * g).primeFactors := by
    rw [hpf]
    intro p hp
    simp only [Finset.mem_union]
    exact Or.inl (Or.inl hp)
  have h3k : ∏ p ∈ (m * d * g).primeFactors, (if p ∈ d.primeFactors then 3 else 1)
      = 3 ^ d.primeFactors.card := by
    rw [← Finset.prod_subset hdsub (fun p hp hpnot => by simp [hpnot])]
    rw [Finset.prod_congr rfl (fun p hp => if_pos hp), Finset.prod_const]
  have htd : ∏ p ∈ (m * d * g).primeFactors,
        (if p ∈ d.primeFactors then d.factorization p + 1 else 1) = d.divisors.card := by
    rw [← Finset.prod_subset hdsub (fun p hp hpnot => by simp [hpnot])]
    rw [Finset.prod_congr rfl (fun p hp => if_pos hp), Nat.card_divisors (ne_of_gt hd)]
  have htg : ∏ p ∈ (m * d * g).primeFactors,
        (if p ∈ g.primeFactors then g.factorization p + 1 else 1) = g.divisors.card := by
    rw [← Finset.prod_subset hgsub (fun p hp hpnot => by simp [hpnot])]
    rw [Finset.prod_congr rfl (fun p hp => if_pos hp), Nat.card_divisors (ne_of_gt hg)]
  have htm : ∏ p ∈ (m * d * g).primeFactors,
        (if p ∈ m.primeFactors then m.factorization p + 1 else 1) = m.divisors.card := by
    rw [← Finset.prod_subset hmsub (fun p hp hpnot => by simp [hpnot])]
    rw [Finset.prod_congr rfl (fun p hp => if_pos hp), Nat.card_divisors (ne_of_gt hm)]
  have hLHS : ∏ p ∈ (m * d * g).primeFactors, Ffun m d g p
      = 3 ^ d.primeFactors.card * d.divisors.card * g.divisors.card ^ 2
          * m.divisors.card ^ 4 := by
    unfold Ffun
    simp only [Finset.prod_mul_distrib, Finset.prod_pow]
    rw [h3k, htd, htg, htm]
  have hpt : ∀ p ∈ (m * d * g).primeFactors, Ffun m d g p ≤ Gfun m d g p := by
    intro p _
    have hfac : (m * d * g).factorization p
        = d.factorization p + g.factorization p + m.factorization p := by
      rw [Nat.factorization_mul hmd0 (ne_of_gt hg),
        Nat.factorization_mul (ne_of_gt hm) (ne_of_gt hd)]
      simp only [Finsupp.add_apply]
      omega
    have hdm : p ∈ d.primeFactors ↔ d.factorization p ≠ 0 := by
      rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    have hgm : p ∈ g.primeFactors ↔ g.factorization p ≠ 0 := by
      rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    have hmm : p ∈ m.primeFactors ↔ m.factorization p ≠ 0 := by
      rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    have h3 : (if p ∈ d.primeFactors then 3 else 1)
        = (if d.factorization p = 0 then 1 else 3) := by
      by_cases h : p ∈ d.primeFactors
      · rw [if_pos h, if_neg (hdm.mp h)]
      · have hz : d.factorization p = 0 := by by_contra hc; exact h (hdm.mpr hc)
        rw [if_neg h, hz]; simp
    have h1 : (if p ∈ d.primeFactors then d.factorization p + 1 else 1)
        = d.factorization p + 1 := by
      by_cases h : p ∈ d.primeFactors
      · rw [if_pos h]
      · rw [if_neg h]
        have : d.factorization p = 0 := by by_contra hcon; exact h (hdm.mpr hcon)
        rw [this]
    have h2 : (if p ∈ g.primeFactors then g.factorization p + 1 else 1)
        = g.factorization p + 1 := by
      by_cases h : p ∈ g.primeFactors
      · rw [if_pos h]
      · rw [if_neg h]
        have : g.factorization p = 0 := by by_contra hcon; exact h (hgm.mpr hcon)
        rw [this]
    have h4 : (if p ∈ m.primeFactors then m.factorization p + 1 else 1)
        = m.factorization p + 1 := by
      by_cases h : p ∈ m.primeFactors
      · rw [if_pos h]
      · rw [if_neg h]
        have : m.factorization p = 0 := by by_contra hcon; exact h (hmm.mpr hcon)
        rw [this]
    unfold Ffun Gfun
    rw [h3, h1, h2, h4, hfac]
    exact core_le (d.factorization p) (g.factorization p) (m.factorization p)
  calc 3 ^ d.primeFactors.card * d.divisors.card * g.divisors.card ^ 2 * m.divisors.card ^ 4
      = ∏ p ∈ (m * d * g).primeFactors, Ffun m d g p := hLHS.symm
    _ ≤ ∏ p ∈ (m * d * g).primeFactors, Gfun m d g p := Finset.prod_le_prod' hpt
    _ = (m * d * g).divisors.card ^ 8 := by
        simp only [Gfun, Finset.prod_pow]
        rw [Nat.card_divisors hmdg0]

/-- The real-valued form of the `τ`-comparison used at the end of Case I. -/
theorem tau_three_pow_le {m d g : ℕ} (hm : 0 < m) (hd : 0 < d) (hg : 0 < g) :
    32 * 3 ^ d.primeFactors.card * ((d.divisors.card : ℕ) : ℝ)
        * (((g.divisors.card : ℕ) : ℝ)) ^ 2 * (((m.divisors.card : ℕ) : ℝ)) ^ 4
      ≤ 30000 * ((((m * d * g).divisors.card : ℕ) : ℝ)) ^ 8 := by
  have hnat := tau_three_pow_le_nat hm hd hg
  have hcast : ((3 ^ d.primeFactors.card * d.divisors.card * g.divisors.card ^ 2
      * m.divisors.card ^ 4 : ℕ) : ℝ) ≤ (((m * d * g).divisors.card ^ 8 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  push_cast at hcast
  linarith [hcast, (show (32:ℝ) ≤ 30000 by norm_num),
    (show (0:ℝ) ≤ (((m * d * g).divisors.card : ℕ) : ℝ) ^ 8 by positivity)]

end Work.LinnikAreas
