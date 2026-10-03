import Mathlib
import Submission.Work.FIArea1.l51arith_defs
import Submission.Commons.NumberTheory.Divisors.sum_tau_pow_div_le

set_option autoImplicit false
namespace Work.FIArea1

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `mP d = d / sP d ^ 2`, the "squarefree kernel" partner of `sP`, so that
`d = mP d * sP d ^ 2`. -/
def mP (d : ℕ) : ℕ := d / sP d ^ 2

theorem mP_mul_sP_sq (d : ℕ) : mP d * sP d ^ 2 = d := by
  rw [mP, Nat.mul_comm]
  exact sP_sq_mul_div d

/-- The divisor-count function is submultiplicative: `τ(mn) ≤ τ(m)τ(n)`. -/
theorem card_divisors_mul_le (m n : ℕ) :
    (m * n).divisors.card ≤ m.divisors.card * n.divisors.card := by
  rcases eq_or_ne (m * n) 0 with hmn | hmn
  · rw [hmn]; simp
  have hm : m ≠ 0 := fun h => hmn (by rw [h, zero_mul])
  have hn : n ≠ 0 := fun h => hmn (by rw [h, mul_zero])
  rw [Nat.card_divisors hmn, Nat.card_divisors hm, Nat.card_divisors hn,
      Nat.primeFactors_mul hm hn]
  have hprod : ∏ p ∈ m.primeFactors ∪ n.primeFactors, ((m * n).factorization p + 1)
      ≤ (∏ p ∈ m.primeFactors ∪ n.primeFactors, (m.factorization p + 1))
        * (∏ p ∈ m.primeFactors ∪ n.primeFactors, (n.factorization p + 1)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀
    · intro i hi; exact Nat.zero_le _
    · intro p hp
      rw [Nat.factorization_mul hm hn, Finsupp.add_apply]
      have : (m.factorization p + 1) * (n.factorization p + 1)
          = m.factorization p * n.factorization p
            + (m.factorization p + n.factorization p + 1) := by ring
      rw [this]
      exact Nat.le_add_left _ _
  have hC1 : ∏ p ∈ m.primeFactors ∪ n.primeFactors, (m.factorization p + 1)
      = ∏ p ∈ m.primeFactors, (m.factorization p + 1) := by
    rw [Finset.prod_subset (s₁ := m.primeFactors) (s₂ := m.primeFactors ∪ n.primeFactors)
      Finset.subset_union_left]
    intro p hpU hpm
    have hpP : p.Prime := by
      rcases Finset.mem_union.mp hpU with h | h
      · exact Nat.prime_of_mem_primeFactors h
      · exact Nat.prime_of_mem_primeFactors h
    have hnd : ¬ p ∣ m := fun hd => hpm (Nat.mem_primeFactors.mpr ⟨hpP, hd, hm⟩)
    rw [Nat.factorization_eq_zero_of_not_dvd hnd]; simp
  have hC2 : ∏ p ∈ m.primeFactors ∪ n.primeFactors, (n.factorization p + 1)
      = ∏ p ∈ n.primeFactors, (n.factorization p + 1) := by
    rw [Finset.prod_subset (s₁ := n.primeFactors) (s₂ := m.primeFactors ∪ n.primeFactors)
      Finset.subset_union_right]
    intro p hpU hpn
    have hpP : p.Prime := by
      rcases Finset.mem_union.mp hpU with h | h
      · exact Nat.prime_of_mem_primeFactors h
      · exact Nat.prime_of_mem_primeFactors h
    have hnd : ¬ p ∣ n := fun hd => hpn (Nat.mem_primeFactors.mpr ⟨hpP, hd, hn⟩)
    rw [Nat.factorization_eq_zero_of_not_dvd hnd]; simp
  rw [hC1, hC2] at hprod
  exact hprod

/-- Pointwise bound: for `d ≥ 1`, writing `d = mP d * sP d ^ 2`, the summand
`τ(d)^2 · sP d / d` is at most `(τ(mP d)^2 / mP d) · (τ(sP d)^4 / sP d)`. -/
theorem term_le (d : ℕ) (hd : 1 ≤ d) :
    ((d.divisors.card : ℝ) ^ 2) * (sP d : ℝ) / (d : ℝ)
      ≤ (((mP d).divisors.card : ℝ) ^ 2) / (mP d : ℝ)
          * ((((sP d).divisors.card : ℝ) ^ 4) / (sP d : ℝ)) := by
  have hmul : mP d * sP d ^ 2 = d := mP_mul_sP_sq d
  have hs1 : 1 ≤ sP d := sP_pos d
  have hm1 : 1 ≤ mP d := by
    rcases Nat.eq_zero_or_pos (mP d) with h | h
    · rw [h, zero_mul] at hmul; omega
    · exact h
  have htau_nat : d.divisors.card ≤ (mP d).divisors.card * ((sP d).divisors.card) ^ 2 := by
    have h1 : d.divisors.card = (mP d * sP d ^ 2).divisors.card := by rw [hmul]
    rw [h1]
    calc (mP d * sP d ^ 2).divisors.card
        ≤ (mP d).divisors.card * (sP d ^ 2).divisors.card := card_divisors_mul_le _ _
      _ ≤ (mP d).divisors.card * ((sP d).divisors.card * (sP d).divisors.card) := by
          apply Nat.mul_le_mul_left
          have h := card_divisors_mul_le (sP d) (sP d)
          simpa [pow_two] using h
      _ = (mP d).divisors.card * ((sP d).divisors.card) ^ 2 := by ring
  have htau : ((d.divisors.card : ℝ) ^ 2)
      ≤ (((mP d).divisors.card : ℝ) ^ 2) * (((sP d).divisors.card : ℝ) ^ 4) := by
    have h2 : (d.divisors.card : ℝ)
        ≤ (mP d).divisors.card * ((sP d).divisors.card : ℝ) ^ 2 := by
      have h3 : ((mP d).divisors.card * ((sP d).divisors.card) ^ 2 : ℕ)
          = ((mP d).divisors.card : ℝ) * ((sP d).divisors.card : ℝ) ^ 2 := by
        push_cast; ring
      rw [← h3]
      exact_mod_cast htau_nat
    have h4 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (d.divisors.card : ℝ)) h2 2
    calc ((d.divisors.card : ℝ) ^ 2)
        ≤ ((mP d).divisors.card * ((sP d).divisors.card : ℝ) ^ 2) ^ 2 := h4
      _ = (((mP d).divisors.card : ℝ) ^ 2) * (((sP d).divisors.card : ℝ) ^ 4) := by ring
  have hdeq : ((d : ℝ)) = (mP d : ℝ) * (sP d : ℝ) ^ 2 := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) hmul.symm
    push_cast at h
    exact h
  have hmR : (0 : ℝ) < mP d := by exact_mod_cast hm1
  have hsR : (0 : ℝ) < sP d := by exact_mod_cast hs1
  calc ((d.divisors.card : ℝ) ^ 2) * (sP d : ℝ) / (d : ℝ)
      = ((d.divisors.card : ℝ) ^ 2) / ((mP d : ℝ) * (sP d : ℝ)) := by
        rw [hdeq]; field_simp
    _ ≤ (((mP d).divisors.card : ℝ) ^ 2) * (((sP d).divisors.card : ℝ) ^ 4)
          / ((mP d : ℝ) * (sP d : ℝ)) :=
        div_le_div_of_nonneg_right htau (le_of_lt (mul_pos hmR hsR))
    _ = (((mP d).divisors.card : ℝ) ^ 2) / (mP d : ℝ)
          * ((((sP d).divisors.card : ℝ) ^ 4) / (sP d : ℝ)) := by
        rw [div_mul_div_comm]

/-- **Arithmetic bound for the divisor average on `a c₁² - b c₂²`.** With
`sP d = ∏_{p ∈ d.primeFactors} p ^ (d.factorization p / 2)` (`sP d ^ 2` is the largest square
divisor of `d`, so `d = sP d ^ 2 * (d / sP d ^ 2)`),
`∑_{d ≤ D} τ(d)² · sP d / d ≤ C · (log (D+2))^{20}`, where `τ(m) = m.divisors.card`.

*Route.* For `d ≥ 1` one has `τ(d) ≤ 2 ^ d.primeFactors.card * (sP d).divisors.card`
(exponent-by-exponent: `e_p + 1 ≤ 2 (⌊e_p/2⌋ + 1)`, so it suffices that
`(sP d).factorization p = (p ∈ d.primeFactors ? d.factorization p / 2 : 0) = d.factorization p / 2`,
which follows from `Nat.factorization_prod` + `Nat.factorization_pow` + `Nat.Prime.factorization`).
Write `mP d := d / sP d ^ 2` (so `d = mP d * sP d ^ 2`); then
`τ(d)² · sP d / d = τ(d)² / (sP d · mP d) ≤ (4^{ω(mP d)} / mP d) · (4^{ω(sP d)} τ(sP d)² / sP d)`
using `ω(d) ≤ ω(mP d) + ω(sP d)` (every prime `p ∣ d` divides `mP d = ∏_{e odd} p` or
`sP d = ∏ p^{⌊e/2⌋}`). The map `d ↦ (mP d, sP d)` is injective (because `d = mP d * sP d ^ 2`) and
`1 ≤ mP d ≤ D`, `1 ≤ sP d ≤ D` for `d ≤ D`, so the sum is at most
`(∑_{m ≤ D} 4^{ω m}/m)·(∑_{s ≤ D} 4^{ω s} τ(s)²/s)`. Finally `4^{ω(m)} ≤ τ(m)²` gives
`∑_{m ≤ D} 4^{ω m}/m ≤ ∑_{m ≤ D} τ(m)²/m ≤ C (log(D+2))^4`, and `4^{ω(s)} τ(s)² ≤ τ(s)^4` gives
`∑_{s ≤ D} 4^{ω s} τ(s)²/s ≤ ∑_{s ≤ D} τ(s)^4/s ≤ C (log(D+2))^{16}`
(both by `Commons.NumberTheory.Divisors.sum_tau_pow_div_le` with `k = 2` resp. `k = 4`;
add `import Submission.Commons.NumberTheory.Divisors.sum_tau_pow_div_le`).
The injection step `∑_{d≤D} A(mP d) B(sP d) ≤ (∑_{m≤D}A m)(∑_{s≤D}B s)` for `A, B ≥ 0` is proved by
`Finset.sum_image` + `Finset.sum_le_sum_of_subset_of_nonneg` + `Finset.sum_product`. -/
theorem l51_arith_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ D : ℕ, 1 ≤ D →
      (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ) ^ 2) * (sP d : ℝ) / (d : ℝ))
        ≤ C * (Real.log ((D : ℝ) + 2)) ^ (20 : ℕ) := by
  obtain ⟨C₂, hC₂pos, hC₂⟩ := Commons.NumberTheory.Divisors.sum_tau_pow_div_le 2
  obtain ⟨C₄, hC₄pos, hC₄⟩ := Commons.NumberTheory.Divisors.sum_tau_pow_div_le 4
  refine ⟨max (C₂ * C₄) 1, lt_max_of_lt_left (mul_pos hC₂pos hC₄pos), ?_⟩
  intro D hD
  set L := Real.log ((D : ℝ) + 2) with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
      have h := Real.log_le_log (Real.exp_pos 1) (le_of_lt Real.exp_one_lt_three)
      rwa [Real.log_exp] at h
    have h3 : (3 : ℝ) ≤ (D : ℝ) + 2 := by
      exact_mod_cast (show 3 ≤ D + 2 by omega)
    exact le_trans hlog3 (Real.log_le_log (by norm_num) h3)
  have hA : (∑ a ∈ Finset.Icc 1 D, ((a.divisors.card : ℝ) ^ 2) / (a : ℝ)) ≤ C₂ * L ^ 4 := by
    have h := hC₂ D hD
    rw [hLdef]
    simpa using h
  have hB : (∑ b ∈ Finset.Icc 1 D, ((b.divisors.card : ℝ) ^ 4) / (b : ℝ)) ≤ C₄ * L ^ 16 := by
    have h := hC₄ D hD
    rw [hLdef]
    simpa using h
  have hstep1 : (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ) ^ 2) * (sP d : ℝ) / (d : ℝ))
      ≤ ∑ d ∈ Finset.Icc 1 D,
          (((mP d).divisors.card : ℝ) ^ 2) / (mP d : ℝ)
            * ((((sP d).divisors.card : ℝ) ^ 4) / (sP d : ℝ)) := by
    apply Finset.sum_le_sum
    intro d hd
    exact term_le d (Finset.mem_Icc.mp hd).1
  have hinj : Set.InjOn (fun d : ℕ => (mP d, sP d)) ↑(Finset.Icc 1 D) := by
    intro a _ b _ hab
    have h1 : mP a = mP b := congrArg Prod.fst hab
    have h2 : sP a = sP b := congrArg Prod.snd hab
    have ha' := mP_mul_sP_sq a
    have hb' := mP_mul_sP_sq b
    rw [← ha', ← hb', h1, h2]
  have himg : (∑ q ∈ (Finset.Icc 1 D).image (fun d => (mP d, sP d)),
        ((q.1.divisors.card : ℝ) ^ 2) / (q.1 : ℝ)
          * (((q.2.divisors.card : ℝ) ^ 4) / (q.2 : ℝ)))
      = ∑ d ∈ Finset.Icc 1 D,
          (((mP d).divisors.card : ℝ) ^ 2) / (mP d : ℝ)
            * ((((sP d).divisors.card : ℝ) ^ 4) / (sP d : ℝ)) :=
    Finset.sum_image hinj
  have hsub : (Finset.Icc 1 D).image (fun d => (mP d, sP d))
      ⊆ (Finset.Icc 1 D) ×ˢ (Finset.Icc 1 D) := by
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨d, hd, rfl⟩ := hq
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hdD : d ≤ D := (Finset.mem_Icc.mp hd).2
    have hd0 : d ≠ 0 := by omega
    have hmul := mP_mul_sP_sq d
    have hm1 : 1 ≤ mP d := by
      rcases Nat.eq_zero_or_pos (mP d) with h | h
      · rw [h, zero_mul] at hmul; omega
      · exact h
    refine ⟨⟨hm1, ?_⟩, ⟨sP_pos d, ?_⟩⟩
    · calc mP d ≤ d := Nat.div_le_self d _
        _ ≤ D := hdD
    · calc sP d ≤ d := sP_le d hd0
        _ ≤ D := hdD
  have hprod2 : (∑ q ∈ (Finset.Icc 1 D).image (fun d => (mP d, sP d)),
        ((q.1.divisors.card : ℝ) ^ 2) / (q.1 : ℝ)
          * (((q.2.divisors.card : ℝ) ^ 4) / (q.2 : ℝ)))
      ≤ (∑ a ∈ Finset.Icc 1 D, ((a.divisors.card : ℝ) ^ 2) / (a : ℝ))
        * (∑ b ∈ Finset.Icc 1 D, ((b.divisors.card : ℝ) ^ 4) / (b : ℝ)) := by
    calc (∑ q ∈ (Finset.Icc 1 D).image (fun d => (mP d, sP d)),
        ((q.1.divisors.card : ℝ) ^ 2) / (q.1 : ℝ)
          * (((q.2.divisors.card : ℝ) ^ 4) / (q.2 : ℝ)))
        ≤ ∑ q ∈ (Finset.Icc 1 D) ×ˢ (Finset.Icc 1 D),
            ((q.1.divisors.card : ℝ) ^ 2) / (q.1 : ℝ)
              * (((q.2.divisors.card : ℝ) ^ 4) / (q.2 : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro q hq _; positivity)
      _ = (∑ a ∈ Finset.Icc 1 D, ((a.divisors.card : ℝ) ^ 2) / (a : ℝ))
            * (∑ b ∈ Finset.Icc 1 D, ((b.divisors.card : ℝ) ^ 4) / (b : ℝ)) := by
          rw [Finset.sum_product]
          exact (Finset.sum_mul_sum (Finset.Icc 1 D) (Finset.Icc 1 D)
            (fun a : ℕ => ((a.divisors.card : ℝ) ^ 2) / (a : ℝ))
            (fun b : ℕ => ((b.divisors.card : ℝ) ^ 4) / (b : ℝ))).symm
  rw [← himg] at hstep1
  calc (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ) ^ 2) * (sP d : ℝ) / (d : ℝ))
      ≤ ∑ q ∈ (Finset.Icc 1 D).image (fun d => (mP d, sP d)),
          ((q.1.divisors.card : ℝ) ^ 2) / (q.1 : ℝ)
            * (((q.2.divisors.card : ℝ) ^ 4) / (q.2 : ℝ)) := hstep1
    _ ≤ (∑ a ∈ Finset.Icc 1 D, ((a.divisors.card : ℝ) ^ 2) / (a : ℝ))
          * (∑ b ∈ Finset.Icc 1 D, ((b.divisors.card : ℝ) ^ 4) / (b : ℝ)) := hprod2
    _ ≤ (C₂ * L ^ 4) * (C₄ * L ^ 16) :=
        mul_le_mul hA hB (Finset.sum_nonneg fun b _ => by positivity) (by positivity)
    _ = C₂ * C₄ * L ^ 20 := by ring
    _ ≤ max (C₂ * C₄) 1 * L ^ 20 := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

end

end Work.FIArea1
