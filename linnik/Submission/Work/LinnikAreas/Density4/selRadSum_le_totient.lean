import Mathlib
import Submission.Work.LinnikAreas.Density4.SelbergDefs

namespace Work.LinnikAreas.Density4

open scoped BigOperators
open Finset

noncomputable section

/-!
## The harmonic bound `Σ_{d ≤ y, rad d ∣ k} 1/d ≤ k/φ(k)` for squarefree `k`

The main tool is the reciprocal divisor sum `recDiv n = Σ_{d ∣ n} 1/d`.  For squarefree `k`, every
`k`-smooth `d ≤ N` divides `k^N`, so `selRadSum y k ≤ recDiv (k^⌊y⌋₊)`, and the latter is at most
`k/φ(k)` by induction on `k`: splitting off a prime `p = k.minFac`, the multiplicity
`recDiv (p^N * m^N) = recDiv (p^N) · recDiv (m^N)` (coprime factors) gives a factor `p/φ(p)` from the
geometric series `Σ_{j ≤ N} p^{-j} ≤ p/(p-1)` times the induction hypothesis for `m = k/p`, and
`φ(p·m) = φ(p)·φ(m)`.

The same three ingredients are also available, proved independently, as standalone library lemmas in
sibling files (`Submission/Work/LinnikAreas/Density4/divisors_recip_mul_coprime.lean`,
`divisors_recip_prime_pow_le.lean` and `divisors_recip_pow_le_totient_div.lean`); the proof below is
self-contained and does not depend on them.
-/

/-- `recDiv n = Σ_{d ∣ n} 1/d`, the value at `1` of the divisor sum `σ_{-1}`. -/
private def recDiv (n : ℕ) : ℝ := ∑ d ∈ n.divisors, (1 : ℝ) / (d : ℝ)

private lemma recDiv_nonneg (n : ℕ) : 0 ≤ recDiv n :=
  Finset.sum_nonneg fun d _ => div_nonneg zero_le_one (Nat.cast_nonneg d)

/-- `recDiv` is multiplicative on coprime arguments. -/
private lemma recDiv_mul_coprime {m n : ℕ} (hmn : m.Coprime n) :
    recDiv (m * n) = recDiv m * recDiv n := by
  have step1 : (∑ d ∈ (m * n).divisors, (1 : ℝ) / (d : ℝ))
      = ∑ p ∈ m.divisors ×ˢ n.divisors, (1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ) := by
    rw [Nat.Coprime.divisors_mul hmn, Finset.sum_map]
    exact Finset.sum_attach (m.divisors ×ˢ n.divisors)
      (fun p : ℕ × ℕ => (1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ))
  have step2 : (∑ p ∈ m.divisors ×ˢ n.divisors, (1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ))
      = ∑ a ∈ m.divisors, ∑ b ∈ n.divisors, (1 : ℝ) / (a : ℝ) * ((1 : ℝ) / (b : ℝ)) := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Nat.cast_mul]
    exact (one_div_mul_one_div _ _).symm
  have step3 : (∑ a ∈ m.divisors, ∑ b ∈ n.divisors, (1 : ℝ) / (a : ℝ) * ((1 : ℝ) / (b : ℝ)))
      = (∑ d ∈ m.divisors, (1 : ℝ) / (d : ℝ)) * ∑ d ∈ n.divisors, (1 : ℝ) / (d : ℝ) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
  unfold recDiv
  rw [step1, step2, step3]

/-- A truncated geometric series is bounded by its sum: `Σ_{x < n} r^x ≤ 1/(1-r)` for `0 ≤ r < 1`. -/
private lemma geom_partial_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∑ x ∈ range n, r ^ x ≤ 1 / (1 - r) := by
  have hpos : 0 < 1 - r := by linarith
  have hle : (∑ x ∈ range n, r ^ x) * (1 - r) ≤ 1 := by
    rw [geom_sum_mul_neg r n]
    have : 0 ≤ r ^ n := pow_nonneg hr0 n
    linarith
  rw [le_div_iff₀ hpos]
  linarith

/-- The reciprocal divisor sum of a prime power is at most the full geometric series `p/(p-1)`. -/
private lemma recDiv_prime_pow_le (p N : ℕ) (hp : p.Prime) :
    recDiv (p ^ N) ≤ (p : ℝ) / ((p : ℝ) - 1) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  unfold recDiv
  rw [Nat.sum_divisors_prime_pow hp]
  have hcongr : (∑ x ∈ range (N + 1), (1 : ℝ) / (((p ^ x : ℕ) : ℝ)))
      = ∑ x ∈ range (N + 1), ((1 : ℝ) / (p : ℝ)) ^ x := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Nat.cast_pow, one_div_pow]
  rw [hcongr]
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hr0 : 0 ≤ (1 : ℝ) / (p : ℝ) := by positivity
  have hr1 : (1 : ℝ) / (p : ℝ) < 1 := by
    rw [div_lt_one hp0]
    linarith
  have h := geom_partial_le hr0 hr1 (N + 1)
  have heq : (1 : ℝ) / (1 - (1 : ℝ) / (p : ℝ)) = (p : ℝ) / ((p : ℝ) - 1) := by
    have hb : (1 : ℝ) - (1 : ℝ) / (p : ℝ) ≠ 0 := by
      have : (1 : ℝ) - (1 : ℝ) / (p : ℝ) = ((p : ℝ) - 1) / (p : ℝ) := by
        field_simp
      rw [this]
      exact div_ne_zero (by linarith) (ne_of_gt hp0)
    rw [div_eq_div_iff hb (by linarith : (p : ℝ) - 1 ≠ 0)]
    field_simp
  linarith [h, heq]

/-- For squarefree `k`, `Σ_{d ∣ k^N} 1/d ≤ k/φ(k)` for every `N`. -/
private lemma recDiv_pow_le_totient_div (N : ℕ) : ∀ k : ℕ, Squarefree k →
    recDiv (k ^ N) ≤ (k : ℝ) / (Nat.totient k : ℝ) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    rcases Nat.eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hk.ne_zero) with hk1 | hk1
    · rw [hk1.symm]
      simp [recDiv]
    · set p := k.minFac with hpdef
      set m := k / p with hmdef
      have hpprime : p.Prime := by
        rw [hpdef]; exact Nat.minFac_prime (by omega)
      have hpdvd : p ∣ k := by
        rw [hpdef]; exact Nat.minFac_dvd k
      have hkeq : k = p * m := by
        rw [hmdef]; exact (Nat.mul_div_cancel' hpdvd).symm
      have hmlt : m < k := by
        rw [hmdef]; exact Nat.div_lt_self (by omega) hpprime.one_lt
      have hmdvd : m ∣ k := ⟨p, by rw [hkeq, mul_comm]⟩
      have hmsf : Squarefree m := hk.squarefree_of_dvd hmdvd
      have hcop : p.Coprime m := Nat.coprime_of_squarefree_mul (hkeq ▸ hk)
      have hp2R : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpprime.two_le
      have h1nn : 0 ≤ (p : ℝ) / ((p : ℝ) - 1) :=
        div_nonneg (by linarith) (by linarith)
      have hmul := mul_le_mul (recDiv_prime_pow_le p N hpprime) (ih m hmlt hmsf)
        (recDiv_nonneg _) h1nn
      have hpow : k ^ N = p ^ N * m ^ N := by rw [hkeq, mul_pow]
      rw [hpow, recDiv_mul_coprime (hcop.pow N N)]
      refine hmul.trans_eq ?_
      have hkey : (p : ℝ) / ((p : ℝ) - 1) * ((m : ℝ) / (Nat.totient m : ℝ))
          = (k : ℝ) / (Nat.totient k : ℝ) := by
        rw [hkeq, Nat.totient_mul hcop, Nat.totient_prime hpprime, Nat.cast_mul, Nat.cast_mul,
          Nat.cast_sub hpprime.one_le]
        rw [div_mul_div_comm]
        norm_num
      exact hkey

theorem selRadSum_le_totient (y : ℝ) (k : ℕ) (hk : Squarefree k) :
    Work.LinnikAreas.Density4.selRadSum y k ≤ (k : ℝ) / (Nat.totient k : ℝ) := by
  have hk0 : k ≠ 0 := hk.ne_zero
  have hsub : (Finset.Icc 1 ⌊y⌋₊).filter (fun d => SmoothOf d k) ⊆ (k ^ ⌊y⌋₊).divisors := by
    intro d hd
    simp only [Finset.mem_filter, Finset.mem_Icc] at hd
    obtain ⟨⟨hd1, hdN⟩, hsm⟩ := hd
    exact Nat.mem_divisors.mpr ⟨hsm.trans (pow_dvd_pow k hdN), pow_ne_zero _ hk0⟩
  have h1 : selRadSum y k
      = ∑ d ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun d => SmoothOf d k), (1 : ℝ) / (d : ℝ) := rfl
  rw [h1]
  calc ∑ d ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun d => SmoothOf d k), (1 : ℝ) / (d : ℝ)
      ≤ ∑ d ∈ (k ^ ⌊y⌋₊).divisors, (1 : ℝ) / (d : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro i hi hni
        exact div_nonneg zero_le_one (Nat.cast_nonneg _)
    _ ≤ (k : ℝ) / (Nat.totient k : ℝ) := recDiv_pow_le_totient_div ⌊y⌋₊ k hk

end

end Work.LinnikAreas.Density4
