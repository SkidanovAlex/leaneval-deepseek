import Mathlib
import Submission.Commons.Analysis.ExponentialSums.large_sieve

namespace Commons.Analysis.ExponentialSums

/-- The finite set of reduced pairs `(q, r)` with `1 ≤ q ≤ Q`, `1 ≤ r ≤ q`, `(r,q) = 1`,
viewed as pairs `(q, r)` of natural numbers. -/
private def arithSet (Q : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Finset.Icc 1 Q).sigma (fun q => (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q))

/-- The reduced fraction `r/q` attached to a pair `(q, r)`. -/
private noncomputable def fracPhase (p : Σ _ : ℕ, ℕ) : ℝ := (p.2 : ℝ) / (p.1 : ℝ)

/-- Two reduced fractions `r/q` and `r'/q'` with `q, q' ≤ Q` and both distinct are
`1/Q^2`-separated from every integer multiple. -/
private lemma coprime_frac_eq {q r q' r' : ℕ} (hr : 1 ≤ r) (hrq : r ≤ q)
    (hcop : Nat.Coprime r q) (hr' : 1 ≤ r') (hrq' : r' ≤ q') (hcop' : Nat.Coprime r' q')
    (h : r * q' = r' * q) : q = q' ∧ r = r' := by
  have hq0 : 0 < q := by omega
  have hq'0 : 0 < q' := by omega
  have hqq' : q ∣ q' := Nat.Coprime.dvd_of_dvd_mul_left hcop.symm ⟨r', by rw [h, mul_comm]⟩
  have hq'q : q' ∣ q := Nat.Coprime.dvd_of_dvd_mul_left hcop'.symm ⟨r, by rw [← h, mul_comm]⟩
  have heq : q = q' := Nat.dvd_antisymm hqq' hq'q
  refine ⟨heq, ?_⟩
  have h2 : r * q' = r' * q' := by rw [h, heq]
  exact Nat.mul_right_cancel hq'0 h2

private lemma frac_sep (Q : ℕ) {q r q' r' : ℕ}
    (hq : q ∈ Finset.Icc 1 Q) (hr : r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q))
    (hq' : q' ∈ Finset.Icc 1 Q) (hr' : r' ∈ (Finset.Icc 1 q').filter (fun r => Nat.Coprime r q'))
    (hne : ¬(q = q' ∧ r = r')) (k : ℤ) :
    (1/(Q:ℝ)^2 : ℝ) ≤ |(r:ℝ)/(q:ℝ) - (r':ℝ)/(q':ℝ) - (k:ℝ)| := by
  obtain ⟨hqa, hqb⟩ := Finset.mem_Icc.mp hq
  obtain ⟨hrmem, hcop⟩ := Finset.mem_filter.mp hr
  obtain ⟨hra, hrb⟩ := Finset.mem_Icc.mp hrmem
  obtain ⟨hq'a, hq'b⟩ := Finset.mem_Icc.mp hq'
  obtain ⟨hr'mem, hcop'⟩ := Finset.mem_filter.mp hr'
  obtain ⟨hr'a, hr'b⟩ := Finset.mem_Icc.mp hr'mem
  have hqpos : 0 < q := by omega
  have hq'pos : 0 < q' := by omega
  have hqR : (0:ℝ) < q := by exact_mod_cast hqpos
  have hq'R : (0:ℝ) < q' := by exact_mod_cast hq'pos
  have hqne : (q:ℝ) ≠ 0 := ne_of_gt hqR
  have hq'ne : (q':ℝ) ≠ 0 := ne_of_gt hq'R
  set M : ℤ := (r:ℤ)*(q':ℤ) - (r':ℤ)*(q:ℤ) - k*(q:ℤ)*(q':ℤ) with hM
  have hA : (r:ℝ)/(q:ℝ) - (r':ℝ)/(q':ℝ) - (k:ℝ) = ((M:ℤ):ℝ) / ((q:ℝ)*(q':ℝ)) := by
    rw [hM]; push_cast; field_simp
  have hMne : M ≠ 0 := by
    intro hM0
    have hc : ((M:ℤ):ℝ) = 0 := by rw [hM0]; simp
    rw [hM] at hc; push_cast at hc
    have hident : (r:ℝ)/(q:ℝ) - (r':ℝ)/(q':ℝ) = (k:ℝ) := by
      field_simp; linarith [hc]
    have hrqpos : 0 < (r:ℝ)/(q:ℝ) := by positivity
    have hrqle : (r:ℝ)/(q:ℝ) ≤ 1 := by rw [div_le_one hqR]; exact_mod_cast hrb
    have hr'q'pos : 0 < (r':ℝ)/(q':ℝ) := by positivity
    have hr'q'le : (r':ℝ)/(q':ℝ) ≤ 1 := by rw [div_le_one hq'R]; exact_mod_cast hr'b
    have hklt : |(k:ℝ)| < 1 := by
      rw [← hident, abs_lt]
      constructor <;> linarith
    have hk0 : k = 0 := by
      have hz : |k| < 1 := by
        have : ((|k| : ℤ) : ℝ) < 1 := by rw [Int.cast_abs]; exact hklt
        exact_mod_cast this
      exact Int.abs_lt_one_iff.mp hz
    have hrat : (r:ℝ)/(q:ℝ) = (r':ℝ)/(q':ℝ) := by
      rw [hk0] at hident
      exact sub_eq_zero.mp (by simpa using hident)
    have hcross : r * q' = r' * q := by
      have hreal : (r:ℝ)*(q':ℝ) = (r':ℝ)*(q:ℝ) := by
        field_simp at hrat; linarith
      exact_mod_cast hreal
    exact hne (coprime_frac_eq hra hrb hcop hr'a hr'b hcop' hcross)
  have hMabs : (1:ℝ) ≤ |((M:ℤ):ℝ)| := by
    have h := Int.one_le_abs hMne
    rw [← Int.cast_abs]
    exact_mod_cast h
  have hden : (0:ℝ) < (q:ℝ)*(q':ℝ) := by positivity
  have hQQ : (q:ℝ)*(q':ℝ) ≤ (Q:ℝ)^2 := by
    have h1 : (q:ℝ) ≤ Q := by exact_mod_cast hqb
    have h2 : (q':ℝ) ≤ Q := by exact_mod_cast hq'b
    have h3 : (0:ℝ) ≤ Q := by positivity
    nlinarith [h1, h2, hqR, hq'R, h3]
  calc (1/(Q:ℝ)^2 : ℝ) = 1/((Q:ℝ)*(Q:ℝ)) := by rw [pow_two]
    _ ≤ 1/((q:ℝ)*(q':ℝ)) := one_div_le_one_div_of_le hden (by rw [pow_two] at hQQ; exact hQQ)
    _ ≤ |((M:ℤ):ℝ) / ((q:ℝ)*(q':ℝ))| := by
        rw [abs_div, abs_of_pos hden]
        exact div_le_div_of_nonneg_right hMabs (le_of_lt hden)
    _ = |(r:ℝ)/(q:ℝ) - (r':ℝ)/(q':ℝ) - (k:ℝ)| := by rw [hA]

theorem arithmetic_large_sieve (Q N : ℕ) (hQ : 1 ≤ Q) (a : ℕ → ℂ) :
    (∑ q ∈ Finset.Icc 1 Q, ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
        ‖∑ n ∈ Finset.Icc 1 N, a n * Commons.Analysis.ExponentialSums.ch ((n : ℝ) * (r : ℝ) / q)‖ ^ 2)
      ≤ (N + Q ^ 2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) := by
  classical
  have hδ : (0:ℝ) < 1/(Q:ℝ)^2 := by
    have hQ0 : (0:ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
    positivity
  have hsep : ∀ p p' : ↥(arithSet Q), p ≠ p' → ∀ k : ℤ,
      (1/(Q:ℝ)^2 : ℝ) ≤ |fracPhase ↑p - fracPhase ↑p' - (k:ℝ)| := by
    intro p p' hne k
    obtain ⟨p0, hp0⟩ := p
    obtain ⟨p0', hp0'⟩ := p'
    obtain ⟨q, r⟩ := p0
    obtain ⟨q', r'⟩ := p0'
    simp only [arithSet] at hp0 hp0'
    obtain ⟨hq, hr⟩ := Finset.mem_sigma.mp hp0
    obtain ⟨hq', hr'⟩ := Finset.mem_sigma.mp hp0'
    have hne' : ¬(q = q' ∧ r = r') := by
      rintro ⟨h1, h2⟩
      exact hne (by subst h1; subst h2; rfl)
    show (1/(Q:ℝ)^2 : ℝ) ≤ |(r:ℝ)/(q:ℝ) - (r':ℝ)/(q':ℝ) - (k:ℝ)|
    exact frac_sep Q hq hr hq' hr' hne' k
  have hmain := large_sieve (fun p : ↥(arithSet Q) => fracPhase ↑p) hδ hsep N a
  have hδinv : (1 / (1/(Q:ℝ)^2) : ℝ) = (Q:ℝ)^2 := by rw [one_div, one_div, inv_inv]
  rw [hδinv] at hmain
  have hsum : (∑ p : ↥(arithSet Q), ‖∑ n ∈ Finset.Icc 1 N, a n * ch ((n:ℝ) * fracPhase ↑p)‖^2)
      = (∑ q ∈ Finset.Icc 1 Q, ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          ‖∑ n ∈ Finset.Icc 1 N, a n * ch ((n : ℝ) * (r : ℝ) / q)‖ ^ 2) := by
    rw [Finset.sum_coe_sort (arithSet Q) (fun x : Σ _ : ℕ, ℕ =>
        ‖∑ n ∈ Finset.Icc 1 N, a n * ch ((n:ℝ) * fracPhase x)‖^2)]
    simp only [arithSet]
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl (fun q hq => Finset.sum_congr rfl (fun r hr => ?_))
    simp only [fracPhase]
    congr 1
    congr 1
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [mul_div_assoc]
  rw [hsum] at hmain
  exact hmain

end Commons.Analysis.ExponentialSums
