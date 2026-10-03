import Mathlib
import Submission.Work.KMTPlan.A6.ConcAux.Defs

-- the (redundant) hypotheses `hroot`, `h1` of the statement are not used by the proof
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6.ConcAux

open Polynomial Work.KMTPlan.A6.ConcAux

/-- The coefficients of `∑_{j ≤ N} C (c j) * X^j`. -/
private lemma coeff_sum_C_mul_X_pow (N : ℕ) (c : ℕ → ℤ) (i : ℕ) :
    ((∑ j ∈ Finset.range (N + 1), C (c j) * X ^ j : ℤ[X])).coeff i
      = if i ≤ N then c i else 0 := by
  by_cases hi : i ≤ N
  · rw [if_pos hi, finsetSum_coeff, Finset.sum_eq_single i]
    · rw [coeff_C_mul_X_pow, if_pos rfl]
    · intro b _ hbi
      rw [coeff_C_mul_X_pow, if_neg (Ne.symm hbi)]
    · intro hmem
      exact absurd (Finset.mem_range.mpr (by omega : i < N + 1)) hmem
  · rw [if_neg hi, finsetSum_coeff, Finset.sum_eq_zero]
    intro b hb
    have hb' : b < N + 1 := Finset.mem_range.mp hb
    rw [coeff_C_mul_X_pow, if_neg (fun h => by
      subst h
      omega)]

/-- **The rescaling normal form.**  Let `p` be prime, `H ∈ ℤ[X]`, `r ∈ ℤ` and `s ≥ 1` the smallest
index with `p ∤ taylorCoeff H r s` (all the lower Taylor coefficients of `H` at `r`, including the
value `H r`, being divisible by `p`).  Then the rescaled polynomial `rescale p H r = H(r + pX)/p`
factors as `p ^ a` times a polynomial `Ŵ` which is "as `p`-primitive as the `p^s`-divisibility of
`rescale p H r` allows": some coefficient of `Ŵ` is not divisible by `p`, and every coefficient of
`Ŵ` of index `> s` is divisible by `p`. -/
theorem rescale_bound (p : ℕ) [Fact p.Prime] (H : ℤ[X]) (r : ℤ) (s : ℕ)
    (hs : 1 ≤ s) (hroot : (p : ℤ) ∣ H.eval r)
    (h1 : ∀ i, i < s → (p : ℤ) ∣ taylorCoeff H r i)
    (h2 : ¬ ((p : ℤ) ∣ taylorCoeff H r s)) :
    ∃ a : ℕ, ∃ Ŵ : ℤ[X], rescale p H r = C ((p : ℤ) ^ a) * Ŵ ∧
      (∃ i, ¬ (p : ℤ) ∣ Ŵ.coeff i) ∧ (∀ i, s < i → (p : ℤ) ∣ Ŵ.coeff i) := by
  classical
  have hp0 : (p : ℤ) ≠ 0 := by
    have h2p : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast (Fact.out (p := p.Prime)).two_le
    omega
  -- `P n` says that `p ^ n` divides every coefficient of the rescaled polynomial.
  let P : ℕ → Prop := fun n => ∀ i, (p : ℤ) ^ n ∣ (rescale p H r).coeff i
  have hP0 : P 0 := by intro i; simp
  -- `P s` fails: the coefficient of index `s` is `taylorCoeff H r s * p ^ (s-1)`.
  have hPs : ¬ P s := by
    intro hcon
    have hcoe := hcon s
    rw [rescale_coeff_of_pos p H r hs] at hcoe
    obtain ⟨k, hk⟩ := hcoe
    have hpow : (p : ℤ) ^ s = (p : ℤ) ^ (s - 1) * (p : ℤ) := by
      rw [← pow_succ, Nat.sub_add_cancel hs]
    rw [hpow] at hk
    have hcancel : taylorCoeff H r s = (p : ℤ) * k := by
      have hne : (p : ℤ) ^ (s - 1) ≠ 0 := pow_ne_zero _ hp0
      refine mul_left_cancel₀ hne ?_
      calc (p : ℤ) ^ (s - 1) * taylorCoeff H r s
          = taylorCoeff H r s * (p : ℤ) ^ (s - 1) := by ring
        _ = (p : ℤ) ^ (s - 1) * (p : ℤ) * k := hk
        _ = (p : ℤ) ^ (s - 1) * ((p : ℤ) * k) := by ring
    exact h2 ⟨k, hcancel⟩
  -- `a` = the largest exponent with `p ^ a` dividing all coefficients of `rescale p H r`.
  set a : ℕ := Nat.findGreatest P s with ha_def
  have haP : P a := by
    rw [ha_def]
    exact Nat.findGreatest_spec (Nat.zero_le s) hP0
  have ha_le : a ≤ s := by
    rw [ha_def]; exact Nat.findGreatest_le s
  have ha_lt : a < s := lt_of_le_of_ne ha_le (fun h => hPs (h ▸ haP))
  have hnotPa1 : ¬ P (a + 1) :=
    Nat.findGreatest_is_greatest (P := P) (n := s) (k := a + 1)
      (by rw [ha_def]; exact Nat.lt_succ_self a) (by omega)
  have hnot : ∃ i, ¬ (p : ℤ) ^ (a + 1) ∣ (rescale p H r).coeff i := by
    by_contra hc
    exact hnotPa1 (fun i => by
      by_contra hi
      exact hc ⟨i, hi⟩)
  obtain ⟨i₀, hi₀⟩ := hnot
  -- divide coefficientwise by `p ^ a`
  set Ŵ : ℤ[X] := ∑ i ∈ Finset.range ((rescale p H r).natDegree + 1),
      C ((rescale p H r).coeff i / (p : ℤ) ^ a) * X ^ i with hW_def
  have hWcoeff : ∀ i, Ŵ.coeff i = (rescale p H r).coeff i / (p : ℤ) ^ a := by
    intro i
    rw [hW_def]
    by_cases hi : i ≤ (rescale p H r).natDegree
    · rw [coeff_sum_C_mul_X_pow, if_pos hi]
    · rw [coeff_sum_C_mul_X_pow, if_neg hi,
        coeff_eq_zero_of_natDegree_lt (not_le.mp hi)]
      simp
  have hpPa : ∀ i, (p : ℤ) ^ a ∣ (rescale p H r).coeff i := haP
  have hmain : rescale p H r = C ((p : ℤ) ^ a) * Ŵ := by
    apply Polynomial.ext
    intro i
    rw [coeff_C_mul, hWcoeff i]
    by_cases hi : i ≤ (rescale p H r).natDegree
    · exact (Int.mul_ediv_cancel' (hpPa i)).symm
    · rw [coeff_eq_zero_of_natDegree_lt (not_le.mp hi)]
      simp
  refine ⟨a, Ŵ, hmain, ?_, ?_⟩
  · -- some coefficient of `Ŵ` is not divisible by `p`
    refine ⟨i₀, ?_⟩
    intro hdiv
    apply hi₀
    have hci : (rescale p H r).coeff i₀ = (p : ℤ) ^ a * Ŵ.coeff i₀ := by
      rw [hmain, coeff_C_mul]
    rw [hci, pow_succ]
    exact mul_dvd_mul_left _ hdiv
  · -- the coefficients of `Ŵ` of index `> s` are divisible by `p`
    intro i hi
    have hi1 : 1 ≤ i := by omega
    have hci : (p : ℤ) ^ a * Ŵ.coeff i = (rescale p H r).coeff i := by
      rw [hmain, coeff_C_mul]
    have hne : (p : ℤ) ^ a ≠ 0 := pow_ne_zero _ hp0
    have hexp : a + ((i - 1) - a) = i - 1 := by omega
    have hq : (p : ℤ) ^ (i - 1) = (p : ℤ) ^ a * (p : ℤ) ^ ((i - 1) - a) := by
      rw [← pow_add, hexp]
    have hw : Ŵ.coeff i = taylorCoeff H r i * (p : ℤ) ^ ((i - 1) - a) := by
      refine mul_left_cancel₀ hne ?_
      calc (p : ℤ) ^ a * Ŵ.coeff i
          = (rescale p H r).coeff i := hci
        _ = taylorCoeff H r i * (p : ℤ) ^ (i - 1) :=
            rescale_coeff_of_pos p H r hi1
        _ = taylorCoeff H r i * ((p : ℤ) ^ a * (p : ℤ) ^ ((i - 1) - a)) := by rw [hq]
        _ = (p : ℤ) ^ a * (taylorCoeff H r i * (p : ℤ) ^ ((i - 1) - a)) := by ring
    refine ⟨(p : ℤ) ^ ((i - 1) - a - 1) * taylorCoeff H r i, ?_⟩
    rw [hw]
    have hk : 1 ≤ (i - 1) - a := by omega
    have hstep : (p : ℤ) ^ ((i - 1) - a) = (p : ℤ) ^ ((i - 1) - a - 1) * (p : ℤ) := by
      rw [← pow_succ, Nat.sub_add_cancel hk]
    rw [hstep]
    ring

end Work.KMTPlan.A6.ConcAux
