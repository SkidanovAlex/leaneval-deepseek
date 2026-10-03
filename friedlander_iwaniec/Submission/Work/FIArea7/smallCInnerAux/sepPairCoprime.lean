import Mathlib
import Submission.Work.FIArea7.SepDiv
import Submission.Work.FIArea7.sepPair_squarefree

set_option linter.unusedVariables false

namespace Work.FIArea7.smallCInnerAux

/-- **The separation triple consists of pairwise coprime squarefree numbers.**  For a *FI* §24
separation triple `(d,m,n)` of a squarefree `ℓ = d·m·n` (the three parts of the decreasing prime
list over the disjoint index sets `dIdx`, `mIdx`, `nIdx`), the numbers `d, m, n` are pairwise
coprime and each is squarefree (indeed `d·m·n` is squarefree), and all three are positive.

This is what makes `μ` and the sieve indicator multiplicative over the triple:
`μ(d·m·n) = μ(d)μ(m)μ(n)` and `nspInd Pa (d·m·n) = nspInd Pa d · nspInd Pa m · nspInd Pa n`
(`Work.FIArea7.nspInd_mul`), and it splits the coprimality condition
`(c, d·m·n) = 1` into `(c,d) = (c,m) = (c,n) = 1`. -/
theorem sepPairCoprime {r d m n : ℕ} (hr : 2 ≤ r) (h : Work.FIArea7.IsSepPair r d m n) :
    0 < d ∧ 0 < m ∧ 0 < n ∧ Nat.Coprime d m ∧ Nat.Coprime d n ∧ Nat.Coprime m n ∧
      Squarefree d ∧ Squarefree m ∧ Squarefree n ∧ Squarefree (d * m * n) := by
  obtain ⟨k, p, hpl, hd, hm, hn⟩ := h
  obtain ⟨hanti, hprime, hprod⟩ := hpl
  have hN : Squarefree (d * m * n) :=
    sepPair_squarefree ⟨k, p, ⟨hanti, hprime, hprod⟩, hd, hm, hn⟩
  -- positivity of the three factors
  have hpos_d : 0 < d := by rw [hd]; exact Finset.prod_pos fun i _ => (hprime i).pos
  have hpos_m : 0 < m := by rw [hm]; exact Finset.prod_pos fun i _ => (hprime i).pos
  have hpos_n : 0 < n := by rw [hn]; exact Finset.prod_pos fun i _ => (hprime i).pos
  -- divisibility of each factor (and each partial product) into the whole
  have hd_dvd : d ∣ d * m * n := by rw [mul_assoc]; exact dvd_mul_right d (m * n)
  have hm_dvd : m ∣ d * m * n := dvd_mul_of_dvd_left (dvd_mul_left m d) n
  have hn_dvd : n ∣ d * m * n := dvd_mul_left n (d * m)
  have hdm_dvd : d * m ∣ d * m * n := dvd_mul_right (d * m) n
  have hdn_dvd : d * n ∣ d * m * n := by
    rw [mul_assoc]; exact mul_dvd_mul_left d (dvd_mul_left n m)
  have hmn_dvd : m * n ∣ d * m * n := by
    rw [mul_assoc]; exact dvd_mul_left (m * n) d
  -- squarefreeness of everything
  have hsf_d : Squarefree d := hN.squarefree_of_dvd hd_dvd
  have hsf_m : Squarefree m := hN.squarefree_of_dvd hm_dvd
  have hsf_n : Squarefree n := hN.squarefree_of_dvd hn_dvd
  -- pairwise coprimality: a squarefree product of two factors forces the factors to be coprime
  have hcdm : Nat.Coprime d m :=
    Nat.coprime_iff_isRelPrime.mpr
      (IsRelPrime.of_squarefree_mul (hN.squarefree_of_dvd hdm_dvd))
  have hcdn : Nat.Coprime d n :=
    Nat.coprime_iff_isRelPrime.mpr
      (IsRelPrime.of_squarefree_mul (hN.squarefree_of_dvd hdn_dvd))
  have hcmn : Nat.Coprime m n :=
    Nat.coprime_iff_isRelPrime.mpr
      (IsRelPrime.of_squarefree_mul (hN.squarefree_of_dvd hmn_dvd))
  exact ⟨hpos_d, hpos_m, hpos_n, hcdm, hcdn, hcmn, hsf_d, hsf_m, hsf_n, hN⟩

end Work.FIArea7.smallCInnerAux
