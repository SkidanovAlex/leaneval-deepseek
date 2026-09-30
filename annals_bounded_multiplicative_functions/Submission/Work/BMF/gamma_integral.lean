import Mathlib
import Submission.Work.BMF.adi_basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Polynomial Finset

/-- A single monomial `mu m * X^m`, evaluated at `(q/Qm) * n`, is an integer, under the
situation of the divisibility hypotheses of `gamma_integral`: `mu m` is an explicit rational
combination of `Qm^m` and the denominator `Dfac k m · m! · qj a b m` divides `q^m`. -/
theorem gamma_integral_term {k a b Qm : ℕ} {q : ℕ} {mu : ℕ → ℝ} {m : ℕ} (hm : 1 ≤ m) (n : ℤ)
    (hQm : 1 ≤ Qm)
    (hmu : ∃ z : ℤ, mu m = z * (Qm : ℝ) ^ m /
      (((Dfac k m : ℕ) : ℝ) * ((m.factorial : ℕ) : ℝ) * ((qj a b m : ℕ) : ℝ)))
    (hdiv : (Dfac k m * m.factorial * qj a b m) ∣ q ^ m) :
    ∃ r : ℤ, mu m * (((q : ℝ) / (Qm : ℝ)) * (n : ℝ)) ^ m = (r : ℝ) := by
  obtain ⟨z, hz⟩ := hmu
  obtain ⟨c, hq⟩ := hdiv
  by_cases hDN : Dfac k m * m.factorial * qj a b m = 0
  · -- the denominator vanishes, so `q = 0` and the whole term is `0`
    have hqm : q ^ m = 0 := by rw [hq, hDN, zero_mul]
    have hq0 : q = 0 := by
      by_contra h
      exact absurd hqm (pow_ne_zero m h)
    refine ⟨0, ?_⟩
    rw [hq0]
    simp [zero_pow (by omega : m ≠ 0)]
  · -- the denominator does not vanish: clear it
    have hDNR : ((Dfac k m * m.factorial * qj a b m : ℕ) : ℝ) ≠ 0 := by
      rw [Nat.cast_ne_zero]; exact hDN
    have hprod : ((Dfac k m * m.factorial * qj a b m : ℕ) : ℝ)
        = ((Dfac k m : ℕ) : ℝ) * ((m.factorial : ℕ) : ℝ) * ((qj a b m : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_mul]
    have hDR : ((Dfac k m : ℕ) : ℝ) * ((m.factorial : ℕ) : ℝ) * ((qj a b m : ℕ) : ℝ) ≠ 0 := by
      rw [← hprod]; exact hDNR
    have hQmR : (Qm : ℝ) ≠ 0 := by
      have : Qm ≠ 0 := by omega
      exact_mod_cast this
    have hDfacR : ((Dfac k m : ℕ) : ℝ) ≠ 0 := by
      rw [Nat.cast_ne_zero]; exact ne_of_gt (Dfac_pos k m)
    have hfactR : ((m.factorial : ℕ) : ℝ) ≠ 0 := by
      rw [Nat.cast_ne_zero]; exact ne_of_gt (Nat.factorial_pos m)
    have hqjR : ((qj a b m : ℕ) : ℝ) ≠ 0 := by
      intro h
      exact hDR (by rw [h, mul_zero])
    refine ⟨z * (c : ℤ) * n ^ m, ?_⟩
    rw [hz]
    have hpow : (((q : ℝ) / (Qm : ℝ)) * (n : ℝ)) ^ m
        = ((Dfac k m * m.factorial * qj a b m : ℕ) : ℝ) * (c : ℝ) * (n : ℝ) ^ m
          / (Qm : ℝ) ^ m := by
      have hq' : (q : ℝ) ^ m = ((Dfac k m * m.factorial * qj a b m : ℕ) : ℝ) * (c : ℝ) := by
        rw [← Nat.cast_pow, hq, Nat.cast_mul]
      rw [mul_pow, div_pow, hq']
      ring
    rw [hpow, hprod]
    push_cast
    field_simp [hDfacR, hfactR, hqjR, hQmR]

theorem gamma_integral (k : ℕ) (a b : ℕ) (Qm : ℕ) {q : ℕ} {mu : ℕ → ℝ}
    (hQm : 1 ≤ Qm)
    (hmu : ∀ m ∈ Finset.Icc 1 k, ∃ z : ℤ,
      mu m = z * (Qm : ℝ) ^ m / (((Dfac k m : ℕ) : ℝ) * ((m.factorial : ℕ) : ℝ) *
        (((qj a b m : ℕ) : ℝ))))
    (hdiv : ∀ m ∈ Finset.Icc 1 k, (Dfac k m * m.factorial * qj a b m) ∣ q ^ m) :
    IntegralOn ((q : ℝ) / (Qm : ℝ)) (∑ m ∈ Finset.Icc 1 k, C (mu m) * X ^ m) := by
  intro n
  have hterm : ∀ mm ∈ Finset.Icc 1 k, ∃ r : ℤ,
      mu mm * (((q : ℝ) / (Qm : ℝ)) * (n : ℝ)) ^ mm = (r : ℝ) := by
    intro mm hmm
    exact gamma_integral_term (Finset.mem_Icc.mp hmm).1 n hQm (hmu mm hmm) (hdiv mm hmm)
  refine ⟨∑ mm ∈ Finset.Icc 1 k,
      (if h : mm ∈ Finset.Icc 1 k then Classical.choose (hterm mm h) else 0), ?_⟩
  have heval : (∑ mm ∈ Finset.Icc 1 k, C (mu mm) * X ^ mm).eval
        (((q : ℝ) / (Qm : ℝ)) * (n : ℝ))
      = ∑ mm ∈ Finset.Icc 1 k, mu mm * (((q : ℝ) / (Qm : ℝ)) * (n : ℝ)) ^ mm := by
    rw [Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro mm _
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  rw [heval, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro mm hmm
  rw [dite_eq_left hmm]
  exact Classical.choose_spec (hterm mm hmm)

end Work.BMF
