import Mathlib

namespace Work.Fatou.Analysis

open Polynomial

/-- An injective polynomial over `ℂ` (i.e. one whose evaluation map is injective)
has degree at most `1`.

Proof by contradiction: if `p.natDegree ≥ 2`, pick `r` with `p.derivative.eval r ≠ 0`.
Then `q = p - C (p.eval r)` has degree `≥ 2` and root `r`, so `q = (X - C r) * S` with
`S` nonconstant. Since `S` is a nonconstant complex polynomial it has a root `w`, which
cannot equal `r` because `S.eval r = p.derivative.eval r ≠ 0`. But `q.eval w = 0` gives
`p.eval w = p.eval r`, contradicting injectivity. -/
lemma injPolynomialNatDegreeLeOne (p : Polynomial ℂ)
    (hinj : ∀ z w : ℂ, p.eval z = p.eval w → z = w) : p.natDegree ≤ 1 := by
  by_contra h
  rw [not_le] at h
  -- The derivative of a polynomial of degree ≥ 2 is nonzero.
  have hderiv : p.derivative ≠ 0 := by
    intro hd
    have : p.natDegree = 0 := Polynomial.derivative_eq_zero.mp hd
    omega
  -- Hence there is a point where the derivative does not vanish.
  obtain ⟨r, hr⟩ : ∃ r, p.derivative.eval r ≠ 0 := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    exact hderiv (Polynomial.funext (fun z => by simpa using hc z))
  set q : Polynomial ℂ := p - C (p.eval r) with hq
  have hqnat : q.natDegree = p.natDegree := by rw [hq, Polynomial.natDegree_sub_C]
  have hqroot : q.eval r = 0 := by
    rw [hq]; simp
  have hqne : q ≠ 0 := by
    intro h0
    rw [h0] at hqnat
    simp at hqnat
    omega
  have hdvd : (X - C r) ∣ q := by
    rw [Polynomial.dvd_iff_isRoot]
    exact hqroot
  obtain ⟨S, hS⟩ := hdvd
  have hXnz : (X - C r : Polynomial ℂ) ≠ 0 := Polynomial.X_sub_C_ne_zero r
  have hSne : S ≠ 0 := by
    intro hS0
    have : q = 0 := by rw [hS, hS0, mul_zero]
    exact hqne this
  -- `S` is nonconstant
  have hdegS : S.natDegree = p.natDegree - 1 := by
    have hmul := Polynomial.natDegree_mul hXnz hSne
    rw [Polynomial.natDegree_X_sub_C, ← hS, hqnat] at hmul
    omega
  -- so it has a root `w`
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_root S (by
    rw [Polynomial.degree_eq_natDegree hSne]
    have : S.natDegree ≠ 0 := by omega
    simpa using this)
  have hweval : p.eval w = p.eval r := by
    have hq0 : q.eval w = 0 := by
      simp [hS, Polynomial.IsRoot.def.mp hw]
    rw [hq] at hq0
    simp only [Polynomial.eval_sub, Polynomial.eval_C] at hq0
    exact sub_eq_zero.mp hq0
  have hwr : w = r := hinj w r hweval
  -- `S.eval r` is the derivative of `p` at `r`, hence nonzero, so `w ≠ r`.
  have hSr : S.eval r = p.derivative.eval r := by
    have hd : q.derivative = S + (X - C r) * S.derivative := by
      rw [hS, Polynomial.derivative_mul, Polynomial.derivative_X_sub_C, one_mul]
    have h2 := congrArg (fun f : Polynomial ℂ => f.eval r) hd
    rw [hq, Polynomial.derivative_sub, Polynomial.derivative_C, sub_zero] at h2
    simp only [Polynomial.eval_add, Polynomial.eval_mul] at h2
    simp at h2
    exact h2.symm
  have : p.derivative.eval r = 0 := by
    rw [← hSr, ← hwr]
    exact Polynomial.IsRoot.def.mp hw
  exact hr this

end Work.Fatou.Analysis
