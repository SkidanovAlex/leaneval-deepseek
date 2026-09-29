import Mathlib

namespace Work.GenShared

open Complex Metric Work.GenShared

/-- For a polynomial `p` and `m ≥ p.natDegree`, the `m`-th iterated derivative of `p` is a
constant polynomial. -/
private lemma iterDeriv_eq_C_of_natDegree_le (p : Polynomial ℂ) (m : ℕ)
    (h : p.natDegree ≤ m) :
    (Polynomial.derivative^[m]) p
      = Polynomial.C (((Polynomial.derivative^[m]) p).coeff 0) := by
  refine Polynomial.eq_C_of_natDegree_le_zero ?_
  have := Polynomial.natDegree_iterate_derivative p m
  rwa [Nat.sub_eq_zero_of_le h] at this

/-- If `p.natDegree = m` then the constant value of the `m`-th iterated derivative is
`m! * leadingCoeff p`, which is nonzero when `p ≠ 0`. -/
private lemma coeff_iterDeriv_zero_eq_factorial_mul_leadingCoeff (p : Polynomial ℂ) {m : ℕ}
    (h : p.natDegree = m) :
    ((Polynomial.derivative^[m]) p).coeff 0 = (m.factorial : ℂ) * p.leadingCoeff := by
  have hcoeff : p.coeff m = p.leadingCoeff := by
    rw [← h]; exact Polynomial.coeff_natDegree
  rw [Polynomial.coeff_iterate_derivative, zero_add, hcoeff, Nat.descFactorial_self, nsmul_eq_mul]

theorem iterate_derivative_C {k : ℕ} (C : Fin k → Polynomial ℂ) (hC : C ≠ 0) :
    ∃ m : ℕ, ∃ c : Fin k → ℂ, c ≠ 0 ∧
      ∀ i, (Polynomial.derivative^[m]) (C i) = Polynomial.C (c i) := by
  -- Some component of `C` is nonzero.
  obtain ⟨j, hj⟩ : ∃ j, C j ≠ 0 := by
    simpa [funext_iff] using hC
  -- `M` is the largest degree occurring among the *nonzero* components.
  let S : Finset (Fin k) := Finset.univ.filter (fun i => C i ≠ 0)
  have memS : ∀ i, i ∈ S ↔ C i ≠ 0 := fun i => by simp [S]
  have hSne : S.Nonempty := ⟨j, (memS j).mpr hj⟩
  obtain ⟨i0, hi0S, hi0max⟩ := Finset.exists_mem_eq_sup S hSne (fun i => (C i).natDegree)
  have hi0ne : C i0 ≠ 0 := (memS i0).mp hi0S
  let M : ℕ := S.sup (fun i => (C i).natDegree)
  have hi0max' : M = (C i0).natDegree := hi0max
  -- Every component has degree at most `M`.
  have hnat : ∀ i, (C i).natDegree ≤ M := by
    intro i
    by_cases hi : C i = 0
    · rw [hi, Polynomial.natDegree_zero]; exact Nat.zero_le M
    · exact Finset.le_sup (s := S) (f := fun i => (C i).natDegree) ((memS i).mpr hi)
  -- Take `m = M` and read off the constant value of each `M`-th derivative.
  refine ⟨M, fun i => ((Polynomial.derivative^[M]) (C i)).coeff 0, ?_, ?_⟩
  · -- the vector of constants is nonzero, witnessed by `i0` (of maximal degree).
    intro hc
    have h1 : ((Polynomial.derivative^[M]) (C i0)).coeff 0 = 0 := by
      simpa using congrFun hc i0
    rw [coeff_iterDeriv_zero_eq_factorial_mul_leadingCoeff (C i0) (m := M) hi0max'.symm] at h1
    have hfac : (M.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero M)
    have hlc : (C i0).leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hi0ne
    exact (mul_ne_zero hfac hlc) h1
  · intro i
    exact iterDeriv_eq_C_of_natDegree_le (C i) M (hnat i)

end Work.GenShared
