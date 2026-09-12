import Mathlib.RingTheory.MvPolynomial.Ideal

namespace Commons.Algebra.MvPolynomial

/-- The ideal of variables of `MvPolynomial (Fin m) k` is the kernel of the constant coefficient
map. -/
lemma idealOfVars_eq_ker_constantCoeff {k : Type} [Field k] {m : ℕ} :
    MvPolynomial.idealOfVars (Fin m) k = RingHom.ker MvPolynomial.constantCoeff := by
  ext x
  rw [MvPolynomial.idealOfVars, RingHom.mem_ker, MvPolynomial.constantCoeff_eq,
    show Set.range (MvPolynomial.X : Fin m → MvPolynomial (Fin m) k)
      = MvPolynomial.X '' (Set.univ : Set (Fin m)) from by ext; simp,
    MvPolynomial.mem_ideal_span_X_image]
  constructor
  · intro h
    by_contra hc
    obtain ⟨i, -, hi⟩ := h 0 (MvPolynomial.mem_support_iff.mpr hc)
    exact hi (by simp)
  · intro h m' hm'
    have hm0 : m' ≠ 0 := by
      intro h0
      exact (MvPolynomial.mem_support_iff.mp hm') (by rw [h0]; exact h)
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hm0
    exact ⟨i, Set.mem_univ i, hi⟩

theorem idealOfVars_isMaximal {k : Type} [Field k] {m : ℕ} :
    (MvPolynomial.idealOfVars (Fin m) k).IsMaximal := by
  rw [idealOfVars_eq_ker_constantCoeff]
  exact RingHom.ker_isMaximal_of_surjective MvPolynomial.constantCoeff
    (fun x => ⟨MvPolynomial.C x, by simp⟩)

end Commons.Algebra.MvPolynomial