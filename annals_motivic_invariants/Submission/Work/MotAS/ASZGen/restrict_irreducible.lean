import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotAS.ASZGen

/-- Substituting `f 0 = X` and `f 1 = 0` into a two-variable polynomial cannot increase the
`natDegree`.  This is the specialisation of `MvPolynomial.aeval_natDegree_le` to `n = 1`. -/
private lemma aeval_natDegree_le_of_fin_two {K : Type*} [Field K] (f : Fin 2 → Polynomial K)
    (hf0 : f 0 = Polynomial.X) (hf1 : f 1 = 0) (Q : MvPolynomial (Fin 2) K) :
    (MvPolynomial.aeval f Q).natDegree ≤ Q.totalDegree := by
  have hf : ∀ i : Fin 2, (f i).natDegree ≤ 1 := by
    rw [Fin.forall_fin_two]
    exact ⟨by rw [hf0]; exact le_of_eq Polynomial.natDegree_X, by rw [hf1]; simp⟩
  have := MvPolynomial.aeval_natDegree_le Q le_rfl f hf
  simpa using this

/-- If `φ` is the substitution `X ↦ X`, `Y ↦ 0`, `A B ≠ 0`, `φ A` is a unit, and the product
`φ A * φ B` has degree `5` while `A * B` has total degree at most `5`, then `A` is a unit. -/
private lemma isUnit_of_aeval_isUnit {K : Type*} [Field K] (f : Fin 2 → Polynomial K)
    (hf0 : f 0 = Polynomial.X) (hf1 : f 1 = 0)
    (A B : MvPolynomial (Fin 2) K) (hA : A ≠ 0) (hB : B ≠ 0)
    (hu : IsUnit (MvPolynomial.aeval f A))
    (hnat : (MvPolynomial.aeval f A * MvPolynomial.aeval f B).natDegree = 5)
    (hdeg : (A * B).totalDegree ≤ 5) : IsUnit A := by
  have hne : MvPolynomial.aeval f A * MvPolynomial.aeval f B ≠ 0 := by
    intro h; rw [h] at hnat; simp only [Polynomial.natDegree_zero] at hnat; omega
  have hsum : (MvPolynomial.aeval f A).natDegree + (MvPolynomial.aeval f B).natDegree = 5 := by
    rw [← Polynomial.natDegree_mul (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne)]
    exact hnat
  have hndA : (MvPolynomial.aeval f A).natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
  have hnB : (MvPolynomial.aeval f B).natDegree = 5 := by omega
  have htb : 5 ≤ B.totalDegree := by
    have := aeval_natDegree_le_of_fin_two f hf0 hf1 B
    omega
  have htd : A.totalDegree + B.totalDegree ≤ 5 := by
    rw [MvPolynomial.totalDegree_mul_of_isDomain hA hB] at hdeg
    exact hdeg
  have hAdeg : A.totalDegree = 0 := by omega
  have hAeq : A = MvPolynomial.C (A.coeff 0) :=
    (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp hAdeg
  have hc0 : A.coeff 0 ≠ 0 := by
    intro h0
    exact hA (by rw [hAeq, h0]; simp)
  rw [hAeq]
  exact IsUnit.map (MvPolynomial.C : K →+* MvPolynomial (Fin 2) K) (isUnit_iff_ne_zero.mpr hc0)

/-- Degree argument: a two-variable polynomial of total degree at most `5` whose substitution
`Y ↦ 0` is irreducible of degree `5` is itself irreducible. -/
private lemma restrict_irreducible_aux {K : Type*} [Field K] (f : Fin 2 → Polynomial K)
    (hf0 : f 0 = Polynomial.X) (hf1 : f 1 = 0) (P : MvPolynomial (Fin 2) K)
    (hdeg : P.totalDegree ≤ 5)
    (hirr : Irreducible (MvPolynomial.aeval f P))
    (hnat : (MvPolynomial.aeval f P).natDegree = 5) : Irreducible P := by
  have hφP_ne : MvPolynomial.aeval f P ≠ 0 := by
    intro h; rw [h] at hnat; simp only [Polynomial.natDegree_zero] at hnat; omega
  refine ⟨?_, ?_⟩
  · intro hP
    exact hirr.not_isUnit (IsUnit.map (MvPolynomial.aeval f) hP)
  · intro A B hAB
    have hφAB : MvPolynomial.aeval f P = MvPolynomial.aeval f A * MvPolynomial.aeval f B := by
      rw [hAB, map_mul]
    have hne : MvPolynomial.aeval f A * MvPolynomial.aeval f B ≠ 0 := by
      rw [← hφAB]; exact hφP_ne
    have hnat' : (MvPolynomial.aeval f A * MvPolynomial.aeval f B).natDegree = 5 := by
      rw [← hφAB]; exact hnat
    have hdeg' : (A * B).totalDegree ≤ 5 := by rw [← hAB]; exact hdeg
    have hAnz : A ≠ 0 := fun h => left_ne_zero_of_mul hne (by rw [h]; simp)
    have hBnz : B ≠ 0 := fun h => right_ne_zero_of_mul hne (by rw [h]; simp)
    rcases hirr.isUnit_or_isUnit hφAB with huA | huB
    · exact Or.inl (isUnit_of_aeval_isUnit f hf0 hf1 A B hAnz hBnz huA hnat' hdeg')
    · exact Or.inr (isUnit_of_aeval_isUnit f hf0 hf1 B A hBnz hAnz huB
        (by rw [mul_comm]; exact hnat') (by rw [mul_comm]; exact hdeg'))

theorem restrict_irreducible {K : Type*} [Field K] (P : MvPolynomial (Fin 2) K)
    (hdeg : P.totalDegree ≤ 5)
    (hirr : Irreducible (MvPolynomial.aeval (fun i : Fin 2 =>
        if i = 0 then (Polynomial.X : Polynomial K) else 0) P))
    (hnat : (MvPolynomial.aeval (fun i : Fin 2 =>
        if i = 0 then (Polynomial.X : Polynomial K) else 0) P).natDegree = 5) :
    Irreducible P := by
  refine restrict_irreducible_aux (fun i : Fin 2 =>
    if i = 0 then (Polynomial.X : Polynomial K) else 0) ?_ ?_ P hdeg hirr hnat
  · simp
  · simp

end Work.MotAS.ASZGen
