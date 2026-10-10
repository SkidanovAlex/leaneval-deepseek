import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotAS.ASZGen

/-- If `L / K` is a field extension of degree `5` and `T ∈ L` does not lie in the image of `K`,
then any nonzero polynomial `f ∈ K[X]` of degree `≤ 5` with `f(T) = 0` is irreducible.

Indeed `K⟮T⟯` is an intermediate field with `2 ≤ [K⟮T⟯ : K] ∣ [L : K] = 5`, so `[K⟮T⟯ : K] = 5`
and `minpoly K T` has degree `5`; since `minpoly K T ∣ f` and `natDegree f ≤ 5`, the polynomial
`f` is a nonzero constant multiple of the irreducible `minpoly K T`. -/
theorem irreducible_of_root_finrank_five {K L : Type*} [Field K] [Field L] [Algebra K L]
    (hL : Module.finrank K L = 5) (T : L) (hT : T ∉ Set.range (algebraMap K L))
    (f : Polynomial K) (hf0 : f ≠ 0) (hf : Polynomial.aeval T f = 0) (hdeg : f.natDegree ≤ 5) :
    Irreducible f := by
  have hInt : IsIntegral K T := isAlgebraic_iff_isIntegral.mp ⟨f, hf0, hf⟩
  -- `K⟮T⟯` has degree at least `2` over `K`
  have h2 : 2 ≤ Module.finrank K ↥(IntermediateField.adjoin K ({T} : Set L)) := by
    rw [IntermediateField.adjoin.finrank hInt]
    exact (minpoly.two_le_natDegree_iff hInt).mpr hT
  -- and its degree divides `[L : K] = 5`
  have hdvd : Module.finrank K ↥(IntermediateField.adjoin K ({T} : Set L)) ∣ 5 := by
    have h := IntermediateField.finrank_dvd_of_le_right
      (F := IntermediateField.adjoin K ({T} : Set L)) (E := ⊤) le_top
    rw [IntermediateField.finrank_top', hL] at h
    exact h
  have hfin : Module.finrank K ↥(IntermediateField.adjoin K ({T} : Set L)) = 5 := by
    rcases Nat.Prime.eq_one_or_self_of_dvd (by norm_num : Nat.Prime 5) _ hdvd with h | h
    · omega
    · exact h
  have hmin : (minpoly K T).natDegree = 5 := by
    rw [← IntermediateField.adjoin.finrank hInt]; exact hfin
  have hg0 : minpoly K T ≠ 0 := (minpoly.monic hInt).ne_zero
  obtain ⟨q, hq⟩ := minpoly.dvd K T hf
  have hq0 : q ≠ 0 := fun h => hf0 (by rw [hq, h, mul_zero])
  have hfdeg : f.natDegree = 5 := by
    have h1 : (minpoly K T).natDegree ≤ f.natDegree := Polynomial.natDegree_le_of_dvd ⟨q, hq⟩ hf0
    omega
  have hqdeg : q.natDegree = 0 := by
    have hqm := Polynomial.natDegree_mul hg0 hq0
    rw [← hq] at hqm
    omega
  obtain ⟨c, hqC⟩ : ∃ c : K, q = Polynomial.C c :=
    ⟨q.coeff 0, Polynomial.eq_C_of_natDegree_eq_zero hqdeg⟩
  have hc : c ≠ 0 := by
    intro hc0
    exact hq0 (by rw [hqC, hc0, Polynomial.C_0])
  have hf_eq : f = Polynomial.C c * minpoly K T := by
    rw [hq, hqC]; exact mul_comm _ _
  have hunit : IsUnit (Polynomial.C c) := Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)
  have hassoc : Associated (minpoly K T) f :=
    ⟨hunit.unit, by rw [IsUnit.unit_spec hunit, hf_eq]; exact mul_comm _ _⟩
  exact hassoc.irreducible (minpoly.irreducible hInt)

end Work.MotAS.ASZGen
