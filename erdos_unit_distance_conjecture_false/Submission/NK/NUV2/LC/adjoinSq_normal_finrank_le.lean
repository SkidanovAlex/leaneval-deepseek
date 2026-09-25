import Mathlib

namespace NK.NUV2.LC

open Polynomial

/-- A finite-dimensional field extension whose degree over the base is at most `2` is normal:
every minimal polynomial has degree `≤ 2`, and a polynomial of degree `≤ 1` splits while a
polynomial of degree `2` having a root (namely the element itself) splits as well. -/
theorem normal_of_finrank_le_two {K E : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] (h : Module.finrank K E ≤ 2) : Normal K E := by
  rw [normal_iff]
  intro x
  refine ⟨IsIntegral.of_finite K x, ?_⟩
  have hx : (minpoly K x).natDegree ≤ 2 := (minpoly.natDegree_le x).trans h
  by_cases h2 : (minpoly K x).natDegree = 2
  · exact Splits.of_natDegree_eq_two ((natDegree_map _).trans h2)
      ((eval_map_algebraMap _ _).trans (minpoly.aeval K x))
  · exact Splits.of_natDegree_le_one (natDegree_map_le.trans (by omega))

/-- If `y ^ 2 = b` with `b` in the base field, then `K(y)` is a normal extension of `K`
of dimension at most `2`. -/
theorem adjoinSq_normal_finrank_le {K L : Type*} [Field K] [Field L] [Algebra K L]
    (y : L) (b : K) (hy : y * y = algebraMap K L b) [NeZero (2 : K)] :
    Normal K ↥(IntermediateField.adjoin K ({y} : Set L)) ∧
      FiniteDimensional K ↥(IntermediateField.adjoin K ({y} : Set L)) ∧
      Module.finrank K ↥(IntermediateField.adjoin K ({y} : Set L)) ≤ 2 := by
  have hyroot : (aeval y) (X ^ 2 - C b : K[X]) = 0 := by
    simp only [map_sub, map_pow, aeval_X, aeval_C]
    rw [pow_two, hy, sub_self]
  have hmonic : (X ^ 2 - C b : K[X]).Monic := monic_X_pow_sub_C b (by norm_num)
  have hint : IsIntegral K y := ⟨_, hmonic, hyroot⟩
  let _inst_fd : FiniteDimensional K ↥(IntermediateField.adjoin K ({y} : Set L)) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hfin : Module.finrank K ↥(IntermediateField.adjoin K ({y} : Set L)) ≤ 2 := by
    rw [IntermediateField.adjoin.finrank hint]
    calc (minpoly K y).natDegree
        ≤ (X ^ 2 - C b : K[X]).natDegree :=
          Polynomial.natDegree_le_of_dvd (minpoly.dvd K y hyroot) hmonic.ne_zero
      _ ≤ 2 := by
          calc (X ^ 2 - C b : K[X]).natDegree
              ≤ max (X ^ 2 : K[X]).natDegree (C b).natDegree := natDegree_sub_le _ _
            _ = 2 := by simp
  exact ⟨normal_of_finrank_le_two hfin, ‹_›, hfin⟩

end NK.NUV2.LC
