import Mathlib

namespace Work.WilkiesH.Norm

/-- The supremum of a function `Fin 2 → α` in a conditionally complete lattice is the maximum of
its two values. -/
lemma max_eq_iSup_fin2 {α : Type*} [ConditionallyCompleteLattice α] (a b : α) :
    max a b = ⨆ i : Fin 2, ![a, b] i :=
  eq_of_forall_ge_iff <| by simp [ciSup_le_iff, Fin.forall_fin_two]

lemma finprod_finitePlace_max {K : Type*} [Field K] [NumberField K]
    {a b : NumberField.RingOfIntegers K} (hb : b ≠ 0) :
    (∏ᶠ v : NumberField.FinitePlace K, max (v (a : K)) (v (b : K)))
      * (Ideal.absNorm (Ideal.span ({(a : NumberField.RingOfIntegers K), b}
          : Set (NumberField.RingOfIntegers K))) : ℝ) = 1 := by
  have hb' : ![a, b] ≠ (0 : Fin 2 → NumberField.RingOfIntegers K) := by
    intro h; exact hb (congrFun h 1)
  have h := NumberField.absNorm_mul_finprod_finitePlace_eq_one (K := K) hb'
  have hrange : Set.range ![a, b] = ({a, b} : Set (NumberField.RingOfIntegers K)) := by
    ext z; simp; tauto
  have hfin : (∏ᶠ v : NumberField.FinitePlace K,
        ⨆ i : Fin 2, v (((![a, b] i : NumberField.RingOfIntegers K) : K)))
      = ∏ᶠ v : NumberField.FinitePlace K, max (v (a : K)) (v (b : K)) := by
    refine finprod_congr fun v => ?_
    have hii : ∀ i : Fin 2, v (((![a, b] i : NumberField.RingOfIntegers K) : K))
        = ![v (a : K), v (b : K)] i := by
      intro i; fin_cases i <;> simp
    rw [show (⨆ i : Fin 2, v (((![a, b] i : NumberField.RingOfIntegers K) : K)))
          = ⨆ i : Fin 2, ![v (a : K), v (b : K)] i from iSup_congr hii]
    exact (max_eq_iSup_fin2 _ _).symm
  rw [hrange, hfin, mul_comm] at h
  exact h

end Work.WilkiesH.Norm
