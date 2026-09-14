import Mathlib.Algebra.Module.ZLattice.Basic

namespace Commons.LinearAlgebra.Independence

/-- The values (in the ambient real vector space `E`) of a `ℤ`-basis of a discrete
`ℤ`-submodule `ℒ` of a finite-dimensional real vector space are linearly independent
over `ℝ`.

PROOF. Let `v i := (b i : E)`.  Since `b` is a basis of `ℒ`, the `ℤ`-span of `Set.range v`
is `ℒ` itself, which is discrete by hypothesis.  Hence, by
`Real.finrank_eq_int_finrank_of_discrete`, the `ℝ`-dimension of the `ℝ`-span of
`Set.range v` equals the `ℤ`-rank of `ℒ`, namely `m`.  A family of `m` vectors spanning
an `m`-dimensional space is linearly independent, by
`linearIndependent_iff_card_eq_finrank_span`. -/
theorem discrete_basis_values_linIndep {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (ℒ : Submodule ℤ E) [DiscreteTopology ℒ] {m : ℕ}
    (b : Module.Basis (Fin m) ℤ ℒ) :
    LinearIndependent ℝ (fun i : Fin m => ((b i : ℒ) : E)) := by
  let v : Fin m → E := fun i => ((b i : ℒ) : E)
  have hrange : Set.range v = ℒ.subtype '' Set.range b := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨b i, ⟨i, rfl⟩, ?_⟩
      simp [v]
    · rintro ⟨y, ⟨i, rfl⟩, hx⟩
      refine ⟨i, ?_⟩
      simpa [v, Submodule.subtype_apply] using hx
  have hspan : Submodule.span ℤ (Set.range v) = ℒ := by
    calc
      Submodule.span ℤ (Set.range v) = Submodule.span ℤ (ℒ.subtype '' Set.range b) := by
        rw [hrange]
      _ = Submodule.map ℒ.subtype (Submodule.span ℤ (Set.range b)) := by
        rw [Submodule.map_span]
      _ = Submodule.map ℒ.subtype ⊤ := by rw [b.span_eq]
      _ = ℒ := by
        rw [Submodule.map_top, Submodule.range_subtype]
  have hdisc : DiscreteTopology (Submodule.span ℤ (Set.range v)) := by
    rw [hspan]
    infer_instance
  have hfinℤ : Module.finrank ℤ ℒ = m := by
    simpa using (Module.finrank_eq_card_basis (R := ℤ) (M := ℒ) b)
  have hfinℝ : Module.finrank ℝ (Submodule.span ℝ (Set.range v)) = m := by
    have hset := Real.finrank_eq_int_finrank_of_discrete (E := E) (s := Set.range v) hdisc
    rw [Set.finrank, Set.finrank] at hset
    rw [hspan] at hset
    exact hset.trans hfinℤ
  simpa [v] using (linearIndependent_iff_card_eq_finrank_span (R := ℝ) (M := E) (b := v)).2
    (by simpa [Set.finrank] using hfinℝ.symm)

end Commons.LinearAlgebra.Independence
