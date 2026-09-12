import Mathlib.Algebra.Module.ZLattice.Basic
import Submission.Commons.Lattice.SuccessiveMinima.Basic

namespace Commons.Lattice.SuccessiveMinima

/-- The finite-index case of `linearIndependent_real_of_int`: a `ℤ`-linearly independent
finite family in a discrete `ℤ`-submodule `L ≤ E` (`E` a finite-dimensional real inner product
space) is `ℝ`-linearly independent in `E`.

Proof: the family spans a discrete `ℤ`-submodule `N = span ℤ (range w)`, whose `ℤ`-rank equals
the cardinality of the index set; by `Real.finrank_eq_int_finrank_of_discrete` the `ℝ`-rank of
the range equals its `ℤ`-rank, hence the cardinality, which characterises linear independence
over `ℝ`. -/
lemma linearIndependent_real_of_int_fintype {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]
    {ι : Type*} [Fintype ι] (w : ι → L) (hw : LinearIndependent ℤ w) :
    LinearIndependent ℝ (fun i => (w i : E)) := by
  let v : ι → E := fun i => (w i : E)
  -- the images in `E` are still `ℤ`-linearly independent
  have hZ : LinearIndependent ℤ v := hw.map' L.subtype (Submodule.ker_subtype L)
  -- hence the `ℤ`-rank of the range equals the cardinality of the index set
  have hcardZ : Set.finrank ℤ (Set.range v) = Fintype.card ι :=
    finrank_span_eq_card hZ
  -- the `ℤ`-span of the range is a submodule of the discrete lattice `L`, so it is discrete
  have hdisc : DiscreteTopology (Submodule.span ℤ (Set.range v)) := by
    rw [← SetLike.isDiscrete_iff_discreteTopology]
    refine (inferInstance : DiscreteTopology L).isDiscrete.mono ?_
    rw [SetLike.coe_subset_coe, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (w i).2
  -- discreteness forces the `ℝ`-rank and the `ℤ`-rank of the range to agree
  have hEq := Real.finrank_eq_int_finrank_of_discrete hdisc
  have hcardR : Set.finrank ℝ (Set.range v) = Fintype.card ι := by
    rw [hEq]
    exact hcardZ
  exact linearIndependent_iff_card_eq_finrank_span.mpr hcardR.symm

/-- A `ℤ`-linearly independent family in a full `ℤ`-lattice `L ≤ E` (`E` a finite-dimensional
real inner product space) is `ℝ`-linearly independent in `E`: coordinates in a `ℤ`-basis of `L`
are integer vectors, and a family of integer vectors that is independent over `ℤ` (equivalently
over `ℚ`) stays independent over `ℝ`. -/
lemma linearIndependent_real_of_int {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type*} (w : ι → L) (hw : LinearIndependent ℤ w) :
    LinearIndependent ℝ (fun i => (w i : E)) := by
  -- `ℝ`-linear independence is a finite condition: it suffices to check every finite
  -- subfamily, which is `ℤ`-linearly independent by restriction.
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  exact linearIndependent_real_of_int_fintype L (fun i : s => w i)
    (hw.comp (Subtype.val : s → ι) Subtype.val_injective)

end Commons.Lattice.SuccessiveMinima