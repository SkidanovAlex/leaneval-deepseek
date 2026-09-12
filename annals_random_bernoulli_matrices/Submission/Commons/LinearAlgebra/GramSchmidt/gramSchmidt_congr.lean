import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

open scoped BigOperators

namespace Commons.LinearAlgebra.GramSchmidt

/-- A linear order which is locally finite and has a bottom element is well-founded:
every element has only finitely many strict predecessors (they are contained in the
finite `Finset.Iio` interval), so accessibility follows by induction on that cardinal. -/
instance wellFoundedLT_of_LocallyFiniteOrderBot (ι : Type*) [LinearOrder ι]
    [LocallyFiniteOrderBot ι] : WellFoundedLT ι := by
  constructor
  refine ⟨?_⟩
  intro a
  have hmain : ∀ k : ℕ, ∀ x : ι, (Finset.Iio x).card ≤ k → Acc (· < ·) x := by
    intro k
    induction k with
    | zero =>
        intro x hk
        refine Acc.intro x ?_
        intro y hyx
        exfalso
        have hyIio : y ∈ Finset.Iio x := Finset.mem_Iio.mpr hyx
        have hcardpos : 0 < (Finset.Iio x).card := Finset.card_pos.mpr ⟨y, hyIio⟩
        omega
    | succ k ih =>
        intro x hk
        refine Acc.intro x ?_
        intro y hyx
        have hyIio : y ∈ Finset.Iio x := Finset.mem_Iio.mpr hyx
        have hsub : Finset.Iio y ⊆ Finset.Iio x := by
          intro z hz
          exact Finset.mem_Iio.mpr (lt_trans (Finset.mem_Iio.mp hz) hyx)
        have hne : Finset.Iio y ≠ Finset.Iio x := by
          intro heq
          have hyself : y ∈ Finset.Iio y := by simpa [heq] using hyIio
          exact (lt_irrefl y) (Finset.mem_Iio.mp hyself)
        have hcardlt : (Finset.Iio y).card < (Finset.Iio x).card :=
          Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
        have hcardle : (Finset.Iio y).card ≤ k := by omega
        exact ih y hcardle
  exact hmain (Finset.Iio a).card a le_rfl

theorem gramSchmidt_congr {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {f g : ι → E} (h : ∀ i : ι, f i = g i) (i : ι) :
    InnerProductSpace.gramSchmidtNormed 𝕜 f i = InnerProductSpace.gramSchmidtNormed 𝕜 g i := by
  have hgs : ∀ n : ι,
      InnerProductSpace.gramSchmidt 𝕜 f n = InnerProductSpace.gramSchmidt 𝕜 g n := by
    intro n
    refine WellFoundedLT.induction (motive := fun m =>
      InnerProductSpace.gramSchmidt 𝕜 f m = InnerProductSpace.gramSchmidt 𝕜 g m) n ?_
    intro m ih
    conv_lhs => rw [InnerProductSpace.gramSchmidt_def]
    conv_rhs => rw [InnerProductSpace.gramSchmidt_def]
    rw [h m]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hjm : j < m := Finset.mem_Iio.mp hj
    have hjh : InnerProductSpace.gramSchmidt 𝕜 f j = InnerProductSpace.gramSchmidt 𝕜 g j := ih j hjm
    rw [Submodule.starProjection_singleton 𝕜 (w := g m) (v := InnerProductSpace.gramSchmidt 𝕜 f j),
        Submodule.starProjection_singleton 𝕜 (w := g m) (v := InnerProductSpace.gramSchmidt 𝕜 g j)]
    rw [hjh]
  dsimp [InnerProductSpace.gramSchmidtNormed]
  rw [hgs i]

end Commons.LinearAlgebra.GramSchmidt