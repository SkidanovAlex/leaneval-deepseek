import Mathlib
import Submission.Work.Pi6.EMZ.Defs
import Submission.Work.Cohomology.kronH_bijective_field
import Submission.Work.Pi6.HALG.card_le_of_rank_le
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# AREA EMZ — dualising a homology bound into a cohomology bound (and back)

Over a field `𝕜` the Kronecker pairing `Hⁿ(X;𝕜) ⟶ Hom_𝕜(Hₙ(X;𝕜), 𝕜)` of
`Work.Cohomology.kronH_bijective_field` is an isomorphism, so the `𝕜`-dimension of the homology
never exceeds the `𝕜`-dimension of the cohomology: the dual of a vector space is never smaller than
the space itself (`Work.Pi6.EMZ.rank_le_rank_dual`, via the injective basis map
`Basis.toDual`).  Consequently a *rank* bound on `Hⁿ(X;𝕜)` bounds `Hₙ(X;𝕜)` as well, and — over a
finite coefficient field — bounds the *cardinality* of `Hₙ(X;𝕜)`, by
`Work.Pi6.HALG.card_le_of_rank_le` (`|V| = |𝕜| ^ finrank`).
-/

set_option autoImplicit false

open CategoryTheory

namespace Work.Pi6.EMZ

noncomputable section

/-- **The dual of a vector space is never smaller than the space.**  The basis map
`b.toDual : V →ₗ[𝕜] (V →ₗ[𝕜] 𝕜)`, `v ↦ (w ↦ coefficient of v at w)`, is injective, and the
dimension of the source of an injective linear map is at most the dimension of its target. -/
theorem rank_le_rank_dual (𝕜 V : Type) [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] :
    Module.rank 𝕜 V ≤ Module.rank 𝕜 (V →ₗ[𝕜] 𝕜) := by
  classical
  exact LinearMap.rank_le_of_injective _
    (Module.Free.chooseBasis 𝕜 V).toDual_injective

/-- **Kronecker duality bounds the homology dimension by the cohomology dimension.**  Over a field
`𝕜` the Kronecker pairing is a linear equivalence `Hⁿ(X;𝕜) ≃ₗ Hom_𝕜(Hₙ(X;𝕜), 𝕜)`
(`Work.Cohomology.kronH_bijective_field`), and the dual of `Hₙ(X;𝕜)` is never smaller
(`rank_le_rank_dual`). -/
theorem rank_HR_le_rank_Coh (𝕜 : Type) [Field 𝕜] (X : Type) [TopologicalSpace X] (n : ℕ) :
    Module.rank 𝕜 (Work.Pi6.HR 𝕜 X n) ≤ Module.rank 𝕜 (Work.Pi6.Coh 𝕜 X n) := by
  have e : ↥(Work.Pi6.Coh 𝕜 X n) ≃ₗ[𝕜] (↥(Work.Pi6.HR 𝕜 X n) →ₗ[𝕜] 𝕜) :=
    LinearEquiv.ofBijective (Work.Cohomology.kronH 𝕜 (TopCat.toSSet.obj (TopCat.of X)) n)
      (Work.Cohomology.kronH_bijective_field 𝕜 (TopCat.toSSet.obj (TopCat.of X)) n)
  calc Module.rank 𝕜 (Work.Pi6.HR 𝕜 X n)
      ≤ Module.rank 𝕜 (↥(Work.Pi6.HR 𝕜 X n) →ₗ[𝕜] 𝕜) := rank_le_rank_dual _ _
    _ = Module.rank 𝕜 (Work.Pi6.Coh 𝕜 X n) := e.rank_eq.symm

/-- **A rank bound on the mod-`𝕜` cohomology bounds the cardinality of the mod-`𝕜` homology**,
for a finite coefficient field `𝕜`: the homology dimension is at most the cohomology dimension
(`rank_HR_le_rank_Coh`), and a `𝕜`-vector space of dimension `≤ r` has at most `|𝕜| ^ r` elements
(`Work.Pi6.HALG.card_le_of_rank_le`). -/
theorem card_HR_le_of_rank_Coh_le (𝕜 : Type) [Field 𝕜] [Fintype 𝕜] (X : Type)
    [TopologicalSpace X] (n r : ℕ) (h : Module.rank 𝕜 (Work.Pi6.Coh 𝕜 X n) ≤ r) :
    Nat.card (Work.Pi6.HR 𝕜 X n) ≤ Nat.card 𝕜 ^ r :=
  Work.Pi6.HALG.card_le_of_rank_le r ((rank_HR_le_rank_Coh 𝕜 X n).trans h)

theorem rankDual :
    (∀ (𝕜 : Type) [Field 𝕜] (X : Type) [TopologicalSpace X] (n : ℕ),
      Module.rank 𝕜 (Work.Pi6.HR 𝕜 X n) ≤ Module.rank 𝕜 (Work.Pi6.Coh 𝕜 X n)) ∧
    (∀ (𝕜 : Type) [Field 𝕜] [Fintype 𝕜] (X : Type) [TopologicalSpace X] (n r : ℕ),
      Module.rank 𝕜 (Work.Pi6.Coh 𝕜 X n) ≤ r → Nat.card (Work.Pi6.HR 𝕜 X n) ≤ Nat.card 𝕜 ^ r) :=
  ⟨fun 𝕜 _ X _ n => rank_HR_le_rank_Coh 𝕜 X n
  , fun 𝕜 _ _ X _ n r h => card_HR_le_of_rank_Coh_le 𝕜 X n r h⟩

end

end Work.Pi6.EMZ
