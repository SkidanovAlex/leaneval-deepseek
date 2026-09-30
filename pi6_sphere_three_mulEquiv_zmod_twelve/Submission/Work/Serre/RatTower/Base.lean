import Mathlib
import Submission.Work.Serre.RatTower.Defs
import Submission.Work.Serre.ratPairBasic
import Submission.Work.Serre.CWModel.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre.RatTower

noncomputable section

/-- **The invariant of the tower induction**, over `ℚ`.`GoodQ p b f Γ g γ₀` says that the
comparison map of the pullback of `p` along `g` is an isomorphism below `b + f` and surjective in
degree `b + f`. -/
def GoodQ {B : Type} [TopologicalSpace B] {E : Type} [TopologicalSpace E]
    (p : C(E, B)) (b f : ℕ) (Γ : Type) [TopologicalSpace Γ] (g : C(Γ, B)) (γ₀ : Γ) : Prop :=
  (∀ i : ℕ, i < b + f → CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (stagePairMapRat g p γ₀) i)) ∧
  Function.Surjective (HomologicalComplex.homologyMap (stagePairMapRat g p γ₀) (b + f)).hom

/-- The relative chains of `(X, univ)` form a zero complex. -/
theorem rt_isZero_relChainsR_univ (X : TopCat) :
    IsZero (Work.StemsB.relChainsR ℚ X (Set.univ : Set X)) := by
  haveI h1 : IsIso (Work.Cohomology.subtypeIncl X (Set.univ : Set X)) :=
    ⟨TopCat.ofHom ⟨fun x => ⟨x, trivial⟩, by fun_prop⟩, by ext x; rfl, by ext x; rfl⟩
  haveI h2 : IsIso (Work.StemsB.relChainsRIncl ℚ X (Set.univ : Set X)) := inferInstance
  exact Limits.isZero_cokernel_of_epi _

theorem rt_baseGood {B : Type} [TopologicalSpace B] {E : Type} [TopologicalSpace E]
    (p : C(E, B)) (b₀ : B) (b f : ℕ) :
    GoodQ p b f PUnit (ContinuousMap.const PUnit b₀) ⟨⟩ := by
  have hsrc : ((Work.StemsB.pullbackFst (ContinuousMap.const PUnit b₀) p) ⁻¹'
      ({⟨⟩} : Set PUnit)) = Set.univ := by
    ext x; simp
  have htgt : ({⟨⟩} : Set PUnit) = (Set.univ : Set PUnit) := by
    ext x; simp
  have hX : ∀ i : ℕ, IsZero ((Work.StemsB.relChainsR ℚ
      (TopCat.of (Work.StemsB.Pullback (ContinuousMap.const PUnit b₀) p))
      ((Work.StemsB.pullbackFst (ContinuousMap.const PUnit b₀) p) ⁻¹'
        ({⟨⟩} : Set PUnit))).homology i) := by
    intro i
    rw [hsrc]
    exact (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) i).map_isZero
      (rt_isZero_relChainsR_univ _)
  have hY : ∀ i : ℕ, IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of PUnit)
      ({⟨⟩} : Set PUnit)).homology i) := by
    intro i
    rw [htgt]
    exact (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) i).map_isZero
      (rt_isZero_relChainsR_univ _)
  constructor
  · intro i _
    have he := IsZero.eq_of_src (hX i) (HomologicalComplex.homologyMap
      (stagePairMapRat (ContinuousMap.const PUnit b₀) p ⟨⟩) i) (IsZero.iso (hX i) (hY i)).hom
    rw [he]
    infer_instance
  · change Function.Surjective (HomologicalComplex.homologyMap
      (stagePairMapRat (ContinuousMap.const PUnit b₀) p ⟨⟩) (b + f)).hom
    haveI : Subsingleton (↥((Work.StemsB.relChainsR ℚ (TopCat.of PUnit)
        ({⟨⟩} : Set PUnit)).homology (b + f))) :=
      ModuleCat.subsingleton_of_isZero (hY (b + f))
    intro y
    exact ⟨0, Subsingleton.elim _ _⟩

end

end Work.Serre.RatTower
