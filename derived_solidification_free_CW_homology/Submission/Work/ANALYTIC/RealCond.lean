import Mathlib
import ChallengeDeps
import Submission.Blueprint.Interfaces

/-!
# The light condensed abelian group `ℝ`

The *condensation* of `ℝ`: the sheaf on `LightProfinite` whose value at `S` is the ℤ-module
`C(S, ℝ)` of continuous ℝ-valued functions.  It is a light condensed abelian group, and its
`S`-points are definitionally `C(S, ℝ)` (see `realCond_obj_obj`).

This is the target of the parametrised null sequence of REFS/03 §3 (the map `f : P ⟶ ℝ`,
`e_n ↦ 2^{-⌊log₂(n+1)⌋}`), and the ring along which the "ℝ-module objects" of that section are
formed.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open CategoryTheory.regularTopology

noncomputable section

namespace Work.ANALYTIC

open _root_.LightCondensed _root_.LightCondensed.Solid

/-- The defining property of the category `LightProfinite`. -/
abbrev LP : TopCat → Prop := fun X ↦ TotallyDisconnectedSpace X ∧ SecondCountableTopology X

/-- The presheaf of continuous `ℝ`-valued functions on light profinite sets. -/
def realPresheaf : LightProfiniteᵒᵖ ⥤ ModuleCat ℤ where
  obj S := ModuleCat.of ℤ C(S.unop, ℝ)
  map f := ModuleCat.ofHom
    { toFun := fun g => g.comp (LightProfinite.toTopCat.map f.unop).hom
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The underlying presheaf of sets of `realPresheaf` is the Yoneda presheaf of `ℝ`
(Mathlib's `TopCat.toSheafCompHausLike`), so the sheaf condition is the standard one for
continuous maps into a topological space. -/
theorem realPresheaf_eq_yonedaPresheaf :
    realPresheaf ⋙ CategoryTheory.forget (ModuleCat ℤ) =
      ContinuousMap.yonedaPresheaf (CompHausLike.compHausLikeToTop LP) ℝ := rfl

theorem realPresheaf_equalizerCondition :
    EqualizerCondition (realPresheaf ⋙ CategoryTheory.forget (ModuleCat ℤ)) := by
  rw [realPresheaf_eq_yonedaPresheaf]
  apply equalizerCondition_yonedaPresheaf
  intro Z B π _
  exact Topology.IsQuotientMap.of_surjective_continuous
    ((LightProfinite.effectiveEpi_iff_surjective π).mp inferInstance) π.hom.hom.continuous

instance : PreservesFiniteProducts (realPresheaf ⋙ CategoryTheory.forget (ModuleCat ℤ)) :=
  inferInstanceAs (PreservesFiniteProducts
    (ContinuousMap.yonedaPresheaf (CompHausLike.compHausLikeToTop LP) ℝ))

/-- **The light condensed abelian group `ℝ`**, i.e. the sheaf `S ↦ C(S, ℝ)`. -/
noncomputable def realCond : LightCondAb :=
  LightCondensed.ofSheafForgetLightProfinite realPresheaf realPresheaf_equalizerCondition

/-- The `S`-points of `realCond` are the continuous `ℝ`-valued functions on `S`
(definitionally). -/
theorem realCond_obj_obj (S : LightProfinite) :
    realCond.obj.obj (Opposite.op S) = C(S, ℝ) := rfl

/-! ## The unit of `ℝ` -/

/-- The free/forget adjunction identifies morphisms out of `ℤ[S]` with sections over `S`; combined
with the Yoneda equivalence for the (subcanonical) coherent topology, this identifies
`ℤ[S] ⟶ M` with `M(S)`.  In particular `ℤ[∗] ⟶ realCond ≃ C(∗, ℝ) ≃ ℝ`. -/
noncomputable def freeHomEquiv (S : LightProfinite) (M : LightCondAb) :
    ((free ℤ).obj S.toCondensed ⟶ M) ≃ M.obj.obj (Opposite.op S) :=
  (((LightCondensed.freeForgetAdjunction ℤ).homEquiv _ _).trans
    (coherentTopology LightProfinite).yonedaEquiv)

/-- The element of `C(∗, ℝ) ≃ ℝ` which is the constant `1`: this is the "unit" of `ℝ` seen at the
point. -/
def realOnePoint : C(LightProfinite.of PUnit, ℝ) := ⟨fun _ => 1, continuous_const⟩

end Work.ANALYTIC
