import Mathlib
import Submission.Work.SSSR.serreE1Defs
import Submission.Work.SSSR.StemsB.Fibrations
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
noncomputable section

/-- The preimage of the bottom subcomplex of a simplicial set is again the bottom subcomplex. -/
lemma preimage_bot_subcomplex {X Y : SSet.{0}} (p : Y ⟶ X) :
    (⊥ : X.Subcomplex).preimage p = ⊥ := by
  ext n x
  simp

/-- **The boundary of a vertex pullback is empty.**  For any morphism of simplicial sets `f : X ⟶ Y`
and any vertex `σ : Δ[0] ⟶ Y`, the subcomplex `∂T_σ ⊆ T_σ` cut out by `∂Δ[0]` is `⊥`: this is the
pullback of the identity `∂Δ[0] = ⊥` along the first projection of `T_σ = Δ[0] ×_Y X`. -/
lemma bdryAlong_eq_bot_of_zero {X Y : SSet.{0}} (f : X ⟶ Y)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Y) :
    bdryAlong f σ = ⊥ := by
  rw [bdryAlong, SSet.boundary_zero]
  exact preimage_bot_subcomplex _

/-- The chain map induced by the inclusion of the bottom subcomplex of a simplicial set is zero: the
simplicial chain complex of `⊥` has no chains in any degree, so its `n`-th component is a map out of
the coproduct over the empty index set. -/
lemma sCCMap_bot_ι_eq_zero (X : SSet.{0}) : sCCMap R (⊥ : X.Subcomplex).ι = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  apply SSet.chainComplex_hom_ext (X := (⊥ : X.Subcomplex)) (R := ModuleCat.of R R)
  intro x
  exact x.2.elim

/-- The chain map induced by the inclusion of a subcomplex which happens to be `⊥` is zero. -/
lemma sCCMap_ι_eq_zero_of_eq_bot {X : SSet.{0}} {A : X.Subcomplex} (hA : A = ⊥) :
    sCCMap R A.ι = 0 := by
  subst hA
  exact sCCMap_bot_ι_eq_zero X

end

end Work.SSSR
