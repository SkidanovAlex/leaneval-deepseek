import Mathlib
import Submission.Work.SSS.serreE1Defs
import Submission.Work.StemsB.Fibrations

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The `s = 0` piece is the chain complex of the pullback

For `σ : Δ[0] ⟶ Y` a **vertex** of a simplicial set `Y` and `f : X ⟶ Y` an arbitrary morphism of
simplicial sets, the σ-piece `pieceAlong f σ = C(T_σ)/C(∂T_σ)` of `Submission/Work/SSS/serreE1Defs.lean`
is *definitionally* the cokernel of `C(∂T_σ) ⟶ C(T_σ)`, and here the inclusion is that of the
bottom subcomplex: `∂Δ[0] = ⊥` (`SSet.boundary_zero`), hence `∂T_σ = ⊥` and

  `pieceAlong f σ = cokernel (C(⊥) ⟶ C(T_σ)) ≅ C(T_σ)`.

Indeed the source is a zero object (the only map out of the empty simplicial set is `0`, and
`C(⊥)` has no chains in any degree), so the cokernel of the zero map is the target.  This is the
"cokernel" half of the base case `s = 0` of the σ-piece computation; the companion statement
`Work.SSS.pieceAlongZero` identifies the pullback `T_σ = Δ[0] ×_{Sing B} Sing E` with the singular
simplicial set of the fibre of `p` over the vertex `σ(v₀)`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

namespace Work.SSS

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

/-- **The cokernel of a zero map is the target** (in any category with zero morphisms and the
relevant cokernel): `cokernel (0 : A ⟶ B) ≅ B`. -/
lemma cokernel_iso_of_eq_zero {C : Type*} [Category* C] [HasZeroMorphisms C] {A B : C}
    (f : A ⟶ B) (hf : f = 0) [HasCokernel f] : Nonempty (cokernel f ≅ B) := by
  have hπ : IsIso (cokernel.π f) :=
    CokernelCofork.IsColimit.isIso_π (CokernelCofork.ofπ (cokernel.π f) (cokernel.condition f))
      (cokernelIsCokernel f) hf
  exact ⟨(asIso (cokernel.π f)).symm⟩

/-- The chain map induced by the inclusion of the bottom subcomplex of a simplicial set is zero: the
simplicial chain complex of `⊥` has no chains in any degree, so its `n`-th component is a map out of
the coproduct over the empty index set. -/
lemma sCCMap_bot_ι_eq_zero (X : SSet.{0}) : sCCMap (⊥ : X.Subcomplex).ι = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  apply SSet.chainComplex_hom_ext (X := (⊥ : X.Subcomplex)) (R := ModuleCat.of ℤ ℤ)
  intro x
  exact x.2.elim

/-- The chain map induced by the inclusion of a subcomplex which happens to be `⊥` is zero. -/
lemma sCCMap_ι_eq_zero_of_eq_bot {X : SSet.{0}} {A : X.Subcomplex} (hA : A = ⊥) :
    sCCMap A.ι = 0 := by
  subst hA
  exact sCCMap_bot_ι_eq_zero X

/-- **A σ-piece with empty boundary is the chain complex of the pullback.**  If the subcomplex
`∂T_σ ⊆ T_σ` is `⊥`, then `pieceAlong f σ = C(T_σ)/C(∂T_σ) ≅ C(T_σ)`, since
`C(∂T_σ) ⟶ C(T_σ)` is the zero map out of a zero complex. -/
lemma pieceAlong_iso_of_bdry_eq_bot {X Y : SSet.{0}} (f : X ⟶ Y) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Y)
    (h : bdryAlong f σ = ⊥) :
    Nonempty (pieceAlong f σ ≅ sCC (pullAlong f σ)) := by
  unfold pieceAlong
  exact cokernel_iso_of_eq_zero _ (sCCMap_ι_eq_zero_of_eq_bot h)

theorem pieceAlongZeroCoker {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSS.sSing B) :
    Nonempty (Work.SSS.pieceAlong (Work.SSS.sSingP p) σ ≅
      Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)) :=
  pieceAlong_iso_of_bdry_eq_bot _ σ (bdryAlong_eq_bot_of_zero _ σ)

end

end Work.SSS
