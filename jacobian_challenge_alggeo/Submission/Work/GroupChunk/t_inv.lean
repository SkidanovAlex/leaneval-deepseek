import Mathlib
import Submission.Work.GroupChunk.Transitions

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.GroupChunk

open CategoryTheory AlgebraicGeometry
open scoped MonoidalCategory
open scoped Work.GCBasics

universe u

noncomputable section

open Work.GCBasics

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

variable {K : Type u} [Field K] {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver}
  [SpecLin.DivBase C]

/-! ## Open subschemes: instances and point lemmas -/

/-- The inclusion of an open subscheme is a monomorphism. -/
instance instMono_ιOver {X : Sch K} (U : X.left.Opens) : Mono (Opens.ιOver U) :=
  Over.mono_of_mono_left _

/-- The composite inclusion `U i j ↪ Sym^g C` is a monomorphism. -/
instance instMono_Uι [D : Input C P0] (i j : D.Idx) : Mono (Uι i j) := by
  rw [show Uι i j = Opens.ιOver (U i j) ≫ Opens.ιOver D.V from rfl]
  infer_instance

instance instIsReducedV [D : Input C P0] : IsReduced (Opens.toOver D.V).left :=
  isReduced_of_isOpenImmersion D.V.ι

instance instIsReducedU [D : Input C P0] (i j : D.Idx) :
    IsReduced (Opens.toOver (U i j)).left :=
  isReduced_of_isOpenImmersion (U i j).ι

instance instIsSeparatedV [D : Input C P0] : IsSeparated (Opens.toOver D.V).hom := by
  change IsSeparated (D.V.ι ≫ (D.Sym D.g).hom)
  exact MorphismProperty.IsStableUnderComposition.comp_mem _ _ (by infer_instance)
    (by haveI := D.isProper_Sym D.g; infer_instance)

instance instIsSeparatedU [D : Input C P0] (i j : D.Idx) :
    IsSeparated (Opens.toOver (U i j)).hom := by
  change IsSeparated ((U i j).ι ≫ (Opens.toOver D.V).hom)
  exact MorphismProperty.IsStableUnderComposition.comp_mem _ _ (by infer_instance)
    (instIsSeparatedV (D := D))

namespace TInvAux

variable [D : Input C P0]

/-- The structure identity `Uι i j = ιOver (U i j) ≫ ιOver V`. -/
theorem Uι_def' (i j : D.Idx) :
    Uι i j = Opens.ιOver (U i j) ≫ Opens.ιOver D.V := rfl

/-- A point of the transition domain `U i j` lands in `W i j` after including in `Sym^g C`. -/
theorem landsIn_W_Uι (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (q : FPt (Opens.toOver (U i j)) F) : RPt.LandsIn (q ≫ Uι i j) (W i j) :=
  range_Uι_le_W i j ⟨q.left (IsLocalRing.closedPoint F), rfl⟩

/-- A point of the transition domain `U i j` lies in the domain of `σ i j`. -/
theorem landsIn_domain_Uι (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (q : FPt (Opens.toOver (U i j)) F) : RPt.LandsIn (q ≫ Uι i j) (σ i j).domain :=
  W_le_domain i j (landsIn_W_Uι i j q)

/-- The value of `σ i j` at a point of `W i j` lies in the chart `V`. -/
theorem landsIn_V_σVal (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (q : FPt (D.Sym D.g) F) (hq : RPt.LandsIn q (σ i j).domain)
    (hqW : RPt.LandsIn q (W i j)) :
    RPt.LandsIn (σVal i j q hq) D.V := by
  obtain ⟨Q, hQ, -⟩ := RPt.factor_of_closed_landsIn (σ i j).domain q hq
  show (σVal i j q hq).left (IsLocalRing.closedPoint F) ∈ D.V
  rw [σVal_eq_of_factor i j q hq Q hQ]
  exact σPM_hom_mem_V_of_landsIn_W i j q hqW Q hQ

/-- **The inverse of the transition, pointwise.**  The transition `t i j` followed by
`t j i` is the identity on the points of `U i j`. -/
theorem t_inv_point (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (q : FPt (Opens.toOver (U i j)) F) :
    (q ≫ t i j ≫ t j i) ≫ Uι i j = q ≫ Uι i j := by
  have hq0 : RPt.LandsIn (q ≫ Uι i j) (σ i j).domain := landsIn_domain_Uι i j q
  set y : FPt (D.Sym D.g) F := σVal i j (q ≫ Uι i j) hq0 with hy
  have h1 : (q ≫ t i j) ≫ Uι j i = y := by
    rw [hy]
    simpa only [Category.assoc] using t_value i j q hq0
  have hyW : RPt.LandsIn y (W j i) := by
    rw [← h1]
    exact landsIn_W_Uι j i (q ≫ t i j)
  have hy_dom : RPt.LandsIn y (σ j i).domain := W_le_domain j i hyW
  have hp : RPt.LandsIn ((q ≫ t i j) ≫ Uι j i) (σ j i).domain := by
    rw [h1]; exact hy_dom
  have h3 : σVal j i ((q ≫ t i j) ≫ Uι j i) hp = σVal j i y hy_dom :=
    TExistsAux.σVal_congr j i h1 hp hy_dom
  have hmain : σVal j i y hy_dom = q ≫ Uι i j := by
    have hlin1 : LinEquiv C (D.divOf D.g (σVal j i y hy_dom) + bcKF F (D.EDiv j))
        (D.divOf D.g y + bcKF F (D.EDiv i)) := σ_value j i y hy_dom
    have hlin2 : LinEquiv C (D.divOf D.g y + bcKF F (D.EDiv i))
        (D.divOf D.g (q ≫ Uι i j) + bcKF F (D.EDiv j)) := by
      have h := σ_value i j (q ≫ Uι i j) hq0
      rw [← hy] at h
      exact h
    have hlin : LinEquiv C (D.divOf D.g (σVal j i y hy_dom) + bcKF F (D.EDiv j))
        (D.divOf D.g (q ≫ Uι i j) + bcKF F (D.EDiv j)) := hlin1.trans hlin2
    have h5 : LinEquiv C (D.divOf D.g (σVal j i y hy_dom)) (D.divOf D.g (q ≫ Uι i j)) := by
      have key := (LinEquiv.sub_iff (D.divOf D.g (σVal j i y hy_dom) + bcKF F (D.EDiv j))
        (D.divOf D.g (q ≫ Uι i j) + bcKF F (D.EDiv j)) (bcKF F (D.EDiv j))).mpr hlin
      rwa [show D.divOf D.g (σVal j i y hy_dom) + bcKF F (D.EDiv j) - bcKF F (D.EDiv j)
              = D.divOf D.g (σVal j i y hy_dom) by abel,
           show D.divOf D.g (q ≫ Uι i j) + bcKF F (D.EDiv j) - bcKF F (D.EDiv j)
              = D.divOf D.g (q ≫ Uι i j) by abel] at key
    have hyV' : RPt.LandsIn (σVal j i y hy_dom) D.V := landsIn_V_σVal j i y hy_dom hyW
    have hyV : RPt.LandsIn y D.V := by
      rw [hy, ← TExistsAux.tHom_eq_σVal i j q hq0]
      exact TExistsAux.tHom_landsIn_V i j q
    have hdiv := linEquiv_eq_of_ell_eq_one
      ((D.symGeom D.g).divOf_isEffective (σVal j i y hy_dom))
      (ell_of_landsIn_V (σVal j i y hy_dom) hyV')
      ((D.symGeom D.g).divOf_isEffective (q ≫ Uι i j)) h5
    exact (D.symGeom D.g).divOf_injective _ _ hdiv
  calc (q ≫ t i j ≫ t j i) ≫ Uι i j
      = (q ≫ t i j) ≫ t j i ≫ Uι i j := by simp only [Category.assoc]
    _ = σVal j i ((q ≫ t i j) ≫ Uι j i) hp := t_value j i (q ≫ t i j) hp
    _ = σVal j i y hy_dom := h3
    _ = q ≫ Uι i j := hmain

end TInvAux

open TInvAux in
theorem t_inv {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : 𝟙_ (Work.GCBasics.Sch K) ⟶ C.toOver} [Work.SpecLin.DivBase C]
    [D : Work.GroupChunk.Input C P0] (i j : D.Idx) :
    Work.GroupChunk.t i j ≫ Work.GroupChunk.t j i
      = 𝟙 (Work.GCBasics.Opens.toOver (Work.GroupChunk.U i j)) := by
  haveI : IsReduced (Work.GCBasics.Opens.toOver (Work.GroupChunk.U i j)).left :=
    isReduced_of_isOpenImmersion (U i j).ι
  apply (cancel_mono (Uι i j)).mp
  rw [Category.id_comp]
  apply hom_ext_of_resPt
  intro x
  simpa only [Category.assoc] using
    TInvAux.t_inv_point (C := C) (P0 := P0) i j (resPt (Opens.toOver (U i j)) x)

end

end Work.GroupChunk
