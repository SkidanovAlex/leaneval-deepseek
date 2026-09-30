import Mathlib
import Submission.Work.Serre.E3aStepDefs
import Submission.Work.Serre.RatTower.fiveLemmaTau2
import Submission.Work.Serre.RatTower.pullbackFstRangeHomeo
import Submission.Work.Cohomology.relChainsMapOf_comp
import Submission.Work.StemsB.RelChainsR
import Submission.Work.Serre.RatTower.attachStepQ
import Submission.Work.Serre.OneCell.Transfer

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Serre

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option linter.style.haveILetI false

noncomputable section

/-- **Transfer of the homology comparison along a commuting square of homeomorphisms**, in the
epimorphism form: if `eY ∘ g' = g ∘ eX` with `eX`, `eY` homeomorphisms and `ratHomologyMap g k`
is an epimorphism, then so is `ratHomologyMap g' k`.  (The `IsIso` form is
`Work.Serre.OneCell.isIso_ratHomologyMap_of_homeo_square`.) -/
theorem epi_ratHomologyMap_of_homeo_square {X Y X' Y' : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y'] (eX : X ≃ₜ X')
    (eY : Y ≃ₜ Y') (g' : C(X, Y)) (g : C(X', Y')) (h : ∀ x : X, eY (g' x) = g (eX x))
    (k : ℕ) (hg : Epi (ratHomologyMap g k)) : Epi (ratHomologyMap g' k) := by
  haveI hX : IsIso (ratHomologyMap (eX : C(X, X')) k) :=
    Work.Serre.OneCell.isIso_ratHomologyMap_homeo eX k
  haveI hY : IsIso (ratHomologyMap (eY : C(Y, Y')) k) :=
    Work.Serre.OneCell.isIso_ratHomologyMap_homeo eY k
  have hmaps : (eY : C(Y, Y')).comp g' = g.comp (eX : C(X, X')) :=
    ContinuousMap.ext fun x => h x
  have h1 : ratHomologyMap g' k ≫ ratHomologyMap (eY : C(Y, Y')) k
      = ratHomologyMap (eX : C(X, X')) k ≫ ratHomologyMap g k := by
    rw [← ratHomologyMap_comp g' (eY : C(Y, Y')),
      ← ratHomologyMap_comp (eX : C(X, X')) g, hmaps]
  have h2 := congrArg (fun t => t ≫ inv (ratHomologyMap (eY : C(Y, Y')) k)) h1
  have h3 : ratHomologyMap g' k
      = ratHomologyMap (eX : C(X, X')) k ≫ ratHomologyMap g k ≫
        inv (ratHomologyMap (eY : C(Y, Y')) k) := by
    simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id, IsIso.inv_hom_id] using h2
  rw [h3]
  infer_instance

/-- **Propagation of `AbsGoodQ` along an inclusion of stages.**

Let `p : E → B` be a map, `incl : Γ → Γ'` an injective inducing map (so that `Γ` is a subspace of
`Γ'`) with compatible structure maps `g = g' ∘ incl : Γ → B`.  Then `AbsGoodQ p r g` (the statement
that `Γ ×_B E → Γ` is a rational homology isomorphism in degrees `< r` and an epimorphism in degree
`r`) propagates to `Γ'` **provided** the relative comparison `stepMapQ p incl g'` — which compares
`C_*(Γ' ×_B E, (Γ' ×_B E)|Γ; ℚ)` with `C_*(Γ', Γ; ℚ)` — is a quasi-isomorphism in degrees
`≤ r`.

The proof is the long exact sequence of the pair `(Γ' ×_B E, (Γ' ×_B E)|Γ)`, compared by the map of
pairs induced by the projection of the pullback with the long exact sequence of the pair `(Γ', Γ)`:
the two outer vertical maps are the relative comparison (the hypothesis) and the absolute comparison
over `Γ` (the hypothesis `IH`, transported across the homeomorphism
`Work.Serre.RatTower.pullbackFstRangeHomeo`), and the five lemma
(`Work.Serre.RatTower.fiveLemmaTau2`) gives the middle one. -/
theorem propagateAbsQ {B E Γ Γ' : Type} [TopologicalSpace B] [TopologicalSpace E]
    [TopologicalSpace Γ] [TopologicalSpace Γ'] (p : ContinuousMap E B) (r : ℕ)
    (g : ContinuousMap Γ B)
    (IH : Work.Serre.E3aStep.AbsGoodQ p r g) (incl : ContinuousMap Γ Γ')
    (hinj : Function.Injective incl) (hind : Topology.IsInducing incl) (g' : ContinuousMap Γ' B)
    (hrel : ∀ x, g' (incl x) = g x)
    (hstep : ∀ i : ℕ, i < r + 1 →
      CategoryTheory.IsIso (HomologicalComplex.homologyMap (Work.Serre.E3aStep.stepMapQ p incl g') i)) :
    Work.Serre.E3aStep.AbsGoodQ p r g' := by
  classical
  -- ## 0. The vocabulary
  let Q := Work.StemsB.Pullback g' p
  let P := Work.StemsB.Pullback g p
  let qP : C(P, Γ) := Work.StemsB.pullbackFst g p
  let R : Set Γ' := Set.range incl
  let X : Set Q := (Work.StemsB.pullbackFst g' p) ⁻¹' R
  obtain ⟨e, he1, he2, he3, he4⟩ :=
    Work.Serre.RatTower.pullbackFstRangeHomeo incl hinj hind g g' hrel p
  have hemb : Topology.IsEmbedding incl := ⟨hind, hinj⟩
  let hom : ↥R ≃ₜ Γ := hemb.toHomeomorph.symm
  have hom_spec : ∀ y : ↥R, incl (hom y) = y.1 := by
    intro y
    calc incl (hom y) = ↑(hemb.toHomeomorph (hom y)) :=
          (Topology.IsEmbedding.toHomeomorph_apply_coe hemb (hom y)).symm
      _ = ↑y := congrArg Subtype.val (Homeomorph.apply_symm_apply hemb.toHomeomorph y)
  let qX : C(↥X, ↥R) := ⟨fun x => ⟨(Work.StemsB.pullbackFst g' p) x.1, x.2⟩, by fun_prop⟩
  have hsquare : ∀ x : ↥X, hom (qX x) = qP (e x) := by
    intro x
    have h1 : incl (hom (qX x)) = (qX x).1 := hom_spec (qX x)
    refine hinj ?_
    rw [h1]
    exact (he1 x).symm
  -- ## 1. The two short exact sequences and the morphism between them
  let S₁ : ShortComplex (ChainComplex (ModuleCat ℚ) ℕ) :=
    Work.StemsB.relChainsRShort ℚ (TopCat.of Q) X
  let S₂ : ShortComplex (ChainComplex (ModuleCat ℚ) ℕ) :=
    Work.StemsB.relChainsRShort ℚ (TopCat.of Γ') R
  have hS₁ : S₁.ShortExact := Work.StemsB.relChainsR_shortExact ℚ (TopCat.of Q) X
  have hS₂ : S₂.ShortExact := Work.StemsB.relChainsR_shortExact ℚ (TopCat.of Γ') R
  let τ₁ := Work.Cohomology.chainMap ℚ (TopCat.of ↥X) (TopCat.of ↥R) (TopCat.ofHom qX)
  let τ₂ := Work.Cohomology.chainMap ℚ (TopCat.of Q) (TopCat.of Γ')
    (TopCat.ofHom (Work.StemsB.pullbackFst g' p))
  let τ₃ := Work.Serre.E3aStep.stepMapQ p incl g'
  have comm₁₂ : τ₁ ≫ S₂.f = S₁.f ≫ τ₂ := by
    show Work.Cohomology.chainMap ℚ (TopCat.of ↥X) (TopCat.of ↥R) (TopCat.ofHom qX)
        ≫ Work.Cohomology.chainMap ℚ (TopCat.of ↥R) (TopCat.of Γ')
            (Work.Cohomology.subtypeIncl (TopCat.of Γ') R)
      = Work.Cohomology.chainMap ℚ (TopCat.of ↥X) (TopCat.of Q)
            (Work.Cohomology.subtypeIncl (TopCat.of Q) X)
        ≫ Work.Cohomology.chainMap ℚ (TopCat.of Q) (TopCat.of Γ')
            (TopCat.ofHom (Work.StemsB.pullbackFst g' p))
    rw [← Work.Cohomology.chainMap_comp_relChains, ← Work.Cohomology.chainMap_comp_relChains]
    congr 1
  have comm₂₃ : τ₂ ≫ S₂.g = S₁.g ≫ τ₃ := by
    show Work.Cohomology.chainMap ℚ (TopCat.of Q) (TopCat.of Γ')
          (TopCat.ofHom (Work.StemsB.pullbackFst g' p))
        ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Γ') R)
      = cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Q) X)
        ≫ Work.Serre.E3aStep.stepMapQ p incl g'
    unfold Work.Serre.E3aStep.stepMapQ Work.Serre.relChainsRMapOf
    exact (Work.Cohomology.cokernel_π_map _ _ _ _ _).symm
  let φ : S₁ ⟶ S₂ := ShortComplex.homMk τ₁ τ₂ τ₃ comm₁₂ comm₂₃
  -- ## 2. The outer columns
  have hτ₁ : ∀ i : ℕ, i < r → IsIso (HomologicalComplex.homologyMap φ.τ₁ i) := by
    intro i hi
    have h : HomologicalComplex.homologyMap φ.τ₁ i = ratHomologyMap qX i := rfl
    rw [h]
    exact Work.Serre.OneCell.isIso_ratHomologyMap_of_homeo_square e hom qX qP hsquare i (IH.1 i hi)
  have e₁ : Epi (HomologicalComplex.homologyMap φ.τ₁ r) := by
    have h : HomologicalComplex.homologyMap φ.τ₁ r = ratHomologyMap qX r := rfl
    rw [h]
    exact epi_ratHomologyMap_of_homeo_square e hom qX qP hsquare r IH.2
  have hτ₃ : ∀ i : ℕ, i < r → IsIso (HomologicalComplex.homologyMap φ.τ₃ i) := by
    intro i hi
    exact hstep i (by omega)
  have e₃ : Epi (HomologicalComplex.homologyMap φ.τ₃ r) := by
    haveI h : IsIso (HomologicalComplex.homologyMap φ.τ₃ r) := hstep r (Nat.lt_succ_self r)
    exact IsIso.epi_of_iso _
  -- ## 3. The five lemma
  obtain ⟨h₂, e₂⟩ := Work.Serre.RatTower.fiveLemmaTau2 φ hS₁ hS₂ r hτ₁ hτ₃ e₁ e₃
  exact ⟨h₂, e₂⟩

end

end Work.Serre
