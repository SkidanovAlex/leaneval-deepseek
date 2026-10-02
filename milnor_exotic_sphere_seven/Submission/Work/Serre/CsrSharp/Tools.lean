import Mathlib
import Submission.Work.Serre.csrDefs
import Submission.Work.Serre.csrGlue
import Submission.Work.Serre.csrExcisionRat
import Submission.Work.Serre.csrGeom

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Generic tools for the sharp rational cell step

Functoriality of the rational maps of pairs `Work.Serre.relChainsRPairMap`, and the homeomorphism
identifying a union of pairwise disjoint open pieces with the disjoint union of the pieces.

The code is adapted from `Submission/Work/Serre/csrUnionIso.lean` (the `N`-indexed rational cell
step), which cannot be imported here because its import closure contains `sorry`s.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.CsrSharp.Tools

noncomputable section

/-! ## Functoriality of `relChainsRPairMap` -/

/-- The relative chain map of the identity map of pairs. -/
theorem relChainsRPairMap_id {X : Type} [TopologicalSpace X] (A : Set X)
    (hg : Set.MapsTo (ContinuousMap.id X) A A) :
    relChainsRPairMap A A (ContinuousMap.id X) hg
      = 𝟙 (Work.StemsB.relChainsR ℚ (TopCat.of X) A) := by
  apply (cancel_epi (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) A))).mp
  show cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) A) ≫
      relChainsRPairMap A A (ContinuousMap.id X) hg
    = cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) A) ≫ 𝟙 _
  unfold relChainsRPairMap csrRelMapOf
  rw [Work.Cohomology.cokernel_π_map]
  simp [Work.Cohomology.chainMap]

/-- `relChainsRPairMap` depends only on the continuous map. -/
theorem relChainsRPairMap_congr {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} {g g' : C(X, Y)} (h : g = g')
    (hg : Set.MapsTo g A B) (hg' : Set.MapsTo g' A B) :
    relChainsRPairMap A B g hg = relChainsRPairMap A B g' hg' := by
  unfold relChainsRPairMap csrRelMapOf
  apply Work.Serre.cokernel_map_congr (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) A)
    (Work.StemsB.relChainsRIncl ℚ (TopCat.of Y) B)
  · refine congrArg (fun φ => Work.Cohomology.chainMap ℚ (TopCat.of A) (TopCat.of B) φ) ?_
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    exact Subtype.ext (congrFun (congrArg DFunLike.coe h) x.1)
  · exact congrArg (fun φ => Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y) φ)
      (congrArg TopCat.ofHom h)

/-- The relative chain map of the identity map of pairs, with an arbitrary `MapsTo` proof. -/
theorem relChainsRPairMap_id' {X : Type} [TopologicalSpace X] (A : Set X)
    (hg : Set.MapsTo (ContinuousMap.id X) A A) :
    relChainsRPairMap A A (ContinuousMap.id X) hg
      = 𝟙 (Work.StemsB.relChainsR ℚ (TopCat.of X) A) :=
  (relChainsRPairMap_congr rfl hg (by intro x hx; exact hx)).trans (relChainsRPairMap_id A _)

/-- **Composition of the relative chain maps of a composite of maps of pairs.** -/
theorem relChainsRPairMap_comp {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z}
    (g : C(X, Y)) (g' : C(Y, Z)) (hg : Set.MapsTo g A B) (hg' : Set.MapsTo g' B C)
    {hg'' : Set.MapsTo (g'.comp g) A C} :
    relChainsRPairMap A B g hg ≫ relChainsRPairMap B C g' hg'
      = relChainsRPairMap A C (g'.comp g) hg'' := by
  apply (cancel_epi (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) A))).mp
  show cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) A) ≫
      (relChainsRPairMap A B g hg ≫ relChainsRPairMap B C g' hg')
    = cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) A) ≫
      relChainsRPairMap A C (g'.comp g) hg''
  unfold relChainsRPairMap csrRelMapOf
  rw [← Category.assoc, Work.Cohomology.cokernel_π_map, Category.assoc,
    Work.Cohomology.cokernel_π_map, Work.Cohomology.cokernel_π_map, ← Category.assoc,
    ← Work.Cohomology.chainMap_comp_relChains ℚ, ← TopCat.ofHom_comp]

/-- **The chain-level form of a commuting square of maps of pairs.** -/
theorem relChainsRPairMap_comp_congr {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    {A : Set X} {C : Set Z}
    {Y₁ : Type} [TopologicalSpace Y₁] {B₁ : Set Y₁}
    {Y₂ : Type} [TopologicalSpace Y₂] {B₂ : Set Y₂}
    (g₁ : C(X, Y₁)) (g₁' : C(Y₁, Z)) (hg₁ : Set.MapsTo g₁ A B₁) (hg₁' : Set.MapsTo g₁' B₁ C)
    (g₂ : C(X, Y₂)) (g₂' : C(Y₂, Z)) (hg₂ : Set.MapsTo g₂ A B₂) (hg₂' : Set.MapsTo g₂' B₂ C)
    (h : g₁'.comp g₁ = g₂'.comp g₂) :
    relChainsRPairMap A B₁ g₁ hg₁ ≫ relChainsRPairMap B₁ C g₁' hg₁'
      = relChainsRPairMap A B₂ g₂ hg₂ ≫ relChainsRPairMap B₂ C g₂' hg₂' :=
  (relChainsRPairMap_comp g₁ g₁' hg₁ hg₁' (hg'' := fun x hx => hg₁' (hg₁ hx))).trans
    ((relChainsRPairMap_congr h (fun x hx => hg₁' (hg₁ hx))
        (fun x hx => hg₂' (hg₂ hx))).trans
      (relChainsRPairMap_comp g₂ g₂' hg₂ hg₂' (hg'' := fun x hx => hg₂' (hg₂ hx))).symm)

/-! ## The union of pairwise disjoint open pieces is the disjoint union of the pieces -/

/-- **Continuity of the canonical map from a space covered by disjoint open pieces to the disjoint
union of the pieces.**  For a family `o : ι → Set Z` of pairwise disjoint open sets and a set
`S ⊆ Z` covered by them, the map `z ↦ (i, z)` — with `i` the (unique, by disjointness) index of a
piece containing `z` — is continuous: near `z` it agrees with `y ↦ ⟨i, y⟩` on the open piece
`o i ∩ S`, which is a neighbourhood of `z`. -/
theorem continuous_sigmaPieces_toFun {ι Z : Type} [TopologicalSpace Z] {S : Set Z}
    (o : ι → Set Z) (hopen : ∀ i, IsOpen (o i)) (hdisj : ∀ i j, i ≠ j → Disjoint (o i) (o j))
    (hcov : ∀ z ∈ S, ∃ i, z ∈ o i) :
    Continuous fun z : ↥S => (⟨Classical.choose (hcov z.1 z.2),
      ⟨z.1, Classical.choose_spec (hcov z.1 z.2)⟩⟩ : Σ i, ↥(o i)) := by
  rw [continuous_iff_continuousAt]
  intro z
  have hzi : z.1 ∈ o (Classical.choose (hcov z.1 z.2)) :=
    Classical.choose_spec (hcov z.1 z.2)
  have hU : IsOpen ({w : ↥S | w.1 ∈ o (Classical.choose (hcov z.1 z.2))}) :=
    (hopen _).preimage continuous_subtype_val
  have hmodel : Continuous (fun w : {w : ↥S | w.1 ∈ o (Classical.choose (hcov z.1 z.2))} =>
      (⟨Classical.choose (hcov z.1 z.2), ⟨(w.1 : Z), w.2⟩⟩ : Σ j, ↥(o j))) :=
    continuous_sigmaMk.comp (Continuous.subtype_mk
      (continuous_subtype_val.comp continuous_subtype_val) (fun w => w.2))
  have hEqOn : ∀ w : {w : ↥S | w.1 ∈ o (Classical.choose (hcov z.1 z.2))},
      (fun z : ↥S => (⟨Classical.choose (hcov z.1 z.2),
        ⟨z.1, Classical.choose_spec (hcov z.1 z.2)⟩⟩ : Σ i, ↥(o i))) w.1
      = (⟨Classical.choose (hcov z.1 z.2), ⟨(w.1 : Z), w.2⟩⟩ : Σ j, ↥(o j)) := by
    intro w
    have h : Classical.choose (hcov w.1.1 w.1.2) = Classical.choose (hcov z.1 z.2) := by
      by_contra hne
      exact Set.disjoint_left.mp (hdisj _ _ hne)
        (Classical.choose_spec (hcov w.1.1 w.1.2)) w.2
    have hiff : ∀ y : Z, y ∈ o (Classical.choose (hcov w.1.1 w.1.2))
        ↔ y ∈ o (Classical.choose (hcov z.1 z.2)) :=
      fun y => ⟨fun hy => by rw [← h]; exact hy, fun hy => by rw [h]; exact hy⟩
    show (⟨Classical.choose (hcov w.1.1 w.1.2),
      ⟨(w.1 : Z), Classical.choose_spec (hcov w.1.1 w.1.2)⟩⟩ : Σ j, ↥(o j))
      = ⟨Classical.choose (hcov z.1 z.2), ⟨(w.1 : Z), w.2⟩⟩
    exact Sigma.ext h ((Subtype.heq_iff_coe_eq hiff).mpr rfl)
  have hcontOn : ContinuousOn (fun z : ↥S => (⟨Classical.choose (hcov z.1 z.2),
      ⟨z.1, Classical.choose_spec (hcov z.1 z.2)⟩⟩ : Σ i, ↥(o i)))
      {w : ↥S | w.1 ∈ o (Classical.choose (hcov z.1 z.2))} := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact hmodel.congr (fun w => (hEqOn w).symm)
  exact hcontOn.continuousAt (hU.mem_nhds hzi)

/-- **A union of pairwise disjoint open pieces is the disjoint union of the pieces.**  The canonical
homeomorphism `↥S ≃ₜ Σ i, ↥(o i)`, `z ↦ (i, z)` with `i` the index (unique, by disjointness) of a
piece containing `z`. -/
noncomputable def sigmaPiecesHomeo {ι Z : Type} [TopologicalSpace Z] {S : Set Z} (o : ι → Set Z)
    (hopen : ∀ i, IsOpen (o i)) (hdisj : ∀ i j, i ≠ j → Disjoint (o i) (o j))
    (hsub : ∀ i, o i ⊆ S) (hcov : ∀ z ∈ S, ∃ i, z ∈ o i) :
    ↥S ≃ₜ (Σ i, ↥(o i)) where
  toFun := fun z => ⟨Classical.choose (hcov z.1 z.2),
    ⟨z.1, Classical.choose_spec (hcov z.1 z.2)⟩⟩
  invFun := fun x => ⟨x.2.1, hsub x.1 x.2.2⟩
  left_inv := fun z => Subtype.ext rfl
  right_inv := by
    intro x
    obtain ⟨i, y⟩ := x
    have h : Classical.choose (hcov (y : Z) (hsub i y.2)) = i := by
      by_contra hne
      exact Set.disjoint_left.mp (hdisj (Classical.choose (hcov (y : Z) (hsub i y.2))) i hne)
        (Classical.choose_spec (hcov (y : Z) (hsub i y.2))) y.2
    have hiff : ∀ z : Z, z ∈ o (Classical.choose (hcov (y : Z) (hsub i y.2))) ↔ z ∈ o i :=
      fun z => ⟨fun hz => by rw [← h]; exact hz, fun hz => by rw [h]; exact hz⟩
    show (⟨Classical.choose (hcov (y : Z) (hsub i y.2)),
      ⟨(y : Z), Classical.choose_spec (hcov (y : Z) (hsub i y.2))⟩⟩ : Σ i, ↥(o i)) = ⟨i, y⟩
    exact Sigma.ext h ((Subtype.heq_iff_coe_eq hiff).mpr rfl)
  continuous_toFun := continuous_sigmaPieces_toFun o hopen hdisj hcov
  continuous_invFun := by
    refine continuous_sigma ?_
    intro i
    exact Continuous.subtype_mk continuous_subtype_val _


/-! ## The two projection formulas and the transfer of the isomorphism/surjectivity property
along a commuting square of maps of relative chain complexes -/

/-- The compatibility of `Work.Serre.relChainsRPairMap` with the projections onto the relative
chains. -/
theorem cokernel_π_pairMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (g : C(X, Y)) (hg : Set.MapsTo g A B) :
    cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) A) ≫ relChainsRPairMap A B g hg
      = Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom g)
        ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Y) B) := by
  unfold relChainsRPairMap
  exact Work.Serre.cokernel_π_csrRelMapOf

/-- The compatibility of `Work.Serre.relChainsRInclPairMap` with the projections onto the relative
chains. -/
theorem cokernel_π_inclPairMap (X : TopCat) (U A : Set X) :
    cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥U) {x : ↥U | (x : X) ∈ A})
      ≫ Work.Serre.relChainsRInclPairMap X U A
      = Work.Cohomology.chainMap ℚ (TopCat.of ↥U) X (Work.Cohomology.subtypeIncl X U)
        ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ X A) := by
  unfold Work.Serre.relChainsRInclPairMap
  exact Work.Serre.cokernel_π_csrRelMapOf

/-- `Work.Serre.csrRelMapOf` depends only on its two horizontal maps. -/
theorem csrRelMapOf_congr {X Y : TopCat} {A : Set X} {B : Set Y}
    {f₁ f₂ : X ⟶ Y} {g₁ g₂ : TopCat.of A ⟶ TopCat.of B} (hf : f₁ = f₂) (hg : g₁ = g₂)
    (w₁ : Work.Cohomology.subtypeIncl X A ≫ f₁ = g₁ ≫ Work.Cohomology.subtypeIncl Y B)
    (w₂ : Work.Cohomology.subtypeIncl X A ≫ f₂ = g₂ ≫ Work.Cohomology.subtypeIncl Y B) :
    Work.Serre.csrRelMapOf X Y A B f₁ g₁ w₁ = Work.Serre.csrRelMapOf X Y A B f₂ g₂ w₂ := by
  cases hf; cases hg; rfl

/-- **Transfer of `IsIso` along a commuting square to the first map**: if `a ≫ b = c ≫ d` and
`b`, `c`, `d` are isomorphisms on `H_m`, then so is `a`. -/
theorem isIso_of_sq_left {K L M Nc : ChainComplex (ModuleCat ℚ) ℕ}
    (a : K ⟶ L) (b : L ⟶ Nc) (c : K ⟶ M) (d : M ⟶ Nc) (hsq : a ≫ b = c ≫ d) (m : ℕ)
    (hb : IsIso (HomologicalComplex.homologyMap b m))
    (hc : IsIso (HomologicalComplex.homologyMap c m))
    (hd : IsIso (HomologicalComplex.homologyMap d m)) :
    IsIso (HomologicalComplex.homologyMap a m) := by
  have h := congrArg (fun t => HomologicalComplex.homologyMap t m) hsq
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
  haveI hb' : IsIso (HomologicalComplex.homologyMap b m) := hb
  haveI hc' : IsIso (HomologicalComplex.homologyMap c m) := hc
  haveI hd' : IsIso (HomologicalComplex.homologyMap d m) := hd
  haveI hab : IsIso (HomologicalComplex.homologyMap a m ≫ HomologicalComplex.homologyMap b m) :=
    h.symm ▸ (inferInstance : IsIso (HomologicalComplex.homologyMap c m
      ≫ HomologicalComplex.homologyMap d m))
  exact IsIso.of_isIso_comp_right (HomologicalComplex.homologyMap a m)
    (HomologicalComplex.homologyMap b m)

/-- **Transfer of `IsIso` along a commuting square to the second map**: if `a ≫ b = c ≫ d` and
`a`, `c`, `d` are isomorphisms on `H_m`, then so is `b`. -/
theorem isIso_of_sq_right {K L M Nc : ChainComplex (ModuleCat ℚ) ℕ}
    (a : K ⟶ L) (b : L ⟶ Nc) (c : K ⟶ M) (d : M ⟶ Nc) (hsq : a ≫ b = c ≫ d) (m : ℕ)
    (ha : IsIso (HomologicalComplex.homologyMap a m))
    (hc : IsIso (HomologicalComplex.homologyMap c m))
    (hd : IsIso (HomologicalComplex.homologyMap d m)) :
    IsIso (HomologicalComplex.homologyMap b m) := by
  have h := congrArg (fun t => HomologicalComplex.homologyMap t m) hsq
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
  haveI ha' : IsIso (HomologicalComplex.homologyMap a m) := ha
  haveI hc' : IsIso (HomologicalComplex.homologyMap c m) := hc
  haveI hd' : IsIso (HomologicalComplex.homologyMap d m) := hd
  haveI hab : IsIso (HomologicalComplex.homologyMap a m ≫ HomologicalComplex.homologyMap b m) :=
    h.symm ▸ (inferInstance : IsIso (HomologicalComplex.homologyMap c m
      ≫ HomologicalComplex.homologyMap d m))
  exact IsIso.of_isIso_comp_left (HomologicalComplex.homologyMap a m)
    (HomologicalComplex.homologyMap b m)

/-- **Transfer of surjectivity along a commuting square to the first map**: if `a ≫ b = c ≫ d`,
`b` is injective on `H_m` and `c`, `d` are surjective on `H_m`, then `a` is surjective on `H_m`. -/
theorem surjective_of_sq_left {K L M Nc : ChainComplex (ModuleCat ℚ) ℕ}
    (a : K ⟶ L) (b : L ⟶ Nc) (c : K ⟶ M) (d : M ⟶ Nc) (hsq : a ≫ b = c ≫ d) (m : ℕ)
    (hb : Function.Injective (HomologicalComplex.homologyMap b m).hom)
    (hc : Function.Surjective (HomologicalComplex.homologyMap c m).hom)
    (hd : Function.Surjective (HomologicalComplex.homologyMap d m).hom) :
    Function.Surjective (HomologicalComplex.homologyMap a m).hom := by
  have h := congrArg (fun t => HomologicalComplex.homologyMap t m) hsq
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
  have hcomp : Function.Surjective
      ((HomologicalComplex.homologyMap a m ≫ HomologicalComplex.homologyMap b m).hom) := by
    rw [h]
    simp only [ModuleCat.hom_comp]
    exact hd.comp hc
  intro z
  obtain ⟨x, hx⟩ := hcomp ((HomologicalComplex.homologyMap b m).hom z)
  exact ⟨x, hb hx⟩

/-- **Transfer of surjectivity along a commuting square to the second map**: if `a ≫ b = c ≫ d`
and `c`, `d` are surjective on `H_m`, then so is `b`. -/
theorem surjective_of_sq_right {K L M Nc : ChainComplex (ModuleCat ℚ) ℕ}
    (a : K ⟶ L) (b : L ⟶ Nc) (c : K ⟶ M) (d : M ⟶ Nc) (hsq : a ≫ b = c ≫ d) (m : ℕ)
    (hc : Function.Surjective (HomologicalComplex.homologyMap c m).hom)
    (hd : Function.Surjective (HomologicalComplex.homologyMap d m).hom) :
    Function.Surjective (HomologicalComplex.homologyMap b m).hom := by
  have h := congrArg (fun t => HomologicalComplex.homologyMap t m) hsq
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
  have hcomp : Function.Surjective
      ((HomologicalComplex.homologyMap a m ≫ HomologicalComplex.homologyMap b m).hom) := by
    rw [h]
    simp only [ModuleCat.hom_comp]
    exact hd.comp hc
  exact Function.Surjective.of_comp hcomp

end

end Work.Serre.CsrSharp.Tools
