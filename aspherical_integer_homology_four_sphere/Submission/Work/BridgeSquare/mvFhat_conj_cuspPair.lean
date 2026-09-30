/-
# `BridgeSquare/mvFhat_conj_cuspPair.lean` — `mvFhat k` is conjugate to the cusp pair `F_k`

This file proves `Work.BridgeSquare.ConjCuspPair k` for every degree `k`: the Mayer–Vietoris map
`mvFhat k : H_k(A ∩ B) ⟶ H_k(A) ⊞ H_k(B)` of the cover `M̂ = A ∪ B`, in the explicit
identifications `isoInter`, `biprodHomology`, `isoA`, `isoB` of the area, is the **cusp pair**

```
F_k := cuspPair k := biprod.lift (H_k τ) (H_k π) :
        H_k(⊔_v ∂[-1,1]² × T²_v) → H_k(M̄) ⊞ H_k(⊔_v T²_v)
```

with `τ = cuspMap` and `π = projMap`.

## The two isomorphisms

* `α := isoInter k` — the cusp-major identification `H_k(A ∩ B) ≅ H_k(⊔_v ∂[-1,1]² × T²_v)`;
* `β := biprodHomology … k ≪≫ biprod.mapIso (isoA k) (isoB k)` — the additivity of homology over
  the binary biproduct of the two pieces, followed by the identifications of the two pieces.

## The proof

Both sides are maps out of `H_k(A ∩ B)` into a binary biproduct, so it suffices to compare the two
components.  On the left, `mvSplit_eq_mvLift` rewrites `mvFhat k` composed with the additivity
isomorphism as the pair of the inclusions `H_k(A ∩ B) ↪ H_k(A)`, `H_k(A ∩ B) ↪ H_k(B)`, and
`β` naturality (`biprod_lift_map`) distributes the two piece identifications over the pair:

  `mvFhat k ≫ β.hom = biprod.lift (mvA k) (mvB k)`.

On the right, `cuspPair k` is a `biprod.lift`, so `α` distributes over it, and it remains to see
that the two components are `mvA k` and `mvB k`:

* `α.hom ≫ H_k(π) = mvB k` — this is `compatB` (`mvB = cuspB`) followed by the definition of
  `cuspB`;
* `α.hom ≫ H_k(τ) = mvA k` — this is `compatA` (`mvA = cuspA`), the identification
  `isoInter_eq` (`isoInter = isoABA ≪≫ isoDopCop`, so `α` factors through the glued boundary
  form `isoABA`) and the cancellation of the change of coordinates with the cusp parametrisation:
  `isoDopCop_hom_comp_cuspMap` says that `H_k(homeo) ≫ H_k(τ ∘ homeo.symm) = H_k(τ)`.

The bookkeeping lemmas of §1–§3 below do that; the only inputs from elsewhere are the two
compatibility squares `compatA`, `compatB`, the splitting `mvSplit_eq_mvLift` and the change of
coordinates `isoInter_eq`.
-/
import Mathlib
import Submission.Work.BridgeSquare.CuspPair
import Submission.Work.BridgeSquare.compatA
import Submission.Work.BridgeSquare.compatB
import Submission.Work.BridgeSquare.mvSplit_eq_mvLift
import Submission.Work.BridgeSquare.isoInter_eq

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open LeanEval.Topology
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Topology

namespace Work.BridgeSquare

/-! ## §1  Two naturality lemmas for binary biproducts

Mathlib's `biprod.map_fst`/`biprod.map_snd` give the components of `biprod.map`, from which the two
naturality statements used below follow by `biprod.hom_ext`. -/

lemma biprod_lift_map {C : Type*} [Category C] [HasZeroMorphisms C] {W X Y Z : C}
    [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y) (g : X ⟶ Z) {P : C}
    (a : P ⟶ W) (b : P ⟶ X) :
    biprod.lift a b ≫ biprod.map f g = biprod.lift (a ≫ f) (b ≫ g) := by
  apply biprod.hom_ext
  · rw [Category.assoc, biprod.map_fst, ← Category.assoc, biprod.lift_fst, biprod.lift_fst]
  · rw [Category.assoc, biprod.map_snd, ← Category.assoc, biprod.lift_snd, biprod.lift_snd]

lemma biprod_comp_lift {C : Type*} [Category C] [HasZeroMorphisms C] {X Y Z W : C}
    [HasBinaryBiproduct X Y] (h : W ⟶ Z) (f : Z ⟶ X) (g : Z ⟶ Y) :
    h ≫ biprod.lift f g = biprod.lift (h ≫ f) (h ≫ g) := by
  apply biprod.hom_ext
  · rw [Category.assoc, biprod.lift_fst, biprod.lift_fst]
  · rw [Category.assoc, biprod.lift_snd, biprod.lift_snd]

noncomputable section

variable [rt : Work.Space.RTData]

/-! ## §2  Functoriality of `homMap` -/

/-- `homMap` is functorial: the homology map of a composite is the composite of the homology
maps (the singular chain complex is a functor and homology is additive on composites). -/
lemma homMap_comp {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) (k : ℕ) :
    homMap (f ≫ g) k = homMap f k ≫ homMap g k := by
  unfold homMap
  simp only [Work.Cohomology.chainMap, Functor.map_comp, HomologicalComplex.homologyMap_comp]
  try rfl

/-! ## §3  The cusp parametrisation as a composite -/

/-- **The cusp parametrisation, as a composite.**  `cuspMap` is the parametrisation of the cusp
cross-section `⊔_v ∂[-1,1]² × T²_v` obtained by first transporting to the glued boundary
`{q : a.Y // q ∈ boundarySet}` along the canonical homeomorphism `homeoBdrySubSig` (read backwards)
and then applying the boundary parametrisation `tauBdry`. -/
lemma cuspMap_eq :
    cuspMap (rt := rt) =
      TopCat.ofHom (⟨fun x => (Work.Space.Split.homeoBdrySubSig rt.core).symm x,
        (Work.Space.Split.homeoBdrySubSig rt.core).symm.continuous⟩ :
          C(Cop (rt := rt), Dop (rt := rt))) ≫
      TopCat.ofHom (Work.Space.Assembly.tauBdry rt.core) := by
  rw [cuspMap, TopCat.ofHom_comp]

/-- The identification `isoDopCop` of the glued boundary with the cusp cross-section, in the
presentation of the map it induces on homology. -/
lemma homMap_ofHom_symm_eq (k : ℕ) :
    homMap (TopCat.ofHom (⟨fun x => (Work.Space.Split.homeoBdrySubSig rt.core).symm x,
        (Work.Space.Split.homeoBdrySubSig rt.core).symm.continuous⟩ :
          C(Cop (rt := rt), Dop (rt := rt)))) k
      = (intHomologyIsoOfHomotopyEquiv
          (((Work.Space.Split.homeoBdrySubSig rt.core).symm).toHomotopyEquiv) k).hom := rfl

/-- **The change of coordinates cancels the cusp parametrisation.**  Composing the homology
isomorphism `isoDopCop` (induced by the homeomorphism `homeoBdrySubSig : Dop ≃ₜ Cop`) with the map
`H_k(τ ∘ homeoBdrySubSig.symm)` induced by the cusp parametrisation `cuspMap` returns the identity:
the two homeomorphisms cancel.  This is `intHomologyIsoOfHomotopyEquiv_homeomorph_symm_trans` of
`Submission/Work/BridgeSquare/isoInter_eq.lean`. -/
lemma isoDopCop_hom_comp_homMap_symm (k : ℕ) :
    (isoDopCop (rt := rt) k).hom ≫
      homMap (TopCat.ofHom (⟨fun x => (Work.Space.Split.homeoBdrySubSig rt.core).symm x,
        (Work.Space.Split.homeoBdrySubSig rt.core).symm.continuous⟩ :
          C(Cop (rt := rt), Dop (rt := rt)))) k
      = 𝟙 (LeanEval.Topology.intHomology k (Dop (rt := rt))) := by
  have h1 : (isoDopCop (rt := rt) k ≪≫ intHomologyIsoOfHomotopyEquiv
      (((Work.Space.Split.homeoBdrySubSig rt.core).symm).toHomotopyEquiv) k) = Iso.refl _ :=
    intHomologyIsoOfHomotopyEquiv_homeomorph_symm_trans
      (X := Cop (rt := rt)) (Y := Dop (rt := rt))
      ((Work.Space.Split.homeoBdrySubSig rt.core).symm) k
  have h2 : (isoDopCop (rt := rt) k).hom ≫ (intHomologyIsoOfHomotopyEquiv
      (((Work.Space.Split.homeoBdrySubSig rt.core).symm).toHomotopyEquiv) k).hom
      = 𝟙 (LeanEval.Topology.intHomology k (Dop (rt := rt))) := by
    simpa using congrArg CategoryTheory.Iso.hom h1
  rw [← h2]
  exact congrArg (fun m => (isoDopCop (rt := rt) k).hom ≫ m) (homMap_ofHom_symm_eq (rt := rt) k)

/-- **The change of coordinates cancels the cusp parametrisation**, in the form used below:
`H_k(homeoBdrySubSig) ≫ H_k(cuspMap) = H_k(tauBdry)`. -/
lemma isoDopCop_hom_comp_cuspMap (k : ℕ) :
    (isoDopCop (rt := rt) k).hom ≫ homMap (cuspMap (rt := rt)) k
      = homMap (TopCat.ofHom (Work.Space.Assembly.tauBdry rt.core)) k := by
  rw [cuspMap_eq (rt := rt), homMap_comp, ← Category.assoc,
    isoDopCop_hom_comp_homMap_symm, Category.id_comp]

/-! ## §4  The two components of `α.hom ≫ cuspPair k` -/

/-- **The `A`-component**: `α.hom ≫ H_k(τ) = mvA k`, i.e. the `A`-piece of the cusp pair is the
`A`-component of the Mayer–Vietoris map.  By `isoInter_eq` the identification `isoInter` factors as
`isoABA ≪≫ isoDopCop`; `compatA` says `mvA = cuspA = isoABA.hom ≫ H_k(tauBdry)`, and the change of
coordinates `isoDopCop` cancels the homeomorphism inside `cuspMap`. -/
lemma isoInter_hom_comp_homMap_cuspMap (k : ℕ) :
    (isoInter (rt := rt) k).hom ≫ homMap (cuspMap (rt := rt)) k = mvA (rt := rt) k := by
  rw [compatA (rt := rt) k]
  have hα : (isoInter (rt := rt) k).hom =
      (isoABA (rt := rt) k).hom ≫ (isoDopCop (rt := rt) k).hom := by
    rw [isoInter_eq (rt := rt) k]
    rfl
  rw [hα, Category.assoc, isoDopCop_hom_comp_cuspMap]
  rfl

/-- **The `B`-component**: `α.hom ≫ H_k(π) = mvB k`, i.e. the `B`-piece of the cusp pair is the
`B`-component of the Mayer–Vietoris map.  This is `compatB` (`mvB = cuspB`) with the definition of
`cuspB`. -/
lemma isoInter_hom_comp_homMap_projMap (k : ℕ) :
    (isoInter (rt := rt) k).hom ≫ homMap (projMap (rt := rt)) k = mvB (rt := rt) k := by
  rw [compatB (rt := rt) k]
  rfl

/-! ## §5  The left-hand side of the square -/

/-- **`mvFhat k` composed with the additivity isomorphism is the pair of the two inclusions**
(`mvSplit_eq_mvLift`), in the form in which it is used below. -/
lemma mvFhat_comp_biprodHomology (k : ℕ) :
    Work.HomologyIso.mvFhat (rt := rt) k ≫
      (biprodHomology (Work.Homology.singChain Work.Homology.ZMod (Aop (rt := rt)))
        (Work.Homology.singChain Work.Homology.ZMod (Bop (rt := rt))) k).hom
      = mvLift (rt := rt) k := by
  rw [← mvSplit_eq_mvLift (rt := rt) k]
  rfl

end

/-! ## §6  The conjugation -/

set_option backward.isDefEq.respectTransparency false in
theorem mvFhat_conj_cuspPair [rt : Work.Space.RTData] (k : ℕ) :
    Work.BridgeSquare.ConjCuspPair (rt := rt) k := by
  -- the two isomorphisms of the conjugation: the cusp-major identification of `A ∩ B`, and the
  -- additivity of homology over `C_*(A) ⊞ C_*(B)` followed by the identifications of the pieces
  let β : Work.HomologyIso.HB (rt := rt) k ≅
      (LeanEval.Topology.intHomology k (Mop (rt := rt)) ⊞
        LeanEval.Topology.intHomology k (Top (rt := rt))) :=
    (biprodHomology (Work.Homology.singChain Work.Homology.ZMod (Aop (rt := rt)))
      (Work.Homology.singChain Work.Homology.ZMod (Bop (rt := rt))) k) ≪≫
      biprod.mapIso (isoA (rt := rt) k) (isoB (rt := rt) k)
  refine ⟨isoInter (rt := rt) k, β, ?_⟩
  have hβ : β.hom =
      (biprodHomology (Work.Homology.singChain Work.Homology.ZMod (Aop (rt := rt)))
        (Work.Homology.singChain Work.Homology.ZMod (Bop (rt := rt))) k).hom ≫
      biprod.map (isoA (rt := rt) k).hom (isoB (rt := rt) k).hom := rfl
  rw [hβ, ← Category.assoc, mvFhat_comp_biprodHomology]
  -- the left-hand side is the pair `(mvA k, mvB k)`
  rw [mvLift, biprod_lift_map]
  rw [show homMap (inclA (rt := rt)) k ≫ (isoA (rt := rt) k).hom = mvA (rt := rt) k from rfl,
      show homMap (inclB (rt := rt)) k ≫ (isoB (rt := rt) k).hom = mvB (rt := rt) k from rfl]
  -- the right-hand side is the pair `(α.hom ≫ H_k τ, α.hom ≫ H_k π)`
  rw [show cuspPair (rt := rt) k =
        biprod.lift (homMap (cuspMap (rt := rt)) k) (homMap (projMap (rt := rt)) k) from rfl]
  apply biprod.hom_ext
  · rw [Category.assoc, biprod.lift_fst, biprod.lift_fst]
    exact (isoInter_hom_comp_homMap_cuspMap (rt := rt) k).symm
  · rw [Category.assoc, biprod.lift_snd, biprod.lift_snd]
    exact (isoInter_hom_comp_homMap_projMap (rt := rt) k).symm

end Work.BridgeSquare
