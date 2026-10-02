import Submission.Work.Serre.Defs
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.isZero_homology_of_homotopyEquiv

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# SUBPROJECT SERRE — the elementary API of the vocabulary

Everything here is a general fact about `IsRatHomologyIso`, `RatAcyclic` and `RatVanishingBelow`
(`Submission/Work/Serre/Defs.lean`), proved from the workspace's homotopy invariance of singular
homology (`Work.Cohomology.homologyEquiv`).

Composition convention: for `f : C(X,Y)` and `g : C(Y,Z)` the composite "first `f`, then `g`" is
written `g.comp f` (`ContinuousMap.comp`'s first explicit argument is the *outer* map).
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace Work.Serre

noncomputable section

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- A zero object of `ModuleCat ℚ` has a subsingleton underlying type (the elementwise form of
`IsZero`, used to feed `Work.RatHurewicz`'s `Subsingleton`-valued hypotheses). -/
theorem subsingleton_of_isZero {M : ModuleCat ℚ} (h : IsZero M) : Subsingleton (↥M) := by
  have hid : (𝟙 M : M ⟶ M) = 0 := IsZero.eq_of_src h _ _
  have hzero : ∀ a : ↥M, a = 0 := by
    intro a
    have h2 : (ModuleCat.Hom.hom (𝟙 M : M ⟶ M)) a = (ModuleCat.Hom.hom (0 : M ⟶ M)) a := by
      rw [hid]
    simpa using h2
  exact ⟨fun a b => by rw [hzero a, hzero b]⟩

/-- The rational chain map of an identity is an identity. -/
theorem chainMap_id_rat (X : TopCat) :
    Work.Cohomology.chainMap ℚ X X (𝟙 X) = 𝟙 (ratChains X) :=
  CategoryTheory.Functor.map_id _ _

theorem ratHomologyMap_id (X : Type) [TopologicalSpace X] (n : ℕ) :
    ratHomologyMap (ContinuousMap.id X) n = 𝟙 (ratH (TopCat.of X) n) := by
  have h1 : TopCat.ofHom (ContinuousMap.id X) = 𝟙 (TopCat.of X) := by
    ext x; rfl
  change HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of X)
        (TopCat.ofHom (ContinuousMap.id X))) n = 𝟙 (ratH (TopCat.of X) n)
  rw [h1, chainMap_id_rat, HomologicalComplex.homologyMap_id]

theorem ratHomologyMap_comp (f : C(X, Y)) (g : C(Y, Z)) (n : ℕ) :
    ratHomologyMap (g.comp f) n = ratHomologyMap f n ≫ ratHomologyMap g n := by
  have h1 : TopCat.ofHom (g.comp f) = TopCat.ofHom f ≫ TopCat.ofHom g := by
    ext x; rfl
  change HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Z)
        (TopCat.ofHom (g.comp f))) n
    = HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)) n
      ≫ HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℚ (TopCat.of Y) (TopCat.of Z) (TopCat.ofHom g)) n
  rw [h1]
  rw [show Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Z)
        (TopCat.ofHom f ≫ TopCat.ofHom g)
      = Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f) ≫
        Work.Cohomology.chainMap ℚ (TopCat.of Y) (TopCat.of Z) (TopCat.ofHom g) from
    CategoryTheory.Functor.map_comp _ _ _]
  rw [HomologicalComplex.homologyMap_comp]

namespace IsRatHomologyIso

protected theorem id (X : Type) [TopologicalSpace X] : IsRatHomologyIso (ContinuousMap.id X) := by
  intro n; rw [ratHomologyMap_id]; infer_instance

protected theorem comp {f : C(X, Y)} {g : C(Y, Z)} (hf : IsRatHomologyIso f)
    (hg : IsRatHomologyIso g) : IsRatHomologyIso (g.comp f) := by
  intro n
  rw [ratHomologyMap_comp f g n]
  haveI : IsIso (ratHomologyMap f n) := hf n
  haveI : IsIso (ratHomologyMap g n) := hg n
  infer_instance

/-- A homotopy equivalence is a rational homology isomorphism. -/
theorem of_homotopyEquiv (e : ContinuousMap.HomotopyEquiv X Y) : IsRatHomologyIso e.toFun := by
  intro n
  exact Work.Cohomology.homologyEquiv ℚ (TopCat.of X) (TopCat.of Y)
    (TopCat.ofHom e.toFun) (TopCat.ofHom e.invFun)
    (e.left_inv.some) (e.right_inv.some) n

end IsRatHomologyIso

/-- **Acyclicity is transported along a rational homology isomorphism**: if `f : X → Y` is one and
`Y` is rationally acyclic, then so is `X`. -/
theorem RatAcyclic.of_isRatHomologyIso {f : C(X, Y)} (hf : IsRatHomologyIso f)
    (hY : RatAcyclic Y) : RatAcyclic X := by
  have h := IsRatHomologyIso.comp hf hY
  rwa [show (toPoint Y).comp f = toPoint X from ContinuousMap.ext fun x => rfl] at h

/-- The one-point space is rationally acyclic. -/
theorem ratAcyclic_punit : RatAcyclic PUnit := by
  have h : toPoint PUnit = ContinuousMap.id PUnit := ContinuousMap.ext fun x => rfl
  rw [RatAcyclic, h]; exact IsRatHomologyIso.id PUnit

/-- **A contractible space is rationally acyclic.**  This is the only case of blueprint E0 that
follows from homotopy invariance of homology alone. -/
theorem ratAcyclic_of_contractible (X : Type) [TopologicalSpace X] [ContractibleSpace X] :
    RatAcyclic X := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv X PUnit
  exact RatAcyclic.of_isRatHomologyIso (IsRatHomologyIso.of_homotopyEquiv e) ratAcyclic_punit

/-- Homotopy equivalent spaces are simultaneously rationally acyclic. -/
theorem ratAcyclic_of_homotopyEquiv (e : ContinuousMap.HomotopyEquiv X Y) (hY : RatAcyclic Y) :
    RatAcyclic X :=
  RatAcyclic.of_isRatHomologyIso (IsRatHomologyIso.of_homotopyEquiv e) hY

/-- **`H_j` vanishes for `0 < j`** for a rationally acyclic space. -/
theorem RatAcyclic.isZero_ratH (h : RatAcyclic X) {j : ℕ} (hj : 0 < j) :
    IsZero (ratH (TopCat.of X) j) := by
  haveI : IsIso (ratHomologyMap (toPoint X) j) := h j
  have h0 : IsZero (ratH (TopCat.of PUnit) j) :=
    Work.Cohomology.homologyContractible_ring ℚ (X := TopCat.of PUnit) j hj
  exact IsZero.of_iso h0 (asIso (ratHomologyMap (toPoint X) j))

/-- **`H_j(X;ℚ) = 0` for `0 < j`**, in the `Subsingleton` form. -/
theorem RatAcyclic.subsingleton_ratH (h : RatAcyclic X) {j : ℕ} (hj : 0 < j) :
    Subsingleton ↥(ratH (TopCat.of X) j) :=
  subsingleton_of_isZero (h.isZero_ratH hj)

/-- **`RatAcyclic` implies `RatVanishingBelow m` for every `m`.** -/
theorem RatAcyclic.ratVanishingBelow (h : RatAcyclic X) (m : ℕ) : RatVanishingBelow X m :=
  fun _ hj _ => h.isZero_ratH hj

end

end Work.Serre
