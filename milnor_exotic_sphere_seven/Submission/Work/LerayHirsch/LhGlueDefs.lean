import Mathlib
import Submission.Work.LerayHirsch.LH
import Submission.Work.LerayHirsch.lhMap_comap
import Submission.Work.LerayHirsch.nonempty_homeo_projSpace_bundleComap_subtype
import Submission.Work.Thom.Ladder2
import Submission.Work.Thom.transgressionSquare
import Submission.Work.Thom.honestDelta_mixedCup
import Submission.Work.Thom.transgressionNatural
import Submission.Work.Thom.thomClass_of_cover

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

attribute [-instance] AddCommGroup.toIntModule

/-!
# Vocabulary for the Mayer–Vietoris rung of Leray–Hirsch

This module fixes the objects in which the proof of `Work.LerayHirsch.LerayHirschGlue` is carried
out.

* `Work.LerayHirsch.lhIdx m k` is the index type `{i : Fin m // 2 * i ≤ k}` of the powers of the
  hyperplane class in total degree `k`;
* `Work.LerayHirsch.lhAny` is the *uniform* Leray–Hirsch map in degree `k`
  (`(x_i) ↦ Σ_i π^*(x_i) ⌣ ζ^i`), defined for every `k` — it degenerates to `lhMap` in even degrees
  and to `lhMapOdd` in odd degrees (`Work.LerayHirsch.lhAny_bijective_iff`);
* `mv2F`, `mv2G`, `mv2δ` are the three maps of the two-set absolute Mayer–Vietoris long exact
  sequence of a space `X` with an open cover `U ∪ V = X`, in terms of the singular cohomology
  `Work.Thom.Coh` (the honest relative sequence of `Submission/Work/Cohomology/relCohMV_honest_les`
  for the pair `(X,∅)`, transported along `Work.Thom.pdCohIso`);
* `lM₁, lP₁, lQ₁, lF₁, lG₁, lδ₁` are the terms and maps of the *base* side of the ladder: the
  Mayer–Vietoris sequence of the cover `(U,V)` of `B`, tensored with the free module
  `⊕_{i<m} ℤ·ζ^i` (the "degree shift by `2i`"), i.e. with terms
  `⨁_i H^{k-2i}(B)`, `⨁_i (H^{k-2i}(U) ⊕ H^{k-2i}(V))`, `⨁_i H^{k-2i}(U∩V)`;
* `lM₂, lP₂, lQ₂, lF₂, lG₂, lδ₂` are the terms and maps of the *total space* side: the honest
  Mayer–Vietoris sequence of the cover `(π⁻¹U, π⁻¹V)` of `P(E)` (in the `pdCoh` world of the Thom
  chapter);
* `lTM, lTQ, lTP` (in `LhGlueCompares`) are the comparison maps of the ladder.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom
open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {B : Type} [TopologicalSpace B] {B' : Type} [TopologicalSpace B']
variable {ι : Type} {m : ℕ}

/-! ## 1. The uniform Leray–Hirsch map -/

/-- The index type of the powers `ζ^i` contributing to total degree `k`: `2 * i ≤ k`. -/
abbrev lhIdx (m k : ℕ) : Type := {i : Fin m // 2 * (i : ℕ) ≤ k}

/-- Evaluation of a linear functional at a fixed vector, as a linear map. -/
def evalLM {M P : Type} [AddCommMonoid M] [AddCommMonoid P] [Module ℤ M] [Module ℤ P] (y : M) :
    (M →ₗ[ℤ] P) →ₗ[ℤ] P where
  toFun f := f y
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The `i`-th summand of the uniform Leray–Hirsch map, as a linear map of the `i`-th component of
the product `∏_{j} H^{k-2j}(B)`. -/
def lhAnySummand (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι] (k : ℕ)
    (i : lhIdx m k) :
    ((j : lhIdx m k) → ↑(Coh ℤ (k - 2 * (j : ℕ)) B)) →ₗ[ℤ] ↑(Coh ℤ k (ProjSpace Z)) :=
  (Work.Thom.cohTransportLM (n := k - 2 * (i : ℕ) + 2 * (i : ℕ)) (n' := k) (by omega)).comp
    ((evalLM (zetaPow Z i)).comp
      (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB (ProjSpace Z)) (k - 2 * (i : ℕ)) (2 * (i : ℕ))))
    ∘ₗ ((CohMap (projMap Z) ℤ (k - 2 * (i : ℕ))).hom ∘ₗ LinearMap.proj (R := ℤ) i)

/-- **The uniform Leray–Hirsch map** in total degree `k`:
`(x_i)_{2i ≤ k} ↦ Σ_i π^*(x_i) ⌣ ζ^i`.  For `k = 2k'` it is `lhMap Z k'` and for `k = 2k'+1` it
is `lhMapOdd Z k'` (up to the canonical identification of the index types), see
`Work.LerayHirsch.lhAny_bijective_iff`. -/
def lhAnyLM (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι] (k : ℕ) :
    ((i : lhIdx m k) → ↑(Coh ℤ (k - 2 * (i : ℕ)) B)) →ₗ[ℤ] ↑(Coh ℤ k (ProjSpace Z)) :=
  ∑ i : lhIdx m k, lhAnySummand Z k i

/-- The uniform Leray–Hirsch map, as a function. -/
def lhAny (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι] (k : ℕ)
    (x : (i : lhIdx m k) → Coh ℤ (k - 2 * (i : ℕ)) B) : Coh ℤ k (ProjSpace Z) :=
  lhAnyLM Z k x

@[simp] theorem lhAny_apply (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (k : ℕ) (x : (i : lhIdx m k) → Coh ℤ (k - 2 * (i : ℕ)) B) :
    lhAny Z k x = lhAnyLM Z k x := rfl

/-! ## 2. The two-set Mayer–Vietoris maps in the singular cohomology of the chapter -/

variable {X : Type} [TopologicalSpace X]

/-- The inclusion `U ∩ V ↪ U`. -/
def mvInclLeft (U V : Set X) : C(↥(U ∩ V), ↥U) :=
  ⟨fun y => ⟨y.1, y.2.1⟩, continuous_subtype_val.subtype_mk _⟩

/-- The inclusion `U ∩ V ↪ V`. -/
def mvInclRight (U V : Set X) : C(↥(U ∩ V), ↥V) :=
  ⟨fun y => ⟨y.1, y.2.2⟩, continuous_subtype_val.subtype_mk _⟩

/-- The first map of the two-set Mayer–Vietoris sequence: the two restrictions, in the
chapter's cohomology `Coh`. -/
def mv2F (U V : Set X) (k : ℕ) :
    Coh ℤ k X ⟶ Coh ℤ k ↥U ⊞ Coh ℤ k ↥V :=
  (pdCohIso X k).inv ≫ Work.Cohomology.honestF (TopCat.of X) (∅ : Set X) U V k
    ≫ (biprod.mapIso (pdCohIso ↥U k) (pdCohIso ↥V k)).hom

/-- The second map of the two-set Mayer–Vietoris sequence: the difference of the two restrictions
to the overlap. -/
def mv2G (U V : Set X) (k : ℕ) :
    Coh ℤ k ↥U ⊞ Coh ℤ k ↥V ⟶ Coh ℤ k ↥(U ∩ V) :=
  (biprod.mapIso (pdCohIso ↥U k) (pdCohIso ↥V k)).inv
    ≫ Work.Cohomology.honestG (TopCat.of X) (∅ : Set X) U V k
    ≫ (pdCohIso ↥(U ∩ V) k).hom

/-- The connecting homomorphism of the two-set Mayer–Vietoris sequence. -/
def mv2δ (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (k : ℕ) :
    Coh ℤ k ↥(U ∩ V) ⟶ Coh ℤ (k + 1) X :=
  (pdCohIso ↥(U ∩ V) k).inv
    ≫ Work.Cohomology.honestDelta (TopCat.of X) (∅ : Set X) U V hU hV hcov k
    ≫ (pdCohIso X (k + 1)).hom

/-! ## 3. The base side of the ladder: the Mayer–Vietoris sequence of `B` tensored with `⊕ ℤ·ζ^i` -/

/-- The `M`-term of the base side in degree `k`: `⨁_{2i ≤ k} H^{k-2i}(B)`. -/
def lM₁ (B : Type) [TopologicalSpace B] (m k : ℕ) : ModuleCat ℤ :=
  ModuleCat.of ℤ ((i : lhIdx m k) → ↑(Coh ℤ (k - 2 * (i : ℕ)) B))

/-- The `P`-term of the base side in degree `k`: `⨁_{2i ≤ k} (H^{k-2i}(U) ⊕ H^{k-2i}(V))`. -/
def lP₁ (B : Type) [TopologicalSpace B] (m k : ℕ) (U V : Set B) : ModuleCat ℤ :=
  ModuleCat.of ℤ ((i : lhIdx m k) →
    ↑(Coh ℤ (k - 2 * (i : ℕ)) ↥U ⊞ Coh ℤ (k - 2 * (i : ℕ)) ↥V))

/-- The `Q`-term of the base side in degree `k`: `⨁_{2i ≤ k} H^{k-2i}(U ∩ V)`. -/
def lQ₁ (B : Type) [TopologicalSpace B] (m k : ℕ) (U V : Set B) : ModuleCat ℤ :=
  ModuleCat.of ℤ ((i : lhIdx m k) → ↑(Coh ℤ (k - 2 * (i : ℕ)) ↥(U ∩ V)))

/-- The first map of the base side: the two restrictions, componentwise. -/
def lF₁LM (U V : Set B) (k : ℕ) :
    ((i : lhIdx m k) → ↑(Coh ℤ (k - 2 * (i : ℕ)) B)) →ₗ[ℤ]
      ((i : lhIdx m k) → ↑(Coh ℤ (k - 2 * (i : ℕ)) ↥U ⊞ Coh ℤ (k - 2 * (i : ℕ)) ↥V)) :=
  LinearMap.pi (fun i => (ModuleCat.Hom.hom (biprod.lift (restrCoh U ℤ (k - 2 * (i : ℕ)))
      (restrCoh V ℤ (k - 2 * (i : ℕ))))) ∘ₗ LinearMap.proj (R := ℤ) i)

/-- The second map of the base side: the difference of the two restrictions to the overlap,
componentwise. -/
def lG₁LM (U V : Set B) (k : ℕ) :
    ((i : lhIdx m k) → ↑(Coh ℤ (k - 2 * (i : ℕ)) ↥U ⊞ Coh ℤ (k - 2 * (i : ℕ)) ↥V)) →ₗ[ℤ]
      ((i : lhIdx m k) → ↑(Coh ℤ (k - 2 * (i : ℕ)) ↥(U ∩ V))) :=
  LinearMap.pi (fun i => (ModuleCat.Hom.hom (biprod.desc
      (CohMap (mvInclLeft U V) ℤ (k - 2 * (i : ℕ)))
      (-(CohMap (mvInclRight U V) ℤ (k - 2 * (i : ℕ)))))) ∘ₗ LinearMap.proj (R := ℤ) i)

/-- The connecting map of the base side: the degree-`(k-2i)` Mayer–Vietoris connecting map
`H^{k-2i}(U∩V) → H^{k+1-2i}(B)` in the `i`-th component, and `0` in the extra component. -/
def lδ₁LM (U V : Set B) (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (k : ℕ) :
    ((i : lhIdx m k) → ↑(Coh ℤ (k - 2 * (i : ℕ)) ↥(U ∩ V))) →ₗ[ℤ]
      ((i : lhIdx m k.succ) → ↑(Coh ℤ (k.succ - 2 * (i : ℕ)) B)) :=
  LinearMap.pi (fun i : lhIdx m k.succ =>
    if h : 2 * (i : ℕ) ≤ k then
      ((Work.Thom.cohTransportLM
        (n := (k - 2 * (i : ℕ)) + 1) (n' := k.succ - 2 * (i : ℕ)) (by omega)).comp
        (mv2δ U V hU hV hcov (k - 2 * (i : ℕ))).hom)
        ∘ₗ LinearMap.proj (R := ℤ) (⟨i.1, h⟩ : lhIdx m k)
    else 0)

/-- The first map of the base side, as a morphism. -/
def lF₁ (U V : Set B) (k : ℕ) : lM₁ B m k ⟶ lP₁ B m k U V :=
  ModuleCat.ofHom (lF₁LM (m := m) U V k)

/-- The second map of the base side, as a morphism. -/
def lG₁ (U V : Set B) (k : ℕ) : lP₁ B m k U V ⟶ lQ₁ B m k U V :=
  ModuleCat.ofHom (lG₁LM (m := m) U V k)

/-- The connecting map of the base side, as a morphism. -/
def lδ₁ (U V : Set B) (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (k : ℕ) :
    lQ₁ B m k U V ⟶ lM₁ B m k.succ :=
  ModuleCat.ofHom (lδ₁LM (m := m) U V hU hV hcov k)

/-! ## 4. The total space side of the ladder: the honest Mayer–Vietoris sequence of `P(E)` -/

/-- The `M`-term of the total space side in degree `k`: the absolute cohomology `H^k(P(E))` of the
projectivisation, in the `pdCoh` model of the Thom chapter. -/
def lM₂ (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (k : ℕ) : ModuleCat ℤ :=
  Work.Cohomology.pdCoh (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) k

/-- The `P`-term of the total space side in degree `k`: the cohomology of the two pieces
`π⁻¹U`, `π⁻¹V` of the projectivisation. -/
def lP₂ (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (U V : Set B) (k : ℕ) :
    ModuleCat ℤ :=
  Work.Cohomology.pdCohBiprod (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
    (projMap Z ⁻¹' U) (projMap Z ⁻¹' V) k

/-- The `Q`-term of the total space side in degree `k`: the cohomology of the overlap. -/
def lQ₂ (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (U V : Set B) (k : ℕ) :
    ModuleCat ℤ :=
  Work.Cohomology.pdCohSub (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
    (projMap Z ⁻¹' U ∩ projMap Z ⁻¹' V) k

/-- The first map of the total space side. -/
def lF₂ (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (U V : Set B) (k : ℕ) :
    lM₂ Z k ⟶ lP₂ Z U V k :=
  Work.Cohomology.honestF (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
    (projMap Z ⁻¹' U) (projMap Z ⁻¹' V) k

/-- The second map of the total space side. -/
def lG₂ (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (U V : Set B) (k : ℕ) :
    lP₂ Z U V k ⟶ lQ₂ Z U V k :=
  Work.Cohomology.honestG (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
    (projMap Z ⁻¹' U) (projMap Z ⁻¹' V) k

/-- The connecting map of the total space side. -/
def lδ₂ (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (U V : Set B)
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (k : ℕ) :
    lQ₂ Z U V k ⟶ lM₂ Z k.succ :=
  Work.Cohomology.honestDelta (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
    (projMap Z ⁻¹' U) (projMap Z ⁻¹' V) (hU.preimage (projMap Z).continuous)
    (hV.preimage (projMap Z).continuous) (by
      rw [← Set.preimage_union, hcov, Set.preimage_univ]) k
    ≫ eqToHom (congrArg (fun t => Work.Cohomology.pdCoh (TopCat.of (ProjSpace Z))
        (∅ : Set (ProjSpace Z)) t) (by omega : k + 1 = k.succ))

/-! ## 5. The canonical identification of a piece of the projectivisation -/

/-- **The canonical map from `P(Z|_U)` onto the piece of `P(E)` over `U`**: the class of a point of
the punctured total space of `Z|_U` is mapped to the class of the corresponding point of `P(E)`.
Its underlying function is `Work.LerayHirsch.projMapComap Z (subtypeMap U)`, restricted to the
piece `π⁻¹U`. -/
def pieceMap (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (U : Set B) :
    C(ProjSpace (bundleComap Z (subtypeMap U)), ↥(projMap Z ⁻¹' U)) where
  toFun x := ⟨projMapComap Z (subtypeMap U) x, by
    show projMap Z (projMapComap Z (subtypeMap U) x) ∈ U
    rw [projMap_projMapComap]
    exact (projMap (bundleComap Z (subtypeMap U)) x).2⟩
  continuous_toFun := (projMapComap Z (subtypeMap U)).continuous.subtype_mk (fun x => by
    change projMap Z (projMapComap Z (subtypeMap U) x) ∈ U
    rw [projMap_projMapComap]
    exact (projMap (bundleComap Z (subtypeMap U)) x).2)

/-- The *inverse* of `Work.LerayHirsch.pieceMap`, as a bare function: a class in `P(E)` lying over
`U` is lifted to the punctured total space of `Z` and read in the punctured total space of `Z|_U`
through `Work.LerayHirsch.comapZeroInv`. -/
def pieceMapInvFun (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (U : Set B)
    (y : ↥(projMap Z ⁻¹' U)) :
    ProjSpace (bundleComap Z (subtypeMap U)) :=
  mkProj (bundleComap Z (subtypeMap U))
    (comapZeroInv Z U ⟨Classical.choose (surjective_mkProj Z y.1), by
      have h := Classical.choose_spec (surjective_mkProj Z y.1)
      have h2 : projMap Z (mkProj Z (Classical.choose (surjective_mkProj Z y.1))) ∈ U := by
        rw [h]; exact y.2
      simpa using h2⟩)

end

end Work.LerayHirsch
