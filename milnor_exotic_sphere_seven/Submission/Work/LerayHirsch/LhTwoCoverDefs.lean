import Mathlib
import Submission.Work.LerayHirsch.LhGlueDefs
import Submission.Work.Thom.luThomGen
import Submission.Work.Thom.honestDelta_mixedCup
import Submission.Work.LerayHirsch.nonempty_homeo_projSpace_bundleComap_subtype
import Submission.Work.LerayHirsch.zetaPow_comap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

attribute [-instance] AddCommGroup.toIntModule

/-!
# The two-cover Mayer–Vietoris ladder for Leray–Hirsch — the vocabulary

This module fixes the objects in which the proof of `Work.LerayHirsch.LerayHirschFull Z` from the
Leray–Hirsch statements on the two pieces `U`, `V` of a cover `B = U ∪ V` and on the overlap
`U ∩ V` is carried out (see `Submission/Work/LerayHirsch/lerayHirschFull_of_two_cover.lean`).

It is the *multi-class* version of `Work.Thom.luThomGen` (the ladder for the single cup map
`x ↦ π^*(x) ⌣ c`): here the comparison map is

  `(x_i)_{2i ≤ k} ↦ Σ_i π^*(x_i) ⌣ ζ^i`,   `ζ = c₁(ℓ)`,

i.e. (up to the identification `pdCohIso`) the Leray–Hirsch decomposition map, and the base side of
the ladder is the Mayer–Vietoris sequence of the cover with coefficients `⊕_i ℤ·t^i` (one copy of the
sequence for each power of the hyperplane class, in the successive degrees `k, k-2, k-4, …`).

## The ladder

  `MvM k --MvF--> MvP k --MvG--> MvQ k --MvD--> MvM (k+1)`   (base, `B` with the cover `U ∪ V`),
  `M₂ k --honestF--> P₂ k --honestG--> Q₂ k --honestDelta--> M₂ (k+1)`   (`P(E)`, `π⁻¹U ∪ π⁻¹V`),

with the comparison maps `MvTM`, `MvTP = biprod.map MvTU MvTV`, `MvTQ`:

* `MvM Z U V k = ∏_{2i ≤ k} H^{k-2i}(B)` — the source of the Leray–Hirsch map in degree `k`;
* `MvPUObj B m k W = ∏_{2i ≤ k} H^{k-2i}(W)` (for `W = U`, `V`) and
  `MvP B m k U V = MvPUObj B m k U ⊞ MvPUObj B m k V` — the rearranged `P`-term, so that the
  comparison map on the two pieces is literally `biprod.map (MvTU) (MvTV)`;
* `MvQ B m k U V = ∏_{2i ≤ k} H^{k-2i}(U ∩ V)`;
* `MvCM k i`, `MvCU k i`, `MvCV k i`, `MvCQ k i` — the individual summands (the `i`-th power of
  `ζ`), built from `Work.Thom.luTM` / `Work.Thom.luTU` / `Work.Thom.luTQ` (the single-class cup maps
  of `Work.Thom.luThomGen`), with the degree cast from `k - 2i + 2i` to `k`.

All of this is in the `pdCoh` (relative cohomology) model of the Thom chapter, so that the three
ladder squares are the naturality statements `Work.Thom.luF_comp`, `Work.Thom.luG_comp` and
`Work.Thom.luDelta_square` applied to each power of `ζ` separately.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom Work.Cohomology
open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}

/-! ## Degree transport in the `pdCoh` model -/

/-- The transport of a class of the pair `(X,A)` along an equality of degrees. -/
noncomputable def pdCast (X : TopCat) (A : Set X) {k l : ℕ} (h : k = l) :
    pdCoh X A k ⟶ pdCoh X A l :=
  eqToHom (congrArg (fun n => pdCoh X A n) h)

/-- The transport of a class of the pair `(U, U∩A)` along an equality of degrees. -/
noncomputable def pdSubCast (X : TopCat) (A U : Set X) {k l : ℕ} (h : k = l) :
    pdCohSub X A U k ⟶ pdCohSub X A U l :=
  eqToHom (congrArg (fun n => pdCohSub X A U n) h)

/-- **Restriction commutes with the degree cast.** -/
theorem pdCohRes_pdCast (X : TopCat) (A U : Set X) {k l : ℕ} (h : k = l) :
    pdCohRes X A U k ≫ pdSubCast X A U h = pdCast X A h ≫ pdCohRes X A U l := by
  subst h
  simp only [pdCast, pdSubCast, eqToHom_refl, Category.comp_id, Category.id_comp]

/-- **The comparison `pdCohIso` commutes with the degree cast** (absolute cohomology). -/
theorem pdCohIso_pdCast (B : Type) [TopologicalSpace B] {k l : ℕ} (h : k = l)
    (y : pdCoh (TopCat.of B) (∅ : Set B) k) :
    (pdCohIso B l).hom ((pdCast (TopCat.of B) (∅ : Set B) h).hom y)
      = cohTransport h ((pdCohIso B k).hom y) := by
  subst h
  simp [pdCast, cohTransport_rfl]

/-- **The comparison `pdCohIso` commutes with the degree cast on a piece.** -/
theorem pdCohIso_pdSubCast (X : TopCat) (U : Set X) {k l : ℕ} (h : k = l)
    (y : pdCohSub X (∅ : Set X) U k) :
    (pdCohIso ↥U l).hom ((pdSubCast X (∅ : Set X) U h).hom y)
      = cohTransport h ((pdCohIso ↥U k).hom y) := by
  subst h
  simp [pdSubCast, cohTransport_rfl]

/-! ## The classes `ζ^i` and their restrictions -/

/-- The power `ζ^i` of the hyperplane class, read in the relative cohomology of the pair
`(P(E),∅)`. -/
noncomputable def zetaRel (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (i : ℕ) : RelCoh ℤ (2 * i) (ProjSpace Z) (∅ : Set (ProjSpace Z)) :=
  (pdCohIso (ProjSpace Z) (2 * i)).inv (zetaPow Z i)

/-- The restriction of `ζ^i` to the piece of `P(E)` lying over `U`. -/
noncomputable def zetaRelPiece (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (U : Set B) (i : ℕ) :
    pdCohSub (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
      (projMap Z ⁻¹' U) (2 * i) :=
  (pdCohRes (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
    (projMap Z ⁻¹' U) (2 * i)).hom (zetaRel Z i)

/-- The restriction of `ζ^i` to the overlap of the two pieces. -/
noncomputable def zetaRelOvl (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (U V : Set B) (i : ℕ) :
    pdCohSub (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
      (projMap Z ⁻¹' U ∩ projMap Z ⁻¹' V) (2 * i) :=
  (pdCohRes (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
    (projMap Z ⁻¹' U ∩ projMap Z ⁻¹' V) (2 * i)).hom (zetaRel Z i)

@[simp] theorem zetaRelPiece_def (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    [Fintype ι] (U : Set B) (i : ℕ) :
    zetaRelPiece Z U i
      = (pdCohRes (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
          (projMap Z ⁻¹' U) (2 * i)).hom (zetaRel Z i) := rfl

@[simp] theorem zetaRelOvl_def (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    [Fintype ι] (U V : Set B) (i : ℕ) :
    zetaRelOvl Z U V i
      = (pdCohRes (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
          (projMap Z ⁻¹' U ∩ projMap Z ⁻¹' V) (2 * i)).hom (zetaRel Z i) := rfl


/-! ## Opaque presentations of the product terms

The ladder terms are products `∏_i H^{k-2i}(…)` of modules.  In Lean the type `Π i, M i` carries
*two* `Module ℤ` instances (the pointwise one and the one derived from the additive group), which do
not coincide definitionally; a statement mentioning a linear map with such a product as source
therefore has to pick one, and different files may pick different ones.  To keep the interface
robust, the terms are presented through the following type aliases, which carry their *own*
instances (declared at high priority). -/

/-- The product `∏ i, M i`, as a named type (so that its module structure is unambiguous). -/
def MvProd {ι : Type} (M : ι → Type) : Type := (i : ι) → M i

instance {ι : Type} {M : ι → Type} [∀ i, AddCommGroup (M i)] :
    AddCommGroup (MvProd M) :=
  inferInstanceAs (AddCommGroup ((i : ι) → M i))

instance {ι : Type} {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℤ (M i)] :
    Module ℤ (MvProd M) :=
  inferInstanceAs (Module ℤ ((i : ι) → M i))

/-- **The `i`-th projection of a product term** (as a linear map), the form in which the
componentwise maps of the ladder are expressed. -/
noncomputable def MvProj {ι : Type} {M : ι → Type} [∀ i, AddCommGroup (M i)]
    [∀ i, Module ℤ (M i)] (i : ι) : MvProd M →ₗ[ℤ] M i where
  toFun x := x i
  map_add' x y := rfl
  map_smul' c x := rfl

@[simp] theorem MvProj_apply {ι : Type} {M : ι → Type} [∀ i, AddCommGroup (M i)]
    [∀ i, Module ℤ (M i)] (i : ι) (x : MvProd M) : MvProj (M := M) i x = x i := rfl

/-! ## The terms of the ladder -/

/-- The `M`-term of the ladder in degree `k`: `∏_{2i ≤ k} H^{k-2i}(B;ℤ)`, the source of the
Leray–Hirsch map. -/
noncomputable abbrev MvM (B : Type) [TopologicalSpace B] (m k : ℕ) : ModuleCat ℤ :=
  ModuleCat.of ℤ (MvProd fun i : lhIdx m k =>
    ↑(pdCoh (TopCat.of B) (∅ : Set B) (k - 2 * (i : ℕ))))

/-- `∏_{2i ≤ k} H^{k-2i}(W;ℤ)`, the `W`-part of the `P`-term. -/
noncomputable abbrev MvW (B : Type) [TopologicalSpace B] (m k : ℕ) (W : Set B) : ModuleCat ℤ :=
  ModuleCat.of ℤ (MvProd fun i : lhIdx m k =>
    ↑(pdCohSub (TopCat.of B) (∅ : Set B) W (k - 2 * (i : ℕ))))

/-- The `P`-term of the ladder in degree `k`, in the *rearranged* form
`(∏_{2i ≤ k} H^{k-2i}(U)) ⊞ (∏_{2i ≤ k} H^{k-2i}(V))`. -/
noncomputable abbrev MvP (B : Type) [TopologicalSpace B] (m k : ℕ) (U V : Set B) : ModuleCat ℤ :=
  MvW B m k U ⊞ MvW B m k V

/-- The `Q`-term of the ladder in degree `k`: `∏_{2i ≤ k} H^{k-2i}(U ∩ V;ℤ)`. -/
noncomputable abbrev MvQ (B : Type) [TopologicalSpace B] (m k : ℕ) (U V : Set B) : ModuleCat ℤ :=
  ModuleCat.of ℤ (MvProd fun i : lhIdx m k =>
    ↑(pdCohSub (TopCat.of B) (∅ : Set B) (U ∩ V) (k - 2 * (i : ℕ))))

@[simp] theorem MvP_def (B : Type) [TopologicalSpace B] (m k : ℕ) (U V : Set B) :
    MvP B m k U V = (MvW B m k U ⊞ MvW B m k V) := rfl

@[simp] theorem MvW_def (B : Type) [TopologicalSpace B] (m k : ℕ) (W : Set B) :
    MvW B m k W = ModuleCat.of ℤ ((i : lhIdx m k) →
      ↑(pdCohSub (TopCat.of B) (∅ : Set B) W (k - 2 * (i : ℕ)))) := rfl

/-! ## The base side: the Mayer–Vietoris maps, componentwise -/

/-- The componentwise restriction to `W`, as a morphism
`∏_{2i ≤ k} H^{k-2i}(B) → ∏_{2i ≤ k} H^{k-2i}(W)`. -/
noncomputable def MvRes (B : Type) [TopologicalSpace B] (m k : ℕ) (W : Set B) :
    MvM B m k ⟶ MvW B m k W :=
  ModuleCat.ofHom (LinearMap.pi (fun i : lhIdx m k =>
    (pdCohRes (TopCat.of B) (∅ : Set B) W (k - 2 * (i : ℕ))).hom ∘ₗ LinearMap.proj i))

@[simp] theorem MvRes_apply (k : ℕ) (W : Set B) (x : ↑(MvM B m k)) (i : lhIdx m k) :
    (MvRes (B := B) m k W).hom x i
      = (pdCohRes (TopCat.of B) (∅ : Set B) W (k - 2 * (i : ℕ))).hom (x i) := rfl

/-- The componentwise restriction to the overlap `U ∩ V`, from the `U`-part. -/
noncomputable def MvResOvlU (B : Type) [TopologicalSpace B] (m k : ℕ) (U V : Set B) :
    MvW B m k U ⟶ MvQ B m k U V :=
  ModuleCat.ofHom (LinearMap.pi (fun i : lhIdx m k =>
    (pdCohMap (TopCat.of B) (∅ : Set B) U (U ∩ V) Set.inter_subset_left
      (k - 2 * (i : ℕ))).hom ∘ₗ LinearMap.proj i))

/-- The componentwise restriction to the overlap `U ∩ V`, from the `V`-part. -/
noncomputable def MvResOvlV (B : Type) [TopologicalSpace B] (m k : ℕ) (U V : Set B) :
    MvW B m k V ⟶ MvQ B m k U V :=
  ModuleCat.ofHom (LinearMap.pi (fun i : lhIdx m k =>
    (pdCohMap (TopCat.of B) (∅ : Set B) V (U ∩ V) Set.inter_subset_right
      (k - 2 * (i : ℕ))).hom ∘ₗ LinearMap.proj i))

@[simp] theorem MvResOvlU_apply (k : ℕ) (U V : Set B) (x : ↑(MvW B m k U)) (i : lhIdx m k) :
    (MvResOvlU (B := B) m k U V).hom x i
      = (pdCohMap (TopCat.of B) (∅ : Set B) U (U ∩ V) Set.inter_subset_left
          (k - 2 * (i : ℕ))).hom (x i) := rfl

@[simp] theorem MvResOvlV_apply (k : ℕ) (U V : Set B) (x : ↑(MvW B m k V)) (i : lhIdx m k) :
    (MvResOvlV (B := B) m k U V).hom x i
      = (pdCohMap (TopCat.of B) (∅ : Set B) V (U ∩ V) Set.inter_subset_right
          (k - 2 * (i : ℕ))).hom (x i) := rfl

/-- The first map of the base side of the ladder: the two componentwise restrictions. -/
noncomputable def MvF (B : Type) [TopologicalSpace B] (m k : ℕ) (U V : Set B) :
    MvM B m k ⟶ MvP B m k U V :=
  biprod.lift (MvRes B m k U) (MvRes B m k V)

/-- The second map of the base side of the ladder: the difference of the two componentwise
restrictions to the overlap. -/
noncomputable def MvG (B : Type) [TopologicalSpace B] (m k : ℕ) (U V : Set B) :
    MvP B m k U V ⟶ MvQ B m k U V :=
  biprod.desc (MvResOvlU B m k U V) (-(MvResOvlV B m k U V))

/-- The connecting map of the base side of the ladder: in the `i`-th component (for `2i ≤ k`) it is
the Mayer–Vietoris connecting map `H^{k-2i}(U∩V) → H^{k+1-2i}(B)`, and it is `0` in the new
component `2i = k+1` (which contributes no summand of `H^{k+1}`). -/
noncomputable def MvD (B : Type) [TopologicalSpace B] (m k : ℕ) (U V : Set B)
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) :
    MvQ B m k U V ⟶ MvM B m (k + 1) :=
  ModuleCat.ofHom (LinearMap.pi (fun i : lhIdx m (k + 1) =>
    if h : 2 * (i : ℕ) ≤ k then
      (pdCast (TopCat.of B) (∅ : Set B)
        (by omega : k - 2 * (i : ℕ) + 1 = k + 1 - 2 * (i : ℕ))).hom
        ∘ₗ (honestDelta (TopCat.of B) (∅ : Set B) U V hU hV hcov (k - 2 * (i : ℕ))).hom
        ∘ₗ LinearMap.proj (⟨i.1, h⟩ : lhIdx m k)
    else 0))

@[simp] theorem MvF_fst (k : ℕ) (U V : Set B) :
    MvF (B := B) m k U V ≫ biprod.fst = MvRes B m k U :=
  biprod.lift_fst _ _

@[simp] theorem MvF_snd (k : ℕ) (U V : Set B) :
    MvF (B := B) m k U V ≫ biprod.snd = MvRes B m k V :=
  biprod.lift_snd _ _

@[simp] theorem MvG_inl (k : ℕ) (U V : Set B) :
    biprod.inl ≫ MvG (B := B) m k U V = MvResOvlU B m k U V :=
  biprod.inl_desc _ _

@[simp] theorem MvG_inr (k : ℕ) (U V : Set B) :
    biprod.inr ≫ MvG (B := B) m k U V = -(MvResOvlV B m k U V) :=
  biprod.inr_desc _ _

/-! ## The comparison maps -/

/-- The `i`-th summand of the Leray–Hirsch comparison map on `P(E)`: `x ↦ π^*(x) ⌣ ζ^i`, from
`H^{k-2i}(B)` to `H^k(P(E))`. -/
noncomputable def MvCM (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (k : ℕ) (i : lhIdx m k) :
    pdCoh (TopCat.of B) (∅ : Set B) (k - 2 * (i : ℕ)) ⟶
      pdCoh (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) k :=
  luTM (projMap Z) (∅ : Set (ProjSpace Z)) (2 * (i : ℕ)) (zetaRel Z i) (k - 2 * (i : ℕ))
    ≫ pdCast (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
        (by omega : k - 2 * (i : ℕ) + 2 * (i : ℕ) = k)

/-- **The comparison map of the ladder on `P(E)`**: `(x_i) ↦ Σ_i π^*(x_i) ⌣ ζ^i`. -/
noncomputable def MvTM (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (k : ℕ) : MvM B m k ⟶ pdCoh (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) k :=
  ModuleCat.ofHom (∑ i : lhIdx m k, (MvCM Z k i).hom ∘ₗ MvProj i)

@[simp] theorem MvTM_apply (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (k : ℕ) (x : ↑(MvM B m k)) :
    (MvTM Z k).hom x = ∑ i : lhIdx m k, (MvCM Z k i).hom (x i) := by
  show (∑ i : lhIdx m k, (MvCM Z k i).hom ∘ₗ MvProj i) x
      = ∑ i : lhIdx m k, (MvCM Z k i).hom (x i)
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, MvProj_apply]

/-- The `i`-th summand of the comparison map on the piece of `P(E)` over `U`. -/
noncomputable def MvCU (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (U : Set B) (k : ℕ) (i : lhIdx m k) :
    pdCohSub (TopCat.of B) (∅ : Set B) U (k - 2 * (i : ℕ)) ⟶
      pdCohSub (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' U) k :=
  luTU (projMap Z) (∅ : Set (ProjSpace Z)) (2 * (i : ℕ)) (zetaRelPiece Z U i)
      (k - 2 * (i : ℕ))
    ≫ pdSubCast (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' U)
        (by omega : k - 2 * (i : ℕ) + 2 * (i : ℕ) = k)

/-- The comparison map on the piece of `P(E)` over `U`. -/
noncomputable def MvTU (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (U : Set B) (k : ℕ) : MvW B m k U ⟶
      pdCohSub (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' U) k :=
  ModuleCat.ofHom (∑ i : lhIdx m k, (MvCU Z U k i).hom ∘ₗ MvProj i)

@[simp] theorem MvTU_apply (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (U : Set B) (k : ℕ) (x : ↑(MvW B m k U)) :
    (MvTU Z U k).hom x = ∑ i : lhIdx m k, (MvCU Z U k i).hom (x i) := by
  show (∑ i : lhIdx m k, (MvCU Z U k i).hom ∘ₗ MvProj i) x
      = ∑ i : lhIdx m k, (MvCU Z U k i).hom (x i)
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, MvProj_apply]

/-- The `i`-th summand of the comparison map on the piece of `P(E)` over `V`. -/
noncomputable def MvCV (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (V : Set B) (k : ℕ) (i : lhIdx m k) :
    pdCohSub (TopCat.of B) (∅ : Set B) V (k - 2 * (i : ℕ)) ⟶
      pdCohSub (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' V) k :=
  luTU (projMap Z) (∅ : Set (ProjSpace Z)) (2 * (i : ℕ)) (zetaRelPiece Z V i)
      (k - 2 * (i : ℕ))
    ≫ pdSubCast (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' V)
        (by omega : k - 2 * (i : ℕ) + 2 * (i : ℕ) = k)

/-- The comparison map on the piece of `P(E)` over `V`. -/
noncomputable def MvTV (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (V : Set B) (k : ℕ) : MvW B m k V ⟶
      pdCohSub (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' V) k :=
  ModuleCat.ofHom (∑ i : lhIdx m k, (MvCV Z V k i).hom ∘ₗ MvProj i)

@[simp] theorem MvTV_apply (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (V : Set B) (k : ℕ) (x : ↑(MvW B m k V)) :
    (MvTV Z V k).hom x = ∑ i : lhIdx m k, (MvCV Z V k i).hom (x i) := by
  show (∑ i : lhIdx m k, (MvCV Z V k i).hom ∘ₗ MvProj i) x
      = ∑ i : lhIdx m k, (MvCV Z V k i).hom (x i)
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, MvProj_apply]

/-- The identification of the two syntactic forms of the overlap `π⁻¹U ∩ π⁻¹V = π⁻¹(U ∩ V)`. -/
noncomputable def MvOvlIso (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (U V : Set B) (k : ℕ) :
    pdCohSub (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
        (projMap Z ⁻¹' U ∩ projMap Z ⁻¹' V) k ≅
      pdCohSub (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
        (projMap Z ⁻¹' (U ∩ V)) k :=
  eqToIso (congrArg (fun S : Set (ProjSpace Z) =>
    pdCohSub (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) S k) ((Set.preimage_inter (f := projMap Z) (s := U) (t := V)).symm))

/-- The `i`-th summand of the comparison map on the overlap of the two pieces. -/
noncomputable def MvCQ (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (U V : Set B) (k : ℕ) (i : lhIdx m k) :
    pdCohSub (TopCat.of B) (∅ : Set B) (U ∩ V) (k - 2 * (i : ℕ)) ⟶
      pdCohSub (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
        (projMap Z ⁻¹' U ∩ projMap Z ⁻¹' V) k :=
  luTQ (projMap Z) (∅ : Set (ProjSpace Z)) (2 * (i : ℕ)) (zetaRelOvl Z U V i)
      (k - 2 * (i : ℕ))
    ≫ pdSubCast (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
        (projMap Z ⁻¹' U ∩ projMap Z ⁻¹' V) (by omega : k - 2 * (i : ℕ) + 2 * (i : ℕ) = k)

/-- The comparison map on the overlap of the two pieces. -/
noncomputable def MvTQ (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (U V : Set B) (k : ℕ) : MvQ B m k U V ⟶
      pdCohSub (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
        (projMap Z ⁻¹' U ∩ projMap Z ⁻¹' V) k :=
  ModuleCat.ofHom (∑ i : lhIdx m k, (MvCQ Z U V k i).hom ∘ₗ MvProj i)

@[simp] theorem MvTQ_apply (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (U V : Set B) (k : ℕ) (x : ↑(MvQ B m k U V)) :
    (MvTQ Z U V k).hom x = ∑ i : lhIdx m k, (MvCQ Z U V k i).hom (x i) := by
  show (∑ i : lhIdx m k, (MvCQ Z U V k i).hom ∘ₗ MvProj i) x
      = ∑ i : lhIdx m k, (MvCQ Z U V k i).hom (x i)
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, MvProj_apply]

/-- **The comparison map on the two pieces**: on the `U`-part (resp. the `V`-part) of the `P`-term
it is the Leray–Hirsch map of `P(Z|_U)` (resp. of `P(Z|_V)`). -/
noncomputable def MvTP (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (U V : Set B) (k : ℕ) : MvP B m k U V ⟶
      pdCohBiprod (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
        (projMap Z ⁻¹' U) (projMap Z ⁻¹' V) k :=
  biprod.map (MvTU Z U k) (MvTV Z V k)

@[simp] theorem MvTP_def (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (U V : Set B) (k : ℕ) :
    MvTP Z U V k = biprod.map (MvTU Z U k) (MvTV Z V k) := rfl

/-- **The connecting map of the ladder on the overlap**: the Mayer–Vietoris connecting map of the
cover `(π⁻¹U, π⁻¹V)` of `P(E)`. -/
noncomputable def MvDeltaTwo (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    {U V : Set B} (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (k : ℕ) :
    pdCohSub (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
        (projMap Z ⁻¹' U ∩ projMap Z ⁻¹' V) k ⟶
      pdCoh (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (k + 1) :=
  honestDelta (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
    (projMap Z ⁻¹' U) (projMap Z ⁻¹' V) (hU.preimage (projMap Z).continuous)
    (hV.preimage (projMap Z).continuous)
    (by rw [← Set.preimage_union, hcov, Set.preimage_univ]) k

/-- The first map of the second sequence of the ladder. -/
noncomputable def MvF₂ (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (U V : Set B) (k : ℕ) :
    pdCoh (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) k ⟶
      pdCohBiprod (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
        (projMap Z ⁻¹' U) (projMap Z ⁻¹' V) k :=
  honestF (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
    (projMap Z ⁻¹' U) (projMap Z ⁻¹' V) k

/-- The second map of the second sequence of the ladder. -/
noncomputable def MvG₂ (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (U V : Set B) (k : ℕ) :
    pdCohBiprod (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
        (projMap Z ⁻¹' U) (projMap Z ⁻¹' V) k ⟶
      pdCohSub (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
        (projMap Z ⁻¹' U ∩ projMap Z ⁻¹' V) k :=
  honestG (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
    (projMap Z ⁻¹' U) (projMap Z ⁻¹' V) k

end

end Work.LerayHirsch
