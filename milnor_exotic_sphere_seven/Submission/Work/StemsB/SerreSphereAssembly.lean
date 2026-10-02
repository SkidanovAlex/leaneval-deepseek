import Submission.Work.StemsB.ProjectionO
import Submission.Work.StemsB.FibrewiseTrivRel
import Submission.Work.StemsB.SerreExact

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The pentagon of the Serre exact sequence over a sphere

This file assembles the sphere case of the Serre exact sequence in the stable range from the pieces
proved in this directory:

* `Work.StemsB.isIso_relChainsMapOf_sphLoopOuter` — the thickening `C_*(E, p⁻¹∞) → C_*(E, E|_{O})`
  (the outer piece `O = sphLoopOuter b` is based-contractible to `∞`);
* `Work.StemsB.isIso_relChainsMap_excision` — the excision `C_*(E|_{G}, E|_{G∩O}) → C_*(E, E|_{O})`
  for the open cover `(G, O)`, `G = sphLoopBig b`;
* `Work.StemsB.isIso_relMap` — the fibrewise triviality over `G` read on the pair;
* `Work.StemsB.sphProjRelMapO_isIso` — the projection lemma with the outer spelling of the collar;
* `Work.StemsB.ccPh`, a pair homeomorphism `(↥G × PUnit, collar) ≅ (↥G, collar)`;
* `Work.StemsB.isIso_relChainsMap_excision_base` — the excision `C_*(G, G∩O) → C_*(Sᵇ, O)`;
* `Work.StemsB.isIso_relChainsMapOf_self_sphLoopOuter` — the thickening `C_*(Sᵇ,{∞}) → C_*(Sᵇ,O)`.

The main theorem is `Work.StemsB.serreExactSphere_of_fibrewiseTrivial`.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace Work.StemsB

noncomputable section

variable {E : Type} [TopologicalSpace E]

/-- **Cube-based `π₀`-triviality implies path connectedness** (local copy of the bridge; the quotient
`HomotopyGroup (Fin 0) X x₀` is `ZerothHomotopy X`). -/
theorem pathConnectedSpace_of_subsingleton_pi0 {X : Type} [TopologicalSpace X] (x₀ : X)
    (h0 : Subsingleton (HomotopyGroup (Fin 0) X x₀)) : PathConnectedSpace X := by
  haveI := h0
  have hsub : Subsingleton (ZerothHomotopy X) :=
    (HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x₀)).surjective.subsingleton
  exact pathConnectedSpace_iff_zerothHomotopy.mpr ⟨⟨ZerothHomotopy.mk x₀⟩, hsub⟩

/-- `∞` belongs to the outer piece. -/
theorem infty_subset_outer (b : ℕ) : ({OnePoint.infty} : Set (SphModel b)) ⊆ sphLoopOuter b := by
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  rw [hx]
  exact Or.inl rfl

/-! ## The chain maps of the pentagon -/

/-- The thickening `C_*(E, p⁻¹∞) → C_*(E, E|_O)`. -/
def ccAlpha (b : ℕ) (p : C(E, SphModel b)) :
    Work.Cohomology.relChains (TopCat.of E) (p ⁻¹' {OnePoint.infty}) ⟶
      Work.Cohomology.relChains (TopCat.of E) (p ⁻¹' sphLoopOuter b) :=
  Work.Cohomology.relChainsMapOf (TopCat.of E) (TopCat.of E) (p ⁻¹' {OnePoint.infty})
    (p ⁻¹' sphLoopOuter b) (𝟙 (TopCat.of E))
    (preimageIncl p {OnePoint.infty} (sphLoopOuter b) (infty_subset_outer b))
    (preimageIncl_subtypeIncl p {OnePoint.infty} (sphLoopOuter b) (infty_subset_outer b))

/-- The base thickening `C_*(Sᵇ, {∞}) → C_*(Sᵇ, O)`. -/
def ccIB (b : ℕ) :
    Work.Cohomology.relChains (TopCat.of (SphModel b)) ({OnePoint.infty} : Set (SphModel b)) ⟶
      Work.Cohomology.relChains (TopCat.of (SphModel b)) (sphLoopOuter b) :=
  Work.Cohomology.relChainsMapOf (TopCat.of (SphModel b)) (TopCat.of (SphModel b))
    {OnePoint.infty} (sphLoopOuter b) (𝟙 (TopCat.of (SphModel b)))
    (preimageIncl (ContinuousMap.id (SphModel b)) {OnePoint.infty} (sphLoopOuter b)
      (infty_subset_outer b))
    (preimageIncl_subtypeIncl (ContinuousMap.id (SphModel b)) {OnePoint.infty} (sphLoopOuter b)
      (infty_subset_outer b))

/-- The restriction of `p` to the preimage of the outer piece. -/
def ccG1 (b : ℕ) (p : C(E, SphModel b)) :
    TopCat.of ↥(p ⁻¹' sphLoopOuter b) ⟶ TopCat.of ↥(sphLoopOuter b) :=
  TopCat.ofHom ⟨fun x => ⟨p x.1, x.2⟩, by
    exact Continuous.subtype_mk (p.continuous.comp continuous_subtype_val) (fun x => x.2)⟩

theorem ccG1_w (b : ℕ) (p : C(E, SphModel b)) :
    Work.Cohomology.subtypeIncl (TopCat.of E) (p ⁻¹' sphLoopOuter b) ≫ TopCat.ofHom p
      = ccG1 b p ≫ Work.Cohomology.subtypeIncl (TopCat.of (SphModel b)) (sphLoopOuter b) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  rfl

/-- The `p`-induced map `C_*(E, E|_O) → C_*(Sᵇ, O)`. -/
def ccF1 (b : ℕ) (p : C(E, SphModel b)) :
    Work.Cohomology.relChains (TopCat.of E) (p ⁻¹' sphLoopOuter b) ⟶
      Work.Cohomology.relChains (TopCat.of (SphModel b)) (sphLoopOuter b) :=
  Work.Cohomology.relChainsMapOf (TopCat.of E) (TopCat.of (SphModel b)) (p ⁻¹' sphLoopOuter b)
    (sphLoopOuter b) (TopCat.ofHom p) (ccG1 b p) (ccG1_w b p)

/-- The excision on the total space. -/
def ccE2 (b : ℕ) (p : C(E, SphModel b)) :
    Work.Cohomology.relChains (TopCat.of ↥(p ⁻¹' sphLoopBig b))
        (relA p (sphLoopBig b) (sphLoopOuter b)) ⟶
      Work.Cohomology.relChains (TopCat.of E) (p ⁻¹' sphLoopOuter b) :=
  Work.Cohomology.relChainsMap (TopCat.of E) (p ⁻¹' sphLoopBig b) (p ⁻¹' sphLoopOuter b)

/-- The fibrewise triviality over the inner cube, read on the pair. -/
def ccXi (b : ℕ) (p : C(E, SphModel b)) (d₀ : ↥(sphLoopBig b))
    (hT : FibrewiseTrivial p (sphLoopBig b) d₀) :
    Work.Cohomology.relChains (TopCat.of ↥(p ⁻¹' sphLoopBig b))
        (relA p (sphLoopBig b) (sphLoopOuter b)) ⟶
      Work.Cohomology.relChains (TopCat.of (↥(sphLoopBig b) × ↥(p ⁻¹' {d₀.1})))
        (collarProdO b ↥(p ⁻¹' {d₀.1})) :=
  relMap p (sphLoopBig b) d₀ (sphLoopOuter b) hT

/-- The excision on the base. -/
def ccS2 (b : ℕ) :
    Work.Cohomology.relChains (TopCat.of ↥(sphLoopBig b)) (collarInG b) ⟶
      Work.Cohomology.relChains (TopCat.of (SphModel b)) (sphLoopOuter b) :=
  Work.Cohomology.relChainsMap (TopCat.of (SphModel b)) (sphLoopBig b) (sphLoopOuter b)

/-- The projection `↥G × PUnit → ↥G`. -/
def ccProj (b : ℕ) : TopCat.of (↥(sphLoopBig b) × PUnit) ⟶ TopCat.of ↥(sphLoopBig b) :=
  TopCat.ofHom ⟨fun x => x.1, by fun_prop⟩

/-- Its restriction to the collar. -/
def ccProjRel (b : ℕ) :
    TopCat.of ↥(collarProdO b PUnit) ⟶ TopCat.of ↥(collarInG b) :=
  TopCat.ofHom ⟨fun x => ⟨x.1.1, x.2⟩, by
    exact Continuous.subtype_mk (continuous_fst.comp continuous_subtype_val) (fun x => x.2)⟩

theorem ccProj_w (b : ℕ) :
    Work.Cohomology.subtypeIncl (TopCat.of (↥(sphLoopBig b) × PUnit)) (collarProdO b PUnit)
        ≫ ccProj b
      = ccProjRel b ≫ Work.Cohomology.subtypeIncl (TopCat.of ↥(sphLoopBig b)) (collarInG b) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  rfl

/-- The pair map `(↥G × PUnit, collar) → (↥G, collar)` of the projection: a pair homeomorphism. -/
def ccPh (b : ℕ) :
    Work.Cohomology.relChains (TopCat.of (↥(sphLoopBig b) × PUnit)) (collarProdO b PUnit) ⟶
      Work.Cohomology.relChains (TopCat.of ↥(sphLoopBig b)) (collarInG b) :=
  Work.Cohomology.relChainsMapOf (TopCat.of (↥(sphLoopBig b) × PUnit))
    (TopCat.of ↥(sphLoopBig b)) (collarProdO b PUnit) (collarInG b)
    (ccProj b) (ccProjRel b) (ccProj_w b)

/-- The map `↥(p⁻¹G) → ↥G × PUnit` of the `p`-induced pair map. -/
def ccGK' (b : ℕ) (p : C(E, SphModel b)) :
    TopCat.of ↥(p ⁻¹' sphLoopBig b) ⟶ TopCat.of (↥(sphLoopBig b) × PUnit) :=
  TopCat.ofHom ⟨fun x => (⟨p x.1, x.2⟩, ()), by
    exact Continuous.prodMk
      (Continuous.subtype_mk (p.continuous.comp continuous_subtype_val) (fun x => x.2))
      continuous_const⟩

/-- Its restriction to the relative part. -/
def ccGK'Rel (b : ℕ) (p : C(E, SphModel b)) :
    TopCat.of ↥(relA p (sphLoopBig b) (sphLoopOuter b)) ⟶ TopCat.of ↥(collarProdO b PUnit) :=
  TopCat.ofHom ⟨fun x => ⟨(⟨p x.1.1, x.1.2⟩, ()), x.2⟩, by
    exact Continuous.subtype_mk
      (Continuous.prodMk
        (Continuous.subtype_mk
          (p.continuous.comp (continuous_subtype_val.comp continuous_subtype_val))
          (fun x => x.1.2))
        continuous_const)
      (fun x => x.2)⟩

theorem ccGK'_w (b : ℕ) (p : C(E, SphModel b)) :
    Work.Cohomology.subtypeIncl (TopCat.of ↥(p ⁻¹' sphLoopBig b))
        (relA p (sphLoopBig b) (sphLoopOuter b)) ≫ ccGK' b p
      = ccGK'Rel b p
        ≫ Work.Cohomology.subtypeIncl (TopCat.of (↥(sphLoopBig b) × PUnit))
            (collarProdO b PUnit) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  rfl

/-- The `p`-induced map on the pair, read on `↥G × PUnit`. -/
def ccKappa' (b : ℕ) (p : C(E, SphModel b)) :
    Work.Cohomology.relChains (TopCat.of ↥(p ⁻¹' sphLoopBig b))
        (relA p (sphLoopBig b) (sphLoopOuter b)) ⟶
      Work.Cohomology.relChains (TopCat.of (↥(sphLoopBig b) × PUnit))
        (collarProdO b PUnit) :=
  Work.Cohomology.relChainsMapOf (TopCat.of ↥(p ⁻¹' sphLoopBig b))
    (TopCat.of (↥(sphLoopBig b) × PUnit)) (relA p (sphLoopBig b) (sphLoopOuter b))
    (collarProdO b PUnit) (ccGK' b p) (ccGK'Rel b p) (ccGK'_w b p)

/-- The `p`-induced map on the pair, read on `↥G`. -/
def ccKappa (b : ℕ) (p : C(E, SphModel b)) :
    Work.Cohomology.relChains (TopCat.of ↥(p ⁻¹' sphLoopBig b))
        (relA p (sphLoopBig b) (sphLoopOuter b)) ⟶
      Work.Cohomology.relChains (TopCat.of ↥(sphLoopBig b)) (collarInG b) :=
  ccKappa' b p ≫ ccPh b

/-- The section `↥G → ↥G × PUnit`. -/
def ccSec (b : ℕ) : TopCat.of ↥(sphLoopBig b) ⟶ TopCat.of (↥(sphLoopBig b) × PUnit) :=
  TopCat.ofHom ⟨fun x => (x, ()), by fun_prop⟩

/-- Its restriction to the collar. -/
def ccSecRel (b : ℕ) :
    TopCat.of ↥(collarInG b) ⟶ TopCat.of ↥(collarProdO b PUnit) :=
  TopCat.ofHom ⟨fun y => ⟨(y.1, ()), y.2⟩, by
    exact Continuous.subtype_mk
      (Continuous.prodMk continuous_subtype_val continuous_const) (fun y => y.2)⟩

def ccProjSecHomotopy (b : ℕ) :
    TopCat.Homotopy (ccProj b ≫ ccSec b) (𝟙 (TopCat.of (↥(sphLoopBig b) × PUnit))) :=
  topCatHomotopyOf (X := TopCat.of (↥(sphLoopBig b) × PUnit))
    (Y := TopCat.of ↥(sphLoopBig b)) (f := ccProj b) (g := ccSec b)
    ⟨fun z => z.1, continuous_fst⟩ (fun x => rfl)
    (fun x => by
      show x = (ccProj b x, ())
      exact Prod.ext rfl (Subsingleton.elim _ _))

def ccSecProjHomotopy (b : ℕ) :
    TopCat.Homotopy (ccSec b ≫ ccProj b) (𝟙 (TopCat.of ↥(sphLoopBig b))) :=
  topCatHomotopyOf (X := TopCat.of ↥(sphLoopBig b)) (Y := TopCat.of (↥(sphLoopBig b) × PUnit))
    (f := ccSec b) (g := ccProj b) ⟨fun z => z.1, continuous_fst⟩ (fun x => rfl)
    (fun x => by show x = ccProj b (ccSec b x); rfl)

def ccProjRelSecRelHomotopy (b : ℕ) :
    TopCat.Homotopy (ccProjRel b ≫ ccSecRel b) (𝟙 (TopCat.of ↥(collarProdO b PUnit))) :=
  topCatHomotopyOf (X := TopCat.of ↥(collarProdO b PUnit))
    (Y := TopCat.of ↥(collarInG b)) (f := ccProjRel b) (g := ccSecRel b)
    ⟨fun z => z.1, continuous_fst⟩ (fun x => rfl)
    (fun x => by
      show x = ccSecRel b (ccProjRel b x)
      exact Subtype.ext (Prod.ext rfl (Subsingleton.elim _ _)))

def ccSecRelProjRelHomotopy (b : ℕ) :
    TopCat.Homotopy (ccSecRel b ≫ ccProjRel b) (𝟙 (TopCat.of ↥(collarInG b))) :=
  topCatHomotopyOf (X := TopCat.of ↥(collarInG b)) (Y := TopCat.of ↥(collarProdO b PUnit))
    (f := ccSecRel b) (g := ccProjRel b) ⟨fun z => z.1, continuous_fst⟩ (fun x => rfl)
    (fun x => by show x = ccProjRel b (ccSecRel b x); rfl)

/-- The total-space map of the pair homeomorphism is a quasi-isomorphism. -/
theorem isIso_ccProjChain (b : ℕ) (j : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of (↥(sphLoopBig b) × PUnit)) (TopCat.of ↥(sphLoopBig b)) (ccProj b)) j) :=
  Work.Cohomology.homologyEquiv ℤ (TopCat.of (↥(sphLoopBig b) × PUnit))
    (TopCat.of ↥(sphLoopBig b)) (ccProj b) (ccSec b) (ccProjSecHomotopy b)
    (ccSecProjHomotopy b) j

/-- The relative-part map of the pair homeomorphism is a quasi-isomorphism. -/
theorem isIso_ccProjRelChain (b : ℕ) (j : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of ↥(collarProdO b PUnit)) (TopCat.of ↥(collarInG b)) (ccProjRel b)) j) :=
  Work.Cohomology.homologyEquiv ℤ (TopCat.of ↥(collarProdO b PUnit))
    (TopCat.of ↥(collarInG b)) (ccProjRel b) (ccSecRel b) (ccProjRelSecRelHomotopy b)
    (ccSecRelProjRelHomotopy b) j

/-- **The pair homeomorphism `(↥G × PUnit, collar) → (↥G, collar)` is a quasi-isomorphism.** -/
theorem isIso_ccPh (b : ℕ) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (ccPh b) k) := by
  rw [ccPh]
  exact Work.Cohomology.relChainsMapOf_homologyMap_isIso
    (X := TopCat.of (↥(sphLoopBig b) × PUnit)) (Y := TopCat.of ↥(sphLoopBig b))
    (collarProdO b PUnit) (collarInG b) (ccProj b) (ccProjRel b) (ccProj_w b) k
    (fun j => isIso_ccProjChain b j) (fun j => isIso_ccProjRelChain b j)

/-! ## The quasi-isomorphisms of the five maps -/

theorem isIso_ccAlpha (b : ℕ) (p : C(E, SphModel b)) (hp : IsHurewiczFibration p) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (ccAlpha b p) k) :=
  isIso_relChainsMapOf_sphLoopOuter b p hp (infty_subset_outer b) k

theorem isIso_ccIB (b : ℕ) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (ccIB b) k) :=
  isIso_relChainsMapOf_self_sphLoopOuter b (infty_subset_outer b) k

theorem isIso_ccE2 (b : ℕ) (p : C(E, SphModel b)) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (ccE2 b p) k) :=
  isIso_relChainsMap_excision b p k

theorem isIso_ccS2 (b : ℕ) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (ccS2 b) k) :=
  isIso_relChainsMap_excision_base b k

theorem isIso_ccXi (b : ℕ) (p : C(E, SphModel b)) (d₀ : ↥(sphLoopBig b))
    (hT : FibrewiseTrivial p (sphLoopBig b) d₀) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (ccXi b p d₀ hT) k) :=
  isIso_relMap p (sphLoopBig b) d₀ (sphLoopOuter b) hT k

/-! ## The commuting squares of the pentagon -/

/-- The first square: `i_a ≫ f₁ = f ≫ i_b` on relative chains. -/
theorem sqAlpha (b : ℕ) (p : C(E, SphModel b)) :
    relPairMap p OnePoint.infty ≫ ccIB b = ccAlpha b p ≫ ccF1 b p := by
  rw [relPairMap, ccAlpha, ccIB, ccF1]
  rw [Work.Cohomology.relChainsMapOf_comp]
  rw [Work.Cohomology.relChainsMapOf_comp]
  rw [relChainsMapOf_congr (A := p ⁻¹' {OnePoint.infty}) (B := sphLoopOuter b)
    (f := TopCat.ofHom p ≫ 𝟙 (TopCat.of (SphModel b)))
    (f' := 𝟙 (TopCat.of E) ≫ TopCat.ofHom p)
    (g := fibreMap p OnePoint.infty ≫ preimageIncl (ContinuousMap.id (SphModel b)) {OnePoint.infty}
      (sphLoopOuter b) (infty_subset_outer b))
    (g' := preimageIncl p {OnePoint.infty} (sphLoopOuter b) (infty_subset_outer b) ≫ ccG1 b p)
    (by rw [Category.comp_id, Category.id_comp])
    (by
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro x
      apply Subtype.ext
      exact x.2.symm)]
  all_goals
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    simp only [CategoryTheory.comp_apply, CategoryTheory.id_apply, TopCat.hom_ofHom,
      Work.Cohomology.subtypeIncl, preimageIncl, ccG1, fibreMap] at ⊢
    first
      | rfl
      | exact Set.mem_singleton_iff.mp x.2

/-- The third square: the triviality over the inner cube followed by the projection is the
`p`-induced map on the pair. -/
theorem sqXi (b : ℕ) (p : C(E, SphModel b)) (d₀ : ↥(sphLoopBig b))
    (hT : FibrewiseTrivial p (sphLoopBig b) d₀) :
    ccXi b p d₀ hT ≫ sphProjRelMapO b ↥(p ⁻¹' {d₀.1}) = ccKappa' b p := by
  rw [ccXi, relMap, sphProjRelMapO, ccKappa']
  rw [Work.Cohomology.relChainsMapOf_comp]
  rw [relChainsMapOf_congr (A := relA p (sphLoopBig b) (sphLoopOuter b))
    (B := collarProdO b PUnit)
    (f := TopCat.ofHom (fibTrivΦ p (sphLoopBig b) d₀ hT) ≫ sphProjHom b ↥(p ⁻¹' {d₀.1}))
    (f' := ccGK' b p)
    (g := relΦA p (sphLoopBig b) d₀ (sphLoopOuter b) hT
      ≫ sphProjRelHomO b ↥(p ⁻¹' {d₀.1}))
    (g' := ccGK'Rel b p)
    (by
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro x
      apply Prod.ext
      · exact fibTrivΦ_fst p (sphLoopBig b) d₀ hT x
      · exact Subsingleton.elim _ _)
    (by
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro x
      simp only [CategoryTheory.comp_apply, CategoryTheory.id_apply, TopCat.hom_ofHom,
        Work.Cohomology.subtypeIncl, sphProjRelHomO, sphProjHom, relΦA, ccGK'Rel, ccGK'] at ⊢
      apply Subtype.ext
      apply Prod.ext
      · exact fibTrivΦ_fst p (sphLoopBig b) d₀ hT x.1
      · exact Subsingleton.elim _ _)]
  all_goals
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    rfl


/-- The second square of the pentagon: the excision on the total space, the `p`-induced map on the
pair and the two excisions on the base form a commuting square. -/
theorem sq2 (b : ℕ) (p : C(E, SphModel b)) :
    ccE2 b p ≫ ccF1 b p = ccKappa b p ≫ ccS2 b := by
  rw [ccE2, ccF1, ccKappa, ccKappa', ccPh, ccS2, Work.Cohomology.relChainsMap,
    Work.Cohomology.relChainsMap]
  rw [Category.assoc]
  rw [Work.Cohomology.relChainsMapOf_comp]
  rw [Work.Cohomology.relChainsMapOf_comp]
  rw [Work.Cohomology.relChainsMapOf_comp]
  rw [relChainsMapOf_congr (A := relA p (sphLoopBig b) (sphLoopOuter b)) (B := sphLoopOuter b)
    (f := Work.Cohomology.subtypeIncl (TopCat.of E) (p ⁻¹' sphLoopBig b) ≫ TopCat.ofHom p)
    (f' := ccGK' b p ≫ (ccProj b ≫ Work.Cohomology.subtypeIncl (TopCat.of (SphModel b)) (sphLoopBig b)))
    (g := Work.Cohomology.inclInterA (TopCat.of E) (p ⁻¹' sphLoopBig b) (p ⁻¹' sphLoopOuter b) ≫ ccG1 b p)
    (g' := ccGK'Rel b p ≫ (ccProjRel b ≫ Work.Cohomology.inclInterA (TopCat.of (SphModel b)) (sphLoopBig b) (sphLoopOuter b)))
    (by
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro x
      simp only [CategoryTheory.comp_apply, CategoryTheory.id_apply, TopCat.hom_ofHom,
        Work.Cohomology.subtypeIncl, ccGK', ccProj]
      rfl)
    (by
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro x
      apply Subtype.ext
      simp only [CategoryTheory.comp_apply, CategoryTheory.id_apply, TopCat.hom_ofHom,
        Work.Cohomology.inclInterA, ccGK'Rel, ccProjRel, ccG1]
      rfl)]
  all_goals
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    first
      | (simp only [CategoryTheory.comp_apply, CategoryTheory.id_apply, TopCat.hom_ofHom,
          Work.Cohomology.subtypeIncl, Work.Cohomology.inclInterA, ccG1, ccGK', ccGK'Rel, ccProj,
          ccProjRel, fibreMap]
         rfl)
      | (apply Subtype.ext
         simp only [CategoryTheory.comp_apply, CategoryTheory.id_apply, TopCat.hom_ofHom,
          Work.Cohomology.subtypeIncl, Work.Cohomology.inclInterA, ccG1, ccGK', ccGK'Rel, ccProj,
          ccProjRel, fibreMap]
         rfl)


/-- **The relative form of the sphere case**: the `p`-induced map on the pair `(E, E|_O) → (Sᵇ, O)`
(`O = sphLoopOuter b`) is a quasi-isomorphism in the stable range.  This is the middle column of the
pentagon, and the shape in which the sphere case is used as the input for the cell-attachment step
of the general base. -/
theorem isIso_ccF1 (b : ℕ) (hb : 1 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (hp : IsHurewiczFibration p) (d₀ : ↥(sphLoopBig b)) (f : ℕ)
    (hT : FibrewiseTrivial p (sphLoopBig b) d₀) (y₀ : ↥(p ⁻¹' {d₀.1}))
    (hH0 : Nonempty (((Work.Cohomology.singularChains ℤ
      (TopCat.of ↥(p ⁻¹' {d₀.1}))).homology 0) ≃ₗ[ℤ] ℤ))
    (hH : ∀ j : ℕ, 0 < j → j < f →
      IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(p ⁻¹' {d₀.1}))).homology j))
    (i : ℕ) (hi : i < b + f) :
    IsIso (HomologicalComplex.homologyMap (ccF1 b p) i) := by
  haveI hXi : IsIso (HomologicalComplex.homologyMap (ccXi b p d₀ hT) i) := isIso_ccXi b p d₀ hT i
  haveI hZO : IsIso (HomologicalComplex.homologyMap (sphProjRelMapO b ↥(p ⁻¹' {d₀.1})) i) :=
    sphProjRelMapO_isIso b hb ↥(p ⁻¹' {d₀.1}) f ⟨y₀⟩ hH hH0 i hi
  haveI hKp : IsIso (HomologicalComplex.homologyMap (ccKappa' b p) i) := by
    rw [← sqXi b p d₀ hT, HomologicalComplex.homologyMap_comp]
    exact IsIso.comp_isIso
  haveI hPh : IsIso (HomologicalComplex.homologyMap (ccPh b) i) := isIso_ccPh b i
  haveI hK : IsIso (HomologicalComplex.homologyMap (ccKappa b p) i) := by
    rw [ccKappa, HomologicalComplex.homologyMap_comp]
    exact IsIso.comp_isIso
  haveI hS2 : IsIso (HomologicalComplex.homologyMap (ccS2 b) i) := isIso_ccS2 b i
  haveI hE2 : IsIso (HomologicalComplex.homologyMap (ccE2 b p) i) := isIso_ccE2 b p i
  haveI hc : IsIso (HomologicalComplex.homologyMap (ccE2 b p ≫ ccF1 b p) i) := by
    rw [sq2 b p, HomologicalComplex.homologyMap_comp]
    exact IsIso.comp_isIso
  exact IsIso.of_isIso_fac_left
    (HomologicalComplex.homologyMap_comp (ccE2 b p) (ccF1 b p) i).symm

/-! ## The sphere case of the Serre exact sequence in the stable range -/

/-- **The Serre exact sequence over a sphere, in the stable range, in homological form** — the form
in which `H₀` of the fibre over `d₀` is an explicit hypothesis. -/
theorem serreExactSphere_of_fibrewiseTrivial_hH0 (b : ℕ) (hb : 1 ≤ b) (E : Type)
    [TopologicalSpace E] (p : C(E, SphModel b)) (hp : IsHurewiczFibration p)
    (d₀ : ↥(sphLoopBig b)) (f : ℕ) (hT : FibrewiseTrivial p (sphLoopBig b) d₀)
    (y₀ : ↥(p ⁻¹' {d₀.1}))
    (hH0 : Nonempty (((Work.Cohomology.singularChains ℤ
      (TopCat.of ↥(p ⁻¹' {d₀.1}))).homology 0) ≃ₗ[ℤ] ℤ))
    (hH : ∀ j : ℕ, 0 < j → j < f →
      IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(p ⁻¹' {d₀.1}))).homology j))
    (i : ℕ) (hi : i < b + f) :
    IsIso (HomologicalComplex.homologyMap (relPairMap p OnePoint.infty) i) := by
  haveI hF1 : IsIso (HomologicalComplex.homologyMap (ccF1 b p) i) :=
    isIso_ccF1 b hb E p hp d₀ f hT y₀ hH0 hH i hi
  haveI hAlpha : IsIso (HomologicalComplex.homologyMap (ccAlpha b p) i) := isIso_ccAlpha b p hp i
  haveI hIB : IsIso (HomologicalComplex.homologyMap (ccIB b) i) := isIso_ccIB b i
  haveI hcomp : IsIso (HomologicalComplex.homologyMap (relPairMap p OnePoint.infty ≫ ccIB b) i) := by
    rw [sqAlpha b p, HomologicalComplex.homologyMap_comp]
    exact IsIso.comp_isIso
  exact IsIso.of_isIso_fac_right
    (HomologicalComplex.homologyMap_comp (relPairMap p OnePoint.infty) (ccIB b) i).symm

/-- **The Serre exact sequence over a sphere, in the stable range, in homological form.**

Let `p : E → Sᵇ` be a Hurewicz fibration which is fibrewise trivial over the inner cube
`sphLoopBig b` with fibre `p⁻¹(d₀)` for some `d₀` in the cube (`hT`), let that fibre be path
connected (`hconn`) and have vanishing reduced homology below degree `f` (`hH`).  Then the
`p`-induced map of pairs `(E, p⁻¹∞) → (Sᵇ, {∞})` is an isomorphism on relative integral homology in
every degree `i < b + f`.

The fibrewise triviality of the fibration over the contractible piece is an explicit hypothesis (for
a general Hurewicz fibration this is the theorem of Dold–Strøm; for the path–loop fibration
`Work.StemsB.evalOne X x₀` — the case that the rational Hurewicz theorem needs — it is available
explicitly, see `PathSpaceTrivial.lean`, `cubePullback_homotopyEquiv.lean`,
`BundlePullbackHomology.lean`). -/
theorem serreExactSphere_of_fibrewiseTrivial (b : ℕ) (hb : 1 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (hp : IsHurewiczFibration p) (d₀ : ↥(sphLoopBig b)) (f : ℕ)
    (hT : FibrewiseTrivial p (sphLoopBig b) d₀) (y₀ : ↥(p ⁻¹' {d₀.1}))
    (hconn : Subsingleton (HomotopyGroup (Fin 0) (↥(p ⁻¹' {d₀.1})) y₀))
    (hH : ∀ j : ℕ, 0 < j → j < f →
      IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(p ⁻¹' {d₀.1}))).homology j))
    (i : ℕ) (hi : i < b + f) :
    IsIso (HomologicalComplex.homologyMap (relPairMap p OnePoint.infty) i) := by
  haveI hPC : PathConnectedSpace ↥(p ⁻¹' {d₀.1}) :=
    pathConnectedSpace_of_subsingleton_pi0 y₀ hconn
  have hH0 : Nonempty (((Work.Cohomology.singularChains ℤ
      (TopCat.of ↥(p ⁻¹' {d₀.1}))).homology 0) ≃ₗ[ℤ] ℤ) := by
    haveI hε : IsIso (TopCat.singularHomology₀ε (TopCat.of ↥(p ⁻¹' {d₀.1}))
        (ModuleCat.of ℤ ℤ)) := inferInstance
    exact ⟨Work.Cohomology.uctIsoToLinearEquiv
      (asIso (TopCat.singularHomology₀ε (TopCat.of ↥(p ⁻¹' {d₀.1})) (ModuleCat.of ℤ ℤ)))⟩
  exact serreExactSphere_of_fibrewiseTrivial_hH0 b hb E p hp d₀ f hT y₀ hH0 hH i hi

end

end Work.StemsB
