/-
# `BridgeSquare/Explicit.lean` — the choices made explicit

The delivered areas state their homology identifications as `Nonempty (X ≅ Y)` and consume them
with the `.some` of the `Nonempty` (i.e. `Classical.choice`).  Such a term is **opaque**: Lean has
no reduction for `Classical.choice`, and it is not determined by the surrounding data — see
`Submission/Work/BridgeSquare/NOTES.md` §2.  Every downstream statement that has to *evaluate* such
an isomorphism (in particular the bridge square
`(D.eAB k).hom ≫ mvFhat k = wConcrete k ≫ (D.eN k).hom`, whose two sides are built from the
identifications of the piece data) is therefore unprovable.

This file supplies **choice-free** versions of the identifications used by the Mayer–Vietoris
computation.  Each one is the *same* isomorphism that the delivered proof built, but exposed as an
`Iso` rather than as the `.some` of a `Nonempty`; the proofs are the proof bodies of the delivered
results with the `Nonempty` wrapper removed.

* `Work.BridgeSquare.biprodHomology` — `H_n(K ⊞ L) ≅ H_n(K) ⊞ H_n(L)`
  (explicit version of `Work.Homology.HomologyBiprod`);
* `Work.BridgeSquare.finiteBiprodHomology` — `H_n(⨁_i K_i) ≅ ⨁_i H_n(K_i)`
  (explicit version of `Work.Homology.FiniteBiprodHomology`);
* `Work.BridgeSquare.sigmaOpenCoverChain` — the splitting of the singular chains of a finite
  disjoint open cover (explicit version of `Work.HomologyIso.sigmaOpenCoverChainIso`);
* `Work.BridgeSquare.intHomologySigma` — `H_k(⊔_i X_i) ≅ ⨁_i H_k(X_i)`
  (explicit version of `Work.HomologyIso.intHomology_sigma`);
* `Work.BridgeSquare.intHomologyIsoOfQuasiIso` and `...OfHomotopyEquiv` — the transport of a
  homology computation along a quasi-isomorphism / homotopy equivalence (explicit versions of
  `Work.HomologyMV.intHomology_iso_of_quasiIso` and
  `Work.HomologyIso.intHomology_iso_of_homotopyEquiv`).

## What is *not* yet choice-free (see `NOTES.md` §4)

The chain through the generated cell-complex data — `Work.Certificates.SDR.sound` →
`Work.HomologyIso.Gen.mbarCx_homology_modelA` → `Work.MbarHomology.eA`, and
`Work.PieceHomology.eT2_concrete`/`eTorus_concrete` — still passes through `.some`s
(`Work.Certificates.SDR.section_chainMap`, `retract_chainMap`, `homotopy_exists`,
`FinChainCx.zeroDiff_homology` are `∃`-valued).  Those identifications must be re-run in the same
way before the piece data of the final wiring can be evaluated on generators; the *interface* for
doing so is in place here, and the reduction in `Compatible.lean`/`Residual.lean` is stated for
whatever choice-free `PieceData` the provider supplies.
-/
import Submission.Work.HomologyIso.intHomology_sigma
import Submission.Work.HomologyMV.Interface
import Submission.Work.HomologyMV.Model
import Submission.Work.Cohomology.localHomology

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open LeanEval.Topology
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Topology

namespace Work.BridgeSquare

open Work.Homology

noncomputable section

/-- Chain complexes of `ℤ`-modules have finite biproducts (the instance used by the delivered
proofs of additivity). -/
local instance instChainComplexFiniteBiproducts :
    HasFiniteBiproducts (ChainComplex (ModuleCat ℤ) ℕ) :=
  Abelian.hasFiniteBiproducts (C := ChainComplex (ModuleCat ℤ) ℕ)

/-! ## §1  Binary additivity of homology, explicitly -/

/-- **Choice-free binary additivity of homology**: `H_n(K ⊞ L) ≅ H_n(K) ⊞ H_n(L)`, built from the
maps induced by `biprod.inl`, `biprod.inr`, `biprod.fst`, `biprod.snd`.  This is the iso inside
`Work.Homology.HomologyBiprod`, exposed. -/
def biprodHomology (K L : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    (K ⊞ L).homology n ≅ K.homology n ⊞ L.homology n := by
  let a : (K ⊞ L).homology n ⟶ K.homology n := homologyMap (biprod.fst : K ⊞ L ⟶ K) n
  let b : (K ⊞ L).homology n ⟶ L.homology n := homologyMap (biprod.snd : K ⊞ L ⟶ L) n
  let c : K.homology n ⟶ (K ⊞ L).homology n := homologyMap (biprod.inl : K ⟶ K ⊞ L) n
  let d : L.homology n ⟶ (K ⊞ L).homology n := homologyMap (biprod.inr : L ⟶ K ⊞ L) n
  have hca : c ≫ a = 𝟙 (K.homology n) := by
    simp only [c, a, ← homologyMap_comp, biprod.inl_fst, homologyMap_id]
  have hdb : d ≫ b = 𝟙 (L.homology n) := by
    simp only [d, b, ← homologyMap_comp, biprod.inr_snd, homologyMap_id]
  have hcb : c ≫ b = 0 := by
    simp only [c, b, ← homologyMap_comp, biprod.inl_snd, homologyMap_zero]
  have hda : d ≫ a = 0 := by
    simp only [d, a, ← homologyMap_comp, biprod.inr_fst, homologyMap_zero]
  have hac : a ≫ c + b ≫ d = 𝟙 ((K ⊞ L).homology n) := by
    simp only [a, c, b, d, ← homologyMap_comp, ← homologyMap_add, biprod.total, homologyMap_id]
  exact { hom := biprod.lift a b
          inv := biprod.desc c d
          hom_inv_id := by rw [biprod.lift_desc]; exact hac
          inv_hom_id := biprod_desc_lift hca hda hcb hdb }

/-! ## §2  Finite additivity of homology, explicitly -/

/-- **Choice-free additivity of homology over a finite biproduct**:
`H_n(⨁_i K_i) ≅ ⨁_i H_n(K_i)`, built from the maps induced by the `biproduct.ι` and
`biproduct.π`. -/
def finiteBiprodHomology {ι : Type*} [Fintype ι]
    (K : ι → ChainComplex (ModuleCat ℤ) ℕ) [HasBiproduct K] (n : ℕ) :
    (biproduct K).homology n ≅ biproduct (fun i => (K i).homology n) := by
  classical
  let Z := (biproduct K).homology n
  let H : ι → ModuleCat ℤ := fun i => (K i).homology n
  let a : ∀ i, Z ⟶ H i := fun i => homologyMap (biproduct.π K i) n
  let c : ∀ i, H i ⟶ Z := fun i => homologyMap (biproduct.ι K i) n
  have hdelta : ∀ k j, c k ≫ a j = biproduct.ι H k ≫ biproduct.π H j := by
    intro k j
    simp only [a, c, ← homologyMap_comp]
    by_cases h : k = j
    · subst h
      rw [biproduct.ι_π_self K k, biproduct.ι_π_self H k, homologyMap_id]
    · rw [biproduct.ι_π_ne K h, homologyMap_zero, biproduct.ι_π_ne H h]
  have hck : ∀ k, c k ≫ biproduct.lift a = biproduct.ι H k := by
    intro k
    apply biproduct.hom_ext
    intro j
    rw [Category.assoc, biproduct.lift_π]
    exact hdelta k j
  have key : biproduct.lift a ≫ biproduct.desc c = 𝟙 Z := by
    rw [Work.Homology.biproduct_lift_desc' (f := H) a c]
    calc ∑ i, a i ≫ c i
        = ∑ i, homologyMap (biproduct.π K i ≫ biproduct.ι K i) n := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [a, c, ← homologyMap_comp]
      _ = homologyMap (∑ i, (biproduct.π K i ≫ biproduct.ι K i)) n :=
          (Work.Homology.homologyMap_sum n Finset.univ _).symm
      _ = homologyMap (𝟙 (biproduct K)) n := by rw [biproduct_total']
      _ = 𝟙 Z := by rw [homologyMap_id]
  have hdesc : biproduct.desc c ≫ biproduct.lift a = 𝟙 (biproduct H) := by
    apply biproduct.hom_ext'
    intro k
    rw [← Category.assoc, biproduct.ι_desc, Category.comp_id]
    exact hck k
  exact { hom := biproduct.lift a, inv := biproduct.desc c, hom_inv_id := key, inv_hom_id := hdesc }

/-! ## §3  The chains of a finite disjoint open cover, explicitly -/

/-- **Choice-free splitting of the singular chains of a finite disjoint open cover**: for a finite
family `V i` of pairwise disjoint open sets covering `X`, the sum of the inclusions is a chain
isomorphism `⨁_i C_*(V i) ≅ C_*(X)`.  This is the iso inside
`Work.HomologyIso.sigmaOpenCoverChainIso`. -/
def sigmaOpenCoverChain {ι : Type} [Fintype ι] (X : TopCat) (V : ι → Set X)
    (hopen : ∀ i, IsOpen (V i)) (hdisj : ∀ i j, i ≠ j → Disjoint (V i) (V j))
    (hcov : ∀ x : X, ∃ i, x ∈ V i) (R : ModuleCat ℤ)
    [HasBiproduct (fun i => Work.Homology.singChain R (TopCat.of (V i)))] :
    biproduct (fun i => Work.Homology.singChain R (TopCat.of (V i))) ≅
      Work.Homology.singChain R X := by
  haveI := Work.HomologyIso.sigmaOpenCoverChainSplit X V hopen hdisj hcov R
  exact asIso (biproduct.desc fun i => Work.Homology.singChainMap R (incl (V i)))

/-! ## §4  Additivity of integral homology over a finite disjoint union, explicitly -/

open Work.HomologyIso in
/-- **Choice-free additivity of integral homology over a finite disjoint union**:
`H_k(⊔_i X_i) ≅ ⨁_i H_k(X_i)`.  This is the iso inside
`Work.HomologyIso.intHomology_sigma`. -/
def intHomologySigma {ι : Type} [Fintype ι] (k : ℕ) (X : ι → Type)
    [∀ i, TopologicalSpace (X i)] :
    LeanEval.Topology.intHomology k (TopCat.of (Σ i, X i)) ≅
      CategoryTheory.Limits.biproduct
        (fun i => LeanEval.Topology.intHomology k (TopCat.of (X i))) := by
  classical
  have eCover := sigmaOpenCoverChain (X := TopCat.of (Σ i, X i))
    (V := fun i => Work.HomologyIso.sigmaPiece X i) (Work.HomologyIso.isOpen_sigmaPiece X)
    (fun _ _ hij => Work.HomologyIso.disjoint_sigmaPiece X hij)
    (Work.HomologyIso.exists_mem_sigmaPiece X) Work.Homology.ZMod
  have eChain : Work.Homology.singChain Work.Homology.ZMod (TopCat.of (Σ i, X i)) ≅
      CategoryTheory.Limits.biproduct
        (fun i => Work.Homology.singChain Work.Homology.ZMod (TopCat.of (X i))) :=
    eCover.symm ≪≫
      (biproduct.mapIso
        (fun i => Work.HomologyIso.chainHomeomorphIso Work.Homology.ZMod
          (Work.HomologyIso.sigmaPieceHomeomorph X i))).symm
  have hBip := finiteBiprodHomology
    (fun i => Work.Homology.singChain Work.Homology.ZMod (TopCat.of (X i))) k
  exact (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) k).mapIso eChain
    ≪≫ hBip

/-! ## §5  Transport of a homology computation along a quasi-isomorphism / homotopy equivalence -/

/-- **Choice-free transport of a homology computation along a quasi-isomorphism**: the iso inside
`Work.HomologyMV.intHomology_iso_of_quasiIso`. -/
def intHomologyIsoOfQuasiIso {C : ChainComplex (ModuleCat ℤ) ℕ} (X : TopCat)
    (φ : C ⟶ Work.HomologyMV.singCx X) (hφ : QuasiIso φ) {k n : ℕ}
    (e : C.homology k ≅ Work.HomologyMV.freeMod n) :
    LeanEval.Topology.intHomology k X ≅ Work.HomologyMV.freeMod n :=
  (asIso (HomologicalComplex.homologyMap φ k)).symm ≪≫ e

/-- **Choice-free transport of a homology computation along a homotopy equivalence**: the iso inside
`Work.HomologyIso.intHomology_iso_of_homotopyEquiv`.  It is the map induced by the *forward* map of
the homotopy equivalence, so it is determined by the homotopy equivalence itself. -/
def intHomologyIsoOfHomotopyEquiv {X Y : TopCat} (e : ContinuousMap.HomotopyEquiv ↥X ↥Y)
    (k : ℕ) :
    LeanEval.Topology.intHomology k X ≅ LeanEval.Topology.intHomology k Y :=
  @asIso (ModuleCat ℤ) _ (LeanEval.Topology.intHomology k X) (LeanEval.Topology.intHomology k Y)
    (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ X Y (TopCat.ofHom e.toFun)) k)
    (Work.Cohomology.isIso_homologyMap_chainMap_of_homotopyEquiv e k)


/-! ## §6  The composite of two homotopy-equivalence-induced isos -/

/-- The composite of the homology isomorphisms induced by two composable homotopy equivalences —
the term that `Work.BridgeSquare.intHomologyIsoOfHomotopyEquiv_trans` identifies with the one of the
composite homotopy equivalence. -/
def intHomologyIsoOfHomotopyEquivComp {X Y Z : TopCat}
    (e : ContinuousMap.HomotopyEquiv ↥X ↥Y) (f : ContinuousMap.HomotopyEquiv ↥Y ↥Z) (k : ℕ) :
    LeanEval.Topology.intHomology k X ≅ LeanEval.Topology.intHomology k Z :=
  intHomologyIsoOfHomotopyEquiv e k ≪≫ intHomologyIsoOfHomotopyEquiv f k
end

end Work.BridgeSquare
