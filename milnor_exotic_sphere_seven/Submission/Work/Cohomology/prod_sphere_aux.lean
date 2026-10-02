import Mathlib
import Submission.Work.Cohomology.Singular
import Submission.Work.Cohomology.MVCohomology
import Submission.Work.Cohomology.sphereCohomologyTop
import Submission.Work.Cohomology.sphereCohomologyZero
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.sphereVanishing
import Submission.Work.Cohomology.sphere_compl_singleton_contractible
import Submission.Work.Cohomology.contractible
import Submission.Work.Cohomology.homotopyEquiv
import Submission.Work.Cohomology.Pullback
import Submission.Work.Cohomology.SmallChains
import Submission.Work.Cohomology.smallChainsHomotopyEquiv
import Submission.Work.Cohomology.singularCohomology_zero
import Submission.Work.Morse.TwoBallsBasic
import Submission.Work.Cohomology.homology_biprod_iso
import Submission.Work.Cohomology.iso_of_section_ker
import Submission.Work.Cohomology.isZero_dualComplex_empty
import Submission.Work.Cohomology.sphereCohomologyOne

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory AlgebraicTopology Limits
open scoped Topology ZeroObject

namespace Work.Cohomology
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-- `S^p` as a type. -/
-- Renamed from `Yt` (Islands subproject, 2026): the name `Work.Cohomology.Yt` was also used for
-- the *pair* `Yt p q = TopCat.of ↥(Yset p q)` in `Cohomology/proj_pair_injective.lean` (now
-- `YtPair`), so the two could not be imported into one file.  Statement unchanged.

abbrev YtSph (p : ℕ) : Type := ↥(sphSet (p + 1))
/-- The product `S^p × S^N` as a type. -/
abbrev XYt (p N : ℕ) : Type := ↥(sphSet (p + 1)) × ↥(sphSet (N + 1))
/-- The product `S^p × S^N` as a space. -/
abbrev XN (p N : ℕ) : TopCat := TopCat.of (XYt p N)
/-- The product `S^p × S^(N+1)` as a space (the total space of the cap cover). -/
abbrev Xs (p N : ℕ) : TopCat := TopCat.of (XYt p (N+1))

/-- The "upper" cap of the second factor inside `S^p × S^(N+1)`. -/
def capU (p N : ℕ) : Set ↥(Xs p N) := {x | x.2 ∈ capA (N+1)}
/-- The "lower" cap of the second factor. -/
def capV (p N : ℕ) : Set ↥(Xs p N) := {x | x.2 ∈ capB (N+1)}

lemma isOpen_capU (p N : ℕ) : IsOpen (capU p N) :=
  (isOpen_capA (N+1)).preimage continuous_snd

lemma isOpen_capV (p N : ℕ) : IsOpen (capV p N) :=
  (isOpen_capB (N+1)).preimage continuous_snd

lemma capU_union_capV (p N : ℕ) : capU p N ∪ capV p N = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  rintro ⟨y, s⟩
  rcases (show s ∈ capA (N+1) ∪ capB (N+1) by rw [capA_union_capB]; trivial) with h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1

def projU (p N : ℕ) : TopCat.of ↥(capU p N) ⟶ TopCat.of (YtSph p) :=
  TopCat.ofHom ⟨fun x => x.1.1, continuous_fst.comp continuous_subtype_val⟩
def projV (p N : ℕ) : TopCat.of ↥(capV p N) ⟶ TopCat.of (YtSph p) :=
  TopCat.ofHom ⟨fun x => x.1.1, continuous_fst.comp continuous_subtype_val⟩
def projW (p N : ℕ) : TopCat.of ↥(capU p N ∩ capV p N) ⟶ TopCat.of (YtSph p) :=
  TopCat.ofHom ⟨fun x => x.1.1, continuous_fst.comp continuous_subtype_val⟩
def projY (p N : ℕ) : XN p N ⟶ TopCat.of (YtSph p) :=
  TopCat.ofHom ⟨Prod.fst, continuous_fst⟩

def capUHomeo (p N : ℕ) : ↥(capU p N) ≃ₜ YtSph p × ↥(capA (N+1)) :=
  (Homeomorph.setCongr (by
    ext x
    exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩)).trans
  ((Homeomorph.Set.prod Set.univ (capA (N+1))).trans
    ((Homeomorph.Set.univ (YtSph p)).prodCongr (Homeomorph.refl _)))
def capVHomeo (p N : ℕ) : ↥(capV p N) ≃ₜ YtSph p × ↥(capB (N+1)) :=
  (Homeomorph.setCongr (by
    ext x
    exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩)).trans
  ((Homeomorph.Set.prod Set.univ (capB (N+1))).trans
    ((Homeomorph.Set.univ (YtSph p)).prodCongr (Homeomorph.refl _)))
def bandUHomeo (p N : ℕ) : ↥(capU p N ∩ capV p N) ≃ₜ YtSph p × ↥(band (N+1)) :=
  (Homeomorph.setCongr (by
    ext x
    simp [capU, capV, band, Set.mem_prod])).trans
  ((Homeomorph.Set.prod Set.univ (band (N+1))).trans
    ((Homeomorph.Set.univ (YtSph p)).prodCongr (Homeomorph.refl _)))

noncomputable def capUEquiv (p N : ℕ) : ContinuousMap.HomotopyEquiv ↥(capU p N) (YtSph p) :=
  letI : ContractibleSpace ↥(capA (N+1)) := contractibleSpace_capA (N+1)
  let e := Classical.choice (ContractibleSpace.hequiv ↥(capA (N+1)) PUnit)
  (capUHomeo p N).toHomotopyEquiv.trans
    ((ContinuousMap.HomotopyEquiv.prodCongr (ContinuousMap.HomotopyEquiv.refl (YtSph p)) e).trans
      (Homeomorph.prodPUnit (YtSph p)).toHomotopyEquiv)

noncomputable def capVEquiv (p N : ℕ) : ContinuousMap.HomotopyEquiv ↥(capV p N) (YtSph p) :=
  letI : ContractibleSpace ↥(capB (N+1)) := contractibleSpace_capB (N+1)
  let e := Classical.choice (ContractibleSpace.hequiv ↥(capB (N+1)) PUnit)
  (capVHomeo p N).toHomotopyEquiv.trans
    ((ContinuousMap.HomotopyEquiv.prodCongr (ContinuousMap.HomotopyEquiv.refl (YtSph p)) e).trans
      (Homeomorph.prodPUnit (YtSph p)).toHomotopyEquiv)

noncomputable def bandEquiv (p N : ℕ) :
    ContinuousMap.HomotopyEquiv ↥(capU p N ∩ capV p N) (XYt p N) :=
  let e := Classical.choice (bandHomotopyEquiv (N+1) (by omega))
  (bandUHomeo p N).toHomotopyEquiv.trans
    (ContinuousMap.HomotopyEquiv.prodCongr (ContinuousMap.HomotopyEquiv.refl (YtSph p)) e)

def bandMap (p N : ℕ) : TopCat.of ↥(capU p N ∩ capV p N) ⟶ XN p N :=
  TopCat.ofHom (bandEquiv p N).toFun

/-- The "north pole" of `S^(N+1)` (a unit vector). -/
def sphPt (N : ℕ) : ↥(sphSet (N+2)) :=
  ⟨Work.Morse.snocLp (0 : EuclideanSpace ℝ (Fin (N+1))) 1, by
    rw [sphSet, Set.mem_setOf_eq]
    have h2 : ‖Work.Morse.snocLp (0 : EuclideanSpace ℝ (Fin (N+1))) 1‖ ^ 2 = 1 := by
      rw [Work.Morse.snocLp_norm_sq]
      simp
    rcases sq_eq_one_iff.mp h2 with h' | h'
    · exact h'
    · exact absurd h' (by
        linarith [norm_nonneg (Work.Morse.snocLp (0 : EuclideanSpace ℝ (Fin (N+1))) 1)])⟩

/-- The section of the projection `S^p × S^(N+1) → S^p` at the north pole. -/
def projSect (p N : ℕ) : TopCat.of (YtSph p) ⟶ Xs p N :=
  TopCat.ofHom ⟨fun y => (y, sphPt N), continuous_id.prodMk continuous_const⟩

lemma projSect_comp (p N : ℕ) : projSect p N ≫ projY p (N+1) = 𝟙 (TopCat.of (YtSph p)) := by
  apply TopCat.hom_ext
  ext y
  rfl

lemma bandMap_projY (p N : ℕ) : bandMap p N ≫ projY p N = projW p N := by
  apply TopCat.hom_ext
  ext x
  rfl

lemma inclUVU_comp_projU (p N : ℕ) :
    inclUVU (X := Xs p N) (capU p N) (capV p N) ≫ projU p N = projW p N := by
  apply TopCat.hom_ext
  ext x
  rfl

lemma inclUVV_comp_projV (p N : ℕ) :
    inclUVV (X := Xs p N) (capU p N) (capV p N) ≫ projV p N = projW p N := by
  apply TopCat.hom_ext
  ext x
  rfl

theorem isIso_projU (p N k : ℕ) :
    IsIso (singularCohomologyMap ℤ (TopCat.of ↥(capU p N)) (TopCat.of (YtSph p)) (projU p N) k) := by
  have h : TopCat.ofHom (capUEquiv p N).toFun = projU p N := rfl
  rw [← h]
  exact homotopyEquiv ℤ (TopCat.of ↥(capU p N)) (TopCat.of (YtSph p))
    (TopCat.ofHom (capUEquiv p N).toFun) (TopCat.ofHom (capUEquiv p N).invFun)
    (capUEquiv p N).left_inv.some (capUEquiv p N).right_inv.some k

theorem isIso_projV (p N k : ℕ) :
    IsIso (singularCohomologyMap ℤ (TopCat.of ↥(capV p N)) (TopCat.of (YtSph p)) (projV p N) k) := by
  have h : TopCat.ofHom (capVEquiv p N).toFun = projV p N := rfl
  rw [← h]
  exact homotopyEquiv ℤ (TopCat.of ↥(capV p N)) (TopCat.of (YtSph p))
    (TopCat.ofHom (capVEquiv p N).toFun) (TopCat.ofHom (capVEquiv p N).invFun)
    (capVEquiv p N).left_inv.some (capVEquiv p N).right_inv.some k

theorem isIso_bandMap (p N k : ℕ) :
    IsIso (singularCohomologyMap ℤ (TopCat.of ↥(capU p N ∩ capV p N)) (XN p N)
      (bandMap p N) k) :=
  homotopyEquiv ℤ (TopCat.of ↥(capU p N ∩ capV p N)) (XN p N)
    (bandMap p N) (TopCat.ofHom (bandEquiv p N).invFun)
    (bandEquiv p N).left_inv.some (bandEquiv p N).right_inv.some k

/-! ## The canonical map `lam : H^k(S^p) ⟶ B_k` -/

/-- The shifted module `H^{k-N}(S^p)` (zero when `k < N`). -/
def shiftCohom (p N k : ℕ) : ModuleCat ℤ :=
  if N ≤ k then singularCohomology ℤ (k - N) (TopCat.of (YtSph p)) else 0

/-- The map `H^k(S^p) → H^k(↥(capU)) ⊞ H^k(↥(capV))` whose range is the kernel of `mvCochainG`. -/
noncomputable def lam (p N k : ℕ) :
    singularCohomology ℤ k (TopCat.of (YtSph p)) ⟶
      HomologicalComplex.homology (cochainU (capU p N) (capV p N) ⊞
        cochainV (capU p N) (capV p N)) k :=
  (singularCohomologyMap ℤ (TopCat.of ↥(capU p N)) (TopCat.of (YtSph p)) (projU p N) k
      ≫ HomologicalComplex.homologyMap (biprod.inl : cochainU (capU p N) (capV p N) ⟶
          cochainU (capU p N) (capV p N) ⊞ cochainV (capU p N) (capV p N)) k)
    - (singularCohomologyMap ℤ (TopCat.of ↥(capV p N)) (TopCat.of (YtSph p)) (projV p N) k
      ≫ HomologicalComplex.homologyMap (biprod.inr : cochainV (capU p N) (capV p N) ⟶
          cochainU (capU p N) (capV p N) ⊞ cochainV (capU p N) (capV p N)) k)

section Nat

variable (p N k : ℕ)

lemma projU_inclU :
    singularCohomologyMap ℤ (TopCat.of ↥(capU p N)) (TopCat.of (YtSph p)) (projU p N) k
      ≫ singularCohomologyMap ℤ (TopCat.of ↥(capU p N ∩ capV p N)) (TopCat.of ↥(capU p N))
          (inclUVU (X := Xs p N) (capU p N) (capV p N)) k
    = singularCohomologyMap ℤ (TopCat.of ↥(capU p N ∩ capV p N)) (TopCat.of (YtSph p))
        (projW p N) k := by
  have h := singularCohomologyMap_comp (R := ℤ)
    (f := inclUVU (X := Xs p N) (capU p N) (capV p N)) (g := projU p N) k
  rw [inclUVU_comp_projU] at h
  exact h.symm

lemma projV_inclV :
    singularCohomologyMap ℤ (TopCat.of ↥(capV p N)) (TopCat.of (YtSph p)) (projV p N) k
      ≫ singularCohomologyMap ℤ (TopCat.of ↥(capU p N ∩ capV p N)) (TopCat.of ↥(capV p N))
          (inclUVV (X := Xs p N) (capU p N) (capV p N)) k
    = singularCohomologyMap ℤ (TopCat.of ↥(capU p N ∩ capV p N)) (TopCat.of (YtSph p))
        (projW p N) k := by
  have h := singularCohomologyMap_comp (R := ℤ)
    (f := inclUVV (X := Xs p N) (capU p N) (capV p N)) (g := projV p N) k
  rw [inclUVV_comp_projV] at h
  exact h.symm

lemma projY_band :
    singularCohomologyMap ℤ (XN p N) (TopCat.of (YtSph p)) (projY p N) k
      ≫ singularCohomologyMap ℤ (TopCat.of ↥(capU p N ∩ capV p N)) (XN p N)
          (bandMap p N) k
    = singularCohomologyMap ℤ (TopCat.of ↥(capU p N ∩ capV p N)) (TopCat.of (YtSph p))
        (projW p N) k := by
  have h := singularCohomologyMap_comp (R := ℤ) (f := bandMap p N) (g := projY p N) k
  rw [bandMap_projY] at h
  exact h.symm

lemma inl_comp_G :
    HomologicalComplex.homologyMap (biprod.inl : cochainU (capU p N) (capV p N) ⟶
        cochainU (capU p N) (capV p N) ⊞ cochainV (capU p N) (capV p N)) k
      ≫ HomologicalComplex.homologyMap (mvCochainG (capU p N) (capV p N)) k
    = singularCohomologyMap ℤ (TopCat.of ↥(capU p N ∩ capV p N)) (TopCat.of ↥(capU p N))
        (inclUVU (X := Xs p N) (capU p N) (capV p N)) k := by
  rw [← HomologicalComplex.homologyMap_comp, biprod_inl_mvCochainG, dualComplexMap_chainInclU]
  rfl

lemma chainInclV_eq_chainMap' {X : TopCat} (U V : Set X) :
    chainInclV U V = chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of V) (inclUVV U V) := rfl

lemma dualComplexMap_chainInclV' {X : TopCat} (U V : Set X) :
    dualComplexMap ℤ (singularChains ℤ (TopCat.of ↥(U ∩ V))) (singularChains ℤ (TopCat.of V))
      (chainInclV U V)
      = dualChainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of V) (inclUVV U V) := by
  rw [chainInclV_eq_chainMap']
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  rfl

lemma biprod_inr_mvCochainG' {X : TopCat} (U V : Set X) :
    (biprod.inr : cochainV U V ⟶ cochainU U V ⊞ cochainV U V) ≫ mvCochainG U V
      = dualComplexMap ℤ (singularChains ℤ (TopCat.of ↥(U ∩ V)))
          (singularChains ℤ (TopCat.of V)) (chainInclV U V) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, mvCochainG_inr]

lemma inr_comp_G :
    HomologicalComplex.homologyMap (biprod.inr : cochainV (capU p N) (capV p N) ⟶
        cochainU (capU p N) (capV p N) ⊞ cochainV (capU p N) (capV p N)) k
      ≫ HomologicalComplex.homologyMap (mvCochainG (capU p N) (capV p N)) k
    = singularCohomologyMap ℤ (TopCat.of ↥(capU p N ∩ capV p N)) (TopCat.of ↥(capV p N))
        (inclUVV (X := Xs p N) (capU p N) (capV p N)) k := by
  rw [← HomologicalComplex.homologyMap_comp, biprod_inr_mvCochainG', dualComplexMap_chainInclV']
  rfl

lemma lam_comp_G :
    lam p N k ≫ HomologicalComplex.homologyMap (mvCochainG (capU p N) (capV p N)) k = 0 := by
  rw [lam, Preadditive.sub_comp]
  have hp : (singularCohomologyMap ℤ (TopCat.of ↥(capU p N)) (TopCat.of (YtSph p)) (projU p N) k
      ≫ HomologicalComplex.homologyMap (biprod.inl : cochainU (capU p N) (capV p N) ⟶
          cochainU (capU p N) (capV p N) ⊞ cochainV (capU p N) (capV p N)) k)
      ≫ HomologicalComplex.homologyMap (mvCochainG (capU p N) (capV p N)) k
      = singularCohomologyMap ℤ (TopCat.of ↥(capU p N ∩ capV p N)) (TopCat.of (YtSph p))
          (projW p N) k := by
    rw [Category.assoc, inl_comp_G, projU_inclU]
  have hq : (singularCohomologyMap ℤ (TopCat.of ↥(capV p N)) (TopCat.of (YtSph p)) (projV p N) k
      ≫ HomologicalComplex.homologyMap (biprod.inr : cochainV (capU p N) (capV p N) ⟶
          cochainU (capU p N) (capV p N) ⊞ cochainV (capU p N) (capV p N)) k)
      ≫ HomologicalComplex.homologyMap (mvCochainG (capU p N) (capV p N)) k
      = singularCohomologyMap ℤ (TopCat.of ↥(capU p N ∩ capV p N)) (TopCat.of (YtSph p))
          (projW p N) k := by
    rw [Category.assoc, inr_comp_G, projV_inclV]
  rw [hp, hq]
  simp

/-! ## The identification with the small chains -/

lemma smallOfU_comp_smallToSing' {X : TopCat} (U V : Set X) :
    smallOfU U V ≫ smallToSing U V = inclChains X U := by
  have hlift : smallLiftU U V ≫ (smallSubcomplex U V).ι = TopCat.toSSet.map (inclUX U) :=
    SSet.Subcomplex.lift_ι _ _
  show SSet.chainComplexMap (smallLiftU U V) (ModuleCat.of ℤ ℤ) ≫
      SSet.chainComplexMap (smallSubcomplex U V).ι (ModuleCat.of ℤ ℤ) = _
  rw [← Functor.map_comp, hlift]
  rfl

lemma smallOfV_comp_smallToSing' {X : TopCat} (U V : Set X) :
    smallOfV U V ≫ smallToSing U V = inclChains X V := by
  have hlift : smallLiftV U V ≫ (smallSubcomplex U V).ι = TopCat.toSSet.map (inclVX V) :=
    SSet.Subcomplex.lift_ι _ _
  show SSet.chainComplexMap (smallLiftV U V) (ModuleCat.of ℤ ℤ) ≫
      SSet.chainComplexMap (smallSubcomplex U V).ι (ModuleCat.of ℤ ℤ) = _
  rw [← Functor.map_comp, hlift]
  rfl

/-- The dual of the inclusion of the small chains, as a cohomology map. -/
noncomputable def smallIsoHom {X : TopCat} (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n : ℕ) :
    singularCohomology ℤ n X ⟶ HomologicalComplex.homology (dualComplex ℤ (smallChains U V)) n :=
  HomologicalComplex.homologyMap
    (dualComplexMap ℤ (smallChains U V) (singularChains ℤ X) (smallToSing U V)) n

lemma smallIsoHom_comp_smallOfU {X : TopCat} (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n : ℕ) :
    smallIsoHom U V hU hV hcov n
      ≫ HomologicalComplex.homologyMap (dualComplexMap ℤ (singularChains ℤ (TopCat.of U))
          (smallChains U V) (smallOfU U V)) n
      = singularCohomologyMap ℤ (TopCat.of U) X (subtypeIncl X U) n := by
  show HomologicalComplex.homologyMap
      (dualComplexMap ℤ (smallChains U V) (singularChains ℤ X) (smallToSing U V)) n
      ≫ HomologicalComplex.homologyMap
        (dualComplexMap ℤ (singularChains ℤ (TopCat.of U)) (smallChains U V) (smallOfU U V)) n = _
  rw [← HomologicalComplex.homologyMap_comp, ← dualComplexMap_comp, smallOfU_comp_smallToSing']
  rfl

lemma smallIsoHom_comp_smallOfV {X : TopCat} (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n : ℕ) :
    smallIsoHom U V hU hV hcov n
      ≫ HomologicalComplex.homologyMap (dualComplexMap ℤ (singularChains ℤ (TopCat.of V))
          (smallChains U V) (smallOfV U V)) n
      = singularCohomologyMap ℤ (TopCat.of V) X (subtypeIncl X V) n := by
  show HomologicalComplex.homologyMap
      (dualComplexMap ℤ (smallChains U V) (singularChains ℤ X) (smallToSing U V)) n
      ≫ HomologicalComplex.homologyMap
        (dualComplexMap ℤ (singularChains ℤ (TopCat.of V)) (smallChains U V) (smallOfV U V)) n = _
  rw [← HomologicalComplex.homologyMap_comp, ← dualComplexMap_comp, smallOfV_comp_smallToSing']
  rfl

/-- The pullback of the projection `S^p × S^N → S^p` into the small chains of the cap cover. -/
noncomputable def sigmaPi (p N k : ℕ) :
    singularCohomology ℤ k (TopCat.of (YtSph p)) ⟶
      HomologicalComplex.homology (dualComplex ℤ (smallChains (capU p N) (capV p N))) k :=
  singularCohomologyMap ℤ (Xs p N) (TopCat.of (YtSph p)) (projY p (N+1)) k
    ≫ smallIsoHom (capU p N) (capV p N) (isOpen_capU p N) (isOpen_capV p N)
        (capU_union_capV p N) k

lemma inclUX_comp_projY (p N : ℕ) :
    inclUX (X := Xs p N) (capU p N) ≫ projY p (N+1) = projU p N := by
  apply TopCat.hom_ext
  ext x
  rfl

lemma inclVX_comp_projY (p N : ℕ) :
    inclVX (X := Xs p N) (capV p N) ≫ projY p (N+1) = projV p N := by
  apply TopCat.hom_ext
  ext x
  rfl

lemma mvCochainF_fst_glob (p N : ℕ) :
    mvCochainF (capU p N) (capV p N) ≫ (biprod.fst : cochainU (capU p N) (capV p N) ⊞
        cochainV (capU p N) (capV p N) ⟶ cochainU (capU p N) (capV p N))
      = dualComplexMap ℤ (singularChains ℤ (TopCat.of ↥(capU p N))) (smallChains (capU p N) (capV p N))
          (smallOfU (capU p N) (capV p N)) := by
  apply HomologicalComplex.hom_ext
  intro n
  exact mvCochainF_fst (capU p N) (capV p N) n

lemma mvCochainF_snd_glob (p N : ℕ) :
    mvCochainF (capU p N) (capV p N) ≫ (biprod.snd : cochainU (capU p N) (capV p N) ⊞
        cochainV (capU p N) (capV p N) ⟶ cochainV (capU p N) (capV p N))
      = -(dualComplexMap ℤ (singularChains ℤ (TopCat.of ↥(capV p N))) (smallChains (capU p N) (capV p N))
          (smallOfV (capU p N) (capV p N))) := by
  apply HomologicalComplex.hom_ext
  intro n
  exact mvCochainF_snd (capU p N) (capV p N) n

/-- Two morphisms into a homology of a biproduct of complexes agree if their two components do. -/
lemma homologyMap_biprod_ext {C D : CochainComplex (ModuleCat ℤ) ℕ} {W : ModuleCat ℤ} (k : ℕ)
    {f g : W ⟶ HomologicalComplex.homology (C ⊞ D) k}
    (h1 : f ≫ HomologicalComplex.homologyMap (biprod.fst : C ⊞ D ⟶ C) k
      = g ≫ HomologicalComplex.homologyMap (biprod.fst : C ⊞ D ⟶ C) k)
    (h2 : f ≫ HomologicalComplex.homologyMap (biprod.snd : C ⊞ D ⟶ D) k
      = g ≫ HomologicalComplex.homologyMap (biprod.snd : C ⊞ D ⟶ D) k) : f = g := by
  have htot := coh_homologyMap_total C D k
  have key : ∀ {W' : ModuleCat ℤ} (u : W' ⟶ HomologicalComplex.homology (C ⊞ D) k),
      u = (u ≫ HomologicalComplex.homologyMap (biprod.fst : C ⊞ D ⟶ C) k)
            ≫ HomologicalComplex.homologyMap (biprod.inl : C ⟶ C ⊞ D) k
          + (u ≫ HomologicalComplex.homologyMap (biprod.snd : C ⊞ D ⟶ D) k)
            ≫ HomologicalComplex.homologyMap (biprod.inr : D ⟶ C ⊞ D) k := by
    intro W' u
    calc u = u ≫ 𝟙 _ := (Category.comp_id u).symm
      _ = u ≫ (HomologicalComplex.homologyMap (biprod.fst : C ⊞ D ⟶ C) k
              ≫ HomologicalComplex.homologyMap (biprod.inl : C ⟶ C ⊞ D) k
            + HomologicalComplex.homologyMap (biprod.snd : C ⊞ D ⟶ D) k
              ≫ HomologicalComplex.homologyMap (biprod.inr : D ⟶ C ⊞ D) k) := by rw [htot]
      _ = _ := by rw [Preadditive.comp_add, Category.assoc, Category.assoc]
  rw [key f, key g, h1, h2]

/-- The first component of `lam`. -/
lemma lam_fst (p N k : ℕ) :
    lam p N k ≫ HomologicalComplex.homologyMap (biprod.fst : cochainU (capU p N) (capV p N) ⊞
        cochainV (capU p N) (capV p N) ⟶ cochainU (capU p N) (capV p N)) k
      = singularCohomologyMap ℤ (TopCat.of ↥(capU p N)) (TopCat.of (YtSph p)) (projU p N) k := by
  have hA : (singularCohomologyMap ℤ (TopCat.of ↥(capU p N)) (TopCat.of (YtSph p)) (projU p N) k
        ≫ HomologicalComplex.homologyMap (biprod.inl : cochainU (capU p N) (capV p N) ⟶
            cochainU (capU p N) (capV p N) ⊞ cochainV (capU p N) (capV p N)) k)
        ≫ HomologicalComplex.homologyMap (biprod.fst : cochainU (capU p N) (capV p N) ⊞
            cochainV (capU p N) (capV p N) ⟶ cochainU (capU p N) (capV p N)) k
      = singularCohomologyMap ℤ (TopCat.of ↥(capU p N)) (TopCat.of (YtSph p)) (projU p N) k := by
    rw [Category.assoc, ← HomologicalComplex.homologyMap_comp, biprod.inl_fst,
      HomologicalComplex.homologyMap_id]
    change singularCohomologyMap ℤ (TopCat.of ↥(capU p N)) (TopCat.of (YtSph p)) (projU p N) k
      ≫ 𝟙 (singularCohomology ℤ k (TopCat.of ↥(capU p N)))
      = singularCohomologyMap ℤ (TopCat.of ↥(capU p N)) (TopCat.of (YtSph p)) (projU p N) k
    rw [Category.comp_id]
  have hB : (singularCohomologyMap ℤ (TopCat.of ↥(capV p N)) (TopCat.of (YtSph p)) (projV p N) k
        ≫ HomologicalComplex.homologyMap (biprod.inr : cochainV (capU p N) (capV p N) ⟶
            cochainU (capU p N) (capV p N) ⊞ cochainV (capU p N) (capV p N)) k)
        ≫ HomologicalComplex.homologyMap (biprod.fst : cochainU (capU p N) (capV p N) ⊞
            cochainV (capU p N) (capV p N) ⟶ cochainU (capU p N) (capV p N)) k = 0 := by
    rw [Category.assoc, ← HomologicalComplex.homologyMap_comp, biprod.inr_fst]
    simp
  rw [lam, Preadditive.sub_comp, hA, hB]
  simp

/-- The second component of `lam`. -/
lemma lam_snd (p N k : ℕ) :
    lam p N k ≫ HomologicalComplex.homologyMap (biprod.snd : cochainU (capU p N) (capV p N) ⊞
        cochainV (capU p N) (capV p N) ⟶ cochainV (capU p N) (capV p N)) k
      = - singularCohomologyMap ℤ (TopCat.of ↥(capV p N)) (TopCat.of (YtSph p)) (projV p N) k := by
  have hA : (singularCohomologyMap ℤ (TopCat.of ↥(capU p N)) (TopCat.of (YtSph p)) (projU p N) k
        ≫ HomologicalComplex.homologyMap (biprod.inl : cochainU (capU p N) (capV p N) ⟶
            cochainU (capU p N) (capV p N) ⊞ cochainV (capU p N) (capV p N)) k)
        ≫ HomologicalComplex.homologyMap (biprod.snd : cochainU (capU p N) (capV p N) ⊞
            cochainV (capU p N) (capV p N) ⟶ cochainV (capU p N) (capV p N)) k = 0 := by
    rw [Category.assoc, ← HomologicalComplex.homologyMap_comp, biprod.inl_snd]
    simp
  have hB : (singularCohomologyMap ℤ (TopCat.of ↥(capV p N)) (TopCat.of (YtSph p)) (projV p N) k
        ≫ HomologicalComplex.homologyMap (biprod.inr : cochainV (capU p N) (capV p N) ⟶
            cochainU (capU p N) (capV p N) ⊞ cochainV (capU p N) (capV p N)) k)
        ≫ HomologicalComplex.homologyMap (biprod.snd : cochainU (capU p N) (capV p N) ⊞
            cochainV (capU p N) (capV p N) ⟶ cochainV (capU p N) (capV p N)) k
      = singularCohomologyMap ℤ (TopCat.of ↥(capV p N)) (TopCat.of (YtSph p)) (projV p N) k := by
    rw [Category.assoc, ← HomologicalComplex.homologyMap_comp, biprod.inr_snd,
      HomologicalComplex.homologyMap_id]
    change singularCohomologyMap ℤ (TopCat.of ↥(capV p N)) (TopCat.of (YtSph p)) (projV p N) k
      ≫ 𝟙 (singularCohomology ℤ k (TopCat.of ↥(capV p N)))
      = singularCohomologyMap ℤ (TopCat.of ↥(capV p N)) (TopCat.of (YtSph p)) (projV p N) k
    rw [Category.comp_id]
  rw [lam, Preadditive.sub_comp, hA, hB]
  simp

end Nat

end
end Work.Cohomology
