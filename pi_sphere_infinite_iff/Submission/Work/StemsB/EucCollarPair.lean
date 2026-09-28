import Submission.Work.StemsB.CollarNorm
import Submission.Work.StemsB.EucCubeAffine
import Submission.Work.Cohomology.relChainsMapOf_isIso

/-!
# The Euclidean collar pair: the normalisation is a homotopy equivalence of pairs

The radial normalisation `Work.StemsB.collarNorm` sends the inner piece `eucBig n = {|v|_∞ < 3/2}`
into the cube `eucCube n = {|v|_∞ ≤ 1}` and the collar `eucCollar n = {1/2 < |v|_∞ < 3/2}` onto the
boundary `eucBdry n = {|v|_∞ = 1}`.  This file proves that it is a homotopy equivalence of pairs,
with homotopy inverse the inclusion and with the radial interpolation
`Work.StemsB.collarInterp` (reparametrised by `σ`) as the homotopy, and it draws the consequences

* `Work.StemsB.isIso_eucNormRelChains` — the induced map of *relative* chain complexes is a
  quasi-isomorphism;
* `Work.StemsB.eucCollar_iso`, `Work.StemsB.eucCollar_isZero` — the relative homology of the collar
  pair (in the Euclidean model), computed from the cube pair `Work.StemsB.cubePair_main`.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

namespace Work.StemsB

noncomputable section

variable {n : ℕ} {Y : Type} [TopologicalSpace Y]

/-! ## The continuous maps -/

/-- The normalisation on the total space `↥(eucBig n) × Y`. -/
def eucNormMap (n : ℕ) : C(↥(eucBig n) × Y, ↥(eucCube n) × Y) :=
  ⟨fun p => (⟨collarNorm n p.1.1, collarNorm_mem_cube n p.1.1⟩, p.2), by fun_prop⟩

/-- The inclusion of the cube into the inner piece. -/
def eucCubeInclMap (n : ℕ) : C(↥(eucCube n) × Y, ↥(eucBig n) × Y) :=
  ⟨fun p => (⟨p.1.1, eucCube_subset_eucBig n p.1.2⟩, p.2), by fun_prop⟩

/-- The normalisation on the collar, as a map to the boundary. -/
def eucNormRelMapFun (n : ℕ) : C(↥(eucCollarProd n Y), ↥(eucBdryProd n Y)) :=
  ⟨fun p => ⟨(⟨collarNorm n p.1.1.1, collarNorm_mem_cube n p.1.1.1⟩, p.1.2),
      collarNorm_mem_bdry_of_mem_collar n p.1.1.1 p.2⟩, by fun_prop⟩

/-- The inclusion of the boundary into the collar. -/
def eucBdryInclMap (n : ℕ) : C(↥(eucBdryProd n Y), ↥(eucCollarProd n Y)) :=
  ⟨fun p => ⟨(⟨p.1.1.1, eucCube_subset_eucBig n p.1.1.2⟩, p.1.2),
      eucBdry_subset_eucCollar n p.2⟩, by fun_prop⟩

/-- The maps as morphisms of `TopCat`. -/
def eucNormHom (n : ℕ) :
    TopCat.of (↥(eucBig n) × Y) ⟶ TopCat.of (↥(eucCube n) × Y) :=
  TopCat.ofHom (eucNormMap (Y := Y) n)

def eucCubeInclHom (n : ℕ) :
    TopCat.of (↥(eucCube n) × Y) ⟶ TopCat.of (↥(eucBig n) × Y) :=
  TopCat.ofHom (eucCubeInclMap (Y := Y) n)

def eucNormRelHom (n : ℕ) :
    TopCat.of ↥(eucCollarProd n Y) ⟶ TopCat.of ↥(eucBdryProd n Y) :=
  TopCat.ofHom (eucNormRelMapFun (Y := Y) n)

def eucBdryInclHom (n : ℕ) :
    TopCat.of ↥(eucBdryProd n Y) ⟶ TopCat.of ↥(eucCollarProd n Y) :=
  TopCat.ofHom (eucBdryInclMap (Y := Y) n)

@[simp] theorem eucNormMap_apply (n : ℕ) (p : ↥(eucBig n) × Y) :
    eucNormMap (Y := Y) n p = (⟨collarNorm n p.1.1, collarNorm_mem_cube n p.1.1⟩, p.2) := rfl

@[simp] theorem eucCubeInclMap_apply (n : ℕ) (p : ↥(eucCube n) × Y) :
    eucCubeInclMap (Y := Y) n p = (⟨p.1.1, eucCube_subset_eucBig n p.1.2⟩, p.2) := rfl

@[simp] theorem eucNormRelMapFun_apply (n : ℕ) (p : ↥(eucCollarProd n Y)) :
    eucNormRelMapFun (Y := Y) n p =
      ⟨(⟨collarNorm n p.1.1.1, collarNorm_mem_cube n p.1.1.1⟩, p.1.2),
        collarNorm_mem_bdry_of_mem_collar n p.1.1.1 p.2⟩ := rfl

@[simp] theorem eucBdryInclMap_apply (n : ℕ) (p : ↥(eucBdryProd n Y)) :
    eucBdryInclMap (Y := Y) n p =
      ⟨(⟨p.1.1.1, eucCube_subset_eucBig n p.1.1.2⟩, p.1.2),
        eucBdry_subset_eucCollar n p.2⟩ := rfl

/-! ## The homotopies -/

/-- The radial interpolation on the inner piece (reparametrised by `σ`, so that it starts at the
normalisation) exhibits the normalisation followed by the inclusion as homotopic to the
identity. -/
def eucNormInclHomotopy (n : ℕ) :
    TopCat.Homotopy (eucNormHom (Y := Y) n ≫ eucCubeInclHom (Y := Y) n)
      (𝟙 (TopCat.of (↥(eucBig n) × Y))) :=
  ContinuousMap.Homotopy.mk
    ⟨fun z => (let p : ↥(eucBig n) × Y := z.2
      (⟨collarInterp n (p.1.1, σ z.1), collarInterp_mem_big n p.1.1 (σ z.1) p.1.2⟩, p.2)),
      by fun_prop⟩
    (fun p => by
      simp only [ContinuousMap.comp_apply, eucNormMap_apply, eucCubeInclMap_apply,
        unitInterval.symm_zero, collarInterp_one]
      rfl)
    (fun p => by
      simp only [ContinuousMap.id_apply, unitInterval.symm_one, collarInterp_zero]
      rfl)

/-- The radial interpolation on the cube exhibits the inclusion followed by the normalisation as
homotopic to the identity. -/
def eucInclNormHomotopy (n : ℕ) :
    TopCat.Homotopy (eucCubeInclHom (Y := Y) n ≫ eucNormHom (Y := Y) n)
      (𝟙 (TopCat.of (↥(eucCube n) × Y))) :=
  ContinuousMap.Homotopy.mk
    ⟨fun z => (let p : ↥(eucCube n) × Y := z.2
      (⟨collarInterp n (p.1.1, σ z.1), collarInterp_mem_cube n p.1.1 (σ z.1) p.1.2⟩, p.2)),
      by fun_prop⟩
    (fun p => by
      simp only [ContinuousMap.comp_apply, eucCubeInclMap_apply, eucNormMap_apply,
        unitInterval.symm_zero, collarInterp_one]
      rfl)
    (fun p => by
      simp only [ContinuousMap.id_apply, unitInterval.symm_one, collarInterp_zero]
      rfl)

/-- The interpolation stays in the collar: the normalisation on the collar followed by the
inclusion is homotopic to the identity of the collar. -/
def eucNormBdryHomotopy (n : ℕ) :
    TopCat.Homotopy (eucNormRelHom (Y := Y) n ≫ eucBdryInclHom (Y := Y) n)
      (𝟙 (TopCat.of ↥(eucCollarProd n Y))) :=
  ContinuousMap.Homotopy.mk
    ⟨fun z => (let p : ↥(eucCollarProd n Y) := z.2
      ⟨(⟨collarInterp n (p.1.1.1, σ z.1),
          collarInterp_mem_big n p.1.1.1 (σ z.1) p.1.1.2⟩, p.1.2),
        collarInterp_mem_collar n p.1.1.1 (σ z.1) p.2⟩), by fun_prop⟩
    (fun p => by
      simp only [ContinuousMap.comp_apply, eucNormRelMapFun_apply, eucBdryInclMap_apply,
        unitInterval.symm_zero, collarInterp_one]
      rfl)
    (fun p => by
      simp only [ContinuousMap.id_apply, unitInterval.symm_one, collarInterp_zero]
      rfl)

/-- The interpolation is constant on the boundary: the inclusion of the boundary followed by the
normalisation is homotopic to the identity of the boundary. -/
def eucBdryNormHomotopy (n : ℕ) :
    TopCat.Homotopy (eucBdryInclHom (Y := Y) n ≫ eucNormRelHom (Y := Y) n)
      (𝟙 (TopCat.of ↥(eucBdryProd n Y))) :=
  ContinuousMap.Homotopy.mk
    ⟨fun z => (let q : ↥(eucBdryProd n Y) := z.2
      ⟨(⟨collarInterp n (q.1.1.1, σ z.1),
          collarInterp_mem_cube n q.1.1.1 (σ z.1) q.1.1.2⟩, q.1.2),
        by
          change collarInterp n (q.1.1.1, σ z.1) ∈ eucBdry n
          rw [collarInterp_eq_self_of_mem_eucBdry n q.1.1.1 (σ z.1) q.2]
          exact q.2⟩), by fun_prop⟩
    (fun p => by
      simp only [ContinuousMap.comp_apply, eucBdryInclMap_apply, eucNormRelMapFun_apply,
        unitInterval.symm_zero, collarInterp_one]
      rfl)
    (fun p => by
      simp only [ContinuousMap.id_apply, unitInterval.symm_one, collarInterp_zero]
      rfl)

/-! ## The homological consequences -/

/-- **The normalisation induces isomorphisms on the singular homology of the total spaces.** -/
theorem isIso_eucNormHomology (n : ℕ) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of (↥(eucBig n) × Y)) (TopCat.of (↥(eucCube n) × Y)) (eucNormHom (Y := Y) n)) k) :=
  Work.Cohomology.homologyEquiv ℤ (TopCat.of (↥(eucBig n) × Y))
    (TopCat.of (↥(eucCube n) × Y)) (eucNormHom (Y := Y) n) (eucCubeInclHom (Y := Y) n)
    (eucNormInclHomotopy (Y := Y) n) (eucInclNormHomotopy (Y := Y) n) k

/-- **The normalisation induces isomorphisms on the singular homology of the relative parts.** -/
theorem isIso_eucNormRelHomology (n : ℕ) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of ↥(eucCollarProd n Y)) (TopCat.of ↥(eucBdryProd n Y))
      (eucNormRelHom (Y := Y) n)) k) :=
  Work.Cohomology.homologyEquiv ℤ (TopCat.of ↥(eucCollarProd n Y))
    (TopCat.of ↥(eucBdryProd n Y)) (eucNormRelHom (Y := Y) n) (eucBdryInclHom (Y := Y) n)
    (eucNormBdryHomotopy (Y := Y) n) (eucBdryNormHomotopy (Y := Y) n) k

/-- The compatibility of the two maps with the inclusions of the relative parts. -/
theorem eucNormHom_subtypeIncl (n : ℕ) :
    Work.Cohomology.subtypeIncl (TopCat.of (↥(eucBig n) × Y)) (eucCollarProd n Y)
        ≫ eucNormHom (Y := Y) n
      = eucNormRelHom (Y := Y) n
        ≫ Work.Cohomology.subtypeIncl (TopCat.of (↥(eucCube n) × Y)) (eucBdryProd n Y) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  rfl

/-- The chain map of relative complexes induced by the normalisation. -/
def eucNormRelMap (n : ℕ) :
    Work.Cohomology.relChains (TopCat.of (↥(eucBig n) × Y)) (eucCollarProd n Y) ⟶
      Work.Cohomology.relChains (TopCat.of (↥(eucCube n) × Y)) (eucBdryProd n Y) :=
  Work.Cohomology.relChainsMapOf (TopCat.of (↥(eucBig n) × Y))
    (TopCat.of (↥(eucCube n) × Y)) (eucCollarProd n Y) (eucBdryProd n Y)
    (eucNormHom (Y := Y) n) (eucNormRelHom (Y := Y) n) (eucNormHom_subtypeIncl (Y := Y) n)

/-- **The normalisation is a quasi-isomorphism of the relative chain complexes.** -/
theorem isIso_eucNormRelChains (n : ℕ) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (eucNormRelMap (Y := Y) n) k) :=
  Work.Cohomology.relChainsMapOf_isIso (X := TopCat.of (↥(eucBig n) × Y))
    (Y := TopCat.of (↥(eucCube n) × Y)) (eucCollarProd n Y) (eucBdryProd n Y)
    (eucNormHom (Y := Y) n) (eucNormRelHom (Y := Y) n) (eucNormHom_subtypeIncl (Y := Y) n) k
    (fun m => isIso_eucNormHomology (Y := Y) n m)
    (fun m => isIso_eucNormRelHomology (Y := Y) n m)

/-- **The relative homology of the Euclidean collar pair in degrees above the dimension.** -/
theorem eucCollar_iso (n : ℕ) (hn : 1 ≤ n) (Y : Type) [TopologicalSpace Y] (j : ℕ) :
    Nonempty (((Work.Cohomology.relChains (TopCat.of (↥(eucBig n) × Y))
        (eucCollarProd n Y)).homology (j + n)) ≅
      (Work.Cohomology.singularChains ℤ (TopCat.of Y)).homology j) := by
  obtain ⟨e₁⟩ := cubePair_iso n Y j
  haveI h₁ : IsIso (HomologicalComplex.homologyMap (eucNormRelMap (Y := Y) n) (j + n)) :=
    isIso_eucNormRelChains (Y := Y) n (j + n)
  haveI h₂ : IsIso (HomologicalComplex.homologyMap (eucAffineRelMap (Y := Y) n) (j + n)) :=
    isIso_eucAffineRelChains (Y := Y) n (j + n)
  exact ⟨asIso (HomologicalComplex.homologyMap (eucNormRelMap (Y := Y) n) (j + n)) ≪≫
    asIso (HomologicalComplex.homologyMap (eucAffineRelMap (Y := Y) n) (j + n)) ≪≫ e₁⟩

/-- **The relative homology of the Euclidean collar pair vanishes below the dimension.** -/
theorem eucCollar_isZero (n : ℕ) (hn : 1 ≤ n) (Y : Type) [TopologicalSpace Y] (m : ℕ)
    (hm : m < n) :
    IsZero ((Work.Cohomology.relChains (TopCat.of (↥(eucBig n) × Y))
      (eucCollarProd n Y)).homology m) :=
  haveI h₁ : IsIso (HomologicalComplex.homologyMap (eucNormRelMap (Y := Y) n) m) :=
    isIso_eucNormRelChains (Y := Y) n m
  haveI h₂ : IsIso (HomologicalComplex.homologyMap (eucAffineRelMap (Y := Y) n) m) :=
    isIso_eucAffineRelChains (Y := Y) n m
  IsZero.of_iso (IsZero.of_iso (cubePair_isZero n Y m hm)
      (asIso (HomologicalComplex.homologyMap (eucAffineRelMap (Y := Y) n) m)))
    (asIso (HomologicalComplex.homologyMap (eucNormRelMap (Y := Y) n) m))

end

end Work.StemsB
