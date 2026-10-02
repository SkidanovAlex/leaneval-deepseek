import Mathlib
import Submission.Work.RatHurewicz.Cofibre.StableRangeDefs
import Submission.Work.RatHurewicz.Cofibre.BMInstantiate
import Submission.Work.RatHurewicz.Cofibre.isIso_beta_cofibreV
import Submission.Work.RatHurewicz.Cofibre.collar_homotopyEquiv
import Submission.Work.RatHurewicz.Cofibre.URetractEqv
import Submission.Work.RatHurewicz.Cofibre.UShrink
import Submission.Work.RatHurewicz.Cofibre.coneMidHomotopyEquiv
import Submission.Work.RatHurewicz.Cofibre.collarHomotopyEquiv
import Submission.Work.Serre.Assembly.serreK2IntSharp
import Submission.Work.Cohomology.relChainsMapOf_comp
import Submission.Work.RatHurewicz.relHurewiczClass_eq_of_homotopic
import Submission.Work.Thom.PairPrism
import Submission.Work.Serre.serreRangeEMVanAll

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option linter.style.haveILetI false

/-!
# The comparison maps of the cofibre computation of Serre's exact sequence

This file fixes the vocabulary of the final assembly of
`Work.RatHurewicz.fibrationPairMap_injective_stableRange`.

For a continuous map `ι : C(F,E)` put

* `C := cofibre ι = E ∪_F CF`, `U := cofibreU ι = {h < 1/2}`, `V := cofibreV ι = {0 < h}`
  (the two open pieces of the Blakers–Massey cover),
* `collarSet ι := {z : ↥U | (z : C) ∈ V}`, so that the pair `(U, U∩V)` has relative chains
  `relChains (TopCat.of ↥U) (collarSet ι)`.

The comparison map of pairs `(U, U∩V) → (E, range ι)` is `uMap`: its first component is the
retraction `cofibreURetract : ↥U → E` (a homotopy equivalence, `cofibreUHomotopyEquiv`) and its
second component is the "base of a cone point" `collarBase : ↥(U∩V) → ↥F`.

The map `psiMap` is the pair map `(C,V) → (B,{b})` induced by a continuous map `c : C → B` which is
constant with value `b` on `V`.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits
open Work.RatHurewicz

namespace Work.RatHurewicz.Cofibre

noncomputable section

variable {E : Type} [TopologicalSpace E] {F : Set E}

/-! ## The fibre inclusion -/

theorem range_setIncl (F : Set E) : Set.range (setIncl F : C(↥F, E)) = F := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-! ## The collar, viewed as a subset of `↥U` -/

/-- The collar `U ∩ V`, viewed as a subset of `↥(cofibreU ι)`. -/
abbrev collarSet (ι : C(↥F, E)) : Set ↥(cofibreU ι) :=
  {z | (z : cofibre ι) ∈ cofibreV ι}

/-- The canonical map `↥(collarSet ι) → ↥(cofibreU ι ∩ cofibreV ι)`. -/
def collarInter (ι : C(↥F, E)) :
    C(↥(collarSet ι), ↥(cofibreU ι ∩ cofibreV ι)) where
  toFun z := ⟨z.1.1, z.1.2, z.2⟩
  continuous_toFun := Continuous.subtype_mk
    (f := fun z : ↥(collarSet ι) => (z.1.1 : cofibre ι))
    (continuous_subtype_val.comp continuous_subtype_val)
    (fun z => ⟨z.1.2, z.2⟩)

/-- The inverse of `collarInter`. -/
def collarInterInv (ι : C(↥F, E)) :
    C(↥(cofibreU ι ∩ cofibreV ι), ↥(collarSet ι)) where
  toFun z := ⟨⟨z.1, z.2.1⟩, z.2.2⟩
  continuous_toFun := Continuous.subtype_mk
    (f := fun z : ↥(cofibreU ι ∩ cofibreV ι) => (⟨z.1, z.2.1⟩ : ↥(cofibreU ι)))
    (Continuous.subtype_mk
      (f := fun z : ↥(cofibreU ι ∩ cofibreV ι) => (z.1 : cofibre ι))
      continuous_subtype_val (fun z => z.2.1))
    (fun z => z.2.2)

theorem collarInter_comp_inv (ι : C(↥F, E)) :
    (collarInterInv ι).comp (collarInter ι) = ContinuousMap.id _ := by
  ext z
  rfl

theorem collarInterInv_comp (ι : C(↥F, E)) :
    (collarInter ι).comp (collarInterInv ι) = ContinuousMap.id _ := by
  ext z
  rfl

/-- The canonical map `↥(collarSet ι) → ↥(U∩V)` is a homotopy equivalence. -/
def collarInterHE (ι : C(↥F, E)) :
    ContinuousMap.HomotopyEquiv ↥(collarSet ι) ↥(cofibreU ι ∩ cofibreV ι) where
  toFun := collarInter ι
  invFun := collarInterInv ι
  left_inv := by
    have h := collarInter_comp_inv ι
    rw [h]
  right_inv := by
    have h := collarInterInv_comp ι
    rw [h]

/-! ## The middle of the cone is homotopy equivalent to `F` -/

/-- The homotopy equivalence `midSet ≃ F`, with `coneMidProj` as its forward map. -/
def coneMidHE (F : Type) [TopologicalSpace F] [Nonempty F] :
    ContinuousMap.HomotopyEquiv ↥(coneMidSet (F := F)) F where
  toFun := coneMidProj (F := F)
  invFun := coneMidSec (F := F)
  left_inv := ⟨(coneMidHomotopyId (F := F)).symm⟩
  right_inv := by
    have hcomp : (coneMidProj (F := F)).comp (coneMidSec (F := F)) = ContinuousMap.id F := by
      ext x
      show coneMidProj (F := F) (coneMidMk (F := F) ⟨(x, coneQuarter), coneMid_mem_sec (F := F) x⟩)
        = x
      exact coneMidProj_coneMidMk (F := F) ⟨(x, coneQuarter), coneMid_mem_sec (F := F) x⟩
    rw [hcomp]

/-- The composite `↥(U∩V) → ↥midSet → F`. -/
def collarBaseMid (ι : C(↥F, E)) [Nonempty ↥F] :
    C(↥(cofibreU ι ∩ cofibreV ι), ↥F) :=
  (coneMidProj (F := ↥F)).comp (collarToMid ι)

theorem isIso_intHomologyMap_collarBaseMid (ι : C(↥F, E)) [Nonempty ↥F] (n : ℕ) :
    IsIso (Work.Serre.intHomologyMap (collarBaseMid ι) n) :=
  Work.Serre.isIso_intHomologyMap_of_homotopyEquiv
    ((collarMidHomotopyEquiv ι).trans (coneMidHE ↥F)) n

/-- **The "base of a collar point"** `↥(U∩V) → F`. -/
def collarBase (ι : C(↥F, E)) [Nonempty ↥F] : C(↥(collarSet ι), ↥F) :=
  (collarBaseMid ι).comp (collarInter ι)

theorem isIso_intHomologyMap_collarBase (ι : C(↥F, E)) [Nonempty ↥F] (n : ℕ) :
    IsIso (Work.Serre.intHomologyMap (collarBase ι) n) := by
  rw [show collarBase ι = (collarBaseMid ι).comp (collarInter ι) from rfl,
    Work.Serre.intHomologyMap_comp]
  haveI h1 : IsIso (Work.Serre.intHomologyMap (collarInter ι) n) :=
    Work.Serre.isIso_intHomologyMap_of_homotopyEquiv (collarInterHE ι) n
  haveI h2 : IsIso (Work.Serre.intHomologyMap (collarBaseMid ι) n) :=
    isIso_intHomologyMap_collarBaseMid ι n
  exact IsIso.comp_isIso

/-! ## The identification of `cofibreURetract` with the base map on the collar -/

theorem mem_midSet_of_mem (ι : C(↥F, E)) {y : Work.Stems.Cone ↥F}
    (hU : cofibreInclCone ι y ∈ cofibreU ι) (hV : cofibreInclCone ι y ∈ cofibreV ι) :
    y ∈ midSet (F := ↥F) :=
  ⟨(mem_cofibreV_coneIncl_iff ι y).mp hV, (mem_cofibreU_coneIncl_iff ι y).mp hU⟩

/-- **On the collar the retraction `cofibreURetract` is `ι` applied to the base of the cone
point.**  Stated for `ι = setIncl F`, so that `ι` can be evaluated on the base point. -/
theorem cofibreURetract_eq_collarBase (F : Set E) [Nonempty E] [Nonempty ↥F] (e₀ : E)
    (z : ↥(collarSet (setIncl F))) :
    cofibreURetract (setIncl F) e₀ z.1 = (collarBase (setIncl F) z : E) := by
  obtain ⟨⟨q, hq'⟩, hV⟩ := z
  obtain ⟨a, ha⟩ := Quotient.exists_rep q
  subst ha
  obtain ⟨y, hymid, hay⟩ : a ∈ Sum.inr '' midSet (F := ↥F) := by
    rw [← preimage_collar (setIncl F)]
    exact ⟨hq', hV⟩
  subst hay
  rw [cofibreURetract_mk (setIncl F) e₀ (Sum.inr y) hq']
  rw [show uRetractFun (setIncl F) e₀ (Sum.inr y)
      = coneBaseLtHalf (setIncl F) ⟨y, hymid.2⟩ from dif_pos hymid.2]
  obtain ⟨p, rfl⟩ := Quotient.exists_rep y
  have hmid : (Quotient.mk'' p : Work.Stems.Cone ↥F) ∈ midSet (F := ↥F) := hymid
  have hcb : (coneBaseLtHalf (setIncl F)) ⟨Quotient.mk'' (p : ↥F × unitInterval), hmid.2⟩
      = (setIncl F) p.1 :=
    coneBaseLtHalf_coneMk (setIncl F) p hmid.2
  rw [hcb]
  show ((setIncl F) p.1) = (coneMidProj (F := ↥F) (collarToMid (setIncl F)
    ⟨Quotient.mk'' (Sum.inr (Quotient.mk'' p)), ⟨hq', hV⟩⟩) : E)
  rw [collarToMid_mk (setIncl F) (Sum.inr (Quotient.mk'' p)) ⟨hq', hV⟩]
  rw [collarToMidRaw_inr (setIncl F) (a := Sum.inr (Quotient.mk'' p)) ⟨hq', hV⟩ rfl hmid]
  show ((setIncl F) p.1) = (coneMidProj (F := ↥F) (coneMidMk (F := ↥F) ⟨p, hmid⟩) : E)
  exact congrArg (fun x : ↥F => (x : E))
    (coneMidProj_coneMidMk (F := ↥F) ⟨p, hmid⟩).symm

/-! ## The comparison maps -/

/-- **The comparison `(U, U∩V) → (E, F)`** of the pair of the cover with the pair of the
fibration: the retraction `cofibreURetract` on the total space and the base of a cone point on the
collar. -/
def uMap (F : Set E) [Nonempty E] [Nonempty ↥F] (e₀ : E) :
    Work.Cohomology.relChains (TopCat.of ↥(cofibreU (setIncl F))) (collarSet (setIncl F)) ⟶
      Work.Cohomology.relChains (TopCat.of E) F :=
  Work.Cohomology.relChainsMapOf (TopCat.of ↥(cofibreU (setIncl F))) (TopCat.of E)
    (collarSet (setIncl F)) F
    (TopCat.ofHom (cofibreURetract (setIncl F) e₀)) (TopCat.ofHom (collarBase (setIncl F)))
    (by ext z; exact cofibreURetract_eq_collarBase F e₀ z)

/-- **The comparison `(C,V) → (B,{b})`** induced by a map `c : C → B` which is constant on `V`. -/
def psiMap {E F B : Type} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
    (ι : C(F, E)) (c : C(cofibre ι, B)) (b : B)
    (hc : ∀ z : cofibre ι, z ∈ cofibreV ι → c z = b) :
    Work.Cohomology.relChains (TopCat.of (cofibre ι)) (cofibreV ι) ⟶
      Work.Cohomology.relChains (TopCat.of B) ({b} : Set B) :=
  Work.Cohomology.relChainsMapOf (TopCat.of (cofibre ι)) (TopCat.of B) (cofibreV ι) {b}
    (TopCat.ofHom c)
    (TopCat.ofHom ⟨fun _ : ↥(cofibreV ι) => ⟨b, rfl⟩, continuous_const⟩)
    (by ext z; exact hc z.1 z.2)

/-- The collapse is constant on the punctured cone. -/
theorem cofibreCollapse_eq_of_mem_cofibreV {E F B : Type} [TopologicalSpace E] [TopologicalSpace F]
    [TopologicalSpace B] (ι : C(F, E)) (p : C(E, B)) (b : B) (hp : ∀ x : F, p (ι x) = b) :
    ∀ z : cofibre ι, z ∈ cofibreV ι → cofibreCollapse ι p b hp z = b := by
  intro z hz
  obtain ⟨a, ha⟩ := Quotient.exists_rep z
  subst ha
  rcases a with x | y
  · exfalso
    rw [mem_cofibreV_iff] at hz
    have h0 : cofibreHeight ι (Quotient.mk'' (Sum.inl x)) = 0 := by
      show cofibreHeight ι (cofibreIncl ι x) = 0
      exact cofibreHeight_incl ι x
    rw [h0] at hz
    exact absurd hz (not_lt.mpr le_rfl)
  · exact cofibreCollapse_cone ι p b hp y

end

end Work.RatHurewicz.Cofibre
