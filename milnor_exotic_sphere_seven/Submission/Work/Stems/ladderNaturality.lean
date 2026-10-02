import Mathlib
import Submission.Work.Serre.thomCylLadderEps
import Submission.Work.Serre.thomCylLadder
import Submission.Work.StemsB.AToolsR
import Submission.Work.Serre.DiscPair.fibreValuePropagation
import Submission.Work.Serre.TripleCohDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Naturality of the `G`-square of the cellular-step ladder

This file proves `Work.Stems.ladderNaturality`, the commutativity of the square

```
H^k(Γ', S) --TQ--> H^{k+r+1}(new, A)
   |                    ^
 baseG                  | totG
   v                    |
H^k(S) ----TP------> H^{k+r+1}(cyl q, A)
```

of the ladder of the CW-model Thom case: the composition of the restriction to the old part with
the cup map of the induction-hypothesis class `U_S` agrees with the cup map of the extension class
`U` followed by the restriction to `(new, A)`.

The proof is the naturality of the mixed cup product (`Work.StemsB.mixedCupC_pairNaturalR`) applied
to the map `ladNat_iotaBig : cyl (q|_S) → cyl q`, which identifies the mapping cylinder of the
restricted fibration `q|_S` with the part of `cyl q` lying over `S`.  The two ingredients are

* `oldPartIso.hom` is the pullback along `ladNat_iota : cyl (q|_S) → (new, A)` and the composite
  `totG ≫ oldPartIso.hom` is the pullback along `ladNat_iotaBig` (both by `relCohMap_compA`), and
* the retraction of `cyl q` agrees with the retraction of `cyl (q|_S)` under this identification
  (`Work.Serre.DiscPair.cylRetract_cylPreimageHomeo`), which identifies the two pullbacks of the
  base class.

Consequently both sides are the value on the image of `x` under the same element of
`H^{k+r+1}(cyl (q|_S), range (cylIncl (q|_S)))`.
-/

open CategoryTheory CategoryTheory.Limits

set_option maxHeartbeats 4000000

namespace Work.Stems

noncomputable section

/-! ## Notation for the sets and maps of the square -/

abbrev ladNat_Sset (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)) :
    Set (Work.RatHurewicz.attachCells (D - 2) Γ ι f) := Work.Serre.ladS D Γ ι f

abbrev ladNat_New (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)) : Set (Work.Serre.cyl q) :=
  Work.Serre.ladNew D ι f q

abbrev ladNat_Pre (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)) : Set (Work.Serre.cyl q) :=
  (Work.Serre.cylRetract q) ⁻¹' ladNat_Sset D Γ ι f

abbrev ladNat_Aq {X : Type} [TopologicalSpace X] {Γ : Type} [TopologicalSpace Γ]
    (q : C(X, Γ)) : Set (Work.Serre.cyl q) := Set.range (Work.Serre.cylIncl q)

abbrev ladNat_CylS (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)) : Type :=
  Work.Serre.cyl (Work.Serre.restrictFibre q (ladNat_Sset D Γ ι f))

abbrev ladNat_RS (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)) : Set (ladNat_CylS D Γ ι f q) :=
  Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q (ladNat_Sset D Γ ι f)))

abbrev ladNat_Aold (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)) : Set ↥(ladNat_Pre D Γ ι f q) :=
  {x | (x : Work.Serre.cyl q) ∈ ladNat_Aq q}

abbrev ladNat_AB (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)) : Set ↥(ladNat_New D Γ ι f q) :=
  {x | (x : Work.Serre.cyl q) ∈ ladNat_Aq q}

abbrev ladNat_inclS (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)) :
    C(↥(ladNat_Sset D Γ ι f), Work.RatHurewicz.attachCells (D - 2) Γ ι f) :=
  ⟨Subtype.val, continuous_subtype_val⟩

abbrev ladNat_inclB (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)) :
    C(↥(ladNat_New D Γ ι f q), Work.Serre.cyl q) := ⟨Subtype.val, continuous_subtype_val⟩

abbrev ladNat_iota (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)) (hh : IsClosed (ladNat_Sset D Γ ι f)) :
    C(ladNat_CylS D Γ ι f q, ↥(ladNat_New D Γ ι f q)) :=
  (Work.Serre.oldInclToNew q (ladNat_Sset D Γ ι f)).comp (Work.Serre.preimageMap q (ladNat_Sset D Γ ι f) hh)

abbrev ladNat_iotaBig (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)) (hh : IsClosed (ladNat_Sset D Γ ι f)) :
    C(ladNat_CylS D Γ ι f q, Work.Serre.cyl q) :=
  (ladNat_inclB D Γ ι f q).comp (ladNat_iota D Γ ι f q hh)

variable {D : ℕ} {Γ : Type} [TopologicalSpace Γ] {ι : Type}
  {f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)} {X : Type} [TopologicalSpace X]
  {q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)}

/-! ## The elementary identifications -/

/-- The membership needed for `ladNat_iota`. -/
theorem ladNat_hmemIota (hh : IsClosed (ladNat_Sset D Γ ι f)) :
    ∀ x ∈ ladNat_RS D Γ ι f q, (ladNat_iota D Γ ι f q hh) x ∈ ladNat_AB D Γ ι f q :=
  fun x hx => (Work.Serre.DiscPair.cylPreimageHomeo_range q (ladNat_Sset D Γ ι f) hh x).mpr hx

/-- The membership needed for `ladNat_iotaBig`. -/
theorem ladNat_hmemBig (hh : IsClosed (ladNat_Sset D Γ ι f)) :
    ∀ x ∈ ladNat_RS D Γ ι f q, (ladNat_iotaBig D Γ ι f q hh) x ∈ ladNat_Aq q :=
  fun x hx => (Work.Serre.DiscPair.cylPreimageHomeo_range q (ladNat_Sset D Γ ι f) hh x).mpr hx

/-- `baseG` is the pullback along the inclusion of the old part. -/
theorem ladNat_baseG_eq (k : ℕ) :
    Work.Serre.baseG D Γ ι f k = Work.Thom.CohMap (ladNat_inclS D Γ ι f) ℚ k := rfl

/-- `totG` is the pullback along the inclusion of `new` into the mapping cylinder. -/
theorem ladNat_totG_eq (k : ℕ) :
    Work.Serre.totG D ι f q k
      = Work.Thom.relCohMap (ladNat_inclB D Γ ι f q) (ladNat_AB D Γ ι f q) (ladNat_Aq q)
          (fun x hx => hx) ℚ k := rfl

/-- **`oldPartIso.hom` is the pullback along `ladNat_iota`.** -/
theorem ladNat_oldPartIso_hom (hh : IsClosed (ladNat_Sset D Γ ι f)) (k : ℕ) :
    (Work.Serre.oldPartIso q (ladNat_Sset D Γ ι f) hh k).hom
      = Work.Thom.relCohMap (ladNat_iota D Γ ι f q hh) (ladNat_RS D Γ ι f q) (ladNat_AB D Γ ι f q)
          (ladNat_hmemIota (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) (q := q) hh) ℚ k := by
  rw [show (Work.Serre.oldPartIso q (ladNat_Sset D Γ ι f) hh k).hom
        = (Work.Serre.oldInclIso q (ladNat_Sset D Γ ι f) hh k).hom
          ≫ (Work.Serre.preimageIso q (ladNat_Sset D Γ ι f) hh k).hom from rfl]
  rw [show (Work.Serre.oldInclIso q (ladNat_Sset D Γ ι f) hh k).hom
        = Work.Thom.relCohMap (Work.Serre.oldInclToNew q (ladNat_Sset D Γ ι f))
            (ladNat_Aold D Γ ι f q) (ladNat_AB D Γ ι f q) (fun _ hx => hx) ℚ k from rfl]
  rw [show (Work.Serre.preimageIso q (ladNat_Sset D Γ ι f) hh k).hom
        = Work.Thom.relCohMap (Work.Serre.preimageMap q (ladNat_Sset D Γ ι f) hh)
            (ladNat_RS D Γ ι f q) (ladNat_Aold D Γ ι f q)
            (ladNat_hmemIota (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) (q := q) hh) ℚ k from rfl]
  exact Work.Thom.relCohMap_compA (ladNat_RS D Γ ι f q) (ladNat_Aold D Γ ι f q) (ladNat_AB D Γ ι f q)
    (Work.Serre.preimageMap q (ladNat_Sset D Γ ι f) hh)
    (Work.Serre.oldInclToNew q (ladNat_Sset D Γ ι f)) _ _ _ ℚ k

/-- **The composite `totG ≫ oldPartIso.hom` is the pullback along `ladNat_iotaBig`.** -/
theorem ladNat_totG_comp_oldPartIso_hom (hh : IsClosed (ladNat_Sset D Γ ι f)) (k : ℕ) :
    Work.Serre.totG D ι f q k ≫ (Work.Serre.oldPartIso q (ladNat_Sset D Γ ι f) hh k).hom
      = Work.Thom.relCohMap (ladNat_iotaBig D Γ ι f q hh) (ladNat_RS D Γ ι f q) (ladNat_Aq q)
          (ladNat_hmemBig (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) (q := q) hh) ℚ k := by
  rw [ladNat_totG_eq (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) (q := q) k,
    ladNat_oldPartIso_hom (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) (q := q) hh k]
  rw [Work.Thom.relCohMap_compA (ladNat_RS D Γ ι f q) (ladNat_AB D Γ ι f q) (ladNat_Aq q)
    (ladNat_iota D Γ ι f q hh) (ladNat_inclB D Γ ι f q) _ _ _ ℚ k]

/-- The elementwise form of `ladNat_totG_comp_oldPartIso_hom`. -/
theorem ladNat_totG_comp_oldPartIso_hom_apply (hh : IsClosed (ladNat_Sset D Γ ι f)) (k : ℕ)
    (z : Work.Thom.RelCoh ℚ k (Work.Serre.cyl q) (ladNat_Aq q)) :
    ModuleCat.Hom.hom (Work.Serre.oldPartIso q (ladNat_Sset D Γ ι f) hh k).hom
        (ModuleCat.Hom.hom (Work.Serre.totG D ι f q k) z)
      = ModuleCat.Hom.hom (Work.Thom.relCohMap (ladNat_iotaBig D Γ ι f q hh) (ladNat_RS D Γ ι f q) (ladNat_Aq q)
          (ladNat_hmemBig (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) (q := q) hh) ℚ k) z :=
  congrArg (fun m => ModuleCat.Hom.hom m z)
    (ladNat_totG_comp_oldPartIso_hom (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) (q := q) hh k)

/-- **The retraction of `cyl q` and the retraction of `cyl (q|_S)` agree** under the identification
of the cylinder of the restricted fibration with the part of `cyl q` over `S`. -/
theorem ladNat_cylRetract_comp_iotaBig (hh : IsClosed (ladNat_Sset D Γ ι f)) :
    (Work.Serre.cylRetract q).comp (ladNat_iotaBig D Γ ι f q hh)
      = (ladNat_inclS D Γ ι f).comp (Work.Serre.cylRetract (Work.Serre.restrictFibre q (ladNat_Sset D Γ ι f))) := by
  ext y
  show Work.Serre.cylRetract q ((Work.Serre.preimageMap q (ladNat_Sset D Γ ι f) hh) y : Work.Serre.cyl q) = _
  exact Work.Serre.DiscPair.cylRetract_cylPreimageHomeo q (ladNat_Sset D Γ ι f) hh y

/-- **The pullback of the extension class `U` along `ladNat_iotaBig` is the old class `U_S`.** -/
theorem ladNat_relCohMap_iotaBig_apply (hh : IsClosed (ladNat_Sset D Γ ι f)) (r : ℕ)
    (U_S : Work.Thom.RelCoh ℚ (r + 1) (ladNat_CylS D Γ ι f q) (ladNat_RS D Γ ι f q))
    (U : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) (ladNat_Aq q))
    (hU : (HomologicalComplex.homologyMap (Work.Serre.tripleRestr ℚ (TopCat.of (Work.Serre.cyl q))
        (ladNat_Aq q) (ladNat_New D Γ ι f q) (fun _ hx => Or.inr hx)) (r + 1)).hom U
      = Work.Serre.uNew r q (ladNat_Sset D Γ ι f) hh U_S) :
    ModuleCat.Hom.hom (Work.Thom.relCohMap (ladNat_iotaBig D Γ ι f q hh) (ladNat_RS D Γ ι f q) (ladNat_Aq q)
      (ladNat_hmemBig (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) (q := q) hh) ℚ (r + 1)) U = U_S := by
  have h1 : Work.Thom.relCohMap (ladNat_iotaBig D Γ ι f q hh) (ladNat_RS D Γ ι f q) (ladNat_Aq q)
      (ladNat_hmemBig (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) (q := q) hh) ℚ (r + 1)
      = Work.Thom.relCohMap (ladNat_inclB D Γ ι f q) (ladNat_AB D Γ ι f q) (ladNat_Aq q) (fun x hx => hx) ℚ (r + 1)
        ≫ Work.Thom.relCohMap (ladNat_iota D Γ ι f q hh) (ladNat_RS D Γ ι f q) (ladNat_AB D Γ ι f q)
          (ladNat_hmemIota (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) (q := q) hh) ℚ (r + 1) :=
    (Work.Thom.relCohMap_compA (ladNat_RS D Γ ι f q) (ladNat_AB D Γ ι f q) (ladNat_Aq q)
      (ladNat_iota D Γ ι f q hh) (ladNat_inclB D Γ ι f q) _ _ _ ℚ (r + 1)).symm
  rw [h1]
  have h2 : ModuleCat.Hom.hom (Work.Thom.relCohMap (ladNat_inclB D Γ ι f q) (ladNat_AB D Γ ι f q) (ladNat_Aq q)
      (fun x hx => hx) ℚ (r + 1)) U
      = ModuleCat.Hom.hom (Work.Serre.oldPartIso q (ladNat_Sset D Γ ι f) hh (r + 1)).inv U_S := by
    rw [show ModuleCat.Hom.hom (Work.Serre.oldPartIso q (ladNat_Sset D Γ ι f) hh (r + 1)).inv U_S
        = Work.Serre.uNew r q (ladNat_Sset D Γ ι f) hh U_S from rfl]
    exact hU
  show ModuleCat.Hom.hom (Work.Thom.relCohMap (ladNat_iota D Γ ι f q hh) (ladNat_RS D Γ ι f q) (ladNat_AB D Γ ι f q)
      (ladNat_hmemIota (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) (q := q) hh) ℚ (r + 1))
      (ModuleCat.Hom.hom (Work.Thom.relCohMap (ladNat_inclB D Γ ι f q) (ladNat_AB D Γ ι f q) (ladNat_Aq q)
        (fun x hx => hx) ℚ (r + 1)) U) = U_S
  rw [h2]
  rw [show Work.Thom.relCohMap (ladNat_iota D Γ ι f q hh) (ladNat_RS D Γ ι f q) (ladNat_AB D Γ ι f q)
      (ladNat_hmemIota (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) (q := q) hh) ℚ (r + 1)
      = (Work.Serre.oldPartIso q (ladNat_Sset D Γ ι f) hh (r + 1)).hom from
    (ladNat_oldPartIso_hom (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) (q := q) hh (r + 1)).symm]
  exact CategoryTheory.Iso.inv_hom_id_apply
    (Work.Serre.oldPartIso q (ladNat_Sset D Γ ι f) hh (r + 1)) U_S

/-- **The pullback along `ladNat_iotaBig` of the retraction of `cyl q` is the retraction of `cyl (q|_S)`. -/
theorem ladNat_CohMap_step (hh : IsClosed (ladNat_Sset D Γ ι f)) (k : ℕ)
    (x : Work.Thom.Coh ℚ k (Work.RatHurewicz.attachCells (D - 2) Γ ι f)) :
    ModuleCat.Hom.hom (Work.Thom.CohMap (ladNat_iotaBig D Γ ι f q hh) ℚ k)
        (ModuleCat.Hom.hom (Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ k) x)
      = ModuleCat.Hom.hom
          (Work.Thom.CohMap (Work.Serre.cylRetract (Work.Serre.restrictFibre q (ladNat_Sset D Γ ι f))) ℚ k)
          (ModuleCat.Hom.hom (Work.Thom.CohMap (ladNat_inclS D Γ ι f) ℚ k) x) := by
  have h1 : ModuleCat.Hom.hom (Work.Thom.CohMap (ladNat_iotaBig D Γ ι f q hh) ℚ k)
        (ModuleCat.Hom.hom (Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ k) x)
      = ModuleCat.Hom.hom (Work.Thom.CohMap
          ((Work.Serre.cylRetract q).comp (ladNat_iotaBig D Γ ι f q hh)) ℚ k) x := by
    rw [show Work.Thom.CohMap ((Work.Serre.cylRetract q).comp (ladNat_iotaBig D Γ ι f q hh)) ℚ k
        = Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ k
          ≫ Work.Thom.CohMap (ladNat_iotaBig D Γ ι f q hh) ℚ k
        from Work.Thom.CohMap_comp (ladNat_iotaBig D Γ ι f q hh) (Work.Serre.cylRetract q) ℚ k]
    rfl
  have h2 : ModuleCat.Hom.hom
        (Work.Thom.CohMap (Work.Serre.cylRetract (Work.Serre.restrictFibre q (ladNat_Sset D Γ ι f))) ℚ k)
        (ModuleCat.Hom.hom (Work.Thom.CohMap (ladNat_inclS D Γ ι f) ℚ k) x)
      = ModuleCat.Hom.hom (Work.Thom.CohMap
          ((ladNat_inclS D Γ ι f).comp (Work.Serre.cylRetract (Work.Serre.restrictFibre q (ladNat_Sset D Γ ι f)))) ℚ k) x := by
    rw [show Work.Thom.CohMap
          ((ladNat_inclS D Γ ι f).comp (Work.Serre.cylRetract (Work.Serre.restrictFibre q (ladNat_Sset D Γ ι f)))) ℚ k
        = Work.Thom.CohMap (ladNat_inclS D Γ ι f) ℚ k
          ≫ Work.Thom.CohMap (Work.Serre.cylRetract (Work.Serre.restrictFibre q (ladNat_Sset D Γ ι f))) ℚ k
        from Work.Thom.CohMap_comp (Work.Serre.cylRetract (Work.Serre.restrictFibre q (ladNat_Sset D Γ ι f)))
          (ladNat_inclS D Γ ι f) ℚ k]
    rfl
  rw [h1, h2, ladNat_cylRetract_comp_iotaBig (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) (q := q) hh]

theorem ladderNaturality (r D : ℕ) (hD : 2 ≤ D) {Γ : Type} [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (U_S : Work.Thom.RelCoh ℚ (r + 1)
      (Work.Serre.cyl (Work.Serre.restrictFibre q (Work.Serre.ladS D Γ ι f)))
      (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q (Work.Serre.ladS D Γ ι f)))))
    (U : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) (Set.range (Work.Serre.cylIncl q)))
    (hU : (HomologicalComplex.homologyMap (Work.Serre.tripleRestr ℚ (TopCat.of (Work.Serre.cyl q))
        (Set.range (Work.Serre.cylIncl q))
        ((Work.Serre.cylRetract q) ⁻¹' (Work.Serre.ladS D Γ ι f) ∪
          Set.range (Work.Serre.cylIncl q)) (fun _ hx => Or.inr hx)) (r + 1)).hom U
      = Work.Serre.uNew r q (Work.Serre.ladS D Γ ι f)
          Work.RatHurewicz.isClosed_range_attachIncl U_S)
    (k : ℕ) :
    CategoryTheory.CategoryStruct.comp (Work.Serre.baseG D Γ ι f k)
        (Work.Serre.TQ r q (Work.Serre.ladS D Γ ι f)
          Work.RatHurewicz.isClosed_range_attachIncl U_S k)
      = CategoryTheory.CategoryStruct.comp (Work.Serre.TP r q U k)
        (Work.Serre.totG D ι f q (k + (r + 1))) := by
  have hh : IsClosed (ladNat_Sset D Γ ι f) := Work.RatHurewicz.isClosed_range_attachIncl
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  -- the two sides are now `TQ k (baseG k x)` and `totG (TP k x)`
  rw [show ModuleCat.Hom.hom (Work.Serre.baseG D Γ ι f k) x
      = ModuleCat.Hom.hom (Work.Thom.CohMap (ladNat_inclS D Γ ι f) ℚ k) x from rfl]
  -- the common value of the two sides
  have hL : ModuleCat.Hom.hom (Work.Serre.TQ r q (ladNat_Sset D Γ ι f) hh U_S k)
        (ModuleCat.Hom.hom (Work.Thom.CohMap (ladNat_inclS D Γ ι f) ℚ k) x)
      = ModuleCat.Hom.hom (Work.Serre.oldPartIso q (ladNat_Sset D Γ ι f) hh (k + (r + 1))).inv
          ((Work.Thom.mixedCupC ℚ (ladNat_RS D Γ ι f q) k (r + 1))
            (ModuleCat.Hom.hom (Work.Thom.CohMap
              (Work.Serre.cylRetract (Work.Serre.restrictFibre q (ladNat_Sset D Γ ι f))) ℚ k)
              (ModuleCat.Hom.hom (Work.Thom.CohMap (ladNat_inclS D Γ ι f) ℚ k) x)) U_S) := by
    rw [show Work.Serre.TQ r q (ladNat_Sset D Γ ι f) hh U_S k
        = Work.Serre.oldCupMap r q (ladNat_Sset D Γ ι f) U_S k ≫
            (Work.Serre.oldPartIso q (ladNat_Sset D Γ ι f) hh (k + (r + 1))).inv from rfl]
    rw [show Work.Serre.oldCupMap r q (ladNat_Sset D Γ ι f) U_S k
        = ModuleCat.ofHom (((Work.Thom.mixedCupC ℚ (ladNat_RS D Γ ι f q) k (r + 1)).flip U_S) ∘ₗ
            (Work.Thom.CohMap (Work.Serre.cylRetract (Work.Serre.restrictFibre q (ladNat_Sset D Γ ι f)))
              ℚ k).hom) from rfl]
    rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearMap.flip_apply]
  have hR : ModuleCat.Hom.hom (Work.Serre.totG D ι f q (k + (r + 1)))
        (ModuleCat.Hom.hom (Work.Serre.TP r q U k) x)
      = ModuleCat.Hom.hom (Work.Serre.oldPartIso q (ladNat_Sset D Γ ι f) hh (k + (r + 1))).inv
          ((Work.Thom.mixedCupC ℚ (ladNat_RS D Γ ι f q) k (r + 1))
            (ModuleCat.Hom.hom (Work.Thom.CohMap
              (Work.Serre.cylRetract (Work.Serre.restrictFibre q (ladNat_Sset D Γ ι f))) ℚ k)
              (ModuleCat.Hom.hom (Work.Thom.CohMap (ladNat_inclS D Γ ι f) ℚ k) x)) U_S) := by
    -- the formula for `TP`
    rw [show ModuleCat.Hom.hom (Work.Serre.TP r q U k) x
        = (Work.Thom.mixedCupC ℚ (ladNat_Aq q) k (r + 1))
            (ModuleCat.Hom.hom (Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ k) x) U from by
      rw [show Work.Serre.TP r q U k
          = ModuleCat.ofHom (((Work.Thom.mixedCupC ℚ (ladNat_Aq q) k (r + 1)).flip U) ∘ₗ
              (Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ k).hom) from rfl]
      rw [ModuleCat.hom_ofHom, LinearMap.comp_apply, LinearMap.flip_apply]]
    -- `e.hom` after `totG`
    rw [← CategoryTheory.Iso.hom_inv_id_apply
      (Work.Serre.oldPartIso q (ladNat_Sset D Γ ι f) hh (k + (r + 1)))
      (ModuleCat.Hom.hom (Work.Serre.totG D ι f q (k + (r + 1)))
        ((Work.Thom.mixedCupC ℚ (ladNat_Aq q) k (r + 1))
          (ModuleCat.Hom.hom (Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ k) x) U))]
    rw [ladNat_totG_comp_oldPartIso_hom_apply (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X)
      (q := q) hh (k + (r + 1))]
    -- naturality of the mixed cup product along `ladNat_iotaBig`
    rw [Work.StemsB.mixedCupC_pairNaturalR ℚ (ladNat_iotaBig D Γ ι f q hh) (ladNat_RS D Γ ι f q) (ladNat_Aq q)
      (ladNat_hmemBig (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) (q := q) hh) k (r + 1)
      (ModuleCat.Hom.hom (Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ k) x) U]
    -- the pullback of the retraction and the class
    rw [ladNat_CohMap_step (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) (q := q) hh k x,
      ladNat_relCohMap_iotaBig_apply (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) (q := q)
        hh r U_S U hU]
  exact hL.trans hR.symm

end

end Work.Stems
