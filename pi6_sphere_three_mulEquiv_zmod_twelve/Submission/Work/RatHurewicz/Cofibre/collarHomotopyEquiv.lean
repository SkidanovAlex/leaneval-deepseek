import Mathlib
import Submission.Work.RatHurewicz.Cofibre.Basic
import Submission.Work.RatHurewicz.Cofibre.Cover
import Submission.Work.RatHurewicz.Cofibre.Maps
import Submission.Work.RatHurewicz.Cofibre.Gluing
import Submission.Work.RatHurewicz.Cofibre.URetractEqv
import Submission.Work.RatHurewicz.Cofibre.RelClass
import Submission.Work.RatHurewicz.Cofibre.coneMidHomotopyEquiv

/-!
# The collar of the Blakers–Massey cover is homotopy equivalent to the fibre

`collarHomotopyEquiv` states `Nonempty (HomotopyEquiv ↥(cofibreU ι ∩ cofibreV ι) F)`.  The route:

* `midSet := {y : Cone F | 0 < coneHeight y ∧ coneHeight y < cofibreHalf}` is the *middle* of the
  cone; the middle of the cone on `F` is homotopy equivalent to `F` (this is the separate lemma
  `Work.RatHurewicz.Cofibre.coneMidHomotopyEquiv`);
* the map `↥midSet → ↥(cofibreU ι ∩ cofibreV ι)`, `y ↦ cofibreInclCone ι y`, is a homeomorphism,
  because the preimage of the collar under the quotient map is exactly `Sum.inr '' midSet`
  (`preimage_collar`) and on the middle the cone relation is trivial.

Everything here is the "descent along a restricted quotient map" pattern of
`Submission/Work/RatHurewicz/Cofibre/URetractEqv.lean`.
-/

namespace Work.RatHurewicz.Cofibre

open scoped Topology unitInterval

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

variable {E F : Type} [TopologicalSpace E] [TopologicalSpace F]

/-! ## The middle of the cone -/

/-- The middle slab of the cone on `F`: the cone points whose height lies in `(0, 1/2)`. -/
abbrev midSet : Set (Work.Stems.Cone F) :=
  {y | (0 : unitInterval) < coneHeight y ∧ coneHeight y < cofibreHalf}

theorem isOpen_midSet : IsOpen (midSet (F := F)) := by
  have h : midSet (F := F) = {y : Work.Stems.Cone F | (0 : unitInterval) < coneHeight y}
      ∩ {y : Work.Stems.Cone F | coneHeight y < cofibreHalf} := by
    ext y
    simp only [midSet, Set.mem_ofPred_eq, Set.mem_inter_iff]
  rw [h]
  exact (isOpen_coneHeight_gt_zero (F := F)).inter (isOpen_coneHeight_lt_half (F := F))

/-! ## The collar is the image of the middle of the cone -/

theorem preimage_collar (ι : C(F, E)) :
    (Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' (cofibreU ι ∩ cofibreV ι)
      = Sum.inr '' midSet (F := F) := by
  ext a
  constructor
  · intro ha
    rcases a with e | y
    · exfalso
      have hV : cofibreIncl ι e ∈ cofibreV ι := (Set.mem_inter_iff _ _ _).mp ha |>.2
      rw [mem_cofibreV_iff, cofibreHeight_incl] at hV
      exact absurd hV (not_lt.mpr le_rfl)
    · refine ⟨y, ?_, rfl⟩
      have hU : cofibreInclCone ι y ∈ cofibreU ι := (Set.mem_inter_iff _ _ _).mp ha |>.1
      have hV : cofibreInclCone ι y ∈ cofibreV ι := (Set.mem_inter_iff _ _ _).mp ha |>.2
      rw [mem_cofibreU_coneIncl_iff] at hU
      rw [mem_cofibreV_coneIncl_iff] at hV
      exact ⟨hV, hU⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hy1, hy2⟩ := hy
    exact Set.mem_inter ((mem_cofibreU_coneIncl_iff ι y).mpr hy2)
      ((mem_cofibreV_coneIncl_iff ι y).mpr hy1)

/-! ## The restricted quotient map of the collar -/

/-- The restricted quotient map `↥(q ⁻¹' collar) → ↥collar` of the cofibre quotient. -/
def collarQuot (ι : C(F, E)) :
    C(↥((Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' (cofibreU ι ∩ cofibreV ι)),
      ↥(cofibreU ι ∩ cofibreV ι)) where
  toFun p := ⟨Quotient.mk'' p.1, p.2⟩
  continuous_toFun := Continuous.subtype_mk
    (continuous_quotient_mk'.comp continuous_subtype_val) _

@[simp]
theorem collarQuot_mk (ι : C(F, E))
    (p : ↥((Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' (cofibreU ι ∩ cofibreV ι))) :
    collarQuot ι p = (⟨Quotient.mk'' p.1, p.2⟩ : ↥(cofibreU ι ∩ cofibreV ι)) := rfl

@[simp]
theorem collarQuot_apply (ι : C(F, E))
    (p : ↥((Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' (cofibreU ι ∩ cofibreV ι))) :
    (collarQuot ι p : cofibre ι) = Quotient.mk'' p.1 := rfl

theorem isQuotientMap_collarQuot (ι : C(F, E)) :
    Topology.IsQuotientMap (collarQuot ι) :=
  (isQuotientMap_quotient_mk' (s := Relation.EqvGen.setoid (cofibreRel ι))).restrictPreimage_isOpen
    ((isOpen_cofibreU ι).inter (isOpen_cofibreV ι))

/-! ## The projection of the collar to the middle of the cone -/

/-- The raw map `E ⊕ Cone F → Cone F` used to descend the inverse of the identification: on the
`Sum.inr` summand it is the identity, and the junk value is irrelevant (the preimage of the collar
meets only `Sum.inr '' midSet`). -/
def collarToMidFun [Nonempty F] : E ⊕ Work.Stems.Cone F → Work.Stems.Cone F :=
  Sum.elim (fun _ : E => Work.Stems.coneIncl (X := F) (Classical.ofNonempty : F)) (fun y => y)

@[simp]
theorem collarToMidFun_inr [Nonempty F] (y : Work.Stems.Cone F) :
    collarToMidFun (E := E) (F := F) (Sum.inr y) = y := rfl

theorem continuous_collarToMidFun [Nonempty F] :
    Continuous (collarToMidFun (E := E) (F := F)) :=
  (continuous_const (y := Work.Stems.coneIncl (X := F) (Classical.ofNonempty : F))).sumElim
    (continuous_id : Continuous fun y : Work.Stems.Cone F => y)

/-- The raw projection sends the preimage of the collar into the middle of the cone. -/
theorem collarToMidFun_mem (ι : C(F, E)) [Nonempty F] {a : E ⊕ Work.Stems.Cone F}
    (ha : a ∈ (Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' (cofibreU ι ∩ cofibreV ι)) :
    collarToMidFun (E := E) (F := F) a ∈ midSet (F := F) := by
  have hmem : a ∈ Sum.inr '' midSet (F := F) := by
    rw [← preimage_collar ι]; exact ha
  rcases hmem with ⟨y, hy, hya⟩
  rw [← hya]
  exact hy

/-- The (raw) projection of the preimage of the collar onto the middle of the cone. -/
def collarToMidRaw (ι : C(F, E)) [Nonempty F] :
    C(↥((Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' (cofibreU ι ∩ cofibreV ι)),
      ↥(midSet (F := F))) where
  toFun a := ⟨collarToMidFun (E := E) (F := F) a.1, collarToMidFun_mem ι a.2⟩
  continuous_toFun := Continuous.subtype_mk
    ((continuous_collarToMidFun (E := E) (F := F)).comp continuous_subtype_val)
    (fun a => collarToMidFun_mem ι a.2)

/-- The underlying cone point of the raw projection, on a representative. -/
theorem collarToMidRaw_inr (ι : C(F, E)) [Nonempty F] {a : E ⊕ Work.Stems.Cone F}
    (ha : a ∈ (Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' (cofibreU ι ∩ cofibreV ι))
    {y : Work.Stems.Cone F} (hya : a = Sum.inr y) (hy : y ∈ midSet (F := F)) :
    collarToMidRaw ι ⟨a, ha⟩ = ⟨y, hy⟩ := by
  apply Subtype.ext
  show collarToMidFun (E := E) (F := F) a = y
  rw [hya, collarToMidFun_inr]

/-- The raw projection is constant on the fibres of the restricted quotient map: two related points
of the preimage of the collar are `Sum.inr a`, `Sum.inr b` with `a = b` in `Cone F`. -/
theorem collarToMidRaw_factors (ι : C(F, E)) [Nonempty F] :
    Function.FactorsThrough (collarToMidRaw ι) (collarQuot ι) := by
  intro a b hab
  have hrel : Relation.EqvGen (cofibreRel ι) a.1 b.1 := by
    have h : (Quotient.mk'' a.1 : cofibre ι) = Quotient.mk'' b.1 := congrArg Subtype.val hab
    exact Quotient.exact h
  obtain ⟨y, hy, hya⟩ : a.1 ∈ Sum.inr '' midSet (F := F) := by
    rw [← preimage_collar ι]; exact a.2
  obtain ⟨y', hy', hy'a⟩ : b.1 ∈ Sum.inr '' midSet (F := F) := by
    rw [← preimage_collar ι]; exact b.2
  have hpos : (0 : unitInterval) < cofibreHeightFun ι a.1 := by
    rw [← hya]
    simpa only [cofibreHeightFun, Sum.elim_inr] using hy.1
  obtain ⟨p, q, hap, hbq, hpq⟩ := cofibreEqvGen_cone_of_pos ι hrel hpos
  have h1 : y = p := Sum.inr.inj (hya.trans hap)
  have h2 : y' = q := Sum.inr.inj (hy'a.trans hbq)
  rw [collarToMidRaw_inr ι a.2 hya.symm hy, collarToMidRaw_inr ι b.2 hy'a.symm hy']
  apply Subtype.ext
  show y = y'
  rw [h1, h2, hpq]

/-- **The projection of the collar onto the middle of the cone.** -/
def collarToMid (ι : C(F, E)) [Nonempty F] :
    C(↥(cofibreU ι ∩ cofibreV ι), ↥(midSet (F := F))) :=
  Topology.IsQuotientMap.lift (isQuotientMap_collarQuot ι) (collarToMidRaw ι)
    (collarToMidRaw_factors ι)

/-- The computation rule of `collarToMid` on a representative. -/
theorem collarToMid_mk (ι : C(F, E)) [Nonempty F] (a : E ⊕ Work.Stems.Cone F)
    (ha : a ∈ (Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' (cofibreU ι ∩ cofibreV ι)) :
    collarToMid ι ⟨Quotient.mk'' a, ha⟩ = collarToMidRaw ι ⟨a, ha⟩ := by
  have h := Topology.IsQuotientMap.lift_comp (isQuotientMap_collarQuot ι) (collarToMidRaw ι)
    (collarToMidRaw_factors ι)
  have h2 := congrFun (congrArg (fun k : C(↥((Quotient.mk'' : E ⊕ Work.Stems.Cone F →
      cofibre ι) ⁻¹' (cofibreU ι ∩ cofibreV ι)), ↥(midSet (F := F))) => (⇑k)) h)
    (⟨a, ha⟩ : ↥((Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' (cofibreU ι ∩ cofibreV ι)))
  have hpt : (⟨Quotient.mk'' a, ha⟩ : ↥(cofibreU ι ∩ cofibreV ι)) = collarQuot ι ⟨a, ha⟩ :=
    Subtype.ext rfl
  rw [hpt]
  exact h2

/-! ## The inclusion of the middle of the cone into the collar -/

/-- **The inclusion of the middle of the cone into the collar.** -/
def midToCollar (ι : C(F, E)) : C(↥(midSet (F := F)), ↥(cofibreU ι ∩ cofibreV ι)) where
  toFun y := ⟨cofibreInclCone ι y.1, Set.mem_inter
    ((mem_cofibreU_coneIncl_iff ι y.1).mpr y.2.2)
    ((mem_cofibreV_coneIncl_iff ι y.1).mpr y.2.1)⟩
  continuous_toFun := Continuous.subtype_mk
    ((cofibreInclCone ι).continuous.comp continuous_subtype_val)
    (fun y => Set.mem_inter ((mem_cofibreU_coneIncl_iff ι y.1).mpr y.2.2)
      ((mem_cofibreV_coneIncl_iff ι y.1).mpr y.2.1))

@[simp]
theorem midToCollar_apply (ι : C(F, E)) (y : ↥(midSet (F := F))) :
    (midToCollar ι y : cofibre ι) = cofibreInclCone ι y.1 := rfl

/-! ## The two round trips -/

theorem collarToMid_midToCollar (ι : C(F, E)) [Nonempty F] (y : ↥(midSet (F := F))) :
    collarToMid ι (midToCollar ι y) = y := by
  have hmem : (Sum.inr y.1 : E ⊕ Work.Stems.Cone F) ∈
      (Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' (cofibreU ι ∩ cofibreV ι) := by
    rw [preimage_collar ι]
    exact ⟨y.1, y.2, rfl⟩
  have hpt : midToCollar ι y =
      (⟨Quotient.mk'' (Sum.inr y.1), hmem⟩ : ↥(cofibreU ι ∩ cofibreV ι)) := Subtype.ext rfl
  rw [hpt, collarToMid_mk ι (Sum.inr y.1) hmem,
    collarToMidRaw_inr ι (a := Sum.inr y.1) hmem (y := y.1) rfl y.2]

theorem midToCollar_collarToMid (ι : C(F, E)) [Nonempty F] (z : ↥(cofibreU ι ∩ cofibreV ι)) :
    midToCollar ι (collarToMid ι z) = z := by
  obtain ⟨a, ha⟩ := (isQuotientMap_collarQuot ι).surjective z
  subst ha
  rw [collarQuot_mk, collarToMid_mk ι a.1 a.2]
  obtain ⟨y, hy, hya⟩ : a.1 ∈ Sum.inr '' midSet (F := F) := by
    rw [← preimage_collar ι]; exact a.2
  rw [collarToMidRaw_inr ι (a := a.1) a.2 (y := y) hya.symm hy]
  apply Subtype.ext
  show (cofibreInclCone ι y : cofibre ι) = Quotient.mk'' a.1
  rw [← hya]
  rfl

/-! ## The identification `collar ≃ₕ midSet` -/

/-- **The collar `cofibreU ι ∩ cofibreV ι` is the middle of the cone.** -/
def collarMidHomotopyEquiv (ι : C(F, E)) [Nonempty F] :
    ContinuousMap.HomotopyEquiv ↥(cofibreU ι ∩ cofibreV ι) ↥(midSet (F := F)) where
  toFun := collarToMid ι
  invFun := midToCollar ι
  left_inv := by
    have h : (midToCollar ι).comp (collarToMid ι) =
        ContinuousMap.id ↥(cofibreU ι ∩ cofibreV ι) := by
      apply ContinuousMap.ext
      intro z
      exact midToCollar_collarToMid ι z
    rw [h]
  right_inv := by
    have h : (collarToMid ι).comp (midToCollar ι) =
        ContinuousMap.id ↥(midSet (F := F)) := by
      apply ContinuousMap.ext
      intro y
      exact collarToMid_midToCollar ι y
    rw [h]

/-- **The collar `cofibreU ι ∩ cofibreV ι` is homotopy equivalent to `F`.**  For `ι : C(F, E)`, the
overlap `cofibreU ι ∩ cofibreV ι = {0 < h < 1/2}` of the two halves of the Blakers–Massey cover of
`cofibre ι = E ∪_F CF` is the *middle* part of the open cone, i.e. the image of
`midSet := {y : Cone F | 0 < coneHeight y ∧ coneHeight y < 1/2}`, and it is homotopy equivalent to
`F` (the cone point of height `1/4` gives a section, and the height is pushed to `1/4`).

Suggested route (the pattern of `Cofibre/URetractEqv.lean` and `Cofibre/ConeShrink.lean`, which both
build continuous maps *out of* a subtype of a quotient by descending `IsQuotientMap.lift` along a
restricted quotient map from a set of representatives where the coordinates exist):

* `coneMidMk : ↥(coneMk ⁻¹' midSet) → ↥midSet` is a quotient map
  (`Topology.IsQuotientMap.restrictPreimage_isOpen`), the map `p ↦ p.1.1` on `↥(coneMk ⁻¹' midSet)`
  is continuous and constant on its fibres (on the middle the cone relation is trivial), giving
  `coneMidProj : C(↥midSet, F)`; dually `coneMidSec : C(F, ↥midSet)`, `x ↦ [x, 1/4]`;
* `coneMidProj ∘ coneMidSec = id`, and `coneMidSec ∘ coneMidProj ~ id` by descending
  `(p, s) ↦ [p.1, (1-s)·p.2 + s/4]` (which stays in `(0,1/2)`);
* the collar itself is identified with `↥midSet` by `y ↦ ⟨cofibreInclCone ι y, _⟩`, whose inverse is
  obtained by descending along the restricted quotient map `↥(cofibreU ι ∩ cofibreV ι) ←
  ↥(Sum.inr '' midSet)` — the preimage of the collar is exactly `Sum.inr '' midSet` (the `Sum.inl`
  points have height `0`), so on the *larger* set `Sum.inl '' univ ∪ Sum.inr '' midSet` the map
  `Sum.elim junk coneMidProj` is continuous by `continuous_of_sumPiecewise`, and restricting to
  `Sum.inr '' midSet` gives the raw map whose well-definedness is that `EqvGen` between two middle
  points only relates middle points (on the middle the cone relation is trivial).-/
theorem collarHomotopyEquiv {E F : Type} [TopologicalSpace E] [TopologicalSpace F] [Nonempty F]
    (ι : C(F, E)) :
    Nonempty (ContinuousMap.HomotopyEquiv
      ↥(Work.RatHurewicz.cofibreU ι ∩ Work.RatHurewicz.cofibreV ι) F) := by
  obtain ⟨e⟩ := coneMidHomotopyEquiv (F := F)
  exact ⟨(collarMidHomotopyEquiv ι).trans e⟩

end

end Work.RatHurewicz.Cofibre
