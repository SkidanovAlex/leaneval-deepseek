import Mathlib
import Submission.Work.RatHurewicz.Cofibre.Basic

/-!
# The two-set open cover of the cofibre

For `ι : F → E` and `C = E ∪_F CF` (the cofibre, `Submission/Work/RatHurewicz/Cofibre/Basic.lean`),
this file produces the open cover used in the Blakers–Massey computation of `π_*(C)`:

* `Cone F` carries a **height** function `coneHeight : Cone F → I` (the `I`-coordinate, which is
  well defined because the collapsed set `F × {1}` has constant height `1`);
* `cofibreHeight : cofibre ι → I` is the height of the cone part, extended by `0` on the image of
  `E`;
* `cofibreU = {z | height z < 1/2}` is `E ∪ (lower half of the cone)` and
  `cofibreV = {z | 0 < height z}` is the punctured cone; both are open and `U ∪ V = C`.

The cone part of `U` is a genuine "collar": its points are the cone points of height `< 1/2`, which
form the subspace `F × (0,1/2)` of `Cone F`; this is recorded in `CoverCollar.lean`.

## Main names

* `coneHeight`, `cofibreHeight`, `continuous_cofibreHeight`;
* `cofibreU`, `cofibreV`, `isOpen_cofibreU`, `isOpen_cofibreV`, `cofibreU_union_cofibreV`;
* `cofibreHalf`.
-/

open scoped Topology unitInterval

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.RatHurewicz

noncomputable section

variable {E F : Type} [TopologicalSpace E] [TopologicalSpace F]

/-- The midpoint of the unit interval. -/
def cofibreHalf : unitInterval := ⟨1 / 2, by norm_num⟩

theorem cofibreHalf_pos : (0 : unitInterval) < cofibreHalf := by
  rw [← Subtype.coe_lt_coe]
  show (0 : ℝ) < 1 / 2
  norm_num

/-! ## Height on the cone -/

/-- The height function on the cone, `[x,t] ↦ t`.  Well defined because the defining relation of
`Cone F = (F × I)/(F × {1})` only identifies points with the same second coordinate. -/
def coneHeight : Work.Stems.Cone F → unitInterval :=
  Quotient.lift (s := Work.Stems.coneSetoid F) (fun p : F × unitInterval => p.2)
    (by
      intro a b h
      rcases h with h | ⟨h1, h2⟩
      · rw [h]
      · rw [h1, h2])

theorem continuous_coneHeight : Continuous (coneHeight (F := F)) :=
  continuous_snd.quotient_lift (s := Work.Stems.coneSetoid F)
    (fun a b h => by
      rcases h with h | ⟨h1, h2⟩
      · rw [h]
      · rw [h1, h2])

@[simp]
theorem coneHeight_coneIncl (x : F) : coneHeight (Work.Stems.coneIncl x) = 0 := rfl

@[simp]
theorem coneHeight_coneApex (x : F) : coneHeight (Work.Stems.coneApex x) = 1 := rfl

/-- The set of cone points of height `< 1/2` is open. -/
theorem isOpen_coneHeight_lt_half : IsOpen {y : Work.Stems.Cone F | coneHeight y < cofibreHalf} :=
  isOpen_lt continuous_coneHeight continuous_const

/-- The set of cone points of height `> 0` is open. -/
theorem isOpen_coneHeight_gt_zero : IsOpen {y : Work.Stems.Cone F | (0 : unitInterval) < coneHeight y} :=
  isOpen_lt continuous_const continuous_coneHeight

theorem coneHeight_mem_I (y : Work.Stems.Cone F) : (0 : ℝ) ≤ (coneHeight y : ℝ) :=
  (coneHeight y).2.1

/-! ## Height on the cofibre -/

/-- The height function on `E ⊕ CF`: `0` on `E` and the cone height on the cone part.  It
respects the gluing relation of the cofibre because the base of the cone has height `0`. -/
def cofibreHeightFun (ι : C(F, E)) : E ⊕ Work.Stems.Cone F → unitInterval :=
  Sum.elim (fun _ : E => 0) (coneHeight (F := F))

theorem continuous_cofibreHeightFun (ι : C(F, E)) : Continuous (cofibreHeightFun ι) :=
  continuous_const.sumElim continuous_coneHeight

theorem cofibreHeightFun_rel (ι : C(F, E)) :
    ∀ a b : E ⊕ Work.Stems.Cone F,
      Relation.EqvGen (cofibreRel ι) a b → cofibreHeightFun ι a = cofibreHeightFun ι b := by
  have hgen : ∀ a b : E ⊕ Work.Stems.Cone F, cofibreRel ι a b →
      cofibreHeightFun ι a = cofibreHeightFun ι b := by
    rintro a b ⟨x, rfl, rfl⟩
    show (0 : unitInterval) = coneHeight (Work.Stems.coneIncl x)
    rw [coneHeight_coneIncl]
  intro a b hab
  induction hab with
  | rel x y h => exact hgen x y h
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- **The height function on the cofibre** `E ∪_F CF`. -/
def cofibreHeight (ι : C(F, E)) : cofibre ι → unitInterval :=
  Quotient.lift (s := Relation.EqvGen.setoid (cofibreRel ι)) (cofibreHeightFun ι)
    (cofibreHeightFun_rel ι)

theorem continuous_cofibreHeight (ι : C(F, E)) : Continuous (cofibreHeight ι) :=
  (continuous_cofibreHeightFun ι).quotient_lift
    (s := Relation.EqvGen.setoid (cofibreRel ι)) (cofibreHeightFun_rel ι)

@[simp]
theorem cofibreHeight_incl (ι : C(F, E)) (x : E) :
    cofibreHeight ι (cofibreIncl ι x) = 0 := by
  show Quotient.lift (s := Relation.EqvGen.setoid (cofibreRel ι)) (cofibreHeightFun ι)
    (cofibreHeightFun_rel ι) (Quotient.mk'' (Sum.inl x)) = 0
  rw [Quotient.lift_mk]
  rfl

@[simp]
theorem cofibreHeight_cone (ι : C(F, E)) (y : Work.Stems.Cone F) :
    cofibreHeight ι (cofibreInclCone ι y) = coneHeight y := by
  show Quotient.lift (s := Relation.EqvGen.setoid (cofibreRel ι)) (cofibreHeightFun ι)
    (cofibreHeightFun_rel ι) (Quotient.mk'' (Sum.inr y)) = coneHeight y
  rw [Quotient.lift_mk]
  rfl

/-! ## The cover -/

/-- The "lower" piece of the cover: `E` together with the cone points of height `< 1/2`. -/
def cofibreU (ι : C(F, E)) : Set (cofibre ι) := {z | cofibreHeight ι z < cofibreHalf}

/-- The "upper" piece of the cover: the punctured cone. -/
def cofibreV (ι : C(F, E)) : Set (cofibre ι) := {z | (0 : unitInterval) < cofibreHeight ι z}

theorem isOpen_cofibreU (ι : C(F, E)) : IsOpen (cofibreU ι) :=
  isOpen_lt (continuous_cofibreHeight ι) continuous_const

theorem isOpen_cofibreV (ι : C(F, E)) : IsOpen (cofibreV ι) :=
  isOpen_lt continuous_const (continuous_cofibreHeight ι)

theorem cofibreU_union_cofibreV (ι : C(F, E)) : cofibreU ι ∪ cofibreV ι = Set.univ := by
  ext z
  constructor
  · intro _; exact Set.mem_univ _
  · intro _
    rcases eq_or_lt_of_le ((cofibreHeight ι z).2.1) with h | h
    · left
      show cofibreHeight ι z < cofibreHalf
      have hz : cofibreHeight ι z = 0 := Subtype.ext h.symm
      rw [hz]
      exact cofibreHalf_pos
    · exact Or.inr h

@[simp]
theorem mem_cofibreU_iff (ι : C(F, E)) (z : cofibre ι) :
    z ∈ cofibreU ι ↔ cofibreHeight ι z < cofibreHalf := Iff.rfl

@[simp]
theorem mem_cofibreV_iff (ι : C(F, E)) (z : cofibre ι) :
    z ∈ cofibreV ι ↔ (0 : unitInterval) < cofibreHeight ι z := Iff.rfl

theorem cofibreIncl_mem_cofibreU (ι : C(F, E)) (x : E) : cofibreIncl ι x ∈ cofibreU ι := by
  rw [mem_cofibreU_iff, cofibreHeight_incl]
  exact cofibreHalf_pos

theorem mem_cofibreU_coneIncl_iff (ι : C(F, E)) (y : Work.Stems.Cone F) :
    cofibreInclCone ι y ∈ cofibreU ι ↔ coneHeight y < cofibreHalf := by
  rw [mem_cofibreU_iff, cofibreHeight_cone]

theorem mem_cofibreV_coneIncl_iff (ι : C(F, E)) (y : Work.Stems.Cone F) :
    cofibreInclCone ι y ∈ cofibreV ι ↔ (0 : unitInterval) < coneHeight y := by
  rw [mem_cofibreV_iff, cofibreHeight_cone]

theorem cofibreIncl_not_mem_cofibreV (ι : C(F, E)) (x : E) :
    cofibreIncl ι x ∉ cofibreV ι := by
  rw [mem_cofibreV_iff, cofibreHeight_incl]
  exact not_lt.mpr le_rfl

/-- The overlap of the two pieces: the cone points of height in `(0, 1/2)`. -/
theorem mem_cofibreU_inter_cofibreV_iff (ι : C(F, E)) (z : cofibre ι) :
    z ∈ cofibreU ι ∩ cofibreV ι ↔
      (0 : unitInterval) < cofibreHeight ι z ∧ cofibreHeight ι z < cofibreHalf := by
  rw [Set.mem_inter_iff, mem_cofibreU_iff, mem_cofibreV_iff]
  exact and_comm

end

end Work.RatHurewicz
