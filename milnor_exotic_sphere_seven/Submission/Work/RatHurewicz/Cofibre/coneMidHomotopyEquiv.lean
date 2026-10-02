import Mathlib
import Submission.Work.RatHurewicz.Cofibre.Maps
import Submission.Work.RatHurewicz.Cofibre.Cover

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The middle slab of the cone on `F` is homotopy equivalent to `F`

`{y : Cone F | 0 < coneHeight y ∧ coneHeight y < cofibreHalf}` is the middle part of the cone
(no apex, no base).  The projection to the first coordinate `[x,t] ↦ x` is well defined and
continuous because on the middle the cone relation is trivial; the section `x ↦ [x, 1/4]` is a
right inverse of it, and `(x,t,s) ↦ [x, (1-s)*t + s/4]` is the homotopy `id ~ sec ∘ proj`.

The construction follows the "descent along a restricted quotient map" pattern of
`Submission/Work/RatHurewicz/Cofibre/ConeShrink.lean`.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz.Cofibre

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

variable {F : Type} [TopologicalSpace F]

/-! ## The middle of the cone -/

/-- The middle slab of the cone on `F`: the cone points whose height lies in `(0, 1/2)`. -/
abbrev coneMidSet : Set (Work.Stems.Cone F) :=
  {y | (0 : unitInterval) < Work.RatHurewicz.coneHeight y ∧
    Work.RatHurewicz.coneHeight y < Work.RatHurewicz.cofibreHalf}

theorem isOpen_coneMidSet : IsOpen (coneMidSet (F := F)) := by
  have h1 : IsOpen {y : Work.Stems.Cone F | (0 : unitInterval) < coneHeight y} :=
    isOpen_lt continuous_const continuous_coneHeight
  have h2 : IsOpen {y : Work.Stems.Cone F | coneHeight y < cofibreHalf} :=
    isOpen_lt continuous_coneHeight continuous_const
  rw [show coneMidSet (F := F) =
      {y : Work.Stems.Cone F | (0 : unitInterval) < coneHeight y} ∩
      {y : Work.Stems.Cone F | coneHeight y < cofibreHalf} from rfl]
  exact h1.inter h2

/-! ## The restricted quotient map of the middle -/

/-- The restricted quotient map `↥(coneMk ⁻¹' midSet) → ↥midSet`. -/
def coneMidMk :
    C(↥((coneMk (F := F)) ⁻¹' coneMidSet (F := F)), ↥(coneMidSet (F := F))) where
  toFun p := ⟨coneMk (F := F) p.1, p.2⟩
  continuous_toFun := Continuous.subtype_mk
    (continuous_quotient_mk'.comp continuous_subtype_val) _

theorem isQuotientMap_coneMidMk : Topology.IsQuotientMap (coneMidMk (F := F)) :=
  (isQuotientMap_quotient_mk' (s := Work.Stems.coneSetoid F)).restrictPreimage_isOpen
    (isOpen_coneMidSet (F := F))

/-! ## The projection to the base -/

/-- The raw projection `p ↦ p.1.1` on the preimage of the middle. -/
def coneMidProjFun : C(↥((coneMk (F := F)) ⁻¹' coneMidSet (F := F)), F) where
  toFun p := p.1.1
  continuous_toFun := continuous_fst.comp continuous_subtype_val

/-- The raw projection is constant on the fibres of the restricted quotient map: on the middle the
cone relation is trivial. -/
theorem coneMidProjFun_factors :
    Function.FactorsThrough (coneMidProjFun (F := F)) (coneMidMk (F := F)) := by
  intro a b hab
  have h : coneMk (F := F) a.1 = coneMk (F := F) b.1 := congrArg Subtype.val hab
  have hrel : (Work.Stems.coneSetoid F).r a.1 b.1 := Quotient.eq''.mp h
  show a.1.1 = b.1.1
  rcases hrel with h' | ⟨h1, h2⟩
  · rw [h']
  · exfalso
    have ha : coneHeight (coneMk (F := F) a.1) < cofibreHalf := a.2.2
    rw [coneHeight_coneMk, h1] at ha
    have : ((1 : unitInterval) : ℝ) < ((cofibreHalf : unitInterval) : ℝ) := ha
    norm_num [cofibreHalf] at this

/-- **The projection of the middle of the cone to its base.** -/
def coneMidProj : C(↥(coneMidSet (F := F)), F) :=
  Topology.IsQuotientMap.lift (isQuotientMap_coneMidMk (F := F)) (coneMidProjFun (F := F))
    (coneMidProjFun_factors (F := F))

/-- The computation rule of the projection on a representative. -/
theorem coneMidProj_coneMidMk (p : ↥((coneMk (F := F)) ⁻¹' coneMidSet (F := F))) :
    coneMidProj (F := F) (coneMidMk (F := F) p) = p.1.1 := by
  have h := Topology.IsQuotientMap.lift_comp (isQuotientMap_coneMidMk (F := F))
    (coneMidProjFun (F := F)) (coneMidProjFun_factors (F := F))
  exact congrFun (congrArg (fun k : C(↥((coneMk (F := F)) ⁻¹' coneMidSet (F := F)), F) => ⇑k) h) p

/-! ## The section `x ↦ [x, 1/4]` -/

/-- The point `1/4` of the unit interval. -/
def coneQuarter : unitInterval := ⟨1 / 4, by norm_num⟩

theorem coneQuarter_pos : (0 : unitInterval) < coneQuarter := by
  rw [← Subtype.coe_lt_coe]; norm_num [coneQuarter]

theorem coneQuarter_lt_half : coneQuarter < cofibreHalf := by
  rw [← Subtype.coe_lt_coe]; norm_num [coneQuarter, cofibreHalf]

theorem coneMid_mem_sec (x : F) :
    coneMk (F := F) (x, coneQuarter) ∈ coneMidSet (F := F) := by
  show (0 : unitInterval) < coneHeight (coneMk (F := F) (x, coneQuarter)) ∧
    coneHeight (coneMk (F := F) (x, coneQuarter)) < cofibreHalf
  rw [coneHeight_coneMk]
  exact ⟨coneQuarter_pos, coneQuarter_lt_half⟩

/-- **The section of the projection**: `x ↦ [x, 1/4]`. -/
def coneMidSec : C(F, ↥(coneMidSet (F := F))) where
  toFun x := ⟨coneMk (F := F) (x, coneQuarter), coneMid_mem_sec (F := F) x⟩
  continuous_toFun := Continuous.subtype_mk
    (continuous_quotient_mk'.comp (continuous_id.prodMk (continuous_const (y := coneQuarter))))
    (coneMid_mem_sec (F := F))

/-! ## The homotopy `(x,t,s) ↦ [x, (1-s)*t + s/4]` -/

/-- `(1-s)*t + s/4 ∈ I`, the height of the homotoped point. -/
def midPt (s t : unitInterval) : unitInterval :=
  ⟨(1 - (s : ℝ)) * (t : ℝ) + (s : ℝ) / 4, by
    constructor <;> nlinarith [s.2.1, s.2.2, t.2.1, t.2.2]⟩

@[simp] theorem midPt_zero (t : unitInterval) : midPt 0 t = t := by
  apply Subtype.ext; simp [midPt]

@[simp] theorem midPt_one (t : unitInterval) : midPt 1 t = coneQuarter := by
  apply Subtype.ext; simp [midPt, coneQuarter]

/-- The same, as a continuous map. -/
def midPtC : C(unitInterval × unitInterval, unitInterval) where
  toFun p := midPt p.1 p.2
  continuous_toFun := Continuous.subtype_mk (by fun_prop) (fun p => by
    constructor <;> nlinarith [p.1.2.1, p.1.2.2, p.2.2.1, p.2.2.2])

/-- The homotoped height is positive if the starting height is. -/
theorem midPt_pos (s : unitInterval) {t : unitInterval} (ht : (0 : unitInterval) < t) :
    (0 : unitInterval) < midPt s t := by
  rw [← Subtype.coe_lt_coe]
  have ht' : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  rcases lt_or_eq_of_le s.2.2 with hs | hs
  · have hs' : (s : ℝ) < 1 := hs
    have h1 : (0 : ℝ) < 1 - (s : ℝ) := by linarith
    have h2 : (0 : ℝ) < (1 - (s : ℝ)) * (t : ℝ) := mul_pos h1 ht'
    have h3 : (0 : ℝ) ≤ (s : ℝ) / 4 := by linarith [s.2.1]
    show (0 : ℝ) < (1 - (s : ℝ)) * (t : ℝ) + (s : ℝ) / 4
    exact add_pos_of_pos_of_nonneg h2 h3
  · have hmid : midPt s t = coneQuarter := by
      apply Subtype.ext
      simp only [midPt, coneQuarter, Subtype.coe_mk]
      rw [hs]; ring
    rw [hmid]; exact coneQuarter_pos

/-- The homotoped height stays below `1/2` if the starting height is. -/
theorem midPt_lt_half (s : unitInterval) {t : unitInterval} (ht : t < cofibreHalf) :
    midPt s t < cofibreHalf := by
  rw [← Subtype.coe_lt_coe]
  have ht' : (t : ℝ) < 1 / 2 := by
    have := ht; rw [← Subtype.coe_lt_coe] at this; simpa [cofibreHalf] using this
  rcases lt_or_eq_of_le s.2.2 with hs | hs
  · have hs' : (s : ℝ) < 1 := hs
    have h1 : (0 : ℝ) < 1 - (s : ℝ) := by linarith
    have h2 : (1 - (s : ℝ)) * (t : ℝ) < (1 - (s : ℝ)) * (1 / 2) :=
      mul_lt_mul_of_pos_left ht' h1
    show (1 - (s : ℝ)) * (t : ℝ) + (s : ℝ) / 4 < (1 : ℝ) / 2
    nlinarith [h2, s.2.1]
  · have hmid : midPt s t = coneQuarter := by
      apply Subtype.ext
      simp only [midPt, coneQuarter, Subtype.coe_mk]
      rw [hs]; ring
    rw [hmid]; exact coneQuarter_lt_half

/-- The homotoped point lies in the middle. -/
theorem coneMid_mem_hom (q : ↥((coneMk (F := F)) ⁻¹' coneMidSet (F := F)) × unitInterval) :
    coneMk (F := F) (q.1.1.1, midPt q.2 q.1.1.2) ∈ coneMidSet (F := F) := by
  show (0 : unitInterval) < coneHeight (coneMk (F := F) (q.1.1.1, midPt q.2 q.1.1.2)) ∧
    coneHeight (coneMk (F := F) (q.1.1.1, midPt q.2 q.1.1.2)) < cofibreHalf
  rw [coneHeight_coneMk]
  refine ⟨?_, ?_⟩
  · exact midPt_pos q.2 (by simpa [coneHeight_coneMk] using q.1.2.1)
  · exact midPt_lt_half q.2 (by simpa [coneHeight_coneMk] using q.1.2.2)

/-- The raw homotopy, on the preimage of the middle. -/
def coneMidHomRaw :
    C(↥((coneMk (F := F)) ⁻¹' coneMidSet (F := F)) × unitInterval, ↥(coneMidSet (F := F))) where
  toFun q := ⟨coneMk (F := F) (q.1.1.1, midPt q.2 q.1.1.2), coneMid_mem_hom (F := F) q⟩
  continuous_toFun := Continuous.subtype_mk
    (continuous_quotient_mk'.comp (Continuous.prodMk
      (continuous_fst.comp (continuous_subtype_val.comp continuous_fst))
      (midPtC.continuous.comp (continuous_snd.prodMk
        (continuous_snd.comp (continuous_subtype_val.comp continuous_fst))))))
    (coneMid_mem_hom (F := F))

/-- The curried homotopy, as a continuous map into the function space. -/
def coneMidHomCurried :
    C(↥((coneMk (F := F)) ⁻¹' coneMidSet (F := F)), C(unitInterval, ↥(coneMidSet (F := F)))) where
  toFun p := ⟨fun s => coneMidHomRaw (F := F) (p, s),
    (coneMidHomRaw (F := F)).continuous.comp (continuous_const.prodMk continuous_id)⟩
  continuous_toFun := ContinuousMap.continuous_of_continuous_uncurry _
    (coneMidHomRaw (F := F)).continuous

/-- The raw homotopy is constant on the fibres of the restricted quotient map: on the middle the
cone relation is trivial. -/
theorem coneMidHomCurried_factors :
    Function.FactorsThrough (coneMidHomCurried (F := F)) (coneMidMk (F := F)) := by
  intro a b hab
  have h : coneMk (F := F) a.1 = coneMk (F := F) b.1 := congrArg Subtype.val hab
  have hrel : (Work.Stems.coneSetoid F).r a.1 b.1 := Quotient.eq''.mp h
  have hab' : a = b := by
    apply Subtype.ext
    rcases hrel with h' | ⟨h1, h2⟩
    · exact h'
    · exfalso
      have ha : coneHeight (coneMk (F := F) a.1) < cofibreHalf := a.2.2
      rw [coneHeight_coneMk, h1] at ha
      have : ((1 : unitInterval) : ℝ) < ((cofibreHalf : unitInterval) : ℝ) := ha
      norm_num [cofibreHalf] at this
  subst hab'
  rfl

/-- **The homotopy of the middle of the cone, curried.** -/
def coneMidHom :
    C(↥(coneMidSet (F := F)), C(unitInterval, ↥(coneMidSet (F := F)))) :=
  Topology.IsQuotientMap.lift (isQuotientMap_coneMidMk (F := F)) (coneMidHomCurried (F := F))
    (coneMidHomCurried_factors (F := F))

/-- The computation rule of the homotopy on a representative. -/
theorem coneMidHom_coneMidMk (p : ↥((coneMk (F := F)) ⁻¹' coneMidSet (F := F)))
    (s : unitInterval) :
    coneMidHom (F := F) (coneMidMk (F := F) p) s = coneMidHomRaw (F := F) (p, s) := by
  have h := Topology.IsQuotientMap.lift_comp (isQuotientMap_coneMidMk (F := F))
    (coneMidHomCurried (F := F)) (coneMidHomCurried_factors (F := F))
  have h2 := congrFun (congrArg (fun k : C(↥((coneMk (F := F)) ⁻¹' coneMidSet (F := F)),
      C(unitInterval, ↥(coneMidSet (F := F)))) => ⇑k) h) p
  exact congrFun (congrArg (fun k : C(unitInterval, ↥(coneMidSet (F := F))) => ⇑k) h2) s

/-- Every point of the middle is the image of a point of `F × I`. -/
theorem exists_coneMidMk_eq (y : ↥(coneMidSet (F := F))) :
    ∃ p : ↥((coneMk (F := F)) ⁻¹' coneMidSet (F := F)), coneMidMk (F := F) p = y := by
  refine ⟨⟨Quotient.out y.1, ?_⟩, Subtype.ext ?_⟩
  · show coneMk (F := F) (Quotient.out y.1) ∈ coneMidSet (F := F)
    rw [show coneMk (F := F) (Quotient.out y.1) = y.1 from Quotient.out_eq y.1]
    exact y.2
  · show coneMk (F := F) (Quotient.out y.1) = y.1
    exact Quotient.out_eq y.1

/-- At time `0` the homotopy is the identity. -/
theorem coneMidHomRaw_zero (p : ↥((coneMk (F := F)) ⁻¹' coneMidSet (F := F))) :
    coneMidHomRaw (F := F) (p, (0 : unitInterval)) = coneMidMk (F := F) p := by
  apply Subtype.ext
  show coneMk (F := F) (p.1.1, midPt 0 p.1.2) = coneMk (F := F) p.1
  rw [midPt_zero]

/-- At time `1` the homotopy is the section of the projection. -/
theorem coneMidHomRaw_one (p : ↥((coneMk (F := F)) ⁻¹' coneMidSet (F := F))) :
    coneMidHomRaw (F := F) (p, (1 : unitInterval)) = coneMidSec (F := F) p.1.1 := by
  apply Subtype.ext
  show coneMk (F := F) (p.1.1, midPt 1 p.1.2) = coneMk (F := F) (p.1.1, coneQuarter)
  rw [midPt_one]

/-- The homotopy, uncurried and with the variables swapped into the order `(time, point)`. -/
def coneMidHomotopyMap :
    C(unitInterval × ↥(coneMidSet (F := F)), ↥(coneMidSet (F := F))) where
  toFun q := ContinuousMap.uncurry (coneMidHom (F := F)) (q.2, q.1)
  continuous_toFun := (ContinuousMap.uncurry (coneMidHom (F := F))).continuous.comp
    (continuous_snd.prodMk continuous_fst)

theorem coneMidHomotopyMap_zero (y : ↥(coneMidSet (F := F))) :
    coneMidHomotopyMap (F := F) (0, y) = y := by
  obtain ⟨p, hp⟩ := exists_coneMidMk_eq (F := F) y
  rw [← hp]
  show coneMidHom (F := F) (coneMidMk (F := F) p) 0 = coneMidMk (F := F) p
  rw [coneMidHom_coneMidMk]
  exact coneMidHomRaw_zero (F := F) p

theorem coneMidHomotopyMap_one (y : ↥(coneMidSet (F := F))) :
    coneMidHomotopyMap (F := F) (1, y) = coneMidSec (F := F) (coneMidProj (F := F) y) := by
  obtain ⟨p, hp⟩ := exists_coneMidMk_eq (F := F) y
  rw [← hp]
  show coneMidHom (F := F) (coneMidMk (F := F) p) 1 =
    coneMidSec (F := F) (coneMidProj (F := F) (coneMidMk (F := F) p))
  rw [coneMidHom_coneMidMk, coneMidProj_coneMidMk]
  exact coneMidHomRaw_one (F := F) p

/-- The homotopy `id ~ sec ∘ proj` on the middle of the cone. -/
def coneMidHomotopyId :
    ContinuousMap.Homotopy (ContinuousMap.id ↥(coneMidSet (F := F)))
      ((coneMidSec (F := F)).comp (coneMidProj (F := F))) where
  toContinuousMap := coneMidHomotopyMap (F := F)
  map_zero_left y := coneMidHomotopyMap_zero (F := F) y
  map_one_left y := coneMidHomotopyMap_one (F := F) y

/-! ## The homotopy equivalence -/

theorem coneMidHomotopyEquivAux {F : Type} [TopologicalSpace F] [Nonempty F] :
    Nonempty (ContinuousMap.HomotopyEquiv ↥(coneMidSet (F := F)) F) := by
  have hcomp : (coneMidProj (F := F)).comp (coneMidSec (F := F)) = ContinuousMap.id F := by
    ext x
    show coneMidProj (F := F) (coneMidMk (F := F) ⟨(x, coneQuarter), coneMid_mem_sec (F := F) x⟩) = x
    exact coneMidProj_coneMidMk (F := F) ⟨(x, coneQuarter), coneMid_mem_sec (F := F) x⟩
  refine ⟨{ toFun := coneMidProj (F := F)
            invFun := coneMidSec (F := F)
            left_inv := ⟨(coneMidHomotopyId (F := F)).symm⟩
            right_inv := ?_ }⟩
  rw [hcomp]

/-- **The middle slab of the cone on `F` is homotopy equivalent to `F`.**

`{y : Cone F | 0 < coneHeight y ∧ coneHeight y < cofibreHalf}` is the middle part of the cone; the
projection to the first coordinate `[x,t] ↦ x` is well defined and continuous (on the middle the
cone relation is trivial), the section `x ↦ [x, 1/4]` is a right inverse, and
`(x,t,s) ↦ [x, (1-s)*t + s/4]` is the homotopy `sec ∘ proj ~ id` (the value stays in `(0,1/2)`).

Suggested route (the pattern of `Submission/Work/RatHurewicz/Cofibre/ConeShrink.lean`):
the restricted quotient map `midMk : ↥(coneMk ⁻¹' midSet) → ↥midSet` (with
`Topology.IsQuotientMap.restrictPreimage_isOpen`) is a quotient map; the raw map `p ↦ p.1.1` is
continuous and constant on its fibres (use `Quotient.eq''`; the `t = 1` case of the cone relation is
excluded by `t < 1/2`), so it descends to `midProj : C(↥midSet, F)`.  Descend the curried
`p ↦ (s ↦ ⟨coneMk (p.1.1, (1-s)*p.1.2 + s/4), _⟩)` the same way (`FactorsThrough` reduces to
`a = b` on the mid, so you can use the `coneShrinkCurried_factors` proof verbatim), giving
`midHom : C(↥midSet, C(I, ↥midSet))`, and conclude with
`ContinuousMap.Homotopy.mk` (swap the variables with `continuous_snd.prodMk continuous_fst`).
For the range condition `0 < (1-s)*t + s/4 < 1/2` from `0 < t < 1/2` it is enough to note that
`1 - s ≥ 0` and to split on `s = 1` vs `s < 1`; `nlinarith` with `s.2.1, s.2.2, t.2.1, t.2.2`
plus the multiplicativity hints does it. -/
theorem coneMidHomotopyEquiv {F : Type} [TopologicalSpace F] [Nonempty F] :
    Nonempty (ContinuousMap.HomotopyEquiv
      ↥{y : Work.Stems.Cone F | (0 : unitInterval) < Work.RatHurewicz.coneHeight y ∧
          Work.RatHurewicz.coneHeight y < Work.RatHurewicz.cofibreHalf} F) :=
  coneMidHomotopyEquivAux

end

end Work.RatHurewicz.Cofibre
