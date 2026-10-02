import Mathlib
import Submission.Work.Thom.Orientation.Reflection
import Submission.Work.Cohomology.SphZeroBase

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-!
# The two constant sections of the rank-one sphere bundle, and the reflection

For the rank-one sphere bundle `Sph Y 1 = Y × S⁰ ⊆ Y × ℝ¹` of the trivial line bundle over a space
`Y`, this file fixes

* the two points `sphPlus`, `sphMinus` of `S⁰ ⊆ ℝ¹` (the fibre coordinates of the two components),
* the two constant sections `sigPos`, `sigNeg : Y → Sph Y 1`, `y ↦ (y, ±1)`,
* the projection `sphProj : Y × ℝ¹ → Y` and the inclusion `sphIncl : Sph Y 1 → Y × ℝ¹`,
* the reflection `fibSph : Sph Y 1 → Sph Y 1` induced by `fibRefl 1 Y`,
* the two open "halves" `Upos`, `Uneg` of `Sph Y 1` (the images of the two sections), a disjoint
  open cover of `Sph Y 1`,

together with the elementary relations between them.
-/

namespace Work.Thom.Orientation

open Work.Thom

noncomputable section

/-! ## The two points of `S⁰ ⊆ ℝ¹` -/

/-- The point `+1` of `S⁰ = {±1} ⊆ ℝ¹`. -/
def sphPlus : EuclideanSpace ℝ (Fin 1) := (Work.Cohomology.s0N : EuclideanSpace ℝ (Fin 1))

/-- The point `-1` of `S⁰ = {±1} ⊆ ℝ¹`. -/
def sphMinus : EuclideanSpace ℝ (Fin 1) := (Work.Cohomology.s0S : EuclideanSpace ℝ (Fin 1))

theorem sphPlus_mem : sphPlus ∈ mSph 1 := Work.Cohomology.s0N.2

theorem sphMinus_mem : sphMinus ∈ mSph 1 := Work.Cohomology.s0S.2

theorem sphPlus_ne_sphMinus : sphPlus ≠ sphMinus :=
  fun h => Work.Cohomology.s0N_ne_s0S (Subtype.ext h)

theorem sphMinus_eq_neg : sphMinus = -sphPlus := by
  apply WithLp.ofLp_injective 2
  funext i
  fin_cases i
  simp [sphPlus, sphMinus, Work.Cohomology.s0N, Work.Cohomology.s0S]

/-- Every point of `S⁰ ⊆ ℝ¹` is `sphPlus` or `sphMinus`. -/
theorem sph_cover (v : EuclideanSpace ℝ (Fin 1)) (hv : v ∈ mSph 1) :
    v = sphPlus ∨ v = sphMinus := by
  rcases Work.Cohomology.s0_cover (⟨v, hv⟩ : ↥(Work.Cohomology.sphSet 1)) with h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (congrArg Subtype.val h)

theorem flipFst_one (v : EuclideanSpace ℝ (Fin 1)) : flipFst 1 v = -v := by
  apply WithLp.ofLp_injective 2
  funext i
  fin_cases i
  rw [flipFst_ofLp, negFst_apply_pos 1 (by norm_num)]
  simp

theorem flipFst_sphPlus : flipFst 1 sphPlus = sphMinus := by
  rw [flipFst_one]
  exact sphMinus_eq_neg.symm

theorem flipFst_sphMinus : flipFst 1 sphMinus = sphPlus := by
  rw [flipFst_one, sphMinus_eq_neg, neg_neg]

theorem norm_sphMinus_sub_sphPlus : ‖sphMinus - sphPlus‖ = 2 := by
  have h : sphMinus - sphPlus = (-2 : ℝ) • sphPlus := by
    rw [sphMinus_eq_neg]
    module
  rw [h, norm_smul, Real.norm_eq_abs, sphPlus_mem]
  norm_num

/-! ## The two constant sections and the projection -/

/-- The constant section `y ↦ (y, +1)` of the rank-one sphere bundle. -/
def sigPos {Y : Type} [TopologicalSpace Y] : C(Y, ↥(Sph Y 1)) where
  toFun y := ⟨(y, sphPlus), sphPlus_mem⟩
  continuous_toFun :=
    Continuous.subtype_mk (continuous_id.prodMk continuous_const) (fun _ => sphPlus_mem)

/-- The constant section `y ↦ (y, -1)` of the rank-one sphere bundle. -/
def sigNeg {Y : Type} [TopologicalSpace Y] : C(Y, ↥(Sph Y 1)) where
  toFun y := ⟨(y, sphMinus), sphMinus_mem⟩
  continuous_toFun :=
    Continuous.subtype_mk (continuous_id.prodMk continuous_const) (fun _ => sphMinus_mem)

/-- The projection `Y × ℝ¹ → Y`. -/
def sphProj {Y : Type} [TopologicalSpace Y] : C(Y × EuclideanSpace ℝ (Fin 1), Y) :=
  ⟨Prod.fst, continuous_fst⟩

/-- The inclusion of the rank-one sphere bundle into its ambient trivial bundle. -/
def sphIncl {Y : Type} [TopologicalSpace Y] : C(↥(Sph Y 1), Y × EuclideanSpace ℝ (Fin 1)) :=
  Work.Thom.subtypeMap (Sph Y 1)

theorem sigPos_apply {Y : Type} [TopologicalSpace Y] (y : Y) :
    ((sigPos (Y := Y)) y : ↥(Sph Y 1)).val = (y, sphPlus) := rfl

theorem sigNeg_apply {Y : Type} [TopologicalSpace Y] (y : Y) :
    ((sigNeg (Y := Y)) y : ↥(Sph Y 1)).val = (y, sphMinus) := rfl

theorem sphProj_comp_sphIncl_comp_sigPos {Y : Type} [TopologicalSpace Y] :
    (sphProj (Y := Y)).comp ((sphIncl (Y := Y)).comp (sigPos (Y := Y))) = ContinuousMap.id Y := by
  apply ContinuousMap.ext
  intro y
  rfl

theorem sphProj_comp_sphIncl_comp_sigNeg {Y : Type} [TopologicalSpace Y] :
    (sphProj (Y := Y)).comp ((sphIncl (Y := Y)).comp (sigNeg (Y := Y))) = ContinuousMap.id Y := by
  apply ContinuousMap.ext
  intro y
  rfl

/-! ## The reflection of the rank-one sphere bundle -/

/-- The reflection `(y, v) ↦ (y, -v)` of the rank-one sphere bundle. -/
def fibSph {Y : Type} [TopologicalSpace Y] : C(↥(Sph Y 1), ↥(Sph Y 1)) :=
  Work.Thom.restrictMap (fibRefl 1 Y) (Sph Y 1) (Sph Y 1) (fibRefl_mem_sph 1 Y)

theorem fibSph_apply_val {Y : Type} [TopologicalSpace Y] (p : ↥(Sph Y 1)) :
    ((fibSph (Y := Y) p : ↥(Sph Y 1)) : Y × EuclideanSpace ℝ (Fin 1))
      = fibRefl 1 Y (p : Y × EuclideanSpace ℝ (Fin 1)) := rfl

theorem fibSph_comp_sigPos {Y : Type} [TopologicalSpace Y] :
    (fibSph (Y := Y)).comp (sigPos (Y := Y)) = sigNeg (Y := Y) := by
  apply ContinuousMap.ext
  intro y
  apply Subtype.ext
  rw [ContinuousMap.comp_apply, fibSph_apply_val, sigPos_apply, sigNeg_apply, fibRefl_apply,
    flipFst_sphPlus]

theorem fibSph_comp_sigNeg {Y : Type} [TopologicalSpace Y] :
    (fibSph (Y := Y)).comp (sigNeg (Y := Y)) = sigPos (Y := Y) := by
  apply ContinuousMap.ext
  intro y
  apply Subtype.ext
  rw [ContinuousMap.comp_apply, fibSph_apply_val, sigPos_apply, sigNeg_apply, fibRefl_apply,
    flipFst_sphMinus]

/-- The fold map onto the positive half: `p ↦ (p.1, +1)`. -/
def foldPos {Y : Type} [TopologicalSpace Y] : C(↥(Sph Y 1), ↥(Sph Y 1)) :=
  (sigPos (Y := Y)).comp ((sphProj (Y := Y)).comp (sphIncl (Y := Y)))

/-- The fold map onto the negative half: `p ↦ (p.1, -1)`. -/
def foldNeg {Y : Type} [TopologicalSpace Y] : C(↥(Sph Y 1), ↥(Sph Y 1)) :=
  (sigNeg (Y := Y)).comp ((sphProj (Y := Y)).comp (sphIncl (Y := Y)))

theorem foldPos_comp_sigPos {Y : Type} [TopologicalSpace Y] :
    (foldPos (Y := Y)).comp (sigPos (Y := Y)) = sigPos (Y := Y) := by
  apply ContinuousMap.ext
  intro y
  rfl

theorem foldNeg_comp_sigPos {Y : Type} [TopologicalSpace Y] :
    (foldNeg (Y := Y)).comp (sigPos (Y := Y)) = sigNeg (Y := Y) := by
  apply ContinuousMap.ext
  intro y
  rfl

theorem foldPos_comp_sigNeg {Y : Type} [TopologicalSpace Y] :
    (foldPos (Y := Y)).comp (sigNeg (Y := Y)) = sigPos (Y := Y) := by
  apply ContinuousMap.ext
  intro y
  rfl

theorem foldNeg_comp_sigNeg {Y : Type} [TopologicalSpace Y] :
    (foldNeg (Y := Y)).comp (sigNeg (Y := Y)) = sigNeg (Y := Y) := by
  apply ContinuousMap.ext
  intro y
  rfl

/-! ## The two halves of `Sph Y 1` -/

/-- The positive half of the rank-one sphere bundle, described by a metric condition that makes
openness immediate. -/
def Upos {Y : Type} [TopologicalSpace Y] : Set ↥(Sph Y 1) :=
  {p | ‖(p : Y × EuclideanSpace ℝ (Fin 1)).2 - sphPlus‖ < 1}

/-- The negative half of the rank-one sphere bundle. -/
def Uneg {Y : Type} [TopologicalSpace Y] : Set ↥(Sph Y 1) :=
  {p | 1 < ‖(p : Y × EuclideanSpace ℝ (Fin 1)).2 - sphPlus‖}

theorem mem_Upos_iff {Y : Type} [TopologicalSpace Y] (p : ↥(Sph Y 1)) :
    p ∈ Upos ↔ (p : Y × EuclideanSpace ℝ (Fin 1)).2 = sphPlus := by
  constructor
  · intro hp
    change ‖(p : Y × EuclideanSpace ℝ (Fin 1)).2 - sphPlus‖ < 1 at hp
    rcases sph_cover (p : Y × EuclideanSpace ℝ (Fin 1)).2 p.2 with h | h
    · exact h
    · rw [h, norm_sphMinus_sub_sphPlus] at hp
      exact absurd hp (by norm_num)
  · intro hp
    change ‖(p : Y × EuclideanSpace ℝ (Fin 1)).2 - sphPlus‖ < 1
    rw [hp, sub_self, norm_zero]
    norm_num

theorem mem_Uneg_iff {Y : Type} [TopologicalSpace Y] (p : ↥(Sph Y 1)) :
    p ∈ Uneg ↔ (p : Y × EuclideanSpace ℝ (Fin 1)).2 = sphMinus := by
  constructor
  · intro hp
    change 1 < ‖(p : Y × EuclideanSpace ℝ (Fin 1)).2 - sphPlus‖ at hp
    rcases sph_cover (p : Y × EuclideanSpace ℝ (Fin 1)).2 p.2 with h | h
    · rw [h, sub_self, norm_zero] at hp
      exact absurd hp (by norm_num)
    · exact h
  · intro hp
    change 1 < ‖(p : Y × EuclideanSpace ℝ (Fin 1)).2 - sphPlus‖
    rw [hp, norm_sphMinus_sub_sphPlus]
    norm_num

theorem isOpen_Upos {Y : Type} [TopologicalSpace Y] : IsOpen (Upos (Y := Y)) :=
  isOpen_lt (continuous_norm.comp (((continuous_snd.comp continuous_subtype_val).sub
    continuous_const))) continuous_const

theorem isOpen_Uneg {Y : Type} [TopologicalSpace Y] : IsOpen (Uneg (Y := Y)) :=
  isOpen_lt continuous_const (continuous_norm.comp (((continuous_snd.comp continuous_subtype_val).sub
    continuous_const)))

theorem disjoint_Upos_Uneg {Y : Type} [TopologicalSpace Y] :
    Disjoint (Upos (Y := Y)) (Uneg (Y := Y)) := by
  rw [Set.disjoint_left]
  intro p hp hq
  change ‖(p : Y × EuclideanSpace ℝ (Fin 1)).2 - sphPlus‖ < 1 at hp
  change 1 < ‖(p : Y × EuclideanSpace ℝ (Fin 1)).2 - sphPlus‖ at hq
  exact absurd hp (not_lt.mpr (le_of_lt hq))

theorem union_Upos_Uneg {Y : Type} [TopologicalSpace Y] :
    Upos (Y := Y) ∪ Uneg (Y := Y) = Set.univ := by
  ext p
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  rcases sph_cover (p : Y × EuclideanSpace ℝ (Fin 1)).2 p.2 with h | h
  · left
    rw [mem_Upos_iff, h]
  · right
    rw [mem_Uneg_iff, h]

theorem range_sigPos {Y : Type} [TopologicalSpace Y] :
    Set.range (sigPos (Y := Y)) = Upos (Y := Y) := by
  ext p
  constructor
  · rintro ⟨y, rfl⟩
    rw [mem_Upos_iff]
    rfl
  · intro hp
    refine ⟨(p : Y × EuclideanSpace ℝ (Fin 1)).1, ?_⟩
    apply Subtype.ext
    exact Prod.ext rfl ((mem_Upos_iff p).mp hp).symm

theorem range_sigNeg {Y : Type} [TopologicalSpace Y] :
    Set.range (sigNeg (Y := Y)) = Uneg (Y := Y) := by
  ext p
  constructor
  · rintro ⟨y, rfl⟩
    rw [mem_Uneg_iff]
    rfl
  · intro hp
    refine ⟨(p : Y × EuclideanSpace ℝ (Fin 1)).1, ?_⟩
    apply Subtype.ext
    exact Prod.ext rfl ((mem_Uneg_iff p).mp hp).symm

/-! ## The two halves are homeomorphic to `Y` -/

/-- The section `Y → Upos` landing in the subtype `Upos`. -/
def sigPosU {Y : Type} [TopologicalSpace Y] : C(Y, ↥(Upos (Y := Y))) where
  toFun y := ⟨sigPos y, by rw [mem_Upos_iff]; rfl⟩
  continuous_toFun :=
    Continuous.subtype_mk (sigPos.continuous) (fun y => by rw [mem_Upos_iff]; rfl)

/-- Its inverse, `Upos → Y`. -/
def sigPosUinv {Y : Type} [TopologicalSpace Y] : C(↥(Upos (Y := Y)), Y) :=
  ⟨fun p => (p : ↥(Sph Y 1)).val.1, continuous_fst.comp (continuous_subtype_val.comp
    continuous_subtype_val)⟩

theorem sigPosUinv_comp_sigPosU {Y : Type} [TopologicalSpace Y] :
    (sigPosUinv (Y := Y)).comp (sigPosU (Y := Y)) = ContinuousMap.id Y := by
  apply ContinuousMap.ext
  intro y
  rfl

theorem sigPosU_comp_sigPosUinv {Y : Type} [TopologicalSpace Y] :
    (sigPosU (Y := Y)).comp (sigPosUinv (Y := Y)) = ContinuousMap.id ↥(Upos (Y := Y)) := by
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext rfl ((mem_Upos_iff (p : ↥(Sph Y 1))).mp p.2).symm

theorem sigPos_eq_subtypeMap_comp_sigPosU {Y : Type} [TopologicalSpace Y] :
    (sigPos (Y := Y))
      = (Work.Thom.subtypeMap (Upos (Y := Y))).comp (sigPosU (Y := Y)) := by
  apply ContinuousMap.ext
  intro y
  rfl

/-- The section `Y → Uneg` landing in the subtype `Uneg`. -/
def sigNegU {Y : Type} [TopologicalSpace Y] : C(Y, ↥(Uneg (Y := Y))) where
  toFun y := ⟨sigNeg y, by rw [mem_Uneg_iff]; rfl⟩
  continuous_toFun :=
    Continuous.subtype_mk (sigNeg.continuous) (fun y => by rw [mem_Uneg_iff]; rfl)

/-- Its inverse, `Uneg → Y`. -/
def sigNegUinv {Y : Type} [TopologicalSpace Y] : C(↥(Uneg (Y := Y)), Y) :=
  ⟨fun p => (p : ↥(Sph Y 1)).val.1, continuous_fst.comp (continuous_subtype_val.comp
    continuous_subtype_val)⟩

theorem sigNegUinv_comp_sigNegU {Y : Type} [TopologicalSpace Y] :
    (sigNegUinv (Y := Y)).comp (sigNegU (Y := Y)) = ContinuousMap.id Y := by
  apply ContinuousMap.ext
  intro y
  rfl

theorem sigNegU_comp_sigNegUinv {Y : Type} [TopologicalSpace Y] :
    (sigNegU (Y := Y)).comp (sigNegUinv (Y := Y)) = ContinuousMap.id ↥(Uneg (Y := Y)) := by
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext rfl ((mem_Uneg_iff (p : ↥(Sph Y 1))).mp p.2).symm

theorem sigNeg_eq_subtypeMap_comp_sigNegU {Y : Type} [TopologicalSpace Y] :
    (sigNeg (Y := Y))
      = (Work.Thom.subtypeMap (Uneg (Y := Y))).comp (sigNegU (Y := Y)) := by
  apply ContinuousMap.ext
  intro y
  rfl

end

end Work.Thom.Orientation
