/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The regions of the polar (iterated radial) Seeley estimate

This module sets up the *level-dependent* regions used in the proof of the `C^{k,α}` estimate
for the iterated polar extension (the target `Work.NN.Final.exists_extension_polar`).

The iterated extension `iterateFrom n ρ a b j` extends a function in the coordinates
`j, j+1, …, n-1`.  At level `j` the function is controlled on the region

  `cvReg n ρ j = {z | (∀ i < j, ‖z i‖ < chainC n j * ρ i) ∧ (∀ i ≥ j, ‖z i‖ < chainD n j * ρ i)}`,

with *strictly increasing* level-dependent constants `1 < chainC n j` and `2 ≤ chainD n j`
(both `< 3` for `j ≤ n`).  The monotonicity in `j` is what makes the one-step estimate
("_the extension in the `j`-th coordinate of a function which is `C^k` on `cvReg (j+1)` is
`C^k` on `cvReg j`_") go through: the evaluation points of the `j`-th step lie strictly inside
the next level's region, so that the smoothness of the input on the *open* region can be used.

The two ingredients of the one-step estimate are the flat Seoley estimate
(`seeleyRegionEstimate`) on the flat region `cvFlat n ρ j ×ˢ {t | 0 < t}`, and the change of
variables `radialExt_seeleyExt_flat` along the logarithmic chart `polarChart`.
-/
import Mathlib
import Submission.Work.NN.Final.Defs
import Submission.Work.NN.Final.PolarDefs
import Submission.Work.NN.Final.PolarRegions
import Submission.Work.NN.Final.PolarGlob
import Submission.Work.NN.Final.radialExt_seeleyExt_flat
import Submission.Work.NN.Final.holderNorm_comp_flatPoint

noncomputable section

open scoped NNReal ENNReal ContDiff Topology
open Set Filter

namespace Work.NN.Final

variable {n : ℕ} {ρ : Fin n → ℝ}

/-! ## The level-dependent constants -/

/-- The transverse bound (`i < j`) of the chain region at level `j`. -/
def chainC (n j : ℕ) : ℝ := 3 / 2 + (j : ℝ) / (8 * ((n : ℝ) + 1))

/-- The "free" bound (`i ≥ j`) of the chain region at level `j`. -/
def chainD (n j : ℕ) : ℝ := 2 + (j : ℝ) / (8 * ((n : ℝ) + 1))

lemma chainC_pos (n j : ℕ) : 0 < chainC n j := by
  have h : (0 : ℝ) ≤ (j : ℝ) / (8 * ((n : ℝ) + 1)) := by positivity
  rw [chainC]; linarith

lemma chainC_gt_one (n j : ℕ) : 1 < chainC n j := by
  have h : (0 : ℝ) ≤ (j : ℝ) / (8 * ((n : ℝ) + 1)) := by positivity
  rw [chainC]; linarith

lemma chainC_lt_three (n j : ℕ) (hj : j ≤ n) : chainC n j < 3 := by
  rw [chainC]
  have h1 : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hj
  have h2 : (j : ℝ) / (8 * ((n : ℝ) + 1)) ≤ 1 / 8 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  linarith

lemma chainC_mono (n : ℕ) {j k : ℕ} (h : j ≤ k) : chainC n j ≤ chainC n k := by
  rw [chainC, chainC]
  have h1 : (0 : ℝ) < 8 * ((n : ℝ) + 1) := by positivity
  have h2 : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
  exact add_le_add_right (div_le_div_of_nonneg_right h2 (le_of_lt h1)) (3 / 2)

lemma chainD_ge_two (n j : ℕ) : 2 ≤ chainD n j := by
  have h : (0 : ℝ) ≤ (j : ℝ) / (8 * ((n : ℝ) + 1)) := by positivity
  rw [chainD]; linarith

lemma chainD_gt_two (n j : ℕ) (hj : 1 ≤ j) : 2 < chainD n j := by
  rw [chainD]
  have h : (0 : ℝ) < (j : ℝ) / (8 * ((n : ℝ) + 1)) := by
    apply div_pos
    · exact_mod_cast hj
    · positivity
  linarith

lemma chainD_lt_three (n j : ℕ) (hj : j ≤ n) : chainD n j < 3 := by
  rw [chainD]
  have h1 : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hj
  have h2 : (j : ℝ) / (8 * ((n : ℝ) + 1)) ≤ 1 / 8 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  linarith

lemma chainD_mono (n : ℕ) {j k : ℕ} (h : j ≤ k) : chainD n j ≤ chainD n k := by
  rw [chainD, chainD]
  have h1 : (0 : ℝ) < 8 * ((n : ℝ) + 1) := by positivity
  have h2 : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
  exact add_le_add_right (div_le_div_of_nonneg_right h2 (le_of_lt h1)) 2

/-- `exp 1 < 3`, the constant comparison which makes the annulus of the `j`-th step fit into
the flat region. -/
lemma exp_one_lt_three' : Real.exp 1 < 3 := Real.exp_one_lt_three

/-- `2 < exp 1`. -/
lemma two_lt_exp_one' : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two

/-! ## The regions -/

/-- The region of the chain at level `j`: the coordinates `i < j` are bounded by
`chainC n j * ρ i` and the coordinates `i ≥ j` by `chainD n j * ρ i`. -/
def cvReg (n : ℕ) (ρ : Fin n → ℝ) (j : ℕ) : Set (Fin n → ℂ) :=
  {z | (∀ i : Fin n, (i : ℕ) < j → ‖z i‖ < chainC n j * ρ i) ∧
       (∀ i : Fin n, j ≤ (i : ℕ) → ‖z i‖ < chainD n j * ρ i)}

@[simp] lemma mem_cvReg {j : ℕ} {z : Fin n → ℂ} :
    z ∈ cvReg n ρ j ↔
      (∀ i : Fin n, (i : ℕ) < j → ‖z i‖ < chainC n j * ρ i) ∧
      (∀ i : Fin n, j ≤ (i : ℕ) → ‖z i‖ < chainD n j * ρ i) := Iff.rfl

lemma isOpen_cvReg (hρ : ∀ i, 0 < ρ i) (j : ℕ) : IsOpen (cvReg n ρ j) := by
  have h1 : IsOpen {z : Fin n → ℂ | ∀ i : Fin n, (i : ℕ) < j → ‖z i‖ < chainC n j * ρ i} := by
    have hset : {z : Fin n → ℂ | ∀ i : Fin n, (i : ℕ) < j → ‖z i‖ < chainC n j * ρ i}
        = ⋂ i ∈ {i : Fin n | (i : ℕ) < j}, {z : Fin n → ℂ | ‖z i‖ < chainC n j * ρ i} := by
      ext z; simp [Set.mem_iInter]
    rw [hset]
    exact Set.Finite.isOpen_biInter (Set.toFinite _) fun i _ =>
      isOpen_lt (continuous_norm.comp (continuous_apply i)) continuous_const
  have h2 : IsOpen {z : Fin n → ℂ | ∀ i : Fin n, j ≤ (i : ℕ) → ‖z i‖ < chainD n j * ρ i} := by
    have hset : {z : Fin n → ℂ | ∀ i : Fin n, j ≤ (i : ℕ) → ‖z i‖ < chainD n j * ρ i}
        = ⋂ i ∈ {i : Fin n | j ≤ (i : ℕ)}, {z : Fin n → ℂ | ‖z i‖ < chainD n j * ρ i} := by
      ext z; simp [Set.mem_iInter]
    rw [hset]
    exact Set.Finite.isOpen_biInter (Set.toFinite _) fun i _ =>
      isOpen_lt (continuous_norm.comp (continuous_apply i)) continuous_const
  have h4 : cvReg n ρ j =
      {z : Fin n → ℂ | ∀ i : Fin n, (i : ℕ) < j → ‖z i‖ < chainC n j * ρ i} ∩
      {z : Fin n → ℂ | ∀ i : Fin n, j ≤ (i : ℕ) → ‖z i‖ < chainD n j * ρ i} := by
    ext z; simp only [mem_cvReg, mem_inter_iff, Set.mem_ofPred_eq]
  rw [h4]; exact h1.inter h2

/-- The region of the `j`-th step where the flat chart is used: an annulus in the `j`-th
coordinate, with the level-`j` transverse bounds. -/
def cvAnn (n : ℕ) (ρ : Fin n → ℝ) (j : Fin n) (δ : ℝ) : Set (Fin n → ℂ) :=
  {z | (∀ i : Fin n, (i : ℕ) < (j : ℕ) → ‖z i‖ < chainC n (j : ℕ) * ρ i) ∧
       (ρ j / 2 < ‖z j‖ ∧ ‖z j‖ < ρ j * Real.exp δ) ∧
       (∀ i : Fin n, (j : ℕ) < (i : ℕ) → ‖z i‖ < chainD n (j : ℕ) * ρ i)}

@[simp] lemma mem_cvAnn {j : Fin n} {δ : ℝ} {z : Fin n → ℂ} :
    z ∈ cvAnn n ρ j δ ↔
      (∀ i : Fin n, (i : ℕ) < (j : ℕ) → ‖z i‖ < chainC n (j : ℕ) * ρ i) ∧
      (ρ j / 2 < ‖z j‖ ∧ ‖z j‖ < ρ j * Real.exp δ) ∧
      (∀ i : Fin n, (j : ℕ) < (i : ℕ) → ‖z i‖ < chainD n (j : ℕ) * ρ i) := Iff.rfl

lemma isOpen_cvAnn (hρ : ∀ i, 0 < ρ i) (j : Fin n) (δ : ℝ) : IsOpen (cvAnn n ρ j δ) := by
  have h1 : IsOpen {z : Fin n → ℂ | ∀ i : Fin n, (i : ℕ) < (j : ℕ) → ‖z i‖ < chainC n (j:ℕ) * ρ i} := by
    have hset : {z : Fin n → ℂ | ∀ i : Fin n, (i : ℕ) < (j : ℕ) → ‖z i‖ < chainC n (j:ℕ) * ρ i}
        = ⋂ i ∈ {i : Fin n | (i : ℕ) < (j : ℕ)}, {z : Fin n → ℂ | ‖z i‖ < chainC n (j:ℕ) * ρ i} := by
      ext z; simp [Set.mem_iInter]
    rw [hset]
    exact Set.Finite.isOpen_biInter (Set.toFinite _) fun i _ =>
      isOpen_lt (continuous_norm.comp (continuous_apply i)) continuous_const
  have h2 : IsOpen {z : Fin n → ℂ | ρ j / 2 < ‖z j‖ ∧ ‖z j‖ < ρ j * Real.exp δ} :=
    (isOpen_lt continuous_const (continuous_norm.comp (continuous_apply j))).inter
      (isOpen_lt (continuous_norm.comp (continuous_apply j)) continuous_const)
  have h3 : IsOpen {z : Fin n → ℂ | ∀ i : Fin n, (j : ℕ) < (i : ℕ) → ‖z i‖ < chainD n (j:ℕ) * ρ i} := by
    have hset : {z : Fin n → ℂ | ∀ i : Fin n, (j : ℕ) < (i : ℕ) → ‖z i‖ < chainD n (j:ℕ) * ρ i}
        = ⋂ i ∈ {i : Fin n | (j : ℕ) < (i : ℕ)}, {z : Fin n → ℂ | ‖z i‖ < chainD n (j:ℕ) * ρ i} := by
      ext z; simp [Set.mem_iInter]
    rw [hset]
    exact Set.Finite.isOpen_biInter (Set.toFinite _) fun i _ =>
      isOpen_lt (continuous_norm.comp (continuous_apply i)) continuous_const
  have h4 : cvAnn n ρ j δ =
      {z : Fin n → ℂ | ∀ i : Fin n, (i : ℕ) < (j : ℕ) → ‖z i‖ < chainC n (j:ℕ) * ρ i} ∩
      {z : Fin n → ℂ | ρ j / 2 < ‖z j‖ ∧ ‖z j‖ < ρ j * Real.exp δ} ∩
      {z : Fin n → ℂ | ∀ i : Fin n, (j : ℕ) < (i : ℕ) → ‖z i‖ < chainD n (j:ℕ) * ρ i} := by
    ext z; simp only [mem_cvAnn, mem_inter_iff, Set.mem_ofPred_eq]; tauto
  rw [h4]; exact (h1.inter h2).inter h3

/-- The inner part of the level-`j` region: the `j`-th coordinate is strictly inside the
identity region of the radial extension. -/
def cvInner (n : ℕ) (ρ : Fin n → ℝ) (j : Fin n) : Set (Fin n → ℂ) :=
  {z | (∀ i : Fin n, (i : ℕ) < (j : ℕ) → ‖z i‖ < chainC n (j : ℕ) * ρ i) ∧
       ‖z j‖ < ρ j * (3 / 4) ∧
       (∀ i : Fin n, (j : ℕ) < (i : ℕ) → ‖z i‖ < chainD n (j : ℕ) * ρ i)}

@[simp] lemma mem_cvInner {j : Fin n} {z : Fin n → ℂ} :
    z ∈ cvInner n ρ j ↔
      (∀ i : Fin n, (i : ℕ) < (j : ℕ) → ‖z i‖ < chainC n (j : ℕ) * ρ i) ∧
      ‖z j‖ < ρ j * (3 / 4) ∧
      (∀ i : Fin n, (j : ℕ) < (i : ℕ) → ‖z i‖ < chainD n (j : ℕ) * ρ i) := Iff.rfl

lemma isOpen_cvInner (hρ : ∀ i, 0 < ρ i) (j : Fin n) : IsOpen (cvInner n ρ j) := by
  have h1 : IsOpen {z : Fin n → ℂ | ∀ i : Fin n, (i : ℕ) < (j : ℕ) → ‖z i‖ < chainC n (j:ℕ) * ρ i} := by
    have hset : {z : Fin n → ℂ | ∀ i : Fin n, (i : ℕ) < (j : ℕ) → ‖z i‖ < chainC n (j:ℕ) * ρ i}
        = ⋂ i ∈ {i : Fin n | (i : ℕ) < (j : ℕ)}, {z : Fin n → ℂ | ‖z i‖ < chainC n (j:ℕ) * ρ i} := by
      ext z; simp [Set.mem_iInter]
    rw [hset]
    exact Set.Finite.isOpen_biInter (Set.toFinite _) fun i _ =>
      isOpen_lt (continuous_norm.comp (continuous_apply i)) continuous_const
  have h2 : IsOpen {z : Fin n → ℂ | ‖z j‖ < ρ j * (3 / 4)} :=
    isOpen_lt (continuous_norm.comp (continuous_apply j)) continuous_const
  have h3 : IsOpen {z : Fin n → ℂ | ∀ i : Fin n, (j : ℕ) < (i : ℕ) → ‖z i‖ < chainD n (j:ℕ) * ρ i} := by
    have hset : {z : Fin n → ℂ | ∀ i : Fin n, (j : ℕ) < (i : ℕ) → ‖z i‖ < chainD n (j:ℕ) * ρ i}
        = ⋂ i ∈ {i : Fin n | (j : ℕ) < (i : ℕ)}, {z : Fin n → ℂ | ‖z i‖ < chainD n (j:ℕ) * ρ i} := by
      ext z; simp [Set.mem_iInter]
    rw [hset]
    exact Set.Finite.isOpen_biInter (Set.toFinite _) fun i _ =>
      isOpen_lt (continuous_norm.comp (continuous_apply i)) continuous_const
  have h4 : cvInner n ρ j =
      {z : Fin n → ℂ | ∀ i : Fin n, (i : ℕ) < (j : ℕ) → ‖z i‖ < chainC n (j:ℕ) * ρ i} ∩
      {z : Fin n → ℂ | ‖z j‖ < ρ j * (3 / 4)} ∩
      {z : Fin n → ℂ | ∀ i : Fin n, (j : ℕ) < (i : ℕ) → ‖z i‖ < chainD n (j:ℕ) * ρ i} := by
    ext z; simp only [mem_cvInner, mem_inter_iff, Set.mem_ofPred_eq]; tauto
  rw [h4]; exact (h1.inter h2).inter h3

/-- The flat region of the `j`-th step in the logarithmic chart: the transverse point set. -/
def cvFlat (n : ℕ) (ρ : Fin n → ℝ) (j : Fin n) : Set (Fin n → ℂ) :=
  {z | (∀ i : Fin n, (i : ℕ) < (j : ℕ) → ‖z i‖ < chainC n (j : ℕ) * ρ i) ∧
       (ρ j / 2 < ‖z j‖ ∧ ‖z j‖ < 3 * ρ j) ∧
       (∀ i : Fin n, (j : ℕ) < (i : ℕ) → ‖z i‖ < chainD n (j : ℕ) * ρ i)}

@[simp] lemma mem_cvFlat {j : Fin n} {z : Fin n → ℂ} :
    z ∈ cvFlat n ρ j ↔
      (∀ i : Fin n, (i : ℕ) < (j : ℕ) → ‖z i‖ < chainC n (j : ℕ) * ρ i) ∧
      (ρ j / 2 < ‖z j‖ ∧ ‖z j‖ < 3 * ρ j) ∧
      (∀ i : Fin n, (j : ℕ) < (i : ℕ) → ‖z i‖ < chainD n (j : ℕ) * ρ i) := Iff.rfl

lemma isOpen_cvFlat (hρ : ∀ i, 0 < ρ i) (j : Fin n) : IsOpen (cvFlat n ρ j) := by
  have h1 : IsOpen {z : Fin n → ℂ |
      ∀ i : Fin n, (i : ℕ) < (j : ℕ) → ‖z i‖ < chainC n (j:ℕ) * ρ i} := by
    have hset : {z : Fin n → ℂ |
        ∀ i : Fin n, (i : ℕ) < (j : ℕ) → ‖z i‖ < chainC n (j:ℕ) * ρ i}
        = ⋂ i ∈ {i : Fin n | (i : ℕ) < (j : ℕ)},
            {z : Fin n → ℂ | ‖z i‖ < chainC n (j:ℕ) * ρ i} := by
      ext z; simp [Set.mem_iInter]
    rw [hset]
    exact Set.Finite.isOpen_biInter (Set.toFinite _) fun i _ =>
      isOpen_lt (continuous_norm.comp (continuous_apply i)) continuous_const
  have h2 : IsOpen {z : Fin n → ℂ | ρ j / 2 < ‖z j‖ ∧ ‖z j‖ < 3 * ρ j} :=
    (isOpen_lt continuous_const (continuous_norm.comp (continuous_apply j))).inter
      (isOpen_lt (continuous_norm.comp (continuous_apply j)) continuous_const)
  have h3 : IsOpen {z : Fin n → ℂ |
      ∀ i : Fin n, (j : ℕ) < (i : ℕ) → ‖z i‖ < chainD n (j:ℕ) * ρ i} := by
    have hset : {z : Fin n → ℂ |
        ∀ i : Fin n, (j : ℕ) < (i : ℕ) → ‖z i‖ < chainD n (j:ℕ) * ρ i}
        = ⋂ i ∈ {i : Fin n | (j : ℕ) < (i : ℕ)},
            {z : Fin n → ℂ | ‖z i‖ < chainD n (j:ℕ) * ρ i} := by
      ext z; simp [Set.mem_iInter]
    rw [hset]
    exact Set.Finite.isOpen_biInter (Set.toFinite _) fun i _ =>
      isOpen_lt (continuous_norm.comp (continuous_apply i)) continuous_const
  have h4 : cvFlat n ρ j =
      {z : Fin n → ℂ | ∀ i : Fin n, (i : ℕ) < (j : ℕ) → ‖z i‖ < chainC n (j:ℕ) * ρ i} ∩
      {z : Fin n → ℂ | ρ j / 2 < ‖z j‖ ∧ ‖z j‖ < 3 * ρ j} ∩
      {z : Fin n → ℂ | ∀ i : Fin n, (j : ℕ) < (i : ℕ) → ‖z i‖ < chainD n (j:ℕ) * ρ i} := by
    ext z; simp only [mem_cvFlat, mem_inter_iff, Set.mem_ofPred_eq]; tauto
  rw [h4]; exact (h1.inter h2).inter h3

/-! ## The structural containments -/

/-- The chain region contains the `stepRegion` of the (existing) one-step estimate. -/
lemma stepRegion_subset_cvReg (hρ : ∀ i, 0 < ρ i) (j : ℕ) :
    stepRegion n ρ j ⊆ cvReg n ρ j := by
  intro z hz
  rw [mem_stepRegion] at hz
  obtain ⟨h1, h2⟩ := hz
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have hlt := h1 i hi
    have hc : (1 : ℝ) < chainC n j := chainC_gt_one n j
    have hp := hρ i
    nlinarith
  · have hle := h2 i hi
    have hd : (2 : ℝ) ≤ chainD n j := chainD_ge_two n j
    have hp := hρ i
    nlinarith

/-- The one-sided region of the `j`-th step is contained in the level-`(j+1)` chain region. -/
lemma oneSidedRegion_subset_cvReg_succ (hρ : ∀ i, 0 < ρ i) (j : ℕ) :
    oneSidedRegion n ρ j ⊆ cvReg n ρ (j + 1) := by
  intro z hz
  rw [mem_oneSidedRegion] at hz
  obtain ⟨h1, h2⟩ := hz
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have hle : (i : ℕ) ≤ j := by omega
    have hle' := h1 i hle
    have hc : (1 : ℝ) < chainC n (j + 1) := chainC_gt_one n (j + 1)
    have hp := hρ i
    nlinarith
  · have hlt : j < (i : ℕ) := by omega
    have hlt' := h2 i hlt
    have hd : (2 : ℝ) < chainD n (j + 1) := chainD_gt_two n (j + 1) (by omega)
    have hp := hρ i
    nlinarith

/-- The level-`j` chain region with the `j`-th coordinate inside the identity region is
contained in the level-`(j+1)` chain region. -/
lemma cvReg_inter_le_subset_cvReg_succ (hρ : ∀ i, 0 < ρ i) (j : Fin n) :
    cvReg n ρ (j : ℕ) ∩ {z : Fin n → ℂ | ‖z j‖ ≤ ρ j} ⊆ cvReg n ρ ((j : ℕ) + 1) := by
  intro z hz
  obtain ⟨hzr, hzj⟩ := hz
  have hzj' : ‖z j‖ ≤ ρ j := hzj
  obtain ⟨h1, h2⟩ := hzr
  rw [mem_cvReg]
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | heq
    · have hlt' := h1 i hlt
      have hmono : chainC n (j : ℕ) ≤ chainC n ((j : ℕ) + 1) := chainC_mono n (Nat.le_succ _)
      have hp := hρ i
      nlinarith
    · have hji : i = j := Fin.ext heq
      rw [hji]
      have hc : (1 : ℝ) < chainC n ((j : ℕ) + 1) := chainC_gt_one n ((j : ℕ) + 1)
      have hp := hρ j
      nlinarith
  · have hge : (j : ℕ) ≤ (i : ℕ) := by omega
    have hlt' := h2 i hge
    have hmono : chainD n (j : ℕ) ≤ chainD n ((j : ℕ) + 1) := chainD_mono n (Nat.le_succ _)
    have hp := hρ i
    nlinarith

/-- The flat fibre map sends the flat region into the next level's chain region. -/
lemma flatPoint_mapsTo_cvReg (hρ : ∀ i, 0 < ρ i) (j : Fin n) :
    Set.MapsTo (flatPoint n ρ j) (cvFlat n ρ j ×ˢ {t : ℝ | 0 ≤ t}) (cvReg n ρ ((j : ℕ) + 1)) := by
  intro p hp
  obtain ⟨hpw, hpt⟩ := Set.mem_prod.mp hp
  have hpt' : (0 : ℝ) ≤ p.2 := hpt
  rw [mem_cvFlat] at hpw
  obtain ⟨h1, ⟨hj1, hj2⟩, h3⟩ := hpw
  rw [mem_cvReg]
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | heq
    · rw [flatPoint, Function.update_apply,
        if_neg (fun h : i = j => (ne_of_lt hlt) (congrArg Fin.val h))]
      have hlt' := h1 i hlt
      have hmono : chainC n (j : ℕ) ≤ chainC n ((j : ℕ) + 1) := chainC_mono n (Nat.le_succ _)
      have hp' := hρ i
      nlinarith
    · have hji : i = j := Fin.ext heq
      rw [hji, flatPoint, Function.update_self]
      have hnorm : ‖((ρ j * Real.exp (-p.2) / ‖p.1 j‖ : ℝ) : ℂ) * p.1 j‖
          = ρ j * Real.exp (-p.2) := by
        have hpos : 0 < ‖p.1 j‖ := by linarith [hρ j, hj1]
        rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div,
          abs_of_pos (mul_pos (hρ j) (Real.exp_pos _)), abs_of_pos hpos,
          div_mul_cancel₀ _ (ne_of_gt hpos)]
      rw [hnorm]
      have hexp : Real.exp (-p.2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have hc : (1 : ℝ) < chainC n ((j : ℕ) + 1) := chainC_gt_one n ((j : ℕ) + 1)
      nlinarith [hρ j, Real.exp_pos (-p.2)]
  · rw [flatPoint, Function.update_apply,
      if_neg (fun h : i = j => (ne_of_lt (by omega : (j : ℕ) < (i : ℕ))) (congrArg Fin.val h).symm)]
    have hlt' := h3 i (by omega)
    have hmono : chainD n (j : ℕ) ≤ chainD n ((j : ℕ) + 1) := chainD_mono n (Nat.le_succ _)
    have hp' := hρ i
    nlinarith

/-- The annulus of the `j`-th step is contained in the flat region (the chart's first
component is the point itself). -/
lemma cvAnn_subset_cvFlat (hρ : ∀ i, 0 < ρ i) (j : Fin n) (δ : ℝ)
    (hδ : Real.exp δ < 3) :
    cvAnn n ρ j δ ∩ {z : Fin n → ℂ | ρ j ≤ ‖z j‖} ⊆ cvFlat n ρ j := by
  intro z hz
  obtain ⟨hza, hzj⟩ := hz
  have hzj' : ρ j ≤ ‖z j‖ := hzj
  rw [mem_cvAnn] at hza
  obtain ⟨h1, ⟨hj1, hj2⟩, h3⟩ := hza
  rw [mem_cvFlat]
  refine ⟨h1, ⟨by linarith, ?_⟩, h3⟩
  have hpos : 0 < ρ j := hρ j
  calc ‖z j‖ < ρ j * Real.exp δ := hj2
    _ < ρ j * 3 := mul_lt_mul_of_pos_left hδ hpos
    _ = 3 * ρ j := by ring

/-- The chain region at level `0` is the polydisc of radius `2`. -/
lemma cvReg_zero (n : ℕ) (ρ : Fin n → ℝ) : cvReg n ρ 0 = pd n ρ 2 := by
  ext z
  rw [mem_cvReg, mem_pd]
  constructor
  · intro h i
    simpa [chainD] using h.2 i (Nat.zero_le _)
  · intro h
    exact ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => by simpa [chainD] using h i⟩

/-- The chain region at level `n` is the polydisc of radius `chainC n n`. -/
lemma cvReg_last (n : ℕ) (ρ : Fin n → ℝ) : cvReg n ρ n = pd n ρ (chainC n n) := by
  ext z
  rw [mem_cvReg, mem_pd]
  constructor
  · intro h i
    simpa using h.1 i i.isLt
  · intro h
    refine ⟨fun i hi => by simpa using h i, fun i hi => ?_⟩
    exact absurd hi (not_le.mpr i.isLt)

/-- The region `cvReg n ρ j` is contained in the level-`n` region's polydisc, hence in `pd3`. -/
lemma cvReg_subset_pd3 (hρ : ∀ i, 0 < ρ i) {j : ℕ} (hj : j ≤ n) :
    cvReg n ρ j ⊆ pd n ρ 3 := by
  intro z hz
  rw [mem_cvReg] at hz
  rw [mem_pd]
  intro i
  rcases lt_or_ge (i : ℕ) j with hlt | hge
  · have h := hz.1 i hlt
    have hc := chainC_lt_three n j hj
    nlinarith [hρ i]
  · have h := hz.2 i hge
    have hd := chainD_lt_three n j hj
    nlinarith [hρ i]

lemma cvReg_last_subset_pd3 (n : ℕ) (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i) :
    cvReg n ρ n ⊆ pd n ρ 3 :=
  cvReg_subset_pd3 (n := n) (ρ := ρ) hρ le_rfl

end Work.NN.Final
