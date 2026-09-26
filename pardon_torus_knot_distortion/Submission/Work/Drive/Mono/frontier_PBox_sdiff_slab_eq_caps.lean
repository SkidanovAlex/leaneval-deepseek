import Mathlib
import Submission.Work.Drive.Mono.SlabCaps

/-!
# The frontier of the box minus the tilted slab is the union of the frontiers of the two caps

Let `PBox s c σ` be Pardon's open box and `tiltedSlabClosed a v h` the closed slab
`{y | |⟪v,y⟫ - a| ≤ h}` (`0 < h`, `v ≠ 0`).  Removing the slab from the box cuts the box into the
two *caps*

`slabCapPlus  = PBox ∩ {a + h ≤ ⟪v,·⟫}`  and  `slabCapMinus = PBox ∩ {⟪v,·⟫ ≤ a - h}`,

whose union's *closure* is the closure of `PBox \ slab` while their interiors are exactly
`PBox ∩ {a + h < ⟪v,·⟫}` and `PBox ∩ {⟪v,·⟫ < a - h}`.  Hence the frontier of `PBox \ slab` is the
union of the frontiers of the two caps.

The three ingredients are: `interior` of a closed half-space cut by a **nonzero** functional is the
open half-space (this is where `v ≠ 0` enters), the box is open, and the two caps lie in the two
*disjoint* closed half-spaces (`0 < h`), so the elementary set identity
`(A ∪ B) \ (P ∪ Q) = (A \ P) ∪ (B \ Q)` (valid when `A ∩ Q = ∅` and `B ∩ P = ∅`) applies.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion Set
open scoped ENNReal

noncomputable section

/-- The **interior of the closed half-space** `{y | c ≤ ⟪v,y⟫}` cut out by a nonzero functional
`v ≠ 0` is the open half-space `{y | c < ⟪v,y⟫}`. -/
private lemma interior_le_inner {v : R3} (hv : v ≠ 0) (c : ℝ) :
    interior {y : R3 | c ≤ inner ℝ v y} = {y : R3 | c < inner ℝ v y} := by
  have hcl : Continuous fun y : R3 => inner ℝ v y := continuous_const.inner continuous_id
  refine Subset.antisymm ?_ ?_
  · intro y hy
    have hyS : c ≤ inner ℝ v y := by
      have h := interior_subset hy
      exact h
    by_contra hcon
    have hcon' : inner ℝ v y ≤ c := not_lt.mp hcon
    have hyc : inner ℝ v y = c := le_antisymm hcon' hyS
    obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hy)
    set t : ℝ := δ / (2 * (‖v‖ + 1)) with htdef
    have htpos : 0 < t := by rw [htdef]; positivity
    have htt : t * ‖v‖ < δ := by
      have hle : t * ‖v‖ ≤ t * (‖v‖ + 1) :=
        mul_le_mul_of_nonneg_left (show ‖v‖ ≤ ‖v‖ + 1 by linarith) (le_of_lt htpos)
      have h2 : t * (‖v‖ + 1) = δ / 2 := by rw [htdef]; field_simp
      linarith
    have hmem : y + (-t) • v ∈ Metric.ball y δ := by
      rw [Metric.mem_ball, dist_eq_norm]
      have hsub : y + (-t) • v - y = (-t) • v := by module
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos htpos]
      exact htt
    have hz := hδ hmem
    have hzS : c ≤ inner ℝ v (y + (-t) • v) := by
      have h := interior_subset hz
      exact h
    rw [inner_add_right, inner_smul_right, hyc, neg_mul] at hzS
    have hpos : 0 < t * inner ℝ v v := mul_pos htpos (real_inner_self_pos.mpr hv)
    linarith
  · intro y hy
    have hopen : IsOpen {y : R3 | c < inner ℝ v y} := isOpen_lt continuous_const hcl
    have hsub : {y : R3 | c < inner ℝ v y} ⊆ {y : R3 | c ≤ inner ℝ v y} := by
      intro z hz
      simp only [Set.mem_ofPred_eq] at hz ⊢
      exact le_of_lt hz
    exact interior_mono hsub (by rw [hopen.interior_eq]; exact hy)

/-- The **interior of the closed half-space** `{y | ⟪v,y⟫ ≤ c}` cut out by a nonzero functional
`v ≠ 0` is the open half-space `{y | ⟪v,y⟫ < c}`. -/
private lemma interior_inner_le {v : R3} (hv : v ≠ 0) (c : ℝ) :
    interior {y : R3 | inner ℝ v y ≤ c} = {y : R3 | inner ℝ v y < c} := by
  have hcl : Continuous fun y : R3 => inner ℝ v y := continuous_const.inner continuous_id
  refine Subset.antisymm ?_ ?_
  · intro y hy
    have hyS : inner ℝ v y ≤ c := by
      have h := interior_subset hy
      exact h
    by_contra hcon
    have hcon' : c ≤ inner ℝ v y := le_of_not_gt hcon
    have hyc : inner ℝ v y = c := le_antisymm hyS hcon'
    obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hy)
    set t : ℝ := δ / (2 * (‖v‖ + 1)) with htdef
    have htpos : 0 < t := by rw [htdef]; positivity
    have htt : t * ‖v‖ < δ := by
      have hle : t * ‖v‖ ≤ t * (‖v‖ + 1) :=
        mul_le_mul_of_nonneg_left (show ‖v‖ ≤ ‖v‖ + 1 by linarith) (le_of_lt htpos)
      have h2 : t * (‖v‖ + 1) = δ / 2 := by rw [htdef]; field_simp
      linarith
    have hmem : y + t • v ∈ Metric.ball y δ := by
      rw [Metric.mem_ball, dist_eq_norm]
      have hsub : y + t • v - y = t • v := by module
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
      exact htt
    have hz := hδ hmem
    have hzS : inner ℝ v (y + t • v) ≤ c := by
      have h := interior_subset hz
      exact h
    rw [inner_add_right, inner_smul_right, hyc] at hzS
    have hpos : 0 < t * inner ℝ v v := mul_pos htpos (real_inner_self_pos.mpr hv)
    linarith
  · intro y hy
    have hopen : IsOpen {y : R3 | inner ℝ v y < c} := isOpen_lt hcl continuous_const
    have hsub : {y : R3 | inner ℝ v y < c} ⊆ {y : R3 | inner ℝ v y ≤ c} := by
      intro z hz
      simp only [Set.mem_ofPred_eq] at hz ⊢
      exact le_of_lt hz
    exact interior_mono hsub (by rw [hopen.interior_eq]; exact hy)

/-- **The interior of the upper cap** is the open upper half of the box. -/
private lemma interior_slabCapPlus (v : R3) (hv : v ≠ 0) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (a h : ℝ) :
    interior (slabCapPlus s c σ a h v)
      = {y : R3 | y ∈ Submission.PBox s c σ ∧ a + h < inner ℝ v y} := by
  have hunion : slabCapPlus s c σ a h v
      = Submission.PBox s c σ ∩ {y : R3 | a + h ≤ inner ℝ v y} := rfl
  rw [hunion, interior_inter, (Work.Topology.SphereSlicing.isOpen_PBox s c σ).interior_eq,
    interior_le_inner hv (a + h)]
  ext y; simp

/-- **The interior of the lower cap** is the open lower half of the box. -/
private lemma interior_slabCapMinus (v : R3) (hv : v ≠ 0) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (a h : ℝ) :
    interior (slabCapMinus s c σ a h v)
      = {y : R3 | y ∈ Submission.PBox s c σ ∧ inner ℝ v y < a - h} := by
  have hunion : slabCapMinus s c σ a h v
      = Submission.PBox s c σ ∩ {y : R3 | inner ℝ v y ≤ a - h} := rfl
  rw [hunion, interior_inter, (Work.Topology.SphereSlicing.isOpen_PBox s c σ).interior_eq,
    interior_inner_le hv (a - h)]
  ext y; simp

/-- **The upper cap is contained in the closure of its interior.**  The point is that from a point of
the cap one can move a little in the direction `v` (staying inside the open box, since its plan
coordinate is only increased by `t·‖v‖² > 0`), which strictly increases `⟪v,·⟫`. -/
private lemma closure_interior_slabCapPlus (v : R3) (hv : v ≠ 0) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (a h : ℝ) :
    closure (interior (slabCapPlus s c σ a h v)) = closure (slabCapPlus s c σ a h v) := by
  refine le_antisymm (closure_mono interior_subset) ?_
  apply closure_minimal ?_ isClosed_closure
  intro y hy
  simp only [slabCapPlus, Set.mem_ofPred_eq] at hy
  obtain ⟨hyBox, hyf⟩ := hy
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ :=
    Metric.mem_nhds_iff.mp ((Work.Topology.SphereSlicing.isOpen_PBox s c σ).mem_nhds hyBox)
  set t : ℝ := min δ ε / (2 * (‖v‖ + 1)) with htdef
  have htpos : 0 < t := by rw [htdef]; positivity
  have htM : t * (‖v‖ + 1) = min δ ε / 2 := by rw [htdef]; field_simp
  have htb : t * ‖v‖ ≤ min δ ε / 2 := by
    have h := mul_le_mul_of_nonneg_left (show ‖v‖ ≤ ‖v‖ + 1 by linarith) (le_of_lt htpos)
    rw [htM] at h
    exact h
  have hdist : dist y (y + t • v) = t * ‖v‖ := by
    rw [dist_eq_norm]
    have hsub : y - (y + t • v) = -(t • v) := by module
    rw [hsub, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
  refine ⟨y + t • v, ?_, ?_⟩
  · rw [interior_slabCapPlus v hv s c σ a h]
    simp only [Set.mem_ofPred_eq]
    refine ⟨?_, ?_⟩
    · apply hδ
      rw [Metric.mem_ball, dist_comm, hdist]
      have h2 : min δ ε ≤ δ := min_le_left _ _
      linarith
    · rw [inner_add_right, inner_smul_right]
      have hpos : 0 < t * inner ℝ v v := mul_pos htpos (real_inner_self_pos.mpr hv)
      linarith
  · rw [hdist]
    have h2 : min δ ε ≤ ε := min_le_right _ _
    linarith

/-- **The lower cap is contained in the closure of its interior.**  Here one moves in the direction
`-v`. -/
private lemma closure_interior_slabCapMinus (v : R3) (hv : v ≠ 0) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (a h : ℝ) :
    closure (interior (slabCapMinus s c σ a h v)) = closure (slabCapMinus s c σ a h v) := by
  refine le_antisymm (closure_mono interior_subset) ?_
  apply closure_minimal ?_ isClosed_closure
  intro y hy
  simp only [slabCapMinus, Set.mem_ofPred_eq] at hy
  obtain ⟨hyBox, hyf⟩ := hy
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ :=
    Metric.mem_nhds_iff.mp ((Work.Topology.SphereSlicing.isOpen_PBox s c σ).mem_nhds hyBox)
  set t : ℝ := min δ ε / (2 * (‖v‖ + 1)) with htdef
  have htpos : 0 < t := by rw [htdef]; positivity
  have htM : t * (‖v‖ + 1) = min δ ε / 2 := by rw [htdef]; field_simp
  have htb : t * ‖v‖ ≤ min δ ε / 2 := by
    have h := mul_le_mul_of_nonneg_left (show ‖v‖ ≤ ‖v‖ + 1 by linarith) (le_of_lt htpos)
    rw [htM] at h
    exact h
  have hdist : dist y (y + (-t) • v) = t * ‖v‖ := by
    rw [dist_eq_norm]
    have hsub : y - (y + (-t) • v) = t • v := by module
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
  refine ⟨y + (-t) • v, ?_, ?_⟩
  · rw [interior_slabCapMinus v hv s c σ a h]
    simp only [Set.mem_ofPred_eq]
    refine ⟨?_, ?_⟩
    · apply hδ
      rw [Metric.mem_ball, dist_comm, hdist]
      have h2 : min δ ε ≤ δ := min_le_left _ _
      linarith
    · rw [inner_add_right, inner_smul_right]
      have hpos : 0 < t * inner ℝ v v := mul_pos htpos (real_inner_self_pos.mpr hv)
      linarith
  · rw [hdist]
    have h2 : min δ ε ≤ ε := min_le_right _ _
    linarith

/-- The set identity `(A ∪ B) \ (P ∪ Q) = (A \ P) ∪ (B \ Q)`, valid when `A ∩ Q = ∅` and
`B ∩ P = ∅`. -/
private lemma sdiff_union_eq_union_sdiff {α : Type*} (A B P Q : Set α)
    (hAQ : Disjoint A Q) (hBP : Disjoint B P) :
    (A ∪ B) \ (P ∪ Q) = (A \ P) ∪ (B \ Q) := by
  rw [Set.disjoint_left] at hAQ hBP
  ext y
  constructor
  · intro hy
    rw [Set.mem_sdiff, Set.mem_union] at hy
    obtain ⟨hyAB, hyPQ⟩ := hy
    rcases hyAB with hyA | hyB
    · rw [Set.mem_union, Set.mem_sdiff]
      exact Or.inl ⟨hyA, fun hyP => hyPQ (Or.inl hyP)⟩
    · rw [Set.mem_union, Set.mem_sdiff]
      exact Or.inr ⟨hyB, fun hyQ => hyPQ (Or.inr hyQ)⟩
  · intro hy
    rw [Set.mem_union, Set.mem_sdiff] at hy
    rw [Set.mem_sdiff, Set.mem_union]
    rcases hy with ⟨hyA, hyP⟩ | ⟨hyB, hyQ⟩
    · refine ⟨Or.inl hyA, ?_⟩
      rintro (h | h)
      · exact hyP h
      · exact hAQ hyA h
    · refine ⟨Or.inr hyB, ?_⟩
      rintro (h | h)
      · exact hBP hyB h
      · exact hyQ h

/-- **The frontier of the box minus the closed tilted slab is the union of the frontiers of the two
caps.** -/
theorem frontier_PBox_sdiff_slab_eq_caps (s : ℝ) (c : LeanEval.KnotTheory.PardonDistortion.R3)
    (σ : Equiv.Perm (Fin 3)) (a h : ℝ) {v : LeanEval.KnotTheory.PardonDistortion.R3}
    (hh : 0 < h) (hv : v ≠ 0) :
    frontier (Submission.PBox s c σ \ Work.Drive.EpsForm.tiltedSlabClosed a v h) =
      frontier (Work.Drive.Mono.slabCapPlus s c σ a h v) ∪
        frontier (Work.Drive.Mono.slabCapMinus s c σ a h v) := by
  set P := slabCapPlus s c σ a h v with hP
  set Q := slabCapMinus s c σ a h v with hQ
  have hintP : interior P = {y : R3 | y ∈ Submission.PBox s c σ ∧ a + h < inner ℝ v y} := by
    rw [hP]; exact interior_slabCapPlus v hv s c σ a h
  have hintQ : interior Q = {y : R3 | y ∈ Submission.PBox s c σ ∧ inner ℝ v y < a - h} := by
    rw [hQ]; exact interior_slabCapMinus v hv s c σ a h
  have hclP : closure (interior P) = closure P := by
    rw [hP]; exact closure_interior_slabCapPlus v hv s c σ a h
  have hclQ : closure (interior Q) = closure Q := by
    rw [hQ]; exact closure_interior_slabCapMinus v hv s c σ a h
  have hU : Submission.PBox s c σ \ Work.Drive.EpsForm.tiltedSlabClosed a v h
      = interior P ∪ interior Q := by
    rw [hintP, hintQ]
    ext y
    constructor
    · intro hy
      rw [Set.mem_sdiff] at hy
      obtain ⟨hyBox, hySlab⟩ := hy
      have hySlab' : ¬ (|inner ℝ v y - a| ≤ h) := by
        simpa only [Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_ofPred_eq] using hySlab
      have hgt : h < |inner ℝ v y - a| := lt_of_not_ge hySlab'
      rcases lt_abs.mp hgt with h1 | h2
      · left
        simp only [Set.mem_ofPred_eq]
        exact ⟨hyBox, by linarith⟩
      · right
        simp only [Set.mem_ofPred_eq]
        exact ⟨hyBox, by linarith⟩
    · intro hy
      rcases hy with hy | hy
      · simp only [Set.mem_ofPred_eq] at hy
        obtain ⟨hyBox, hgt⟩ := hy
        refine ⟨hyBox, ?_⟩
        intro hle
        have hle' : |inner ℝ v y - a| ≤ h := by
          simpa only [Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_ofPred_eq] using hle
        have hlt' : h < |inner ℝ v y - a| := lt_abs.mpr (Or.inl (by linarith))
        linarith
      · simp only [Set.mem_ofPred_eq] at hy
        obtain ⟨hyBox, hlt⟩ := hy
        refine ⟨hyBox, ?_⟩
        intro hle
        have hle' : |inner ℝ v y - a| ≤ h := by
          simpa only [Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_ofPred_eq] using hle
        have hlt' : h < |inner ℝ v y - a| := lt_abs.mpr (Or.inr (by linarith))
        linarith
  rw [hU]
  have hUopen : IsOpen (interior P ∪ interior Q) := by
    rw [← hU]
    exact (Work.Topology.SphereSlicing.isOpen_PBox s c σ).sdiff
      (Work.Drive.EpsForm.isClosed_tiltedSlabClosed a v h)
  rw [hUopen.frontier_eq, closure_union, hclP, hclQ]
  have hfrontP : frontier P = closure P \ interior P := rfl
  have hfrontQ : frontier Q = closure Q \ interior Q := rfl
  rw [hfrontP, hfrontQ]
  have hcl : Continuous fun y : R3 => inner ℝ v y := continuous_const.inner continuous_id
  have hA : closure P ⊆ {y : R3 | a + h ≤ inner ℝ v y} := by
    rw [hP]
    apply closure_minimal _ (isClosed_le continuous_const hcl)
    intro y hy
    simp only [slabCapPlus, Set.mem_ofPred_eq] at hy
    exact hy.2
  have hB : closure Q ⊆ {y : R3 | inner ℝ v y ≤ a - h} := by
    rw [hQ]
    apply closure_minimal _ (isClosed_le hcl continuous_const)
    intro y hy
    simp only [slabCapMinus, Set.mem_ofPred_eq] at hy
    exact hy.2
  have hPi : interior P ⊆ {y : R3 | a + h ≤ inner ℝ v y} := by
    rw [hintP]
    intro y hy
    show a + h ≤ inner ℝ v y
    exact le_of_lt hy.2
  have hQi : interior Q ⊆ {y : R3 | inner ℝ v y ≤ a - h} := by
    rw [hintQ]
    intro y hy
    show inner ℝ v y ≤ a - h
    exact le_of_lt hy.2
  have hAQ : Disjoint (closure P) (interior Q) := by
    rw [Set.disjoint_left]
    intro y hyA hyQ
    have h1 := hA hyA
    have h2 := hQi hyQ
    simp only [Set.mem_ofPred_eq] at h1 h2
    linarith
  have hBP : Disjoint (closure Q) (interior P) := by
    rw [Set.disjoint_left]
    intro y hyB hyP
    have h1 := hB hyB
    have h2 := hPi hyP
    simp only [Set.mem_ofPred_eq] at h1 h2
    linarith
  exact sdiff_union_eq_union_sdiff (closure P) (closure Q) (interior P) (interior Q) hAQ hBP

end

end Work.Drive.Mono
