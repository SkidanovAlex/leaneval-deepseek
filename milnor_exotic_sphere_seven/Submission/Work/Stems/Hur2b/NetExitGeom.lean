import Mathlib
import Submission.Work.Stems.Hur2b.NetExit

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The net region and the radial exit point, as subsets of the square

This file relates the *offset* picture of `NetGeo.lean`/`NetExit.lean` to the *cell* picture:
`NetRegion = ⋃ k, netCell k` is exactly the image of `netOff` under `z ↦ c + z`, the exit point
`radialPoint z` of the ray in a nonzero direction `z` lies in the net region (and, on `∂D`, the
radial projection is the identity).
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2b

open Work.Stems.Cubical Work.Stems.Hur2

noncomputable section

/-- The clamping of a real number into `I`, read back in `ℝ`. -/
theorem clamp_val (r : ℝ) (h : r ∈ Set.Icc (0:ℝ) 1) : ((clamp r : unitInterval) : ℝ) = r :=
  congrArg Subtype.val (clamp_of_mem h)

/-- The coercion of `clamp`. -/
theorem clamp_coe_max (r : ℝ) : ((clamp r : unitInterval) : ℝ) = max 0 (min 1 r) := rfl

theorem offOf_eq (y : IC 2) (i : Fin 2) : offOf y i = (y i : ℝ) - 7/16 := rfl

theorem continuous_offOf (i : Fin 2) : Continuous fun z : IC 2 => offOf z i := by
  have h : (fun z : IC 2 => offOf z i) = fun z => ((z i : unitInterval) : ℝ) - 7/16 := by
    funext z; rw [offOf_eq]
  rw [h]
  exact (continuous_subtype_val.comp (continuous_apply i)).sub continuous_const

/-- The point with the offsets of `y` is `y`. -/
theorem ptOf_offOf (y : IC 2) : ptOf (offOf y) = y := by
  funext i
  apply Subtype.ext
  rw [ptOf_coe]
  have h := (y i).2
  rw [show 7/16 + offOf y i = (y i : ℝ) by rw [offOf_eq]; ring, clamp_val _ h]

/-- The clamp of a real number whose clamp lies in `[1/4,3/4]` is the number itself. -/
theorem clamp_eq_self_of_bounds {r : ℝ}
    (hlo : (1/4:ℝ) ≤ max 0 (min 1 r)) (hhi : max 0 (min 1 r) ≤ 3/4) :
    max 0 (min 1 r) = r := by
  have hm : min 1 r ≤ 3/4 := le_trans (le_max_right _ _) hhi
  have hpos : (0:ℝ) < min 1 r := by
    by_contra hc
    push_neg at hc
    rw [max_eq_left hc] at hlo
    norm_num at hlo
  have hr1 : r ≤ 1 := by
    by_contra hc
    push_neg at hc
    rw [min_eq_left hc.le] at hm
    linarith
  rw [max_eq_right hpos.le, min_eq_right hr1]

/-- **The net region is the union of the belt and the column.** -/
theorem net_region_eq (y : IC 2) : y ∈ NetRegion ↔ offOf y ∈ netOff := by
  constructor
  · intro hy
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hy
    fin_cases k
    · exact Or.inl (by
        simp only [netCell, gridCell, Set.mem_ofPred_eq] at hk
        simp only [beltOff, Set.mem_ofPred_eq, offOf_eq]
        push_cast at hk ⊢
        exact ⟨by linarith [hk.1], by linarith [hk.2.1], by linarith [hk.2.2.1],
          by linarith [hk.2.2.2]⟩)
    · exact Or.inl (by
        simp only [netCell, gridCell, Set.mem_ofPred_eq] at hk
        simp only [beltOff, Set.mem_ofPred_eq, offOf_eq]
        push_cast at hk ⊢
        exact ⟨by linarith [hk.1], by linarith [hk.2.1], by linarith [hk.2.2.1],
          by linarith [hk.2.2.2]⟩)
    · exact Or.inl (by
        simp only [netCell, gridCell, Set.mem_ofPred_eq] at hk
        simp only [beltOff, Set.mem_ofPred_eq, offOf_eq]
        push_cast at hk ⊢
        exact ⟨by linarith [hk.1], by linarith [hk.2.1], by linarith [hk.2.2.1],
          by linarith [hk.2.2.2]⟩)
    · exact Or.inl (by
        simp only [netCell, gridCell, Set.mem_ofPred_eq] at hk
        simp only [beltOff, Set.mem_ofPred_eq, offOf_eq]
        push_cast at hk ⊢
        exact ⟨by linarith [hk.1], by linarith [hk.2.1], by linarith [hk.2.2.1],
          by linarith [hk.2.2.2]⟩)
    · exact Or.inr (by
        simp only [netCell, gridCell, Set.mem_ofPred_eq] at hk
        simp only [colOff, Set.mem_ofPred_eq, offOf_eq]
        push_cast at hk ⊢
        exact ⟨by linarith [hk.1], by linarith [hk.2.1], by linarith [hk.2.2.1],
          by linarith [hk.2.2.2]⟩)
    · exact Or.inr (by
        simp only [netCell, gridCell, Set.mem_ofPred_eq] at hk
        simp only [colOff, Set.mem_ofPred_eq, offOf_eq]
        push_cast at hk ⊢
        exact ⟨by linarith [hk.1], by linarith [hk.2.1], by linarith [hk.2.2.1],
          by linarith [hk.2.2.2]⟩)
  · intro hy
    simp only [netOff, beltOff, colOff, Set.mem_union, Set.mem_ofPred_eq, offOf_eq] at hy
    simp only [NetRegion, Set.mem_iUnion]
    rcases hy with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · push_cast at h1 h2 h3 h4
      rcases le_or_gt (y 0 : ℝ) (3/8) with c0 | c0
      · exact ⟨0, by
          simp only [netCell, gridCell, Set.mem_ofPred_eq]; push_cast
          exact ⟨by linarith, by linarith, by linarith, by linarith⟩⟩
      · rcases le_or_gt (y 0 : ℝ) (1/2) with c1 | c1
        · exact ⟨1, by
            simp only [netCell, gridCell, Set.mem_ofPred_eq]; push_cast
            exact ⟨by linarith, by linarith, by linarith, by linarith⟩⟩
        · rcases le_or_gt (y 0 : ℝ) (5/8) with c2 | c2
          · exact ⟨2, by
              simp only [netCell, gridCell, Set.mem_ofPred_eq]; push_cast
              exact ⟨by linarith, by linarith, by linarith, by linarith⟩⟩
          · exact ⟨3, by
              simp only [netCell, gridCell, Set.mem_ofPred_eq]; push_cast
              exact ⟨by linarith, by linarith, by linarith, by linarith⟩⟩
    · push_cast at h1 h2 h3 h4
      rcases le_or_gt (y 1 : ℝ) (3/8) with c0 | c0
      · exact ⟨4, by
          simp only [netCell, gridCell, Set.mem_ofPred_eq]; push_cast
          exact ⟨by linarith, by linarith, by linarith, by linarith⟩⟩
      · rcases le_or_gt (1/2 : ℝ) (y 1) with c1 | c1
        · exact ⟨5, by
            simp only [netCell, gridCell, Set.mem_ofPred_eq]; push_cast
            exact ⟨by linarith, by linarith, by linarith, by linarith⟩⟩
        · rcases le_or_gt (y 0 : ℝ) (1/2) with c2 | c2
          · exact ⟨1, by
              simp only [netCell, gridCell, Set.mem_ofPred_eq]; push_cast
              exact ⟨by linarith, by linarith, by linarith, by linarith⟩⟩
          · exact ⟨2, by
              simp only [netCell, gridCell, Set.mem_ofPred_eq]; push_cast
              exact ⟨by linarith, by linarith, by linarith, by linarith⟩⟩

/-- Every point of the net region lies in the box `[1/4,3/4] × [1/4,5/8]`. -/
theorem net_region_bounds {y : IC 2} (hy : y ∈ NetRegion) :
    1/4 ≤ (y 0 : ℝ) ∧ (y 0 : ℝ) ≤ 3/4 ∧ 1/4 ≤ (y 1 : ℝ) ∧ (y 1 : ℝ) ≤ 5/8 := by
  have h := (net_region_eq y).mp hy
  simp only [netOff, beltOff, colOff, Set.mem_union, Set.mem_ofPred_eq, offOf_eq] at h
  rcases h with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ <;>
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The coordinates of the exit point: the clamp is inactive. -/
theorem offOf_radialPoint (z : Fin 2 → ℝ) : offOf (radialPoint z) = rayOff z := by
  have hray : ∀ i, rayOff z i ∈ Set.Icc (-3/16) (5/16) := by
    rcases eq_or_ne z 0 with hz | hz
    · subst hz
      intro i
      have h0 : rayOff 0 = 0 := by
        funext j
        simp [rayOff, exitScale, Mmin, MBelt, MCol, nu, nuB0, nuB1, nuC0, nuC1]
      rw [h0]
      norm_num
    · have h := rayOff_mem_netOff hz
      intro i
      rcases (show i = 0 ∨ i = 1 from by fin_cases i <;> simp) with hi | hi
      · subst hi
        rcases h with h | h
        · exact ⟨h.1, h.2.1⟩
        · exact ⟨by linarith [h.1], by linarith [h.2.1]⟩
      · subst hi
        rcases h with h | h
        · exact ⟨by linarith [h.2.2.1], by linarith [h.2.2.2]⟩
        · exact ⟨by linarith [h.2.2.1], by linarith [h.2.2.2]⟩
  funext i
  rw [offOf_eq]
  rw [show ((radialPoint z) i : unitInterval) = ptOf (rayOff z) i from rfl, ptOf_coe]
  have h0 := hray 0
  have h1 := hray 1
  have hb : (0:ℝ) ≤ 7/16 + rayOff z i ∧ 7/16 + rayOff z i ≤ 1 := by
    rcases (show i = 0 ∨ i = 1 from by fin_cases i <;> simp) with h | h
    · subst h; exact ⟨by linarith [h0.1], by linarith [h0.2]⟩
    · subst h; exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
  rw [clamp_val _ hb]
  ring

/-- The exit point in a nonzero direction lies in the net region. -/
theorem radialPoint_mem_region {z : Fin 2 → ℝ} (hz : z ≠ 0) : radialPoint z ∈ NetRegion :=
  (net_region_eq _).mpr (by rw [offOf_radialPoint]; exact rayOff_mem_netOff hz)

/-- If the offset lies in the net region, the reciprocal exit scale is at most `1`. -/
theorem Mmin_le_one_of_mem {ζ : Fin 2 → ℝ} (h : ζ ∈ netOff) : Mmin ζ ≤ 1 := by
  have h1 : (fun i => (1:ℝ) * ζ i) ∈ netOff := by simpa using h
  have h2 := (ray_mem_netOff (z := ζ) (t := 1) (by norm_num)).mp h1
  simpa using h2

/-- The open belt. -/
def openBeltSet : Set (IC 2) :=
  {z | -3/16 < offOf z 0 ∧ offOf z 0 < 5/16 ∧ -1/16 < offOf z 1 ∧ offOf z 1 < 1/16}

/-- The open column. -/
def openColSet : Set (IC 2) :=
  {z | -1/16 < offOf z 0 ∧ offOf z 0 < 1/16 ∧ -3/16 < offOf z 1 ∧ offOf z 1 < 3/16}

theorem isOpen_openBeltSet : IsOpen openBeltSet := by
  have h : openBeltSet = {z : IC 2 | (-3/16:ℝ) < offOf z 0} ∩ {z : IC 2 | offOf z 0 < 5/16} ∩
      {z : IC 2 | (-1/16:ℝ) < offOf z 1} ∩ {z : IC 2 | offOf z 1 < 1/16} := by
    ext z; simp only [openBeltSet, Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
  rw [h]
  exact IsOpen.inter (IsOpen.inter (IsOpen.inter
    (isOpen_lt continuous_const (continuous_offOf 0))
    (isOpen_lt (continuous_offOf 0) continuous_const))
    (isOpen_lt continuous_const (continuous_offOf 1)))
    (isOpen_lt (continuous_offOf 1) continuous_const)

theorem isOpen_openColSet : IsOpen openColSet := by
  have h : openColSet = {z : IC 2 | (-1/16:ℝ) < offOf z 0} ∩ {z : IC 2 | offOf z 0 < 1/16} ∩
      {z : IC 2 | (-3/16:ℝ) < offOf z 1} ∩ {z : IC 2 | offOf z 1 < 3/16} := by
    ext z; simp only [openColSet, Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
  rw [h]
  exact IsOpen.inter (IsOpen.inter (IsOpen.inter
    (isOpen_lt continuous_const (continuous_offOf 0))
    (isOpen_lt (continuous_offOf 0) continuous_const))
    (isOpen_lt continuous_const (continuous_offOf 1)))
    (isOpen_lt (continuous_offOf 1) continuous_const)

theorem openBeltSet_subset_interior : openBeltSet ⊆ interior NetRegion := by
  refine interior_maximal (fun z hz => ?_) isOpen_openBeltSet
  rw [net_region_eq]
  exact Or.inl ⟨le_of_lt hz.1, le_of_lt hz.2.1, le_of_lt hz.2.2.1, le_of_lt hz.2.2.2⟩

theorem openColSet_subset_interior : openColSet ⊆ interior NetRegion := by
  refine interior_maximal (fun z hz => ?_) isOpen_openColSet
  rw [net_region_eq]
  exact Or.inr ⟨le_of_lt hz.1, le_of_lt hz.2.1, le_of_lt hz.2.2.1, le_of_lt hz.2.2.2⟩

theorem offOf_netCentre (i : Fin 2) : offOf netCentre i = 0 := by
  rw [offOf_eq, netCentre_coe]; norm_num

theorem netCentre_mem_interior : netCentre ∈ interior NetRegion :=
  openBeltSet_subset_interior ⟨by rw [offOf_netCentre]; norm_num, by rw [offOf_netCentre]; norm_num,
    by rw [offOf_netCentre]; norm_num, by rw [offOf_netCentre]; norm_num⟩

theorem offOf_eq_zero_iff {y : IC 2} : offOf y = 0 ↔ y = netCentre := by
  constructor
  · intro h
    funext i
    apply Subtype.ext
    have := congrFun h i
    simp only [offOf, Pi.zero_apply] at this
    rw [netCentre_coe]
    linarith
  · intro h
    subst h
    funext i
    exact offOf_netCentre i

/-- **On `∂D` the exit point is the point itself**: the reciprocal exit scale is `1`. -/
theorem Mmin_eq_one_of_mem_NetBdy {y : IC 2} (hy : y ∈ NetBdy) : Mmin (offOf y) = 1 := by
  have hmem : y ∈ NetRegion := hy.1
  have hnot : y ∉ interior NetRegion := hy.2
  have hoff : offOf y ∈ netOff := (net_region_eq y).mp hmem
  have hoff0 : offOf y ≠ 0 := by
    intro h
    exact hnot (offOf_eq_zero_iff.mp h ▸ netCentre_mem_interior)
  refine le_antisymm (Mmin_le_one_of_mem hoff) ?_
  by_contra hcon
  push_neg at hcon
  set s : ℝ := Mmin (offOf y) with hs
  have hs0 : 0 < s := by rw [hs]; exact Mmin_pos hoff0
  have hs1 : s < 1 := by rw [hs]; exact hcon
  have hray_eq : rayOff (offOf y) = fun i => exitScale (offOf y) * offOf y i := rfl
  have hscale : exitScale (offOf y) * s = 1 := by
    rw [exitScale, one_div, ← hs]
    exact inv_mul_cancel₀ (ne_of_gt hs0)
  have hy_eq : y = ptOf (fun i => s * rayOff (offOf y) i) := by
    have h : offOf y = fun i => s * rayOff (offOf y) i := by
      funext i
      rw [rayOff, ← mul_assoc, mul_comm s (exitScale (offOf y)), hscale, one_mul]
    exact (ptOf_offOf y).symm.trans (congrArg ptOf h)
  have hy_seg : ∀ i, (y i : ℝ) = 7/16 + s * ((radialPoint (offOf y) : IC 2) i - 7/16) := by
    intro i
    have h1 : ((y i : unitInterval) : ℝ) = clamp (7/16 + s * rayOff (offOf y) i) := by
      have h := congrArg (fun z : IC 2 => ((z i : unitInterval) : ℝ)) hy_eq
      simp only [ptOf_coe] at h
      exact h
    have h4 : 1/4 ≤ (y i : ℝ) := by
      have hb := net_region_bounds hmem
      rcases (show i = 0 ∨ i = 1 from by fin_cases i <;> simp) with h | h
      · subst h; exact hb.1
      · subst h; exact hb.2.2.1
    have h5 : (y i : ℝ) ≤ 3/4 := by
      have hb := net_region_bounds hmem
      rcases (show i = 0 ∨ i = 1 from by fin_cases i <;> simp) with h | h
      · subst h; exact hb.2.1
      · subst h; linarith [hb.2.2.2]
    have h3 : (0:ℝ) ≤ 7/16 + s * rayOff (offOf y) i ∧ 7/16 + s * rayOff (offOf y) i ≤ 1 := by
      rw [h1] at h4 h5
      rw [clamp_coe_max] at h4 h5
      constructor
      · by_contra hlt; push_neg at hlt
        rw [min_eq_right (by linarith : 7/16 + s * rayOff (offOf y) i ≤ 1),
          max_eq_left (le_of_lt hlt)] at h4
        norm_num at h4
      · by_contra hlt; push_neg at hlt
        rw [min_eq_left (le_of_lt hlt)] at h5
        norm_num at h5
    rw [h1, clamp_val _ h3]
    have h6 : ((radialPoint (offOf y) : IC 2) i : ℝ) - 7/16 = rayOff (offOf y) i := by
      have := congrFun (offOf_radialPoint (offOf y)) i
      simp only [offOf] at this
      linarith
    rw [h6]
  have hpex := net_region_bounds (radialPoint_mem_region hoff0)
  have hpnb : ((radialPoint (offOf y) : IC 2) 0 : ℝ) ∈ Set.Icc (1/4:ℝ) (3/4) :=
    ⟨hpex.1, hpex.2.1⟩
  have hpnc : ((radialPoint (offOf y) : IC 2) 1 : ℝ) ∈ Set.Icc (1/4:ℝ) (5/8) :=
    ⟨hpex.2.2.1, hpex.2.2.2⟩
  rcases (rayOff_mem_netOff hoff0) with hb | hb
  · -- the exit point lies in the belt
    have hb1 : -3/16 ≤ rayOff (offOf y) 0 ∧ rayOff (offOf y) 0 ≤ 5/16 := ⟨hb.1, hb.2.1⟩
    have hb2 : -1/16 ≤ rayOff (offOf y) 1 ∧ rayOff (offOf y) 1 ≤ 1/16 :=
      ⟨hb.2.2.1, hb.2.2.2⟩
    have h6 : ∀ i, rayOff (offOf y) i = ((radialPoint (offOf y) : IC 2) i : ℝ) - 7/16 := by
      intro i
      have := congrFun (offOf_radialPoint (offOf y)) i
      simp only [offOf] at this
      linarith
    refine hnot (openBeltSet_subset_interior ⟨?_, ?_, ?_, ?_⟩)
    · rw [offOf_eq, hy_seg 0]
      have hq : rayOff (offOf y) 0 = ((radialPoint (offOf y) : IC 2) 0 : ℝ) - 7/16 := h6 0
      nlinarith [hb1.1, hpnb.1, hs0, hs1, hq]
    · rw [offOf_eq, hy_seg 0]
      have hq : rayOff (offOf y) 0 = ((radialPoint (offOf y) : IC 2) 0 : ℝ) - 7/16 := h6 0
      nlinarith [hb1.2, hpnb.2, hs0, hs1, hq]
    · rw [offOf_eq, hy_seg 1]
      have hq : rayOff (offOf y) 1 = ((radialPoint (offOf y) : IC 2) 1 : ℝ) - 7/16 := h6 1
      nlinarith [hb2.1, hpnc.1, hs0, hs1, hq]
    · rw [offOf_eq, hy_seg 1]
      have hq : rayOff (offOf y) 1 = ((radialPoint (offOf y) : IC 2) 1 : ℝ) - 7/16 := h6 1
      nlinarith [hb2.2, hpnc.2, hs0, hs1, hq]
  · -- the exit point lies in the column
    have hb1 : -1/16 ≤ rayOff (offOf y) 0 ∧ rayOff (offOf y) 0 ≤ 1/16 := ⟨hb.1, hb.2.1⟩
    have hb2 : -3/16 ≤ rayOff (offOf y) 1 ∧ rayOff (offOf y) 1 ≤ 3/16 :=
      ⟨hb.2.2.1, hb.2.2.2⟩
    have h6 : ∀ i, rayOff (offOf y) i = ((radialPoint (offOf y) : IC 2) i : ℝ) - 7/16 := by
      intro i
      have := congrFun (offOf_radialPoint (offOf y)) i
      simp only [offOf] at this
      linarith
    refine hnot (openColSet_subset_interior ⟨?_, ?_, ?_, ?_⟩)
    · rw [offOf_eq, hy_seg 0]
      have hq : rayOff (offOf y) 0 = ((radialPoint (offOf y) : IC 2) 0 : ℝ) - 7/16 := h6 0
      nlinarith [hb1.1, hpnb.1, hs0, hs1, hq]
    · rw [offOf_eq, hy_seg 0]
      have hq : rayOff (offOf y) 0 = ((radialPoint (offOf y) : IC 2) 0 : ℝ) - 7/16 := h6 0
      nlinarith [hb1.2, hpnb.2, hs0, hs1, hq]
    · rw [offOf_eq, hy_seg 1]
      have hq : rayOff (offOf y) 1 = ((radialPoint (offOf y) : IC 2) 1 : ℝ) - 7/16 := h6 1
      nlinarith [hb2.1, hpnc.1, hs0, hs1, hq]
    · rw [offOf_eq, hy_seg 1]
      have hq : rayOff (offOf y) 1 = ((radialPoint (offOf y) : IC 2) 1 : ℝ) - 7/16 := h6 1
      nlinarith [hb2.2, hpnc.2, hs0, hs1, hq]

/-- **On `∂D` the radial projection is the identity.** -/
theorem net_exit_self {y : IC 2} (hy : y ∈ NetBdy) : radialPoint (offOf y) = y := by
  have h1 : Mmin (offOf y) = 1 := Mmin_eq_one_of_mem_NetBdy hy
  have h2 : rayOff (offOf y) = offOf y := by
    funext i
    simp only [rayOff, exitScale, h1, one_div]
    ring
  rw [radialPoint, h2, ptOf_offOf]

/-- The `ℓ∞`-norm of the exit offset is at most `5/16`. -/
theorem exitDist_le (z : Fin 2 → ℝ) : exitDist z ≤ 5/16 := by
  rcases eq_or_ne z 0 with hz | hz
  · subst hz
    have h0 : rayOff 0 = 0 := by
      funext j
      simp [rayOff, exitScale, Mmin, MBelt, MCol, nu, nuB0, nuB1, nuC0, nuC1]
    rw [exitDist, h0]
    simp only [sNorm, Pi.zero_apply, abs_zero, max_self]
    norm_num
  · have h := rayOff_mem_netOff hz
    have h0 : |rayOff z 0| ≤ 5/16 := by
      rcases h with h | h
      · rw [abs_le]; exact ⟨by linarith [h.1], h.2.1⟩
      · rw [abs_le]; exact ⟨by linarith [h.1], by linarith [h.2.1]⟩
    have h1 : |rayOff z 1| ≤ 3/16 := by
      rcases h with h | h
      · rw [abs_le]; exact ⟨by linarith [h.2.2.1], by linarith [h.2.2.2]⟩
      · rw [abs_le]; exact ⟨by linarith [h.2.2.1], h.2.2.2⟩
    rw [exitDist, sNorm, max_le_iff]
    exact ⟨by linarith, by linarith⟩

end

end Work.Stems.Hur2b
