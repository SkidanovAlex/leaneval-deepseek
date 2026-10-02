import Mathlib
import Submission.Work.ELTop.PolyCurve.Defs
import Submission.Work.ELTop.landsN_mem_K
import Submission.Work.ELTop.rayPiece_eq_image

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELTop.PolyCurve

variable {c : ℂ} {φ : ℂ → ℂ}

/-! ## Elementary unfolding lemmas for `rayArc` -/

theorem rayArc_one (hN : Work.EL.DynB c φ) (β : ℝ) (y : ℂ) :
    Work.ELTop.rayArc hN β y 1 = y := by
  simp [Work.ELTop.rayArc]

theorem rayArc_of_ne (hN : Work.EL.DynB c φ) (β : ℝ) (y : ℂ) {t : ℝ} (ht : t ≠ 1) :
    Work.ELTop.rayArc hN β y t = Work.EL.rayPt hN β t := by
  simp [Work.ELTop.rayArc, ht]

/-- `rayArc` is `rayPt` with the value at level `1` overwritten by the landing point. -/
theorem rayArc_eq_update (hN : Work.EL.DynB c φ) (β : ℝ) (y : ℂ) :
    Work.ELTop.rayArc hN β y = Function.update (fun t : ℝ => Work.EL.rayPt hN β t) 1 y := by
  funext t
  rw [Function.update_apply]
  by_cases h : t = 1
  · simp [Work.ELTop.rayArc, h]
  · simp [Work.ELTop.rayArc, h]

/-! ## Continuity -/

/-- The ray arc of an angle which lands at `y` is continuous on the level interval `[1,R]`:
above level `1` it is the (continuous) ray parametrization, and at level `1` it is `y`, which is
the limit of the ray points as the level tends to `1` from above by the landing hypothesis. -/
theorem continuousOn_rayArc (hN : Work.EL.DynB c φ) (β : ℝ) {y : ℂ} (h : Work.EL.LandsN hN β y)
    (R : ℝ) : ContinuousOn (Work.ELTop.rayArc hN β y) (Set.Icc 1 R) := by
  have hcont : ContinuousOn (fun t : ℝ => Work.EL.rayPt hN β t) (Set.Ioi 1) :=
    Work.Top.continuousOn_rayPt hN β
  have hland : Tendsto (fun t : ℝ => Work.EL.rayPt hN β t) (𝓝[Set.Ioi (1 : ℝ)] 1) (𝓝 y) := h
  change ContinuousOn (fun t : ℝ => if t = 1 then y else Work.EL.rayPt hN β t) (Set.Icc 1 R)
  intro t ht
  obtain rfl | ht1 := eq_or_lt_of_le ht.1
  · -- at the level `1`, the value is the limit of the ray points from above
    have hsub : Set.Icc (1 : ℝ) R ⊆ ({1} ∪ Set.Ioi (1 : ℝ)) := by
      intro x hx
      obtain h | h := eq_or_lt_of_le hx.1
      · exact Or.inl h.symm
      · exact Or.inr h
    have hle := nhdsWithin_mono (1 : ℝ) hsub
    rw [nhdsWithin_union] at hle
    have ha : Tendsto (fun t : ℝ => if t = 1 then y else Work.EL.rayPt hN β t)
        (𝓝[{1}] (1 : ℝ)) (𝓝 y) := by
      rw [nhdsWithin_singleton]
      simpa using tendsto_pure_nhds (fun t : ℝ => if t = 1 then y else Work.EL.rayPt hN β t)
        (1 : ℝ)
    have hb : Tendsto (fun t : ℝ => if t = 1 then y else Work.EL.rayPt hN β t)
        (𝓝[Set.Ioi (1 : ℝ)] 1) (𝓝 y) := by
      refine hland.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      rw [Set.mem_Ioi] at hs
      simp only [ite_eq_right (ne_of_gt hs)]
    have hsup := (Filter.Tendsto.sup ha hb).mono_left hle
    simpa [ContinuousWithinAt] using hsup
  · -- above level `1` this is continuity of the ray parametrization
    have hft : ContinuousAt (fun t : ℝ => Work.EL.rayPt hN β t) t :=
      hcont.continuousAt (isOpen_Ioi.mem_nhds ht1)
    have hgt : ContinuousAt (fun t : ℝ => if t = 1 then y else Work.EL.rayPt hN β t) t := by
      refine hft.congr ?_
      filter_upwards [eventually_ne_nhds (a := t) (b := (1 : ℝ)) (ne_of_gt ht1)] with s hs
      simp only [ite_eq_right hs]
    exact hgt.continuousWithinAt

/-! ## Injectivity -/

/-- The ray arc is injective on `[1,R]`: the level is recovered from the potential of the point
above level `1`, and no ray point is the landing point (which lies in the filled Julia set). -/
theorem injOn_rayArc (hN : Work.EL.DynB c φ) (β : ℝ) {y : ℂ} (h : Work.EL.LandsN hN β y)
    {R : ℝ} (hR : 1 < R) : Set.InjOn (Work.ELTop.rayArc hN β y) (Set.Icc 1 R) := by
  intro t ht t' ht' hEq
  by_cases ht1 : t = 1
  · subst ht1
    by_cases ht1' : t' = 1
    · exact ht1'.symm
    · -- a ray point is never the landing point
      exfalso
      have ht'1 : 1 < t' := lt_of_le_of_ne ht'.1 (Ne.symm ht1')
      have hy : y = Work.EL.rayPt hN β t' := by
        rw [rayArc_one, rayArc_of_ne hN β y ht1'] at hEq
        exact hEq
      exact Work.EL.rayPt_notMem_K hN ht'1 (hy ▸ Work.ELTop.landsN_mem_K hN h)
  · by_cases ht1' : t' = 1
    · subst ht1'
      exfalso
      have ht1'' : 1 < t := lt_of_le_of_ne ht.1 (Ne.symm ht1)
      have hy : y = Work.EL.rayPt hN β t := by
        rw [rayArc_one, rayArc_of_ne hN β y ht1] at hEq
        exact hEq.symm
      exact Work.EL.rayPt_notMem_K hN ht1'' (hy ▸ Work.ELTop.landsN_mem_K hN h)
    · -- both levels are `> 1`: the potential separates them
      have ht1'' : 1 < t := lt_of_le_of_ne ht.1 (Ne.symm ht1)
      have ht1''' : 1 < t' := lt_of_le_of_ne ht'.1 (Ne.symm ht1')
      have hray : Work.EL.rayPt hN β t = Work.EL.rayPt hN β t' := by
        rw [rayArc_of_ne hN β y ht1, rayArc_of_ne hN β y ht1'] at hEq
        exact hEq
      have hpot := congrArg (Work.EL.pot hN) hray
      rw [Work.EL.pot_rayPt hN ht1'', Work.EL.pot_rayPt hN ht1'''] at hpot
      exact Real.log_injOn_pos (by linarith : (0:ℝ) < t) (by linarith : (0:ℝ) < t') hpot

/-! ## Image -/

/-- The image of the level interval `[1,R]` under the ray arc is the ray piece of levels
`(1, R]` together with the landing point `y` (the image of the level `1`). -/
theorem image_rayArc (hN : Work.EL.DynB c φ) (β : ℝ) {y : ℂ} (h : Work.EL.LandsN hN β y)
    {R : ℝ} (hR : 1 < R) :
    Work.ELTop.rayArc hN β y '' Set.Icc 1 R = Work.EL.rayPiece hN β 0 R ∪ {y} := by
  ext z
  rw [Work.ELTop.rayPiece_eq_image hN hR, Set.mem_union, Set.mem_singleton_iff, Set.mem_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    by_cases ht1 : t = 1
    · right
      rw [ht1, rayArc_one]
    · left
      exact ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm ht1), ht.2⟩, (rayArc_of_ne hN β y ht1).symm⟩
  · rintro (⟨t, ht, htz⟩ | hz)
    · exact ⟨t, ⟨ht.1.le, ht.2⟩, by rw [rayArc_of_ne hN β y (ne_of_gt ht.1)]; exact htz⟩
    · exact ⟨1, ⟨le_refl 1, hR.le⟩, by rw [hz, rayArc_one]⟩

/-! ## The main statement -/

theorem rayArc_facts {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {β R : ℝ} (hR : 1 < R) {y : ℂ}
    (h : Work.EL.LandsN hN β y) :
    ContinuousOn (Work.ELTop.rayArc hN β y) (Set.Icc 1 R) ∧
    Set.InjOn (Work.ELTop.rayArc hN β y) (Set.Icc 1 R) ∧
    Work.ELTop.rayArc hN β y '' Set.Icc 1 R = Work.EL.rayPiece hN β 0 R ∪ {y} :=
  ⟨continuousOn_rayArc hN β h R, injOn_rayArc hN β h hR, image_rayArc hN β h hR⟩

end Work.ELTop.PolyCurve
