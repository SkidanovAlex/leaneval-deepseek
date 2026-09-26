import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.outerArcs

namespace Work.Smooth.SphereJordan

noncomputable section

open Set Metric

/-- **The endpoint at `t = 1` of the radial arc through `w` lies in the inner disc `range T.e`.**
Indeed `arcPt w 1` is a point of the unit circle, hence `circlePoint θ` for some `θ`; then
`T.e' (circlePoint θ) = c θ`, and `range c ⊆ range e` by `TwoDiscs.meet`. -/
theorem arcPt_one_mem_range_e {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    (w : Metric.sphere (0 : ℂ) 1) :
    T.e' (arcPt w 1) ∈ Set.range T.e := by
  have hnorm : ‖((arcPt w 1 : Disc) : ℂ)‖ = 1 := by
    rw [arcPt_coe, show max 0 (min (1 : ℝ) 1) = 1 from by norm_num, Complex.ofReal_one,
      one_mul]
    simpa [dist_eq_norm] using w.2
  obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq (arcPt w 1) hnorm
  have hendpoint : T.e' (arcPt w 1) = c θ := by
    rw [← hθ, T.boundary' θ]
  rw [hendpoint]
  have hle : Set.range c ⊆ Set.range T.e := by
    rw [← T.meet]; exact Set.inter_subset_left
  exact hle ⟨θ, rfl⟩

/-- **The closure of a cut meets the open annulus exactly in the cut itself.**

The cut `cutSet T w` is the image of the *open* parameter interval
`(crosscutTime T w, 1)` under the radial arc.  Its closure is contained in the image of the closed
interval (the radial arc is continuous and the interval is compact), and a point of that closed
image which lies in the open annulus cannot be an endpoint: the endpoint `t = crosscutTime T w` is
not in the open unit disc (`crosscutTime_notMem_openDisc`) while `t = 1` lands in the inner disc
`range e` (`arcPt_one_mem_range_e`).  Hence the point is an interior point of the cut. -/
theorem closure_cutSet_inter_openAnnulus {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    {w : Metric.sphere (0 : ℂ) 1} (hne : (arcOutSet T w).Nonempty) :
    closure (cutSet T w) ∩ openAnnulus T = cutSet T w := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxcl, hxA⟩
    have hf : Continuous fun t : ℝ => T.e' (arcPt w t) :=
      T.e'.continuous.comp (continuous_arcPt w)
    have hsub : cutSet T w ⊆ (fun t : ℝ => T.e' (arcPt w t)) '' Icc (crosscutTime T w) 1 := by
      rintro y ⟨z, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
    have hclosed : IsClosed ((fun t : ℝ => T.e' (arcPt w t)) '' Icc (crosscutTime T w) 1) :=
      (isCompact_Icc.image hf).isClosed
    have hmembig : x ∈ (fun t : ℝ => T.e' (arcPt w t)) '' Icc (crosscutTime T w) 1 :=
      closure_minimal hsub hclosed hxcl
    obtain ⟨t, ht, htxy⟩ := hmembig
    have htxy' : T.e' (arcPt w t) = x := htxy
    have htlt1 : t < 1 := by
      rcases lt_or_eq_of_le ht.2 with h | h
      · exact h
      · exfalso
        have hxe : x ∈ Set.range T.e := by
          rw [← htxy', h]
          exact arcPt_one_mem_range_e T w
        exact hxA.2 hxe
    have htgtc : crosscutTime T w < t := by
      rcases lt_or_eq_of_le ht.1 with h | h
      · exact h
      · exfalso
        have hxd : InOpenDisc (T.e' (arcPt w (crosscutTime T w))) := by
          rw [h, htxy']
          exact hxA.1
        exact crosscutTime_notMem_openDisc T hne hxd
    exact ⟨arcPt w t, ⟨t, ⟨htgtc, htlt1⟩, rfl⟩, htxy'⟩
  · intro x hx
    exact ⟨subset_closure hx, cutSet_subset_openAnnulus T hne hx⟩

/-- The slit annulus, with the *open* cuts removed, is the open annulus with the *closures* of
the cuts removed: by `closure_cutSet_inter_openAnnulus` the extra points of the closure all lie
outside the open annulus. -/
theorem sdiff_cutSet_eq_sdiff_closure {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    {w : Metric.sphere (0 : ℂ) 1} (hne : (arcOutSet T w).Nonempty) :
    openAnnulus T \ cutSet T w = openAnnulus T \ closure (cutSet T w) := by
  ext x
  constructor
  · rintro ⟨hxA, hxn⟩
    refine ⟨hxA, fun hxcl => hxn ?_⟩
    have hmem : x ∈ closure (cutSet T w) ∩ openAnnulus T := ⟨hxcl, hxA⟩
    rwa [closure_cutSet_inter_openAnnulus T hne] at hmem
  · rintro ⟨hxA, hxn⟩
    exact ⟨hxA, fun hx => hxn (subset_closure hx)⟩

theorem isOpen_slitAnnulus {c : ℝ → RiemannSphere} (T : Work.Smooth.SphereJordan.TwoDiscs c)
    (w₁ w₂ : Metric.sphere (0 : ℂ) 1)
    (hne₁ : (Work.Smooth.SphereJordan.arcOutSet T w₁).Nonempty)
    (hne₂ : (Work.Smooth.SphereJordan.arcOutSet T w₂).Nonempty) :
    IsOpen (Work.Smooth.SphereJordan.slitAnnulus T w₁ w₂) := by
  have hset : slitAnnulus T w₁ w₂
      = (openAnnulus T \ closure (cutSet T w₁)) ∩ (openAnnulus T \ closure (cutSet T w₂)) := by
    rw [slitAnnulus]
    rw [show openAnnulus T \ (cutSet T w₁ ∪ cutSet T w₂)
        = (openAnnulus T \ cutSet T w₁) ∩ (openAnnulus T \ cutSet T w₂) from by
      ext x; simp only [Set.mem_sdiff, Set.mem_union, Set.mem_inter_iff]; tauto]
    rw [sdiff_cutSet_eq_sdiff_closure T hne₁, sdiff_cutSet_eq_sdiff_closure T hne₂]
  rw [hset]
  exact ((isOpen_openAnnulus T).sdiff isClosed_closure).inter
    ((isOpen_openAnnulus T).sdiff isClosed_closure)

end

end Work.Smooth.SphereJordan
