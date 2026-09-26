import Mathlib
import Submission.Work.Drive.Mono.LevelCountDefs
import Submission.Work.Drive.Mono.visit_structure

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

variable {K : Knot} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h : ℝ}
variable {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} {exc : Finset ℝ}

/-! ## Tools: one-sided strict inequalities from a non-vanishing derivative

A `C¹` function with `deriv f p = m ≠ 0` is strictly monotone on a neighbourhood of `p`, and we
only need the two one-sided consequences. -/

lemma exists_Ioo_side_lt_of_deriv_pos {f : ℝ → ℝ} (hfc : Continuous f)
    (hfd : Continuous (deriv f)) {p m : ℝ} (hd : deriv f p = m) (hm : 0 < m) :
    (∃ δ > 0, ∀ t ∈ Ioo (p - δ) p, f t < f p) ∧
      (∃ δ > 0, ∀ t ∈ Ioo p (p + δ), f p < f t) := by
  have hmem : p ∈ {t : ℝ | 0 < deriv f t} := by
    show 0 < deriv f p
    rw [hd]
    exact hm
  have hnhds : ∀ᶠ t in nhds p, 0 < deriv f t :=
    (isOpen_Ioi.preimage hfd).mem_nhds hmem
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp hnhds
  have hpδ : p ∈ Ioo (p - δ) (p + δ) := ⟨by linarith, by linarith⟩
  have hmono : StrictMonoOn f (Ioo (p - δ) (p + δ)) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioo (p - δ) (p + δ)) hfc.continuousOn
      (fun x hx => ?_)
    rw [interior_Ioo] at hx
    exact hδ' (by rw [Real.dist_eq, abs_lt]; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  exact ⟨⟨δ, hδ, fun t ht => hmono ⟨ht.1, by linarith [ht.2]⟩ hpδ ht.2⟩,
    ⟨δ, hδ, fun t ht => hmono hpδ ⟨by linarith [ht.1], ht.2⟩ ht.1⟩⟩

lemma exists_Ioo_side_lt_of_deriv_neg {f : ℝ → ℝ} (hfc : Continuous f)
    (hfd : Continuous (deriv f)) {p m : ℝ} (hd : deriv f p = m) (hm : m < 0) :
    (∃ δ > 0, ∀ t ∈ Ioo (p - δ) p, f p < f t) ∧
      (∃ δ > 0, ∀ t ∈ Ioo p (p + δ), f t < f p) := by
  have hmem : p ∈ {t : ℝ | deriv f t < 0} := by
    show deriv f p < 0
    rw [hd]
    exact hm
  have hnhds : ∀ᶠ t in nhds p, deriv f t < 0 :=
    (isOpen_Iio.preimage hfd).mem_nhds hmem
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp hnhds
  have hpδ : p ∈ Ioo (p - δ) (p + δ) := ⟨by linarith, by linarith⟩
  have hanti : StrictAntiOn f (Ioo (p - δ) (p + δ)) := by
    refine strictAntiOn_of_deriv_neg (convex_Ioo (p - δ) (p + δ)) hfc.continuousOn
      (fun x hx => ?_)
    rw [interior_Ioo] at hx
    exact hδ' (by rw [Real.dist_eq, abs_lt]; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  exact ⟨⟨δ, hδ, fun t ht => hanti ⟨ht.1, by linarith [ht.2]⟩ hpδ ht.2⟩,
    ⟨δ, hδ, fun t ht => hanti hpδ ⟨by linarith [ht.1], ht.2⟩ ht.1⟩⟩

/-! ## A face point of the slab has a one-sided neighbourhood in the slab visit set

At a point `p` of the knot in the open box with `|cutG p| = h`, the transverse crossing condition
`hface` forces `cutG` to be strictly monotone near `p`; hence on one side of `p` the level `|cutG|`
is strictly below `h`, and (the box being open) that whole side lies in the slab visit set. -/

lemma exists_Ioo_side_slabVisit
    (hh : 0 < h)
    (hface : ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
      |cutG K c u v t| = h → deriv (fun r : ℝ => inner ℝ v (K.curve r)) t ≠ 0)
    {p : ℝ} (hbox : boxA K s c σ p < 0) (hcut : |cutG K c u v p| = h) :
    ∃ δ > 0, (∀ t ∈ Ioo (p - δ) p, t ∈ slabVisit K s c σ u v h) ∨
      (∀ t ∈ Ioo p (p + δ), t ∈ slabVisit K s c σ u v h) := by
  have hf : Continuous (cutG K c u v) := continuous_cutG
  have hdf : Continuous (deriv (cutG K c u v)) :=
    (contDiff_cutG (K := K) (c := c) (u := u) (v := v)).continuous_deriv (by simp)
  have hderiv : deriv (cutG K c u v) p ≠ 0 := by
    rw [deriv_cutG_eq]
    exact hface p ((boxA_lt_zero_iff p).mp hbox) hcut
  -- a two-sided neighbourhood on which the *other* face bound and the box condition hold
  have hnb1 : ∀ᶠ t in nhds p, |cutG K c u v t - cutG K c u v p| < h := by
    have hmem : p ∈ {t : ℝ | |cutG K c u v t - cutG K c u v p| < h} := by
      show |cutG K c u v p - cutG K c u v p| < h
      rw [sub_self, abs_zero]
      exact hh
    exact (isOpen_Iio.preimage ((hf.sub continuous_const).abs)).mem_nhds hmem
  have hnb2 : ∀ᶠ t in nhds p, boxA K s c σ t < 0 :=
    (isOpen_Iio.preimage continuous_boxA).mem_nhds (by simpa using hbox)
  obtain ⟨δ2, hδ2, hδ2'⟩ := Metric.eventually_nhds_iff.mp (hnb1.and hnb2)
  have hfp : cutG K c u v p = h ∨ cutG K c u v p = -h := by
    rcases le_or_gt 0 (cutG K c u v p) with h0 | h0
    · left
      rw [← abs_of_nonneg h0]
      exact hcut
    · right
      have h1 : |cutG K c u v p| = h := hcut
      rw [abs_of_neg h0] at h1
      linarith
  rcases hfp with hfp | hfp
  · -- `cutG p = h`: the interior of the slab is on the side where `cutG` drops below `h`
    rcases lt_or_gt_of_ne hderiv with hm | hm
    · -- decreasing: the right side
      obtain ⟨δ1, hδ1, hright⟩ := (exists_Ioo_side_lt_of_deriv_neg hf hdf rfl hm).2
      refine ⟨min δ1 δ2, lt_min hδ1 hδ2, Or.inr ?_⟩
      intro t ht
      have hM1 : min δ1 δ2 ≤ δ1 := min_le_left _ _
      have hM2 : min δ1 δ2 ≤ δ2 := min_le_right _ _
      have ht1 : t ∈ Ioo p (p + δ1) := ⟨by linarith [ht.1, hM1], by linarith [ht.2, hM1]⟩
      have ht2 : dist t p < δ2 := by
        rw [Real.dist_eq, abs_lt]
        exact ⟨by linarith [ht.1, hM2], by linarith [ht.2, hδ2]⟩
      obtain ⟨h1, h2⟩ := hδ2' ht2
      rw [abs_lt] at h1
      refine ⟨h2, abs_lt.mpr ⟨?_, ?_⟩⟩
      · have := h1.1
        rw [hfp] at this
        linarith
      · have := hright t ht1
        rwa [hfp] at this
    · -- increasing: the left side
      obtain ⟨δ1, hδ1, hleft⟩ := (exists_Ioo_side_lt_of_deriv_pos hf hdf rfl hm).1
      refine ⟨min δ1 δ2, lt_min hδ1 hδ2, Or.inl ?_⟩
      intro t ht
      have hM1 : min δ1 δ2 ≤ δ1 := min_le_left _ _
      have hM2 : min δ1 δ2 ≤ δ2 := min_le_right _ _
      have ht1 : t ∈ Ioo (p - δ1) p := ⟨by linarith [ht.1, hM1], ht.2⟩
      have ht2 : dist t p < δ2 := by
        rw [Real.dist_eq, abs_lt]
        exact ⟨by linarith [ht.1, hδ2], by linarith [ht.2, hM2]⟩
      obtain ⟨h1, h2⟩ := hδ2' ht2
      rw [abs_lt] at h1
      refine ⟨h2, abs_lt.mpr ⟨?_, ?_⟩⟩
      · have := h1.1
        rw [hfp] at this
        linarith
      · have := hleft t ht1
        rwa [hfp] at this
  · -- `cutG p = -h`: the interior of the slab is on the side where `cutG` rises above `-h`
    rcases lt_or_gt_of_ne hderiv with hm | hm
    · -- decreasing: the left side
      obtain ⟨δ1, hδ1, hleft⟩ := (exists_Ioo_side_lt_of_deriv_neg hf hdf rfl hm).1
      refine ⟨min δ1 δ2, lt_min hδ1 hδ2, Or.inl ?_⟩
      intro t ht
      have hM1 : min δ1 δ2 ≤ δ1 := min_le_left _ _
      have hM2 : min δ1 δ2 ≤ δ2 := min_le_right _ _
      have ht1 : t ∈ Ioo (p - δ1) p := ⟨by linarith [ht.1, hM1], ht.2⟩
      have ht2 : dist t p < δ2 := by
        rw [Real.dist_eq, abs_lt]
        exact ⟨by linarith [ht.1, hδ2], by linarith [ht.2, hM2]⟩
      obtain ⟨h1, h2⟩ := hδ2' ht2
      rw [abs_lt] at h1
      refine ⟨h2, abs_lt.mpr ⟨?_, ?_⟩⟩
      · have := hleft t ht1
        rwa [hfp] at this
      · have := h1.2
        rw [hfp] at this
        linarith
    · -- increasing: the right side
      obtain ⟨δ1, hδ1, hright⟩ := (exists_Ioo_side_lt_of_deriv_pos hf hdf rfl hm).2
      refine ⟨min δ1 δ2, lt_min hδ1 hδ2, Or.inr ?_⟩
      intro t ht
      have hM1 : min δ1 δ2 ≤ δ1 := min_le_left _ _
      have hM2 : min δ1 δ2 ≤ δ2 := min_le_right _ _
      have ht1 : t ∈ Ioo p (p + δ1) := ⟨by linarith [ht.1, hM1], by linarith [ht.2, hM1]⟩
      have ht2 : dist t p < δ2 := by
        rw [Real.dist_eq, abs_lt]
        exact ⟨by linarith [ht.1, hM2], by linarith [ht.2, hδ2]⟩
      obtain ⟨h1, h2⟩ := hδ2' ht2
      rw [abs_lt] at h1
      refine ⟨h2, abs_lt.mpr ⟨?_, ?_⟩⟩
      · have := hright t ht1
        rwa [hfp] at this
      · have := h1.2
        rw [hfp] at this
        linarith

/-! ## Every in-box trace parameter lies in the closure of a visit through a crossing -/

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set in
open scoped ENNReal Topology in
theorem visit_cover
    {K : Knot} {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ}
    {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} {exc : Finset ℝ}
    (hh : 0 < h)
    (hcross : ∀ t ∈ Work.Drive.Mono.slabVisit K s c σ u v h,
      ∃ w : ℝ, w ∈ Work.Drive.Mono.visit (Work.Drive.Mono.slabVisit K s c σ u v h) t ∧
        Work.Drive.Mono.cutG K c u v w = 0)
    (hface : ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
        |Work.Drive.Mono.cutG K c u v t| = h →
        deriv (fun r : ℝ => inner ℝ v (K.curve r)) t ≠ 0) :
    ∀ p ∈ Work.Drive.Mono.facePts K s c σ u v h ℓ lam ∪
        Work.Drive.Mono.wallPts K s c σ u v h ℓ lam,
      ∃ z ∈ Work.Drive.Mono.cutCross K s c σ u v,
        p ∈ closure (Work.Drive.Mono.visit (Work.Drive.Mono.slabVisit K s c σ u v h) z) := by
  intro p hp
  rcases hp with hp | hp
  · -- `p` is a face parameter: one side of `p` lies in the slab visit set
    rw [facePts, Set.mem_ofPred_eq] at hp
    obtain ⟨hboxp, hcutp, -⟩ := hp
    obtain ⟨δ, hδ, hside⟩ := exists_Ioo_side_slabVisit (K := K) (s := s) (c := c) (σ := σ)
      (u := u) (v := v) (h := h) hh hface hboxp hcutp
    rcases hside with hleft | hright
    · have ht0 : p - δ / 2 ∈ Ioo (p - δ) p := ⟨by linarith, by linarith⟩
      have hslab : p - δ / 2 ∈ slabVisit K s c σ u v h := hleft _ ht0
      obtain ⟨z, hz, hz0⟩ := hcross _ hslab
      refine ⟨z, ?_, ?_⟩
      · rw [cutCross, Set.mem_ofPred_eq]
        exact ⟨(connectedComponentIn_subset _ _ hz).1, hz0⟩
      · have hsub : Ioo (p - δ) p ⊆ connectedComponentIn (slabVisit K s c σ u v h) (p - δ / 2) :=
          IsPreconnected.subset_connectedComponentIn isPreconnected_Ioo ht0 hleft
        have hpcl : p ∈ closure (Ioo (p - δ) p) := by
          rw [closure_Ioo (by linarith : p - δ ≠ p)]
          exact ⟨by linarith, le_rfl⟩
        have hmem := closure_mono hsub hpcl
        have hcomp := connectedComponentIn_eq hz
        show p ∈ closure (visit (slabVisit K s c σ u v h) z)
        unfold visit
        rw [← hcomp]
        exact hmem
    · have ht0 : p + δ / 2 ∈ Ioo p (p + δ) := ⟨by linarith, by linarith⟩
      have hslab : p + δ / 2 ∈ slabVisit K s c σ u v h := hright _ ht0
      obtain ⟨z, hz, hz0⟩ := hcross _ hslab
      refine ⟨z, ?_, ?_⟩
      · rw [cutCross, Set.mem_ofPred_eq]
        exact ⟨(connectedComponentIn_subset _ _ hz).1, hz0⟩
      · have hsub : Ioo p (p + δ) ⊆ connectedComponentIn (slabVisit K s c σ u v h) (p + δ / 2) :=
          IsPreconnected.subset_connectedComponentIn isPreconnected_Ioo ht0 hright
        have hpcl : p ∈ closure (Ioo p (p + δ)) := by
          rw [closure_Ioo (by linarith : p ≠ p + δ)]
          exact ⟨le_rfl, by linarith⟩
        have hmem := closure_mono hsub hpcl
        have hcomp := connectedComponentIn_eq hz
        show p ∈ closure (visit (slabVisit K s c σ u v h) z)
        unfold visit
        rw [← hcomp]
        exact hmem
  · -- `p` is a wall parameter: it already lies in the slab visit set
    rw [wallPts, Set.mem_ofPred_eq] at hp
    obtain ⟨hboxp, hcutp, -⟩ := hp
    have hslab : p ∈ slabVisit K s c σ u v h := ⟨hboxp, hcutp⟩
    obtain ⟨z, hz, hz0⟩ := hcross p hslab
    refine ⟨z, ?_, ?_⟩
    · rw [cutCross, Set.mem_ofPred_eq]
      exact ⟨(connectedComponentIn_subset _ _ hz).1, hz0⟩
    · have hcomp := connectedComponentIn_eq hz
      show p ∈ closure (visit (slabVisit K s c σ u v h) z)
      unfold visit
      rw [← hcomp]
      exact subset_closure (mem_connectedComponentIn hslab)

end

end Work.Drive.Mono
