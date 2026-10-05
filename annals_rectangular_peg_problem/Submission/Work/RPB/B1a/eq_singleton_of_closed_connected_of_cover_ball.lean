import Mathlib

/-!
# `Work.RPB.B1a.eq_singleton_of_closed_connected_of_cover_ball`

If two closed, connected subsets `A`, `B` of `ℂ` cover a ball `ball p r` (`r > 0`) and meet only
in `p` (where `p ∈ A ∩ B`), then one of them is the singleton `{p}`.

The proof rests on the elementary fact that the *punctured* ball `ball p r \ {p}` is preconnected
(it is the continuous image of the connected set `(0,r) × S¹` under `(t, u) ↦ p + t·u`).  The two
closed sets then separate that preconnected set, so one of them contains `ball p r \ {p}`; if e.g.
`B` contains it, then `B ∩ ball p r ⊆ {p}`, and since `{p}` is relatively open and closed in the
connected `B`, `B = {p}`.
-/

namespace Work.RPB.B1a

/-- The punctured open ball `ball p r \ {p}` in `ℂ` is preconnected.

It is the image of the connected set `(0,r) ×ˢ sphere 0 1` under the continuous map
`(t, u) ↦ p + t • u`. -/
lemma isPreconnected_ball_sdiff_singleton (p : ℂ) (r : ℝ) :
    IsPreconnected (Metric.ball p r \ {p}) := by
  have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]; norm_num
  have hsrc : IsPreconnected ((Set.Ioo (0 : ℝ) r) ×ˢ Metric.sphere (0 : ℂ) 1) :=
    isPreconnected_Ioo.prod (isPreconnected_sphere hrank 0 1)
  have hf : ContinuousOn (fun q : ℝ × ℂ => p + (q.1 : ℂ) * q.2)
      ((Set.Ioo (0 : ℝ) r) ×ˢ Metric.sphere (0 : ℂ) 1) :=
    (by fun_prop : Continuous (fun q : ℝ × ℂ => p + (q.1 : ℂ) * q.2)).continuousOn
  have hset : (fun q : ℝ × ℂ => p + (q.1 : ℂ) * q.2) ''
      ((Set.Ioo (0 : ℝ) r) ×ˢ Metric.sphere (0 : ℂ) 1) = Metric.ball p r \ {p} := by
    ext z
    constructor
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨hq1, hq2⟩ := Set.mem_prod.mp hq
      rw [Set.mem_Ioo] at hq1
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hq2
      rw [Set.mem_sdiff, Metric.mem_ball, dist_eq_norm, Set.mem_singleton_iff]
      refine ⟨?_, ?_⟩
      · have hnorm : ‖(q.1 : ℂ)‖ = q.1 := by simp [abs_of_pos hq1.1]
        rw [add_sub_cancel_left, norm_mul, hnorm, hq2, mul_one]
        exact hq1.2
      · intro h
        have hzero : (q.1 : ℂ) * q.2 = 0 := by
          have := congrArg (fun w => w - p) h
          simpa using this
        rcases mul_eq_zero.mp hzero with h1 | h2
        · rw [Complex.ofReal_eq_zero] at h1; linarith [hq1.1]
        · rw [h2, norm_zero] at hq2; norm_num at hq2
    · rintro hz
      rw [Set.mem_sdiff, Metric.mem_ball, dist_eq_norm, Set.mem_singleton_iff] at hz
      obtain ⟨hzlt, hzne⟩ := hz
      have hpos : 0 < ‖z - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzne)
      refine ⟨(‖z - p‖, ((‖z - p‖ : ℝ) : ℂ)⁻¹ * (z - p)), ?_, ?_⟩
      · rw [Set.mem_prod, Set.mem_Ioo, Metric.mem_sphere, dist_eq_norm, sub_zero]
        refine ⟨⟨hpos, hzlt⟩, ?_⟩
        have hnorm : ‖((‖z - p‖ : ℝ) : ℂ)‖ = ‖z - p‖ := by simp
        rw [norm_mul, norm_inv, hnorm, inv_mul_cancel₀ (ne_of_gt hpos)]
      · have hne : ((‖z - p‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)
        show p + ((‖z - p‖ : ℝ) : ℂ) * (((‖z - p‖ : ℝ) : ℂ)⁻¹ * (z - p)) = z
        rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
        ring
  have himg := hsrc.image (fun q : ℝ × ℂ => p + (q.1 : ℂ) * q.2) hf
  rw [hset] at himg
  exact himg

theorem eq_singleton_of_closed_connected_of_cover_ball (A B : Set ℂ) (p : ℂ) (r : ℝ) (hr : 0 < r)
    (hAcl : IsClosed A) (hBcl : IsClosed B) (hAc : IsConnected A) (hBc : IsConnected B)
    (hcover : Metric.ball p r ⊆ A ∪ B) (hpA : p ∈ A) (hpB : p ∈ B) (hint : A ∩ B ⊆ {p}) :
    A = {p} ∨ B = {p} := by
  have hpball : p ∈ Metric.ball p r := Metric.mem_ball_self hr
  have hX : IsPreconnected (Metric.ball p r \ {p}) := isPreconnected_ball_sdiff_singleton p r
  have hsub : Metric.ball p r \ {p} ⊆ A ∪ B := fun z hz => hcover hz.1
  have hdisj : (Metric.ball p r \ {p}) ∩ (A ∩ B) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    obtain ⟨hxX, hxAB⟩ := hx
    have hxp : x = p := by simpa [Set.mem_singleton_iff] using hint hxAB
    exact hxX.2 (by simpa using hxp)
  have hsep := (isPreconnected_iff_subset_of_disjoint_closed.mp hX) A B hAcl hBcl hsub hdisj
  rcases hsep with hXA | hXB
  · -- `ball p r \ {p} ⊆ A`, so `B ∩ ball p r ⊆ {p}` and hence `B = {p}`.
    right
    have hBball : B ∩ Metric.ball p r ⊆ {p} := by
      intro b hb
      obtain ⟨hbB, hbball⟩ := hb
      by_contra hbp
      have hbA : b ∈ A := hXA ⟨hbball, by simpa [Set.mem_singleton_iff] using hbp⟩
      have hthis : b ∈ {p} := hint ⟨hbA, hbB⟩
      rw [Set.mem_singleton_iff] at hthis
      exact hbp hthis
    have hBsep := (isPreconnected_iff_subset_of_disjoint_closed.mp hBc.isPreconnected)
        {p} (Metric.ball p r)ᶜ isClosed_singleton Metric.isOpen_ball.isClosed_compl
        (by
          intro b hb
          by_cases hb' : b ∈ Metric.ball p r
          · exact Or.inl (hBball ⟨hb, hb'⟩)
          · exact Or.inr hb')
        (by
          rw [Set.eq_empty_iff_forall_notMem]
          intro x hx
          obtain ⟨_, hxp, hxball⟩ := hx
          rw [Set.mem_singleton_iff] at hxp
          exact hxball (hxp ▸ hpball))
    rcases hBsep with h | h
    · exact Set.Subset.antisymm h (Set.singleton_subset_iff.mpr hpB)
    · exfalso; exact (h hpB) hpball
  · -- symmetric case: `ball p r \ {p} ⊆ B`, so `A ∩ ball p r ⊆ {p}` and hence `A = {p}`.
    left
    have hAball : A ∩ Metric.ball p r ⊆ {p} := by
      intro a ha
      obtain ⟨haA, haball⟩ := ha
      by_contra hap
      have haB : a ∈ B := hXB ⟨haball, by simpa [Set.mem_singleton_iff] using hap⟩
      have hthis : a ∈ {p} := hint ⟨haA, haB⟩
      rw [Set.mem_singleton_iff] at hthis
      exact hap hthis
    have hAsep := (isPreconnected_iff_subset_of_disjoint_closed.mp hAc.isPreconnected)
        {p} (Metric.ball p r)ᶜ isClosed_singleton Metric.isOpen_ball.isClosed_compl
        (by
          intro a ha
          by_cases ha' : a ∈ Metric.ball p r
          · exact Or.inl (hAball ⟨ha, ha'⟩)
          · exact Or.inr ha')
        (by
          rw [Set.eq_empty_iff_forall_notMem]
          intro x hx
          obtain ⟨_, hxp, hxball⟩ := hx
          rw [Set.mem_singleton_iff] at hxp
          exact hxball (hxp ▸ hpball))
    rcases hAsep with h | h
    · exact Set.Subset.antisymm h (Set.singleton_subset_iff.mpr hpA)
    · exfalso; exact (h hpA) hpball

end Work.RPB.B1a
