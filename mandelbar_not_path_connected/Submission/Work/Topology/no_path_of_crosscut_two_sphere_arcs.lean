import Mathlib
import Submission.Work.TopJordan.SidesAPI
import Submission.Work.TopJordan.isJordanCurve_of_two_arcs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Topology

-- Useful existing modules (import what you need; they are all in this workspace):
--   `import Submission.Commons.Topology.Jordan.crosscut_complement_at_most_two`
--   `import Submission.Commons.Topology.Jordan.exists_injective_circle_map_of_two_arcs`
--   `import Submission.Work.TopJordan.SidesAPI`  (or `Submission.Work.TopJordan.Main`)
-- Relevant tools: `Commons.Topology.Jordan.exists_injective_circle_map_of_two_arcs`,
-- `Commons.Topology.Jordan.crosscut_complement_at_most_two`,
-- `Work.Top.IsJordanCurve`, `Work.TopJordan.sidesOfCurve`, `Work.Top.Sides.subset_of_preconnected`,
-- `Work.TopJordan.sides_I_subset_closedBall`, `Work.Top.Sides.frontier_I`.
open Set Metric

/-! ## Small interval helpers -/

private lemma mem_Ioo_unitInterval_iff (t : Set.Icc (0:ℝ) 1) :
    t ∈ Set.Ioo (0 : Set.Icc (0:ℝ) 1) 1 ↔ t ≠ 0 ∧ t ≠ 1 := by
  rw [Set.mem_Ioo]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun h => absurd (h ▸ h1) (lt_irrefl _), fun h => absurd (h ▸ h2) (lt_irrefl _)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨lt_of_le_of_ne t.2.1 (fun h => h1 h.symm), lt_of_le_of_ne t.2.2 h2⟩

private lemma coe_zero_unitInterval : ((0 : Set.Icc (0:ℝ) 1) : ℝ) = 0 := rfl

private lemma coe_one_unitInterval : ((1 : Set.Icc (0:ℝ) 1) : ℝ) = 1 := rfl

private lemma exists_near_zero (d : ℝ) (hd : 0 < d) :
    ∃ t : Set.Icc (0:ℝ) 1, t ≠ 0 ∧ t ≠ 1 ∧ dist t 0 < d := by
  have hmin : 0 < min d 1 := lt_min hd one_pos
  have hpos : 0 < min d 1 / 2 := by linarith
  have hle1 : min d 1 / 2 ≤ 1 := by linarith [min_le_right d 1]
  refine ⟨⟨min d 1 / 2, by linarith, hle1⟩, ?_, ?_, ?_⟩
  · intro hh
    have hz : min d 1 / 2 = 0 := by simpa using congrArg Subtype.val hh
    linarith
  · intro hh
    have hz : min d 1 / 2 = 1 := by simpa using congrArg Subtype.val hh
    linarith [min_le_right d 1]
  · have hcast : ((⟨min d 1 / 2, by linarith, hle1⟩ : Set.Icc (0:ℝ) 1) : ℝ) = min d 1 / 2 := rfl
    rw [Subtype.dist_eq, Real.dist_eq, hcast, coe_zero_unitInterval, sub_zero, abs_of_pos hpos]
    linarith [min_le_left d 1]

private lemma exists_near_one (d : ℝ) (hd : 0 < d) :
    ∃ t : Set.Icc (0:ℝ) 1, t ≠ 0 ∧ t ≠ 1 ∧ dist t 1 < d := by
  have hmin : 0 < min d 1 := lt_min hd one_pos
  have hpos : 0 < min d 1 / 2 := by linarith
  have hle1 : min d 1 / 2 ≤ 1 := by linarith [min_le_right d 1]
  have hge0 : 0 ≤ 1 - min d 1 / 2 := by linarith [min_le_right d 1]
  have hle : 1 - min d 1 / 2 ≤ 1 := by linarith [hmin]
  refine ⟨⟨1 - min d 1 / 2, hge0, hle⟩, ?_, ?_, ?_⟩
  · intro hh
    have hz : 1 - min d 1 / 2 = 0 := by simpa using congrArg Subtype.val hh
    linarith [min_le_right d 1]
  · intro hh
    have hz : 1 - min d 1 / 2 = 1 := by simpa using congrArg Subtype.val hh
    linarith
  · have hcast : ((⟨1 - min d 1 / 2, hge0, hle⟩ : Set.Icc (0:ℝ) 1) : ℝ) = 1 - min d 1 / 2 := rfl
    rw [Subtype.dist_eq, Real.dist_eq, hcast, coe_one_unitInterval]
    rw [show (1 - min d 1 / 2 : ℝ) - 1 = -(min d 1 / 2) by ring, abs_neg, abs_of_pos hpos]
    linarith [min_le_left d 1]

/-- **An arc joining two boundary points of the disc separates the disc: points on different
closing arcs cannot be joined outside the arc.**  `β` is an injective arc with endpoints on the
unit circle and interior inside the open unit disc; `α₁`, `α₂` are the two arcs of the unit circle
joining the same endpoints.  Then there is no path from a point of `α₁` (other than the two
endpoints) to a point of `α₂` (other than the two endpoints) that stays in the closed disc, stays in
the *open* disc away from the endpoints, and avoids the image of `β`. -/
theorem no_path_of_crosscut_two_sphere_arcs {β : C(Set.Icc (0:ℝ) 1, ℂ)}
    (hβ : Function.Injective β)
    (h0 : β 0 ∈ Metric.sphere (0:ℂ) 1) (h1 : β 1 ∈ Metric.sphere (0:ℂ) 1)
    (hint : ∀ t : Set.Icc (0:ℝ) 1, β t ≠ β 0 → β t ≠ β 1 → β t ∈ Metric.ball (0:ℂ) 1)
    {α₁ α₂ : C(Set.Icc (0:ℝ) 1, ℂ)}
    (hα₁ : Function.Injective α₁) (hα₂ : Function.Injective α₂)
    (hα₁s : ∀ t : Set.Icc (0:ℝ) 1, α₁ t ∈ Metric.sphere (0:ℂ) 1)
    (hα₂s : ∀ t : Set.Icc (0:ℝ) 1, α₂ t ∈ Metric.sphere (0:ℂ) 1)
    (hα₁0 : α₁ 0 = β 0) (hα₁1 : α₁ 1 = β 1) (hα₂0 : α₂ 0 = β 0) (hα₂1 : α₂ 1 = β 1)
    (hcover : Set.range α₁ ∪ Set.range α₂ = Metric.sphere (0:ℂ) 1)
    (hdisj : ∀ s t : Set.Icc (0:ℝ) 1, α₁ s = α₂ t → s = 0 ∨ s = 1)
    {x y : ℂ} (hx : x ∈ Set.range α₁) (hx0 : x ≠ β 0) (hx1 : x ≠ β 1)
    (hy : y ∈ Set.range α₂) (hy0 : y ≠ β 0) (hy1 : y ≠ β 1) :
    ¬ ∃ γ : C(Set.Icc (0:ℝ) 1, ℂ), γ 0 = x ∧ γ 1 = y ∧
      ∀ t : Set.Icc (0:ℝ) 1, t ≠ 0 → t ≠ 1 →
        γ t ∈ Metric.ball (0:ℂ) 1 ∧ γ t ∉ Set.range β := by
  classical
  rintro ⟨γ, hγ0, hγ1, hγ⟩
  haveI : CompactSpace (Set.Icc (0:ℝ) 1) := isCompact_iff_compactSpace.mp isCompact_Icc
  -- ## basic facts about the crosscut `β`
  have hβ01 : β 0 ≠ β 1 := by
    intro hb
    have hsub : (0 : Set.Icc (0:ℝ) 1) = 1 := hβ hb
    exact absurd (congrArg Subtype.val hsub) (by norm_num)
  have hβsp : ∀ t : Set.Icc (0:ℝ) 1,
      β t ∈ Metric.sphere (0:ℂ) 1 → β t = β 0 ∨ β t = β 1 := by
    intro t ht
    by_cases h0t : t = 0
    · exact Or.inl (by rw [h0t])
    · by_cases h1t : t = 1
      · exact Or.inr (by rw [h1t])
      · exfalso
        have hb := hint t (fun hh => h0t (hβ hh)) (fun hh => h1t (hβ hh))
        have ht' : ‖β t‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using ht
        have hb' : ‖β t‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hb
        linarith
  have hdisjβ : ∀ s t : Set.Icc (0:ℝ) 1, β s = α₁ t → s = 0 ∨ s = 1 := by
    intro s t hst
    have hsp : β s ∈ Metric.sphere (0:ℂ) 1 := hst ▸ hα₁s t
    rcases hβsp s hsp with hh | hh
    · exact Or.inl (hβ hh)
    · exact Or.inr (hβ hh)
  -- ## the Jordan curve `C = range β ∪ range α₁`
  set C : Set ℂ := Set.range β ∪ Set.range α₁ with hCdef
  have hjc : Work.Top.IsJordanCurve C := by
    rw [hCdef]
    exact Work.TopJordan.isJordanCurve_of_two_arcs β α₁ hβ hα₁ hα₁0.symm hα₁1.symm hβ01 hdisjβ
  let S : Work.Top.Sides C := Work.TopJordan.sidesOf hjc
  have hCsub : C ⊆ Metric.closedBall (0:ℂ) 1 := by
    rw [hCdef]
    rintro z (⟨t, rfl⟩ | ⟨t, rfl⟩)
    · by_cases h0t : t = 0
      · rw [h0t]; exact Metric.sphere_subset_closedBall h0
      · by_cases h1t : t = 1
        · rw [h1t]; exact Metric.sphere_subset_closedBall h1
        · exact Metric.ball_subset_closedBall
            (hint t (fun hh => h0t (hβ hh)) (fun hh => h1t (hβ hh)))
    · exact Metric.sphere_subset_closedBall (hα₁s t)
  -- ## `x` and `y` are off the parts of the curve they should be
  have hxsphere : x ∈ Metric.sphere (0:ℂ) 1 := by
    obtain ⟨s, rfl⟩ := hx; exact hα₁s s
  have hxβ : x ∉ Set.range β := by
    rintro ⟨t, ht⟩
    rcases hβsp t (ht ▸ hxsphere) with hh | hh
    · exact hx0 (ht.symm.trans hh)
    · exact hx1 (ht.symm.trans hh)
  have hxα₂ : x ∉ Set.range α₂ := by
    rintro ⟨t, ht⟩
    obtain ⟨s, hs⟩ := hx
    rcases hdisj s t (by rw [hs, ht]) with hh | hh
    · exact hx0 (by rw [← hs, hh, hα₁0])
    · exact hx1 (by rw [← hs, hh, hα₁1])
  have hysphere : y ∈ Metric.sphere (0:ℂ) 1 := by
    obtain ⟨t, rfl⟩ := hy; exact hα₂s t
  have hyβ : y ∉ Set.range β := by
    rintro ⟨t, ht⟩
    rcases hβsp t (ht ▸ hysphere) with hh | hh
    · exact hy0 (ht.symm.trans hh)
    · exact hy1 (ht.symm.trans hh)
  have hyα₁ : y ∉ Set.range α₁ := by
    rintro ⟨t, ht⟩
    obtain ⟨s, hs⟩ := hy
    rcases hdisj t s (by rw [ht, hs]) with hh | hh
    · exact hy0 (by rw [← ht, hh, hα₁0])
    · exact hy1 (by rw [← ht, hh, hα₁1])
  have hyC : y ∉ C := by
    rw [hCdef]; rintro (h | h)
    · exact hyβ h
    · exact hyα₁ h
  -- ## `y` lies in the unbounded side
  have hOext : {z : ℂ | 1 < ‖z‖} ⊆ S.O := Work.TopJordan.exterior_subset_sides_O S hCsub
  have hyO : y ∈ S.O := by
    have hcl : y ∈ closure {z : ℂ | 1 < ‖z‖} := by
      rw [Metric.mem_closure_iff]
      intro e he
      have hpos : (0:ℝ) < 1 + e/2 := by linarith
      have hy1' : ‖y‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hysphere
      have he2 : (0:ℝ) < e/2 := by linarith
      refine ⟨((1 + e/2 : ℝ) : ℂ) * y, ?_, ?_⟩
      · show 1 < ‖((1 + e/2 : ℝ) : ℂ) * y‖
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, hy1', mul_one]
        linarith
      · rw [dist_eq_norm]
        rw [show y - ((1 + e/2 : ℝ) : ℂ) * y = -(((e/2 : ℝ) : ℂ) * y) by push_cast; ring]
        rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos he2, hy1', mul_one]
        linarith
    have h1mem : y ∈ closure S.O := closure_mono hOext hcl
    rw [Work.TopJordan.closure_sides_O S] at h1mem
    rcases h1mem with h | h
    · exact h
    · exact absurd h hyC
  -- ## the curve agrees with the unit circle near `x`
  have hclosedβ : IsClosed (Set.range β) := (isCompact_range β.continuous).isClosed
  have hclosedα₂ : IsClosed (Set.range α₂) := (isCompact_range α₂.continuous).isClosed
  obtain ⟨δ₁, hδ₁pos, hδ₁sub⟩ :=
    Metric.isOpen_iff.mp (hclosedβ.union hclosedα₂).isOpen_compl x (by
      simp only [Set.mem_compl_iff, Set.mem_union, not_or]; exact ⟨hxβ, hxα₂⟩)
  have hδ₁sub' : ∀ z : ℂ, z ∈ Metric.ball x δ₁ → z ∉ Set.range β ∧ z ∉ Set.range α₂ := by
    intro z hz
    have h := hδ₁sub hz
    rwa [Set.mem_compl_iff, Set.mem_union, not_or] at h
  have hδeq : Metric.ball x δ₁ ∩ Metric.sphere (0:ℂ) 1 = Metric.ball x δ₁ ∩ C := by
    ext z
    constructor
    · rintro ⟨hz1, hz2⟩
      have hzs : z ∈ Set.range α₁ ∪ Set.range α₂ := hcover.symm ▸ hz2
      refine ⟨hz1, ?_⟩
      rw [hCdef]
      rcases hzs with h | h
      · exact Or.inr h
      · exact absurd h (hδ₁sub' z hz1).2
    · rintro ⟨hz1, hz2⟩
      refine ⟨hz1, ?_⟩
      rw [hCdef] at hz2
      rcases hz2 with h | h
      · exact absurd h (hδ₁sub' z hz1).1
      · obtain ⟨s, rfl⟩ := h
        exact hα₁s s
  -- ## the cap of the disc near `x` lies in the bounded side
  have hxC : x ∈ C := by
    have h1 : x ∈ Metric.ball x δ₁ ∩ Metric.sphere (0:ℂ) 1 :=
      ⟨Metric.mem_ball_self hδ₁pos, hxsphere⟩
    rw [hδeq] at h1
    exact h1.2
  have hcapExists : ∃ e > 0, Metric.ball x e ∩ Metric.ball (0:ℂ) 1 ⊆ S.I := by
    set e : ℝ := min δ₁ (1/2) / 2 with hedef
    have hepos : 0 < e := by
      rw [hedef]
      exact div_pos (lt_min hδ₁pos (by norm_num)) (by norm_num)
    have heδ : e ≤ δ₁ := by rw [hedef]; linarith [min_le_left δ₁ (1/2:ℝ)]
    refine ⟨e, hepos, ?_⟩
    have hballsub : Metric.ball x e ⊆ Metric.ball x δ₁ := Metric.ball_subset_ball heδ
    have hloc : Metric.ball x e ∩ Metric.sphere (0:ℂ) 1 = Metric.ball x e ∩ C := by
      calc Metric.ball x e ∩ Metric.sphere (0:ℂ) 1
          = (Metric.ball x e ∩ Metric.ball x δ₁) ∩ Metric.sphere (0:ℂ) 1 := by
              rw [Set.inter_eq_left.mpr hballsub]
        _ = Metric.ball x e ∩ (Metric.ball x δ₁ ∩ Metric.sphere (0:ℂ) 1) := Set.inter_assoc ..
        _ = Metric.ball x e ∩ (Metric.ball x δ₁ ∩ C) := by rw [hδeq]
        _ = (Metric.ball x e ∩ Metric.ball x δ₁) ∩ C := (Set.inter_assoc ..).symm
        _ = Metric.ball x e ∩ C := by rw [Set.inter_eq_left.mpr hballsub]
    have hcapC : ∀ z : ℂ, z ∈ Metric.ball x e → z ∈ Metric.ball (0:ℂ) 1 → z ∉ C := by
      intro z hz1 hz2 hzC
      have h1 : z ∈ Metric.ball x e ∩ Metric.sphere (0:ℂ) 1 := by
        rw [hloc]; exact ⟨hz1, hzC⟩
      have h2 : ‖z‖ = 1 := by
        simpa [Metric.mem_sphere, dist_eq_norm] using h1.2
      have h3 : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hz2
      linarith
    have hQsub : {z : ℂ | 1 < ‖z‖} ⊆ Cᶜ := by
      intro z hz hzC
      have hz' : (1:ℝ) < ‖z‖ := hz
      have h4 : ‖z‖ ≤ 1 := by
        have := hCsub hzC
        simpa [Metric.mem_closedBall, dist_eq_norm] using this
      linarith
    have hQconn : IsPreconnected {z : ℂ | 1 < ‖z‖} := by
      simpa using Commons.Topology.Connected.isPreconnected_compl_closedBall (0:ℂ) 1
    refine S.sides_of_halves (B := Metric.ball x e)
      (P := Metric.ball x e ∩ Metric.ball (0:ℂ) 1) (Q := {z : ℂ | 1 < ‖z‖})
      Metric.isOpen_ball ⟨x, Metric.mem_ball_self hepos, hxC⟩ ?_ ?_ hQconn ?_ ?_ ?_
    · -- the ball minus the curve is covered by the inner and the outer part
      rintro z ⟨hz1, hzC⟩
      rcases lt_trichotomy ‖z‖ 1 with hlt | heq | hgt
      · exact Or.inl ⟨hz1, by simpa [Metric.mem_ball, dist_eq_norm] using hlt⟩
      · exact absurd (by
          have h1 : z ∈ Metric.sphere (0:ℂ) 1 := by
            simpa [Metric.mem_sphere, dist_eq_norm] using heq
          have h2 : z ∈ Metric.ball x e ∩ Metric.sphere (0:ℂ) 1 := ⟨hz1, h1⟩
          rw [hloc] at h2
          exact h2.2) hzC
      · exact Or.inr (by simpa using hgt)
    · exact ((convex_ball x e).inter (convex_ball (0:ℂ) 1)).isPreconnected
    · rw [Set.disjoint_left]
      rintro z ⟨hz1, hz2⟩ hzC
      exact hcapC z hz1 hz2 hzC
    · rw [Set.disjoint_left]
      intro z hz hzC
      exact hQsub hz hzC
    · -- a point of the outer part lies in the unbounded side
      have hx1' : ‖x‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hxsphere
      have he2 : (0:ℝ) < e/2 := by linarith
      have hpos : (0:ℝ) < 1 + e/2 := by linarith
      refine ⟨((1 + e/2 : ℝ) : ℂ) * x, ?_, ?_⟩
      · show 1 < ‖((1 + e/2 : ℝ) : ℂ) * x‖
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, hx1', mul_one]
        linarith
      · exact hOext (by
          show 1 < ‖((1 + e/2 : ℝ) : ℂ) * x‖
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, hx1', mul_one]
          linarith)
  obtain ⟨e, hepos, hcap⟩ := hcapExists
  -- ## two interior times at which the path meets the two sides
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp γ.continuous.continuousAt e hepos
  obtain ⟨t₀, ht₀ne0, ht₀ne1, ht₀dist⟩ := exists_near_zero δ hδpos
  have ht₀ball : γ t₀ ∈ Metric.ball x e := by
    have := hδ ht₀dist
    rwa [hγ0] at this
  have ht₀I : γ t₀ ∈ S.I := hcap ⟨ht₀ball, (hγ t₀ ht₀ne0 ht₀ne1).1⟩
  obtain ⟨δ', hδ'pos, hδ'sub⟩ := Metric.isOpen_iff.mp S.isOpen_O y hyO
  obtain ⟨δ'', hδ''pos, hδ''⟩ := Metric.continuousAt_iff.mp γ.continuous.continuousAt δ' hδ'pos
  obtain ⟨t₁, ht₁ne0, ht₁ne1, ht₁dist⟩ := exists_near_one δ'' hδ''pos
  have ht₁O : γ t₁ ∈ S.O := by
    have h := hδ'' ht₁dist
    rw [hγ1] at h
    exact hδ'sub h
  -- ## contradiction
  have houtC : ∀ t : Set.Icc (0:ℝ) 1, t ≠ 0 → t ≠ 1 → γ t ∉ C := by
    intro t ht0 ht1 hmem
    rw [hCdef] at hmem
    rcases hmem with h | h
    · exact (hγ t ht0 ht1).2 h
    · obtain ⟨s, hs⟩ := h
      have h1' : ‖γ t‖ = 1 := by rw [← hs]; simpa [Metric.mem_sphere, dist_eq_norm] using hα₁s s
      have h2' : ‖γ t‖ < 1 := by
        simpa [Metric.mem_ball, dist_eq_norm] using (hγ t ht0 ht1).1
      linarith
  have hIoo : IsPreconnected (Set.Ioo (0 : Set.Icc (0:ℝ) 1) 1) := isPreconnected_Ioo
  have hprec : IsPreconnected (γ '' Set.Ioo (0 : Set.Icc (0:ℝ) 1) 1) :=
    hIoo.image γ γ.continuous.continuousOn
  have hsub : γ '' Set.Ioo (0 : Set.Icc (0:ℝ) 1) 1 ⊆ Cᶜ := by
    rintro z ⟨t, ht, rfl⟩
    rw [mem_Ioo_unitInterval_iff] at ht
    exact fun hmem => houtC t ht.1 ht.2 hmem
  rcases S.subset_of_preconnected hprec hsub with h | h
  · refine S.notMem_O_of_mem_I (h ?_) ht₁O
    exact ⟨t₁, by rw [mem_Ioo_unitInterval_iff]; exact ⟨ht₁ne0, ht₁ne1⟩, rfl⟩
  · refine S.notMem_I_of_mem_O (h ?_) ht₀I
    exact ⟨t₀, by rw [mem_Ioo_unitInterval_iff]; exact ⟨ht₀ne0, ht₀ne1⟩, rfl⟩

end Work.Topology
