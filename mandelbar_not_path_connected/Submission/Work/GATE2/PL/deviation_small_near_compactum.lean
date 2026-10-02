import Mathlib
import Submission.Work.GATE2.deviation_continuousAt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2.PL

/-- **The deviation stays inside the `1/8192` window on a neighbourhood of a compactum.**  This
is the compactness step of the exit-path construction: on the compactum `𝒦` of
`Work.GATE2.ExitLoop` the `α`-deviation of the critical Böttcher coordinate of `c₀` is
`< 1/16384`, and `𝒦` lies off `K c₀` (`ExitLoop.offK`), i.e. in `critDomain c₀`; by the joint
continuity `Work.GATE2.deviation_continuousAt` the deviation of the *nearby* parameter `e` is then
`< 1/8192` on a whole neighbourhood of `𝒦`.  Proof: the finite sub-cover argument — cover `𝒦` by
the balls of radius `δ (z₀)/2` supplied by `deviation_continuousAt` at each `z₀ ∈ 𝒦` with
`ε := 1/16384`, and take `η, ρ := min` of the finitely many `δ/2` (empty `𝒦`: vacuous). -/
theorem deviation_small_near_compactum {c₀ : ℂ} {α : ℝ} {𝒦 : Set ℂ} (hK : IsCompact 𝒦)
    (hdom : ∀ z ∈ 𝒦, z ∈ Work.ParamRays.critDomain c₀)
    (hwin : ∀ z ∈ 𝒦, |Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α z| < 1 / 16384) :
    ∃ η : ℝ, 0 < η ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∀ e : ℂ, ‖e - c₀‖ < ρ → ∀ z : ℂ,
      (∃ z₀ ∈ 𝒦, ‖z - z₀‖ < η) →
        |Work.GATE.deviation (Work.Bottcher.varphiCrit e) α z| < 1 / 8192 := by
  classical
  -- Pointwise radius from joint continuity of the deviation.
  have hpt : ∀ z ∈ 𝒦, ∃ δ, 0 < δ ∧ (∀ e : ℂ, ‖e - c₀‖ < δ → ∀ w : ℂ, ‖w - z‖ < δ →
      |Work.GATE.deviation (Work.Bottcher.varphiCrit e) α w -
        Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α z| < 1 / 16384) := by
    intro z hz
    have hzlt : |Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α z| < 1 / 4 := by
      have h := hwin z hz
      have h' : (1 : ℝ) / 16384 < 1 / 4 := by norm_num
      linarith
    obtain ⟨δ, hδpos, hδ⟩ :=
      Work.GATE2.deviation_continuousAt (hdom z hz) hzlt (1 / 16384) (by norm_num)
    exact ⟨δ, hδpos, hδ⟩
  -- A total radius function (the `∈ 𝒦` dependence is absorbed).
  have hpt' : ∀ z : ℂ, ∃ δ, z ∈ 𝒦 → 0 < δ ∧ (∀ e : ℂ, ‖e - c₀‖ < δ → ∀ w : ℂ, ‖w - z‖ < δ →
      |Work.GATE.deviation (Work.Bottcher.varphiCrit e) α w -
        Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α z| < 1 / 16384) := by
    intro z
    by_cases hz : z ∈ 𝒦
    · obtain ⟨δ, hpos, hb⟩ := hpt z hz
      exact ⟨δ, fun _ => ⟨hpos, hb⟩⟩
    · exact ⟨1, fun h => absurd h hz⟩
  let δ : ℂ → ℝ := fun z => Classical.choose (hpt' z)
  have hδpos : ∀ z ∈ 𝒦, 0 < δ z :=
    fun z hz => ((Classical.choose_spec (hpt' z)) hz).1
  have hδbound : ∀ z ∈ 𝒦, ∀ e : ℂ, ‖e - c₀‖ < δ z → ∀ w : ℂ, ‖w - z‖ < δ z →
      |Work.GATE.deviation (Work.Bottcher.varphiCrit e) α w -
        Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α z| < 1 / 16384 :=
    fun z hz e he w hw => ((Classical.choose_spec (hpt' z)) hz).2 e he w hw
  -- The finite sub-cover of `𝒦` by balls of half the pointwise radii.
  obtain ⟨t, ht, hcover⟩ := IsCompact.elim_nhds_subcover hK (fun z => Metric.ball z (δ z / 2))
    (fun z hz => Metric.ball_mem_nhds z (div_pos (hδpos z hz) (by norm_num)))
  by_cases htne : t.Nonempty
  · -- Nonempty cover: the minimum of the finitely many half-radii is positive.
    have hr : (t.image (fun z => δ z / 2)).Nonempty := htne.image _
    let m := (t.image (fun z => δ z / 2)).min' hr
    have hmpos : 0 < m := by
      change 0 < (t.image (fun z => δ z / 2)).min' hr
      rw [Finset.lt_min'_iff]
      intro y hy
      obtain ⟨z, hzt, hzy⟩ := Finset.mem_image.mp hy
      rw [← hzy]
      exact div_pos (hδpos z (ht z hzt)) (by norm_num)
    refine ⟨m, hmpos, m, hmpos, ?_⟩
    intro e he z hmem
    obtain ⟨z₀, hz₀, hdist⟩ := hmem
    have hz₀cover : z₀ ∈ ⋃ x ∈ t, Metric.ball x (δ x / 2) := hcover hz₀
    simp only [Set.mem_iUnion] at hz₀cover
    obtain ⟨w, hwt, hzw⟩ := hz₀cover
    rw [Metric.mem_ball, dist_eq_norm] at hzw
    have hwK : w ∈ 𝒦 := ht w hwt
    have hmle : m ≤ δ w / 2 := by
      change (t.image (fun z => δ z / 2)).min' hr ≤ δ w / 2
      exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨w, hwt, rfl⟩)
    have h1 := dist_triangle z z₀ w
    rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at h1
    have hp := hδpos w hwK
    have hdistw : ‖z - w‖ < δ w := by linarith
    have hew : ‖e - c₀‖ < δ w := by linarith
    have hb := hδbound w hwK e hew z hdistw
    have hb2 := hwin w hwK
    have htri := abs_add_le (Work.GATE.deviation (Work.Bottcher.varphiCrit e) α z -
        Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α w)
        (Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α w)
    rw [sub_add_cancel] at htri
    linarith
  · -- Empty cover: `𝒦` is empty and the statement is vacuous.
    have ht0 : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp htne
    refine ⟨1, one_pos, 1, one_pos, ?_⟩
    intro e _ z hmem
    obtain ⟨z₀, hz₀, _⟩ := hmem
    have h := hcover hz₀
    simp only [Set.mem_iUnion] at h
    obtain ⟨x, hxt, _⟩ := h
    rw [ht0] at hxt
    exact (Finset.notMem_empty x hxt).elim

end Work.GATE2.PL
