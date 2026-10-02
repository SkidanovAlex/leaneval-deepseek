import Mathlib
import Submission.Work.ELRig.rayTail_lift
import Submission.Work.ELRig.Pa_subset_K

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

/-- **The tail of an external ray lies under the repelling coordinate `Ψ` on every far-left half
plane.**  For a root-parabolic parameter `c`, the flower of the simple parabolic point `z₁` of
`F c = (T_c)^[10]`, an angle `θ` whose ray lands at `z₁`, and any level `R`: there is `t₁ > 1`
such that for every `1 < t < t₁` the ray point `rayPt hN θ t` has a preimage `w` under `fl.Ψ`
with `Re w < -R`.

This is step 1 of R-a2: a ray point of level `> 1` is not in the filled Julia set `K c`, while
the attracting petal `Pa` of the flower lies in `K c`; the flower's `cover` says that every point
of the punctured neighbourhood of `z₁` is either in `Pa` or in `Ψ({Re w < -R})`, and the ray
points of level `t → 1⁺` approach `z₁` by the landing hypothesis. -/
theorem exists_preimage_rayTail {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    {θ : ℝ} (hθ : Work.EL.LandsN d.hN θ d.z₁) {R : ℝ} :
    ∃ t₁ : ℝ, 1 < t₁ ∧ ∀ t : ℝ, 1 < t → t < t₁ →
      ∃ w : ℂ, w.re < -R ∧ fl.Ψ w = Work.EL.rayPt d.hN θ t := by
  -- the flower's covering property on the half plane `Re < -R`
  obtain ⟨r, hr, hcov⟩ := fl.cover R
  -- the attracting petal lies in the filled Julia set, and `z₁` too
  have hPaK : fl.Pa ⊆ Work.EL.K c := Pa_subset_K fl
  have hz1K : d.z₁ ∈ Work.EL.K c :=
    mem_K_of_iterate_eq_self (k := 5) (by norm_num) d.per_half
  -- ray points of level `t → 1⁺` are close to `z₁`
  have hB : ∀ᶠ t in nhdsWithin (1 : ℝ) (Set.Ioi 1),
      Work.EL.rayPt d.hN θ t ∈ Metric.ball d.z₁ r :=
    hθ (Metric.ball_mem_nhds d.z₁ hr)
  obtain ⟨t₁, ht₁, h'⟩ := (nhdsGT_basis (1 : ℝ)).eventually_iff.mp hB
  refine ⟨t₁, ht₁, ?_⟩
  intro t ht htlt
  have hb : Work.EL.rayPt d.hN θ t ∈ Metric.ball d.z₁ r := h' ⟨ht, htlt⟩
  -- a ray point of level `> 1` is not in `K c`, hence not `z₁` either
  have hzK : Work.EL.rayPt d.hN θ t ∉ Work.EL.K c := d.hN.rayPt_notMem ht
  have hne : Work.EL.rayPt d.hN θ t ≠ d.z₁ := by
    intro he
    exact hzK (by rw [he]; exact hz1K)
  have hpos : 0 < ‖Work.EL.rayPt d.hN θ t - d.z₁‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hlt : ‖Work.EL.rayPt d.hN θ t - d.z₁‖ < r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hb
  -- the covering: either in `Pa` (impossible) or in `Ψ({Re < -R})`
  rcases hcov (Work.EL.rayPt d.hN θ t) hpos hlt with hmem | ⟨w, hw, hΨ⟩
  · exact absurd (hPaK hmem) hzK
  · exact ⟨w, hw, hΨ⟩

end Work.ELRig
