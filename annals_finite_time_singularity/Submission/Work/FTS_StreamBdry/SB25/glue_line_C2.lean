import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs
import Submission.Work.FTS_StreamBdry.SB25.glue_line_C1
import Submission.Work.FTS_StreamBdry.SB25.contDiffOn_two_of_partials
import Submission.Work.Spaces.uncurry_partial_c1

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25.glue_line_C2` (leaf B7c)

`GlueLineC2 h c r` states that a function `h : ℝ → ℝ → ℝ` which is `C²` on the two open
half-strips `θ < c` and `θ > c`, continuous on the full strip `(0,∞) × (c-r,c+r)`, and whose
six partial derivatives of order `≤ 2` (`∂_z`, `∂_θ`, `∂_z∂_z`, `∂_θ∂_z`, `∂_z∂_θ`, `∂_θ∂_θ`)
have limits at every point `(z₀, c)` of the seam (approached along the punctured strip), is
`C²` on the full strip.

This is the leaf-plan recipe "B7a applied to `h`, `pz h`, `pth h`, then B7b":

* `h` is `C¹` on the punctured strip (from `C²`) and continuous on the full strip, and the
  limits of `∂_z h`, `∂_θ h` at the seam are among the six assumed limits; hence
  `glue_line_C1 h c r` gives `h ∈ C¹` on the full strip, together with the *continuity* of
  `∂_z h`, `∂_θ h`, which is the extra hypothesis needed to feed `pz h` and `pth h` into
  `glue_line_C1`;
* on the punctured strip, `uncurry_partial_c1` gives `uncurry (pz h)` and `uncurry (pth h)`
  `C¹` from `uncurry h` `C²`; their limits at the seam are again among the six, so
  `glue_line_C1 (pz h) c r` and `glue_line_C1 (pth h) c r` give `C¹`-ness of the two first
  partials on the full strip;
* `contDiffOn_two_of_partials` (Mathlib's `C¹` with `C¹` partials is `C²`, on an open set)
  then upgrades to `uncurry h` `C²` on the full strip.
-/

noncomputable section

open scoped Real Topology NNReal ContDiff
open Set Filter

namespace Work.FTS_StreamBdry.SB25

set_option autoImplicit false

theorem glue_line_C2 (h : ℝ → ℝ → ℝ) (c r : ℝ) :
    Work.FTS_StreamBdry.SB25.GlueLineC2 h c r := by
  intro hr hC2 hcont hlim
  have hSopen : IsOpen (glueS c r) := isOpen_glueS c r
  have hUopen : IsOpen (glueU c r) := isOpen_glueU c r
  -- the two first partials of `h` are `C¹` on the punctured strip
  obtain ⟨hpzS, hpthS⟩ := Work.Spaces.uncurry_partial_c1 hSopen hC2
  -- the limits of `∂_z h`, `∂_θ h` at the seam
  have hlim_pz : ∀ z0 : ℝ, 0 < z0 → ∃ l, Tendsto (Function.uncurry (Work.Spaces.pz h))
      (𝓝[glueS c r] (z0, c)) (𝓝 l) :=
    fun z0 hz0 => hlim (Work.Spaces.pz h) (by simp) z0 hz0
  have hlim_pth : ∀ z0 : ℝ, 0 < z0 → ∃ l, Tendsto (Function.uncurry (Work.Spaces.pth h))
      (𝓝[glueS c r] (z0, c)) (𝓝 l) :=
    fun z0 hz0 => hlim (Work.Spaces.pth h) (by simp) z0 hz0
  -- B7a for `h`: `C¹` on the full strip plus continuity of both first partials
  have hC1h := glue_line_C1 h c r hr (hC2.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)) hcont
    hlim_pz hlim_pth
  have hC1 : ContDiffOn ℝ 1 (Function.uncurry h) (glueU c r) := hC1h.1
  have hcont_pz : ContinuousOn (Function.uncurry (Work.Spaces.pz h)) (glueU c r) := hC1h.2.1
  have hcont_pth : ContinuousOn (Function.uncurry (Work.Spaces.pth h)) (glueU c r) := hC1h.2.2
  -- the limits of the four second partials at the seam
  have hlim_ppz : ∀ z0 : ℝ, 0 < z0 →
      ∃ l, Tendsto (Function.uncurry (Work.Spaces.pz (Work.Spaces.pz h)))
        (𝓝[glueS c r] (z0, c)) (𝓝 l) :=
    fun z0 hz0 => hlim (Work.Spaces.pz (Work.Spaces.pz h)) (by simp) z0 hz0
  have hlim_ptpz : ∀ z0 : ℝ, 0 < z0 →
      ∃ l, Tendsto (Function.uncurry (Work.Spaces.pth (Work.Spaces.pz h)))
        (𝓝[glueS c r] (z0, c)) (𝓝 l) :=
    fun z0 hz0 => hlim (Work.Spaces.pth (Work.Spaces.pz h)) (by simp) z0 hz0
  have hlim_ppth : ∀ z0 : ℝ, 0 < z0 →
      ∃ l, Tendsto (Function.uncurry (Work.Spaces.pz (Work.Spaces.pth h)))
        (𝓝[glueS c r] (z0, c)) (𝓝 l) :=
    fun z0 hz0 => hlim (Work.Spaces.pz (Work.Spaces.pth h)) (by simp) z0 hz0
  have hlim_ptpth : ∀ z0 : ℝ, 0 < z0 →
      ∃ l, Tendsto (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth h)))
        (𝓝[glueS c r] (z0, c)) (𝓝 l) :=
    fun z0 hz0 => hlim (Work.Spaces.pth (Work.Spaces.pth h)) (by simp) z0 hz0
  -- B7a for `∂_z h`
  have hC1pz := glue_line_C1 (Work.Spaces.pz h) c r hr hpzS hcont_pz hlim_ppz hlim_ptpz
  have hpzU : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz h)) (glueU c r) := hC1pz.1
  -- B7a for `∂_θ h`
  have hC1pth := glue_line_C1 (Work.Spaces.pth h) c r hr hpthS hcont_pth hlim_ppth hlim_ptpth
  have hpthU : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth h)) (glueU c r) := hC1pth.1
  -- B7b: `C¹` with `C¹` partials is `C²`
  exact contDiffOn_two_of_partials h (glueU c r) hUopen hC1 hpzU hpthU

end Work.FTS_StreamBdry.SB25
