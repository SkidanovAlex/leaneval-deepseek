/-
# `FTS/PhiStar/Honesty/CptDefs` — sources compactly supported in the open quadrant

The "honest-for-free" route of this directory (`Honesty/ellWeakPos_psiSeries_of_cptQ`) proves
the weak-class elliptic node for sources `G` which are `C^∞` on all of `ℝ²` and whose support is
a compact subset of the *open* quadrant `Q0 = (0,∞) × (0,π/2)`.  For such sources

* the slices `θ ↦ G z θ` vanish identically near `θ = 0` and `θ = π/2` for **every** `z`, which is
  what lets the mode coefficients `cmode m G z` decay faster than any power of `m`
  (`Honesty.abs_cmode_le_lzero_iter_fix`), uniformly in `z`;
* every weighted derivative is bounded on the support rectangle (all the weights
  `w`, `sin(2θ)^{-η/2}`, `Wt` are finite there), so `G ∈ ℋ^k` for every `k` with an explicit
  bound (`Honesty.smoothCptQ_hkMem`).

This file contains the definition and the elementary support/vanishing API; the two analytic
consequences above are separate modules.
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

/-- **A source compactly supported in the open quadrant.**  There is a rectangle
`[a,b] × [c,d]` with `0 < a`, `a < b`, `0 < c`, `c < d`, `d < π/2` outside of which `G`
vanishes identically. -/
def CptQ (G : ℝ → ℝ → ℝ) : Prop :=
  ∃ a b c d : ℝ, 0 < a ∧ a < b ∧ 0 < c ∧ c < d ∧ d < Real.pi / 2 ∧
    ∀ z θ, G z θ ≠ 0 → z ∈ Set.Icc a b ∧ θ ∈ Set.Icc c d

/-- **A `C^∞` source compactly supported in the open quadrant.**  `C^∞` means `C^n` on all of
`ℝ²` for every `n` (so the `z`- and `θ`-slices are smooth on all of `ℝ`, in particular on a
neighbourhood of the closed angular interval). -/
def SmoothCptQ (G : ℝ → ℝ → ℝ) : Prop :=
  (∀ n : ℕ, ContDiff ℝ n (Function.uncurry G)) ∧ CptQ G

/-! ## Projections -/

theorem SmoothCptQ.smooth {G : ℝ → ℝ → ℝ} (h : SmoothCptQ G) :
    ∀ n : ℕ, ContDiff ℝ n (Function.uncurry G) := h.1

theorem SmoothCptQ.cpt {G : ℝ → ℝ → ℝ} (h : SmoothCptQ G) : CptQ G := h.2

theorem SmoothCptQ.smoothOpen {G : ℝ → ℝ → ℝ} (h : SmoothCptQ G) :
    Work.FTS.EllipticEst.SmoothOpen G :=
  (Work.FTS.EllipticEst.smoothOpen_iff_forall G).mpr fun n => (h.1 n).contDiffOn

/-! ## The support rectangle -/

/-- The support rectangle of a `CptQ` source, in a form convenient for later `obtain`s. -/
theorem CptQ.exists_box {G : ℝ → ℝ → ℝ} (h : CptQ G) :
    ∃ a b c d : ℝ, 0 < a ∧ a < b ∧ 0 < c ∧ c < d ∧ d < Real.pi / 2 ∧
      (∀ z θ, G z θ ≠ 0 → (z, θ) ∈ Set.Icc a b ×ˢ Set.Icc c d) := by
  obtain ⟨a, b, c, d, ha, hab, hc, hcd, hd, H⟩ := h
  exact ⟨a, b, c, d, ha, hab, hc, hcd, hd, fun z θ hG => ⟨(H z θ hG).1, (H z θ hG).2⟩⟩

/-- The angular support of every slice is contained in `[c,d]`. -/
theorem CptQ.theta_support {G : ℝ → ℝ → ℝ} (h : CptQ G) :
    ∃ c d : ℝ, 0 < c ∧ c < d ∧ d < Real.pi / 2 ∧ ∀ z θ, G z θ ≠ 0 → θ ∈ Set.Icc c d := by
  obtain ⟨a, b, c, d, ha, hab, hc, hcd, hd, H⟩ := h
  exact ⟨c, d, hc, hcd, hd, fun z θ hG => (H z θ hG).2⟩

/-- If `G z θ ≠ 0` then `0 < θ`. -/
theorem CptQ.theta_pos {G : ℝ → ℝ → ℝ} (h : CptQ G) {z θ : ℝ} (hG : G z θ ≠ 0) : 0 < θ := by
  obtain ⟨a, b, c, d, ha, hab, hc, hcd, hd, H⟩ := h
  exact lt_of_lt_of_le hc (H z θ hG).2.1

/-- If `G z θ ≠ 0` then `θ < π/2`. -/
theorem CptQ.theta_lt_pi_div_two {G : ℝ → ℝ → ℝ} (h : CptQ G) {z θ : ℝ}
    (hG : G z θ ≠ 0) : θ < Real.pi / 2 := by
  obtain ⟨a, b, c, d, ha, hab, hc, hcd, hd, H⟩ := h
  exact lt_of_le_of_lt (H z θ hG).2.2 hd

/-- If `G z θ ≠ 0` then `0 < z`. -/
theorem CptQ.z_pos {G : ℝ → ℝ → ℝ} (h : CptQ G) {z θ : ℝ} (hG : G z θ ≠ 0) : 0 < z := by
  obtain ⟨a, b, c, d, ha, hab, hc, hcd, hd, H⟩ := h
  exact lt_of_lt_of_le ha (H z θ hG).1.1

/-- **Every slice of a `CptQ` source vanishes at `θ = 0`.** -/
theorem CptQ.theta_zero_left {G : ℝ → ℝ → ℝ} (h : CptQ G) (z : ℝ) : G z 0 = 0 := by
  by_contra hG
  obtain ⟨a, b, c, d, ha, hab, hc, hcd, hd, H⟩ := h
  exact absurd (H z 0 hG).2.1 (not_le.mpr hc)

/-- **Every slice of a `CptQ` source vanishes at `θ = π/2`.** -/
theorem CptQ.theta_zero_right {G : ℝ → ℝ → ℝ} (h : CptQ G) (z : ℝ) : G z (Real.pi / 2) = 0 := by
  by_contra hG
  obtain ⟨a, b, c, d, ha, hab, hc, hcd, hd, H⟩ := h
  exact absurd (H z (Real.pi / 2) hG).2.2 (not_le.mpr hd)

/-- The pair of endpoint vanishings of every slice. -/
theorem CptQ.theta_vanish {G : ℝ → ℝ → ℝ} (h : CptQ G) (z : ℝ) :
    G z 0 = 0 ∧ G z (Real.pi / 2) = 0 :=
  ⟨h.theta_zero_left z, h.theta_zero_right z⟩

/-! ## Slices of a smooth compactly supported source -/

/-- Every `z`-slice of a `SmoothCptQ` source is `C^∞` on `ℝ`. -/
theorem SmoothCptQ.slice_contDiff {G : ℝ → ℝ → ℝ} (h : SmoothCptQ G) (z : ℝ) (n : ℕ) :
    ContDiff ℝ n (fun θ : ℝ => G z θ) := by
  have hlin : ContDiff ℝ n (fun θ : ℝ => (z, θ)) := contDiff_const.prodMk contDiff_id
  exact (h.1 n).comp hlin

/-- Every `z`-slice of a `SmoothCptQ` source is `C^∞` on the closed angular interval. -/
theorem SmoothCptQ.slice_contDiffOn {G : ℝ → ℝ → ℝ} (h : SmoothCptQ G) (z : ℝ) (n : ℕ) :
    ContDiffOn ℝ n (fun θ : ℝ => G z θ) Work.Spaces.Iθ :=
  (h.slice_contDiff z n).contDiffOn

end Work.FTS.PhiStar.Honesty
