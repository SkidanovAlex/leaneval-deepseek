/-
# Mandelbar endgame: two-sided pinching implies non-path-connectedness

This module contains the top-level theorem of the area `Submission/Work/Top`:

* `Work.Top.not_isPathConnected_of_twoSidedPinch` — pure plane topology plus Nakane's
  parameter Böttcher coordinate as an abstract interface: one parabolic parameter `c₀`, the
  local facts `hLB` (no `Mb`-path approaches `c₀` through the implosion side `Nm`), `hX` (at
  every scale a straight segment in `Nm` near `c₀` carries escaping parameters whose external
  angles lie in two prescribed windows) and `hθ` (the ray of angle `θ` does not accumulate at
  `c₀`), plus the real-ray interface.  The conclusion is `¬ IsPathConnected Mb`.

* `Work.Top.mandelbar_not_isPathConnected_of_twoSidedPinch` — the same statement specialised to
  `Mb = Mandelbar`, the form in which the theorem is consumed by the paper's main argument.

The only plane-topological input is `Work.Top.JordanForm` (the Jordan curve theorem), passed as
an explicit hypothesis; see `Submission/Work/Top/Jordan.lean`.
-/
import Submission.Work.Top.Defs
import Submission.Work.Top.Jordan
import Submission.Work.Top.scale_separation

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

noncomputable section

namespace Work.Top

/-- **The endgame.**  Suppose that, in the parameter plane, `Mb` is the connectedness locus with
Böttcher coordinate `Φ`, that `c₀` is a pinch point, and that:

* `hθ`: the parameter ray of angle `θ` does not accumulate at `c₀`;
* `hLB`: no path inside `Mb` approaches `c₀` through the implosion side `Nm`;
* `hX`: at every scale, a straight segment inside `Nm ∩ ball c₀ r` carries escaping parameters
  whose external angles lie in two windows `(a₁ ± ε)`, `(a₂ ± ε)` separated by `θ`;
* `hreal`: `1/4 ∈ Mb` is a limit point of the real ray, which itself avoids `c₀`;
* `hp`: the ray of angle `θ` accumulates at some point `p ∈ Mb`, `p ≠ 1/4`;

then `Mb` is not path-connected. -/
theorem not_isPathConnected_of_twoSidedPinch
    (Mb : Set ℂ) (Φ : ℂ → ℂ) (hN : NakaneData Mb Φ) (hJ : JordanForm)
    (c₀ : ℂ) (Nm : Set ℂ) (a₁ a₂ θ ε : ℝ)
    (hwin : 0 < a₁ - ε ∧ a₁ + ε < θ ∧ θ < a₂ - ε ∧ a₂ + ε < 1)
    (hθ : c₀ ∉ closure (NakaneData.paramRay hN θ))
    (hq : c₀ ≠ (1 / 4 : ℂ))
    (hreal : (1 / 4 : ℂ) ∈ Mb ∧ (1 / 4 : ℂ) ∈ closure (NakaneData.paramRay hN 0) ∧
      c₀ ∉ closure (NakaneData.paramRay hN 0))
    (hp : ∃ p : ℂ, p ∈ Mb ∧ p ∈ closure (NakaneData.paramRay hN θ) ∧ p ≠ (1 / 4 : ℂ))
    (hLB : ∀ γ : C(unitInterval, ℂ), (∀ t, γ t ∈ Mb) →
      c₀ ∉ closure (Set.range γ ∩ Nm))
    (hX : ∀ r > 0, ∃ x y : ℂ, segment ℝ x y ⊆ Nm ∩ Metric.ball c₀ r ∧
        ∃ e₁ ∈ segment ℝ x y, ∃ e₂ ∈ segment ℝ x y, e₁ ∉ Mb ∧ e₂ ∉ Mb ∧
        NakaneData.extAngle Φ e₁ ∈ Set.Ioo (a₁ - ε) (a₁ + ε) ∧
        NakaneData.extAngle Φ e₂ ∈ Set.Ioo (a₂ - ε) (a₂ + ε)) :
    ¬ IsPathConnected Mb := by
  classical
  rintro ⟨x₀, -, hjoin⟩
  obtain ⟨p, hpMb, hpcl, hpq⟩ := hp
  -- a path in `Mb` from `p` to `1/4`
  have hpath : JoinedIn Mb p (1 / 4 : ℂ) :=
    (hjoin hpMb).symm.trans (hjoin hreal.1)
  obtain ⟨γ, hγmem⟩ := hpath
  have hγ0 : γ 0 = p := Path.source γ
  have hγ1 : γ 1 = (1 / 4 : ℂ) := Path.target γ
  -- `p ≠ c₀`, `1/4 ≠ c₀`
  have hpc : 0 < dist p c₀ := by
    rw [dist_pos]
    intro h
    exact hθ (h ▸ hpcl)
  have hqc : 0 < dist (1 / 4 : ℂ) c₀ := by
    rw [dist_pos]
    exact fun h => hq h.symm
  -- at every positive scale the path meets `Nm` near `c₀`
  have key : ∀ r : ℝ, 0 < r → ∃ t, γ t ∈ Nm ∧ dist c₀ (γ t) < r := by
    intro r hr
    -- shrink the scale so that both `p` and `1/4` are outside the ball, then separate
    set ρ : ℝ := min r (min (dist p c₀) (dist (1 / 4 : ℂ) c₀)) / 2 with hρdef
    have hρpos : 0 < ρ := by
      rw [hρdef]
      have h1 : 0 < min r (min (dist p c₀) (dist (1 / 4 : ℂ) c₀)) := lt_min hr (lt_min hpc hqc)
      linarith
    have hρr : ρ ≤ r := by
      rw [hρdef]
      have := min_le_left r (min (dist p c₀) (dist (1 / 4 : ℂ) c₀))
      linarith
    have hρp : ρ < dist p c₀ := by
      rw [hρdef]
      have h1 := min_le_right r (min (dist p c₀) (dist (1 / 4 : ℂ) c₀))
      have h2 := min_le_left (dist p c₀) (dist (1 / 4 : ℂ) c₀)
      linarith
    have hρq : ρ < dist (1 / 4 : ℂ) c₀ := by
      rw [hρdef]
      have h1 := min_le_right r (min (dist p c₀) (dist (1 / 4 : ℂ) c₀))
      have h2 := min_le_right (dist p c₀) (dist (1 / 4 : ℂ) c₀)
      linarith
    obtain ⟨t, ht1, ht2⟩ := scale_separation hN hJ hwin hθ hreal hX hpMb hpcl hpq hγ0 hγ1
      (fun t => hγmem t) hρpos hρp hρq
    exact ⟨t, ht1, lt_of_lt_of_le ht2 hρr⟩
  -- hence `c₀` is in the closure of `range γ ∩ Nm`
  refine hLB γ (fun t => hγmem t) ?_
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨t, ht1, ht2⟩ := key ε hε
  exact ⟨γ t, ⟨⟨t, rfl⟩, ht1⟩, ht2⟩

/-- **The endgame at the Mandelbar.**  The form in which the paper's main argument consumes the
separation theorem: `Mb` is the mandelbar, `Φ` is Nakane's parameter Böttcher coordinate. -/
theorem mandelbar_not_isPathConnected_of_twoSidedPinch
    (Φ : ℂ → ℂ) (hN : NakaneData LeanEval.ComplexAnalysis.Mandelbar Φ) (hJ : JordanForm)
    (c₀ : ℂ) (Nm : Set ℂ) (a₁ a₂ θ ε : ℝ)
    (hwin : 0 < a₁ - ε ∧ a₁ + ε < θ ∧ θ < a₂ - ε ∧ a₂ + ε < 1)
    (hθ : c₀ ∉ closure (NakaneData.paramRay hN θ))
    (hq : c₀ ≠ (1 / 4 : ℂ))
    (hreal : (1 / 4 : ℂ) ∈ LeanEval.ComplexAnalysis.Mandelbar ∧
      (1 / 4 : ℂ) ∈ closure (NakaneData.paramRay hN 0) ∧
      c₀ ∉ closure (NakaneData.paramRay hN 0))
    (hp : ∃ p : ℂ, p ∈ LeanEval.ComplexAnalysis.Mandelbar ∧
      p ∈ closure (NakaneData.paramRay hN θ) ∧ p ≠ (1 / 4 : ℂ))
    (hLB : ∀ γ : C(unitInterval, ℂ), (∀ t, γ t ∈ LeanEval.ComplexAnalysis.Mandelbar) →
      c₀ ∉ closure (Set.range γ ∩ Nm))
    (hX : ∀ r > 0, ∃ x y : ℂ, segment ℝ x y ⊆ Nm ∩ Metric.ball c₀ r ∧
        ∃ e₁ ∈ segment ℝ x y, ∃ e₂ ∈ segment ℝ x y, e₁ ∉ LeanEval.ComplexAnalysis.Mandelbar ∧
        e₂ ∉ LeanEval.ComplexAnalysis.Mandelbar ∧
        NakaneData.extAngle Φ e₁ ∈ Set.Ioo (a₁ - ε) (a₁ + ε) ∧
        NakaneData.extAngle Φ e₂ ∈ Set.Ioo (a₂ - ε) (a₂ + ε)) :
    ¬ IsPathConnected LeanEval.ComplexAnalysis.Mandelbar :=
  not_isPathConnected_of_twoSidedPinch _ _ hN hJ c₀ Nm a₁ a₂ θ ε hwin hθ hq hreal hp hLB hX

end Work.Top
