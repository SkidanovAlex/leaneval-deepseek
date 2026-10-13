import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB6.UprimeAux.Defs
import Submission.Work.FTS_StreamBdry.SB6.UprimeAux.OdeFacts
import Submission.Work.FTS_StreamBdry.SB6.UprimeAux.Temps

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB6.UprimeAux.OdeBound1` — the two-point bound and the crude pointwise bound

If `u'' = H - c u'` on `(0, π/2)` with `|H| ≤ A / sin 2θ + C`, then `G = wfun · u'` satisfies
`G' = wfun · H`, so `|G θ - G ξ| ≤ ∫_ξ^θ gwt A C` (the comparison argument, using that
`gwt A C` is continuous so its primitive is differentiable).  Moreover, the extra global bound
`|sin 2θ · u'| ≤ C₁` gives `|G ξ| ≤ C₁ · wfun ξ / sin 2ξ`, which vanishes at both endpoints.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB6.UprimeAux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **Two-point bound.**  `|G θ - G ξ| ≤ ∫_ξ^θ gwt A C` for `0 < ξ ≤ θ < π/2`. -/
lemma two_point {u H : ℝ → ℝ → ℝ} {z A C : ℝ}
    (hode : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (u1fun u z)
        (H z θ - (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ) * u1fun u z θ) θ)
    (hH : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |H z θ| ≤ A / Real.sin (2 * θ) + C)
    {ξ θ : ℝ} (hξ : 0 < ξ) (hξθ : ξ ≤ θ) (hθ : θ < Real.pi / 2) :
    |wfun θ * u1fun u z θ - wfun ξ * u1fun u z ξ| ≤ ∫ t in ξ..θ, gwt A C t := by
  have hggcont : Continuous (fun t => gwt A C t) := continuous_gwt A C
  have hmem : ∀ x ∈ Set.Icc ξ θ, x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
    ⟨lt_of_lt_of_le hξ hx.1, lt_of_le_of_lt hx.2 hθ⟩
  have hmem' : ∀ x ∈ Set.Ico ξ θ, x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
    ⟨lt_of_lt_of_le hξ hx.1, lt_trans hx.2 hθ⟩
  have hG' : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (wfun * u1fun u z) (wfun x * H z x) x := by
    intro x hx
    have h1 := hode x hx
    have h2 := Wderiv hx
    have h3 := h2.mul h1
    have hv : (wfun x * (4 * Real.cos (2 * x) / Real.sin (2 * x) - Real.tan x)) * u1fun u z x
        + wfun x * (H z x - (4 * Real.cos (2 * x) / Real.sin (2 * x) - Real.tan x)
          * u1fun u z x) = wfun x * H z x := by ring
    rw [hv] at h3
    exact h3
  have hineq : ∀ x ∈ Set.Ico ξ θ, wfun x * H z x ≤ gwt A C x := by
    intro x hx
    have hxI := hmem' x hx
    have hwx : 0 ≤ wfun x := le_of_lt (Wpos hxI)
    have hHx := hH x hxI
    calc wfun x * H z x ≤ wfun x * (A / Real.sin (2 * x) + C) :=
          mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hHx) hwx
      _ = gwt A C x := by rw [gwt_def]; ring
  have hGcont : ContinuousOn (wfun * u1fun u z) (Set.Icc ξ θ) := fun x hx =>
    ((hG' x (hmem x hx)).continuousAt).continuousWithinAt
  have hprim : ContinuousOn (fun t => ∫ s in ξ..t, gwt A C s) (Set.Icc ξ θ) := by
    intro x hx
    have hint : IntervalIntegrable (fun t => gwt A C t) volume ξ x :=
      hggcont.intervalIntegrable ξ x
    have hsm : StronglyMeasurableAtFilter (fun t => gwt A C t) (𝓝 x) volume :=
      hggcont.stronglyMeasurableAtFilter volume (𝓝 x)
    exact ((intervalIntegral.integral_hasDerivAt_right hint hsm
      hggcont.continuousAt).continuousAt).continuousWithinAt
  have hB' : ∀ x ∈ Set.Ico ξ θ,
      HasDerivWithinAt (fun t => wfun ξ * u1fun u z ξ + ∫ s in ξ..t, gwt A C s) (gwt A C x)
        (Set.Ici x) x := by
    intro x hx
    have hint : IntervalIntegrable (fun t => gwt A C t) volume ξ x :=
      hggcont.intervalIntegrable ξ x
    have hsm : StronglyMeasurableAtFilter (fun t => gwt A C t) (𝓝 x) volume :=
      hggcont.stronglyMeasurableAtFilter volume (𝓝 x)
    exact ((intervalIntegral.integral_hasDerivAt_right hint hsm
      hggcont.continuousAt).const_add (wfun ξ * u1fun u z ξ)).hasDerivWithinAt
  have hup : wfun θ * u1fun u z θ ≤ wfun ξ * u1fun u z ξ + ∫ t in ξ..θ, gwt A C t :=
    image_le_of_deriv_right_le_deriv_boundary (f := wfun * u1fun u z)
      (f' := fun t => wfun t * H z t) (a := ξ) (b := θ)
      (B := fun t => wfun ξ * u1fun u z ξ + ∫ s in ξ..t, gwt A C s)
      (B' := fun t => gwt A C t)
      hGcont (fun x hx => (hG' x (hmem' x hx)).hasDerivWithinAt)
      (by simp) (continuousOn_const.add hprim) hB' hineq ⟨hξθ, le_refl θ⟩
  have hlow : wfun ξ * u1fun u z ξ ≤ wfun θ * u1fun u z θ + ∫ t in ξ..θ, gwt A C t := by
    have hmain : -(wfun θ * u1fun u z θ)
        ≤ -(wfun ξ * u1fun u z ξ) + ∫ t in ξ..θ, gwt A C t :=
      image_le_of_deriv_right_le_deriv_boundary (f := fun t => -(wfun t * u1fun u z t))
        (f' := fun t => -(wfun t * H z t)) (a := ξ) (b := θ)
        (B := fun t => -(wfun ξ * u1fun u z ξ) + ∫ s in ξ..t, gwt A C s)
        (B' := fun t => gwt A C t)
        hGcont.neg (fun x hx => (hG' x (hmem' x hx)).hasDerivWithinAt.neg) (by simp)
        (continuousOn_const.add hprim) (by
          intro x hx
          have hint : IntervalIntegrable (fun t => gwt A C t) volume ξ x :=
            hggcont.intervalIntegrable ξ x
          have hsm : StronglyMeasurableAtFilter (fun t => gwt A C t) (𝓝 x) volume :=
            hggcont.stronglyMeasurableAtFilter volume (𝓝 x)
          exact ((intervalIntegral.integral_hasDerivAt_right hint hsm
            hggcont.continuousAt).const_add (-(wfun ξ * u1fun u z ξ))).hasDerivWithinAt)
        (by
          intro x hx
          have hxI := hmem' x hx
          have hwx : 0 ≤ wfun x := le_of_lt (Wpos hxI)
          have hHx := hH x hxI
          calc -(wfun x * H z x) = wfun x * (-(H z x)) := by ring
            _ ≤ wfun x * (A / Real.sin (2 * x) + C) :=
                mul_le_mul_of_nonneg_left
                  (le_trans (neg_le_abs (H z x)) hHx) hwx
            _ = gwt A C x := by rw [gwt_def]; ring)
        ⟨hξθ, le_refl θ⟩
    linarith
  rw [abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩

/-- **Crude bound**: `|sin 2θ · u'| ≤ C₁` gives `|G ξ| ≤ C₁ · wfun ξ / sin 2ξ`. -/
lemma crude_G {u H : ℝ → ℝ → ℝ} {z C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hcrude : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Real.sin (2 * θ) * u1fun u z θ| ≤ C₁)
    {ξ : ℝ} (hξ : ξ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |wfun ξ * u1fun u z ξ| ≤ C₁ * (wfun ξ / Real.sin (2 * ξ)) := by
  have hw : 0 ≤ wfun ξ := le_of_lt (Wpos hξ)
  have hs : 0 < Real.sin (2 * ξ) := by
    rw [Real.sin_two_mul]
    have h1 : 0 < Real.sin ξ :=
      Real.sin_pos_of_pos_of_lt_pi hξ.1 (by linarith [hξ.2, Real.pi_pos])
    have h2 : 0 < Real.cos ξ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hξ.1], hξ.2⟩
    positivity
  have h1 : |wfun ξ * u1fun u z ξ| = wfun ξ * |u1fun u z ξ| := by
    rw [abs_mul, abs_of_nonneg hw]
  have h2 : |u1fun u z ξ| ≤ C₁ / Real.sin (2 * ξ) := by
    rw [le_div_iff₀ hs]
    calc |u1fun u z ξ| * Real.sin (2 * ξ)
        = |Real.sin (2 * ξ) * u1fun u z ξ| := by rw [abs_mul, abs_of_pos hs, mul_comm]
      _ ≤ C₁ := hcrude ξ hξ
  rw [h1]
  calc wfun ξ * |u1fun u z ξ| ≤ wfun ξ * (C₁ / Real.sin (2 * ξ)) :=
        mul_le_mul_of_nonneg_left h2 hw
    _ = C₁ * (wfun ξ / Real.sin (2 * ξ)) := by ring

end Work.FTS_StreamBdry.SB6.UprimeAux
