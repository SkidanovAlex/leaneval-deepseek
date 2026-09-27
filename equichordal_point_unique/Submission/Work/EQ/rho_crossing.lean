import Mathlib
import Submission.Work.EQ.Defs
import Submission.Work.EQ.SymDefs
import Submission.Work.EQ.normEqCurve_structure
import Submission.Work.EQ.polarPt_reflect

/-!
# Existence of a crossing angle for a normalised two-point equichordal curve

For a normalised equichordal curve (`NormEqCurve a ρ₁ ρ₂`, `0 < a < 1`) whose axis is not
centred at the origin (`hne`), the "gap" function

  `g ψ = ρ₂ ψ - ρ₁ (π - ψ)`

changes sign strictly between `ψ = 0` and `ψ = π`:

* the structure lemma `nec_axis_points_eq` gives `ρ₂ 0 = ρ₁ 0 - a`;
* the chord identities give `ρ₁ π = 1 - ρ₁ 0` and `ρ₂ π = 1 - ρ₂ 0`;

hence `g 0 = 2 ρ₁ 0 - 1 - a` and `g π = -(2 ρ₁ 0 - 1 - a)`, while `hne` is precisely
`θ = 2 ρ₁ 0 - 1 - a ≠ 0` written in terms of real parts of the two axis points.  As `g` is
continuous, the intermediate value theorem yields `ψ ∈ (0, π)` with `g ψ = 0`, i.e.
`ρ₂ ψ = ρ₁ (π - ψ)`.
-/

namespace Work.EQ

open Complex

theorem rho_crossing {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ρ₁ ρ₂ : ℝ → ℝ}
    (hC : NormEqCurve a ρ₁ ρ₂)
    (hne : (polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi).re
        + (polarPt (-(a/2)) (ρ₁ 0) 0).re ≠ 0) :
    ∃ ψ : ℝ, 0 < ψ ∧ ψ < Real.pi ∧ ρ₂ ψ = ρ₁ (Real.pi - ψ) := by
  obtain ⟨hcont₁, hcont₂, hpos₁, hpos₂, hchord₁, hchord₂, hrange⟩ := hC
  -- the two axis points coincide
  have hax := nec_axis_points_eq ha0 hpos₁ hpos₂ hchord₁ hchord₂ hrange
  -- `ρ₂ 0 = ρ₁ 0 - a`
  have hy0 : ρ₂ 0 = ρ₁ 0 - a := by
    have h := congrArg Complex.re hax.1
    rw [nec_polarPt_zero, nec_polarPt_zero] at h
    simp only [Complex.ofReal_re] at h
    linarith
  -- `ρ₁ π = 1 - ρ₁ 0`
  have hxpi : ρ₁ Real.pi = 1 - ρ₁ 0 := by
    have h := hchord₁ 0
    rw [zero_add] at h
    linarith
  -- `ρ₂ π = 1 - ρ₂ 0`
  have hypi : ρ₂ Real.pi = 1 - ρ₂ 0 := by
    have h := hchord₂ 0
    rw [zero_add] at h
    linarith
  -- `hne` is exactly `2 ρ₁ 0 - 1 - a ≠ 0`
  have hne' : (2 * ρ₁ 0 - 1 - a) ≠ 0 := by
    have h := hne
    rw [nec_polarPt_pi, nec_polarPt_zero] at h
    simp only [Complex.ofReal_re] at h
    intro hc
    apply h
    linarith
  -- the values of the gap function at the two endpoints
  have hg0 : ρ₂ 0 - ρ₁ (Real.pi - 0) = 2 * ρ₁ 0 - 1 - a := by
    rw [sub_zero]; linarith
  have hgpi : ρ₂ Real.pi - ρ₁ (Real.pi - Real.pi) = -(2 * ρ₁ 0 - 1 - a) := by
    rw [sub_self]; linarith
  have hcont_g : Continuous (fun ψ : ℝ => ρ₂ ψ - ρ₁ (Real.pi - ψ)) :=
    hcont₂.sub (hcont₁.comp (continuous_const.sub continuous_id))
  have hcont_f : Continuous (fun ψ : ℝ => ρ₁ (Real.pi - ψ) - ρ₂ ψ) :=
    (hcont₁.comp (continuous_const.sub continuous_id)).sub hcont₂
  rcases lt_or_gt_of_ne hne' with hlt | hgt
  · -- `g 0 < 0 < g π`
    have hmem : (0:ℝ) ∈ Set.Ioo ((fun ψ : ℝ => ρ₂ ψ - ρ₁ (Real.pi - ψ)) 0)
        ((fun ψ : ℝ => ρ₂ ψ - ρ₁ (Real.pi - ψ)) Real.pi) := by
      rw [Set.mem_Ioo]; constructor <;> linarith
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo (le_of_lt Real.pi_pos)
      hcont_g.continuousOn hmem
    refine ⟨x, hx.1, hx.2, ?_⟩
    exact sub_eq_zero.mp hfx
  · -- `g 0 > 0 > g π`, apply IVT to `-g`
    have hmem : (0:ℝ) ∈ Set.Ioo ((fun ψ : ℝ => ρ₁ (Real.pi - ψ) - ρ₂ ψ) 0)
        ((fun ψ : ℝ => ρ₁ (Real.pi - ψ) - ρ₂ ψ) Real.pi) := by
      rw [Set.mem_Ioo]; constructor <;> linarith
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo (le_of_lt Real.pi_pos)
      hcont_f.continuousOn hmem
    refine ⟨x, hx.1, hx.2, ?_⟩
    linarith [sub_eq_zero.mp hfx]

end Work.EQ
