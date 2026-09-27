import Mathlib
import Submission.Work.EQ.Defs
import Submission.Work.EQ.hetero_box
import Submission.Work.EQ.arc_iterate_aux
import Submission.Work.EQ.arc_eqU_maps
import Submission.Work.EQ.normEqCurve_periodic_and_sum
import Submission.Work.EQ.polarPt_basic

namespace Work.EQ

open Complex

/-- For `θ ∈ (0, π)` the point `arcPt a ρ₁ θ = polarPt (-(a/2)) (ρ₁ θ) θ` of the normalised
equichordal curve lies on the polar graph of `ρ₂` about `O₂ = a/2` at an angle `ψ ∈ (0, π)`,
and the half-map `eqU a` sends it to the arc point at that angle.  (This is the `key`
computation inside `arc_eqU_maps`: combine `NormEqCurve`'s range equality with
`exists_angle_of_mem_range` to find `ψ`, then compute `eqU` using `polarPt_basic`,
`normEqCurve_periodic_and_sum`'s sum relation `ρ₁ ψ = 1 - ρ₂ ψ`, and the Cartesian forms
`arcPt_eq_polarPt`, `polarPt_sub_center` of `arc_iterate_aux`.) -/
theorem arcPt_O2_repr {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ρ₁ ρ₂ : ℝ → ℝ}
    (hC : NormEqCurve a ρ₁ ρ₂) (hs₁ : ∀ θ, ρ₁ (-θ) = ρ₁ θ) (hs₂ : ∀ θ, ρ₂ θ = ρ₁ (Real.pi - θ))
    {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    ∃ ψ : ℝ, 0 < ψ ∧ ψ < Real.pi ∧
      arcPt a ρ₁ θ = polarPt (a / 2) (ρ₂ ψ) ψ ∧ eqU a (arcPt a ρ₁ θ) = arcPt a ρ₁ ψ := by
  have _ha0 := ha0
  have _ha1 := ha1
  obtain ⟨hper₁', hper₂', hρ₂_eq⟩ := normEqCurve_periodic_and_sum hC hs₁ hs₂
  obtain ⟨-, -, hρ₁pos, hρ₂pos, -, -, hrange⟩ := hC
  -- `P θ` belongs to the polar graph of `ρ₂` about `O₂ = a/2`, by the range equality
  have hmem : arcPt a ρ₁ θ ∈ Set.range (fun φ => polarPt (a / 2) (ρ₂ φ) φ) := by
    rw [arcPt_eq_polarPt, ← hrange]
    exact ⟨θ, rfl⟩
  -- and it lies strictly above `O₂`, since `(P θ - O₂).im = (P θ).im = ρ₁ θ * sin θ > 0`
  have him : 0 < (arcPt a ρ₁ θ - ((a / 2 : ℝ) : ℂ)).im := by
    have h1 : (arcPt a ρ₁ θ - ((a / 2 : ℝ) : ℂ)).im = (arcPt a ρ₁ θ).im := by simp
    rw [h1, arcPt_im]
    exact mul_pos (hρ₁pos θ) (Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ)
  obtain ⟨φ, hφ0, hφπ, hφ⟩ := exists_angle_of_mem_range hper₂' hρ₂pos hmem him
  refine ⟨φ, hφ0, hφπ, hφ, ?_⟩
  obtain ⟨-, hsub, hnorm, -⟩ := polarPt_basic (c := a / 2) (r := ρ₂ φ) (θ := φ) (hρ₂pos φ)
  -- `P θ - O₂ = ρ₂ φ * exp (φ I)`, hence `(P θ - O₂)/|P θ - O₂| = exp (φ I)`
  have hz : arcPt a ρ₁ θ - ((a / 2 : ℝ) : ℂ)
      = (ρ₂ φ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) := by
    rw [hφ, hsub]
  have hzdiv : (arcPt a ρ₁ θ - ((a / 2 : ℝ) : ℂ)) /
      ((‖arcPt a ρ₁ θ - ((a / 2 : ℝ) : ℂ)‖ : ℝ) : ℂ)
      = Complex.exp ((φ : ℂ) * Complex.I) := by
    have hne : ((ρ₂ φ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hρ₂pos φ))
    have hn : ‖arcPt a ρ₁ θ - ((a / 2 : ℝ) : ℂ)‖ = ρ₂ φ := by
      rw [hz, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
        Complex.norm_of_nonneg (le_of_lt (hρ₂pos φ))]
    rw [hn, hz, div_eq_iff hne]
    ring
  -- so `eqU a (P θ) = -P θ + exp (φ I) = -O₂ + (1 - ρ₂ φ) exp (φ I) = P φ`
  have h1 : eqU a (arcPt a ρ₁ θ) = -arcPt a ρ₁ θ + Complex.exp ((φ : ℂ) * Complex.I) := by
    unfold eqU
    rw [hzdiv]
  rw [h1, hφ, arcPt_eq_polarPt]
  have hρ₂φ : ρ₁ φ = 1 - ρ₂ φ := by linarith [hρ₂_eq φ]
  rw [hρ₂φ]
  simp only [polarPt]
  push_cast
  ring_nf

end Work.EQ

-- The requested file header bracketed the statement with `namespace Work.EQ` twice, which
-- places the declaration at `Work.EQ.Work.EQ.arcPt_O2_repr`.  The name requested for this
-- lemma is `Work.EQ.arcPt_O2_repr` (declared above); the alias below keeps the doubly
-- bracketed name available as well, with literally the same statement.
namespace Work.EQ

namespace Work.EQ

open Complex

theorem arcPt_O2_repr {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ρ₁ ρ₂ : ℝ → ℝ}
    (hC : NormEqCurve a ρ₁ ρ₂) (hs₁ : ∀ θ, ρ₁ (-θ) = ρ₁ θ) (hs₂ : ∀ θ, ρ₂ θ = ρ₁ (Real.pi - θ))
    {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    ∃ ψ : ℝ, 0 < ψ ∧ ψ < Real.pi ∧
      arcPt a ρ₁ θ = polarPt (a / 2) (ρ₂ ψ) ψ ∧ eqU a (arcPt a ρ₁ θ) = arcPt a ρ₁ ψ :=
  _root_.Work.EQ.arcPt_O2_repr ha0 ha1 hC hs₁ hs₂ hθ0 hθπ

end Work.EQ

end Work.EQ
