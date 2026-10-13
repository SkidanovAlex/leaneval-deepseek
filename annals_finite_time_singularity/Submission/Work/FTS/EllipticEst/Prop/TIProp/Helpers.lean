import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.surrIntegrals

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Elementary bounds for the weighted angular interpolation

This module collects the elementary facts used by the proof of
`Work.FTS.EllipticEst.Prop.thetaInterpCoreOfTraceBounds`:

* positivity of the angular weight `σ = sin(2θ)^{-η}` on the open interval;
* the fact that almost every point of `Iθ` lies in the open interval;
* the tail bound `∫_0^{L/2} σ ≤ 200 L^{1-η}` (and its mirror image);
* the scaled endpoint bound `F² L^{1-η} ≤ 200 P` from `F² ≤ 2L^{3+η}E + 100L^{η-1}P` and
  `L⁴ = P/(16(P+E))`.
-/

namespace Work.FTS.EllipticEst.Prop.TIProp

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

local notation "σ" => Work.FTS.EllipticEst.thEta

/-- `thEta` is nonnegative on the open angular interval. -/
lemma thEta_nonneg_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) : 0 ≤ σ θ :=
  Work.FTS.EllipticEst.thEta_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩

/-- `thEta` is positive on the open angular interval. -/
lemma thEta_pos_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) : 0 < σ θ :=
  Real.rpow_pos_of_pos
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])) _

/-- Almost every point of `Iθ` lies in the open angular interval. -/
lemma ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  change ∀ᵐ θ ∂(volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2))),
    θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc, MeasureTheory.ae_iff]
  refine measure_mono_null ?_ ((Set.toFinite ({0, Real.pi / 2} : Set ℝ)).measure_zero volume)
  rintro θ hθ
  rw [Set.mem_setOf_eq, not_imp] at hθ
  obtain ⟨h1, h2⟩ := hθ
  rw [Set.mem_Icc] at h1
  rw [Set.mem_Ioo] at h2
  rw [not_and_or, not_lt, not_lt] at h2
  rcases h2 with h2 | h2
  · exact Or.inl (le_antisymm h2 h1.1)
  · exact Or.inr (le_antisymm h1.2 h2)

/-- The tail mass of the angular weight: `∫_0^{L/2} σ ≤ 200 L^{1-η}` (open interval form). -/
lemma thEta_tail_left_Ioo {L : ℝ} (hL : 0 < L) (hLp : L ≤ Real.pi / 4) :
    (∫ θ in Set.Ioo (0 : ℝ) (L / 2), σ θ) ≤ 200 * L ^ (1 - Work.Spaces.eta) := by
  have h := Work.EllipticEst.Core.i0Aux.TVRed.thEta_tail_left (L := L) hL hLp
  rwa [MeasureTheory.integral_Icc_eq_integral_Ioc,
    MeasureTheory.integral_Ioc_eq_integral_Ioo] at h

/-- The tail mass of the angular weight at the right endpoint (open interval form). -/
lemma thEta_tail_right_Ioo {L : ℝ} (hL : 0 < L) (hLp : L ≤ Real.pi / 4) :
    (∫ θ in Set.Ioo (Real.pi / 2 - L / 2) (Real.pi / 2), σ θ)
      ≤ 200 * L ^ (1 - Work.Spaces.eta) := by
  have h := Work.EllipticEst.Core.i0Aux.TVRed.thEta_tail_right (L := L) hL hLp
  rwa [MeasureTheory.integral_Icc_eq_integral_Ioc,
    MeasureTheory.integral_Ioc_eq_integral_Ioo] at h

/-- **Scaled endpoint bound.**  If `L⁴ = P/(16(P+E))` and `F² ≤ 2L^{3+η}E + 100L^{η-1}P`, then
`F²L^{1-η} ≤ 200P`. -/
lemma endpoint_scale {F L P E : ℝ} (hL : 0 < L) (hPpos : 0 < P) (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hL4 : L ^ 4 = P / (16 * (P + E)))
    (hF : F ^ 2 ≤ 2 * L ^ (3 + Work.Spaces.eta) * E
      + 100 * L ^ (Work.Spaces.eta - 1) * P) :
    F ^ 2 * L ^ (1 - Work.Spaces.eta) ≤ 200 * P := by
  have h1 : L ^ (3 + Work.Spaces.eta) * L ^ (1 - Work.Spaces.eta) = L ^ (4 : ℝ) := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  have h2 : L ^ (Work.Spaces.eta - 1) * L ^ (1 - Work.Spaces.eta) = 1 := by
    rw [← Real.rpow_add hL,
      show Work.Spaces.eta - 1 + (1 - Work.Spaces.eta) = (0 : ℝ) by ring, Real.rpow_zero]
  have h := mul_le_mul_of_nonneg_right hF (Real.rpow_nonneg hL.le (1 - Work.Spaces.eta))
  have h3 : (2 * L ^ (3 + Work.Spaces.eta) * E + 100 * L ^ (Work.Spaces.eta - 1) * P)
        * L ^ (1 - Work.Spaces.eta)
      = 2 * (L ^ (3 + Work.Spaces.eta) * L ^ (1 - Work.Spaces.eta)) * E
        + 100 * (L ^ (Work.Spaces.eta - 1) * L ^ (1 - Work.Spaces.eta)) * P := by ring
  rw [h3, h1, h2] at h
  have h4 : L ^ (4 : ℝ) * E ≤ P / 16 := by
    have hc : L ^ (4 : ℝ) = L ^ 4 := Real.rpow_natCast L 4
    rw [hc, hL4, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

end Work.FTS.EllipticEst.Prop.TIProp
