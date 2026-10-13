/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/SixMixed.lean` — the per-`z` bound for a mixed slot of the
# level-`6` integrand, from the level-`8` angular estimate

The mixed half of the per-`z` energy bound of the level-`6` `ℋ`-integrand:

  `∫_θ (D_z^jD_θ^i f · W)² ≤ C (1 + w z ^ 2) · |f|²_{ℋ⁸}`   for `1 ≤ i`, `i + j ≤ 6`, `z > 0`,

obtained from the level-`8` angular window estimate `Work.FTS.EpsEngine.sliceAng_le8` by peeling
off the radial weight `W = w z · sin(2θ)^{-γ/2}` (`Wt_sq_eq`).  This is the verbatim `4 ↦ 6`,
`6 ↦ 8` shift of `Work.FTS.StrongEps.E5Aux.mixed_slot_perz_le`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EpsEngine.sliceAng_le8
import Submission.Work.H2.T1Q.PwBdQ
import Submission.Work.FTS.EllipticEst.SliceDecompDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EpsEngine

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The per-`z` bound for a mixed slot of the level-`6` integrand.** -/
theorem mixed_slot_perz_le8 :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ {f : ℝ → ℝ → ℝ},
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 8 f →
      ∀ (i j : ℕ), 1 ≤ i → i + j ≤ 6 → ∀ {z : ℝ}, 0 < z →
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ C * (1 + (Work.Spaces.w z) ^ 2) * Work.Spaces.HkSq α 8 f := by
  obtain ⟨CB, hCBpos, hCB⟩ := sliceAng_le8
  refine ⟨CB, hCBpos, ?_⟩
  intro α hα f hF hmem i j hi hij z hz
  obtain ⟨hα0, hα1⟩ := hα
  have hcongr :
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
        = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.mixed j i f z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [← MeasureTheory.integral_const_mul]
    refine Work.FTS.EllipticEst.setIntegral_Iθ_congr_of_forall_Ioo (fun θ hθ => ?_)
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    rw [mul_pow, Work.H2.T1Q.Wt_sq_eq α z θ hs]
    ring
  rw [hcongr]
  have hb := hCB α f j i hα0 hα1 hF hmem hi (by omega) z hz
  have hHk := Work.Spaces.HkSq_nonneg α 8 f
  calc (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed j i f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ (Work.Spaces.w z) ^ 2 * (CB * Work.Spaces.HkSq α 8 f) :=
        mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ ≤ CB * (1 + (Work.Spaces.w z) ^ 2) * Work.Spaces.HkSq α 8 f := by
        nlinarith [hCBpos, hHk, sq_nonneg (Work.Spaces.w z)]

end Work.FTS.EpsEngine
