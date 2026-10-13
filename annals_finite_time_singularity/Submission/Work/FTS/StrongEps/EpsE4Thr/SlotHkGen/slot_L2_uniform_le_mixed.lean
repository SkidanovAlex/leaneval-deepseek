/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/SlotHkGen/slot_L2_uniform_le_mixed.lean` — the uniform
# in-time `L²` bound on a *mixed* slot with the `γ`-weight

`EnergyFinalAssembly.slot_L2_uniform_le` gives the uniform bound
`∫ (mixed j i (xd σ))²·w²σ^c ≤ K` from a uniform `ℋ⁴`-size of the family `xd`, under the exponent
hypothesis `c ≥ -η`.  That exponent is what a *pure* `D_z`-slot (`i = 0`) needs; a *mixed* slot
(`i ≥ 1`) only needs `c ≥ -γ(α)` (the `D_θ`-part of the slot fits into the `w²σ^{-γ}` summand of
`HkIntegrand`).

This module records the mixed case, which is what the `rhoGam α = w²σ^{-γ(α)}` bundles of the level
four energy consume (`γ(α) = 1 + α/10 > 1 > η = 99/100`, so `-γ(α) < -η` and the older statement
does not apply).  The proof is the `4`-version with `integral_slot_sq_rpow_le_HkSq` replaced by
`SlotHkGen.integral_slot_sq_rpow_le_HkSq_mixed`.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.SlotHkGen.integral_slot_sq_rpow_le_HkSq_mixed
import Submission.Work.FTS.StrongEps.EpsE4Thr.EnergyFinalAssembly

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.SlotHkGen

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **The uniform `L²` bound on a *mixed* slot of the derivative family.**  If the family has a
uniform `ℋ⁴`-size `R`, every slot `mixed j i` with `1 ≤ i` and `j + i ≤ 4` has weighted
square-integral `≤ R²` uniformly in the fake time, for every weight `w²σ^c` with `c ≥ -γ(α)`. -/
theorem slot_L2_uniform_le_mixed {α c : ℝ} {j i : ℕ} {xd : ℝ → Fn} {T : ℝ}
    (hα : 0 < α) (hc : -(Work.Spaces.gam α) ≤ c) (hi : 1 ≤ i) (hji : j + i ≤ 4)
    (hsm : ∀ σ ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (xd σ))
    (hmem : ∀ σ ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkMem α 4 (xd σ))
    (hR : ∃ R : ℝ, 0 ≤ R ∧ ∀ σ ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkNorm α 4 (xd σ) ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ ∈ Set.Icc (0 : ℝ) T,
      ∫ p : ℝ × ℝ, (Work.Spaces.mixed j i (xd σ) p.1 p.2) ^ 2
        * (Work.Spaces.w p.1 ^ 2 * Real.sin (2 * p.2) ^ c)
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ≤ K := by
  obtain ⟨R, hR0, hRb⟩ := hR
  refine ⟨R ^ 2, sq_nonneg R, fun σ hσ => ?_⟩
  have h1 := integral_slot_sq_rpow_le_HkSq_mixed (α := α) (g := xd σ) (c := c) (j := j) (i := i)
    hα hc hi hji (hsm σ hσ) (hmem σ hσ)
  have h2 : Work.Spaces.HkSq α 4 (xd σ) = (Work.Spaces.HkNorm α 4 (xd σ)) ^ 2 := by
    rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 _)]
  have h3 : (∫ p : ℝ × ℝ, (Work.Spaces.mixed j i (xd σ) p.1 p.2) ^ 2
        * (Work.Spaces.w p.1 ^ 2 * Real.sin (2 * p.2) ^ c)
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = ∫ p : ℝ × ℝ, (Work.Spaces.w p.1 ^ 2 * Real.sin (2 * p.2) ^ c)
          * (Work.Spaces.mixed j i (xd σ) p.1 p.2) ^ 2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)
  rw [h3]
  refine le_trans h1 ?_
  rw [h2]
  exact pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 _) (hRb σ hσ) 2

end Work.FTS.StrongEps.EpsE4Thr.SlotHkGen
