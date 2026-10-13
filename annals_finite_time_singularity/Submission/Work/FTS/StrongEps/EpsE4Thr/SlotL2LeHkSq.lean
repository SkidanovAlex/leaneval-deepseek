/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/SlotL2LeHkSq.lean` — the weighted `L²` slot bound

The energy identity of the `ε`-scheme consumes, at every slot, the *uniform-in-time* bound

  `∫∫ (D_z^j D_θ^i f_σ)² · ρ ≤ K`   (`ρ ∈ {rhoEta, rhoW, rhoGam α}`)

on the derivative slots of the flow (`wip_bound_volterra`'s `hK`/`hf`) and the corresponding
integrability.  The clean source of such bounds is `HkMem α 4` together with a *uniform* `ℋ⁴`-size
bound (`HkNorm_epsRHSP_le`).

This module records the general weighted slot bound, for the whole one-parameter family of weights
`w²·sin(2θ)^c` with `c ≥ -η` (which covers all three):

  `∫_μ w²·sin(2θ)^c · (D_z^j D_θ^i f)² ≤ HkSq α 4 f`   for `j + i ≤ 4`,

proved by the pointwise domination of the slot by `HkIntegrand` on the open quadrant
(`SlotWt.dzSlot_weight_le_HkIntegrand4` for `i = 0`, `SlotWt.mixedSlot_weight_le_HkIntegrand4`
otherwise) followed by `∫_μ HkIntegrand = HkSq` (`integral_integral`).

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.EpsE4Thr.WipSlotIntegrable
import Submission.Work.FTS.StrongEps.EpsE4Thr.SlotWt.dzSlot_weight_le_HkIntegrand4
import Submission.Work.FTS.StrongEps.EpsE4Thr.SlotWt.mixedSlot_weight_le_HkIntegrand4

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

set_option autoImplicit false

/-- **The weighted `L²` slot bound.**  For `f` smooth on the open quadrant and honestly in `ℋ⁴`,
every slot `D_z^j D_θ^i f` with `j + i ≤ 4` has weighted square-integral bounded by `HkSq α 4 f`,
for every weight `w²σ^c` with `c ≥ -η` (`σ = sin 2θ`). -/
theorem integral_slot_sq_rpow_le_HkSq {α : ℝ} {g : ℝ → ℝ → ℝ} {c : ℝ} {j i : ℕ}
    (hα : 0 < α) (hc : -(Work.Spaces.eta) ≤ c) (hji : j + i ≤ 4)
    (hsm : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g) :
    ∫ p : ℝ × ℝ, (Work.Spaces.w p.1 ^ 2 * Real.sin (2 * p.2) ^ c)
        * (Work.Spaces.mixed j i g p.1 p.2) ^ 2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))
      ≤ Work.Spaces.HkSq α 4 g := by
  have hHk : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 g p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    HkIntegrand_integrable_prod_fts (k := 4) hsm hmem
  -- the pointwise domination on the open quadrant
  have hdom : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      (Work.Spaces.w z ^ 2 * Real.sin (2 * θ) ^ c)
        * (Work.Spaces.mixed j i g z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
    intro z θ hz hθ hθ2
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi
      have h4 : j ≤ 4 := by omega
      exact Work.FTS.StrongEps.EpsE4Thr.SlotWt.dzSlot_weight_le_HkIntegrand4
        (α := α) (c := c) (g := g) (m := j) hc h4 ⟨hθ, hθ2⟩
    · have heta_gam : Work.Spaces.eta ≤ Work.Spaces.gam α := by
        have h1 : 1 < Work.Spaces.gam α := Work.Spaces.one_lt_gam hα
        have h2 : Work.Spaces.eta < 1 := Work.Spaces.eta_lt_one
        linarith
      have hcg : -(Work.Spaces.gam α) ≤ c := by linarith
      exact Work.FTS.StrongEps.EpsE4Thr.SlotWt.mixedSlot_weight_le_HkIntegrand4
        (α := α) (c := c) (g := g) (a := i) (b := j) hα hcg hi (by omega) ⟨hθ, hθ2⟩
  have hae : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.Spaces.w p.1 ^ 2 * Real.sin (2 * p.2) ^ c)
        * (Work.Spaces.mixed j i g p.1 p.2) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 g p.1 p.2 := by
    filter_upwards [ae_mem_openQuadrant_fts] with p hp
    exact hdom p.1 p.2 hp.1 hp.2.1 hp.2.2
  have hnn : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      0 ≤ (Work.Spaces.w p.1 ^ 2 * Real.sin (2 * p.2) ^ c)
        * (Work.Spaces.mixed j i g p.1 p.2) ^ 2 := by
    filter_upwards [ae_mem_openQuadrant_fts] with p hp
    refine mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ?_ c)) (sq_nonneg _)
    exact (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
      (by linarith [hp.2.2, Real.pi_pos])).le
  have hle := MeasureTheory.integral_mono_of_nonneg hnn hHk hae
  have heq : (∫ p : ℝ × ℝ, Work.Spaces.HkIntegrand α 4 g p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = Work.Spaces.HkSq α 4 g := by
    rw [Work.Spaces.HkSq]
    exact (MeasureTheory.integral_integral
      (f := fun z θ => Work.Spaces.HkIntegrand α 4 g z θ) hHk).symm
  calc (∫ p : ℝ × ℝ, (Work.Spaces.w p.1 ^ 2 * Real.sin (2 * p.2) ^ c)
        * (Work.Spaces.mixed j i g p.1 p.2) ^ 2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      ≤ ∫ p : ℝ × ℝ, Work.Spaces.HkIntegrand α 4 g p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := hle
    _ = Work.Spaces.HkSq α 4 g := heq

end Work.FTS.StrongEps.EpsE4Thr
