/-
Copyright: work module for the Elgindi finite-time singularity project.

# Integrability of the crossed slot pairing against a single `sin(2θ)^c` weight

`Work.FTS.StrongEps.EpsE4Thr.integrable_cross_slot_rpow` is the `c`-parameterised companion of
`integrable_wip_slot_cross`: for two functions `f`, `h` which are smooth on the open quadrant and
honestly in `ℋ⁴`, and for a mixed slot `D_z^a D_θ^b` of order `a + b ≤ 4`, the pairing

  `∫∫ D_z^a D_θ^b f · D_z^a D_θ^b h · (w² σ^c)`,   `σ = sin(2θ)`,

is finite for the product measure `mup` against **every** exponent `c ≥ -η` (not merely the three
weights `-η`, `0`, `-γ(α)` of the energy recursion).

The proof is a direct application of the already-proved general assembly
`Work.FTS.StrongEps.EpsE4Thr.integrable_mixed_pairing` (AM–GM on the open quadrant against the
`ℋ⁴`-integrands); the only work is the two pointwise slot dominations

  `crossWt c z θ · (D_z^a D_θ^b g z θ)² ≤ HkIntegrand α 4 g z θ`   (`g = f, h`):

* for `b = 0` (a pure `D_z`-slot) the exponent needed is `c ≥ -η`, which is exactly the
  hypothesis — this is `SlotWt.dzSlot_weight_le_HkIntegrand4`;
* for `b ≥ 1` (a mixed slot) the exponent needed is `c ≥ -γ(α)`, which follows from `c ≥ -η`
  because `η < 1 < γ(α)` — this is `SlotWt.mixedSlot_weight_le_HkIntegrand4`.

A.e. strong measurability of the integrand is `SlotWt.aesm_mixed_pair_weight` (continuity on the
open quadrant, which is co-null for `mup`).

Everything in this file is `sorry`-free.
-/
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.integrable_wip_slot_cross
import Submission.Work.FTS.StrongEps.EpsE4Thr.WipEqIntegral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.StrongEps.EpsE4Thr

set_option autoImplicit false

/-- **The pointwise slot domination for the `c`-parameterised weight.**
For `c ≥ -η` and any slot `(a,b)` with `a + b ≤ 4`, the weighted square
`w²·sin(2θ)^c·(D_z^a D_θ^b g)²` is bounded pointwise by `HkIntegrand α 4 g` on the open
quadrant.  The `b = 0` slot is a `D_z`-slot (`c ≥ -η` suffices) and the `b ≥ 1` slots are mixed
slots (`c ≥ -γ(α)` suffices, and `-γ(α) ≤ -η`). -/
theorem crossWt_mixed_sq_le_HkIntegrand {α c : ℝ} {a b : ℕ} {g : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hc : -(Work.Spaces.eta) ≤ c) (hab : a + b ≤ 4) {z θ : ℝ}
    (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    crossWt c z θ * (Work.Spaces.mixed a b g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have heta_gam : Work.Spaces.eta ≤ Work.Spaces.gam α := by
    have h1 : 1 < Work.Spaces.gam α := Work.Spaces.one_lt_gam hα
    have h2 : Work.Spaces.eta < 1 := Work.Spaces.eta_lt_one
    linarith
  by_cases hb : b = 0
  · subst hb
    have h4 : a ≤ 4 := by omega
    simpa only [Work.Spaces.mixed_zero_right, crossWt] using
      Work.FTS.StrongEps.EpsE4Thr.SlotWt.dzSlot_weight_le_HkIntegrand4
        (α := α) (c := c) (g := g) (m := a) hc h4 ⟨hθ, hθ2⟩
  · have hb1 : 1 ≤ b := by omega
    have hcg : -(Work.Spaces.gam α) ≤ c := by linarith
    exact Work.FTS.StrongEps.EpsE4Thr.SlotWt.mixedSlot_weight_le_HkIntegrand4
      (α := α) (c := c) (g := g) (a := b) (b := a) hα hcg hb1 (by omega) ⟨hθ, hθ2⟩

theorem integrable_cross_slot_rpow {α c : ℝ} {a b : ℕ} {f h : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hc : -(Work.Spaces.eta) ≤ c) (hab : a + b ≤ 4)
    (hsmf : Work.FTS.EllipticEst.SmoothOpen f) (hsmh : Work.FTS.EllipticEst.SmoothOpen h)
    (hmemf : Work.Spaces.HkMem α 4 f) (hmemh : Work.Spaces.HkMem α 4 h) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.mixed a b f p.1 p.2 * Work.Spaces.mixed a b h p.1 p.2
        * (Work.Spaces.w p.1 ^ 2 * Real.sin (2 * p.2) ^ c))
      Work.FTS.StrongEps.EpsE4Thr.mup := by
  have hmain := integrable_mixed_pairing (α := α) (c := c) (f := f) (h := h) (j := a) (i := b)
    hsmf hsmh hmemf hmemh
    (fun z θ _ hθ hθ2 => crossWt_mixed_sq_le_HkIntegrand (g := f) hα hc hab hθ hθ2)
    (fun z θ _ hθ hθ2 => crossWt_mixed_sq_le_HkIntegrand (g := h) hα hc hab hθ hθ2)
    (Work.FTS.StrongEps.EpsE4Thr.SlotWt.aesm_mixed_pair_weight (c := c) hsmf hsmh)
  simpa only [Work.FTS.StrongEps.EpsE4Thr.mup, crossWt] using hmain

end Work.FTS.StrongEps.EpsE4Thr
