import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.AeI1Fts.Defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.identity_defs
import Submission.Work.FTS.EllipticEst.H2W.WeakAux.I1ZibpOpenAbs
import Submission.Work.FTS.EllipticEst.I1Ae.RIFLimits
import Submission.Work.FTS.EllipticEst.I1Ae.RIFMainB

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `I1Ae/AuxInt` — the integrability toolbox of the `I₁` cut-off expansion

The `ε → 0` and `n → ∞` limits of the cut-off identity `I1Ae.auxCutOff` both need *joint*
integrability (for the product measure `nuQ` on `(0,∞) × (0,π/2)`) of the several integrands
produced by the two integrations by parts:

* the `σ`-slots `f·g·w²σ` — supplied here by `H2W.WeakAux.prod_integrable_mul`, transported
  across the null-set difference between the open and the closed product measure
  (`integrable_w2_sig_mul`);
* the singular `σ₁`-slot `U·V·cos(2θ)·w²σ₁` — supplied by the pointwise AM–GM inequality
  `two_mul_sig1_mul_le` together with the two quadratic dominators (`integrable_w2sig1_cos`);
* bounded multipliers (`χ_n`, `z·χ_n'`) preserve integrability (`integrable_mul_of_bound`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.I1Ae

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)
local notation "Qd0" => Work.FTS.EllipticEst.H2W.WeakAux.Qd0
local notation "muP" => Work.FTS.EllipticEst.H2W.WeakAux.muP

open Work.FTS.EllipticEst.AeI1Fts (U V Hh AA BB sigE sig1 sig2 II nuQ Fp Fd)

/-! ## The two product measures -/

/-- `nuQ` (the product measure on the *open* quadrant) and `muP` (the product measure on the
*closed* one) agree: they differ only by the null sets `{0}` and `{0, π/2}`. -/
theorem nuQ_eq_muP : nuQ = muP := by
  show (MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)))
      = (MeasureTheory.volume.restrict (Set.Ici 0)).prod
          (MeasureTheory.volume.restrict (Set.Icc 0 (Real.pi / 2)))
  rw [MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)),
      MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0)
          (b := Real.pi / 2))]

/-! ## Bounded multipliers -/

/-- **A bounded multiplier preserves integrability.**  If `|c| ≤ M` a.e. and `F` is integrable
then `c·F` is integrable (with the `a.e.`-strong measurability of the product as the only
extra input). -/
theorem integrable_mul_of_bound {c F : ℝ × ℝ → ℝ} {M : ℝ}
    (hF : MeasureTheory.Integrable F nuQ) (hM : 0 ≤ M)
    (hc : ∀ᵐ p ∂nuQ, |c p| ≤ M)
    (haesm : MeasureTheory.AEStronglyMeasurable (fun p => c p * F p) nuQ) :
    MeasureTheory.Integrable (fun p => c p * F p) nuQ := by
  refine MeasureTheory.Integrable.mono' (hF.norm.const_mul M) haesm ?_
  filter_upwards [hc] with p hp
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hp (abs_nonneg _)

/-! ## The `σ`-slots: `L² · L² ⊆ L¹` for the weight `w²σ` -/

/-- **Joint integrability of `f·g·w²σ`.**  For two quadrant-continuous, `ℋ⁰`-honest data the
product `f·g·w²σ` is integrable for `nuQ`.  This is `H2W.WeakAux.prod_integrable_mul`
(integrability for the closed product measure `muP`) rewritten across the null sets. -/
theorem integrable_w2_sig_mul {α : ℝ} {f h : ℝ → ℝ → ℝ}
    (hfc : ContinuousOn (Function.uncurry f) Qd0)
    (hhc : ContinuousOn (Function.uncurry h) Qd0)
    (hf : Work.Spaces.HkMem α 0 f) (hh : Work.Spaces.HkMem α 0 h) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      f p.1 p.2 * h p.1 p.2 * (Work.Spaces.w p.1) ^ 2 * sigE p.2) nuQ := by
  have h := Work.FTS.EllipticEst.H2W.WeakAux.prod_integrable_mul hfc hhc hf hh
  rw [nuQ_eq_muP]
  exact h

/-! ## The singular `σ₁`-slot -/

/-- **Pointwise AM–GM with the two singular angular weights.**  For `sin(2θ) > 0` and reals
`a`, `b`:

`2·σ₁·(a·b) ≤ a²·σ₂ + b²·σ`,  where  `σ = sin(2θ)^{-η}`, `σ₁ = sin(2θ)^{-1-η}`,
`σ₂ = sin(2θ)^{-2-η}`.

(The two halves `sin(2θ)^{-(2+η)/2}` and `sin(2θ)^{-η/2}` of `σ₁` are exactly the square roots
of `σ₂` and of `σ`.) -/
theorem two_mul_sig1_mul_le {θ a b : ℝ} (hs : 0 < Real.sin (2 * θ)) :
    2 * (sig1 θ * (a * b)) ≤ a ^ 2 * sig2 θ + b ^ 2 * sigE θ := by
  have hp2 : (Real.sin (2 * θ) ^ (-(2 + Work.Spaces.eta) / 2)) ^ 2
      = Real.sin (2 * θ) ^ (-(2 + Work.Spaces.eta)) := by
    rw [pow_two, ← Real.rpow_add hs]
    congr 1
    ring
  have hq2 : (Real.sin (2 * θ) ^ (-(Work.Spaces.eta) / 2)) ^ 2
      = Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) := by
    rw [pow_two, ← Real.rpow_add hs]
    congr 1
    ring
  have hpq : Real.sin (2 * θ) ^ (-(2 + Work.Spaces.eta) / 2)
        * Real.sin (2 * θ) ^ (-(Work.Spaces.eta) / 2)
      = Real.sin (2 * θ) ^ (-(1 + Work.Spaces.eta)) := by
    rw [← Real.rpow_add hs]
    congr 1
    ring
  have hkey : 2 * (Real.sin (2 * θ) ^ (-(2 + Work.Spaces.eta) / 2)
        * Real.sin (2 * θ) ^ (-(Work.Spaces.eta) / 2) * (a * b))
      ≤ a ^ 2 * (Real.sin (2 * θ) ^ (-(2 + Work.Spaces.eta) / 2)) ^ 2
        + b ^ 2 * (Real.sin (2 * θ) ^ (-(Work.Spaces.eta) / 2)) ^ 2 := by
    nlinarith [sq_nonneg (a * Real.sin (2 * θ) ^ (-(2 + Work.Spaces.eta) / 2)
      - b * Real.sin (2 * θ) ^ (-(Work.Spaces.eta) / 2))]
  rw [sig1, sig2, sigE, ← hpq, ← hp2, ← hq2]
  linarith [hkey]

/-- `σ₁ ≥ 0`. -/
theorem sig1_nonneg_of_pos {θ : ℝ} (hs : 0 < Real.sin (2 * θ)) : 0 ≤ sig1 θ := by
  rw [sig1]
  exact Real.rpow_nonneg (le_of_lt hs) _

/-- **Joint integrability of the singular cross slot** `w²·σ₁·(U·V·cos(2θ))`.  The pointwise
AM–GM `two_mul_sig1_mul_le` dominates the integrand by the two quadratic ones,
`½·w²·(U²cos²(2θ)σ₂) + ½·w²·(V²σ)`, which are integrable by hypothesis. -/
theorem integrable_w2sig1_cos {u : ℝ → ℝ → ℝ}
    (hS : Work.FTS.EllipticEst.SmoothOpen u)
    (hN : MeasureTheory.Integrable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * ((U u p.1 p.2) ^ 2 * (Real.cos (2 * p.2)) ^ 2 * sig2 p.2)) nuQ)
    (hV : MeasureTheory.Integrable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * (V u p.1 p.2) ^ 2 * sigE p.2) nuQ) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * sig1 p.2 * (U u p.1 p.2 * V u p.1 p.2 * Real.cos (2 * p.2))) nuQ := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * sig1 p.2
      * (U u p.1 p.2 * V u p.1 p.2 * Real.cos (2 * p.2))) Work.FTS.EllipticEst.Q0 :=
    ((continuousOn_w_sq_fst.mul continuousOn_uncurry_sig1).mul
      (((continuousOn_uncurry_U hS).mul (continuousOn_uncurry_V hS)).mul
        continuousOn_uncurry_cos2))
  have hdom : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (1 / 2) * ((Work.Spaces.w p.1) ^ 2
          * ((U u p.1 p.2) ^ 2 * (Real.cos (2 * p.2)) ^ 2 * sig2 p.2))
        + (1 / 2) * ((Work.Spaces.w p.1) ^ 2 * (V u p.1 p.2) ^ 2 * sigE p.2)) nuQ :=
    (hN.const_mul (1 / 2)).add (hV.const_mul (1 / 2))
  refine MeasureTheory.Integrable.mono' hdom (aesm_nuQ_of_continuousOn hcont) ?_
  filter_upwards [ae_mem_nuQ] with p hp
  obtain ⟨hz, hθ⟩ := hp
  have hs : 0 < Real.sin (2 * p.2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  have hw2 : 0 ≤ (Work.Spaces.w p.1) ^ 2 := sq_nonneg _
  have hs1 : 0 ≤ sig1 p.2 := sig1_nonneg_of_pos hs
  have hkey := two_mul_sig1_mul_le (θ := p.2)
    (a := |U u p.1 p.2| * |Real.cos (2 * p.2)|) (b := |V u p.1 p.2|) hs
  have h2 : sig1 p.2 * ((|U u p.1 p.2| * |Real.cos (2 * p.2)|) * |V u p.1 p.2|)
      = sig1 p.2 * (|U u p.1 p.2| * |V u p.1 p.2| * |Real.cos (2 * p.2)|) := by ring
  have h3 : (|U u p.1 p.2| * |Real.cos (2 * p.2)|) ^ 2 * sig2 p.2
      = (U u p.1 p.2) ^ 2 * (Real.cos (2 * p.2)) ^ 2 * sig2 p.2 := by
    rw [mul_pow, sq_abs, sq_abs]
  have h4 : (|V u p.1 p.2|) ^ 2 * sigE p.2 = (V u p.1 p.2) ^ 2 * sigE p.2 := by
    rw [sq_abs]
  rw [h2, h3, h4] at hkey
  have h1 : sig1 p.2 * (|U u p.1 p.2| * |V u p.1 p.2| * |Real.cos (2 * p.2)|)
      ≤ ((U u p.1 p.2) ^ 2 * (Real.cos (2 * p.2)) ^ 2 * sig2 p.2
          + (V u p.1 p.2) ^ 2 * sigE p.2) / 2 := by
    linarith [hkey]
  rw [Real.norm_eq_abs]
  simp only [abs_mul, abs_of_nonneg hw2, abs_of_nonneg hs1]
  calc (Work.Spaces.w p.1) ^ 2 * sig1 p.2
        * (|U u p.1 p.2| * |V u p.1 p.2| * |Real.cos (2 * p.2)|)
      = (Work.Spaces.w p.1) ^ 2 * (sig1 p.2
          * (|U u p.1 p.2| * |V u p.1 p.2| * |Real.cos (2 * p.2)|)) := by ring
    _ ≤ (Work.Spaces.w p.1) ^ 2
          * (((U u p.1 p.2) ^ 2 * (Real.cos (2 * p.2)) ^ 2 * sig2 p.2
              + (V u p.1 p.2) ^ 2 * sigE p.2) / 2) :=
        mul_le_mul_of_nonneg_left h1 hw2
    _ = (1 / 2) * ((Work.Spaces.w p.1) ^ 2
          * ((U u p.1 p.2) ^ 2 * (Real.cos (2 * p.2)) ^ 2 * sig2 p.2))
        + (1 / 2) * ((Work.Spaces.w p.1) ^ 2 * (V u p.1 p.2) ^ 2 * sigE p.2) := by ring

end Work.FTS.EllipticEst.I1Ae
