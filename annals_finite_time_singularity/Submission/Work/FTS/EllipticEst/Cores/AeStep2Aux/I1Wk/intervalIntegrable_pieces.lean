import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.SliceThetaIbpDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk

set_option autoImplicit false

/-- `θ ↦ sin(2θ)^p` is continuous on `[a,b]` as soon as `sin (2θ) ≠ 0` there (any real exponent
`p`; the base is then separated from `0`). -/
lemma continuousOn_sin_two_rpow {p a b : ℝ} (h : ∀ θ ∈ Set.Icc a b, Real.sin (2 * θ) ≠ 0) :
    ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) (Set.Icc a b) := by
  have hc : Continuous fun θ : ℝ => Real.sin (2 * θ) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  exact hc.continuousOn.rpow_const fun θ hθ => Or.inl (h θ hθ)

/-- `θ ↦ cos(2θ)` is continuous on `[a,b]`. -/
lemma continuousOn_cos_two {a b : ℝ} :
    ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)) (Set.Icc a b) :=
  (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn

/-- **Interval integrability of the five integrands of the θ-slice identity.**  All of them are
continuous on the compact interval `[a,b] ⊂ (0,π/2)`: `sig θ = sin(2θ)^{-η}` and
`Real.sin (2θ)^{-1}` are continuous there (the sine does not vanish), `ψ` is `C²` on `ℝ`, and
`v`, `deriv v`, `deriv (deriv v)` are continuous on a neighbourhood of `[a,b]` because
`hv : ContDiffOn ℝ 2 v (Ioo 0 (π/2))`.  The last two conjuncts follow from the first five by the
elementary `IntervalIntegrable` combinators (`sub`, `add`, `const_mul`) and the definitions of
`RHSfun` and `GderivFun` in `SliceThetaIbpDefs`. -/
theorem intervalIntegrable_pieces (v ψ : ℝ → ℝ)
    (hv : ContDiffOn ℝ 2 v (Set.Ioo 0 (Real.pi / 2)))
    (hψ : ContDiff ℝ 2 ψ) {a b : ℝ} (ha : 0 < a) (hb : b < Real.pi / 2) (hab : a ≤ b) :
    IntervalIntegrable (Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.Lfun v ψ) volume a b ∧
    IntervalIntegrable (Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.Afun v ψ) volume a b ∧
    IntervalIntegrable (Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.Bfun v ψ) volume a b ∧
    IntervalIntegrable (Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.Cfun v ψ) volume a b ∧
    IntervalIntegrable (Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.Dfun v ψ) volume a b ∧
    IntervalIntegrable (Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.RHSfun v ψ) volume a b ∧
    IntervalIntegrable (Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.GderivFun v ψ) volume a b := by
  -- the sine does not vanish on `[a,b]`
  have hsin : ∀ θ ∈ Set.Icc a b, Real.sin (2 * θ) ≠ 0 := by
    intro θ hθ
    have h1 : 0 < 2 * θ := by linarith [hθ.1]
    have h2 : 2 * θ < Real.pi := by linarith [hθ.2]
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2)
  -- an open interval `(c,d)` with `[a,b] ⊆ (c,d) ⊆ (0,π/2)`
  obtain ⟨c, d, hc0, hca, hbd, hdpi⟩ : ∃ c d : ℝ, 0 < c ∧ c < a ∧ b < d ∧ d < Real.pi / 2 :=
    ⟨a / 2, (b + Real.pi / 2) / 2, by linarith, by linarith, by linarith, by linarith⟩
  have hcd : Set.Ioo c d ⊆ Set.Ioo 0 (Real.pi / 2) :=
    fun x hx => ⟨lt_trans hc0 hx.1, lt_trans hx.2 hdpi⟩
  have hv' : ContDiffOn ℝ 2 v (Set.Ioo c d) := hv.mono hcd
  have hsub : Set.Icc a b ⊆ Set.Ioo c d :=
    fun x hx => ⟨lt_of_lt_of_le hca hx.1, lt_of_le_of_lt hx.2 hbd⟩
  -- continuity of `v` and its first two derivatives on `[a,b]`
  have hvc : ContinuousOn v (Set.Icc a b) := hv'.continuousOn.mono hsub
  have hdv : ContinuousOn (deriv v) (Set.Icc a b) :=
    (hv'.continuousOn_deriv_of_isOpen (n := 2) isOpen_Ioo (by norm_num)).mono hsub
  have hddv : ContinuousOn (deriv (deriv v)) (Set.Icc a b) :=
    ((hv'.deriv_of_isOpen (m := 1) (n := 2) isOpen_Ioo (by norm_num)).continuousOn_deriv_of_isOpen
      (n := 1) isOpen_Ioo (by norm_num)).mono hsub
  -- continuity of `ψ` and of its two derivatives
  have hψc : Continuous ψ := hψ.continuous
  have hψddc : Continuous (deriv (deriv ψ)) := by fun_prop
  -- continuity of the angular weights
  have hsig : ContinuousOn sig (Set.Icc a b) :=
    continuousOn_sin_two_rpow (p := -(Work.Spaces.eta)) hsin
  have hsininv : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(1 : ℝ))) (Set.Icc a b) :=
    continuousOn_sin_two_rpow (p := -(1 : ℝ)) hsin
  have hcos : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)) (Set.Icc a b) :=
    continuousOn_cos_two
  -- the five integrands
  have hL : ContinuousOn (Lfun v ψ) (Set.Icc a b) :=
    (hsig.mul hψc.continuousOn).mul (hvc.mul hddv)
  have hA : ContinuousOn (Afun v ψ) (Set.Icc a b) :=
    (hsig.mul hψc.continuousOn).mul (hvc.pow 2)
  have hB : ContinuousOn (Bfun v ψ) (Set.Icc a b) :=
    (hsig.mul hψc.continuousOn).mul (hdv.pow 2)
  have hCbase : ContinuousOn (fun θ : ℝ => deriv v θ - (1 + Work.Spaces.eta) * v θ
      * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(1 : ℝ))) (Set.Icc a b) :=
    hdv.sub (((continuous_const.continuousOn.mul hvc).mul hcos).mul hsininv)
  have hC : ContinuousOn (Cfun v ψ) (Set.Icc a b) :=
    (hsig.mul hψc.continuousOn).mul (hCbase.pow 2)
  have hD : ContinuousOn (Dfun v ψ) (Set.Icc a b) :=
    (hsig.mul hψddc.continuousOn).mul (hvc.pow 2)
  have hRHS : ContinuousOn (RHSfun v ψ) (Set.Icc a b) :=
    (((hA.const_mul (-2 * Work.Spaces.eta)).sub
        (hB.const_mul ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)))).sub
      (hC.const_mul (2 * Work.Spaces.eta / (1 + Work.Spaces.eta)))).add
      (hD.const_mul (1 / 2))
  have hG : ContinuousOn (GderivFun v ψ) (Set.Icc a b) := hL.sub hRHS
  exact ⟨ContinuousOn.intervalIntegrable_of_Icc hab hL,
    ContinuousOn.intervalIntegrable_of_Icc hab hA,
    ContinuousOn.intervalIntegrable_of_Icc hab hB,
    ContinuousOn.intervalIntegrable_of_Icc hab hC,
    ContinuousOn.intervalIntegrable_of_Icc hab hD,
    ContinuousOn.intervalIntegrable_of_Icc hab hRHS,
    ContinuousOn.intervalIntegrable_of_Icc hab hG⟩

end Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk
