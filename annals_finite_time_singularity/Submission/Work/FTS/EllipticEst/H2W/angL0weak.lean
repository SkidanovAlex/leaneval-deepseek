import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Elliptic.hardy_two
import Submission.Work.FTS.EllipticEst.H2W.weakSliceDerivBound
import Submission.Work.FTS.EllipticEst.H2W.weakSliceLimits
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.I_identity
import Submission.Work.FTS.EllipticEst.AngSecond.IP_cauchy_schwarz
import Submission.Work.FTS.EllipticEst.AngClean.step2_collection
import Submission.Work.FTS.EllipticEst.H2W.I4Open
import Submission.Work.FTS.EllipticEst.H2W.step3Open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

open MeasureTheory Set Filter
open scoped Real Topology

/-!
# `angL0weak`: the level-`0` angular elliptic estimate in the weak class

Target: `L2Sq (∂θθU · W) ≤ C · L2Sq (S · W)` for `W = w / sin(2θ)^{η/2}` and `(S,U)` in the
weak hypothesis class (equation on the open quadrant, Dirichlet values, decay in `z`, both
`OrthCond`s, smoothness on the open quadrant, and `HkMem α 0 S` only — no honesty hypothesis on
the left hand side).

See `NOTES_angL0weak.md` (this directory) for the analysis of the statement (it is *true*, and
the naive counterexample routes — homogeneous/self-similar data, the "mixture" data of
`NOTES_slice_honest_open.md`, the adiabatic two-sided `z`-profile — are all blocked by the
"self-regulation" recorded there), for the route (the paper's Step 2: test against `-∂θθU·ρ` and
control `I₁ … I₅`), for the review-driven correction that the analytic inputs must be stated as
*pairings* (not norms), and for the remaining gaps (weak-class Step 1, the weak-class `I₁`/`I₄`
pairing bounds, and the junk/totalisation layer).

## Contents of this file

* `pthIter_two_eq` — the pointwise identity behind the whole computation:
  `∂θθU = -(bslOp α U) - (α²z²)∂zzU - (α(5+α)z)∂zU + ∂θ(tanθ·U) - 6U` on the open quadrant.
  Every bound of Step 2 is a consequence of this identity together with estimates for the four
  displayed terms.
* `weakBarBound` — the weak-class pointwise bound on the slice profile `Ψ̄ = u / cos θ` which the
  `I₄` analysis consumes, obtained from `weakSliceDerivBound`.
-/

/-- **The pointwise identity of the whole Step 2 computation.**  On the open quadrant,

`∂θθU = -(bslOp α U) - (α²z²)·∂_zzU - (α(5+α)z)·∂_zU + ∂_θ(tanθ·U) - 6U`.

Indeed `bslOp α U = -(α²z²)∂zzU - (α(5+α)z)∂zU + Lzero U` and
`Lzero U = -∂θθU + ∂θ(tanθ·U) - 6U`. -/
theorem pthIter_two_eq (α : ℝ) (U : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter 2 U z θ
      = -(Work.Elliptic.bslOp α U z θ) - (α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 U z θ
        - (α * (5 + α) * z) * Work.Spaces.pz U z θ
        + Work.Spaces.pth (fun z θ => Real.tan θ * U z θ) z θ - 6 * U z θ := by
  simp only [Work.Elliptic.bslOp, Work.Elliptic.Lzero, Work.Spaces.pthIter_succ,
    Work.Spaces.pthIter_zero, Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero]
  ring

/-- **Weak-class bound on the slice profile `Ψ̄ = u / cos θ`.**  From `weakSliceDerivBound`,
`|u θ| ≤ (π/4)·sin(2θ)·√(A·B)` with `A = ∫ (u'')² sEta` and `B = ∫ sin(2θ)^η`, hence
`|u θ / cos θ| ≤ (π/2)·sin θ·√(A·B)` on the open interval.  This is one of the hypotheses
(`|Ψ̄|` bounded) consumed by the `I₄`-identity `AngSecond/I4_Gprim_deriv`; note that in the weak
class the *derivative* `Ψ̄'` is **not** bounded by this route (`|u'| ≤ √(A·B)` only), which is why
the weak-class `I₄` needs the additional endpoint/jump work recorded in the notes. -/
theorem weakBarBound (u : ℝ → ℝ)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)))
    (hcont : ContinuousOn u Work.Spaces.Iθ) (h0 : u 0 = 0) (h1 : u (Real.pi / 2) = 0)
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |u θ / Real.cos θ| ≤ (Real.pi / 2) * Real.sin θ *
        Real.sqrt ((∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ)
            * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta))) := by
  intro θ hθ
  obtain ⟨-, hbound⟩ := weakSliceDerivBound u hu hcont h0 h1 hint
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hst : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
  have hb := hbound θ hθ
  rw [hst] at hb
  rw [abs_div, abs_of_pos hcos]
  calc |u θ| / Real.cos θ
      ≤ (Real.pi / 4 * (2 * Real.sin θ * Real.cos θ) * Real.sqrt ((∫ θ in Work.Spaces.Iθ,
              (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
            * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta)))) / Real.cos θ :=
        div_le_div_of_nonneg_right hb hcos.le
    _ = (Real.pi / 2) * Real.sin θ * Real.sqrt ((∫ θ in Work.Spaces.Iθ,
            (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta))) := by
        rw [div_eq_iff hcos.ne']
        ring

/-- **The final algebraic collection of Step 2** (the paper's "summing up the estimates of
`I₁ … I₅`").  Inputs, all of them real numbers: the identity's expansion with the `I₁` bound
(constant `C₂`), the `I₄` bound (constant `C₁`), the Cauchy–Schwarz bound `|IP S Φ| ≤ A·X` and
the first-order bound `m ≤ C₀A` (`m` = the `Ψ`-norm) together with `α·b ≤ C₀A` (`b` = the
`z∂_zΨ`-norm).  Conclusion: `X ≤ K·A`, the level-`0` angular estimate. -/
theorem step2Collection {C₂ C₁ C₀ α A b m X : ℝ} (hC₂ : 0 < C₂) (hC₁ : 0 < C₁) (hC₀ : 0 < C₀)
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hA : 0 ≤ A) (hb : 0 ≤ b) (hm : 0 ≤ m) (hX : 0 ≤ X)
    (hid : X ^ 2 ≤ A * X + C₂ * α ^ 2 * (b ^ 2 + b * X) + α * (5 + α) * b * X
      + (m * X + C₁ * m ^ 2) + 6 * m * X)
    (hmA : m ≤ C₀ * A) (hbA : α * b ≤ C₀ * A) :
    X ≤ ((max (C₂ / 4 + 49 / 4) (C₂ + C₁) + 1) * (1 + C₀)) * ((1 + C₀) * A) := by
  have hid' : X ^ 2 ≤ C₂ * (α ^ 2 * (b ^ 2 + b * X)) + α * (5 + α) * b * X
      + (m * X + C₁ * m ^ 2) + 6 * m * X + A * X := by linarith [hid]
  have h := Work.FTS.EllipticEst.AngClean.step2_collection hC₂ hC₁ hC₀ hα hα4 hX hA hb hm
    hid' hmA
  have h1 : A + α * b ≤ (1 + C₀) * A := by linarith
  have h0 : 0 ≤ (max (C₂ / 4 + 49 / 4) (C₂ + C₁) + 1) * (1 + C₀) := by positivity
  calc X ≤ (max (C₂ / 4 + 49 / 4) (C₂ + C₁) + 1) * (1 + C₀) * (A + α * b) := h
    _ ≤ (max (C₂ / 4 + 49 / 4) (C₂ + C₁) + 1) * (1 + C₀) * ((1 + C₀) * A) :=
        mul_le_mul_of_nonneg_left h1 h0

theorem angL0weak : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (S U : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    (∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α U z θ = S z θ) →
    (∀ z, U z 0 = 0) → (∀ z, U z (Real.pi / 2) = 0) →
    (∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun z => U z θ) Filter.atTop (nhds 0)) →
    Work.Elliptic.OrthCond S → Work.Elliptic.OrthCond U →
    (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry U) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
    Work.Spaces.HkMem α 0 S →
    Work.Spaces.L2Sq (fun z θ => Work.Spaces.pthIter 2 U z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      ≤ C * Work.Spaces.L2Sq (fun z θ => S z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) := by sorry

end Work.FTS.EllipticEst.H2W
