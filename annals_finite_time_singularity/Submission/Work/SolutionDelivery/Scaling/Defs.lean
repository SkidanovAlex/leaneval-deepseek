/-
# `Work.SolutionDelivery.Scaling` — the Euler scaling that moves the blow-up time to `1`

The last input of the assembly is `EulerScalingToUnit` (`Work.StabilityFar.Defs`): from a solution
of the class of `theorem_1` blowing up at a time `T`, produce one whose blow-up time is exactly
`1`.  The scaling is the classical one,

  `u'(x,t) = λ u(λx, λ²t)`,  `p'(x,t) = λ² p(λx, λ²t)`,  `u₀'(x) = λ u₀(λx)`,  `λ = √T`,

which preserves the Euler equation (both terms of the equation scaling by `λ³`), the oddness, the
`C^{1,α}` class and the `α`-power decay of the vorticity, and which rescales the BKM integral by
`bkm u' t = bkm u (λ²t)`.

**A missing hypothesis in `Work.StabilityFar.EulerScalingToUnit`.**  As stated there, the input
quantifies over data satisfying only *solution-level* hypotheses: the Euler equation, oddness,
the strip `C^{1,α}` regularity and the divergence of `bkm`.  The conclusion, however, demands of
the produced datum `u₀'` the **`α`-power decay of its vorticity**, which those hypotheses do not
imply: they only bound `∇×u₀` on `ℝ³` (through the strip regularity at `t = 0`), while the decay
clause `‖∇×u₀' x‖ ≤ C/(‖x‖^α + 1)` requires `∇×u₀' → 0` at infinity and hence *is* a decay
condition.  Concretely, `T = -1`, `p = 0`, `u(x,t) = (t+1)^{-2}·u₀(x)` with `u₀` the solid
rotation `(x₂,-x₁,0)` satisfies every hypothesis of `EulerScalingToUnit` (the strips and the
oddness clause are vacuous for `T ≤ 0`, and `bkm u t = 2(1 - 1/(t+1)) → +∞` along `𝓝[<](-1)` (i.e. `t ↑ -1`)), while
`u₀` has the *constant* vorticity `-2e₃`; the scaling above then reproduces a constant (non
decaying) vorticity, so no rescaling of this solution can meet the decay clause, and producing
*any* datum/solution pair with the claimed properties is exactly the main theorem.

The delivery therefore proves the scaling at the level at which the assembly uses it — with the
datum hypotheses (`Work.LWP.EulerData`, i.e. divergence-freeness, oddness, `C^{1,α}` regularity
and the `α`-power decay of the vorticity) available as hypotheses, which in the assembly are the
`AssemblyInputs` datum fields:

* `Work.SolutionDelivery.EulerScalingToUnitData` (this file) — the corrected statement;
* `Work.SolutionDelivery.eulerScalingToUnitData_holds` (`Main.lean`) — its proof.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.SolutionDelivery.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.SolutionDelivery

/-- **The rescaling of a velocity field**: `x ↦ λ • u (λ • x) (λ² t)`. -/
def rescale (lam : ℝ) (u : R3 → ℝ → R3) : R3 → ℝ → R3 := fun x t => lam • u (lam • x) (lam ^ 2 * t)

/-- **The rescaling of a datum**: `x ↦ λ • u₀ (λ • x)`. -/
def rescaleDatum (lam : ℝ) (u₀ : R3 → R3) : R3 → R3 := fun x => lam • u₀ (lam • x)

/-- **The rescaling of a pressure**: `λ² p (λx) (λ²t)`. -/
def rescalePressure (lam : ℝ) (p : R3 → ℝ → ℝ) : R3 → ℝ → ℝ :=
  fun x t => lam ^ 2 * p (lam • x) (lam ^ 2 * t)

/-- **The scaling parameter carrying `[0,T)` to `[0,1)`**: `λ = √T`. -/
def rescaleTime (T : ℝ) : ℝ := Real.sqrt T

theorem rescaleTime_sq {T : ℝ} (hT : 0 < T) : rescaleTime T ^ 2 = T :=
  Real.sq_sqrt hT.le

theorem rescaleTime_pos {T : ℝ} (hT : 0 < T) : 0 < rescaleTime T := Real.sqrt_pos.mpr hT

theorem rescaleTime_ne_zero {T : ℝ} (hT : 0 < T) : rescaleTime T ≠ 0 :=
  ne_of_gt (rescaleTime_pos hT)

/-- **The corrected scaling input.**  The same conclusion as `Work.StabilityFar.EulerScalingToUnit`
— a datum and a solution whose blow-up time is `1` — from a solution of the class of `theorem_1`
whose *datum* is Lichtenstein–Gunther admissible (`Work.LWP.EulerData α u₀`: divergence-free,
odd, `C^{1,α}`, with the `α`-power vorticity decay), together with `T > 0`.

In the assembly all of these are available (`AssemblyInputs.div_u₀`, `.odd_u₀`, `.cdh_u₀`,
`.vortDecay_u₀`), so this is the form in which the `T* ≠ 1` step is proved. -/
def EulerScalingToUnitData : Prop :=
  ∀ (α : NNReal) (u₀ : R3 → R3) (T : ℝ) (p : R3 → ℝ → ℝ) (u : R3 → ℝ → R3),
    Work.LWP.EulerData α u₀ → 0 < T →
    IsLocalEulerEquationSolution p u₀ T u →
    (∀ t ∈ Set.Ico 0 T, IsOdd (u · t)) →
    (∀ S ∈ Set.Ioo 0 T, IsContDiffHolderOn ℝ α u.uncurry (Set.univ ×ˢ Set.Icc 0 S)) →
    Filter.Tendsto (Work.LWP.bkm u) (𝓝[<] T) Filter.atTop →
    ∃ u₀' : R3 → R3, ∃ p' : R3 → ℝ → ℝ, ∃ u' : R3 → ℝ → R3,
      div u₀' = 0 ∧ IsOdd u₀' ∧ IsContDiffHolder ℝ α u₀' ∧
      (∃ C : ℝ, 0 < C ∧ ∀ x : R3, ‖vorticity u₀' x‖ ≤ C / (‖x‖ ^ (α : ℝ) + 1)) ∧
      (∀ t ∈ Set.Ico 0 1, IsOdd (u' · t)) ∧
      IsLocalEulerEquationSolution p' u₀' 1 u' ∧
      (∀ S ∈ Set.Ioo 0 1, IsContDiffHolderOn ℝ α u'.uncurry (Set.univ ×ˢ Set.Icc 0 S)) ∧
      Filter.Tendsto (Work.LWP.bkm u') (𝓝[<] 1) Filter.atTop

end Work.SolutionDelivery
