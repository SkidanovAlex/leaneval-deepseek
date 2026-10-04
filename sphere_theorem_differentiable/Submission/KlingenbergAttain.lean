import Submission.GExpJointPt
import Submission.KlingenbergEven
import Submission.CutStep3
import Submission.RayConj

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The attainment of the injectivity radius: the limit step

Roadmap §127.2 plans the attainment of `m := injSup hmet` (a point `p` with `inj(p) = m`) as
follows: the set `W r := {p | ¬ InjAtLeast hmet p r}` is closed for `r ∈ (m, π/√K)`, and the
finite-intersection property on the decreasing compact sets `W (m + 1/k)` then gives a point
`p ∈ ⋂_k W (m + 1/k)`.

The *mechanical core* of the closedness of `W r` is the limit step: a sequence of witness pairs
(two distinct tangent vectors with the same exponential image, of norm `< r`) at base points
`p n → p₀`, whose chart coordinates converge, yields a failure of injectivity at `p₀` at every radius
`> r`.  This file proves that step **in the non-degenerate case** where the two limiting vectors are
distinct; the degenerate case (the two limiting vectors coincide at a *non-zero* value) needs the
"fit lemma" (a uniform local injectivity radius at a prescribed vector) which is documented in
Roadmap §130.

The proof of the non-degenerate case combines

* the brick `Submission.GExpJointPt.tendsto_GExp_frameVector` (joint continuity of `GExp` in the base
  point) — for the limiting *equality* of the two exponential images;
* `tendsto_norm_frameVector` — the convergence of the norms of the chart-level vectors;
* the uniform injectivity radius `Submission.UniformInj.exists_pos_injAllAtLeast` — to exclude the
  vanishing of both limits;
* `InjRadius`'s `frameVector_eq_zero_iff` — to convert coordinate information into tangent-vector
  information.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.GExpFlow
open Submission.ChartBounds
open Submission.ChartConnection
open Submission.InjRadius

namespace Submission.KlingenbergAttain

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **The norm of a frame vector converges with the data.** -/
theorem tendsto_norm_frameVector (hmet : IsMetricCompatible cov)
    {z₀ : M} {p₀ : M} (hp₀ : p₀ ∈ (chartAt H z₀).source)
    {pn : ℕ → M} (hpn : Tendsto pn atTop (𝓝 p₀)) {an : ℕ → E} {a : E}
    (ha : Tendsto an atTop (𝓝 a)) :
    Tendsto (fun n => ‖frameVector (I := I) z₀ (pn n) (an n)‖) atTop
      (𝓝 ‖frameVector (I := I) z₀ p₀ a‖) := by
  have hcont := Submission.ChartBounds.continuousAt_chartGram_prod (I := I) z₀ hp₀ a
  have hpair : Tendsto (fun n => (pn n, an n)) atTop (𝓝 (p₀, a)) :=
    (Prod.tendsto_iff (fun n => (pn n, an n)) (p₀, a)).mpr ⟨hpn, ha⟩
  have h1 : Tendsto (fun n => chartGram (I := I) z₀ (pn n) (an n) (an n)) atTop
      (𝓝 (chartGram (I := I) z₀ p₀ a a)) := hcont.tendsto.comp hpair
  have h2 := Real.continuous_sqrt.continuousAt.tendsto.comp h1
  simpa only [Function.comp_def, Submission.GExpFlow.norm_frameVector] using h2

/-- **The limit step of the closedness of `W r`, non-degenerate case.**  Let `p n → p₀` and let
`a n ≠ b n` be chart-`z₀` coordinate pairs of two tangent vectors with the same exponential image and
fibre norm `< r`.  If the coordinates converge, `a n → a`, `b n → b`, and the **limiting vectors are
distinct**, then the exponential map at `p₀` fails to be injective on the ball of every radius `> r`.
-/
theorem not_injAtLeast_of_tendsto_witness
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {z₀ : M} {p₀ : M} (hp₀ : p₀ ∈ (chartAt H z₀).source)
    {pn : ℕ → M} (hpn : Tendsto pn atTop (𝓝 p₀))
    {an bn : ℕ → E} {a b : E} (ha : Tendsto an atTop (𝓝 a)) (hb : Tendsto bn atTop (𝓝 b))
    {r : ℝ}
    (hdist : frameVector (I := I) z₀ p₀ a ≠ frameVector (I := I) z₀ p₀ b)
    (hnorm : ∀ᶠ n in atTop, ‖frameVector (I := I) z₀ (pn n) (an n)‖ < r ∧
      ‖frameVector (I := I) z₀ (pn n) (bn n)‖ < r)
    (hne : ∀ᶠ n in atTop, frameVector (I := I) z₀ (pn n) (an n)
      ≠ frameVector (I := I) z₀ (pn n) (bn n))
    (heq : ∀ᶠ n in atTop, GExp (cov := cov) hmet (pn n) (frameVector (I := I) z₀ (pn n) (an n))
      = GExp (cov := cov) hmet (pn n) (frameVector (I := I) z₀ (pn n) (bn n))) :
    ∀ r' : ℝ, r < r' → ¬ InjAtLeast hmet p₀ r' := by
  classical
  intro r' hr'
  -- the limiting equality of the images, via the brick
  have himg : GExp (cov := cov) hmet p₀ (frameVector (I := I) z₀ p₀ a)
      = GExp (cov := cov) hmet p₀ (frameVector (I := I) z₀ p₀ b) := by
    have hA := Submission.GExpJointPt.tendsto_GExp_frameVector (cov := cov) hmet htor hp₀ hpn ha
    have hB := Submission.GExpJointPt.tendsto_GExp_frameVector (cov := cov) hmet htor hp₀ hpn hb
    refine tendsto_nhds_unique hA ?_
    refine Filter.Tendsto.congr' ?_ hB
    filter_upwards [heq] with n hn
    exact hn.symm
  -- the limiting norms are `≤ r`
  have hnorma : ‖frameVector (I := I) z₀ p₀ a‖ ≤ r :=
    le_of_tendsto (tendsto_norm_frameVector (cov := cov) hmet hp₀ hpn ha)
      (hnorm.mono fun n h => le_of_lt h.1)
  have hnormb : ‖frameVector (I := I) z₀ p₀ b‖ ≤ r :=
    le_of_tendsto (tendsto_norm_frameVector (cov := cov) hmet hp₀ hpn hb)
      (hnorm.mono fun n h => le_of_lt h.2)
  -- distinct witnesses of norm `< r'` with the same image: the failure of injectivity
  exact fun hinj => hdist (hinj _ _ (lt_of_le_of_lt hnorma hr') (lt_of_le_of_lt hnormb hr') himg)

end Submission.KlingenbergAttain
