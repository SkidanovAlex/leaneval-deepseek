import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.LWP.Main
import Submission.Work.Stability.mul_rpow_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.StabilityFar

/-! ## The ambient space and the two regions -/

/-- `ℝ³`, the ambient space (the challenge's `local notation ℝ³`; definitionally
`Work.LWP.R3`). -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The **far region** outside the sphere of radius `ρ`.  It is *open*, which is what makes
`fderivWithin` on it agree with `fderiv` (`UniqueDiffWithinAt` is automatic on open sets). -/
def farRegion (ρ : ℝ) : Set R3 := {x | ρ < ‖x‖}

/-- The **core region** inside the closed ball of radius `ρ` — where the self-similar profile
lives and where the solution is smooth by construction. -/
def coreRegion (ρ : ℝ) : Set R3 := {x | ‖x‖ ≤ ρ}

/-- The closed time strip over a spatial region. -/
def strip (s : Set R3) (T : ℝ) : Set (R3 × ℝ) := s ×ˢ Set.Icc 0 T

theorem mem_farRegion {ρ : ℝ} {x : R3} : x ∈ farRegion ρ ↔ ρ < ‖x‖ := Iff.rfl

theorem mem_coreRegion {ρ : ℝ} {x : R3} : x ∈ coreRegion ρ ↔ ‖x‖ ≤ ρ := Iff.rfl




/-! ## The hypotheses on the vorticity of the constructed solution

These are the *interface* of `St4`: what the sibling areas `St0`–`St3` (together with `LWP`'s
flow theory and the support-transport lemma `Work.LWP.Transport.support_transport`) deliver about
the vorticity `ω` of the cut-off solution, and what the far-field analysis consumes.

**The time window.**  `timeDeriv ω y t = deriv (ω y) t` is a *two-sided* derivative, so a
statement about `∂ₜω` at a point `t` needs information about `ω` on a two-sided neighbourhood of
`t`; at `t = 0` that is information about the solution at *negative* times.  This is harmless —
the constructed `C^{1,α}` solution extends backwards in time (the Euler equation is
time-reversible: `Work.LWP.local_existence` applied to the reversed equation), and the support of
its vorticity is transported by its flow for both positive and negative times — but it must be
said.  All the hypotheses below are therefore imposed on the two-sided window
`window T = [-1, T+1]`, while the conclusions are drawn on the physical strip `[0,T]`. -/

/-- The two-sided time window `[-1, T+1]` on which the far-field hypotheses are imposed. -/
def window (T : ℝ) : Set ℝ := Set.Icc (-1) (T + 1)

theorem mem_window {T t : ℝ} : t ∈ window T ↔ -1 ≤ t ∧ t ≤ T + 1 := Iff.rfl


theorem Ico_subset_window {T : ℝ} (hT : 0 ≤ T) : Set.Ico 0 T ⊆ window T :=
  fun t ht => ⟨by linarith [ht.1], by linarith [ht.2.le]⟩


/-- **Transport of the support**: every time slice of `ω` in the window is supported in the
closed ball of radius `R`.  For the cut-off solution this is
`Work.LWP.Transport.support_transport` together with the growth bound on the flow. -/
def SlicesSupported (ω : R3 → ℝ → R3) (R T : ℝ) : Prop :=
  ∀ t ∈ window T, ∀ y : R3, ω y t ≠ 0 → y ∈ Metric.closedBall 0 R

/-- A uniform-in-time `L^∞` bound on the vorticity of the solution (on the window). -/
def SlicesBounded (ω : R3 → ℝ → R3) (M T : ℝ) : Prop :=
  ∀ t ∈ window T, ∀ y : R3, ‖ω y t‖ ≤ M

/-- Pointwise measurability of the slices, used by the Biot–Savart estimates. -/
def SlicesMeasurable (ω : R3 → ℝ → R3) (T : ℝ) : Prop :=
  ∀ t ∈ window T, AEStronglyMeasurable (ω · t) volume

/-- **Time-Hölder regularity of `ω` on the support ball.**  This is the regularity of the
*constructed* solution in its core — delivered by `St0`–`St3` (the chain rule on the self-similar
ansatz, with the `H⁴` bound on the perturbation `g`) — and it is one of the two inputs of the
far-field `α`-Hölder estimate. -/
def TimeHolderOnBall (α : ℝ) (ω : R3 → ℝ → R3) (R T H : ℝ) : Prop :=
  ∀ z ∈ Metric.closedBall (0 : R3) R, ∀ t ∈ window T, ∀ τ ∈ window T,
    ‖ω z t - ω z τ‖ ≤ H * |t - τ| ^ α

/-- `u` is the Biot–Savart field of `ω` slice by slice: `u(·,t) = BS(ω(·,t))`.  For the
constructed solution this is the *definition* of `u` (the paper's Biot–Savart reconstruction,
`Work.LWP.BiotSavart`). -/
def IsBiotSavartSlice (u ω : R3 → ℝ → R3) (T : ℝ) : Prop :=
  ∀ t ∈ window T, ∀ x : R3, u x t = Work.LWP.biotSavart (fun y => ω y t) x

/-- **The Biot–Savart reconstruction commutes with `∂ₜ`**: `∂ₜu(·,t) = BS(∂ₜω(·,t))`.  This is
differentiation under the Biot–Savart integral in the Newtonian-potential form, legitimate
because `∂ₜω` is bounded and supported; it is the *transport identity* on the constructed
solution (`VorticityEquation u ω`) read through Biot–Savart.  It is proved in
`Work.StabilityFar.timeDeriv_biotSavart` from the domination of `∂ₜω`. -/
def IsTimeBiotSavartSlice (u ω : R3 → ℝ → R3) (T : ℝ) : Prop :=
  ∀ t ∈ window T, ∀ x : R3,
    timeDeriv u x t = Work.LWP.biotSavart (fun y => timeDeriv ω y t) x


/-! ## The two blocks of the derivative of the uncurried field

The challenge's `IsContDiffHolderOn ℝ α u.uncurry (univ ×ˢ Icc 0 T)` asks for `α`-Hölder
regularity of `fderiv ℝ u.uncurry`, a map into `(ℝ³ × ℝ) →L[ℝ] ℝ³`.  Its two blocks are the
spatial derivative `D_xu` and the time derivative `∂ₜu`, both of which decay in the far region.
`blockDeriv` names the operator, so that the far-field argument can be phrased in terms of two
*scalar-block* estimates. -/



/-! ## `St5`: the BKM divergence -/

/-- **The lower bound on the vorticity sup-norm that drives the blow-up.**  This is what `St5`
consumes: `vortLInf u t ≥ c₀α/(4(T*-t))` for `t < T*`, obtained in the paper from
`λ̄(t) = (T*-t)Λ(t)`, `Λ ≥ 1/2` and the `L^∞ ⊂ H²` embedding `Work.Spaces.Linf_H2` applied to
the profile `F = F_* + g`. -/
def VortLinfLower (u : R3 → ℝ → R3) (T c : ℝ) : Prop :=
  ∀ t ∈ Set.Ico 0 T, c / (T - t) ≤ Work.LWP.vortLInf u t


/-! ## `St4(c)`: the far-in-`z` control -/

/-- The edge of the core region in the self-similar variable `z = ρ^α/λ̄`: the physical support
ball of radius `R` maps to `z ≤ R^α/λ̄`, so the *edge* of the core in `z` is `R^α/λ̄`.  For the
construction `λ̄(t) = (T*-t)Λ(t)`, i.e. `s = -log λ̄`, this grows like `e^s`. -/
noncomputable def zEdge (c : ℝ) (lam : ℝ → ℝ) (s : ℝ) : ℝ := c / lam s

/-- **The far-in-`z` coupling data of `St4(c)`.**  The far part of the perturbation lives in
`z ≳ z_edge(s)`; it is not in `H⁴` and enters the `H⁴` bootstrap of `St0`–`St3` only through the
two functionals `L12far` (the value at `z = 0` of the `L₁₂`-projection of the far term) and
`phiFar` (the far part of the Biot–Savart potential evaluated in the core), each bounded by
`C/z_edge(s)`.  The two inequalities are the *analytic* content of the far-field transport
estimate; the conclusion — that they tend to `0` — is elementary. -/
structure FarInZCoupling (c : ℝ) (lam : ℝ → ℝ) where
  /-- the `L₁₂(·)(0)` coupling of the far term -/
  L12far : ℝ → ℝ
  /-- the core value of the far Biot–Savart potential -/
  phiFar : ℝ → ℝ
  A₁ : ℝ
  A₂ : ℝ
  hA₁ : 0 ≤ A₁
  hA₂ : 0 ≤ A₂
  hL12 : ∀ s : ℝ, |L12far s| ≤ A₁ / zEdge c lam s
  hPhi : ∀ s : ℝ, |phiFar s| ≤ A₂ / zEdge c lam s

end Work.StabilityFar
