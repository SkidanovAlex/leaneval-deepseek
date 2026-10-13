/-
# `Work.StabilityFar` — the STABILITY LAYER, parts 3+4 (`St4`/`St5`) and the `fts` assembly

This is the chapter of the formalisation of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021) 771--887,

that carries the **far-field part of the Stability layer** (the lead's `St4`), the
**Beale–Kato–Majda divergence** (`St5`), and the `theorem_1` assembly.  It builds on the
*delivered* prerequisite areas:

* `Submission.Work.LWP` — the Lichtenstein–Gunther `C^{1,α}` local theory, the continuation
  criterion, the flow machinery, and (crucially here) the unconditional far-field decay
  estimates `Work.LWP.farField_decay_uniform`, `Work.LWP.farField_decay_fderiv_uniform`;
* the coordinate/Biot–Savart dictionary `Work.Cyl`;
* the sibling Stability areas `St0`–`St3` (the dynamic-modulation bootstrap), whose interface is
  taken here as *named hypotheses* (see the `Prop`-valued `def`s and the `input` lemmas below).

## The mathematics of this chapter

The paper's own self-similar solution has `ω ~ |x|^{-α}` at infinity, whence `∂ₜω ~ |x|^{-2α}`
and `∂ₜu ~ |x|^{1-2α}` is **unbounded** for `α < 1/2`: the paper's solution does not satisfy the
*joint* `C^{1,α}` clause of `theorem_1`.  The remedy (EGM-style, and the reason this chapter
exists) is to **cut off the vorticity**: one treats `ω₀^L = χ(ρ/L)·ω₀`, a compactly supported
datum, and the resulting solution has — by the finite speed of propagation of the support of the
vorticity along the flow — its vorticity supported in a ball `B(0,R_T)` for every fixed `T`.
Then:

* `u = BS(ω)` and `∂ₜu = BS(∂ₜω)` are `O(|x|^{-2})` outside `B(0,2R_T)`, with derivatives
  `O(|x|^{-3})`; the support of `∂ₜω` is *the same ball*, because `ω(·,t)` vanishes identically
  on the (open) complement of the ball for all `t` in an interval, hence so does its `t`-derivative;
* consequently both blocks of `D u.uncurry` — the spatial derivative `D_xu` and the time
  derivative `∂ₜu` — are `α`-Hölder on the whole far region, with a constant depending only on
  `R_T`, `T` and the sup-norms of `ω`, `∂ₜω`.  **This is what makes the joint `C^{1,α}` clause
  true**, and it is the core calculation of `St4`;
* the far part of the solution is *not* in `H⁴` (it is only `L¹ ∩ L^∞` plus transport), and it
  couples into the `H⁴` bootstrap of `St0`–`St3` only through two terms, each of which is
  `O(1/z_edge(s))` with `z_edge(s) = μ̄R_T/λ̄(s) → ∞` — the *far-in-`z` control*, `St4(c)`.

`St5` is the Beale–Kato–Majda divergence: from `λ̄(t) = (T*-t)Λ(t)` with `Λ ≥ 1/2`, the paper's
`Linf_H2` embedding (`Work.Spaces.Linf_H2`) bounds `‖ω(·,t)‖_∞` below by
`c₀α/(4(T*-t))`, and `∫₀^{T*} dt/(T*-t) = ∞` gives the divergence of the BKM integral — the
last clause of `theorem_1`.

## What a consumer imports

```lean
import Submission.Work.StabilityFar        -- the whole chapter
```

The main results are

* `Work.StabilityFar.st4_farField_holder` — the far-field joint `C^{1,α}` bound (St4);
* `Work.StabilityFar.isContDiffHolderOn_glue` — core + far ⟹ the whole strip;
* `Work.StabilityFar.bkm_tendsto_atTop_of_linf_lower` — St5;
* `Work.StabilityFar.theorem1_shape_of_stability` — the `theorem_1` `(p,u)`-shape;
* `Work.StabilityFar.theorem_1_of_inputs` — the assembly at the level of the named inputs.
-/
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.LWP.Defs
import Submission.Work.LWP.FarField

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

theorem farRegion_mono {ρ ρ' : ℝ} (h : ρ ≤ ρ') : farRegion ρ' ⊆ farRegion ρ :=
  fun _ hx => lt_of_le_of_lt h hx

theorem coreRegion_mono {ρ ρ' : ℝ} (h : ρ ≤ ρ') : coreRegion ρ ⊆ coreRegion ρ' :=
  fun _ hx => le_trans hx h

/-- The far region and the core region of the *same* radius cover `ℝ³`; this is the cover used
to glue the far-field estimate to the core estimate. -/
theorem coreRegion_union_farRegion (ρ : ℝ) : coreRegion ρ ∪ farRegion ρ = univ := by
  ext x
  simp only [mem_union, mem_univ, mem_coreRegion, mem_farRegion]
  exact ⟨fun _ => trivial, fun _ => by
    rcases lt_or_ge ρ ‖x‖ with h | h
    · exact Or.inr h
    · exact Or.inl h⟩

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

theorem Icc_subset_window {T : ℝ} (hT : 0 ≤ T) : Set.Icc 0 T ⊆ window T :=
  fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩

theorem Ico_subset_window {T : ℝ} (hT : 0 ≤ T) : Set.Ico 0 T ⊆ window T :=
  fun t ht => ⟨by linarith [ht.1], by linarith [ht.2.le]⟩

theorem zero_mem_window {T : ℝ} (hT : 0 ≤ T) : (0 : ℝ) ∈ window T :=
  ⟨by norm_num, by linarith⟩

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

/-- **Lipschitz-in-`x` bound for the spatial derivative of `u` in the far region.**  This is the
one genuinely second-order estimate of `St4`: outside `B(0,ρ)`, `x ↦ D_xu(x,t)` is Lipschitz with
a constant `A` uniform in `t` on the window.  It follows from the second-derivative kernel
estimate (`Work.StabilityFar.farField_fderiv_sub_le` in `Decay/`), which is *proved* for the
Biot–Savart field of a bounded, supported vorticity. -/
def FarDerivLipschitz (A ρ T : ℝ) (u : R3 → ℝ → R3) : Prop :=
  ∀ t ∈ window T, ∀ x y : R3, ρ < ‖x‖ → ρ < ‖y‖ →
    ‖fderiv ℝ (u · t) x - fderiv ℝ (u · t) y‖ ≤ A * ‖x - y‖

/-! ## The two blocks of the derivative of the uncurried field

The challenge's `IsContDiffHolderOn ℝ α u.uncurry (univ ×ˢ Icc 0 T)` asks for `α`-Hölder
regularity of `fderiv ℝ u.uncurry`, a map into `(ℝ³ × ℝ) →L[ℝ] ℝ³`.  Its two blocks are the
spatial derivative `D_xu` and the time derivative `∂ₜu`, both of which decay in the far region.
`blockDeriv` names the operator, so that the far-field argument can be phrased in terms of two
*scalar-block* estimates. -/

/-- The operator `(v, s) ↦ D_xu(x,t) v + s • ∂ₜu(x,t)`: the derivative of `u.uncurry` at
`(x,t)`, as an element of `(ℝ³ × ℝ) →L[ℝ] ℝ³`. -/
noncomputable def blockDeriv (u : R3 → ℝ → R3) (p : R3 × ℝ) : (R3 × ℝ) →L[ℝ] R3 :=
  (fderiv ℝ (u · p.2) p.1).comp (ContinuousLinearMap.fst ℝ R3 ℝ)
    + (ContinuousLinearMap.snd ℝ R3 ℝ).smulRight (timeDeriv u p.1 p.2)

theorem blockDeriv_apply (u : R3 → ℝ → R3) (x : R3) (t : ℝ) (v : R3) (s : ℝ) :
    blockDeriv u (x, t) (v, s) = fderiv ℝ (u · t) x v + s • timeDeriv u x t := by
  simp [blockDeriv]

/-! ## `St5`: the BKM divergence -/

/-- **The lower bound on the vorticity sup-norm that drives the blow-up.**  This is what `St5`
consumes: `vortLInf u t ≥ c₀α/(4(T*-t))` for `t < T*`, obtained in the paper from
`λ̄(t) = (T*-t)Λ(t)`, `Λ ≥ 1/2` and the `L^∞ ⊂ H²` embedding `Work.Spaces.Linf_H2` applied to
the profile `F = F_* + g`. -/
def VortLinfLower (u : R3 → ℝ → R3) (T c : ℝ) : Prop :=
  ∀ t ∈ Set.Ico 0 T, c / (T - t) ≤ Work.LWP.vortLInf u t

/-- **Scaling invariance of the Euler equation transporting the blow-up to time `1`.**  If a
solution of the class of `theorem_1` on `[0,T)` blows up at `T`, then some rescaling
`u'(x,t) = λ u(λx, λ²t)` (which preserves the Euler equation, the oddness, the `C^{1,α}`
regularity and the `α`-decay of the vorticity) produces a datum and a solution whose blow-up time
is exactly `1`.  This is the "`T* ≠ 1`" step of the assembly; it is stated as an input because it
is a self-contained scaling computation about *different* objects (the scaled fields). -/
def EulerScalingToUnit : Prop :=
  ∀ (α : NNReal) (u₀ : R3 → R3) (T : ℝ) (p : R3 → ℝ → ℝ) (u : R3 → ℝ → R3),
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
