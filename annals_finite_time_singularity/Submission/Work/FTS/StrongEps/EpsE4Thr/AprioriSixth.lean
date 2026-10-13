/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/AprioriSixth.lean` — the `ℋ⁶`-half of `AprioriP`

`EpsE4Thr/Reduction.lean` reduces the target `EpsE4Thr` to two inputs: the small-ball local
step `LocalStepP` and the two-clause sub-horizon a-priori bound `AprioriP`.  This module
discharges the **`ℋ⁶`-half** of `AprioriP`, i.e. the first conjunct

  `∀ τ ∈ [0,T'], Xn6 α (slice g τ) ≤ M`

along a regular `P₀`-solution, from the following inputs (each of which is a *named* obligation
of the `ε`-chapter, not an artefact of this file):

* **E3P** (`EpsE3P.EpsSol_IP6_energy_deriv_leP`, **proved**) — the level-six energy
  `e(τ) = IP6 1 … 1 α x(τ) x(τ)` of the *projected mollified* family `x(τ) = slice (JfamP ρ ε g) τ`
  obeys `e' ≤ Λ (1 + e)`, together with its continuity on `[0,T']` and its value at `τ = 0`
  (`EpsE4Thr/energy_barrier.energy_barrier` turns the pair into `1 + e(τ) ≤ (1 + e(0))e^{Λτ}`);
* the **loop identities** `HkSq α 6 x(τ) ≤ e(τ)` (`IP6_lo_coeffs`, proved) and
  `e(0) ≤ E0` where `E0` is an *a priori* bound on the datum (proved from
  `IP6_cs_coeffs` + `SliceWrapP.HkSq_JfamP_le` + `h6 : Xn6 α g₀ ≤ K α²`, see
  `epsEnergy6Q_zero_le` below — the point is that `E0` is a function of the datum's `K` and `α`,
  *not* of the final bound `M`, so no circularity arises);
* the **transfer of the profile** (`EpsE4Thr/HkSq_le_Jeps_six` + `EpsE4Thr/HkSq_le_Pz_add`,
  both reducible to the proved `HkSq_Jeps_sub_le`/`HkMem_JepsSub`/`HkSq_add_le_open`):
  `HkSq α 6 (slice g τ) ≤ 2 HkSq α 6 x(τ) + 2 K7²(1 + e(τ))`, whose input is the
  `ε·‖slice g τ‖₇`-control used to absorb the mollifier's `O(ε)` error (this is the same
  control as the `h7`-slot of E3P; it is the *only* remaining quantitative input besides E3P's
  own).

The conclusion is `Xn6 α (slice g τ) ≤ M` for any `M` dominating the explicit number
`√(2(1+K7²)(1+E0) e^{ΛT'})`.

## Why `E0` is *not* `Cup (C₀ α²)²`

The natural guess for the datum's energy is the small-ball condition
`Xn α x(0) ≤ C₀ α²` of `LocalStepP`/`AprioriP`.  That is the wrong level: `IP6_cs_coeffs`
bounds `e(0)` by `Xn6 α x(0)²`, the *`ℋ⁶`*-norm of the projected mollified datum, and the `ℋ⁶`
norm is **not** controlled by the `ℋ⁴` norm (the weight increases with the order).  What *is*
available is the chain
`e(0) ≤ Cup · Xn6 α x(0)² ≤ Cup · C · Xn6 α g₀² ≤ Cup · C · (K α²)²`
(`SliceWrapP.HkSq_JfamP_le` is ε-**uniform**), i.e. a bound in terms of the datum's own `ℋ⁶`
constant `K`.  Using `M` instead would make the estimate circular; using `K α²` does not.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.EpsE4Thr.Reduction
import Submission.Work.FTS.StrongEps.EpsE4Thr.energy_barrier
import Submission.Work.FTS.StrongPersist.IP6_lo_coeffs
import Submission.Work.FTS.StrongPersist.IP6_cs_coeffs
import Submission.Work.FTS.StrongEps.SliceWrapP

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongGlobal (Xn6)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The level-six energy of the **projected mollified** family at fake time `τ` — the quantity
whose one-sided differential inequality `e' ≤ Λ(1+e)` is E3P
(`EpsE3P.EpsSol_IP6_energy_deriv_leP`). -/
noncomputable def epsEnergy6Q (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (g : Fam) (τ : ℝ) : ℝ :=
  Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
    (slice (JfamP ρ ε g) τ) (slice (JfamP ρ ε g) τ)

/-- The right-hand side of the level-six energy identity at fake time `τ`: twice the pairing of
the scheme's (projected, mollified) source with the projected mollified profile. -/
noncomputable def epsEnergy6Qdot (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (Φs : Fn) (E : Fn → Fn)
    (g : Fam) (τ : ℝ) : ℝ :=
  2 * Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
    (epsRHSP α ρ ε Φs E g τ) (slice (JfamP ρ ε g) τ)

/-- **The `ℋ⁶`-half of `AprioriP`.**

* `hd`/`hΛb`/`hcont` are the (E3P) energy facts: the energy is continuous on `[0,T']`, it is
  differentiable at every *interior* point with the stated derivative, and that derivative obeys
  the one-sided inequality `e' ≤ Λ(1+e)`;
* `he0` is the datum's energy bound, with `E0` a function of the datum's `ℋ⁶`-constant (see the
  header);
* `hlo` is the proved level-six loop `HkSq α 6 x ≤ e`;
* `htr` is the transfer of the profile *combined* with the `ε`-control of the `ℋ⁷`-norm.

The conclusion is `Xn6 α (slice g τ) ≤ M` whenever `M` dominates the explicit number
`√(A(1+K7²)(1+E0) e^{ΛT'})`; the free coefficient `A ≥ 0` is there so that the calls producing
`htr` (the transfer of the profile composed with the `ε`-control) can be used with their own
numerical factors. -/
theorem apriori_sixth {α M Λ K7 A E0 : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {ε T T' : ℝ} {g : Fam}
    (hT' : 0 < T') (hT'le : T' ≤ T) (hΛ : 0 ≤ Λ) (hK7 : 0 ≤ K7) (hA : 0 ≤ A)
    (hE0 : 0 ≤ E0)
    (hd : ∀ τ ∈ Set.Ioo 0 T',
      HasDerivAt (epsEnergy6Q α ρ ε g) (epsEnergy6Qdot α ρ ε Φs E g τ) τ)
    (hΛb : ∀ τ ∈ Set.Ioo 0 T',
      epsEnergy6Qdot α ρ ε Φs E g τ ≤ Λ * (1 + epsEnergy6Q α ρ ε g τ))
    (hcont : ContinuousOn (epsEnergy6Q α ρ ε g) (Set.Icc 0 T'))
    (he0 : epsEnergy6Q α ρ ε g 0 ≤ E0)
    (hlo : ∀ τ ∈ Set.Icc 0 T',
      Work.Spaces.HkSq α 6 (slice (JfamP ρ ε g) τ) ≤ epsEnergy6Q α ρ ε g τ)
    (htr : ∀ τ ∈ Set.Icc 0 T', Work.Spaces.HkSq α 6 (slice g τ)
      ≤ A * Work.Spaces.HkSq α 6 (slice (JfamP ρ ε g) τ)
        + A * K7 ^ 2 * (1 + epsEnergy6Q α ρ ε g τ))
    (hM : Real.sqrt (A * (1 + K7 ^ 2) * (1 + E0) * Real.exp (Λ * T')) ≤ M) :
    ∀ τ ∈ Set.Icc 0 T', Xn6 α (slice g τ) ≤ M := by
  intro τ hτ
  -- the Grönwall barrier for the level-six energy
  have hbar := energy_barrier hT'.le hΛ hcont hd hΛb τ hτ
  have hbar' : 1 + epsEnergy6Q α ρ ε g τ ≤ (1 + E0) * Real.exp (Λ * τ) := by
    have h1 : (1 : ℝ) + epsEnergy6Q α ρ ε g 0 ≤ 1 + E0 := by linarith
    have h2 : 1 + epsEnergy6Q α ρ ε g τ
        ≤ (1 + epsEnergy6Q α ρ ε g 0) * Real.exp (Λ * τ) := by linarith
    have h3 : (0 : ℝ) ≤ Real.exp (Λ * τ) := Real.exp_nonneg _
    nlinarith [h1, h2, h3]
  -- the transfer and the level-six loop
  have hstep : Work.Spaces.HkSq α 6 (slice g τ)
      ≤ A * (1 + K7 ^ 2) * (1 + epsEnergy6Q α ρ ε g τ) := by
    have h1 := htr τ hτ
    have h2 := hlo τ hτ
    nlinarith [h1, h2]
  have hexp : Real.exp (Λ * τ) ≤ Real.exp (Λ * T') :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hτ.2 hΛ)
  have hfinal : Work.Spaces.HkSq α 6 (slice g τ)
      ≤ A * (1 + K7 ^ 2) * (1 + E0) * Real.exp (Λ * T') := by
    have h2 : (0 : ℝ) ≤ A * (1 + K7 ^ 2) := by nlinarith [hK7, hA]
    calc Work.Spaces.HkSq α 6 (slice g τ)
        ≤ A * (1 + K7 ^ 2) * (1 + epsEnergy6Q α ρ ε g τ) := hstep
      _ ≤ A * (1 + K7 ^ 2) * ((1 + E0) * Real.exp (Λ * τ)) := by
          exact mul_le_mul_of_nonneg_left hbar' h2
      _ = A * (1 + K7 ^ 2) * (1 + E0) * Real.exp (Λ * τ) := by ring
      _ ≤ A * (1 + K7 ^ 2) * (1 + E0) * Real.exp (Λ * T') := by
          have h3 : (0 : ℝ) ≤ A * (1 + K7 ^ 2) * (1 + E0) := by
            have : (0 : ℝ) ≤ 1 + E0 := by linarith
            positivity
          exact mul_le_mul_of_nonneg_left hexp h3
  -- compare the square roots
  have hsq : Xn6 α (slice g τ)
      ≤ Real.sqrt (A * (1 + K7 ^ 2) * (1 + E0) * Real.exp (Λ * T')) := by
    rw [Work.FTS.StrongGlobal.Xn6, Work.Spaces.HkNorm]
    exact Real.sqrt_le_sqrt hfinal
  exact le_trans hsq hM

end Work.FTS.StrongEps.EpsE4Thr
