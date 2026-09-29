import Mathlib
import Submission.CDTPlan.Interfaces
import Submission.Work.Holonomy3.defs

/-!
# The cleared pullback of the auxiliary series (definitions)

This module fixes the vocabulary of the analytic step of the fine holonomy bound: the pullback of
the auxiliary series `F = auxSeries f Q` by a `d`-tuple of conformal maps `ψ_1, …, ψ_d`, cleared of
the poles of the meromorphic pullbacks.

The pullback of a single species is meromorphic: `f_i(ψ_s(z)) = N_{i,s}(z)/P_{i,s}(ψ_s(z))` near
`0`, with `P_{i,s}(0) ≠ 0`.  Multiplying by the fixed polynomial `Rn_s := ∏_i P_{i,s}` (polynomial in
the *source* variable of the species, i.e. in `ψ_s(z)`) clears all these poles at once:

  `Rn_s(ψ_s z) · f_i(ψ_s z) = N_{i,s}(z) · ∏_{i' ≠ i} P_{i',s}(ψ_s z)`,

which is holomorphic.  Consequently the *cleared* composite

  `clearedFun Q ψ N P z = ∑_i Q_i(ψ(z)) ∏_s N_{i_s,s}(z_s)·∏_{i' ≠ i_s} P_{i',s}(ψ_s(z_s))`

is holomorphic on the polydisc of radius `ρ` (where all the `ψ_s` and `N_{i,s}` are analytic), and
its Taylor coefficients are the coefficients of the explicit multivariable series

  `uSeries Φ Rn * diagComp Φ (auxSeriesC f Q)`,

with `uSeries Φ Rn` the Taylor series of `z ↦ ∏_s Rn_s(ψ_s(z_s))`.  The lemma identifying the two
(`Work.Holonomy3.taylor_cleared_comp`) is the analytic heart of STEP 3.
-/

namespace Work.Holonomy3

open Submission.CDTPlan
open Filter Topology
open scoped BigOperators

noncomputable section

/-- The univariate series `f(x_s)` viewed as a power series in the `d` variables, over `ℂ`
(the `ℂ`-analogue of `Submission.CDTPlan.embedVar`). -/
def embedVarC {d : ℕ} (s : Fin d) (f : PowerSeries ℂ) : MvPowerSeries (Fin d) ℂ :=
  fun n => if n = Finsupp.single s (n s) then PowerSeries.coeff (n s) f else 0

/-- The auxiliary series `∑_i Q_i(x)·∏_s f_{i_s}(x_s)`, over `ℂ`. -/
def auxSeriesC {m d : ℕ} (f : Fin m → PowerSeries ℂ)
    (Q : (Fin d → Fin m) → MvPolynomial (Fin d) ℂ) : MvPowerSeries (Fin d) ℂ :=
  ∑ i, (Q i : MvPowerSeries (Fin d) ℂ) * ∏ s, embedVarC s (f (i s))

/-- The pullback data of a species `f` under a map `ψ`, with the holomorphy radius of the
numerator made explicit: a polynomial `P` with `P(0) ≠ 0`, a function `N` analytic on the ball of
radius `ρ`, and the identity `f(ψ z) = N z / P z` near `0`.  (This is
`Submission.CDTPlan.PullbackMero` with the ball of analyticity of `N` widened from radius `1` to
`ρ`; the widening is what the scaling `φ ↦ φ(r·)` produces.) -/
def PullbackData (f : PowerSeries ℚ) (ψ : ℂ → ℂ) (ρ : ℝ) (N : ℂ → ℂ) (P : Polynomial ℂ) : Prop :=
  P.eval 0 ≠ 0 ∧ AnalyticOnNhd ℂ N (Metric.ball 0 ρ) ∧
    ∀ᶠ z in 𝓝 (0 : ℂ),
      HasSum (fun n : ℕ => ((PowerSeries.coeff n f : ℚ) : ℂ) * ψ z ^ n) (N z / P.eval z)

/-- **The pole-clearing polynomial of the `s`-th variable.**  Its constant term is
`∏_i P i s (0) ≠ 0`. -/
def uPoly {d m : ℕ} (P : Fin m → Fin d → Polynomial ℂ) : MvPowerSeries (Fin d) ℂ :=
  ∏ s, embedVarC s (∏ i, P i s)

/-- The **cleared composite function** of STEP 3: the pullback of the auxiliary function, with the
poles of the meromorphic pullbacks cleared by the polynomials `∏_{i' ≠ i_s} P_{i',s}`.  Since
`N_{i,s}(z)/P_{i,s}(z)` is the meromorphic pullback (`Submission.CDTPlan.PullbackMero`), the product
`f_i(ψ_s z)·P_{i,s}(z) = N_{i,s}(z)` is holomorphic, so `clearedFun` is holomorphic on the polydisc
of radius `ρ`. -/
def clearedFun {d m : ℕ} (Q : (Fin d → Fin m) → MvPolynomial (Fin d) ℂ)
    (ψ : Fin d → ℂ → ℂ) (N : Fin m → Fin d → ℂ → ℂ) (P : Fin m → Fin d → Polynomial ℂ)
    (z : Fin d → ℂ) : ℂ :=
  ∑ i, (Q i).eval (fun s => ψ s (z s)) *
    ∏ s, (N (i s) s (z s) * ∏ i' ∈ Finset.univ.erase (i s), (P i' s).eval (z s))

/-- **The claim of the analytic STEP 3**: the Taylor expansion of the cleared composite
`clearedFun Q ψ N P` is the composition series `uPoly P * diagComp Φ (auxSeriesC f Q)`. -/
def ClearedTaylorClaim {d m : ℕ} (f : Fin m → PowerSeries ℚ)
    (Q : (Fin d → Fin m) → MvPolynomial (Fin d) ℚ)
    (ψ : Fin d → ℂ → ℂ) (Φ : Fin d → PowerSeries ℂ) (ρ : ℝ)
    (N : Fin m → Fin d → ℂ → ℂ) (P : Fin m → Fin d → Polynomial ℂ) : Prop :=
  ∀ z : Fin d → ℂ, (∀ s, ‖z s‖ < ρ) →
    HasSum (fun n : Fin d →₀ ℕ =>
      (MvPowerSeries.coeff n
        (uPoly P *
          diagComp Φ (auxSeriesC (fun i => PowerSeries.map (algebraMap ℚ ℂ) (f i))
            (fun i => MvPolynomial.map (algebraMap ℚ ℂ) (Q i))))) *
        ∏ s, z s ^ (n s))
      (clearedFun (fun i => MvPolynomial.map (algebraMap ℚ ℂ) (Q i)) ψ N P z)

lemma embedVarC_apply {d : ℕ} {s : Fin d} {f : PowerSeries ℂ} {n : Fin d →₀ ℕ}
    (h : n = Finsupp.single s (n s)) : embedVarC s f n = PowerSeries.coeff (n s) f := by
  rw [embedVarC]; exact if_pos h

lemma embedVarC_apply_of_ne {d : ℕ} {s : Fin d} {f : PowerSeries ℂ} {n : Fin d →₀ ℕ}
    (h : ¬ (n = Finsupp.single s (n s))) : embedVarC s f n = 0 := by
  rw [embedVarC]; exact if_neg h

/-- The constant coefficient of the lift of a univariate series to the `s`-th variable. -/
lemma embedVarC_coeff_zero {d : ℕ} (s : Fin d) (f : PowerSeries ℂ) :
    (embedVarC s f) 0 = PowerSeries.coeff 0 f := by
  rw [embedVarC]
  simp

end

end Work.Holonomy3
