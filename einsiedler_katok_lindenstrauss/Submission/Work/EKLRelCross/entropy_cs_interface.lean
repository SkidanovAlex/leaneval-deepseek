import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLComp.PlaqueToolkit

/-!
# `Work.EKLRelCross.entropy_cs_interface` — interface `Prop`s for EKL (9) / (U9)

The frozen component `P_Leafwise` of the EKL contract contains the clause (U9)

> if for a positive-measure set of `x` the leafwise measure `ν x` is invariant under
> right translation by **some** nonzero `u_ij(s)`, then `μ` is invariant under `U_ij`

(EKL §2.1 (9); the proof in `ROUTE_LEAD.md` §C5 is: EKL (9) = [the period argument, using the
`A`-covariance (U7)] followed by (U4) = Pisa 6.27).

This module records the `Prop`s into which the proof of `leafwise_entropy_cs` is decomposed, so
that the individual pieces can be stated against a common vocabulary:

* `PlaqueId μ U ν` — the `condexp` field of `IsLeafwise`, evaluated at the *base point* of an
  orbit plaque: the local product structure of `μ` along the `U`-plaques.  (P1)
* `PlaqueRatio μ U ν` — its corollary: the ratio of the `μ`-masses of the plaques of `x₀` and
  `t • x₀` is the ratio of the `ν x₀`-masses of the box and its right translate by `t`.  (P1')
* `Covariance μ U ν X'` — EKL (4) / Pisa 7.16, clause (U7) of `P_Leafwise`.  (P2)
* `AeHaar μ U ν` — a.e. right-`U`-invariance of the leafwise measures, i.e. the right hand side
  of (U4).  (P3)
* `IsUInvariant_of …` — the (U4) direction: a.e. Haar leafwise measures imply `U`-invariance
  of `μ` (Pisa 6.27).  (P4)
-/

open MeasureTheory Filter Topology
open Pointwise
open scoped ENNReal
open Work.EKLContract

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLRelCross

/-- **(P1) Local product structure at the base point of an orbit plaque.**  For `μ`-a.e. base
point `x₀`, every `ε > 0` and every Borel `A`, the `μ`-mass of `A` inside the orbit plaque
`P = (V ε ∩ U) • x₀` is, up to the constant `μ P / ν x₀ (V ε ∩ U)`, the `ν x₀`-mass of the
preimage box.  Cross-multiplied so that no division in `ℝ≥0∞` is needed. -/
def PlaqueId (μ : Measure X3) (U : Subgroup SL3) (ν : X3 → Measure SL3) : Prop :=
  ∀ᵐ x₀ ∂μ, ∀ ε : ℝ, 0 < ε → ∀ A : Set X3, MeasurableSet A →
    ν x₀ (V ε ∩ (U : Set SL3)) * μ (A ∩ Work.EKLComp.orbitPlaque U x₀ ε)
      = μ (Work.EKLComp.orbitPlaque U x₀ ε) *
        ν x₀ {u : SL3 | u ∈ V ε ∩ (U : Set SL3) ∧ u • x₀ ∈ A}

/-- **(P1′) Plaque-mass ratio.**  Corollary of `PlaqueId`: for `t ∈ U` (and `ε` large enough
that the box `V ε ∩ U` meets its right translate by `t` in a set of positive `ν x₀`-mass, which
is the only case in which the statement is not vacuous), the `μ`-mass of the plaque of `t • x₀`
is obtained from the mass of the plaque of `x₀` by the factor `ν x₀ (W t)/ν x₀ (W)`,
`W = V ε ∩ U`. -/
def PlaqueRatio (μ : Measure X3) (U : Subgroup SL3) (ν : X3 → Measure SL3) : Prop :=
  ∀ᵐ x₀ ∂μ, ∀ ε : ℝ, 0 < ε → ∀ t : SL3, t ∈ U →
      μ (Work.EKLComp.orbitPlaque U (t • x₀) ε) * ν x₀ (V ε ∩ (U : Set SL3))
    = μ (Work.EKLComp.orbitPlaque U x₀ ε) * ν x₀ ((V ε ∩ (U : Set SL3)) * {t})

/-- **(P2) The covariance clause (U7) of `P_Leafwise`** (EKL (4), Pisa 7.16): on a conull set
`X''`, the leafwise measure at `aDiag s • x` is proportional to the conjugate of the leafwise
measure at `x`. -/
def Covariance (μ : Measure X3) (U : Subgroup SL3) (ν : X3 → Measure SL3) (X' : Set X3) : Prop :=
  ∃ X'' ⊆ X', MeasurableSet X'' ∧ μ X''ᶜ = 0 ∧
    ∀ (s : Fin 3 → ℝ) (x : X3), x ∈ X'' → aDiag s • x ∈ X'' →
      ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
        ν (aDiag s • x) = c • (ν x).map (fun g => aDiag s * g * (aDiag s)⁻¹)

/-- **(P3) a.e. right-`U`-invariance of the leafwise measures** — the right hand side of
clause (U4) of `P_Leafwise`. -/
def AeHaar (μ : Measure X3) (U : Subgroup SL3) (ν : X3 → Measure SL3) : Prop :=
  ∀ᵐ x ∂μ, ∀ u ∈ U, (ν x).map (fun g => g * u) = ν x

/-- The set of points whose leafwise measure is invariant under right translation by
`u_ij(s)`: `Z_s` of the EKL (9) argument. -/
def Zinv (ν : X3 → Measure SL3) {i j : Fin 3} (hij : i ≠ j) (s : ℝ) : Set X3 :=
  {x : X3 | (ν x).map (fun g : SL3 => g * uij hij s) = ν x}

/-- The set of parameters `s` for which `ν x` is invariant under right translation by
`u_ij(s)`; a closed subgroup of `ℝ` when nonempty. -/
def Zstab (ν : X3 → Measure SL3) (x : X3) {i j : Fin 3} (hij : i ≠ j) : Set ℝ :=
  {s : ℝ | (ν x).map (fun g : SL3 => g * uij hij s) = ν x}

end Work.EKLRelCross
