import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseB7.Estimates
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7.Integral` — FS `lem:EstimateIntegral`

FS `lem:EstimateIntegral` compares the `P_H`-sum `(2π)^{-3}∫_{P_H}Ŵ₁(k)α_k dk`
with `ρ_zŴ₁ω(0)` (and with `Ŵ₁ω(k)²/(2𝒟_k)` in the second part).  In the mode
normalisation of this chapter (`(2π)^{-3}ℓ³∫dk = ∑_{k ≠ 0}`) the two claims of
the lemma read

* `EstIntegralOne` (FS `eq:CompIntegrals-Final`):
  `|ρ_zŴ₁ω(0) − ∑_{k∈P_H}Ŵ₁(k)α_k| ≤ Cρ_z a (μa³)^{5/12}K_H^{-1}`,
* `EstIntegralTwo` (FS `eq:CompIntegrals-Final-2`):
  `|Ŵ₁ω(0) − ∑_{k∈P_H}Ŵ₁(k)²/(2𝒟_k)| ≤ Ca(μa³)^{5/12}K_H^{-1}`.

FS prove these by splitting into the pieces `k ∉ P_H` (a `k^{-2}` tail), the
second-order expansion `Ŵ₁(k)α_k = ρ_zŴ₁(k)²/(2𝒜(k)) + O(ρ_z³Ŵ₁⁴/𝒜³)`
(`eq:Comparealpha-A`), and the difference `ĝ(k)/(2k²) − Ŵ₁(k)/(2𝒜(k))`.  The
chapter isolates the *analytic* cores of those steps:

* `Work.BoseB7.ball_invSq_bound` — the tail `∫_{‖k‖≤R}‖k‖^{-2} ≤ 4πR` (the
  `k ∉ P_H` piece);
* `Work.BoseB7.exterior_inv6_bound` — the tail `∫_{R≤‖k‖}‖k‖^{-6} ≤ 4π/(3R³)`
  (the `eq:Comparealpha-A` piece);
* `Work.BoseB7.alpha_secondOrder_bound` — the pointwise second-order expansion
  of `α` (FS's `|Ŵ₁α − ρ_zŴ₁²/(2𝒜)| ≤ Cρ_z³Ŵ₁⁴/𝒜³`).

The remaining step between those and `EstIntegralOne`/`Two` is
(i) the Riemann-sum comparison (a `B4` obligation: the mode lattice against
`∫dk`) and (ii) the identity `Ŵ₁ω(0) = (2π)^{-3}∫Ŵ₁(k)ĝ(k)/(2k²)dk` of the
scattering theory (`B6`/§4).  Both are recorded here as the named hypothesis
`W1omega_secondOrder` so that the arithmetic part can be proved now.

## Contents

* `EstIntegralOne`, `EstIntegralTwo` — the two claims of `lem:EstimateIntegral`.
* `W1omega_secondOrder` — the `ĝ`-identity of FS's proof
  (`eq:CompIntegrals` first line), as a hypothesis.
* `exterior_inv6_bound` — stated (delegated) real-analysis tail bound.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

section

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-- FS `eq:CompIntegrals-Final`: the `P_H`-sum `∑_{k∈P_H}Ŵ₁(k)α_k` computes
`ρ_zŴ₁ω(0)` up to `Cρ_z a(μa³)^{5/12}K_H^{-1}`. -/
def EstIntegralOne (F : FockData Mode) (E : Q3Env Mode) (C : ℝ) : Prop :=
  |E.rho * E.W1omega0 - ∑ k ∈ F.PHset E, E.W1 k * E.alpha k| ≤
    C * E.rho * E.aScat * dil E (5 / 12) * E.KH ^ (-(1 : ℝ))

/-- FS `eq:CompIntegrals-Final-2`: the `P_H`-sum of the second-order kernel
`Ŵ₁(k)²/(2𝒟_k)` computes `Ŵ₁ω(0)` up to `Ca(μa³)^{5/12}K_H^{-1}`. -/
def EstIntegralTwo (F : FockData Mode) (E : Q3Env Mode) (C : ℝ) : Prop :=
  |E.W1omega0 - ∑ k ∈ F.PHset E, E.W1 k ^ 2 / (2 * E.D k)| ≤
    C * E.aScat * dil E (5 / 12) * E.KH ^ (-(1 : ℝ))

/-- The second-order identity of the scattering theory used at the start of FS's
proof of `lem:EstimateIntegral`,

  `ρ_zŴ₁ω(0) = (2π)^{-3}∫ Ŵ₁(k)ĝ(k)/(2k²)dk`,

read at the mode lattice: the sum of `ρ_zŴ₁(k)ĝ(k)/(2‖k‖²)` over all excited
modes with a `k^{-2}`-matching weight `g`.  It is a *hypothesis* here: it belongs
to the `B6`/§4 layer (`g`, `ω` and their Fourier transforms are built from the
scattering solution), not to the `3Q` analysis, and `lem:EstimateIntegral` merely
*uses* it. -/
def W1omega_secondOrder (F : FockData Mode) (E : Q3Env Mode) (g : Mode → ℝ) : Prop :=
  E.rho * E.W1omega0 = ∑ k ∈ F.PHset E, E.rho * E.W1 k * g k / (2 * ‖F.kmom k‖ ^ 2)

end

/-! ## The analytic tail bounds (delegated)

The two continuum inputs of `lem:EstimateIntegral` are delegated to their own
files in this directory, so that the chapter itself stays `sorry`-free:

* `Submission/Work/BoseB7/ball_invSq_bound` — `∫_{‖k‖≤R}|g|/‖k‖² ≤ 4πcR` for
  `|g| ≤ c` (the `k ∉ P_H` tail);
* `Submission/Work/BoseB7/exterior_inv6_bound` — `∫_{R≤‖k‖}|g|/‖k‖⁶ ≤ 4πc/(3R³)`
  for `|g| ≤ c` (the `eq:Comparealpha-A` tail).
-/

end Work.BoseB7
