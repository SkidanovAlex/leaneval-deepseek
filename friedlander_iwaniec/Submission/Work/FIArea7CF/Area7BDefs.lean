/-
# `Submission.Work.FIArea7CF.Area7BDefs` — the definitions of the amended area-7 assembly

This is the definition file of the corrected round-6 area 7 (`Work.FITop4.Area7_6b`,
`AREA7_ROUTE_LEAD.md`, `NOTES.md` §61–§62).  It contains

* `Area7Uni6B`: the paper's Proposition 17.3 (17.19) for the *uniform* cut `WUni6`, with the
  amended contract's hypotheses (`Pa.τ` pinned, axis-free polar box) **and** the range cap
  `X ≤ (log N)^{nuU}` of the frozen contract (which is *not* droppable on the §17 route: the `δτ`
  saving of the Rankin lemma is only polylogarithmic);
* `NumericCoreB`: the pure real-variable core of the amended assembly — `NumericCore` with the
  angular-mode slack `(2K+1) → (2K+L₀+2)` and the three extra summands produced by the §17 bridge
  (the `E = (β̃−β_L) − δτ` mass term, its cross term with `β_L`, and the `L₀`-slack of region II).

See `AREA7_ROUTE_LEAD.md` §2.2 A8 and `NOTES.md` §62.4.
-/
import Mathlib
import Submission.Work.FITop4.Areas6c
import Submission.Work.FIArea7CF.Area7Assembly6

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The paper's Proposition 17.3 (17.19) at the uniform cut, amended contract.**

For every exponent `η ∈ (0, 3/32)` there are `δ, c, x₀ > 0` such that for every admissible datum
with `Pa.τ = tauOf Pa.x Asave`, every coefficient `β` of
(4.13)+(5.13)+(5.7)+(5.9) whose polar box is axis-free, every `1 ≤ X < N^δ` with
`X ≤ (log N)^{nuU}`,

  `‖WUni6 Pa X β‖ ≤ c·(Pz⁻¹ + X⁻¹)·N²·log N`.

The only difference from `Work.FIArea7.Area7Uni6` is the two amended hypotheses plus the cap; the
proof is `AREA7_ROUTE_LEAD.md` §2.2 A8 (the §17 bridge `β = β_L + E`). -/
def Area7Uni6B : Prop :=
  ∀ η : ℝ, 0 < η → η < 3 / 32 →
  ∃ δ c x0 : ℝ, 0 < δ ∧ 0 < c ∧
  ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) → Pa.η = η →
    Pa.τ = Work.FITop4.tauOf Pa.x Work.FITop4.Asave →
  ∀ (X : ℕ) (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ),
    Work.FITop4.IsBetaCoeff6 Pa φ z0 β →
    (∀ z, Work.FITop4.InPolarBox Pa φ z → Work.FITop4.IsAxisFree Pa z) →
    1 ≤ X → (X : ℝ) < Pa.N ^ δ → (X : ℝ) ≤ (Real.log Pa.N) ^ Work.FITop4.nuU →
    ‖WUni6 Pa X β‖
      ≤ c * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N

/-- **The pure real-variable core of the amended assembly.**

`NumericCore` with the angular-mode slack `(2K+1) → (2K+L₀+2)` (with `L₀ ≤ 2K+2Lm+2`, `Lm` the
mode length of the §17 bridge) and with three extra summands:

* `log²(K+2)·Ev·(N log(X+2) + X²N^{δ₁})` — the region-I `E`-mass term (`charRegionLow_pair_sharp_le`
  applied to `E := (β̃−β_L) − δτ`);
* `log²(K+2)·X(1+log(UB+2))·c₁N^{1-δ₁}·√Ev·(5√N + N^{δ₁/2})` — the region-I cross term
  (`charRegionLow_split_le`);
* `(1+Clat)·1000(θN+√N+1)log³(N+2)·log²(K+2)·X(2Lm+2)N^{1-δ₁}` — the part of region II created by
  the mode slack (`regionHighSlack_le` with `2K+L₀+2` in place of `2K+1`).

The extra hypotheses are the contract's cap `X ≤ (log N)^{nuU}` (`nuU = 3012582943`), the
polylogarithmicity `Lm ≤ (log N)^{BL}` of the mode length, and the `L²`-mass
bound `Ev` of `E`, whose `δτ` summand is the Rankin bound `N(log N)^{-4·10⁹}` of `deltaTau_mass_le`
and whose truncation summand is the `deltaQ_mass_le` bound (with `Lm ≥ θ⁻¹X log⁶(N+2)`, i.e.
`θ⁻¹/Lm ≤ 1/(X log⁶(N+2))`).

SUGGESTED ROUTE (for `numeric_core_proof_B`).  Apply the proved `NumericCore` of
`Submission/Work/FIArea7CF/Area7Assembly6.lean` (`Work.FIArea7.numeric_core_proof`) with the *same*
`C_L, C_E, C_G, c₁, Clat, δ₁` but with `C_H` replaced by `2*C_H`: this bounds
`T1_old + T2_old(2C_H) + T3 + T4`, where `T2_old` is the same expression with `2K+1` in place of
`2K+L₀+2`.  Two elementary steps give the new first four terms:

* `T1_new ≤ T1_old`, because `2*(K:ℝ)+1 ≤ 2*(K:ℝ)+(L₀:ℝ)+2` and `u ↦ X√(u+1) + (u+1)^{3/2}` is
  monotone on `u ≥ 0`;
* `T2_new ≤ T2_old + C_H·Sx`, where `Sx` is the third extra summand, because
  `2*(K:ℝ)+(L₀:ℝ)+2 ≤ 2*(2*(K:ℝ)+1) + (2*Lm+2)` (the hypothesis `(L₀:ℝ) ≤ 2*(K:ℝ)+2*Lm+2`) and
  `X·log(UB+2) ≤ 2·X·log(UB+2)`.

Then `ncExtras_le c₁ CR Clat BL ...` bounds `S5 + S6 + Sx ≤ ce·X⁻¹N²log N`, and since
`T2_new ≤ T2_old + C_H·Sx ≤ T2_old + (C_H+CP+CX)(S5+S6+Sx)` one concludes with
`c := c0 + ce*(C_H+CP+CX)` and `N₀ := max N₀₀ Ne`. -/
def NumericCoreB : Prop :=
  ∀ (C_L C_H C_E C_G c₁ Clat CP CX CR BL : ℝ),
    0 < C_L → 0 < C_H → 0 < C_E → 0 < C_G → 0 < c₁ → 0 < Clat →
    0 < CP → 0 < CX → 0 < CR → 0 ≤ BL →
    ∀ δ₁ : ℝ, 0 < δ₁ → δ₁ < 3 / 32 →
    ∃ c N₀ : ℝ, 0 < c ∧
      ∀ {N X Lm : ℝ} {K L₀ : ℕ} {θ Pz UB E2v Ev : ℝ},
        N₀ ≤ N → 3 ≤ N → 1 ≤ X → 0 < θ → θ ≤ 1 → X ^ 8 ≤ N ^ δ₁ →
        X ≤ (Real.log N) ^ Work.FITop4.nuU →
        0 < Pz → 1 ≤ (K : ℝ) → X ^ 3 * (Real.log (N + 2)) ^ 20 ≤ (K : ℝ) →
        (K : ℝ) ≤ 2 * X ^ 3 * (Real.log (N + 2)) ^ 20 →
        (L₀ : ℝ) ≤ 2 * (K : ℝ) + 2 * Lm + 2 → 1 ≤ Lm → Lm ≤ (Real.log N) ^ BL →
        0 < UB → UB ≤ 4 * θ * N + 2 →
        0 ≤ E2v → E2v ≤ 1000 * (θ * N + Real.sqrt N + 1) * (Real.log (N + 2)) ^ 3 →
        0 ≤ Ev → Ev ≤ 2 * N * (Real.log N) ^ (-(4 * 10 ^ 9 : ℝ))
            + 2 * CR * N * (Real.log (Lm + 2)) ^ 2 / (X ^ 2 * (Real.log (N + 2)) ^ 5) →
          C_L * c₁ ^ 2 * N ^ (2 - 2 * δ₁) * (Real.log ((K : ℝ) + 2)) ^ 2
              * (X * Real.sqrt (N ^ δ₁ / (2 * (K : ℝ) + (L₀ : ℝ) + 2) + 1)
                  + (N ^ δ₁ / (2 * (K : ℝ) + (L₀ : ℝ) + 2) + 1) ^ ((3 : ℝ) / 2))
          + C_H * (1 + Clat)
              * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (2 + N)) ^ 3)
              * (Real.log ((K : ℝ) + 2)) ^ 2
              * (X * (2 * (K : ℝ) + (L₀ : ℝ) + 2) * N ^ (1 - δ₁) + X * Real.log (UB + 2))
          + C_E * (X + 1) * (N + 1) * (Real.log (N + 2)) ^ 4 * E2v / (K : ℝ)
          + C_G * (Pz⁻¹ + X⁻¹) * N ^ 2 * Real.log (N + 2)
          + CP * (Real.log ((K : ℝ) + 2)) ^ 2 * Ev * (N * Real.log (X + 2) + X ^ 2 * N ^ δ₁)
          + CX * (Real.log ((K : ℝ) + 2)) ^ 2 * X * (1 + Real.log (UB + 2))
              * (c₁ * N ^ (1 - δ₁)) * Real.sqrt Ev * (5 * Real.sqrt N + N ^ (δ₁ / 2))
        ≤ c * (Pz⁻¹ + X⁻¹) * N ^ 2 * Real.log N

end

end Work.FIArea7
