/-
# `Submission.Work.FIArea7.Area7Assembly6` — the assembly of `Area7Uni6`

This file assembles *FI* Proposition 17.3 (17.19) for the uniform cut `WUni6`, i.e.
`Work.FIArea7.Area7Uni6`, from

1. `hLoop : Prop172_6` — *FI* Proposition 17.2 (17.18), the project's deep input;
2. `hLow` — region I of the (17.10) main term, `4be(2K+1) ≤ N^{δ₁}` (the only place `hLoop` is
   consumed: every frequency of every such term satisfies `Q(|k|+1) ≤ N^{δ₁}`);
3. `hHigh` — region II (the complementary moduli), via the lattice count;
4. `hEng` — the *sharp* mollifier error of `EngineSharp6.lean` (the `1/|Δ|` kept to the end);
5. `hGuard` — the coprimality-guard removal;
6. `hCaps` — the two mass caps, consequences of `IsBetaCoeff6`;
7. `hNum` — `NumericCore`, the pure real-variable arithmetic of the assembly.

The parameters are `δ := δ₁/8`, `K := ⌈X³(log(N+2))²⁰⌉₊`, `x₀` large.  Together with the proved
`Work.FIArea7.area7_6_of_uniform_of_strip` and `Work.FIArea7.strip_bound6` this yields the round-6
contract `Work.FITop4.Area7_6`, conditional only on `Prop172_6`.

See `NOTES.md` §59 for the shape of each bound (in particular the *corrected* region shapes: region
II is `X·(2K+1)·N^{1-δ₁}`, **not** `X√(N(2K+1))N^{-δ₁/2}` — §59.3).
-/
import Mathlib
import Submission.Work.FIArea7.Area7Char6
import Submission.Work.FIArea7.UniAssembled6
import Submission.Work.FIArea7.UniEngine6
import Submission.Work.FIArea7.EngineSharp6
import Submission.Work.FIArea7.UniCharFree6
import Submission.Work.FITop.Defs
import Submission.Work.FIArea7.reflSign_separable
import Submission.Work.FIArea7.UniCut6
import Submission.Work.FIArea7CF.strip_bound6

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The shapes of the five inputs -/

/-- The support cap `#supp β ≤ 200(θ²N+θ√N+1)`. -/
def CapsS (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) : Prop :=
  (((Work.FIPlan.gBox (Work.FITop.radN Pa)).filter (fun z => β z ≠ 0)).card : ℝ)
    ≤ 200 * (Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1)

/-- The `L²`-cap `Σ_z‖β z‖² ≤ 1000(θN+√N+1)(log(N+2))³`. -/
def CapsE2 (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) : Prop :=
  (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2)
    ≤ 1000 * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * (Real.log (2 + Pa.N)) ^ 3

/-- **The sharp mollifier error** (`WUniOmega6Pull6_sub_Moll_le_sharp_aux`). -/
def EngineBound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ {Pa : Work.FITop.Params} {X : ℕ} {φ : ℝ} {z0 : GaussianInt} {β : GaussianInt → ℂ},
      Work.FITop4.IsBetaCoeff6 Pa φ z0 β → 1 ≤ X → ∀ K : ℕ, 1 ≤ K →
      ‖WUniOmega6Pull6 Pa X β - WUniOmega6Pull6Moll Pa X β K‖
        ≤ C * ((X : ℝ) + 1) * (Pa.N + 1) * (Real.log (Pa.N + 2)) ^ 4
            * (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2) / (K : ℝ)

/-- **The coprimality-guard removal** (`uniModeSum_sub_free_sharp`). -/
def GuardBound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt} {β : GaussianInt → ℂ},
      Work.FITop4.IsBetaCoeff6 Pa φ z0 β → ∀ (X K : ℕ) (ε : GaussianInt → ℤ),
      1 ≤ X →
      (K : ℝ) ≤ 2 * (X : ℝ) ^ 3 * (Real.log (Pa.N + 2)) ^ 20 →
      (X : ℝ) ^ 9 ≤ Pa.N →
      (∀ z1 z2 : GaussianInt, Work.FITop3.InPolarBox Pa φ z1 →
          Work.FITop3.InPolarBox Pa φ z2 →
          Work.FIArea7.reflSign z1 z2 = ε z1 * ε z2) →
      CapsS Pa β → CapsE2 Pa β →
      ‖Work.FIArea7.uniModeSum Pa X β K ε - Work.FIArea7.uniModeSumFree Pa X β K ε‖
        ≤ C * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log (Pa.N + 2)

/-- **The two mass caps are consequences of `IsBetaCoeff6`** (`isBetaCoeff6_mass_caps`). -/
def CapsBound : Prop :=
  ∀ {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt} {β : GaussianInt → ℂ},
    Work.FITop4.IsBetaCoeff6 Pa φ z0 β → CapsS Pa β ∧ CapsE2 Pa β

/-! ## 2. The pure arithmetic of the assembly

All the real-variable inequalities of `NOTES.md` §59.3 in one statement: with
`X⁸ ≤ N^{δ₁}`, `K ≥ X³(log(N+2))²⁰`, `θ ∈ (0,1]`, `δ₁ ∈ (0,3/32)`, `UB ≤ 4θN+2` and the two mass
caps, the sum of the four error bounds is `≤ c(Pz⁻¹+X⁻¹)N²log N`. -/
def NumericCore : Prop :=
  ∀ (C_L C_H C_E C_G c₁ Clat δ₁ : ℝ),
    0 < C_L → 0 < C_H → 0 < C_E → 0 < C_G → 0 < c₁ → 0 < Clat → 0 < δ₁ → δ₁ < 3 / 32 →
    ∃ c N₀ : ℝ, 0 < c ∧
      ∀ {N X : ℝ} {K : ℕ} {θ Pz UB E2v : ℝ},
        N₀ ≤ N → 3 ≤ N → 1 ≤ X → 0 < θ → θ ≤ 1 → X ^ 8 ≤ N ^ δ₁ →
        0 < Pz → 1 ≤ (K : ℝ) → X ^ 3 * (Real.log (N + 2)) ^ 20 ≤ (K : ℝ) →
        (K : ℝ) ≤ 2 * X ^ 3 * (Real.log (N + 2)) ^ 20 →
        0 < UB → UB ≤ 4 * θ * N + 2 →
        0 ≤ E2v → E2v ≤ 1000 * (θ * N + Real.sqrt N + 1) * (Real.log (N + 2)) ^ 3 →
          C_L * c₁ ^ 2 * N ^ (2 - 2 * δ₁) * (Real.log ((K : ℝ) + 2)) ^ 2
              * (X * Real.sqrt (N ^ δ₁ / (2 * (K : ℝ) + 1) + 1)
                  + (N ^ δ₁ / (2 * (K : ℝ) + 1) + 1) ^ ((3 : ℝ) / 2))
          + C_H * (1 + Clat)
              * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (2 + N)) ^ 3)
              * (Real.log ((K : ℝ) + 2)) ^ 2
              * (X * (2 * (K : ℝ) + 1) * N ^ (1 - δ₁) + X * Real.log (UB + 2))
          + C_E * (X + 1) * (N + 1) * (Real.log (N + 2)) ^ 4 * E2v / (K : ℝ)
          + C_G * (Pz⁻¹ + X⁻¹) * N ^ 2 * Real.log (N + 2)
          ≤ c * (Pz⁻¹ + X⁻¹) * N ^ 2 * Real.log N

/-! ## 3. The assembly -/

end

end Work.FIArea7
