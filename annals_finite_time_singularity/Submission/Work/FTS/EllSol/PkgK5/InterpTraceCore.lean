/-
# `PkgK5.InterpTraceCore` — the trace-vanishing heavy-weight interpolation core

This module is the analytic engine behind
`Work.FTS.EllSol.PkgK5.i0Family_le_openTrace`.

## The route (the `m`-level / cut-off route, no flux hypotheses, no traces on `V` itself)

Fix a datum `G` which is `C^∞` on the open quadrant, whose values at `θ = 0, π/2` vanish and
whose slices `θ ↦ D_zG(z,θ)` have **vanishing traces** at both endpoints (`z > 0`).  Write

* `ψ := D_zG`, `Ξ := D_z²G + b·D_zG` with `b z = (z-3)/(1+z)`,
* `X := ∫∫ ρ (∂_θψ)²`, `Z := ∫∫ρ ψ²`, `B := ∫∫ρ (D_z²G)²`, `T := ∫∫ρ (∂_θ²G)²`,
  `ρ = w(z)²·sin(2θ)^{-η}`,

and for the logarithmic cut-off `χ_k` of `Work.EllipticEst.Core.zLogCut` put
`m_k(θ) := ∫_z χ_k(z) w(z)² ψ(z,θ)² dz`, `g_k := √(m_k)`.  The steps are

1. `m_k ∈ C²(0,π/2)`, `m_k''/2 = Ψ_k + G_k` where
   `Ψ_k := ∫ χ_k w² (∂_θψ)²`, `G_k := ∫ χ_k w² ψ ∂_θ²ψ`,
   `(g_k')² + g_k g_k'' = m_k''/2` and `(g_k')² ≤ Ψ_k` (Cauchy–Schwarz);
2. the open-class Agmon `Work.EllipticEst.Core.i0Aux.sliceAgmonOpenCore` for `g_k`:
   `(1/200)∫σ(g_k')² ≤ -∫σ g_k g_k'' + 2η∫σ g_k²`;
3. combining: `X_k/200 ≤ 2η Z_k + |𝒢_k|`, `X_k = ∫σΨ_k`, `Z_k = ∫σm_k`, `𝒢_k = ∫σG_k`;
4. the radial integration by parts `RPFresh.radial_ibp_bt` with `φ := χ_k ψ`, `ψ' := ∂_θ²G`
   (the boundary terms vanish because `χ_k` is supported away from `0, ∞`):
   `G_k(θ) = -∫ χ_k w² Ξ ∂_θ²G - ∫ (z∂_zχ_k) w² ψ ∂_θ²G`, and the second term is `O(1/log k)`;
5. Cauchy–Schwarz in `(θ,z)` gives
   `|𝒢_k| ≤ √(DD'_k T_k) + δ_k √(Z T)`, `DD'_k = ∫∫ρχ_kΞ²`, `T_k = ∫∫ρχ_k(∂_θ²G)²`;
6. monotone convergence in `k` (the cut-offs increase to `1` pointwise) yields
   `X/200 ≤ 2η Z + √(DD' T)`, and `DD' ≤ 2B + 18Z`.

Everything is proved with the cut-off in place, so that all the `z`-integrals range over a
compact sub-interval of `(0,∞)` and no flux hypothesis is ever needed.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.EllipticEst.Core.Defs
import Submission.Work.EllipticEst.Core.i0Aux.InterpDefs
import Submission.Work.EllipticEst.Core.i0Aux.Honest
import Submission.Work.EllipticEst.Core.i0Aux.sliceAgmonOpenCore
import Submission.Work.EllipticEst.Core.zLogCut
import Submission.Work.FTS.EllipticEst.RPFresh.CoreInterpHk

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- The properties of the logarithmic cut-off family that the core proof uses (these are
exactly the conclusions of `Work.EllipticEst.Core.zLogCut`). -/
structure CutFam (χ : ℕ → ℝ → ℝ) (K : ℝ) : Prop where
  K0 : 0 ≤ K
  sm : ∀ (k : ℕ), ContDiffOn ℝ Work.Stability.smoothOrder (χ k) (Set.Ioi 0)
  bnd : ∀ (k : ℕ) (z : ℝ), 0 < z → 0 ≤ χ k z ∧ χ k z ≤ 1
  supp : ∀ (k : ℕ) (z : ℝ), 0 < z → (z ≤ 1 / ((k : ℝ) + 1) ^ 2 ∨ ((k : ℝ) + 1) ^ 2 ≤ z) → χ k z = 0
  mono : ∀ (k : ℕ) (z : ℝ), 0 < z → χ k z ≤ χ (k + 1) z
  conv : ∀ (z : ℝ), 0 < z → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k : ℕ, N ≤ k → 1 - χ k z < ε
  d1 : ∀ (k : ℕ) (z : ℝ), 0 < z → |z * deriv (χ k) z| ≤ K / Real.log ((k : ℝ) + 2)
  d2 : ∀ (k : ℕ) (z : ℝ), 0 < z →
    |z * deriv (fun y : ℝ => y * deriv (χ k) y) z| ≤ K / Real.log ((k : ℝ) + 2)

theorem cutFam_exists : ∃ (χ : ℕ → ℝ → ℝ) (K : ℝ), CutFam χ K := by
  obtain ⟨χ, K, h1, h2, h3, h4, h5, h6, h7, h8⟩ := Work.EllipticEst.Core.zLogCut
  exact ⟨χ, K, h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- The support window of `χ k`: `[a_k, b_k]`. -/
def cA (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1) ^ 2
def cB (k : ℕ) : ℝ := ((k : ℝ) + 1) ^ 2

theorem cA_pos (k : ℕ) : 0 < cA k := by
  rw [cA]; positivity

theorem cA_le_cB (k : ℕ) : cA k ≤ cB k := by
  have h1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k; linarith
  have h2 : 0 < ((k : ℝ) + 1) ^ 2 := by positivity
  rw [cA, cB, div_le_iff₀ h2]
  nlinarith [h1, sq_nonneg ((k : ℝ) + 1 - 1)]

theorem cB_pos (k : ℕ) : 0 < cB k := by
  rw [cB]; positivity

theorem cB_nonneg (k : ℕ) : 0 ≤ cB k := (cB_pos k).le

/-! ## The cut-off quantities of the `m`-level argument

For a (smooth) `ψ : ℝ → ℝ → ℝ` and the cut-off index `k` we abbreviate the four parameter
integrals over the window `[cA k, cB k]`:

* `cMK χ k ψ θ  = ∫ χ_k w² ψ²`      (the cut-off mass `m_k(θ)`),
* `cPK χ k ψ θ  = ∫ χ_k w² ψ ∂_θψ`   (`= m_k'(θ)/2`),
* `cAK χ k ψ θ  = ∫ χ_k w² (∂_θψ)²`  (the `θ`-energy, `X_k` before integration in `θ`),
* `cBK χ k ψ θ  = ∫ χ_k w² ψ ∂_θ²ψ`  (the pairing; `m_k''/2 = AK + BK`).

The Cauchy–Schwarz bound `PK² ≤ MK·AK` is what makes `g_k := √m_k` satisfy `(g_k')² ≤ AK`.
-/

/-- The cut-off mass `m_k(θ) = ∫ χ_k w² ψ²`. -/
def cMK (χ : ℕ → ℝ → ℝ) (k : ℕ) (ψ : ℝ → ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ z in (cA k)..(cB k), χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2

/-- The cut-off cross term `P_k(θ) = ∫ χ_k w² ψ ∂_θψ` (half of `m_k'`). -/
def cPK (χ : ℕ → ℝ → ℝ) (k : ℕ) (ψ : ℝ → ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ z in (cA k)..(cB k), χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ * Work.Spaces.pth ψ z θ

/-- `A_k(θ) = ∫ χ_k w² (∂_θψ)²`, the first half of `m_k''/2`. -/
def cAK (χ : ℕ → ℝ → ℝ) (k : ℕ) (ψ : ℝ → ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ z in (cA k)..(cB k), χ k z * (Work.Spaces.w z) ^ 2 * (Work.Spaces.pth ψ z θ) ^ 2

/-- `B_k(θ) = ∫ χ_k w² ψ ∂_θ²ψ`, the second half of `m_k''/2`. -/
def cBK (χ : ℕ → ℝ → ℝ) (k : ℕ) (ψ : ℝ → ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ z in (cA k)..(cB k), χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ * Work.Spaces.pthIter 2 ψ z θ

end Work.FTS.EllSol.PkgK5
