/-
# `Work.FTS.PhiStar.Psi0Classes` — the estimate classes for the angular model

The `𝒲^{5,∞}`-bounds for the explicit angular model `ψ = psiSol α` (`Psi0Ode.lean`) are proved
from four *classes* of pointwise estimates:

* `IClass K`: the "sharp" bounds for the angular tail `I(θ) = ∫_θ^{π/2} cos²t Γ/sin t dt`
  — `O(1/α)` near `0` and `O(cos³θ Γ(θ))` near `π/2` (`Psi0Aux/cos_sq_Gam_div_sin_bounds`);
* `ElemClass b`: the elementary `D_θ`-bounds for `sin²θ`, `cos²θ`, `cos 2θ`;
* `HClass cc dd`: the `D_θ`-bounds for the source `Γ̄`;
* `ZClass κ λ`: the bounds `|D_θ^j P| ≤ κ_j α sin²θ cos^{2α/3}θ + λ_j sin 2θ` (`1 ≤ j ≤ 5`)
  for `P = G₀/(2C³)` — the crux, proved by the cancellation `D_θP = 6 sin²θ P − sin²θ Γ̄`
  together with the recursion `Z_{j+1} = Σ_i C(j,i)(D_θ^i(6 sin²θ)Z_{j-i} − D_θ^i(sin²θ)H_{j-i})`;
* `AClass ν`: `|D_θ^j ψ| ≤ ν_j sin 2θ` (`0 ≤ j ≤ 6`), by the recursion
  `A_{j+1} = 2cos 2θ A_j − 4 sin²2θ A_{j-1} + 4cos²θ Z_j − 16 sin²θcos²θ Z_{j-1}`.

The final `𝒲^{5,∞}`-bounds for `ψ''` (the target of `Psi0_exists`) are then
`|ψ''| ≤ C` and `|D_θ^jψ''| sin(2θ)^{-α/5}/(α+sin 2θ) ≤ C` for `1 ≤ j ≤ 5`, which follow from
`D_θ^jψ'' = 2 Z_j − 4 A_j − D_θ^jΓ̄` (`ψ'' = 2P − 4ψ − Γ̄`) and the weighted bounds for each term.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Psi0Defs
import Submission.Work.FTS.PhiStar.Psi0Ode

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false

/-- The angular tail bound of `Psi0Aux/cos_sq_Gam_div_sin_bounds`. -/
def IClass (K : ℝ) : Prop :=
  0 < K ∧
  (∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∀ θ ∈ Set.Icc (0 : ℝ) (2 / 3),
    (∫ t in θ..(Real.pi / 2), Real.cos t ^ 2 * Work.Spaces.Gam α t / Real.sin t) ≤ K / α) ∧
  (∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∀ θ ∈ Set.Icc (2 / 3 : ℝ) (Real.pi / 2),
    (∫ t in θ..(Real.pi / 2), Real.cos t ^ 2 * Work.Spaces.Gam α t / Real.sin t)
      ≤ K * Real.cos θ ^ 3 * Work.Spaces.Gam α θ)

/-- The elementary `D_θ`-bounds: `|D_θ^i sin²θ| ≤ b_i sin²θ`, `|D_θ^i cos²θ| ≤ b_i cos²θ`,
`|D_θ^i cos 2θ| ≤ b_i`. -/
def ElemClass (b : ℕ → ℝ) : Prop :=
  (∀ i, 0 ≤ b i) ∧
  (∀ i ≤ 7, ∀ θ ∈ Work.Spaces.Iθ,
    |Work.Spaces.dthU^[i] (fun t : ℝ => Real.sin t ^ 2) θ| ≤ b i * Real.sin θ ^ 2) ∧
  (∀ i ≤ 7, ∀ θ ∈ Work.Spaces.Iθ,
    |Work.Spaces.dthU^[i] (fun t : ℝ => Real.cos t ^ 2) θ| ≤ b i * Real.cos θ ^ 2) ∧
  (∀ i ≤ 7, ∀ θ ∈ Work.Spaces.Iθ,
    |Work.Spaces.dthU^[i] (fun t : ℝ => Real.cos (2 * t)) θ| ≤ b i)

/-- The `D_θ`-bounds for the source `Γ̄`. -/
def HClass (cc dd : ℕ → ℝ) : Prop :=
  (∀ j, 0 ≤ cc j) ∧ (∀ j, 0 ≤ dd j) ∧
  ∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∀ j : ℕ, 1 ≤ j → j ≤ 5 →
  ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
    |Work.Spaces.dthU^[j] (Work.FTS.VocabO.GamBar α) θ|
      ≤ cc j * α * Work.Spaces.Gam α θ + dd j * Real.sin (2 * θ)

/-- The `Z`-class: pointwise bounds for `D_θ^j P`, `1 ≤ j ≤ 5`. -/
def ZClass (κ ell : ℕ → ℝ) : Prop :=
  (∀ j, 0 ≤ κ j) ∧ (∀ j, 0 ≤ ell j) ∧
  ∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∀ j : ℕ, 1 ≤ j → j ≤ 5 →
  ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
    |Work.Spaces.dthU^[j] (Pfun α) θ|
      ≤ κ j * α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3)) + ell j * Real.sin (2 * θ)

/-- The `A`-class: `|D_θ^j ψ| ≤ ν_j sin 2θ` for `0 ≤ j ≤ 6`. -/
def AClass (ν : ℕ → ℝ) : Prop :=
  (∀ j, 0 ≤ ν j) ∧
  ∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∀ j : ℕ, j ≤ 6 →
  ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
    |Work.Spaces.dthU^[j] (psiSol α) θ| ≤ ν j * Real.sin (2 * θ)

end Work.FTS.PhiStar
