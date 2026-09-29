import Mathlib
import Submission.CDTPlan.Interfaces
import Submission.CDT.Discrepancy

/-!
# Local definitions for Area H (the fine holonomy bound)

Definitions owned by the `Holonomy3` area, kept in a separate module (with no `sorry`) so that
colleagues proving the pieces of the fine holonomy bound can import them directly.

* `euler` — the Euler operator `x·d/dx` on power series, used in the paper's §"The box principle
  step" to strip the `n^{e_i}` from the denominator type `(den type int)`.
* `blockStart`, `patched` — the patched function `g_{φ,γ}` of the paper's display
  `(rearrangement fine)`, written blockwise from the weights `w k = (γ_{k+1} - γ_k)/m`; the paper's
  rearrangement integral `rearrInt` is the double integral `∬ max(g(s),g(t))`.
-/

namespace Work.Holonomy3

open Submission.CDTPlan
open scoped BigOperators

variable {m d : ℕ}

/-- A multi-index `i : Fin d → Fin m` is **balanced** if each of the `m` species occurs exactly
`d/m` times (paper's set `V_m^d`, relevant when `m ∣ d`). -/
def Balanced (i : Fin d → Fin m) : Prop :=
  ∀ s : Fin m, (Finset.univ.filter (fun j : Fin d => i j = s)).card = d / m

/-- A multi-index `k : Fin d →₀ ℕ` is **`ε`-well distributed in the box `[0,D]^d`** if its
normalised coordinates `k/D` have box discrepancy `< ε` (paper's set `P_ε^d`, intersected with
`[0,D]^d ∩ ℤ^d`). -/
def LowDisc (D : ℕ) (k : Fin d →₀ ℕ) (ε : ℝ) : Prop :=
  (∀ j, k j ≤ D) ∧ Submission.CDT.Discrepancy.disc (fun j => (k j : ℝ) / D) < ε

/-- An auxiliary template `Q` for the box principle: it is supported on the balanced multi-indices,
its monomials are `ε`-well distributed, its coefficients are integers of absolute value `≤ H`, and
`D` bounds its partial degrees. -/
def AuxTemplate (D : ℕ) (ε H : ℝ) (Q : (Fin d → Fin m) → MvPolynomial (Fin d) ℚ) : Prop :=
  (∀ i, Q i ≠ 0 → Balanced i) ∧
  (∀ i, ∀ k ∈ (Q i).support, LowDisc D k ε) ∧
  (∀ i k, ∃ a : ℤ, (Q i).coeff k = a) ∧
  (∀ i k, |(((Q i).coeff k : ℚ) : ℝ)| ≤ H)

/-- The Euler operator `x·d/dx` on power series. -/
noncomputable def euler (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.X * PowerSeries.derivative (R := ℚ) f

/-- Start of the `k`-th block of the partition of `[0,1]` by the weights `w`. -/
noncomputable def blockStart {l : ℕ} (w : Fin (l + 1) → ℝ) (k : Fin (l + 1)) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin (l + 1) => j < k), w j

/-- The diagonal composition `g ∘ (Φ_1, …, Φ_d)` of a multivariable power series with univariate
power series: the coefficient of `z^n` is the sum over `m ≤ n` of the `m`-th coefficient of `g`
times the products of the `n_s`-th coefficients of `Φ_s ^ (m_s)`.  This is the formal expansion of
`(z_1,…,z_d) ↦ g (Φ_1(z_1),…,Φ_d(z_d))`. -/
noncomputable def diagComp {d : ℕ} (Φ : Fin d → PowerSeries ℂ) (g : MvPowerSeries (Fin d) ℂ) :
    MvPowerSeries (Fin d) ℂ :=
  fun n => ∑ m ∈ Finset.Iic n, g.coeff m * ∏ s, (Φ s ^ (m s)).coeff (n s)

/-- The paper's patched function `g_{φ,γ}` of display `(rearrangement fine)`, written blockwise
from the weights `w k = (γ_{k+1} - γ_k)/m`: on the `k`-th block it is `log|φ k|` composed with the
linear scaling of that block onto `[0,1]`. -/
noncomputable def patched {l : ℕ} (w : Fin (l + 1) → ℝ) (φ : Fin (l + 1) → ℂ → ℂ)
    (t : ℝ) : ℝ :=
  ∑ k : Fin (l + 1),
    if t ∈ Set.Ico (blockStart w k) (blockStart w k + w k) then
      circleLog (φ k) ((t - blockStart w k) / w k) else 0

end Work.Holonomy3
