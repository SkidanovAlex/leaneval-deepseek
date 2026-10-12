import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseBogFS.EzeroRow
import Submission.Work.BoseBogFS.bogKAP_of_rows
import Submission.Work.BoseBogFS.hatChi_decay_uniform
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.hKAP_of_rows` — the `𝒞`-slot of the capstone from three honest rows

`Work.BoseBogFS.bogOpBoundAtFSWith_of_honestRows` consumes the `𝒞`-slot (`hKAP`) in the shape

```
∀ μ, Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ, CloseCondFS v μ ρ →
  Σ_k ½·bogKappaErr (bogA E ρ k) (bogB E ρ k) (bogC E ρ k)
    ≤ (ρ − μ)² ((D μ).gHat0/2) (ell v μ)³ (1 + δ μ ρ).
```

This module delivers exactly that shape from the three honest rows

* (`hchi`) the lattice localisation normalisation `Σ_k χ̂(kℓ)² ≤ 1` — FS's
  `(2π)⁻³∫|χ̂_Λ|² = ‖χ_Λ‖²_{L²}`, which at the box lattice is the *lattice Parseval
  identity* `Σ_{n∈ℤ³}χ̂(2πn)² = ∫χ² = 1` (so the row holds with the sharp constant `1`);
* (`hW0pos`, `hW0up`) the mass row `0 < Ŵ₁(0) = E.W1 0 ≤ 8πa(1 + δ')`, with
  `δ' = 2C(R/ℓ)²` the excess of `∫W₁` over `∫g₀ = 8πa` (FS `eq:W1-g`);
* (`hden`) FS's `𝒜(k) + ℬ(k) ≥ 2ρŴ₁(0)(1 − C(μa³)R²/a²)` at every mode, i.e.
  `2ρŴ₁(0)(1 − δ_D) ≤ τ(k) + 2ρŴ₁(k)`,

plus the three §11 identifications already carried by the capstone (`hg0`, `hmu`, `hell`).

The error produced is `δ μ ρ = 4(δ' + δ_D)`; the capstone's `hδ` row
(`δ μ ρ ≤ C₀·dil·(R/a)²`) is then arithmetic, because `(R/ℓ)² ≤ μa³(R/a)²` (`ℓ = K_ℓ/√(μa)`
with `K_ℓ ≥ 1`).

## The `ρ > 0` side condition

`kapArith` needs `0 < ρ`, while `CloseCondFS v μ ρ` only *states* `|ρ − μ| ≤ μK_ℓ⁻²/(2¹⁴π)`.
The lemma `rho_pos_of_close` below derives `0 < ρ` from `Adm` (which gives `μ > 0`,
`μa³ ≤ ε₀ ≤ 1`, so `K_ℓ ≥ 1` by `Kl_ge_one`) and the close condition: the threshold is at most
`μ/(2¹⁴π) ≤ μ/2`, whence `ρ ≥ μ/2 > 0`.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox
open Work.BoseBoxFix Work.BoseFixR Work.BoseB7

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ## 1. `ρ > 0` in the close region -/

/-- **`ρ > 0` in the close region.**  `Adm` gives `0 < μ` and `μa³ ≤ ε₀ ≤ 1`, hence
`K_ℓ ≥ 1` (`Kl_ge_one`), so the close threshold is `≤ μ/(2¹⁴π) ≤ μ/2`; with
`|ρ − μ| ≤ μK_ℓ⁻²/(2¹⁴π)` this gives `ρ ≥ μ/2`. -/
theorem rho_pos_of_close (v : EuclideanSpace ℝ (Fin 3) → ℝ) {ε₀ μ ρ : ℝ}
    (hε₀1 : ε₀ ≤ 1) (hav : 0 < a v) (hadm : Adm v ε₀ μ) (hclose : CloseCondFS v μ ρ) :
    0 < ρ := by
  have hμ : 0 < μ := hadm.1
  have ht : μ * a v ^ 3 ≤ 1 := le_trans hadm.2.1 hε₀1
  have hKl1 : 1 ≤ (paramsAt μ (a v)).Kl := Kl_ge_one v hμ hav ht
  have hKlpos : 0 < (paramsAt μ (a v)).Kl := lt_of_lt_of_le one_pos hKl1
  have hK2 : ((paramsAt μ (a v)).Kl) ^ (-(2 : ℝ)) ≤ 1 := by
    rw [Real.rpow_neg hKlpos.le, Real.rpow_two]
    exact inv_le_one_of_one_le₀ (by nlinarith)
  -- the threshold is at most `μ/2`
  have h214 : (2 : ℝ) ^ 14 = 16384 := by norm_num
  have hc1 : ((paramsAt μ (a v)).Kl) ^ (-(2 : ℝ)) / ((2 : ℝ) ^ 14 * π) ≤ 1 / ((2 : ℝ) ^ 14 * π) :=
    div_le_div_of_nonneg_right hK2 (by positivity)
  have hc2 : (1 : ℝ) / ((2 : ℝ) ^ 14 * π) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity), h214]
    nlinarith [Real.pi_gt_three]
  have hthr : closeThresholdFS v μ ≤ μ / 2 := by
    rw [closeThresholdFS]
    calc μ * ((paramsAt μ (a v)).Kl) ^ (-(2 : ℝ)) / ((2 : ℝ) ^ 14 * π)
        = μ * (((paramsAt μ (a v)).Kl) ^ (-(2 : ℝ)) / ((2 : ℝ) ^ 14 * π)) := by ring
      _ ≤ μ * (1 / ((2 : ℝ) ^ 14 * π)) := mul_le_mul_of_nonneg_left hc1 hμ.le
      _ ≤ μ * (1 / 2) := mul_le_mul_of_nonneg_left hc2 hμ.le
      _ = μ / 2 := by ring
  have habs := abs_le.mp hclose
  linarith [habs.1, habs.2, hthr, hμ]

/-! ## 2. The `𝒞`-slot in the capstone's shape -/

/-- **The capstone's `hKAP` from three honest rows.**  This is
`Work.BoseBogFS.bogOpBoundAtFSWith_of_honestRows`'s `hKAP` at an abstract family `D`, obtained
from the χ̂-normalisation row, the mass row and FS's denominator row.  The error is
`δ μ ρ = 4(δ' μ + δ_D μ)` (`hδdef`); the capstone's `hδ` row is then the arithmetic
`δ μ ρ ≤ 4(2C + 1)·dil·(R/a)²`. -/
theorem hKAP_of_rows {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    (R : ℝ) (D : ℝ → KzDatum) (ε₀ : ℝ) (δ' δD : ℝ → ℝ) (δ : ℝ → ℝ → ℝ)
    (hε₀1 : ε₀ ≤ 1) (hav : 0 < a v)
    (hδ'0 : ∀ μ : ℝ, Adm v ε₀ μ → 0 ≤ δ' μ)
    (hδ'1 : ∀ μ : ℝ, Adm v ε₀ μ → δ' μ ≤ 1 / 2)
    (hδD0 : ∀ μ : ℝ, Adm v ε₀ μ → 0 ≤ δD μ)
    (hδD1 : ∀ μ : ℝ, Adm v ε₀ μ → δD μ ≤ 1 / 2)
    (hchi : ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFS v h μ →
      (∑ k : (D μ).Mode, ((D μ).E.hatChi k) ^ 2) ≤ 1)
    (hW0pos : ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFS v h μ → 0 < (D μ).E.W1 0)
    (hW0up : ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFS v h μ →
      (D μ).E.W1 0 ≤ 8 * π * a v * (1 + δ' μ))
    (hden : ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, CloseCondFS v μ ρ →
      ∀ k : (D μ).Mode,
        2 * ρ * ((D μ).E.W1 0) * (1 - δD μ) ≤ (D μ).E.tau k + 2 * ρ * ((D μ).E.W1 k))
    (hg0 : ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFS v h μ → (D μ).gHat0 = 8 * π * a v)
    (hmu : ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFS v h μ → (D μ).E.mu = μ)
    (hell : ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFS v h μ → (D μ).E.ell = ell v μ)
    (hascat : ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFS v h μ → (D μ).E.aScat = a v)
    (hδdef : ∀ μ ρ : ℝ, Adm v ε₀ μ → δ μ ρ = 4 * (δ' μ + δD μ)) :
    ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, CloseCondFS v μ ρ →
      (∑ k : (D μ).Mode, (1 / 2 : ℝ) * Work.BoseB6.bogKappaErr
          (bogA (D μ).E ρ k) (bogB (D μ).E ρ k) (bogC (D μ).E ρ k))
        ≤ (ρ - μ) ^ 2 * ((D μ).gHat0 / 2) * ell3 v μ * (1 + δ μ ρ) := by
  intro μ hadm hview ρ hclose
  have hμ : 0 < μ := hadm.1
  have hℓ : 0 ≤ (D μ).E.ell := by
    rw [hell μ hadm hview, ell_eq]
    exact Work.BoseBogFS.sideAt_nonneg μ (a v)
  have hρ : 0 < ρ := rho_pos_of_close v hε₀1 hav hadm hclose
  have hg0' : (D μ).gHat0 = 8 * π * (D μ).E.aScat := by
    rw [hg0 μ hadm hview, hascat μ hadm hview]
  have hW0up' : (D μ).E.W1 0 ≤ 8 * π * (D μ).E.aScat * (1 + δ' μ) := by
    rw [hascat μ hadm hview]
    exact hW0up μ hadm hview
  have hmain := bogKAP_of_rows (D μ).F (D μ).E ρ (D μ).gHat0 (δ' μ) 0 (δD μ) hρ hℓ
    hg0' (hW0pos μ hadm hview) hW0up'
    (hδ'0 μ hadm) (hδ'1 μ hadm) le_rfl (by norm_num) (hδD0 μ hadm) (hδD1 μ hadm)
    (by simpa using hchi μ hadm hview) (hden μ hadm hview ρ hclose)
  have h1 : (1 : ℝ) + 4 * (δ' μ + 0 + δD μ) = 1 + δ μ ρ := by
    rw [hδdef μ ρ hadm]; ring
  have h2 : (ρ - (D μ).E.mu) ^ 2 * ((D μ).gHat0 / 2) * (D μ).E.ell ^ 3
      = (ρ - μ) ^ 2 * ((D μ).gHat0 / 2) * ell3 v μ := by
    rw [ell3, hmu μ hadm hview, hell μ hadm hview]
  rw [h2] at hmain
  rw [h1] at hmain
  exact hmain

end Work.BoseBogFS
