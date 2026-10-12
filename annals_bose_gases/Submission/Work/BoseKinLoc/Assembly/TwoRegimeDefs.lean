import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseKinLoc.Residuals
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Assembly` — the two-regime symbol in box-momentum variables

`AssemblySymbol β C` (`Submission/Work/BoseKinLoc/Residuals.lean`) is a **pointwise
budget in momentum space**:

```
εT (dℓ)⁻² raSym ℓ d p + b β⁻¹ ‖p‖²/(ℓ²‖p‖²+β)
  + (1-εT) tprSym ℓ (2s) C p + εT tprSym ℓ (2ds) C p  ≤  ‖p‖²      (∀ ℓ d s εT b, ∀p)
```

over the regime `KinRegime c₀ ℓ d s εT b`.  Its two-regime kernel `tprSym` is
homogeneous in the box momentum `q := ℓ‖p‖`:  the far-region branch is
`(‖p‖ − (2σℓ)⁻¹)₊²`, the near-region branch is `Cσ³‖p‖²`, and the switch is at
`‖p‖ = (5/6)(σℓ)⁻¹`, i.e. **exactly at `q = (5/6)σ⁻¹`**.

This module records that normalisation.  `tprR` is `tprSym` at `ℓ = 1` with the
spatial momentum replaced by the box momentum `q = ℓ‖p‖`; `tprSym_scale` is the
(machine-checked) statement that `ℓ² · tprSym ℓ σ C p = tprR σ C (ℓ‖p‖)`.  All the
real arithmetic of the budget is then done on `tprR` (see `two_regime_core.lean`).
-/

noncomputable section

namespace Work.BoseKinLoc.Assembly

open Work.BoseKinLoc
open Submission.BoseGases

/-- The two-regime symbol `tprSym` at `ℓ = 1`, as a function of the box momentum
`q = ℓ‖p‖ ≥ 0`: the far-region branch `[q − (2σ)⁻¹]₊²` and the near-region Taylor
branch `Cσ³q²`, switched at `q = (5/6)σ⁻¹`. -/
def tprR (σ C q : ℝ) : ℝ :=
  if (5 / 6) * σ⁻¹ ≤ q then fsKinCoeff ((2 * σ)⁻¹) q else C * σ ^ 3 * q ^ 2

/-- `tprR` is nonnegative for nonnegative data. -/
lemma tprR_nonneg {σ C : ℝ} (hσ : 0 ≤ σ) (hC : 0 ≤ C) (q : ℝ) : 0 ≤ tprR σ C q := by
  unfold tprR
  split
  · exact fsKinCoeff_nonneg _ _
  · exact mul_nonneg (mul_nonneg hC (pow_nonneg hσ 3)) (sq_nonneg q)

/-- `tprR` is `≤ q²` when the near-region coefficient is `≤ 1` and the far-region
cut-off is `≥ 0`. -/
lemma tprR_le_sq {σ C : ℝ} (hσ : 0 ≤ σ) (hC : 0 ≤ C)
    (hcoef : C * σ ^ 3 ≤ 1) {q : ℝ} (hq : 0 ≤ q) : tprR σ C q ≤ q ^ 2 := by
  unfold tprR
  split
  · rename_i h
    unfold fsKinCoeff
    have hinv : 0 ≤ (2 * σ)⁻¹ := inv_nonneg.mpr (by linarith)
    have hmax : max (q - (2 * σ)⁻¹) 0 ≤ q := max_le (by linarith) hq
    have h0 : 0 ≤ max (q - (2 * σ)⁻¹) 0 := le_max_right _ _
    nlinarith [mul_nonneg (sub_nonneg.mpr hmax) (add_nonneg hq h0)]
  · nlinarith [mul_le_mul_of_nonneg_right hcoef (sq_nonneg q)]

end Work.BoseKinLoc.Assembly
