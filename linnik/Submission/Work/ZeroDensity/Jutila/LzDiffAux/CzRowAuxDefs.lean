import Mathlib
import Submission.Work.ZeroDensity.Jutila.BzCross.CzRIAux
import Submission.Work.ZeroDensity.Jutila.BzCross.ModelBDefs
import Submission.Work.ZeroDensity.Jutila.BzCross.BzCrossDefs
import Submission.Work.ZeroDensity.Jutila.Bz3Defs
import Submission.Work.ZeroDensity.Jutila.KappaMertensDefs
import Submission.Work.ZeroDensity.Jutila.KappaAux

/-!
# Vocabulary for the row bound of Region I (`czRowBound`)

The `(q,t)`-row of `czRI` (`ModelBDefs.lean`) is

`czRowSum w y N q t = Σ_{r ≤ r₁} czMM r t · (r/κ r) · (t/κ t) · (⌊y/r⌋ · czFI w y r t)`,
`r₁ = min (⌊N/(q w)⌋) (czD w y t)`, `czD w y t = ⌊y/⌊w/t⌋⌋`.

Writing `P_r = [r ⟂ t]·μ(r)/kap(r)`, `C_r = ⌊y/r⌋`, `X_r = y - r·C_r ∈ [0,r)`,
`γ_r = log(C_r r / y) ∈ [-log 2, 0]`, `Y_t = y·t/w` and using
`log(C_r t/w) = log(Y_t/r) + γ_r`, the row becomes

`czRowSum = (t/kap t)·μ(t)·rowMain`, `rowMain = Σ_{r ≤ r₁} P_r ·(r C_r)·czFI w y r t`,

and the identity `r·C_r = y - X_r` together with

`czFI w y r t = (log(Y_t/r) + γ_r - 1)(γ_r - 1) + 1`
      `= (log(Y_t/r) - 1)(γ_r - 1) + (γ_r² - γ_r) + 1`

splits the row into the Mertens-type sums `rowS1`/`rowS0` of `KappaMertensInput`:

`rowMain = y·(- rowS1 t r₁ Y_t + rowT2 + rowT3 + rowS0 t r₁) - rowX`.

The remaining (elementary) estimates are `|rowX| ≤ 5·Σ(|log(Y_t/r)|+1)`,
`y|rowT2| ≤ 2·Σ(|log(Y_t/r)|+1)`, `y|rowT3| ≤ 20 Y_t` and `Σ_{r ≤ r₁}(|log(Y_t/r)|+1) ≤ 10 Y_t`
(for `r₁ ≤ 2Y_t`), while `KappaMertensInput` supplies the cancellation of `rowS1`, `rowS0`.
-/

namespace Work.ZeroDensity.Jutila.LzDiffAux

open Finset
open Work.ZeroDensity.Jutila.BzCross

noncomputable section

/-- `P_r = [r ⟂ t]·μ(r)/kap(r)`: the coefficient of the Mertens sums. -/
def rowCoef (t r : ℕ) : ℝ :=
  if Nat.Coprime r t then (ArithmeticFunction.moebius r : ℝ) / kap r else 0

/-- `Σ_{r ≤ R} [r ⟂ t] μ(r)/kap(r)`: the first Mertens sum of `KappaMertensInput`. -/
def rowS0 (t R : ℕ) : ℝ := ∑ r ∈ Finset.Icc 1 R, rowCoef t r

/-- `Σ_{r ≤ R} [r ⟂ t] (μ(r)/kap(r))·(log(Y/r) − 1)`: the second Mertens sum. -/
def rowS1 (t R : ℕ) (Y : ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 R, rowCoef t r * (Real.log (Y / (r : ℝ)) - 1)

/-- `γ_r = log(C_r r / y)`, where `C_r = ⌊y/r⌋`: the floor defect in logarithmic form. -/
def rowGam (y : ℝ) (r : ℕ) : ℝ :=
  Real.log (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ) / y)

/-- `X_r = y − r·C_r`, where `C_r = ⌊y/r⌋`: the floor remainder (in `[0,r)`). -/
def rowRem (y : ℝ) (r : ℕ) : ℝ := y - ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ)

/-- `Σ_{r ≤ r₁} P_r·czFI w y r t`. -/
def rowA (w y : ℝ) (t r1 : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 r1, rowCoef t r * czFI w y r t

/-- `Σ_{r ≤ r₁} P_r·X_r·czFI w y r t`. -/
def rowX (w y : ℝ) (t r1 : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 r1, rowCoef t r * (rowRem y r * czFI w y r t)

/-- `Σ_{r ≤ r₁} P_r·(log(Y/r) − 1)·γ_r`. -/
def rowT2 (y Y : ℝ) (t r1 : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 r1, rowCoef t r * ((Real.log (Y / (r : ℝ)) - 1) * rowGam y r)

/-- `Σ_{r ≤ r₁} P_r·(γ_r² − γ_r)`. -/
def rowT3 (y : ℝ) (t r1 : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 r1, rowCoef t r * (rowGam y r ^ 2 - rowGam y r)

/-- `Σ_{r ≤ r₁} P_r·(r C_r)·czFI w y r t`, the `r`-sum of the `(q,t)`-row of `czRI`. -/
def rowMain (w y : ℝ) (t r1 : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 r1,
    rowCoef t r * (((r : ℝ) * ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ)) * czFI w y r t)

/-- The pointwise splitting of the `F`-factor: with `C_r = ⌊y/r⌋`, `γ_r = log(C_r r/y)` and
`Y_t = y·t/w`, one has `log(C_r t/w) = log(Y_t/r) + γ_r`, whence
`czFI w y r t = (log(Y_t/r) + γ_r − 1)(γ_r − 1) + 1`. -/
lemma rowFI_split {w y : ℝ} {r t : ℕ} (hw : 0 < w) (hr : 1 ≤ r) (hry : (r : ℝ) ≤ y)
    (ht : 1 ≤ t) :
    czFI w y r t
      = (Real.log (czY w y t / (r : ℝ)) + rowGam y r - 1) * (rowGam y r - 1) + 1 := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hr1' : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hy0 : 0 < y := lt_of_lt_of_le one_pos (le_trans hr1' hry)
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  have hC1 : 1 ≤ ⌊y / (r : ℝ)⌋₊ := BzCross.czCr_ge_one hry hr
  have hCpos : (0 : ℝ) < ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ) / y := by
    have h2 : (1 : ℝ) ≤ ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hC1
    exact div_pos (mul_pos (by linarith) hr0) hy0
  have hYpos : 0 < czY w y t / (r : ℝ) := by
    rw [czY]
    exact div_pos (div_pos (mul_pos hy0 ht0) hw) hr0
  have hA : ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (t : ℝ) / w
      = (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ) / y) * (czY w y t / (r : ℝ)) := by
    rw [czY]
    field_simp
  rw [BzCross.czFI, hA, rowGam, Real.log_mul hCpos.ne' hYpos.ne']
  ring

end

end Work.ZeroDensity.Jutila.LzDiffAux
