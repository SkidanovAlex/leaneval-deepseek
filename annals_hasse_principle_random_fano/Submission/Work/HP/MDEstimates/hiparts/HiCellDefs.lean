import Mathlib
import Submission.Work.HP.MDEstimates.hiparts.HiDefs

/-!
# Dyadic cell bookkeeping for the `𝔡₃`-cells of the case-`I` sum at `(4,4)`

In `hi_cell_sum` the items are grouped according to two dyadic parameters: the `𝔡₃`-cutoff
`Δ i = A^{1/20} · 2^i` (indexed above the threshold `A^{1/20}`) and the `λ₁`-cutoff `M j = 2^j`.

* `hiDelta A i = A^{1/20} * 2^i` is the `i`-th `𝔡₃`-cutoff.
* `hiM j = 2^j` is the `j`-th `λ₁`-cutoff.
* `hiIdx A d = ⌊logb 2 (d / A^{1/20})⌋₊` is the cell index of a `𝔡₃`-value `d`.
* `hiJdx l = ⌊logb 2 l⌋₊` is the cell index of a `λ₁`-value `l`.
* `hiI A B = ⌈logb 2 (48 B² / A^{21/20})⌉₊`, `hiJ A = ⌈logb 2 A⌉₊` bound the indices of all
  items of the relevant range, so that there are at most `(hiI A B + 1)(hiJ A + 1)` cells.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP.MDEstimates.hiparts

/-- The `i`-th dyadic `𝔡₃`-cutoff `A^{1/20} · 2^i`. -/
def hiDelta (A : ℝ) (i : ℕ) : ℝ := A ^ ((1 : ℝ) / 20) * (2 : ℝ) ^ i

/-- The `j`-th dyadic `λ₁`-cutoff `2^j`. -/
def hiM (j : ℕ) : ℝ := (2 : ℝ) ^ j

/-- The dyadic cell index of a `𝔡₃`-value `d`, measured from the threshold `A^{1/20}`. -/
def hiIdx (A d : ℝ) : ℕ := ⌊Real.logb 2 (d / A ^ ((1 : ℝ) / 20))⌋₊

/-- The dyadic cell index of a `λ₁`-value `l`. -/
def hiJdx (l : ℝ) : ℕ := ⌊Real.logb 2 l⌋₊

/-- The largest `𝔡₃`-index of an item in range: `⌈logb 2 (48 B²/A^{21/20})⌉₊`. -/
def hiI (A B : ℝ) : ℕ := ⌈Real.logb 2 (48 * B ^ 2 / A ^ ((21 : ℝ) / 20))⌉₊

/-- The largest `λ₁`-index of an item in range: `⌈logb 2 A⌉₊`. -/
def hiJ (A : ℝ) : ℕ := ⌈Real.logb 2 A⌉₊

/-- The cell of an item, `(hiIdx A (d p), hiJdx (l p))`. -/
def hiCellOf (A : ℝ) (d l : ℝ) : ℕ × ℕ := (hiIdx A d, hiJdx l)

end Work.HP.MDEstimates.hiparts
