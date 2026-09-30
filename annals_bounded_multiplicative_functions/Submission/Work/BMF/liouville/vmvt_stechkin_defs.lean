import Mathlib
import Submission.Work.BMF.vmvt_setup
import Submission.Work.BMF.vkford_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Constants for the sharp (Stechkin) Vinogradov mean value bound

This file fixes the constant used in the sharp Vinogradov--Karatsuba iteration that yields
Stechkin's bound

`J_{s,k}(X) ≤ exp(C min(⌊s/k⌋,k) k² log k) · X^{2s - k(k+1)/2 + (k²/2)(1-1/k)^{⌊s/k⌋}}`

(see `Work.BMF.vmvt_stechkin_explicit`, and the citation of Stechkin's theorem in Ford,
*Vinogradov's integral and bounds for the Riemann zeta function*, Proc. LMS 85 (2002), (1.6)).

The iteration is driven with the constant

`stechF k r = exp(K·k·r·(k+r)·(1+log k))`,

which is monotone in the right way: `stechF k r ≤ exp(C·r·k²·log k)` whenever `r ≤ k`, while
for `r ≥ k` one reduces to `r = k` first (so that only `exp(C·k³·log k)` is paid).
-/

namespace Work.BMF.liouville

open scoped BigOperators

noncomputable section

/-- The constant `K = 10·C₀` with `C₀` the constant of `Submission.Work.BMF.vmvt_setup`. -/
def stechK : ℝ := 10 * Work.BMF.C0

/-- The sharp constant factor `exp(K·k·r·(k+r)·(1+log k))` of the induction. -/
def stechF (k r : ℕ) : ℝ :=
  Real.exp (stechK * (k : ℝ) * (r : ℝ) * ((k : ℝ) + (r : ℝ)) * (1 + Real.log (k : ℝ)))

/-- The constant of the final estimate: `stechC = 8·stechK`. -/
def stechC : ℝ := 8 * stechK

lemma stechK_pos : 0 < stechK := by
  have h := Work.BMF.C0_pos
  simp only [stechK]
  linarith

lemma stechC_pos : 0 < stechC := by
  have h := stechK_pos
  simp only [stechC]
  linarith

lemma stechF_pos (k r : ℕ) : 0 < stechF k r := Real.exp_pos _

lemma stechF_nonneg (k r : ℕ) : 0 ≤ stechF k r := (stechF_pos k r).le

/-- The one-step growth of the constant: `stechF k (r+1) = stechF k r · exp(K k (2r+k+1)(1+log k))`. -/
lemma stechF_growth (k r : ℕ) :
    stechF k (r + 1) =
      stechF k r * Real.exp (stechK * (k : ℝ) * (2 * (r : ℝ) + (k : ℝ) + 1) * (1 + Real.log (k : ℝ))) := by
  rw [stechF, stechF, ← Real.exp_add]
  congr 1
  have h1 : (((r + 1 : ℕ)) : ℝ) = (r : ℝ) + 1 := by push_cast; ring
  rw [h1]
  have h2 : (k : ℝ) + ((r : ℝ) + 1) = (k : ℝ) + (r : ℝ) + 1 := by ring
  rw [h2]
  ring

end

end Work.BMF.liouville
