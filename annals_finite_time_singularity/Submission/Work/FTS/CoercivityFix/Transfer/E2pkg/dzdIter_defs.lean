/-
# `Transfer/E2pkg/dzdIter_defs.lean` — the explicit `(z ∂_z)`-iterate formulas

The `z`-factors of the transfer defect are the elementary rational functions

* `ampA α z = 2·z / (c(α)·(1+z)²)` — the nonlocal term, whose `z`-part is `φ(z) = z/(1+z)²`;
* `ampB α z = 2·z² / (1+z)³` — the projector correction.

The boundedness/integrability statements of `Transfer/E2pkg/dzdIter_coeff_bound` are the
statements that the `(z ∂_z)`-iterates of these functions, up to order `4`, are bounded on
`(0,∞)` and that their `w²`-weighted squares are integrable on `[0,∞)`.

This file just records the *closed forms* of those iterates, so that the two proofs (the
boundedness half and the integrability half) can be written against a fixed interface.
Writing `D_z = z ∂_z`, one checks by hand (`N_j` a polynomial, Γ denoting the gamma function
here only as a symbol):

  `(z∂_z)^j [z/(1+z)²]  = z·Q_j(z)/(1+z)^{j+2}`,  `Q_0 = 1`, `Q_1 = 1 - z`,
  `Q_2 = 1 - 4z + z²`, `Q_3 = 1 - 11z + 11z² - z³`, `Q_4 = 1 - 26z + 66z² - 26z³ + z⁴`;

  `(z∂_z)^j [z²/(1+z)³] = z²·N_j(z)/(1+z)^{j+3}`, `N_0 = 1`, `N_1 = 2 - z`,
  `N_2 = 4 - 7z + z²`, `N_3 = 8 - 33z + 18z² - z³`, `N_4 = 16 - 131z + 171z² - 41z³ + z⁴`.

(The numerator of `(z∂_z)^j [z²/(1+z)³]` is `z² N_j(z)`, i.e. the *double* zero at `z = 0` is
preserved by the iteration — this is what makes the `w²`-weighted square integrable at `0`:
`w(z)² = (1+z)⁴/z⁴` cancels the `z⁴` and leaves `N_j(z)²/(1+z)^{2+2j} ≤ C/(1+z)²`.)

Everything here is a definition or a `rfl`-lemma; nothing needs a proof.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E2pkg

/-- The radial profile `φ(z) = z/(1+z)²` of the nonlocal `z`-factor `ampA`. -/
def fA (z : ℝ) : ℝ := z / (1 + z) ^ 2

/-- The radial profile `z²/(1+z)³` of the projector correction's `z`-factor `ampB`. -/
def fB (z : ℝ) : ℝ := z ^ 2 / (1 + z) ^ 3

/-- The explicit `(z ∂_z)`-iterates of `φ(z) = z/(1+z)²`, i.e. `rA j` is
`z·Q_j(z)/(1+z)^{j+2}` for `j ≤ 4` (and the `j = 4` value is repeated beyond `4`). -/
def rA : ℕ → ℝ → ℝ
  | 0 => fun z => z / (1 + z) ^ 2
  | 1 => fun z => z * (1 - z) / (1 + z) ^ 3
  | 2 => fun z => z * (1 - 4 * z + z ^ 2) / (1 + z) ^ 4
  | 3 => fun z => z * (1 - 11 * z + 11 * z ^ 2 - z ^ 3) / (1 + z) ^ 5
  | _ => fun z => z * (1 - 26 * z + 66 * z ^ 2 - 26 * z ^ 3 + z ^ 4) / (1 + z) ^ 6

/-- The explicit `(z ∂_z)`-iterates of `z²/(1+z)³`, i.e. `rB j` is
`z²·N_j(z)/(1+z)^{j+3}` for `j ≤ 4` (and the `j = 4` value is repeated beyond `4`). -/
def rB : ℕ → ℝ → ℝ
  | 0 => fun z => z ^ 2 / (1 + z) ^ 3
  | 1 => fun z => z ^ 2 * (2 - z) / (1 + z) ^ 4
  | 2 => fun z => z ^ 2 * (4 - 7 * z + z ^ 2) / (1 + z) ^ 5
  | 3 => fun z => z ^ 2 * (8 - 33 * z + 18 * z ^ 2 - z ^ 3) / (1 + z) ^ 6
  | _ => fun z => z ^ 2 * (16 - 131 * z + 171 * z ^ 2 - 41 * z ^ 3 + z ^ 4) / (1 + z) ^ 7

@[simp] theorem fA_apply (z : ℝ) : fA z = z / (1 + z) ^ 2 := rfl

@[simp] theorem fB_apply (z : ℝ) : fB z = z ^ 2 / (1 + z) ^ 3 := rfl

@[simp] theorem rA_zero : rA 0 = fun z : ℝ => z / (1 + z) ^ 2 := rfl
@[simp] theorem rA_one : rA 1 = fun z : ℝ => z * (1 - z) / (1 + z) ^ 3 := rfl
@[simp] theorem rA_two : rA 2 = fun z : ℝ => z * (1 - 4 * z + z ^ 2) / (1 + z) ^ 4 := rfl
@[simp] theorem rA_three :
    rA 3 = fun z : ℝ => z * (1 - 11 * z + 11 * z ^ 2 - z ^ 3) / (1 + z) ^ 5 := rfl
@[simp] theorem rA_four :
    rA 4 = fun z : ℝ => z * (1 - 26 * z + 66 * z ^ 2 - 26 * z ^ 3 + z ^ 4) / (1 + z) ^ 6 := rfl

@[simp] theorem rB_zero : rB 0 = fun z : ℝ => z ^ 2 / (1 + z) ^ 3 := rfl
@[simp] theorem rB_one : rB 1 = fun z : ℝ => z ^ 2 * (2 - z) / (1 + z) ^ 4 := rfl
@[simp] theorem rB_two : rB 2 = fun z : ℝ => z ^ 2 * (4 - 7 * z + z ^ 2) / (1 + z) ^ 5 := rfl
@[simp] theorem rB_three :
    rB 3 = fun z : ℝ => z ^ 2 * (8 - 33 * z + 18 * z ^ 2 - z ^ 3) / (1 + z) ^ 6 := rfl
@[simp] theorem rB_four :
    rB 4 = fun z : ℝ => z ^ 2 * (16 - 131 * z + 171 * z ^ 2 - 41 * z ^ 3 + z ^ 4) / (1 + z) ^ 7 :=
  rfl

end Work.FTS.CoercivityFix.Transfer.E2pkg
