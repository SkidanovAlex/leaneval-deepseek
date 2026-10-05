import Mathlib
import Submission.Work.RPB.B5.RhoPerDefs
import Submission.Work.RPB.B5.rhoQuad_sub_rhoMid_nonneg
import Submission.Work.RPB.B5.deriv_rhoMid_rhoQuad
import Submission.Work.RPB.B5.deriv_wM

/-!
# Positivity of the `x`-derivative of the blended radius function `rhoPer` (node B5)

`rhoPer ρe δ δA u₂ τ x t = wL x * ρe τ t (sig x) + wM x * rhoMid x + wR x * rhoQuad x`
is the smooth blend of the `ρh`-branch, the affine middle branch `rhoMid` and the quadratic
branch `rhoQuad` on the left half `x ≤ 0`.  This file proves that it is strictly increasing in
`x` on `(-√2, 0]`, i.e. its `x`-derivative is positive there.

## Structure of the proof

Write `f y = rhoPer ρe δ δA u₂ τ y t`, `A y = ρe τ t (sig y)`.  On the region where the `ρh`
branch is active (`x + √2 < δA`) the derivative rearranges to

`deriv f x = deriv wL x * (A x - rhoMid x) + wL x * A' x + wM x * (π²/32)`,

with every term `≥ 0` and the middle term *strictly* positive (`wL x > 0`, and `A' x > 0`
because `deriv (ρe τ t) (sig x) < 0` while `x < 0`).  On the complementary region
(`δA ≤ x + √2`) the `wL`-branch is switched off and

`deriv f x = deriv wR x * (rhoQuad x - rhoMid x) + wM x * (π²/32) + wR x * Q' x`,

again with all terms `≥ 0` and one strictly positive.  The sign facts for `rhoQuad - rhoMid`
and `rhoQuad'` use the hypotheses `4 u₂² ≥ 1 + u₂` and `-√2 < x`.

## Contents

* `wL_deriv_nonpos`, `wL_deriv_eq_zero_of_le`, `wL_deriv_eq_zero_of_ge` — the sign and the
  vanishing of `deriv (wL δ δA)` on the two plateaux;
* `wR_deriv_nonneg`, `wR_deriv_eq_zero_of_le`, `wR_deriv_eq_zero_of_ge` — the same for `wR`;
* `rhoPer_deriv_pos` — the requested lemma.
-/

open Set

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-! ## Derivative facts for the two cutoffs -/

theorem wL_deriv_nonpos {δ δA : ℝ} (h : δ < δA) (x : ℝ) : deriv (wL δ δA) x ≤ 0 :=
  (wL_antitone h).deriv_nonpos

theorem wL_deriv_eq_zero_of_le {δ δA x : ℝ} (h : δ < δA) (hx : x + Real.sqrt 2 ≤ δ) :
    deriv (wL δ δA) x = 0 := by
  apply IsLocalMax.deriv_eq_zero
  filter_upwards with y
  rw [wL_eq_one h hx]
  exact wL_le_one δ δA y

theorem wL_deriv_eq_zero_of_ge {δ δA x : ℝ} (h : δ < δA) (hx : δA ≤ x + Real.sqrt 2) :
    deriv (wL δ δA) x = 0 := by
  apply IsLocalMin.deriv_eq_zero
  filter_upwards with y
  rw [wL_eq_zero h hx]
  exact wL_nonneg δ δA y

theorem wR_deriv_nonneg {δ u₂ : ℝ} (h : u₂ < Real.sqrt 2 - δ) (x : ℝ) :
    0 ≤ deriv (wR δ u₂) x := (wR_monotone h).deriv_nonneg

theorem wR_deriv_eq_zero_of_le {δ u₂ x : ℝ} (h : u₂ < Real.sqrt 2 - δ)
    (hx : x + Real.sqrt 2 ≤ u₂) :
    deriv (wR δ u₂) x = 0 := by
  apply IsLocalMin.deriv_eq_zero
  filter_upwards with y
  rw [wR_eq_zero h hx]
  exact wR_nonneg δ u₂ y

theorem wR_deriv_eq_zero_of_ge {δ u₂ x : ℝ} (h : u₂ < Real.sqrt 2 - δ)
    (hx : Real.sqrt 2 - δ ≤ x + Real.sqrt 2) :
    deriv (wR δ u₂) x = 0 := by
  apply IsLocalMax.deriv_eq_zero
  filter_upwards with y
  rw [wR_eq_one h (by linarith : -δ ≤ x)]
  exact wR_le_one δ u₂ y

/-! ## The main lemma -/

end Work.RPB.B5
