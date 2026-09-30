import Mathlib
import Submission.Work.BMF.VKdenom

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Parameter package for the twisted Vinogradov–Korobov prime number theorem

`Work.BMF.liouville.zetaTwSum_sub_main_le` proves
`Σ_{n ≤ x} Λ(n) n^{-iu} − x^{1-iu}/(1-iu) = O(x exp(−c (log x)^{1/10}))` uniformly for
`|u| ≤ exp((log x)^{5/4})`, by the truncated twisted Perron formula with contour shift at
height `T = |u| + (log x)^2 exp((log x)^{1/10}) + 7` and left abscissa
`σ₁ = 1 − c/(4 VKd(2T+3))`.

This file fixes, once and for all, the parameter package, so that the several analytic
estimates (left edge, horizontal edges, zero-free region, truncation) can be stated about
the same objects.
-/

namespace Work.BMF.liouville

/-- `E L = exp (L^{1/10})`. -/
noncomputable def ztE (L : ℝ) : ℝ := Real.exp (L ^ (1 / 10 : ℝ))

/-- The Perron height `T = |u| + L ^ 2 * exp (L^{1/10}) + 7`. -/
noncomputable def ztT (L u : ℝ) : ℝ := |u| + L ^ 2 * ztE L + 7

/-- `V = VKd (2 T + 3)`, the Vinogradov–Korobov denominator at the height of the contour. -/
noncomputable def ztV (L u : ℝ) : ℝ := Work.BMF.VKd (2 * ztT L u + 3)

/-- The saving parameter `c = min (min c₁ c₂) 1`. -/
noncomputable def ztC (c₁ c₂ : ℝ) : ℝ := min (min c₁ c₂) 1

/-- The left abscissa `σ₁ = 1 − c/(4 V)`. -/
noncomputable def ztS (c₁ c₂ L u : ℝ) : ℝ := 1 - ztC c₁ c₂ / (4 * ztV L u)

lemma ztC_le_one (c₁ c₂ : ℝ) : ztC c₁ c₂ ≤ 1 := min_le_right _ _

lemma ztC_le_left (c₁ c₂ : ℝ) : ztC c₁ c₂ ≤ c₁ :=
  le_trans (min_le_left _ _) (min_le_left _ _)

lemma ztC_le_right (c₁ c₂ : ℝ) : ztC c₁ c₂ ≤ c₂ :=
  le_trans (min_le_left _ _) (min_le_right _ _)

lemma ztC_pos {c₁ c₂ : ℝ} (h₁ : 0 < c₁) (h₂ : 0 < c₂) : 0 < ztC c₁ c₂ :=
  lt_min (lt_min h₁ h₂) one_pos

lemma ztE_pos (L : ℝ) : 0 < ztE L := Real.exp_pos _

end Work.BMF.liouville
