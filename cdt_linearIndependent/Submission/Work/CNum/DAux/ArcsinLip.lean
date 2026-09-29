import Mathlib

/-!
# A Lipschitz-type bound for `arcsin` on `[a, b]` with `b ≤ T < 1`

We prove the elementary estimate

`Real.arcsin b - Real.arcsin a ≤ Real.pi * (b - a) / (2 * Real.sqrt (1 - T ^ 2))`

for `0 ≤ a ≤ b ≤ T < 1`.  The route is monotonicity: the function

`G x = arcsin x - x / sqrt (1 - T ^ 2)`

has derivative `1 / sqrt (1 - x ^ 2) - 1 / sqrt (1 - T ^ 2) ≤ 0` on `(a, b)`,
because `0 ≤ x ≤ T` forces `1 - T ^ 2 ≤ 1 - x ^ 2`, hence
`1 / sqrt (1 - x ^ 2) ≤ 1 / sqrt (1 - T ^ 2)`.  Therefore `G` is antitone on
`[a, b]`, i.e. `arcsin b - arcsin a ≤ (b - a) / sqrt (1 - T ^ 2)`.  Finally
`(b - a) / sqrt (1 - T ^ 2) ≤ π (b - a) / (2 sqrt (1 - T ^ 2))` since `1 ≤ π / 2`.
-/

namespace Work.CNum.DAux

/-- The core estimate: for `0 ≤ a ≤ b ≤ T < 1`,
`arcsin b - arcsin a ≤ (b - a) / sqrt (1 - T ^ 2)`.  This is the sharp constant
`1 / sqrt (1 - T ^ 2)`; the stated bound for `ArcsinLip` only needs the weaker
`π / (2 sqrt (1 - T ^ 2))`. -/
private lemma arcsin_sub_le_sqrt {a b T : ℝ} (h0 : 0 ≤ a) (hab : a ≤ b) (hT : b ≤ T)
    (hT1 : T < 1) :
    Real.arcsin b - Real.arcsin a ≤ (b - a) / Real.sqrt (1 - T ^ 2) := by
  have hb0 : 0 ≤ b := le_trans h0 hab
  have hT0 : 0 ≤ T := le_trans hb0 hT
  have hs_pos : 0 < Real.sqrt (1 - T ^ 2) := by
    apply Real.sqrt_pos.mpr
    nlinarith
  have hderiv : ∀ x : ℝ, x ≠ -1 → x ≠ 1 →
      HasDerivAt (fun y : ℝ => Real.arcsin y - y / Real.sqrt (1 - T ^ 2))
        (1 / Real.sqrt (1 - x ^ 2) - 1 / Real.sqrt (1 - T ^ 2)) x := by
    intro x hx1 hx2
    have h1 : HasDerivAt Real.arcsin (1 / Real.sqrt (1 - x ^ 2)) x :=
      Real.hasDerivAt_arcsin hx1 hx2
    have h2 : HasDerivAt (fun y : ℝ => y / Real.sqrt (1 - T ^ 2))
        (1 / Real.sqrt (1 - T ^ 2)) x := (hasDerivAt_id x).div_const _
    exact h1.sub h2
  have hanti : AntitoneOn (fun x : ℝ => Real.arcsin x - x / Real.sqrt (1 - T ^ 2))
      (Set.Icc a b) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc a b) ?_ ?_ ?_
    · fun_prop
    · intro x hx
      rw [interior_Icc] at hx
      exact ((hderiv x (by linarith [hx.1, h0])
        (by linarith [hx.2, hT, hT1])).differentiableAt).differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hderiv x (by linarith [hx.1, h0]) (by linarith [hx.2, hT, hT1])).deriv]
      have hx0 : 0 ≤ x := by linarith [hx.1, h0]
      have hxT : x ≤ T := by linarith [hx.2, hT]
      have hsx : Real.sqrt (1 - T ^ 2) ≤ Real.sqrt (1 - x ^ 2) := by
        apply Real.sqrt_le_sqrt
        have hxsq : x ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hx0 hxT 2
        linarith
      have := one_div_le_one_div_of_le hs_pos hsx
      linarith
  have hthis := hanti (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab) hab
  have he : (b - a) / Real.sqrt (1 - T ^ 2)
      = b / Real.sqrt (1 - T ^ 2) - a / Real.sqrt (1 - T ^ 2) := by ring
  rw [he]
  linarith [hthis]

theorem ArcsinLip {a b T : ℝ} (h0 : 0 ≤ a) (hab : a ≤ b) (hT : b ≤ T) (hT1 : T < 1) :
    Real.arcsin b - Real.arcsin a ≤ Real.pi * (b - a) / (2 * Real.sqrt (1 - T ^ 2)) := by
  have hb0 : 0 ≤ b := le_trans h0 hab
  have hT0 : 0 ≤ T := le_trans hb0 hT
  have hs_pos : 0 < Real.sqrt (1 - T ^ 2) := by
    apply Real.sqrt_pos.mpr
    nlinarith
  have hmain := arcsin_sub_le_sqrt h0 hab hT hT1
  have hpi : (1 : ℝ) ≤ Real.pi / 2 := by nlinarith [Real.pi_gt_three]
  have hdiv : 0 ≤ (b - a) / Real.sqrt (1 - T ^ 2) :=
    div_nonneg (sub_nonneg.mpr hab) hs_pos.le
  have h2 : (b - a) / Real.sqrt (1 - T ^ 2)
      ≤ Real.pi * (b - a) / (2 * Real.sqrt (1 - T ^ 2)) := by
    have e : Real.pi * (b - a) / (2 * Real.sqrt (1 - T ^ 2))
        = (Real.pi / 2) * ((b - a) / Real.sqrt (1 - T ^ 2)) := by ring
    rw [e]
    exact le_mul_of_one_le_left hdiv hpi
  exact le_trans hmain h2

end Work.CNum.DAux
