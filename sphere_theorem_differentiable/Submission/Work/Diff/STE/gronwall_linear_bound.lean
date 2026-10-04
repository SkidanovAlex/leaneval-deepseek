import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedVariables false

namespace Work.Diff.STE

/-- Grönwall's comparison for the auxiliary function `t ↦ (y t + 1) * exp (-(C * t))`:
if `y' ≤ C * (1 + y)` on `[0, T]`, this function is antitone on `[0, T]`.

The proof computes the derivative
`F' t = exp (-(C * t)) * (y' t - C * (1 + y t)) ≤ 0` on the interior and applies
`antitoneOn_of_hasDerivWithinAt_nonpos`.  Only interior points are needed, which is
why the derivative hypothesis is available on a whole neighbourhood there. -/
private lemma gronwall_aux {y y' : ℝ → ℝ} {T C : ℝ}
    (hderiv : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt y (y' t) (Set.Icc 0 T) t)
    (hineq : ∀ t ∈ Set.Icc 0 T, y' t ≤ C * (1 + y t)) :
    AntitoneOn (fun t : ℝ => (y t + 1) * Real.exp (-(C * t))) (Set.Icc 0 T) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T)
    (f := fun t : ℝ => (y t + 1) * Real.exp (-(C * t)))
    (f' := fun t : ℝ => Real.exp (-(C * t)) * (y' t - C * (1 + y t))) ?hcont ?hder ?hnonpos
  · -- continuity of `F` on `[0, T]`
    have hycont : ContinuousOn y (Set.Icc 0 T) := fun t ht => (hderiv t ht).continuousWithinAt
    exact (hycont.add continuousOn_const).mul
      (Real.continuous_exp.comp_continuousOn ((continuousOn_const.mul continuousOn_id).neg))
  · -- differentiability on the interior, with the announced derivative
    intro x hx
    have hxIcc : x ∈ Set.Icc 0 T := interior_subset hx
    have hmem : Set.Icc 0 T ∈ nhds x :=
      Filter.mem_of_superset (IsOpen.mem_nhds isOpen_interior hx) interior_subset
    have hyd : HasDerivAt y (y' x) x := (hderiv x hxIcc).hasDerivAt hmem
    have h1 : HasDerivAt (fun t : ℝ => y t + 1) (y' x) x := by
      simpa using hyd.add_const 1
    have hg : HasDerivAt (fun t : ℝ => -(C * t)) (-C) x := by
      have h : HasDerivAt (fun t : ℝ => (-C) * t) (-C) x := hasDerivAt_const_mul (-C)
      simpa only [neg_mul] using h
    have h2 : HasDerivAt (fun t : ℝ => Real.exp (-(C * t)))
        (Real.exp (-(C * x)) * (-C)) x := hg.exp
    have h3 : HasDerivAt (fun t : ℝ => (y t + 1) * Real.exp (-(C * t)))
        (y' x * Real.exp (-(C * x)) + (y x + 1) * (Real.exp (-(C * x)) * (-C))) x :=
      h1.mul h2
    have h4 : y' x * Real.exp (-(C * x)) + (y x + 1) * (Real.exp (-(C * x)) * (-C))
        = Real.exp (-(C * x)) * (y' x - C * (1 + y x)) := by ring
    exact (h3.congr_deriv h4).hasDerivWithinAt
  · -- the derivative is nonpositive
    intro x hx
    have hxIcc : x ∈ Set.Icc 0 T := interior_subset hx
    have hx' : y' x ≤ C * (1 + y x) := hineq x hxIcc
    have hb : y' x - C * (1 + y x) ≤ 0 := sub_nonpos.mpr hx'
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hb

theorem gronwall_linear_bound {y y' : ℝ → ℝ} {T C B : ℝ} (hC : 0 ≤ C)
    (hderiv : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt y (y' t) (Set.Icc 0 T) t)
    (hineq : ∀ t ∈ Set.Icc 0 T, y' t ≤ C * (1 + y t))
    (h0 : y 0 ≤ B) :
    ∀ t ∈ Set.Icc 0 T, y t ≤ (B + 1) * Real.exp (C * t) - 1 := by
  have hanti := gronwall_aux hderiv hineq
  intro t ht
  have h0mem : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  have hle := hanti h0mem ht ht.1
  -- `F t ≤ F 0 = y 0 + 1 ≤ B + 1`
  have hA : (y t + 1) * Real.exp (-(C * t)) ≤ B + 1 := by
    have h1 : (y 0 + 1) * Real.exp (-(C * 0)) = y 0 + 1 := by simp
    calc (y t + 1) * Real.exp (-(C * t)) ≤ (y 0 + 1) * Real.exp (-(C * 0)) := hle
      _ = y 0 + 1 := h1
      _ ≤ B + 1 := by linarith
  -- multiply by `exp (C * t) > 0`
  have h2 : (y t + 1) * Real.exp (-(C * t)) * Real.exp (C * t) = y t + 1 := by
    rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  have hmult := mul_le_mul_of_nonneg_right hA (Real.exp_pos (C * t)).le
  rw [h2] at hmult
  linarith

end Work.Diff.STE
