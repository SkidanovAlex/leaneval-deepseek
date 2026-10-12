import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseC3QAll.errA_bounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseC3QAll.errA_le` — the arithmetic leg `N1` (`ErrALe`)

`ErrALe b₀ hb₀ C₁ C₂₃ C₄` is FS's "adding the estimates" arithmetic with
*absolute* constants: for **every** real `C₁, C₂₃, C₄` there is a threshold
`t₀ > 0` such that at every parameter point `FSParamsView E` with `t = μa³ ≤ t₀`
and `b ≥ b₀`,

  `C₁·e1A E + C₂₃·e23A E + C₄·e4A E ≤ controlErrA E`.

The content is the monomial arithmetic of `errA_pre`/`errA_bounds`: with
`X = fsXp t 1`, `controlErrA E = E0·X^{325/2}` while

* `e1A E ≤ E0·X^{365/2}·(3 + 1/b₀)`,
* `e23A E ≤ E0·X^{365/2}`,
* `e4A E ≤ E0·X^{1435/8}·((27/4)√2 + 1/b₀)`,

and `X^{365/2} = X^{325/2}·X^{20}`, `X^{1435/8} = X^{325/2}·X^{135/8}`.  Since
`135/8 < 20`, the whole bracket is `≤ M·A·X^{135/8}·controlErrA` with
`M = max(1,|C₁|,|C₂₃|,|C₄|)` and an explicit constant `A`, and `M·A·X^{135/8} ≤ 1`
for `X` small — i.e. for `t ≤ t₀ = X₀^{323}` (`exists_small_rpow`).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseC3QAll

open Work.BoseB7
open Work.BoseBox

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]

theorem errA_le (b₀ : ℝ) (hb₀ : 0 < b₀) (C₁ C₂₃ C₄ : ℝ) :
    Work.BoseC3QAll.ErrALe b₀ hb₀ C₁ C₂₃ C₄ := by
  -- the constants of the final estimate
  let M : ℝ := max 1 (max |C₁| (max |C₂₃| |C₄|))
  have hM1 : (1 : ℝ) ≤ M := le_max_left _ _
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM1
  have hMabs1 : |C₁| ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
  have hMabs23 : |C₂₃| ≤ M :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hMabs4 : |C₄| ≤ M :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  have hA0 : (0 : ℝ) ≤ M * ((3 + 1 / b₀) + 1 + (27 / 4 * Real.sqrt 2 + 1 / b₀)) :=
    mul_nonneg hM0.le (by positivity)
  -- the threshold
  obtain ⟨X₀, hX₀pos, hX₀le1, hX₀K⟩ :=
    exists_small_rpow (e := 135 / 8) (by norm_num) (K := M * ((3 + 1 / b₀) + 1 +
      (27 / 4 * Real.sqrt 2 + 1 / b₀))) hA0
  refine ⟨X₀ ^ (323 : ℝ), Real.rpow_pos_of_pos hX₀pos 323, ?_⟩
  intro Mode instAC instF E hv ht hb
  have h0 : 0 < hv.t := hv.t_pos
  have h1t : hv.t ≤ 1 := hv.t_le_one
  have hEb : 0 < E.b := lt_of_lt_of_le hb₀ hb
  -- `X = fsXp hv.t 1 ≤ X₀`
  have hX : fsXp hv.t 1 ≤ X₀ := fsXp_one_le_of_le h0 hX₀pos.le ht
  have hXc0 : 0 ≤ X₀ ^ (135 / 8 : ℝ) := Real.rpow_nonneg hX₀pos.le _
  have hY20 : fsXp hv.t 20 ≤ X₀ ^ (135 / 8 : ℝ) :=
    le_trans (fsXp_le_fsXp h0 h1t (by norm_num)) (fsXp_le_rpow h0.le hX (by norm_num))
  have hY135 : fsXp hv.t (135 / 8) ≤ X₀ ^ (135 / 8 : ℝ) :=
    fsXp_le_rpow h0.le hX (by norm_num)
  have hP0 : 0 ≤ E0 E * fsXp hv.t (325 / 2) := mul_nonneg (errA_E0_nonneg E hv) (fsXp_pos h0).le
  have hQ0 : 0 ≤ (E0 E * fsXp hv.t (325 / 2)) * X₀ ^ (135 / 8 : ℝ) := mul_nonneg hP0 hXc0
  -- positivity of the three brackets
  have hn1 : 0 ≤ e1A E := e1A_nonneg E hv hEb
  have hn23 : 0 ≤ e23A E := e23A_nonneg E hv
  have hn4 : 0 ≤ e4A E := e4A_nonneg E hv hEb
  -- the three bracket bounds
  have he1 := e1A_le b₀ hb₀ E hv hb
  have he23 := e23A_le E hv
  have he4 := e4A_le b₀ hb₀ E hv hb
  have hE1 : e1A E ≤ (3 + 1 / b₀) * ((E0 E * fsXp hv.t (325 / 2)) * X₀ ^ (135 / 8 : ℝ)) := by
    have hstep : fsXp hv.t (325 / 2) * fsXp hv.t 20 ≤ fsXp hv.t (325 / 2) * X₀ ^ (135 / 8 : ℝ) :=
      mul_le_mul_of_nonneg_left hY20 (fsXp_pos h0).le
    refine le_trans he1 ?_
    rw [show fsXp hv.t (365 / 2) = fsXp hv.t (325 / 2) * fsXp hv.t 20 by
      rw [fsXp_mul h0]; norm_num]
    calc E0 E * (fsXp hv.t (325 / 2) * fsXp hv.t 20) * (3 + 1 / b₀)
        ≤ E0 E * (fsXp hv.t (325 / 2) * X₀ ^ (135 / 8 : ℝ)) * (3 + 1 / b₀) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstep (errA_E0_nonneg E hv))
            (by positivity)
      _ = (3 + 1 / b₀) * ((E0 E * fsXp hv.t (325 / 2)) * X₀ ^ (135 / 8 : ℝ)) := by ring
  have hE23 : e23A E ≤ (E0 E * fsXp hv.t (325 / 2)) * X₀ ^ (135 / 8 : ℝ) := by
    have hstep : fsXp hv.t (325 / 2) * fsXp hv.t 20 ≤ fsXp hv.t (325 / 2) * X₀ ^ (135 / 8 : ℝ) :=
      mul_le_mul_of_nonneg_left hY20 (fsXp_pos h0).le
    refine le_trans he23 ?_
    rw [show fsXp hv.t (365 / 2) = fsXp hv.t (325 / 2) * fsXp hv.t 20 by
      rw [fsXp_mul h0]; norm_num]
    calc E0 E * (fsXp hv.t (325 / 2) * fsXp hv.t 20)
        ≤ E0 E * (fsXp hv.t (325 / 2) * X₀ ^ (135 / 8 : ℝ)) :=
          mul_le_mul_of_nonneg_left hstep (errA_E0_nonneg E hv)
      _ = (E0 E * fsXp hv.t (325 / 2)) * X₀ ^ (135 / 8 : ℝ) := by ring
  have hE4 : e4A E ≤ (27 / 4 * Real.sqrt 2 + 1 / b₀) *
      ((E0 E * fsXp hv.t (325 / 2)) * X₀ ^ (135 / 8 : ℝ)) := by
    have hstep : fsXp hv.t (325 / 2) * fsXp hv.t (135 / 8) ≤
        fsXp hv.t (325 / 2) * X₀ ^ (135 / 8 : ℝ) :=
      mul_le_mul_of_nonneg_left hY135 (fsXp_pos h0).le
    refine le_trans he4 ?_
    rw [show fsXp hv.t (1435 / 8) = fsXp hv.t (325 / 2) * fsXp hv.t (135 / 8) by
      rw [fsXp_mul h0]; norm_num]
    calc E0 E * (fsXp hv.t (325 / 2) * fsXp hv.t (135 / 8)) * (27 / 4 * Real.sqrt 2 + 1 / b₀)
        ≤ E0 E * (fsXp hv.t (325 / 2) * X₀ ^ (135 / 8 : ℝ)) * (27 / 4 * Real.sqrt 2 + 1 / b₀) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hstep (errA_E0_nonneg E hv)) (by positivity)
      _ = (27 / 4 * Real.sqrt 2 + 1 / b₀) *
            ((E0 E * fsXp hv.t (325 / 2)) * X₀ ^ (135 / 8 : ℝ)) := by ring
  -- the sum
  have hsum1 : C₁ * e1A E + C₂₃ * e23A E + C₄ * e4A E ≤
      (|C₁| * (3 + 1 / b₀) + |C₂₃| + |C₄| * (27 / 4 * Real.sqrt 2 + 1 / b₀)) *
        ((E0 E * fsXp hv.t (325 / 2)) * X₀ ^ (135 / 8 : ℝ)) := by
    have h1 : C₁ * e1A E ≤ |C₁| * ((3 + 1 / b₀) *
        ((E0 E * fsXp hv.t (325 / 2)) * X₀ ^ (135 / 8 : ℝ))) :=
      le_trans (mul_le_mul_of_nonneg_right (le_abs_self C₁) hn1)
        (mul_le_mul_of_nonneg_left hE1 (abs_nonneg C₁))
    have h23 : C₂₃ * e23A E ≤ |C₂₃| *
        ((E0 E * fsXp hv.t (325 / 2)) * X₀ ^ (135 / 8 : ℝ)) :=
      le_trans (mul_le_mul_of_nonneg_right (le_abs_self C₂₃) hn23)
        (mul_le_mul_of_nonneg_left hE23 (abs_nonneg C₂₃))
    have h4 : C₄ * e4A E ≤ |C₄| * ((27 / 4 * Real.sqrt 2 + 1 / b₀) *
        ((E0 E * fsXp hv.t (325 / 2)) * X₀ ^ (135 / 8 : ℝ))) :=
      le_trans (mul_le_mul_of_nonneg_right (le_abs_self C₄) hn4)
        (mul_le_mul_of_nonneg_left hE4 (abs_nonneg C₄))
    calc C₁ * e1A E + C₂₃ * e23A E + C₄ * e4A E
        ≤ |C₁| * ((3 + 1 / b₀) * ((E0 E * fsXp hv.t (325 / 2)) * X₀ ^ (135 / 8 : ℝ))) +
          |C₂₃| * ((E0 E * fsXp hv.t (325 / 2)) * X₀ ^ (135 / 8 : ℝ)) +
          |C₄| * ((27 / 4 * Real.sqrt 2 + 1 / b₀) *
            ((E0 E * fsXp hv.t (325 / 2)) * X₀ ^ (135 / 8 : ℝ))) := by linarith [h1, h23, h4]
      _ = (|C₁| * (3 + 1 / b₀) + |C₂₃| + |C₄| * (27 / 4 * Real.sqrt 2 + 1 / b₀)) *
            ((E0 E * fsXp hv.t (325 / 2)) * X₀ ^ (135 / 8 : ℝ)) := by ring
  -- the constant comparison
  have hBIG : |C₁| * (3 + 1 / b₀) + |C₂₃| + |C₄| * (27 / 4 * Real.sqrt 2 + 1 / b₀) ≤
      M * ((3 + 1 / b₀) + 1 + (27 / 4 * Real.sqrt 2 + 1 / b₀)) := by
    have h1 : |C₁| * (3 + 1 / b₀) ≤ M * (3 + 1 / b₀) :=
      mul_le_mul_of_nonneg_right hMabs1 (by positivity)
    have h2 : |C₂₃| ≤ M * 1 := by rw [mul_one]; exact hMabs23
    have h3 : |C₄| * (27 / 4 * Real.sqrt 2 + 1 / b₀) ≤ M * (27 / 4 * Real.sqrt 2 + 1 / b₀) :=
      mul_le_mul_of_nonneg_right hMabs4 (by positivity)
    calc |C₁| * (3 + 1 / b₀) + |C₂₃| + |C₄| * (27 / 4 * Real.sqrt 2 + 1 / b₀)
        ≤ M * (3 + 1 / b₀) + M * 1 + M * (27 / 4 * Real.sqrt 2 + 1 / b₀) := by linarith [h1, h2, h3]
      _ = M * ((3 + 1 / b₀) + 1 + (27 / 4 * Real.sqrt 2 + 1 / b₀)) := by ring
  have hstep1 : (|C₁| * (3 + 1 / b₀) + |C₂₃| + |C₄| * (27 / 4 * Real.sqrt 2 + 1 / b₀)) *
        ((E0 E * fsXp hv.t (325 / 2)) * X₀ ^ (135 / 8 : ℝ)) ≤
      (M * ((3 + 1 / b₀) + 1 + (27 / 4 * Real.sqrt 2 + 1 / b₀))) *
        ((E0 E * fsXp hv.t (325 / 2)) * X₀ ^ (135 / 8 : ℝ)) :=
    mul_le_mul_of_nonneg_right hBIG hQ0
  have hstep2 : (M * ((3 + 1 / b₀) + 1 + (27 / 4 * Real.sqrt 2 + 1 / b₀))) *
        ((E0 E * fsXp hv.t (325 / 2)) * X₀ ^ (135 / 8 : ℝ)) ≤ E0 E * fsXp hv.t (325 / 2) := by
    have h := mul_le_mul_of_nonneg_right hX₀K hP0
    calc (M * ((3 + 1 / b₀) + 1 + (27 / 4 * Real.sqrt 2 + 1 / b₀))) *
          ((E0 E * fsXp hv.t (325 / 2)) * X₀ ^ (135 / 8 : ℝ))
        = ((M * ((3 + 1 / b₀) + 1 + (27 / 4 * Real.sqrt 2 + 1 / b₀))) * X₀ ^ (135 / 8 : ℝ)) *
            (E0 E * fsXp hv.t (325 / 2)) := by ring
      _ ≤ 1 * (E0 E * fsXp hv.t (325 / 2)) := h
      _ = E0 E * fsXp hv.t (325 / 2) := one_mul _
  rw [errA_controlErr E hv]
  exact le_trans hsum1 (le_trans hstep1 hstep2)

end Work.BoseC3QAll
