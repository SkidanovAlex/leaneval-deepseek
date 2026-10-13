import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.R1G.GTest

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G

/-! ## Elementary bounds on the radial factor `gPhi z = z²e^{-z}`

`gPhi` vanishes to second order at `0`, is entire and decays exponentially, so on `[0,∞)` it is
bounded (`|gPhi| ≤ 2`) with bounded derivative (`|gPhi'| ≤ 4`).  The two estimates are proved from
`s + 1 ≤ e^s` and `1 + s + s²/2 ≤ e^s` (`Real.sum_le_exp_of_nonneg`). -/

/-- `s·e^{-s} ≤ 1` for every real `s`. -/
lemma mul_exp_neg_le_one (s : ℝ) : s * Real.exp (-s) ≤ 1 := by
  have hs : s ≤ Real.exp s := by linarith [Real.add_one_le_exp s]
  calc s * Real.exp (-s) ≤ Real.exp s * Real.exp (-s) :=
        mul_le_mul_of_nonneg_right hs (Real.exp_pos (-s)).le
    _ = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

/-- `s²·e^{-s} ≤ 2` for `s ≥ 0`. -/
lemma sq_mul_exp_neg_le_two {s : ℝ} (hs : 0 ≤ s) : s ^ 2 * Real.exp (-s) ≤ 2 := by
  have h3 : (1 : ℝ) + s + s ^ 2 / 2 ≤ Real.exp s := by
    have h := Real.sum_le_exp_of_nonneg hs 3
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
    norm_num at h
    linarith
  have h4 : s ^ 2 ≤ 2 * Real.exp s := by linarith
  calc s ^ 2 * Real.exp (-s) ≤ (2 * Real.exp s) * Real.exp (-s) :=
        mul_le_mul_of_nonneg_right h4 (Real.exp_pos (-s)).le
    _ = 2 * (Real.exp s * Real.exp (-s)) := by ring
    _ = 2 := by
        rw [show Real.exp s * Real.exp (-s) = 1 by
              rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]]
        ring

/-- `|z²e^{-z}| ≤ 2` for `z ≥ 0`. -/
lemma abs_gPhi_le_two {z : ℝ} (hz : 0 ≤ z) : |gPhi z| ≤ 2 := by
  unfold gPhi
  rw [abs_of_nonneg (mul_nonneg (sq_nonneg z) (Real.exp_pos (-z)).le)]
  exact sq_mul_exp_neg_le_two hz

/-- `|(2z - z²)e^{-z}| ≤ 4` for `z ≥ 0`. -/
lemma abs_gPhi1_le_four {z : ℝ} (hz : 0 ≤ z) : |gPhi1 z| ≤ 4 := by
  have h1 : z * Real.exp (-z) ≤ 1 := mul_exp_neg_le_one z
  have h2 : z ^ 2 * Real.exp (-z) ≤ 2 := sq_mul_exp_neg_le_two hz
  have hb : |2 * z - z ^ 2| ≤ 2 * z + z ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg z]
  unfold gPhi1
  rw [abs_mul, abs_of_pos (Real.exp_pos (-z))]
  calc |2 * z - z ^ 2| * Real.exp (-z)
      ≤ (2 * z + z ^ 2) * Real.exp (-z) :=
        mul_le_mul_of_nonneg_right hb (Real.exp_pos (-z)).le
    _ = 2 * (z * Real.exp (-z)) + z ^ 2 * Real.exp (-z) := by ring
    _ ≤ 2 * 1 + 2 := by linarith
    _ = 4 := by norm_num

/-- **Lipschitz bound for the radial factor**: on the halfline `z ≥ 0` we have
`|gPhi z - gPhi z'| ≤ 4|z - z'|` (mean value inequality with `|gPhi'| ≤ 4`). -/
lemma abs_gPhi_sub_le {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') :
    |gPhi z - gPhi z'| ≤ 4 * |z - z'| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (𝕜 := ℝ) (G := ℝ) (f := gPhi) (s := Set.Ici (0 : ℝ)) (C := 4) (x := z') (y := z)
    (fun x _ => (hasDerivAt_gPhi x).differentiableAt)
    (fun x hx => by
      rw [show deriv gPhi x = gPhi1 x from (hasDerivAt_gPhi x).deriv, Real.norm_eq_abs]
      exact abs_gPhi1_le_four hx)
    (convex_Ici 0) hz' hz
  rwa [Real.norm_eq_abs, Real.norm_eq_abs] at h

/-- **Hölder continuity in `z`** of the visible test perturbation `gTest ε z θ = ε·z²e^{-z}·sin(2θ)`,
uniformly in `θ ∈ Iθ`.  The bound is Lipschitz with constant `4|ε|`; for `|z - z'| ≥ 1` the sup
bound `|gPhi| ≤ 2` replaces it, and for `|z - z'| ≤ 1` we use `|z - z'| ≤ |z - z'|^β`. -/
theorem gTest_holder_z {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (ε : ℝ) :
    ∃ Lg : ℝ, 0 ≤ Lg ∧ ∀ z z' θ : ℝ, 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ →
      |gTest ε z θ - gTest ε z' θ| ≤ Lg * |z - z'| ^ β := by
  refine ⟨6 * |ε| + 1, by positivity, ?_⟩
  intro z z' θ hz hz' hθ
  have hpsi : |gPsi θ| ≤ 1 := by simpa [gPsi] using Real.abs_sin_le_one (2 * θ)
  have hLip : |gPhi z - gPhi z'| ≤ 4 * |z - z'| := abs_gPhi_sub_le hz hz'
  have hsup : |gPhi z - gPhi z'| ≤ 4 := by
    have h1 := abs_gPhi_le_two hz
    have h2 := abs_gPhi_le_two hz'
    have h3 : |gPhi z - gPhi z'| ≤ |gPhi z| + |gPhi z'| := by
      have := abs_add_le (gPhi z) (-(gPhi z'))
      simpa [sub_eq_add_neg] using this
    linarith
  have hEq : gTest ε z θ - gTest ε z' θ = (ε * gPsi θ) * (gPhi z - gPhi z') := by
    simp only [gTest_apply]
    ring
  have hLHS : |gTest ε z θ - gTest ε z' θ| ≤ |ε| * |gPhi z - gPhi z'| := by
    have hprod : (|ε| * |gPsi θ|) * |gPhi z - gPhi z'| ≤ |ε| * |gPhi z - gPhi z'| := by
      have h' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpsi (abs_nonneg ε))
        (abs_nonneg (gPhi z - gPhi z'))
      simpa using h'
    rw [hEq, abs_mul, abs_mul]
    exact hprod
  by_cases hA : |z - z'| ≤ 1
  · rcases eq_or_lt_of_le (abs_nonneg (z - z')) with h0 | h0
    · have hzz : z = z' := by
        have : z - z' = 0 := abs_eq_zero.mp h0.symm
        linarith
      subst hzz
      simp [Real.zero_rpow hβ.ne']
    · have hA1 : |z - z'| ^ (1 : ℝ) ≤ |z - z'| ^ β :=
        Real.rpow_le_rpow_of_exponent_ge h0 hA hβ1
      rw [Real.rpow_one] at hA1
      have h4 : |gTest ε z θ - gTest ε z' θ| ≤ 4 * |ε| * |z - z'| := by
        calc |gTest ε z θ - gTest ε z' θ| ≤ |ε| * |gPhi z - gPhi z'| := hLHS
          _ ≤ |ε| * (4 * |z - z'|) := mul_le_mul_of_nonneg_left hLip (abs_nonneg ε)
          _ = 4 * |ε| * |z - z'| := by ring
      have h5 : 4 * |ε| * |z - z'| ≤ 4 * |ε| * |z - z'| ^ β :=
        mul_le_mul_of_nonneg_left hA1 (by positivity)
      have h6 : 4 * |ε| * |z - z'| ^ β ≤ (6 * |ε| + 1) * |z - z'| ^ β := by
        have hb : 4 * |ε| ≤ 6 * |ε| + 1 := by have := abs_nonneg ε; linarith
        exact mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg (abs_nonneg _) _)
      linarith
  · have hA1 : 1 ≤ |z - z'| := by
      have := abs_nonneg (z - z')
      push Not at hA
      linarith
    have hrpow : 1 ≤ |z - z'| ^ β := Real.one_le_rpow hA1 hβ.le
    have h4 : |gTest ε z θ - gTest ε z' θ| ≤ 4 * |ε| := by
      calc |gTest ε z θ - gTest ε z' θ| ≤ |ε| * |gPhi z - gPhi z'| := hLHS
        _ ≤ |ε| * 4 := mul_le_mul_of_nonneg_left hsup (abs_nonneg ε)
        _ = 4 * |ε| := by ring
    have h5 : 4 * |ε| ≤ 6 * |ε| + 1 := by have := abs_nonneg ε; linarith
    have h6 : 6 * |ε| + 1 ≤ (6 * |ε| + 1) * |z - z'| ^ β := by
      calc 6 * |ε| + 1 = (6 * |ε| + 1) * 1 := by ring
        _ ≤ (6 * |ε| + 1) * |z - z'| ^ β :=
            mul_le_mul_of_nonneg_left hrpow (by positivity)
    linarith

end Work.R1G
