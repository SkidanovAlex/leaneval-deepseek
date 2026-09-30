import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.discretise
import Submission.Work.BMF.wgu_nonneg_uncond
import Submission.Work.BMF.block_sum_integral_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Integrating the block decomposition of the local Gowers norm

Given the pointwise block bound
`‖g‖_{u^{k+1}[x,x+H]} ≤ (H'/H) Σ_{j<m} ‖g‖_{u^{k+1}[x+jH', x+jH'+H']} + (m + H' + 2)/H`
(MRTTZ's subdivision step, proved in `wgun_block_sum`), this file integrates it over
`x ∈ [X, 2X]`.  The block integrals are compared with the integral of the short-scale norm over
`[X, 3X]`: the shifted interval `[X + jH', 2X + jH']` lies inside `[X, 3X]` as soon as
`jH' ≤ X`, which follows from `m H' ≤ H + H'` and `H ≤ X`.

The result is
`∫_X^{2X} ‖g‖_{u^{k+1}[x,x+H]} ≤ (m H'/H) ∫_X^{3X} ‖g‖_{u^{k+1}[x,x+H']} + X (m + H' + 2)/H`.
-/

namespace Work.BMF

open MeasureTheory intervalIntegral
open BoundedMultiplicativeFunctions

theorem wgun_integral_block2 (k : ℕ) (g : ℤ → ℂ) (X H H' : ℝ) (m : ℕ)
    (hX : 0 < X) (hH : 0 < H) (hH' : 0 < H') (hHX : H ≤ X)
    (hm₂ : (m : ℝ) * H' ≤ H + H')
    (hmeasH : Measurable (fun x : ℝ => BoundedMultiplicativeFunctions.weakGowersUniformityNorm k x H g))
    (hmeasH' : Measurable (fun x : ℝ => BoundedMultiplicativeFunctions.weakGowersUniformityNorm k x H' g))
    (hbddH : ∀ x : ℝ, BoundedMultiplicativeFunctions.weakGowersUniformityNorm k x H g ≤ (H + 1) / H)
    (hbddH' : ∀ x : ℝ, BoundedMultiplicativeFunctions.weakGowersUniformityNorm k x H' g ≤ (H' + 1) / H')
    (hpt : ∀ x : ℝ, BoundedMultiplicativeFunctions.weakGowersUniformityNorm k x H g ≤
      (H' / H) * ∑ j ∈ Finset.range m,
        BoundedMultiplicativeFunctions.weakGowersUniformityNorm k (x + (j : ℝ) * H') H' g
      + ((m : ℝ) + H' + 2) / H) :
    (∫ x in X..(2 * X), BoundedMultiplicativeFunctions.weakGowersUniformityNorm k x H g)
      ≤ (((m : ℝ) * H' / H)
          * (∫ y in X..(3 * X), BoundedMultiplicativeFunctions.weakGowersUniformityNorm k y H' g))
        + X * (((m : ℝ) + H' + 2) / H) := by
  set F : ℝ → ℝ := fun x => BoundedMultiplicativeFunctions.weakGowersUniformityNorm k x H g with hF
  set G : ℝ → ℝ := fun y => BoundedMultiplicativeFunctions.weakGowersUniformityNorm k y H' g with hG
  set S : ℝ → ℝ := fun x => ∑ j ∈ Finset.range m, G (x + (j : ℝ) * H') with hS
  have hFmeas : Measurable F := by simpa only [hF] using hmeasH
  have hGmeas : Measurable G := by simpa only [hG] using hmeasH'
  have hFbdd : ∀ x, F x ≤ (H + 1) / H := fun x => by simpa only [hF] using hbddH x
  have hGbdd : ∀ x, G x ≤ (H' + 1) / H' := fun x => by simpa only [hG] using hbddH' x
  have hFnn : ∀ x, 0 ≤ F x := fun x => wgu_nonneg_uncond k g x H hH
  have hGnn : ∀ x, 0 ≤ G x := fun x => wgu_nonneg_uncond k g x H' hH'
  have hpt' : ∀ x, F x ≤ (H' / H) * S x + ((m : ℝ) + H' + 2) / H :=
    fun x => by simpa only [hF, hG, hS] using hpt x
  have hFnorm : ∀ x, ‖F x‖ ≤ (H + 1) / H := fun x => by
    rw [Real.norm_of_nonneg (hFnn x)]; exact hFbdd x
  have hGnorm : ∀ x, ‖G x‖ ≤ (H' + 1) / H' := fun x => by
    rw [Real.norm_of_nonneg (hGnn x)]; exact hGbdd x
  have hSmeas : Measurable S := by
    rw [hS]
    exact Finset.measurable_sum _ (fun j _ => hGmeas.comp (measurable_id.add measurable_const))
  have hSnn : ∀ x, 0 ≤ S x := fun x => Finset.sum_nonneg (fun j _ => hGnn _)
  have hSnorm : ∀ x, ‖S x‖ ≤ (m : ℝ) * ((H' + 1) / H') := by
    intro x
    rw [Real.norm_of_nonneg (hSnn x)]
    calc S x ≤ ∑ j ∈ Finset.range m, (H' + 1) / H' := Finset.sum_le_sum (fun j _ => hGbdd _)
      _ = (m : ℝ) * ((H' + 1) / H') := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hRHSbdd : ∀ x, ‖(H' / H) * S x + ((m : ℝ) + H' + 2) / H‖
      ≤ (H' / H) * ((m : ℝ) * ((H' + 1) / H')) + ((m : ℝ) + H' + 2) / H := by
    intro x
    have hc : 0 ≤ ((m : ℝ) + H' + 2) / H := by positivity
    have hH'd : 0 ≤ H' / H := by positivity
    calc ‖(H' / H) * S x + ((m : ℝ) + H' + 2) / H‖
        ≤ ‖(H' / H) * S x‖ + ‖((m : ℝ) + H' + 2) / H‖ := norm_add_le _ _
      _ = (H' / H) * ‖S x‖ + ((m : ℝ) + H' + 2) / H := by
          rw [norm_mul, Real.norm_of_nonneg hH'd, Real.norm_of_nonneg hc]
      _ ≤ (H' / H) * ((m : ℝ) * ((H' + 1) / H')) + ((m : ℝ) + H' + 2) / H := by
          have := mul_le_mul_of_nonneg_left (hSnorm x) hH'd
          linarith
  have hFint : IntervalIntegrable F volume X (2 * X) :=
    intervalIntegrable_of_measurable_bound hFmeas hFnorm X (2 * X)
  have hSint : IntervalIntegrable S volume X (2 * X) :=
    intervalIntegrable_of_measurable_bound hSmeas hSnorm X (2 * X)
  have hRHSint : IntervalIntegrable (fun x => (H' / H) * S x + ((m : ℝ) + H' + 2) / H)
      volume X (2 * X) :=
    intervalIntegrable_of_measurable_bound (by measurability) hRHSbdd X (2 * X)
  -- step 1: integrate the pointwise bound
  have hstep1 : ∫ x in X..(2 * X), F x
      ≤ ∫ x in X..(2 * X), ((H' / H) * S x + ((m : ℝ) + H' + 2) / H) :=
    intervalIntegral.integral_mono_on (by linarith) hFint hRHSint (fun x _ => hpt' x)
  -- step 2: evaluate the integral of the right-hand side
  have hstep2 : ∫ x in X..(2 * X), ((H' / H) * S x + ((m : ℝ) + H' + 2) / H)
      = (H' / H) * (∫ x in X..(2 * X), S x) + X * (((m : ℝ) + H' + 2) / H) := by
    rw [intervalIntegral.integral_add (hSint.const_mul _) intervalIntegrable_const,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  -- step 3: bound the block sum integral
  have hjX_le : ∀ j ∈ Finset.range m, (j : ℝ) * H' ≤ X := by
    intro j hj
    have hjlt : j < m := Finset.mem_range.mp hj
    have hjm : (j : ℝ) + 1 ≤ (m : ℝ) := by
      have : j + 1 ≤ m := by omega
      exact_mod_cast this
    have h1 : ((m : ℝ) - 1) * H' ≤ H := by linarith
    calc (j : ℝ) * H' ≤ ((m : ℝ) - 1) * H' :=
          mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hH')
      _ ≤ H := h1
      _ ≤ X := hHX
  have hstep3 : ∫ x in X..(2 * X), S x ≤ (m : ℝ) * ∫ y in X..(3 * X), G y :=
    block_sum_integral_le G X H' m ((H' + 1) / H') hX hH' hGmeas hGnn hGbdd hjX_le
  -- assembly
  have hmain : ∫ x in X..(2 * X), F x
      ≤ ((m : ℝ) * H' / H) * (∫ y in X..(3 * X), G y) + X * (((m : ℝ) + H' + 2) / H) := by
    calc ∫ x in X..(2 * X), F x
        ≤ ∫ x in X..(2 * X), ((H' / H) * S x + ((m : ℝ) + H' + 2) / H) := hstep1
      _ = (H' / H) * (∫ x in X..(2 * X), S x) + X * (((m : ℝ) + H' + 2) / H) := hstep2
      _ ≤ (H' / H) * ((m : ℝ) * ∫ y in X..(3 * X), G y) + X * (((m : ℝ) + H' + 2) / H) := by
          have hH'd : 0 ≤ H' / H := by positivity
          have := mul_le_mul_of_nonneg_left hstep3 hH'd
          linarith
      _ = ((m : ℝ) * H' / H) * (∫ y in X..(3 * X), G y) + X * (((m : ℝ) + H' + 2) / H) := by
          ring
  simpa only [hF, hG] using hmain

end Work.BMF
