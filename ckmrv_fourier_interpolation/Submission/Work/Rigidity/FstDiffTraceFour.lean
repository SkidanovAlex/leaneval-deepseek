/-
# The trace identity for the first difference at weight `4`

This is the weight-`4` companion of `Work.Rigidity.fstDiff_trace`: for `f` annihilated by
`(T - I)²` and an eigenfunction of the weight-`4` slash action of `S` with eigenvalue `1`,
the first difference `g = fstDiff f` satisfies the trace identity

  `g τ + τ^{-4} g (S • τ) + (τ+1)^{-4} g (S • (τ+1)) = 0`,

i.e. `g ∣[4] (1 + S + ST) = 0`.

The argument is exactly the one used for weight `12` and does not depend on the weight:
with `z = (τ : ℂ)`, `q = S•τ`, `r = T S τ`, `v = T⁻¹ S τ` and `w = T S T τ` one uses

* the `S`-relation at `τ` and at `τ+1`:
  `z^{-k} f (S•τ) = f τ`, `(z+1)^{-k} f (S•(τ+1)) = f (τ+1)`;
* the `S`-relation at `TSTτ`, whose image under `S` is `T^{-1}Sτ`, so that
  `f (T^{-1}Sτ) = (TSTτ)^{k} f (TSTτ)`;
* the second difference relation at `T^{-1}Sτ`, where the three points
  `T^{-1}Sτ, S•τ, T S τ` are consecutive: `f(T S τ) - 2 f(S•τ) + f(T^{-1}Sτ) = 0`.

Since `TSTτ = τ/(τ+1)` the two remaining terms cancel by the identity
`z^{-k} (z/(z+1))^{k} = (z+1)^{-k}`.
-/
import Mathlib
import Submission.Work.Rigidity.Diff
import Submission.Work.Rigidity.fstDiff_trace

namespace Work.Rigidity

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

noncomputable section

/-- The arithmetic identity behind the cancellation of the two remaining terms, for an
arbitrary weight `k`: `z^{-k} (z/(z+1))^{k} = (z+1)^{-k}`. -/
lemma zpow_neg_mul_div (k : ℤ) (z : ℂ) (hz : z ≠ 0) :
    z ^ (-k) * (z / (z + 1)) ^ k = (z + 1) ^ (-k) := by
  rw [div_zpow, zpow_neg z k, zpow_neg (z + 1) k, div_eq_mul_inv]
  rw [inv_mul_cancel_left₀ (zpow_ne_zero k hz)]

theorem FstDiffTraceFour {f : UpperHalfPlane → ℂ} (hT2 : Work.Rigidity.AnnT2 f)
    (hS : Work.Rigidity.SlashEigen 4 (1 : ℂ) f) :
    ∀ τ : UpperHalfPlane, Work.Rigidity.fstDiff f τ
      + (τ : ℂ) ^ (-4 : ℤ) * Work.Rigidity.fstDiff f (ModularGroup.S • τ)
      + ((τ : ℂ) + 1) ^ (-4 : ℤ) * Work.Rigidity.fstDiff f (ModularGroup.S • ((1 : ℝ) +ᵥ τ)) = 0 := by
  intro τ
  set τ₁ : ℍ := (1 : ℝ) +ᵥ τ with hτ₁
  set q : ℍ := ModularGroup.S • τ with hq
  set r : ℍ := (1 : ℝ) +ᵥ q with hr
  set s : ℍ := ModularGroup.S • τ₁ with hs
  set w : ℍ := (1 : ℝ) +ᵥ s with hw
  set v : ℍ := (-1 : ℝ) +ᵥ q with hv
  set zc : ℂ := (τ : ℂ) ^ (-4 : ℤ) with hzc
  set zc₁ : ℂ := (τ₁ : ℂ) ^ (-4 : ℤ) with hzc₁
  have hz : (τ : ℂ) ≠ 0 := Work.Rigidity.coe_ne_zero τ
  have hz1 : (τ : ℂ) + 1 ≠ 0 := by
    intro h
    have him : ((τ : ℂ) + 1).im = 0 := by rw [h]; simp
    have : (τ : ℂ).im = 0 := by simpa using him
    exact τ.im_ne_zero (by rw [← UpperHalfPlane.coe_im]; exact this)
  have hτ₁c : (τ₁ : ℂ) = (τ : ℂ) + 1 := by
    rw [hτ₁, UpperHalfPlane.coe_vadd]; push_cast; ring
  have hcoef : ((τ : ℂ) + 1) ^ (-4 : ℤ) = zc₁ := by rw [hzc₁, hτ₁c]
  rw [hcoef]
  rw [Work.Rigidity.fstDiff_apply, Work.Rigidity.fstDiff_apply, Work.Rigidity.fstDiff_apply]
  rw [← hτ₁, ← hr, ← hw]
  -- the `S`-relation at `τ` and at `τ₁`
  have h1 : zc * f q = f τ := by rw [hzc, hq]; exact slash_S_eigen_apply hS τ
  have h2 : zc₁ * f s = f τ₁ := by rw [hzc₁, hs]; exact slash_S_eigen_apply hS τ₁
  -- `(τ+1) • (TSTτ) = τ`
  have hprod : (τ₁ : ℂ) * (w : ℂ) = (τ : ℂ) := by
    have hwc : (w : ℂ) = 1 - ((τ : ℂ) + 1)⁻¹ := by
      rw [hw, UpperHalfPlane.coe_vadd, hs, Work.Rigidity.coe_S_smul, hτ₁c]
      push_cast
      ring
    rw [hwc, hτ₁c]
    field_simp
    ring
  have hprod' : ((τ : ℂ) + 1) * (w : ℂ) = (τ : ℂ) := by rw [← hτ₁c]; exact hprod
  have hwnz : (w : ℂ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hprod
    exact hz hprod.symm
  -- the `S`-relation at `TSTτ`: `f (T^{-1}Sτ) = (TSTτ)^{4} f (TSTτ)`
  have h3 : f v = (w : ℂ) ^ (4 : ℤ) * f w := by
    have hSw := slash_S_eigen_apply hS w
    rw [S_smul_vadd_S_smul_vadd] at hSw
    have h12 : (w : ℂ) ^ (4 : ℤ) * (w : ℂ) ^ (-4 : ℤ) = 1 := by
      rw [← zpow_add₀ hwnz]; norm_num
    calc f v = 1 * f v := (one_mul _).symm
      _ = ((w : ℂ) ^ (4 : ℤ) * (w : ℂ) ^ (-4 : ℤ)) * f v := by rw [h12]
      _ = (w : ℂ) ^ (4 : ℤ) * ((w : ℂ) ^ (-4 : ℤ) * f v) := by ring
      _ = (w : ℂ) ^ (4 : ℤ) * f w := by rw [hSw]
  -- the second difference relation at `T^{-1}Sτ`
  have hv1 : (1 : ℝ) +ᵥ v = q := by rw [hv, ← add_vadd]; norm_num
  have hv2 : (2 : ℝ) +ᵥ v = r := by rw [hv, hr, ← add_vadd]; norm_num
  have h4 : f r - 2 * f q + f v = 0 := by
    have h := congrFun hT2 v
    simp only [Work.Kernels.T2op, Pi.zero_apply] at h
    rw [hv1, hv2] at h
    exact h
  -- the arithmetic cancellation
  have h4' : f r - 2 * f q = - f v := by linear_combination h4
  have hnum : zc * (w : ℂ) ^ (4 : ℤ) = zc₁ := by
    have hwdiv : (w : ℂ) = (τ : ℂ) / ((τ : ℂ) + 1) := by
      rw [eq_div_iff hz1, mul_comm]
      exact hprod'
    rw [hzc, hzc₁, hwdiv, hτ₁c]
    exact zpow_neg_mul_div 4 (τ : ℂ) hz
  calc f τ₁ - f τ + zc * (f r - f q) + zc₁ * (f w - f s)
      = (zc₁ * f s - zc * f q) + zc * (f r - f q) + zc₁ * (f w - f s) := by rw [h1, h2]
    _ = zc * (f r - 2 * f q) + zc₁ * f w := by ring
    _ = zc * (- f v) + zc₁ * f w := by rw [h4']
    _ = zc * (-((w : ℂ) ^ (4 : ℤ) * f w)) + zc₁ * f w := by rw [h3]
    _ = 0 := by rw [← hnum]; ring

end

end Work.Rigidity
