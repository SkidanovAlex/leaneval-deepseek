/-
# The trace identity for the first difference at weight `12`

Let `f : ℍ → ℂ` be annihilated by `(T - I)²` (i.e. its first difference `fstDiff f` is
periodic of period one) and be an eigenfunction of the weight-`12` slash action of `S`
with eigenvalue `1`.  Writing `g = fstDiff f` this file proves the *trace identity*

  `g τ + τ^{-12} g (S • τ) + (τ+1)^{-12} g (S • (τ+1)) = 0`,

i.e. `g ∣[12] (1 + S + ST) = 0`.

The proof is a short explicit computation.  With `z = (τ : ℂ)`, `q = S•τ`, `r = T S τ`,
`v = T⁻¹ S τ` and `w = T S T τ` one uses:

* the `S`-relation at `τ` and at `τ+1`:
  `z^{-12} f (S•τ) = f τ`, `(z+1)^{-12} f (S•(τ+1)) = f (τ+1)`;
* the `S`-relation at `TSTτ`, whose image under `S` is `T^{-1}Sτ`, so that
  `f (T^{-1}Sτ) = (TSTτ)^{12} f (TSTτ)`;
* the second difference relation at `T^{-1}Sτ`, where the three points
  `T^{-1}Sτ, S•τ, T S τ` are consecutive: `f(T S τ) - 2 f(S•τ) + f(T^{-1}Sτ) = 0`.

Since `TSTτ = τ/(τ+1)` the two remaining terms cancel.  (This is the identity
`g ∣ (1 + S + ST) = 0` used in the rigidity argument of CKMRV, Section 8.)
-/
import Mathlib
import Submission.Work.Rigidity.Basic
import Submission.Work.Rigidity.Diff

namespace Work.Rigidity

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

noncomputable section

/-- The weight-`k` slash action of `S`: `(F ∣[k] S) τ = τ^{-k} F (S • τ)`. -/
lemma slash_S_apply (F : ℍ → ℂ) (k : ℤ) (τ : ℍ) :
    (F ∣[k] ModularGroup.S) τ = (τ : ℂ) ^ (-k) * F (ModularGroup.S • τ) := by
  rw [ModularForm.SL_slash_apply, ModularGroup.denom_S, mul_comm]

/-- `SlashEigen k 1 f`, spelled out at a point: `(σ : ℂ)^{-k} f (S • σ) = f σ`. -/
lemma slash_S_eigen_apply {f : ℍ → ℂ} {k : ℤ} (hS : SlashEigen k (1 : ℂ) f) (σ : ℍ) :
    (σ : ℂ) ^ (-k) * f (ModularGroup.S • σ) = f σ := by
  have h := hS σ
  rw [slash_S_apply, one_mul] at h
  exact h

/-- The arithmetic identity behind the cancellation of the two remaining terms:
`z^{-12} (z/(z+1))^{12} = (z+1)^{-12}`. -/
lemma zpow_neg12_mul_div (z : ℂ) (hz : z ≠ 0) :
    z ^ (-12 : ℤ) * (z / (z + 1)) ^ (12 : ℤ) = (z + 1) ^ (-12 : ℤ) := by
  rw [div_zpow, zpow_neg z 12, zpow_neg (z + 1) 12, div_eq_mul_inv]
  rw [inv_mul_cancel_left₀ (zpow_ne_zero 12 hz)]

/-- The point `TSTτ = τ/(τ+1)` (with `T = (1:ℝ) +ᵥ ·`) is characterised by
`(τ+1)·TSTτ = τ`, in the form needed below: its `S`-image is `T^{-1}Sτ`. -/
lemma S_smul_vadd_S_smul_vadd (τ : ℍ) :
    ModularGroup.S • ((1 : ℝ) +ᵥ (ModularGroup.S • ((1 : ℝ) +ᵥ τ)))
      = (-1 : ℝ) +ᵥ (ModularGroup.S • τ) := by
  have hz : (τ : ℂ) ≠ 0 := Work.Rigidity.coe_ne_zero τ
  have hz1 : (τ : ℂ) + 1 ≠ 0 := by
    intro h
    have him : ((τ : ℂ) + 1).im = 0 := by rw [h]; simp
    have : (τ : ℂ).im = 0 := by simpa using him
    exact τ.im_ne_zero (by rw [← UpperHalfPlane.coe_im]; exact this)
  rw [UpperHalfPlane.ext_iff]
  rw [Work.Rigidity.coe_S_smul, UpperHalfPlane.coe_vadd, Work.Rigidity.coe_S_smul,
      UpperHalfPlane.coe_vadd, UpperHalfPlane.coe_vadd, Work.Rigidity.coe_S_smul]
  push_cast
  have hsplit : 1 + -(1 + (τ : ℂ))⁻¹ = (τ : ℂ) / (1 + (τ : ℂ)) := by
    rw [add_comm (1 : ℂ) (τ : ℂ)]
    rw [eq_div_iff hz1]
    field_simp
    ring
  rw [hsplit]
  field_simp
  ring

theorem fstDiff_trace {f : ℍ → ℂ} (hT : Work.Rigidity.AnnT2 f)
    (hS : Work.Rigidity.SlashEigen 12 (1 : ℂ) f) :
    ∀ τ : ℍ, Work.Rigidity.fstDiff f τ
        + (τ : ℂ) ^ (-12 : ℤ) * Work.Rigidity.fstDiff f (ModularGroup.S • τ)
        + ((τ : ℂ) + 1) ^ (-12 : ℤ)
            * Work.Rigidity.fstDiff f (ModularGroup.S • ((1 : ℝ) +ᵥ τ)) = 0 := by
  intro τ
  set τ₁ : ℍ := (1 : ℝ) +ᵥ τ with hτ₁
  set q : ℍ := ModularGroup.S • τ with hq
  set r : ℍ := (1 : ℝ) +ᵥ q with hr
  set s : ℍ := ModularGroup.S • τ₁ with hs
  set w : ℍ := (1 : ℝ) +ᵥ s with hw
  set v : ℍ := (-1 : ℝ) +ᵥ q with hv
  set zc : ℂ := (τ : ℂ) ^ (-12 : ℤ) with hzc
  set zc₁ : ℂ := (τ₁ : ℂ) ^ (-12 : ℤ) with hzc₁
  have hz : (τ : ℂ) ≠ 0 := Work.Rigidity.coe_ne_zero τ
  have hz1 : (τ : ℂ) + 1 ≠ 0 := by
    intro h
    have him : ((τ : ℂ) + 1).im = 0 := by rw [h]; simp
    have : (τ : ℂ).im = 0 := by simpa using him
    exact τ.im_ne_zero (by rw [← UpperHalfPlane.coe_im]; exact this)
  have hτ₁c : (τ₁ : ℂ) = (τ : ℂ) + 1 := by
    rw [hτ₁, UpperHalfPlane.coe_vadd]; push_cast; ring
  have hcoef : ((τ : ℂ) + 1) ^ (-12 : ℤ) = zc₁ := by rw [hzc₁, hτ₁c]
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
  -- the `S`-relation at `TSTτ`: `f (T^{-1}Sτ) = (TSTτ)^{12} f (TSTτ)`
  have h3 : f v = (w : ℂ) ^ (12 : ℤ) * f w := by
    have hSw := slash_S_eigen_apply hS w
    rw [S_smul_vadd_S_smul_vadd] at hSw
    have h12 : (w : ℂ) ^ (12 : ℤ) * (w : ℂ) ^ (-12 : ℤ) = 1 := by
      rw [← zpow_add₀ hwnz]; norm_num
    calc f v = 1 * f v := (one_mul _).symm
      _ = ((w : ℂ) ^ (12 : ℤ) * (w : ℂ) ^ (-12 : ℤ)) * f v := by rw [h12]
      _ = (w : ℂ) ^ (12 : ℤ) * ((w : ℂ) ^ (-12 : ℤ) * f v) := by ring
      _ = (w : ℂ) ^ (12 : ℤ) * f w := by rw [hSw]
  -- the second difference relation at `T^{-1}Sτ`
  have hv1 : (1 : ℝ) +ᵥ v = q := by rw [hv, ← add_vadd]; norm_num
  have hv2 : (2 : ℝ) +ᵥ v = r := by rw [hv, hr, ← add_vadd]; norm_num
  have h4 : f r - 2 * f q + f v = 0 := by
    have h := congrFun hT v
    simp only [Work.Kernels.T2op, Pi.zero_apply] at h
    rw [hv1, hv2] at h
    exact h
  -- the arithmetic cancellation
  have h4' : f r - 2 * f q = - f v := by linear_combination h4
  have hnum : zc * (w : ℂ) ^ (12 : ℤ) = zc₁ := by
    have hwdiv : (w : ℂ) = (τ : ℂ) / ((τ : ℂ) + 1) := by
      rw [eq_div_iff hz1, mul_comm]
      exact hprod'
    rw [hzc, hzc₁, hwdiv, hτ₁c]
    exact zpow_neg12_mul_div (τ : ℂ) hz
  calc f τ₁ - f τ + zc * (f r - f q) + zc₁ * (f w - f s)
      = (zc₁ * f s - zc * f q) + zc * (f r - f q) + zc₁ * (f w - f s) := by rw [h1, h2]
    _ = zc * (f r - 2 * f q) + zc₁ * f w := by ring
    _ = zc * (- f v) + zc₁ * f w := by rw [h4']
    _ = zc * (-((w : ℂ) ^ (12 : ℤ) * f w)) + zc₁ * f w := by rw [h3]
    _ = 0 := by rw [← hnum]; ring

end

end Work.Rigidity
