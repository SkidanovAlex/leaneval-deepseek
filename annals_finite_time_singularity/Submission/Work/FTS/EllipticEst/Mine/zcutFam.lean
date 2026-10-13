/-
# `Mine.zcutFam` — a smooth cut-off family with uniform weighted derivative bounds

We produce, for every `n : ℕ`, a smooth function `χ n : ℝ → ℝ` with

* `χ n z = 0` for `z ≤ 1/(n+1)`,
* `χ n z = 1` for `2/(n+1) ≤ z ≤ n+1`,
* `χ n z = 0` for `2(n+1) ≤ z`,
* `0 ≤ χ n z ≤ 1`,
* `|z χ n'(z)| ≤ C₁` and `|z (z χ n')'(z)| ≤ C₂` with constants `C₁, C₂` *independent of `n`*,
* `χ n z → 1` for every fixed `z > 0`,

the construction and elementary properties being in
`Submission/Work/FTS/EllipticEst/Mine/zcutFamDefs.lean`.

The cut-off is the product of two rescalings of one fixed smooth step
`Ψ t = Real.smoothTransition (t - 1)`: with `A = n+1`, `B = A⁻¹` and `Ψ` as above,

  `χ n z = Ψ (A z) * (1 - Ψ (z B))`.

Writing `k1 t = t Ψ'(t)`, `k2 t = t k1'(t)` and `u = A z`, `v = z B`, the two key identities are

  `z χ_n'(z) = k1 u (1 - Ψ v) - Ψ u k1 v`,
  `z (z χ_n')'(z) = k2 u (1 - Ψ v) - 2 (k1 u)(k1 v) - Ψ u k2 v`,

so that the uniform bounds follow from the uniform bounds on `k1` and `k2` (the step `Ψ'` is
supported in `[1,2]`).  All the heavy algebraic work is in the two identity lemmas; the rest is
elementary.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Mine.zcutFamDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Topology
open Filter

namespace Work.FTS.EllipticEst.Mine

/-! ## Two generic `deriv` rules in the lambda form used below -/

/-- Derivative of `w ↦ f (w * B)` (the `B⁻¹`-rescaled right factor). -/
theorem deriv_comp_mul_right (B x : ℝ) (f : ℝ → ℝ) :
    deriv (fun w : ℝ => f (w * B)) x = deriv f (x * B) * B := by
  have hfun : (fun w : ℝ => f (w * B)) = fun w : ℝ => f (B * w) := by
    funext w; rw [mul_comm]
  rw [hfun, deriv_comp_mul_left]
  simp only [smul_eq_mul]
  rw [mul_comm B x]; ring

/-- Product rule in lambda form. -/
theorem deriv_prod_lam (f g : ℝ → ℝ) (x : ℝ)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (fun y : ℝ => f y * g y) x = deriv f x * g x + f x * deriv g x := by
  change deriv (f * g) x = deriv f x * g x + f x * deriv g x
  rw [deriv_mul hf hg]

/-- Difference rule in lambda form. -/
theorem deriv_sub_lam (f g : ℝ → ℝ) (x : ℝ)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (fun y : ℝ => f y - g y) x = deriv f x - deriv g x := by
  change deriv (f - g) x = deriv f x - deriv g x
  rw [deriv_sub hf hg]

/-! ## Smoothness and pointwise range of the cut-off -/

theorem zcChi_contDiff (n m : ℕ) : ContDiff ℝ m (zcChi n) := by
  have h1 : ContDiff ℝ m (fun z : ℝ => zcPsi (zcScale n * z)) :=
    (zcPsi_contDiff m).comp (contDiff_const.mul contDiff_id)
  have h2 : ContDiff ℝ m (fun z : ℝ => zcPsi (z * (zcScale n)⁻¹)) :=
    (zcPsi_contDiff m).comp (contDiff_id.mul contDiff_const)
  have h3 : ContDiff ℝ m (fun z : ℝ => 1 - zcPsi (z * (zcScale n)⁻¹)) :=
    contDiff_const.sub h2
  exact h1.mul h3

theorem zcChi_nonneg (n : ℕ) (z : ℝ) : 0 ≤ zcChi n z := by
  show 0 ≤ zcPsi (zcScale n * z) * (1 - zcPsi (z * (zcScale n)⁻¹))
  have h1 : 0 ≤ zcPsi (zcScale n * z) := zcPsi_nonneg _
  have h2 : 0 ≤ 1 - zcPsi (z * (zcScale n)⁻¹) := by
    linarith [zcPsi_le_one (z * (zcScale n)⁻¹)]
  positivity

theorem zcChi_le_one (n : ℕ) (z : ℝ) : zcChi n z ≤ 1 := by
  show zcPsi (zcScale n * z) * (1 - zcPsi (z * (zcScale n)⁻¹)) ≤ 1
  have h1 : 0 ≤ zcPsi (zcScale n * z) := zcPsi_nonneg _
  have h2 : zcPsi (zcScale n * z) ≤ 1 := zcPsi_le_one _
  have h3 : 0 ≤ 1 - zcPsi (z * (zcScale n)⁻¹) := by
    linarith [zcPsi_le_one (z * (zcScale n)⁻¹)]
  have h4 : 1 - zcPsi (z * (zcScale n)⁻¹) ≤ 1 := by
    linarith [zcPsi_nonneg (z * (zcScale n)⁻¹)]
  nlinarith [mul_le_mul h2 h4 h3 (by norm_num : (0:ℝ) ≤ 1)]

/-! ## The three threshold regimes -/

theorem zcChi_eq_zero_left (n : ℕ) (z : ℝ) (hz : z ≤ 1 / ((n : ℝ) + 1)) : zcChi n z = 0 := by
  have hz' : z ≤ (zcScale n)⁻¹ := by rw [one_div] at hz; exact hz
  have h : zcScale n * z ≤ 1 := by
    calc zcScale n * z ≤ zcScale n * (zcScale n)⁻¹ :=
          mul_le_mul_of_nonneg_left hz' (le_of_lt (zcScale_pos n))
      _ = 1 := zcScale_mul_inv n
  show zcPsi (zcScale n * z) * (1 - zcPsi (z * (zcScale n)⁻¹)) = 0
  rw [zcPsi_eq_zero h, zero_mul]

theorem zcChi_eq_one_mid (n : ℕ) (z : ℝ) (hz1 : 2 / ((n : ℝ) + 1) ≤ z)
    (hz2 : z ≤ (n : ℝ) + 1) : zcChi n z = 1 := by
  have hA : 0 < zcScale n := zcScale_pos n
  have hz1' : 2 * (zcScale n)⁻¹ ≤ z := by rw [div_eq_mul_inv] at hz1; exact hz1
  have hz2' : z ≤ zcScale n := hz2
  have h1 : 2 ≤ zcScale n * z := by
    have h := mul_le_mul_of_nonneg_right hz1' (le_of_lt hA)
    rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hA), mul_one] at h
    rwa [mul_comm z (zcScale n)] at h
  have h2 : z * (zcScale n)⁻¹ ≤ 1 := by
    calc z * (zcScale n)⁻¹ ≤ zcScale n * (zcScale n)⁻¹ :=
          mul_le_mul_of_nonneg_right hz2' (inv_nonneg.mpr (le_of_lt hA))
      _ = 1 := zcScale_mul_inv n
  show zcPsi (zcScale n * z) * (1 - zcPsi (z * (zcScale n)⁻¹)) = 1
  rw [zcPsi_eq_one h1, zcPsi_eq_zero h2]
  ring

theorem zcChi_eq_zero_right (n : ℕ) (z : ℝ) (hz : 2 * ((n : ℝ) + 1) ≤ z) : zcChi n z = 0 := by
  have hA : 0 < zcScale n := zcScale_pos n
  have hz' : 2 * zcScale n ≤ z := hz
  have h : 2 ≤ z * (zcScale n)⁻¹ := by
    have h1 := mul_le_mul_of_nonneg_right hz' (inv_nonneg.mpr (le_of_lt hA))
    rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hA), mul_one] at h1
    exact h1
  show zcPsi (zcScale n * z) * (1 - zcPsi (z * (zcScale n)⁻¹)) = 0
  rw [zcPsi_eq_one h, sub_self, mul_zero]

/-! ## The first weighted derivative, and its uniform bound -/

/-- `z ↦ z χ_n'(z)`, computed explicitly. -/
theorem deriv_zcChi_eq (n : ℕ) (z : ℝ) :
    deriv (zcChi n) z
      = deriv zcPsi (zcScale n * z) * zcScale n * (1 - zcPsi (z * (zcScale n)⁻¹))
        - zcPsi (zcScale n * z) * (deriv zcPsi (z * (zcScale n)⁻¹) * (zcScale n)⁻¹) := by
  have hd1 : DifferentiableAt ℝ (fun w : ℝ => zcPsi (zcScale n * w)) z := by
    have h : Differentiable ℝ zcPsi := zcPsi_diff
    fun_prop
  have hd2 : DifferentiableAt ℝ (fun w : ℝ => 1 - zcPsi (w * (zcScale n)⁻¹)) z := by
    have h : Differentiable ℝ zcPsi := zcPsi_diff
    fun_prop
  show deriv (fun w : ℝ => zcPsi (zcScale n * w) * (1 - zcPsi (w * (zcScale n)⁻¹))) z = _
  rw [deriv_prod_lam _ _ _ hd1 hd2, deriv_comp_mul_left, deriv_const_sub,
    deriv_comp_mul_right]
  ring

/-- **The first key identity**: `z χ_n'(z)` in terms of the weighted derivatives `k1`. -/
theorem zcChi_mul_deriv_eq (n : ℕ) (z : ℝ) :
    z * deriv (zcChi n) z
      = zcK1 (zcScale n * z) * (1 - zcPsi (z * (zcScale n)⁻¹))
        - zcPsi (zcScale n * z) * zcK1 (z * (zcScale n)⁻¹) := by
  rw [deriv_zcChi_eq]
  simp only [zcK1]
  ring

theorem zcChi_deriv_bound (M₁ : ℝ) (hK1 : ∀ t : ℝ, |zcK1 t| ≤ M₁) (n : ℕ) (z : ℝ) :
    |z * deriv (zcChi n) z| ≤ 2 * M₁ := by
  rw [zcChi_mul_deriv_eq]
  have h1 : |1 - zcPsi (z * (zcScale n)⁻¹)| ≤ 1 :=
    abs_le.mpr ⟨by linarith [zcPsi_le_one (z * (zcScale n)⁻¹)],
      by linarith [zcPsi_nonneg (z * (zcScale n)⁻¹)]⟩
  have h2 : |zcPsi (zcScale n * z)| ≤ 1 :=
    abs_le.mpr ⟨by linarith [zcPsi_nonneg (zcScale n * z)], zcPsi_le_one _⟩
  have hM : 0 ≤ M₁ := le_trans (abs_nonneg _) (hK1 0)
  have hb1 : |zcK1 (zcScale n * z) * (1 - zcPsi (z * (zcScale n)⁻¹))| ≤ M₁ := by
    rw [abs_mul]
    calc |zcK1 (zcScale n * z)| * |1 - zcPsi (z * (zcScale n)⁻¹)| ≤ M₁ * 1 :=
          mul_le_mul (hK1 _) h1 (abs_nonneg _) hM
      _ = M₁ := mul_one M₁
  have hb2 : |zcPsi (zcScale n * z) * zcK1 (z * (zcScale n)⁻¹)| ≤ M₁ := by
    rw [abs_mul]
    calc |zcPsi (zcScale n * z)| * |zcK1 (z * (zcScale n)⁻¹)| ≤ 1 * M₁ :=
          mul_le_mul h2 (hK1 _) (abs_nonneg _) (by norm_num)
      _ = M₁ := one_mul M₁
  calc |zcK1 (zcScale n * z) * (1 - zcPsi (z * (zcScale n)⁻¹))
        - zcPsi (zcScale n * z) * zcK1 (z * (zcScale n)⁻¹)|
      ≤ |zcK1 (zcScale n * z) * (1 - zcPsi (z * (zcScale n)⁻¹))|
        + |zcPsi (zcScale n * z) * zcK1 (z * (zcScale n)⁻¹)| := abs_sub _ _
    _ ≤ M₁ + M₁ := add_le_add hb1 hb2
    _ = 2 * M₁ := by ring

/-! ## The second weighted derivative, and its uniform bound -/

/-- **The second key identity**: `z (z χ_n')'(z)` in terms of `k1` and `k2`. -/
theorem zcChi_second_mul (n : ℕ) (z : ℝ) :
    z * deriv (fun w : ℝ => w * deriv (zcChi n) w) z
      = zcK2 (zcScale n * z) * (1 - zcPsi (z * (zcScale n)⁻¹))
        - 2 * zcK1 (zcScale n * z) * zcK1 (z * (zcScale n)⁻¹)
        - zcPsi (zcScale n * z) * zcK2 (z * (zcScale n)⁻¹) := by
  have hfun : (fun w : ℝ => w * deriv (zcChi n) w)
      = fun w : ℝ => zcK1 (zcScale n * w) * (1 - zcPsi (w * (zcScale n)⁻¹))
          - zcPsi (zcScale n * w) * zcK1 (w * (zcScale n)⁻¹) :=
    funext fun w => zcChi_mul_deriv_eq n w
  rw [hfun]
  have hd1 : DifferentiableAt ℝ
      (fun w : ℝ => zcK1 (zcScale n * w) * (1 - zcPsi (w * (zcScale n)⁻¹))) z := by
    have h : Differentiable ℝ zcK1 := zcK1_diff
    have h' : Differentiable ℝ zcPsi := zcPsi_diff
    fun_prop
  have hd2 : DifferentiableAt ℝ
      (fun w : ℝ => zcPsi (zcScale n * w) * zcK1 (w * (zcScale n)⁻¹)) z := by
    have h : Differentiable ℝ zcK1 := zcK1_diff
    have h' : Differentiable ℝ zcPsi := zcPsi_diff
    fun_prop
  have hd3 : DifferentiableAt ℝ (fun w : ℝ => zcK1 (zcScale n * w)) z := by
    have h : Differentiable ℝ zcK1 := zcK1_diff
    fun_prop
  have hd4 : DifferentiableAt ℝ (fun w : ℝ => 1 - zcPsi (w * (zcScale n)⁻¹)) z := by
    have h : Differentiable ℝ zcPsi := zcPsi_diff
    fun_prop
  have hd5 : DifferentiableAt ℝ (fun w : ℝ => zcPsi (zcScale n * w)) z := by
    have h : Differentiable ℝ zcPsi := zcPsi_diff
    fun_prop
  have hd6 : DifferentiableAt ℝ (fun w : ℝ => zcK1 (w * (zcScale n)⁻¹)) z := by
    have h : Differentiable ℝ zcK1 := zcK1_diff
    fun_prop
  rw [deriv_sub_lam _ _ _ hd1 hd2, deriv_prod_lam _ _ _ hd3 hd4,
    deriv_prod_lam _ _ _ hd5 hd6,
    deriv_comp_mul_left, deriv_const_sub, deriv_comp_mul_right,
    deriv_comp_mul_left, deriv_comp_mul_right]
  simp only [zcK1, zcK2]
  ring

theorem zcChi_second_bound (M₁ M₂ : ℝ) (hK1 : ∀ t : ℝ, |zcK1 t| ≤ M₁)
    (hK2 : ∀ t : ℝ, |zcK2 t| ≤ M₂) (n : ℕ) (z : ℝ) :
    |z * deriv (fun w : ℝ => w * deriv (zcChi n) w) z| ≤ 2 * M₁ ^ 2 + 2 * M₂ := by
  rw [zcChi_second_mul]
  have h1 : |1 - zcPsi (z * (zcScale n)⁻¹)| ≤ 1 :=
    abs_le.mpr ⟨by linarith [zcPsi_le_one (z * (zcScale n)⁻¹)],
      by linarith [zcPsi_nonneg (z * (zcScale n)⁻¹)]⟩
  have h2 : |zcPsi (zcScale n * z)| ≤ 1 :=
    abs_le.mpr ⟨by linarith [zcPsi_nonneg (zcScale n * z)], zcPsi_le_one _⟩
  have hM : 0 ≤ M₁ := le_trans (abs_nonneg _) (hK1 0)
  have hb1 : |zcK2 (zcScale n * z) * (1 - zcPsi (z * (zcScale n)⁻¹))| ≤ M₂ := by
    rw [abs_mul]
    calc |zcK2 (zcScale n * z)| * |1 - zcPsi (z * (zcScale n)⁻¹)| ≤ M₂ * 1 :=
          mul_le_mul (hK2 _) h1 (abs_nonneg _) (le_trans (abs_nonneg _) (hK2 0))
      _ = M₂ := mul_one M₂
  have hb2 : |2 * zcK1 (zcScale n * z) * zcK1 (z * (zcScale n)⁻¹)| ≤ 2 * M₁ ^ 2 := by
    have e : |2 * zcK1 (zcScale n * z) * zcK1 (z * (zcScale n)⁻¹)|
        = 2 * (|zcK1 (zcScale n * z)| * |zcK1 (z * (zcScale n)⁻¹)|) := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; ring
    rw [e]
    calc 2 * (|zcK1 (zcScale n * z)| * |zcK1 (z * (zcScale n)⁻¹)|) ≤ 2 * (M₁ * M₁) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (hK1 _) (hK1 _) (abs_nonneg _) hM)
            (by norm_num)
      _ = 2 * M₁ ^ 2 := by ring
  have hb3 : |zcPsi (zcScale n * z) * zcK2 (z * (zcScale n)⁻¹)| ≤ M₂ := by
    rw [abs_mul]
    calc |zcPsi (zcScale n * z)| * |zcK2 (z * (zcScale n)⁻¹)| ≤ 1 * M₂ :=
          mul_le_mul h2 (hK2 _) (abs_nonneg _) (by norm_num)
      _ = M₂ := one_mul M₂
  have hsum :
      |zcK2 (zcScale n * z) * (1 - zcPsi (z * (zcScale n)⁻¹))
          - 2 * zcK1 (zcScale n * z) * zcK1 (z * (zcScale n)⁻¹)
          - zcPsi (zcScale n * z) * zcK2 (z * (zcScale n)⁻¹)|
        ≤ |zcK2 (zcScale n * z) * (1 - zcPsi (z * (zcScale n)⁻¹))|
          + |2 * zcK1 (zcScale n * z) * zcK1 (z * (zcScale n)⁻¹)|
          + |zcPsi (zcScale n * z) * zcK2 (z * (zcScale n)⁻¹)| := by
    have h1' := abs_sub (zcK2 (zcScale n * z) * (1 - zcPsi (z * (zcScale n)⁻¹))
      - 2 * zcK1 (zcScale n * z) * zcK1 (z * (zcScale n)⁻¹))
      (zcPsi (zcScale n * z) * zcK2 (z * (zcScale n)⁻¹))
    have h2' := abs_sub (zcK2 (zcScale n * z) * (1 - zcPsi (z * (zcScale n)⁻¹)))
      (2 * zcK1 (zcScale n * z) * zcK1 (z * (zcScale n)⁻¹))
    linarith
  linarith [hsum, hb1, hb2, hb3]

/-! ## Convergence to `1` -/

theorem zcChi_tendsto (z : ℝ) (hz : 0 < z) :
    Filter.Tendsto (fun n : ℕ => zcChi n z) Filter.atTop (nhds 1) := by
  have hscale : Filter.Tendsto (fun n : ℕ => zcScale n) Filter.atTop Filter.atTop := by
    have h1 : Filter.Tendsto (fun n : ℕ => ((n : ℝ))) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop
    simpa only [zcScale] using h1.atTop_add tendsto_const_nhds
  have e1 : ∀ᶠ n : ℕ in Filter.atTop, 2 ≤ z * zcScale n := by
    have h := (Filter.tendsto_atTop.1 hscale) (2 / z)
    filter_upwards [h] with n hn
    rw [div_le_iff₀ hz] at hn
    rwa [mul_comm]
  have e2 : ∀ᶠ n : ℕ in Filter.atTop, z ≤ zcScale n := (Filter.tendsto_atTop.1 hscale) z
  have hev : ∀ᶠ n : ℕ in Filter.atTop, zcChi n z = 1 := by
    filter_upwards [e1, e2] with n hn1 hn2
    have hn1' : 2 ≤ zcScale n * z := by linarith [hn1]
    have h3 : z * (zcScale n)⁻¹ ≤ 1 := by
      calc z * (zcScale n)⁻¹ ≤ zcScale n * (zcScale n)⁻¹ :=
            mul_le_mul_of_nonneg_right hn2 (inv_nonneg.mpr (le_of_lt (zcScale_pos n)))
        _ = 1 := zcScale_mul_inv n
    show zcPsi (zcScale n * z) * (1 - zcPsi (z * (zcScale n)⁻¹)) = 1
    rw [zcPsi_eq_one hn1', zcPsi_eq_zero h3]
    ring
  exact (Filter.tendsto_congr' hev).mpr tendsto_const_nhds

/-! ## Uniform bounds for `k1` and `k2`

Both `k1` and `k2` are continuous and vanish for `t < 1` and for `2 < t`, so they are bounded by
the supremum of their absolute values on the compact interval `[0,3]`.  This is also available as
the standalone module `Work.FTS.EllipticEst.Mine.zcutK12Bound`. -/

theorem zcK12Bound_self :
    ∃ M₁ M₂ : ℝ, 0 < M₁ ∧ 0 < M₂ ∧
      (∀ t : ℝ, |zcK1 t| ≤ M₁) ∧ (∀ t : ℝ, |zcK2 t| ≤ M₂) := by
  obtain ⟨a, _, ha⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by norm_num : (0 : ℝ) ≤ 3)) zcK1_continuous.abs.continuousOn
  obtain ⟨b, _, hb⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by norm_num : (0 : ℝ) ≤ 3)) zcK2_continuous.abs.continuousOn
  refine ⟨|zcK1 a| + 1, |zcK2 b| + 1, by positivity, by positivity, ?_, ?_⟩
  · intro t
    by_cases ht : t ∈ Set.Icc (0 : ℝ) 3
    · have hle : |zcK1 t| ≤ |zcK1 a| := ha ht
      linarith
    · rcases lt_or_ge t 0 with ht0 | ht0
      · rw [zcK1_eq_zero_of_lt_one (by linarith)]
        simp only [abs_zero]; positivity
      · have ht3 : 3 < t := lt_of_not_ge (fun hle => ht ⟨ht0, hle⟩)
        rw [zcK1_eq_zero_of_gt_two (by linarith)]
        simp only [abs_zero]; positivity
  · intro t
    by_cases ht : t ∈ Set.Icc (0 : ℝ) 3
    · have hle : |zcK2 t| ≤ |zcK2 b| := hb ht
      linarith
    · rcases lt_or_ge t 0 with ht0 | ht0
      · rw [zcK2_eq_zero_of_lt_one (by linarith)]
        simp only [abs_zero]; positivity
      · have ht3 : 3 < t := lt_of_not_ge (fun hle => ht ⟨ht0, hle⟩)
        rw [zcK2_eq_zero_of_gt_two (by linarith)]
        simp only [abs_zero]; positivity

/-! ## The cut-off family -/

theorem zcutFam :
    ∃ (χ : ℕ → ℝ → ℝ) (C₁ C₂ : ℝ), 0 < C₁ ∧ 0 < C₂ ∧
      (∀ n m : ℕ, ContDiff ℝ m (χ n)) ∧
      (∀ (n : ℕ) (z : ℝ), 0 ≤ χ n z ∧ χ n z ≤ 1) ∧
      (∀ (n : ℕ) (z : ℝ), z ≤ 1 / ((n : ℝ) + 1) → χ n z = 0) ∧
      (∀ (n : ℕ) (z : ℝ), 2 / ((n : ℝ) + 1) ≤ z → z ≤ (n : ℝ) + 1 → χ n z = 1) ∧
      (∀ (n : ℕ) (z : ℝ), 2 * ((n : ℝ) + 1) ≤ z → χ n z = 0) ∧
      (∀ (n : ℕ) (z : ℝ), |z * deriv (χ n) z| ≤ C₁) ∧
      (∀ (n : ℕ) (z : ℝ), |z * deriv (fun w : ℝ => w * deriv (χ n) w) z| ≤ C₂) ∧
      (∀ z, 0 < z → Filter.Tendsto (fun n : ℕ => χ n z) Filter.atTop (nhds 1)) := by
  obtain ⟨M₁, M₂, hM₁, hM₂, hK1, hK2⟩ := zcK12Bound_self
  refine ⟨zcChi, 2 * M₁, 2 * M₁ ^ 2 + 2 * M₂, by linarith, by positivity, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · exact fun n m => zcChi_contDiff n m
  · exact fun n z => ⟨zcChi_nonneg n z, zcChi_le_one n z⟩
  · exact fun n z hz => zcChi_eq_zero_left n z hz
  · exact fun n z hz1 hz2 => zcChi_eq_one_mid n z hz1 hz2
  · exact fun n z hz => zcChi_eq_zero_right n z hz
  · exact fun n z => zcChi_deriv_bound M₁ hK1 n z
  · exact fun n z => zcChi_second_bound M₁ M₂ hK1 hK2 n z
  · exact fun z hz => zcChi_tendsto z hz

end Work.FTS.EllipticEst.Mine
