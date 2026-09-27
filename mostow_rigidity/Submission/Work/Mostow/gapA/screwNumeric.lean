import Mathlib
import Submission.Work.Mostow.gapA.defs

namespace Work.Mostow.gapA

open Submission.Mostow

noncomputable section

set_option maxHeartbeats 2000000

/-- `1 ≤ sinh 1`, used to replace `cosh r` by `sinh (r+1)` for `r ≥ 0`. -/
lemma sinh_one_ge_one : (1 : ℝ) ≤ Real.sinh 1 := by
  have hE : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hEpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  rw [Real.sinh_eq, Real.exp_neg]
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  rw [one_mul]
  have h : Real.exp 1 - (Real.exp 1)⁻¹ = (Real.exp 1 ^ 2 - 1) / Real.exp 1 := by
    field_simp
  rw [h, le_div_iff₀ hEpos]
  nlinarith [sq_nonneg (Real.exp 1 - 2.7), hE]

/-- `cosh 1 - (21/20) sinh 1 ≥ 1/4`, the numerical core of the estimate
`sinh ρ ≥ x/4` where `sinh (ρ+1) = x`. -/
lemma cosh_one_sub_sinh_one : (1 : ℝ)/4 ≤ Real.cosh 1 - (21/20) * Real.sinh 1 := by
  have hE : Real.exp 1 < 2.72 := by linarith [Real.exp_one_lt_d9]
  have hEpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  rw [Real.cosh_eq, Real.sinh_eq, Real.exp_neg]
  have h : (Real.exp 1 + (Real.exp 1)⁻¹) / 2 - 21 / 20 * ((Real.exp 1 - (Real.exp 1)⁻¹) / 2)
      = (41 / Real.exp 1 - Real.exp 1) / 40 := by
    field_simp
    ring
  rw [h, le_div_iff₀ (by norm_num : (0 : ℝ) < 40)]
  rw [show (1 : ℝ)/4 * 40 = 10 by norm_num]
  rw [le_sub_iff_add_le]
  rw [show (10 : ℝ) + Real.exp 1 = Real.exp 1 + 10 by ring]
  rw [le_div_iff₀ hEpos]
  nlinarith [hE, hEpos.le]

/-- The numeric core of the `n = 3` screw argument: from the tube-volume bound `hℓb`, the depth
bound `hdepth` and the screw-displacement bound `hd`, the displacement is `O(V/η_Z² + 1)·η`. -/
theorem screwNumeric (M : ℕ) (b₀ g : LeanEval.Geometry.MostowRigidity.PO 3 1)
    (ℓ η η_Z V r : ℝ) (z : Submission.Mostow.E 3) (hM : 3 ≤ M) (hℓ : 0 < ℓ) (hV : 0 ≤ V)
    (hηZ : 0 < η_Z) (hη : 0 < η) (hηc : η ≤ η_Z / 5) (hr : 0 ≤ r)
    (hℓb : ℓ * (Real.pi / (M : ℝ)) * (Real.sinh (Work.Mostow.tubeR M η_Z)) ^ 2 / 2 ≤ 2 * V)
    (hdepth : Real.sinh (r + 1) * Real.sin (Real.pi / (M : ℝ)) ≤ η / 2)
    (hd : Submission.Mostow.hdist z ((g * b₀) • z) ≤ 2 * (ℓ + Real.pi / (M : ℝ)) * Real.cosh r) :
    Submission.Mostow.hdist z ((g * b₀) • z) ≤ 300 * (V / η_Z ^ 2 + 1) * η := by
  set s : ℝ := Real.pi / (M : ℝ) with hs
  have hMpos : (0:ℝ) < (M:ℝ) := by
    have : 0 < M := by omega
    exact_mod_cast this
  have hM3 : (3:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
  have hs_pos : 0 < s := by rw [hs]; exact div_pos Real.pi_pos hMpos
  have hs_le : s ≤ Real.pi/3 := by
    rw [hs, div_le_div_iff₀ hMpos (by norm_num : (0:ℝ) < 3)]
    nlinarith [Real.pi_pos, hM3]
  have hs_lt : s < Real.pi/2 := by linarith [hs_le, Real.pi_pos]
  have hsin_pos : 0 < Real.sin s :=
    Real.sin_pos_of_pos_of_lt_pi hs_pos (by linarith [hs_lt, Real.pi_pos])
  -- the parameter `x := η_Z/(2 sin s)`, so that `sinh (tubeR M η_Z + 1) = x`
  set x : ℝ := η_Z / (2 * Real.sin s) with hx
  have hx_pos : 0 < x := by rw [hx]; positivity
  have hxZ : η_Z = 2 * x * Real.sin s := by rw [hx]; field_simp
  -- `y := sinh (r+1)`
  set y : ℝ := Real.sinh (r + 1) with hy
  have hy_pos : 0 < y := by rw [hy]; exact Real.sinh_pos_iff.mpr (by linarith)
  have hdepth' : y * Real.sin s ≤ η / 2 := by rw [hy, hs]; exact hdepth
  have hℓb' : ℓ * s * (Real.sinh (Work.Mostow.tubeR M η_Z)) ^ 2 / 2 ≤ 2 * V := by
    rw [hs]; exact hℓb
  have hd' : Submission.Mostow.hdist z ((g * b₀) • z) ≤ 2 * (ℓ + s) * Real.cosh r := by
    rw [hs]; exact hd
  have htab : Work.Mostow.tubeR M η_Z + 1 = Real.arsinh x := by
    rw [hx, hs]; unfold Work.Mostow.tubeR; ring
  -- depth bound in the form `y ≤ x/5`
  have hyx : y ≤ x / 5 := by
    have h1 : y * Real.sin s ≤ x / 5 * Real.sin s := by
      rw [hx]; field_simp; linarith [hηc]
    exact le_of_mul_le_mul_right h1 hsin_pos
  -- hence `5 ≤ x`
  have hx_ge : 5 ≤ x := by
    have hy1 : Real.sinh 1 ≤ y := by rw [hy]; exact Real.sinh_le_sinh.mpr (by linarith)
    nlinarith [sinh_one_ge_one, hy1, hyx]
  -- the tube radius dominates `x/4`
  have hsinhT : x / 4 ≤ Real.sinh (Work.Mostow.tubeR M η_Z) := by
    have hsub : Work.Mostow.tubeR M η_Z = (Work.Mostow.tubeR M η_Z + 1) - 1 := by ring
    rw [hsub, Real.sinh_sub, htab, Real.sinh_arsinh, Real.cosh_arsinh]
    have hsqrt : Real.sqrt (1 + x ^ 2) ≤ (21/20) * x := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      nlinarith [hx_ge]
    have hmul := mul_le_mul_of_nonneg_right hsqrt (Real.sinh_pos_iff.mpr one_pos).le
    nlinarith [hmul, cosh_one_sub_sinh_one, hx_pos]
  have hsT_pos : 0 < Real.sinh (Work.Mostow.tubeR M η_Z) :=
    lt_of_lt_of_le (by positivity) hsinhT
  have hsq : x ^ 2 / 16 ≤ (Real.sinh (Work.Mostow.tubeR M η_Z)) ^ 2 := by
    nlinarith [hsinhT, hsT_pos]
  -- `ℓ ≤ 64 V / (s x²)`, in product form
  have hℓbound2 : ℓ * (s * x ^ 2) ≤ 64 * V := by
    have hA : ℓ * s * (Real.sinh (Work.Mostow.tubeR M η_Z)) ^ 2 ≤ 4 * V := by
      linarith [hℓb']
    have hA2 : ℓ * s * (x ^ 2 / 16) ≤ ℓ * s * (Real.sinh (Work.Mostow.tubeR M η_Z)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    nlinarith [hA, hA2]
  have hcoshr_y : Real.cosh r ≤ y := by
    rw [hy, Real.sinh_add]
    have h1 : Real.cosh r * (1:ℝ) ≤ Real.cosh r * Real.sinh 1 :=
      mul_le_mul_of_nonneg_left sinh_one_ge_one (Real.cosh_pos r).le
    have h2 : 0 ≤ Real.sinh r * Real.cosh 1 :=
      mul_nonneg (Real.sinh_nonneg_iff.mpr hr) (Real.cosh_pos 1).le
    linarith [h1, h2]
  -- first term: `2 ℓ cosh r ≤ 300 V η / η_Z²`
  have hterm1 : 2 * ℓ * Real.cosh r ≤ 300 * V * η / η_Z ^ 2 := by
    have h1 : 2 * ℓ * Real.cosh r ≤ 128 * V * y / (s * x ^ 2) := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < s * x ^ 2)]
      have ha : 2 * Real.cosh r * (ℓ * (s * x ^ 2)) ≤ 2 * Real.cosh r * (64 * V) :=
        mul_le_mul_of_nonneg_left hℓbound2 (by positivity)
      have hb : 2 * Real.cosh r * (64 * V) ≤ 128 * V * y := by
        nlinarith [hcoshr_y, hV, Real.cosh_pos r]
      nlinarith [ha, hb]
    have hbase : 128 * Real.sin s ≤ 150 * s := by nlinarith [Real.sin_le hs_pos.le]
    have hm1 : 128 * y * Real.sin s ^ 2 ≤ 150 * y * s * Real.sin s := by
      have := mul_le_mul_of_nonneg_left hbase (by positivity : (0:ℝ) ≤ y * Real.sin s)
      nlinarith [this]
    have hm2 : 150 * y * s * Real.sin s ≤ 75 * η * s := by
      have := mul_le_mul_of_nonneg_left hdepth' (by positivity : (0:ℝ) ≤ 150 * s)
      nlinarith [this]
    have hkey : 128 * y * Real.sin s ^ 2 ≤ 75 * η * s := le_trans hm1 hm2
    have h2 : 128 * V * y / (s * x ^ 2) ≤ 300 * V * η / η_Z ^ 2 := by
      have hz : η_Z ^ 2 = 4 * x ^ 2 * Real.sin s ^ 2 := by rw [hxZ]; ring
      rw [hz, div_le_div_iff₀ (by positivity : (0:ℝ) < s * x ^ 2)
        (by positivity : (0:ℝ) < 4 * x ^ 2 * Real.sin s ^ 2)]
      have hmul := mul_le_mul_of_nonneg_left hkey
        (by nlinarith [hV, sq_nonneg x] : (0:ℝ) ≤ 4 * V * x ^ 2)
      nlinarith [hmul]
    linarith [h1, h2]
  -- second term: `2 s cosh r ≤ 300 η`
  have hterm2 : 2 * s * Real.cosh r ≤ 300 * η := by
    have hys2 : 2 * s * Real.cosh r * Real.sin s ≤ η * s := by
      have ha := mul_le_mul_of_nonneg_left hcoshr_y
        (by positivity : (0:ℝ) ≤ 2 * s * Real.sin s)
      have hb := mul_le_mul_of_nonneg_left hdepth' (by positivity : (0:ℝ) ≤ 2 * s)
      nlinarith [ha, hb]
    have hslt : s < 300 * Real.sin s := by
      have hj := Real.mul_lt_sin hs_pos hs_lt
      have hkey : Real.pi / 2 * (2 / Real.pi * s) = s := by field_simp
      have h1 := mul_lt_mul_of_pos_left hj (by positivity : (0:ℝ) < Real.pi / 2)
      rw [hkey] at h1
      nlinarith [h1, Real.pi_le_four, hsin_pos]
    have hmain : 2 * s * Real.cosh r * Real.sin s ≤ 300 * η * Real.sin s := by
      have : η * s ≤ 300 * η * Real.sin s := by nlinarith [hslt, hη]
      linarith [hys2, this]
    exact le_of_mul_le_mul_right hmain hsin_pos
  have htotal : 2 * (ℓ + s) * Real.cosh r ≤ 300 * (V / η_Z ^ 2 + 1) * η := by
    have hexp : 300 * (V / η_Z ^ 2 + 1) * η = 300 * V * η / η_Z ^ 2 + 300 * η := by
      field_simp
    rw [hexp]
    have : 2 * (ℓ + s) * Real.cosh r = 2 * ℓ * Real.cosh r + 2 * s * Real.cosh r := by ring
    rw [this]
    linarith [hterm1, hterm2]
  calc Submission.Mostow.hdist z ((g * b₀) • z) ≤ 2 * (ℓ + s) * Real.cosh r := hd'
    _ ≤ 300 * (V / η_Z ^ 2 + 1) * η := htotal

end

end Work.Mostow.gapA
