import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Elliptic.HardyTwoDefs
import Submission.Work.Elliptic.seg_second_order_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-- `sin (2x) > 0` and Jordan's inequality `(4/π) x ≤ sin (2x)` on `(0, π/4)`. -/
theorem sin_two_jordan (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) (π / 4)) :
    0 < Real.sin (2 * x) ∧ (4 / π) * x ≤ Real.sin (2 * x) := by
  have h2x0 : 0 ≤ 2 * x := by linarith [hx.1]
  have h2x2 : 2 * x ≤ π / 2 := by linarith [hx.2]
  refine ⟨?_, ?_⟩
  · exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2, Real.pi_pos])
  · have h := Real.mul_le_sin h2x0 h2x2
    calc (4 / π) * x = 2 / π * (2 * x) := by ring
      _ ≤ Real.sin (2 * x) := h

/-- If `|y| ≤ K x²` with `K ≥ 0` and `x ∈ (0, π/4)` then `|y| / sin (2x)² ≤ K π²/16`. -/
theorem div_sin_sq_le (y x K : ℝ) (hK : 0 ≤ K) (hx : x ∈ Set.Ioo (0 : ℝ) (π / 4))
    (hy : |y| ≤ K * x ^ 2) :
    |y| / (Real.sin (2 * x)) ^ 2 ≤ K * (π ^ 2 / 16) := by
  obtain ⟨hs, hle⟩ := sin_two_jordan x hx
  have hpi : 0 < π := Real.pi_pos
  have hs2 : 0 < (Real.sin (2 * x)) ^ 2 := pow_pos hs 2
  have h1 : 4 * x ≤ π * Real.sin (2 * x) := by
    have h := mul_le_mul_of_nonneg_left hle (le_of_lt hpi)
    have he : π * ((4 / π) * x) = 4 * x := by field_simp
    linarith [h, he]
  have hsq : x ^ 2 ≤ (π / 4) ^ 2 * (Real.sin (2 * x)) ^ 2 := by
    have h4x0 : 0 ≤ 4 * x := by linarith [hx.1]
    have hsq' : (4 * x) ^ 2 ≤ (π * Real.sin (2 * x)) ^ 2 := pow_le_pow_left₀ h4x0 h1 2
    have he1 : (4 * x) ^ 2 = 16 * x ^ 2 := by ring
    have he2 : (π * Real.sin (2 * x)) ^ 2 = π ^ 2 * (Real.sin (2 * x)) ^ 2 := by ring
    rw [he1, he2] at hsq'
    nlinarith [hsq']
  have hstep : |y| / (Real.sin (2 * x)) ^ 2 ≤ K * x ^ 2 / (Real.sin (2 * x)) ^ 2 :=
    div_le_div_of_nonneg_right hy (le_of_lt hs2)
  have hstep2 : K * x ^ 2 / (Real.sin (2 * x)) ^ 2 ≤ K * (π ^ 2 / 16) := by
    rw [div_le_iff₀ hs2]
    have hmul := mul_le_mul_of_nonneg_left hsq hK
    have he : K * ((π / 4) ^ 2 * (Real.sin (2 * x)) ^ 2)
        = K * (π ^ 2 / 16) * (Real.sin (2 * x)) ^ 2 := by ring
    linarith [hmul, he]
  linarith

/-- Derivative of `y ↦ g₁ y * sin (2y) - 2 (cos (2y) * f y)` within a set `s`, given the
within-derivatives of `g₁` and `f` on `s`. -/
theorem hasDerivWithinAt_comb (g1 g2 f : ℝ → ℝ) (s : Set ℝ)
    (hdg1 : ∀ x ∈ s, HasDerivWithinAt g1 (g2 x) s x)
    (hdf : ∀ x ∈ s, HasDerivWithinAt f (g1 x) s x)
    (t : ℝ) (ht : t ∈ s) :
    HasDerivWithinAt (fun y : ℝ => g1 y * Real.sin (2 * y) - 2 * (Real.cos (2 * y) * f y))
      (g2 t * Real.sin (2 * t) + 4 * Real.sin (2 * t) * f t) s t := by
  have hsin : HasDerivWithinAt (fun y : ℝ => Real.sin (2 * y)) (2 * Real.cos (2 * t)) s t := by
    have h3 : HasDerivAt (fun y : ℝ => Real.sin (2 * y)) (Real.cos (2 * t) * 2) t :=
      (hasDerivAt_const_mul (2 : ℝ) (x := t)).sin
    have h : HasDerivAt (fun y : ℝ => Real.sin (2 * y)) (2 * Real.cos (2 * t)) t := by
      convert h3 using 1
      ring
    exact h.hasDerivWithinAt
  have hcos : HasDerivWithinAt (fun y : ℝ => Real.cos (2 * y)) (-(2 * Real.sin (2 * t))) s t := by
    have h3 : HasDerivAt (fun y : ℝ => Real.cos (2 * y)) (-Real.sin (2 * t) * 2) t :=
      (hasDerivAt_const_mul (2 : ℝ) (x := t)).cos
    have h : HasDerivAt (fun y : ℝ => Real.cos (2 * y)) (-(2 * Real.sin (2 * t))) t := by
      convert h3 using 1
      ring
    exact h.hasDerivWithinAt
  have h1 := (hdg1 t ht).mul hsin
  have h2 := (hcos.mul (hdf t ht)).const_mul 2
  have h4 := h1.sub h2
  convert h4 using 1
  ring

theorem htU_near_zero (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2))) (h0 : f 0 = 0)
    (hcomp1 : ∀ x ∈ Set.Ioo 0 (π / 2), deriv f x = iteratedDerivWithin 1 f (Set.Icc 0 (π / 2)) x)
    (hcomp2 : ∀ x ∈ Set.Ioo 0 (π / 2),
        deriv (deriv f) x = iteratedDerivWithin 2 f (Set.Icc 0 (π / 2)) x)
    (hid1 : ∀ x ∈ Set.Ioo 0 (π / 2),
        (Real.sin (2 * x)) ^ 2 * deriv (Work.Elliptic.htU f) x
          = deriv f x * Real.sin (2 * x) - 2 * Real.cos (2 * x) * f x)
    (hid2 : ∀ x ∈ Set.Ioo 0 (π / 2),
        Real.sin (2 * x) * deriv (deriv (Work.Elliptic.htU f)) x
          = deriv (deriv f) x + 4 * f x - 4 * Real.cos (2 * x) * deriv (Work.Elliptic.htU f) x) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      (∀ x ∈ Set.Ioo 0 δ, |f x| ≤ C * x) ∧
      (∀ x ∈ Set.Ioo 0 δ, |deriv f x - derivWithin f (Set.Icc 0 (π / 2)) 0| ≤ C * x) ∧
      (∀ x ∈ Set.Ioo 0 δ, |deriv (deriv f) x| ≤ C) ∧
      (∀ x ∈ Set.Ioo 0 δ, |Work.Elliptic.htU f x| ≤ C) ∧
      (∀ x ∈ Set.Ioo 0 δ, |deriv (Work.Elliptic.htU f) x| ≤ C) ∧
      (∀ x ∈ Set.Ioo 0 δ,
        |Real.sin (2 * x) * deriv (deriv (Work.Elliptic.htU f)) x| ≤ C) := by
  have hpi : 0 < π := Real.pi_pos
  have hs_unique : UniqueDiffOn ℝ (Set.Icc 0 (π / 2)) := uniqueDiffOn_Icc (by linarith)
  have hfdiff : DifferentiableOn ℝ f (Set.Icc 0 (π / 2)) := hf.differentiableOn (by norm_num)
  set g1 : ℝ → ℝ := iteratedDerivWithin 1 f (Set.Icc 0 (π / 2)) with hg1
  set g2 : ℝ → ℝ := iteratedDerivWithin 2 f (Set.Icc 0 (π / 2)) with hg2
  have hg1_eq : g1 = derivWithin f (Set.Icc 0 (π / 2)) := by rw [hg1, iteratedDerivWithin_one]
  have hg2_eq : g2 = derivWithin g1 (Set.Icc 0 (π / 2)) := by
    rw [hg2, hg1]; exact iteratedDerivWithin_succ
  have hg1diff : DifferentiableOn ℝ g1 (Set.Icc 0 (π / 2)) := by
    have := hf.differentiableOn_iteratedDerivWithin (m := 1) (by norm_num) hs_unique
    simpa [← hg1] using this
  have hg1cont : ContinuousOn g1 (Set.Icc 0 (π / 2)) := by
    have := hf.continuousOn_iteratedDerivWithin (m := 1) (by norm_num) hs_unique
    simpa [← hg1] using this
  have hg2cont : ContinuousOn g2 (Set.Icc 0 (π / 2)) := by
    have := hf.continuousOn_iteratedDerivWithin (m := 2) (by norm_num) hs_unique
    simpa [← hg2] using this
  obtain ⟨m1, hm1⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := π / 2)).exists_bound_of_continuousOn hg1cont
  obtain ⟨m2, hm2⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := π / 2)).exists_bound_of_continuousOn hg2cont
  set Mf : ℝ := max m1 0 with hMfdef
  have hMf0 : 0 ≤ Mf := by rw [hMfdef]; exact le_max_right _ _
  have hMfbd : ∀ x ∈ Set.Icc 0 (π / 2), ‖g1 x‖ ≤ Mf := by
    intro x hx; rw [hMfdef]; exact le_trans (hm1 x hx) (le_max_left _ _)
  set M2 : ℝ := max m2 0 with hM2def
  have hM20 : 0 ≤ M2 := by rw [hM2def]; exact le_max_right _ _
  have hM2bd : ∀ x ∈ Set.Icc 0 (π / 2), ‖g2 x‖ ≤ M2 := by
    intro x hx; rw [hM2def]; exact le_trans (hm2 x hx) (le_max_left _ _)
  -- within-derivatives of `f` and `g₁`
  have hdf : ∀ x ∈ Set.Icc 0 (π / 2), HasDerivWithinAt f (g1 x) (Set.Icc 0 (π / 2)) x := by
    intro x hx
    have h := (hfdiff x hx).hasDerivWithinAt
    rwa [← hg1_eq] at h
  have hdg1 : ∀ x ∈ Set.Icc 0 (π / 2), HasDerivWithinAt g1 (g2 x) (Set.Icc 0 (π / 2)) x := by
    intro x hx
    have h := (hg1diff x hx).hasDerivWithinAt
    rwa [← hg2_eq] at h
  -- first order bounds
  have hMVT1 : ∀ x ∈ Set.Icc 0 (π / 2), ‖f x - f 0‖ ≤ Mf * x := by
    have h := norm_image_sub_le_of_norm_deriv_le_segment' (a := (0 : ℝ)) (b := π / 2) hdf
      (fun y hy => hMfbd y ⟨hy.1, le_of_lt hy.2⟩)
    simpa using h
  have hMVT2 : ∀ x ∈ Set.Icc 0 (π / 2), ‖g1 x - g1 0‖ ≤ M2 * x := by
    have h := norm_image_sub_le_of_norm_deriv_le_segment' (a := (0 : ℝ)) (b := π / 2) hdg1
      (fun y hy => hM2bd y ⟨hy.1, le_of_lt hy.2⟩)
    simpa using h
  have hbd1 : ∀ x ∈ Set.Icc 0 (π / 2), |f x| ≤ Mf * x := by
    intro x hx
    have h := hMVT1 x hx
    simpa [h0, Real.norm_eq_abs] using h
  have hbd3 : ∀ x ∈ Set.Ioo 0 (π / 2), |deriv (deriv f) x| ≤ M2 := by
    intro x hx
    have h := hM2bd x ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    rw [Real.norm_eq_abs] at h
    have h2 : deriv (deriv f) x = g2 x := hcomp2 x hx
    rwa [h2]
  have hbd2 : ∀ x ∈ Set.Ioo 0 (π / 2),
      |deriv f x - derivWithin f (Set.Icc 0 (π / 2)) 0| ≤ M2 * x := by
    intro x hx
    have h := hMVT2 x ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    rw [Real.norm_eq_abs] at h
    have h2 : deriv f x = g1 x := hcomp1 x hx
    have h3 : derivWithin f (Set.Icc 0 (π / 2)) 0 = g1 0 := by rw [← hg1_eq]
    rwa [h2, h3]
  -- the auxiliary function `N` and its second order bound
  set N : ℝ → ℝ := fun y => g1 y * Real.sin (2 * y) - 2 * (Real.cos (2 * y) * f y) with hN
  set N' : ℝ → ℝ := fun y => g2 y * Real.sin (2 * y) + 4 * Real.sin (2 * y) * f y with hN'
  set K : ℝ := 2 * M2 + 4 * π * Mf with hKdef
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  have hNdiff : ∀ t ∈ Set.Icc 0 (π / 2), HasDerivWithinAt N (N' t) (Set.Icc 0 (π / 2)) t := by
    intro t ht
    have h := hasDerivWithinAt_comb g1 g2 f (Set.Icc 0 (π / 2)) hdg1 hdf t ht
    simpa only [hN, hN'] using h
  have hN'bd : ∀ t ∈ Set.Icc 0 (π / 2), ‖N' t‖ ≤ K * t := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have ht2 : t ≤ π / 2 := ht.2
    have hsinabs : |Real.sin (2 * t)| ≤ 2 * t := by
      have h := Real.abs_sin_le_abs (x := 2 * t)
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * t)] at h
      linarith
    have hg2t : |g2 t| ≤ M2 := by
      have h := hM2bd t ht
      rwa [Real.norm_eq_abs] at h
    have hft : |f t| ≤ Mf * t := by
      have h := hMVT1 t ht
      simpa [h0, Real.norm_eq_abs] using h
    have hval : N' t = Real.sin (2 * t) * (g2 t + 4 * f t) := by
      simp only [hN']; ring
    have hfac : |g2 t + 4 * f t| ≤ M2 + 4 * (Mf * t) := by
      calc |g2 t + 4 * f t| ≤ |g2 t| + |4 * f t| := abs_add_le _ _
        _ = |g2 t| + 4 * |f t| := by rw [abs_mul]; norm_num
        _ ≤ M2 + 4 * (Mf * t) := by linarith
    calc ‖N' t‖ = |Real.sin (2 * t) * (g2 t + 4 * f t)| := by rw [Real.norm_eq_abs, hval]
      _ = |Real.sin (2 * t)| * |g2 t + 4 * f t| := abs_mul _ _
      _ ≤ (2 * t) * (M2 + 4 * (Mf * t)) :=
          mul_le_mul hsinabs hfac (abs_nonneg _) (by linarith)
      _ ≤ K * t := by
          rw [hKdef]
          have hX : 0 ≤ Mf * t * (π - 2 * t) :=
            mul_nonneg (mul_nonneg hMf0 ht0) (by linarith)
          nlinarith [hX]
  have hN0 : N 0 = 0 := by simp [hN, h0]
  have hNbd : ∀ x ∈ Set.Icc 0 (π / 2), ‖N x - N 0‖ ≤ K * x ^ 2 :=
    seg_second_order_bound N N' K (π / 2) hK0 (by positivity) hNdiff hN'bd
  have hnum : ∀ x ∈ Set.Ioo 0 (π / 2),
      |deriv f x * Real.sin (2 * x) - 2 * Real.cos (2 * x) * f x| ≤ K * x ^ 2 := by
    intro x hx
    have h1 := hNbd x ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    rw [hN0, sub_zero, Real.norm_eq_abs] at h1
    have h3 : N x = deriv f x * Real.sin (2 * x) - 2 * Real.cos (2 * x) * f x := by
      simp only [hN, hcomp1 x hx]
      ring
    rwa [h3] at h1
  have hnumbd : ∀ x ∈ Set.Ioo 0 (π / 4),
      |deriv f x * Real.sin (2 * x) - 2 * Real.cos (2 * x) * f x| ≤ K * x ^ 2 :=
    fun x hx => hnum x ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
  -- bounds on htU and its derivatives
  have hbdu : ∀ x ∈ Set.Ioo 0 (π / 4), |htU f x| ≤ Mf * (π / 4) := by
    intro x hx
    obtain ⟨hspos, hsj⟩ := sin_two_jordan x hx
    have hxI : x ∈ Set.Icc 0 (π / 2) := ⟨le_of_lt hx.1, by linarith [hx.2, Real.pi_pos]⟩
    have hfx : |f x| ≤ Mf * x := hbd1 x hxI
    have hhtU : htU f x = f x / Real.sin (2 * x) := rfl
    rw [hhtU, abs_div, abs_of_pos hspos, div_le_iff₀ hspos]
    have hxs : x ≤ (π / 4) * Real.sin (2 * x) := by
      have h := mul_le_mul_of_nonneg_left hsj (by positivity : (0 : ℝ) ≤ π / 4)
      have he : (π / 4) * ((4 / π) * x) = x := by field_simp
      linarith [h, he]
    calc |f x| ≤ Mf * x := hfx
      _ ≤ Mf * ((π / 4) * Real.sin (2 * x)) := mul_le_mul_of_nonneg_left hxs hMf0
      _ = Mf * (π / 4) * Real.sin (2 * x) := by ring
  have hbdu' : ∀ x ∈ Set.Ioo 0 (π / 4), |deriv (htU f) x| ≤ K * (π ^ 2 / 16) := by
    intro x hx
    have hxIoo : x ∈ Set.Ioo 0 (π / 2) := ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
    obtain ⟨hspos, _⟩ := sin_two_jordan x hx
    have hsqpos : 0 < (Real.sin (2 * x)) ^ 2 := pow_pos hspos 2
    have hid1x := hid1 x hxIoo
    have hu' : deriv (htU f) x
        = (deriv f x * Real.sin (2 * x) - 2 * Real.cos (2 * x) * f x)
            / (Real.sin (2 * x)) ^ 2 := by
      rw [eq_div_iff (ne_of_gt hsqpos)]
      rw [mul_comm]
      exact hid1x
    rw [hu', abs_div, abs_of_pos hsqpos]
    exact div_sin_sq_le _ x K hK0 hx (hnumbd x hx)
  have hbdu'' : ∀ x ∈ Set.Ioo 0 (π / 4),
      |Real.sin (2 * x) * deriv (deriv (htU f)) x| ≤ M2 + π * Mf + K * (π ^ 2 / 4) := by
    intro x hx
    have hxIoo : x ∈ Set.Ioo 0 (π / 2) := ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
    have hxI : x ∈ Set.Icc 0 (π / 2) := ⟨le_of_lt hx.1, by linarith [hx.2, Real.pi_pos]⟩
    rw [hid2 x hxIoo]
    have hA : |deriv (deriv f) x| ≤ M2 := hbd3 x hxIoo
    have hfx : |f x| ≤ Mf * x := hbd1 x hxI
    have hB : |4 * f x| ≤ π * Mf := by
      rw [abs_mul, show |(4 : ℝ)| = 4 by norm_num]
      have h1 : |f x| ≤ Mf * (π / 4) :=
        calc |f x| ≤ Mf * x := hfx
          _ ≤ Mf * (π / 4) := mul_le_mul_of_nonneg_left (le_of_lt hx.2) hMf0
      calc 4 * |f x| ≤ 4 * (Mf * (π / 4)) := mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ = π * Mf := by ring
    have hC2 : |4 * Real.cos (2 * x) * deriv (htU f) x| ≤ K * (π ^ 2 / 4) := by
      rw [abs_mul, abs_mul, show |(4 : ℝ)| = 4 by norm_num]
      have hcos : |Real.cos (2 * x)| ≤ 1 := Real.abs_cos_le_one _
      have hu'x : |deriv (htU f) x| ≤ K * (π ^ 2 / 16) := hbdu' x hx
      have hstep : |Real.cos (2 * x)| * |deriv (htU f) x| ≤ 1 * (K * (π ^ 2 / 16)) :=
        mul_le_mul hcos hu'x (abs_nonneg _) (by norm_num)
      nlinarith [hstep]
    calc |deriv (deriv f) x + 4 * f x - 4 * Real.cos (2 * x) * deriv (htU f) x|
        ≤ |deriv (deriv f) x + 4 * f x| + |4 * Real.cos (2 * x) * deriv (htU f) x| :=
          abs_sub _ _
      _ ≤ (|deriv (deriv f) x| + |4 * f x|) + |4 * Real.cos (2 * x) * deriv (htU f) x| := by
          linarith [abs_add_le (deriv (deriv f) x) (4 * f x)]
      _ ≤ (M2 + π * Mf) + K * (π ^ 2 / 4) := by linarith [hA, hB, hC2]
      _ = M2 + π * Mf + K * (π ^ 2 / 4) := by ring
  -- the final constant
  set C : ℝ := Mf + M2 + Mf * (π / 4) + K * (π ^ 2 / 16) + (M2 + π * Mf + K * (π ^ 2 / 4))
    with hCdef
  have hC0 : 0 ≤ C := by rw [hCdef]; positivity
  have hCf : Mf ≤ C := by
    rw [hCdef]
    have h2 : 0 ≤ Mf * (π / 4) := by positivity
    have h3 : 0 ≤ K * (π ^ 2 / 16) := by positivity
    have h4 : 0 ≤ M2 + π * Mf + K * (π ^ 2 / 4) := by positivity
    linarith
  have hCM2 : M2 ≤ C := by
    rw [hCdef]
    have h2 : 0 ≤ Mf * (π / 4) := by positivity
    have h3 : 0 ≤ K * (π ^ 2 / 16) := by positivity
    have h4 : 0 ≤ M2 + π * Mf + K * (π ^ 2 / 4) := by positivity
    linarith
  have hCu : Mf * (π / 4) ≤ C := by
    rw [hCdef]
    have h3 : 0 ≤ K * (π ^ 2 / 16) := by positivity
    have h4 : 0 ≤ M2 + π * Mf + K * (π ^ 2 / 4) := by positivity
    linarith
  have hCu' : K * (π ^ 2 / 16) ≤ C := by
    rw [hCdef]
    have h4 : 0 ≤ M2 + π * Mf + K * (π ^ 2 / 4) := by positivity
    linarith
  have hCu'' : M2 + π * Mf + K * (π ^ 2 / 4) ≤ C := by
    rw [hCdef]; linarith
  refine ⟨C, π / 4, hC0, by positivity, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hxI : x ∈ Set.Icc 0 (π / 2) := ⟨le_of_lt hx.1, by linarith [hx.2, Real.pi_pos]⟩
    calc |f x| ≤ Mf * x := hbd1 x hxI
      _ ≤ C * x := mul_le_mul_of_nonneg_right hCf (le_of_lt hx.1)
  · intro x hx
    have hxIoo : x ∈ Set.Ioo 0 (π / 2) := ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
    calc |deriv f x - derivWithin f (Set.Icc 0 (π / 2)) 0| ≤ M2 * x := hbd2 x hxIoo
      _ ≤ C * x := mul_le_mul_of_nonneg_right hCM2 (le_of_lt hx.1)
  · intro x hx
    have hxIoo : x ∈ Set.Ioo 0 (π / 2) := ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
    linarith [hbd3 x hxIoo, hCM2]
  · intro x hx
    linarith [hbdu x hx, hCu]
  · intro x hx
    linarith [hbdu' x hx, hCu']
  · intro x hx
    linarith [hbdu'' x hx, hCu'']

end Work.Elliptic
