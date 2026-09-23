import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace Commons.Analysis.ODE

open scoped Topology
open Set Filter

/-- **Riccati comparison with `cot`.**
Let `K > 0`, `T > 0` and let `w : ℝ → ℝ` be differentiable on `(0,T)` with
`w' + w^2 + K ≤ 0` there, and with the asymptotic behaviour
`(w t - √K * cot (√K * t)) * t^2 → 0` as `t → 0⁺`.
Then `w t ≤ √K * cot (√K * t)` on `(0, min T (π/√K))`. -/
theorem riccati_le_cot {w : ℝ → ℝ} {K T : ℝ} (hK : 0 < K) (hT : 0 < T)
    (hw : ∀ t ∈ Ioo 0 T, HasDerivAt w (deriv w t) t)
    (hineq : ∀ t ∈ Ioo 0 T, deriv w t + w t ^ 2 + K ≤ 0)
    (hasym : Tendsto (fun t : ℝ =>
        (w t - Real.sqrt K * Real.cot (Real.sqrt K * t)) * t ^ 2)
      (nhdsWithin 0 (Ioi 0)) (nhds 0)) :
    ∀ t ∈ Ioo 0 (min T (Real.pi / Real.sqrt K)),
      w t ≤ Real.sqrt K * Real.cot (Real.sqrt K * t) := by
  simp only [Real.cot_eq_cos_div_sin]
  set k : ℝ := Real.sqrt K with hk
  have hk_pos : 0 < k := by rw [hk]; exact Real.sqrt_pos.mpr hK
  have hk_sq : k ^ 2 = K := by rw [hk]; exact Real.sq_sqrt hK.le
  set m : ℝ := min T (Real.pi / k) with hm
  have hm_pos : 0 < m := by rw [hm]; exact lt_min hT (div_pos Real.pi_pos hk_pos)
  have hm_le_T : m ≤ T := by rw [hm]; exact min_le_left _ _
  have hm_le : m ≤ Real.pi / k := by rw [hm]; exact min_le_right _ _
  -- the three functions `s x = sin (k x)`, `c x = cos (k x)`, `u x = k cot (k x)`
  set s : ℝ → ℝ := fun x => Real.sin (k * x) with hs
  set c : ℝ → ℝ := fun x => Real.cos (k * x) with hc
  set u : ℝ → ℝ := fun x => k * (Real.cos (k * x) / Real.sin (k * x)) with hu
  -- `Y` is a positive solution of `Y' = w Y`
  set Y : ℝ → ℝ := fun x => Real.exp (∫ y in T/2..x, w y) with hY
  have hY_pos : ∀ x, 0 < Y x := fun x => Real.exp_pos _
  have hs_deriv : ∀ x : ℝ, HasDerivAt s (k * c x) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => k * y) k x := by
      simpa using (hasDerivAt_id x).const_mul k
    rw [hs]
    convert h1.sin using 1
    ring
  have hc_deriv : ∀ x : ℝ, HasDerivAt c (-(k * s x)) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => k * y) k x := by
      simpa using (hasDerivAt_id x).const_mul k
    rw [hc]
    convert h1.cos using 1
    ring
  have hs_pos : ∀ x ∈ Ioo 0 m, 0 < s x := by
    intro x hx
    have h1 : 0 < k * x := mul_pos hk_pos hx.1
    have h2 : k * x < Real.pi := by
      have h3 : x < Real.pi / k := lt_of_lt_of_le hx.2 hm_le
      calc k * x < k * (Real.pi / k) := mul_lt_mul_of_pos_left h3 hk_pos
        _ = Real.pi := by field_simp
    rw [hs]
    simpa using Real.sin_pos_of_pos_of_lt_pi h1 h2
  have hsq_le : ∀ x ∈ Ioo 0 m, s x ^ 2 ≤ (k * x) ^ 2 := by
    intro x hx
    have h := Real.sin_sq_le_sq (x := k * x)
    rw [hs]
    simpa using h
  have hY_deriv : ∀ x ∈ Ioo 0 T, HasDerivAt Y (w x * Y x) x := by
    intro x hx
    have hwcont : ContinuousOn w (Ioo 0 T) :=
      fun y hy => ((hw y hy).continuousAt).continuousWithinAt
    have hmem : uIcc (T/2) x ⊆ Ioo 0 T := by
      intro y hy
      have hT2 : T/2 ∈ Ioo (0:ℝ) T := ⟨by linarith, by linarith⟩
      rcases le_total (T/2) x with h | h
      · rw [uIcc_of_le h] at hy
        exact ⟨lt_of_lt_of_le hT2.1 hy.1, lt_of_le_of_lt hy.2 hx.2⟩
      · rw [uIcc_of_ge h] at hy
        exact ⟨lt_of_lt_of_le hx.1 hy.1, lt_of_le_of_lt hy.2 hT2.2⟩
    have hint : IntervalIntegrable w MeasureTheory.volume (T/2) x := (hwcont.mono hmem).intervalIntegrable
    have h := intervalIntegral.integral_hasDerivAt_right hint
      (hwcont.stronglyMeasurableAtFilter isOpen_Ioo x hx) ((hw x hx).continuousAt)
    have h2 := h.exp
    rw [hY]
    convert h2 using 1
    ring
  -- the key algebraic relation between `s`, `c` and `u`
  have hkc : ∀ x ∈ Ioo 0 m, k * c x = s x * u x := by
    intro x hx
    have hsx' : Real.sin (k * x) ≠ 0 := by
      simpa only [hs] using (hs_pos x hx).ne'
    simp only [hs, hc, hu]
    field_simp
  -- `u` solves the Riccati equation
  have hu_deriv : ∀ x ∈ Ioo 0 m, HasDerivAt u (-(u x ^ 2 + K)) x := by
    intro x hx
    have hsx' : Real.sin (k * x) ≠ 0 := by
      simpa only [hs] using (hs_pos x hx).ne'
    have hcos : HasDerivAt (fun y : ℝ => Real.cos (k * y)) (-(k * s x)) x := by
      simpa only [hc] using hc_deriv x
    have hsin : HasDerivAt (fun y : ℝ => Real.sin (k * y)) (k * c x) x := by
      simpa only [hs] using hs_deriv x
    have hdiv : HasDerivAt (fun y : ℝ => Real.cos (k * y) / Real.sin (k * y))
        (((-(k * s x)) * Real.sin (k * x) - Real.cos (k * x) * (k * c x))
          / Real.sin (k * x) ^ 2) x :=
      hcos.div hsin hsx'
    have hku := hdiv.const_mul k
    have heq : -((k * (Real.cos (k * x) / Real.sin (k * x))) ^ 2 + K)
        = k * (((-(k * s x)) * Real.sin (k * x) - Real.cos (k * x) * (k * c x))
          / Real.sin (k * x) ^ 2) := by
      simp only [hs, hc]
      field_simp
      rw [hk_sq]
      rw [show Real.cos (k * x) ^ 2 = 1 - Real.sin (k * x) ^ 2 from by
        linarith [Real.sin_sq_add_cos_sq (k * x)]]
      ring
    simp only [hu]
    rw [heq]
    exact hku
  -- `d = w - u`, `A = s * Y`, `q = A * d`
  set d : ℝ → ℝ := fun x => w x - u x with hd
  set A : ℝ → ℝ := fun x => s x * Y x with hA
  set q : ℝ → ℝ := fun x => A x * d x with hq
  have hA_deriv : ∀ x ∈ Ioo 0 T, HasDerivAt A (k * c x * Y x + s x * (w x * Y x)) x := by
    intro x hx
    have h := (hs_deriv x).mul (hY_deriv x hx)
    rw [hA]
    exact h
  have hd_deriv : ∀ x ∈ Ioo 0 m, HasDerivAt d (deriv w x + (u x ^ 2 + K)) x := by
    intro x hx
    have hxT : x ∈ Ioo 0 T := ⟨hx.1, lt_of_lt_of_le hx.2 hm_le_T⟩
    have h := (hw x hxT).sub (hu_deriv x hx)
    have heq : deriv w x + (u x ^ 2 + K) = deriv w x - (-(u x ^ 2 + K)) := by ring
    rw [hd, heq]
    exact h
  have hq_deriv : ∀ x ∈ Ioo 0 m,
      HasDerivAt q (s x * Y x * (deriv w x + w x ^ 2 + K)) x := by
    intro x hx
    have hxT : x ∈ Ioo 0 T := ⟨hx.1, lt_of_lt_of_le hx.2 hm_le_T⟩
    have h1 : HasDerivAt (fun y => A y * d y)
        ((k * c x * Y x + s x * (w x * Y x)) * d x
          + A x * (deriv w x + (u x ^ 2 + K))) x :=
      (hA_deriv x hxT).mul (hd_deriv x hx)
    have heq : s x * Y x * (deriv w x + w x ^ 2 + K)
        = (k * c x * Y x + s x * (w x * Y x)) * d x
          + A x * (deriv w x + (u x ^ 2 + K)) := by
      simp only [hA, hd]
      rw [hkc x hx]
      ring
    rw [hq, heq]
    exact h1
  -- `z = Y / s`
  set z : ℝ → ℝ := fun x => Y x / s x with hz
  have hz_deriv : ∀ x ∈ Ioo 0 m, HasDerivAt z (q x / s x ^ 2) x := by
    intro x hx
    have hxT : x ∈ Ioo 0 T := ⟨hx.1, lt_of_lt_of_le hx.2 hm_le_T⟩
    have hsx : s x ≠ 0 := (hs_pos x hx).ne'
    have h := (hY_deriv x hxT).div (hs_deriv x) hsx
    have heq : q x / s x ^ 2 = (w x * Y x * s x - Y x * (k * c x)) / s x ^ 2 := by
      simp only [hq, hA, hd]
      rw [hkc x hx]
      field_simp
    rw [hz, heq]
    exact h
  intro t ht
  by_contra hcon
  have htT : t ∈ Ioo 0 T := ⟨ht.1, lt_of_lt_of_le ht.2 hm_le_T⟩
  have hst : 0 < s t := hs_pos t ht
  have hdt : 0 < d t := by
    have h1 : k * (Real.cos (k * t) / Real.sin (k * t)) < w t := not_le.mp hcon
    simp only [hd, hu]
    linarith
  have hqt : 0 < q t := by
    rw [hq]
    exact mul_pos (mul_pos hst (hY_pos t)) hdt
  set C : ℝ := q t / k ^ 2 with hC
  have hC_pos : 0 < C := div_pos hqt (pow_pos hk_pos 2)
  set psi : ℝ → ℝ := fun x => z x + C / x with hpsi
  have hpsi_deriv : ∀ x ∈ Ioo 0 m, HasDerivAt psi (q x / s x ^ 2 - C / x ^ 2) x := by
    intro x hx
    have hx0 : x ≠ 0 := hx.1.ne'
    have h2 : HasDerivAt (fun y : ℝ => C / y) (-(C / x ^ 2)) x := by
      have h3 : HasDerivAt (fun y : ℝ => C * y⁻¹) (C * (-(x ^ 2)⁻¹)) x :=
        (hasDerivAt_inv hx0).const_mul C
      have heq : C * (-(x ^ 2)⁻¹) = -(C / x ^ 2) := by field_simp
      rw [heq] at h3
      simpa only [div_eq_mul_inv] using h3
    have h4 := (hz_deriv x hx).add h2
    have heq : q x / s x ^ 2 - C / x ^ 2 = q x / s x ^ 2 + -(C / x ^ 2) := by ring
    rw [hpsi, heq]
    exact h4
  set B : ℝ := |z t| + C / t + 1 with hB
  have hB_pos : 0 < B := by
    have h : 0 < C / t := div_pos hC_pos ht.1
    have h2 : (0:ℝ) ≤ |z t| := abs_nonneg _
    rw [hB]
    linarith
  set x : ℝ := min (t / 2) (C / B) / 2 with hxdef
  have hx_pos : 0 < x := by
    rw [hxdef]
    exact half_pos (lt_min (half_pos ht.1) (div_pos hC_pos hB_pos))
  have hx_lt_t : x < t := by
    rw [hxdef]
    have h := min_le_left (t / 2) (C / B)
    linarith
  have hxI : x ∈ Ioo 0 m := ⟨hx_pos, lt_trans hx_lt_t ht.2⟩
  have hxIcc : x ∈ Icc x t := left_mem_Icc.mpr hx_lt_t.le
  have htIcc : t ∈ Icc x t := right_mem_Icc.mpr hx_lt_t.le
  have hq_anti : AntitoneOn q (Icc x t) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc x t) ?_ ?_ ?_
    · intro y hy
      have hyI : y ∈ Ioo 0 m := ⟨lt_of_lt_of_le hx_pos hy.1, lt_of_le_of_lt hy.2 ht.2⟩
      exact ((hq_deriv y hyI).continuousAt).continuousWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      have hyI : y ∈ Ioo 0 m := ⟨lt_trans hx_pos hy.1, lt_trans hy.2 ht.2⟩
      exact ((hq_deriv y hyI).differentiableAt).differentiableWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      have hyI : y ∈ Ioo 0 m := ⟨lt_trans hx_pos hy.1, lt_trans hy.2 ht.2⟩
      have hyT : y ∈ Ioo 0 T := ⟨hyI.1, lt_of_lt_of_le hyI.2 hm_le_T⟩
      rw [(hq_deriv y hyI).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (hs_pos y hyI).le (hY_pos y).le) (hineq y hyT)
  have hqt_le_hqx : q t ≤ q x := hq_anti hxIcc htIcc hx_lt_t.le
  have hqx_pos : 0 < q x := lt_of_lt_of_le hqt hqt_le_hqx
  have hpsi_mono : MonotoneOn psi (Icc x t) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc x t) ?_ ?_ ?_
    · intro y hy
      have hyI : y ∈ Ioo 0 m := ⟨lt_of_lt_of_le hx_pos hy.1, lt_of_le_of_lt hy.2 ht.2⟩
      exact ((hpsi_deriv y hyI).continuousAt).continuousWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      have hyI : y ∈ Ioo 0 m := ⟨lt_trans hx_pos hy.1, lt_trans hy.2 ht.2⟩
      exact ((hpsi_deriv y hyI).differentiableAt).differentiableWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      have hyI : y ∈ Ioo 0 m := ⟨lt_trans hx_pos hy.1, lt_trans hy.2 ht.2⟩
      rw [(hpsi_deriv y hyI).deriv]
      have hqy : q t ≤ q y := hq_anti ⟨hy.1.le, hy.2.le⟩ htIcc hy.2.le
      have hsy : 0 < s y := hs_pos y hyI
      have hsy2 : 0 < s y ^ 2 := pow_pos hsy 2
      have hy2 : 0 < y ^ 2 := pow_pos (lt_trans hx_pos hy.1) 2
      have h1 : q t / s y ^ 2 ≤ q y / s y ^ 2 := div_le_div_of_nonneg_right hqy hsy2.le
      have h3 : s y ^ 2 ≤ k ^ 2 * y ^ 2 := by
        have h4 := hsq_le y hyI
        nlinarith [h4]
      have h4 : C * s y ^ 2 ≤ q t * y ^ 2 := by
        rw [hC, div_mul_eq_mul_div, div_le_iff₀ (pow_pos hk_pos 2)]
        nlinarith [h3, hqt]
      have h5 : C / y ^ 2 ≤ q t / s y ^ 2 := by
        rw [div_le_div_iff₀ hy2 hsy2]
        exact h4
      linarith
  have hpsi_xt : psi x ≤ psi t := hpsi_mono hxIcc htIcc hx_lt_t.le
  have hCx : z t + C / t + 1 ≤ C / x := by
    have h1 : x ≤ C / B := by
      rw [hxdef]
      have h := min_le_right (t / 2) (C / B)
      linarith
    have h2 : x * B ≤ C := (le_div_iff₀ hB_pos).mp h1
    rw [mul_comm] at h2
    have h3 : B ≤ C / x := (le_div_iff₀ hx_pos).mpr h2
    rw [hB] at h3
    have h4 : z t + C / t + 1 ≤ |z t| + C / t + 1 := by
      have h5 := le_abs_self (z t)
      linarith
    linarith
  have hzx_neg : z x < 0 := by
    have h1 : psi x = z x + C / x := by rw [hpsi]
    have h2 : psi t = z t + C / t := by rw [hpsi]
    linarith
  have hzx_pos : 0 < z x := by
    rw [hz]
    exact div_pos (hY_pos x) (hs_pos x hxI)
  linarith

end Commons.Analysis.ODE