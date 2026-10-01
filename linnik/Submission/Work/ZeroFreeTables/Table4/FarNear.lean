/-
# ZeroFreeTables/Table4/FarNear — the near/far split of the `P₃` explicit formula

Ingredients of the HB §8.2 engine: the pointwise far bounds for the square and cube
terms of the `P₃` weight, the summability of the inverse-square zero kernel, and the
near/far inequalities for the square and cube zero sums with a *prescribed* extra set
of zeros kept (the three specific zeros `ρ₁, ρ₀, ρ̄₀` whose contributions (8.7) needs).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P9.Defs
import Submission.Work.LinnikAreas.FarRepel.zeroMult_eq_analyticOrderNatAt_of_isPrimitive
import Submission.Work.LinnikAreas.ownRepelNW.orderSum_invSq_bound_of_count
import Submission.Work.LinnikAreas.A5.LFunction_disc_zeroCount

namespace Work.ZeroFreeTables.Table4

open DirichletCharacter Complex
open scoped Classical BigOperators

/-- Zeros of a primitive non-principal `L`-function have `Re u < 1`. -/
theorem zeroMult_re_lt_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {u : ℂ} (hu : Work.LinnikContract.zeroMult χ u ≠ 0) :
    u.re < 1 := by
  have h1 : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u ≠ 0 := by
    rw [← Work.LinnikAreas.FarRepel.zeroMult_eq_analyticOrderNatAt_of_isPrimitive χ hprim u]
    exact hu
  have h2 : DirichletCharacter.completedLFunction χ u = 0 :=
    apply_eq_zero_of_analyticOrderNatAt_ne_zero h1
  exact (Commons.NumberTheory.Linnik.completedL_zero_strip χ hχ hprim h2).2

/-- **Pointwise far bound, square.**  Outside the near disk `‖1 + i·Im s - u‖ > δ`
one has `Re (1/(s-u))² ≥ -((1+4/δ²)/(1+‖s-u‖²))`. -/
theorem quad_far_re_bound {s u : ℂ} {δ : ℝ} (hδ : 0 < δ) (hs : 1 ≤ s.re)
    (hsδ : s.re ≤ 1 + δ / 2)
    (hfar : δ < ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖) :
    -((1 + 4 / δ ^ 2) / (1 + ‖s - u‖ ^ 2)) ≤ ((1 / (s - u)) ^ 2).re := by
  have hdecomp : s - u
      = ((1 : ℂ) + (s.im : ℂ) * Complex.I - u) + ((s.re - 1 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp <;> ring
  have hr : δ / 2 < ‖s - u‖ := by
    rw [hdecomp]
    have h1 : ‖((s.re - 1 : ℝ) : ℂ)‖ = |s.re - 1| := RCLike.norm_ofReal _
    have h2 : ‖(1 : ℂ) + (s.im:ℂ)*Complex.I - u + ((s.re - 1 : ℝ) : ℂ)‖
        ≥ ‖(1 : ℂ) + (s.im:ℂ)*Complex.I - u‖ - ‖((s.re - 1 : ℝ) : ℂ)‖ := by
      have := norm_sub_le (((1 : ℂ) + (s.im:ℂ)*Complex.I - u) + ((s.re - 1 : ℝ) : ℂ))
        (((s.re - 1 : ℝ) : ℂ))
      rw [add_sub_cancel_right] at this
      linarith
    rw [h1] at h2
    have h3 : |s.re - 1| = s.re - 1 := abs_of_nonneg (by linarith)
    rw [h3] at h2
    linarith
  have hrpos : 0 < ‖s - u‖ := by linarith
  have hx2 : (s - u).re ^ 2 + (s - u).im ^ 2 = ‖s - u‖ ^ 2 := by
    rw [Complex.sq_norm (s - u), Complex.normSq_apply]; ring
  have hxpos : 0 < (s - u).re ^ 2 + (s - u).im ^ 2 := by rw [hx2]; exact pow_pos hrpos 2
  have hkey : -(1 / ‖s - u‖ ^ 2) ≤ ((1 / (s - u)) ^ 2).re := by
    have hns : Complex.normSq (s - u) = ‖s - u‖ ^ 2 := (Complex.sq_norm (s - u)).symm
    have hsq : ((1 / (s - u)) ^ 2).re
        = ((s - u).re ^ 2 - (s - u).im ^ 2) / (Complex.normSq (s - u)) ^ 2 := by
      have h1 : (1 / (s - u)).re = (s - u).re / Complex.normSq (s - u) := by
        rw [one_div, Complex.inv_re]
      have h2 : (1 / (s - u)).im = -((s - u).im) / Complex.normSq (s - u) := by
        rw [one_div, Complex.inv_im, neg_div]
      rw [pow_two, Complex.mul_re, h1, h2]; ring
    rw [hsq, hns, ← hx2]
    rw [show -(1 / ((s - u).re ^ 2 + (s - u).im ^ 2))
        = (-((s - u).re ^ 2 + (s - u).im ^ 2)) / ((s - u).re ^ 2 + (s - u).im ^ 2) ^ 2 by
          field_simp]
    rw [div_le_div_iff_of_pos_right (pow_pos hxpos 2)]
    nlinarith [sq_nonneg ((s - u).re), sq_nonneg ((s - u).im)]
  have hx : δ ^ 2 / 4 < ‖s - u‖ ^ 2 := by nlinarith [hr, hδ]
  have hstep : 1 / ‖s - u‖ ^ 2 ≤ (1 + 4 / δ ^ 2) / (1 + ‖s - u‖ ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h4 : (0:ℝ) < 4 / δ ^ 2 := by positivity
    have key : 1 ≤ (4 / δ ^ 2) * ‖s - u‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_left hx.le (le_of_lt h4)
      rwa [show (4/δ^2) * (δ^2/4) = 1 by field_simp] at this
    nlinarith [key]
  linarith

/-- **Pointwise far bound, cube.**  Outside the near disk `‖1 + i·Im s - u‖ > δ`,
`Re (1/(s-u))³ ≥ -((2/δ)(1+4/δ²))/(1+‖s-u‖²)`. -/
theorem cubic_far_re_bound {s u : ℂ} {δ : ℝ} (hδ : 0 < δ) (hs : 1 ≤ s.re)
    (hsδ : s.re ≤ 1 + δ / 2)
    (hfar : δ < ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖) :
    -((2 / δ) * (1 + 4 / δ ^ 2) / (1 + ‖s - u‖ ^ 2)) ≤ ((1 / (s - u)) ^ 3).re := by
  have hdecomp : s - u
      = ((1 : ℂ) + (s.im : ℂ) * Complex.I - u) + ((s.re - 1 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp <;> ring
  have hr : δ / 2 < ‖s - u‖ := by
    rw [hdecomp]
    have h1 : ‖((s.re - 1 : ℝ) : ℂ)‖ = |s.re - 1| := RCLike.norm_ofReal _
    have h2 : ‖(1 : ℂ) + (s.im:ℂ)*Complex.I - u + ((s.re - 1 : ℝ) : ℂ)‖
        ≥ ‖(1 : ℂ) + (s.im:ℂ)*Complex.I - u‖ - ‖((s.re - 1 : ℝ) : ℂ)‖ := by
      have := norm_sub_le (((1 : ℂ) + (s.im:ℂ)*Complex.I - u) + ((s.re - 1 : ℝ) : ℂ))
        (((s.re - 1 : ℝ) : ℂ))
      rw [add_sub_cancel_right] at this
      linarith
    rw [h1] at h2
    have h3 : |s.re - 1| = s.re - 1 := abs_of_nonneg (by linarith)
    rw [h3] at h2
    linarith
  have hrpos : 0 < ‖s - u‖ := by linarith
  have hnorm3 : ‖(1 / (s - u)) ^ 3‖ = (1 / ‖s - u‖) ^ 3 := by
    rw [norm_pow, norm_div, norm_one]
  have hre : |((1 / (s - u)) ^ 3).re| ≤ (1 / ‖s - u‖) ^ 3 :=
    (Complex.abs_re_le_norm _).trans_eq hnorm3
  have hkey : (1 / ‖s - u‖) ^ 3
      ≤ (2 / δ) * (1 + 4 / δ ^ 2) * (1 / (1 + ‖s - u‖ ^ 2)) := by
    have hC : (2 / δ) * (1 + 4 / δ ^ 2) = 2 / δ + 8 / δ ^ 3 := by field_simp; ring
    rw [hC, div_pow, one_pow, mul_one_div,
      le_div_iff₀ (by positivity : (0:ℝ) < 1 + ‖s - u‖ ^ 2)]
    have heq : (1:ℝ) / ‖s - u‖ ^ 3 * (1 + ‖s - u‖ ^ 2)
        = 1 / ‖s - u‖ ^ 3 + 1 / ‖s - u‖ := by
      field_simp [ne_of_gt hrpos]
    rw [heq]
    have hlt1 : 1 / ‖s - u‖ < 2 / δ := by
      have h := one_div_lt_one_div_of_lt (show (0:ℝ) < δ / 2 by linarith) hr
      rwa [one_div_div] at h
    have hlt3 : 1 / ‖s - u‖ ^ 3 < 8 / δ ^ 3 := by
      have hpow : (δ / 2) ^ 3 < ‖s - u‖ ^ 3 :=
        pow_lt_pow_left₀ hr (by linarith : (0:ℝ) ≤ δ / 2) (by norm_num)
      have h := one_div_lt_one_div_of_lt (by positivity : (0:ℝ) < (δ / 2) ^ 3) hpow
      have heq : (1:ℝ) / (δ / 2) ^ 3 = 8 / δ ^ 3 := by field_simp; ring
      rwa [heq] at h
    linarith
  rw [show (2 / δ) * (1 + 4 / δ ^ 2) / (1 + ‖s - u‖ ^ 2)
      = (2 / δ) * (1 + 4 / δ ^ 2) * (1 / (1 + ‖s - u‖ ^ 2)) by ring]
  linarith [neg_le_of_abs_le hre, hkey]

end Work.ZeroFreeTables.Table4

namespace Work.ZeroFreeTables.Table4

/-- The kept-set indicator: near the point `1 + i Im s` (`δ`-disk) or in the prescribed
finite set `S` of zeros whose `P₃`-contributions are kept. -/
noncomputable def keptInd (S : Finset ℂ) (s : ℂ) (δ : ℝ) (u : ℂ) : ℝ :=
  if u ∈ S ∨ ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then 1 else 0

theorem keptInd_nonneg (S : Finset ℂ) (s : ℂ) (δ : ℝ) (u : ℂ) : 0 ≤ keptInd S s δ u := by
  unfold keptInd; split <;> norm_num

theorem keptInd_le_one (S : Finset ℂ) (s : ℂ) (δ : ℝ) (u : ℂ) : keptInd S s δ u ≤ 1 := by
  unfold keptInd; split <;> norm_num

theorem keptInd_eq_ite (S : Finset ℂ) (s : ℂ) (δ : ℝ) (u : ℂ) :
    keptInd S s δ u = if u ∈ S ∨ ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then 1 else 0 := rfl

/-- The multiplicity-weighted inverse-square zero kernel is summable (uniform ball count). -/
theorem invSq_summable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) (s : ℂ) :
    Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2))) := by
  obtain ⟨c, hcpos, hc⟩ := Work.LinnikAreas.A5.ball_zeroCount_uniformL_A5
  obtain ⟨C, hCpos, hC⟩ := Work.LinnikAreas.ownRepelNW.orderSum_invSq_bound_of_count hcpos.le
  have hlogN : (0 : ℝ) ≤ Real.log (N : ℝ) := by
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast NeZero.one_le
    exact Real.log_nonneg hN1
  have hΛan : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  have hfin : ∀ T : Finset ℂ, ∑ u ∈ T,
      (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ)
        * (1 / (1 + ‖s - u‖ ^ 2))
      ≤ C * (Real.log (2 + ‖s‖) + Real.log (N : ℝ) + 2) := by
    intro T
    exact hC (DirichletCharacter.completedLFunction χ) hΛan (Real.log (N : ℝ)) hlogN
      (fun a ρ hρ => hc χ hχ hprim a ρ hρ) s T
  have hnn : ∀ u : ℂ, 0 ≤ (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ)
      * (1 / (1 + ‖s - u‖ ^ 2)) := by
    intro u
    have : (0 : ℝ) ≤ 1 / (1 + ‖s - u‖ ^ 2) := by positivity
    positivity
  have hsumm : Summable (fun u : ℂ =>
      (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ)
        * (1 / (1 + ‖s - u‖ ^ 2))) :=
    summable_of_sum_le hnn hfin
  exact hsumm.congr (fun u => by
    rw [← Work.LinnikAreas.FarRepel.zeroMult_eq_analyticOrderNatAt_of_isPrimitive χ hprim u])

/-- **Pointwise far bound with a kept set, cube.** -/
theorem cubicKept_far_bound {s u : ℂ} {δ : ℝ} (hδ : 0 < δ) (hs : 1 ≤ s.re)
    (hsδ : s.re ≤ 1 + δ / 2) (S : Finset ℂ) :
    |(1 - keptInd S s δ u) * ((1 / (s - u)) ^ 3).re|
      ≤ (2 / δ) * (1 + 4 / δ ^ 2) * (1 / (1 + ‖s - u‖ ^ 2)) := by
  classical
  by_cases hkeep : u ∈ S ∨ ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
  · have hki : keptInd S s δ u = 1 := by rw [keptInd_eq_ite, if_pos hkeep]
    rw [hki, sub_self, zero_mul, abs_zero]
    positivity
  · have hki : keptInd S s δ u = 0 := by rw [keptInd_eq_ite, if_neg hkeep]
    rw [hki, sub_zero, one_mul]
    have hfar : δ < ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ := by
      by_contra h
      exact hkeep (Or.inr (not_lt.mp h))
    have hnorm3 : ‖(1 / (s - u)) ^ 3‖ = (1 / ‖s - u‖) ^ 3 := by
      rw [norm_pow, norm_div, norm_one]
    have hre : |((1 / (s - u)) ^ 3).re| ≤ (1 / ‖s - u‖) ^ 3 :=
      (Complex.abs_re_le_norm _).trans_eq hnorm3
    -- ‖s - u‖ > δ/2
    have hdecomp : s - u
        = ((1 : ℂ) + (s.im : ℂ) * Complex.I - u) + ((s.re - 1 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp <;> ring
    have hr : δ / 2 < ‖s - u‖ := by
      rw [hdecomp]
      have h1 : ‖((s.re - 1 : ℝ) : ℂ)‖ = |s.re - 1| := RCLike.norm_ofReal _
      have h2 : ‖(1 : ℂ) + (s.im:ℂ)*Complex.I - u + ((s.re - 1 : ℝ) : ℂ)‖
          ≥ ‖(1 : ℂ) + (s.im:ℂ)*Complex.I - u‖ - ‖((s.re - 1 : ℝ) : ℂ)‖ := by
        have := norm_sub_le (((1 : ℂ) + (s.im:ℂ)*Complex.I - u) + ((s.re - 1 : ℝ) : ℂ))
          (((s.re - 1 : ℝ) : ℂ))
        rw [add_sub_cancel_right] at this
        linarith
      rw [h1] at h2
      have h3 : |s.re - 1| = s.re - 1 := abs_of_nonneg (by linarith)
      rw [h3] at h2
      linarith
    have hrpos : 0 < ‖s - u‖ := by linarith
    have hkey : (1 / ‖s - u‖) ^ 3
        ≤ (2 / δ) * (1 + 4 / δ ^ 2) * (1 / (1 + ‖s - u‖ ^ 2)) := by
      have hC : (2 / δ) * (1 + 4 / δ ^ 2) = 2 / δ + 8 / δ ^ 3 := by field_simp; ring
      rw [hC, div_pow, one_pow, mul_one_div,
        le_div_iff₀ (by positivity : (0:ℝ) < 1 + ‖s - u‖ ^ 2)]
      have heq : (1:ℝ) / ‖s - u‖ ^ 3 * (1 + ‖s - u‖ ^ 2)
          = 1 / ‖s - u‖ ^ 3 + 1 / ‖s - u‖ := by
        field_simp [ne_of_gt hrpos]
      rw [heq]
      have hlt1 : 1 / ‖s - u‖ < 2 / δ := by
        have h := one_div_lt_one_div_of_lt (show (0:ℝ) < δ / 2 by linarith) hr
        rwa [one_div_div] at h
      have hlt3 : 1 / ‖s - u‖ ^ 3 < 8 / δ ^ 3 := by
        have hpow : (δ / 2) ^ 3 < ‖s - u‖ ^ 3 :=
          pow_lt_pow_left₀ hr (by linarith : (0:ℝ) ≤ δ / 2) (by norm_num)
        have h := one_div_lt_one_div_of_lt (by positivity : (0:ℝ) < (δ / 2) ^ 3) hpow
        have heq : (1:ℝ) / (δ / 2) ^ 3 = 8 / δ ^ 3 := by field_simp; ring
        rwa [heq] at h
      linarith
    linarith [hre.trans hkey]

end Work.ZeroFreeTables.Table4

namespace Work.ZeroFreeTables.Table4

open scoped BigOperators

/-- **Near/far for the square term, with a prescribed kept set.** -/
theorem quadNearFar_kept {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {s : ℂ} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hs : 1 < s.re)
    (hsδ : s.re ≤ 1 + δ / 2)
    (hsum : Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 2))
    (S : Finset ℂ) :
    -(∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 2).re
      ≤ -(∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * keptInd S s δ u
            * ((1 / (s - u)) ^ 2).re)
        + (1 + 4 / δ ^ 2) * (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ)
            * (1 / (1 + ‖s - u‖ ^ 2))) := by
  classical
  have hRf : Summable (fun u : ℂ =>
      (Work.LinnikContract.zeroMult χ u : ℝ) * ((1 / (s - u)) ^ 2).re) := by
    have h1 : Summable (fun u : ℂ =>
        ((Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 2).re) :=
      Summable.of_norm_bounded hsum.norm
        (fun u => by rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _)
    exact h1.congr (fun u => by simp [Complex.mul_re])
  have hK : Summable (fun u : ℂ =>
      (Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2))) :=
    invSq_summable χ hχ hprim s
  -- the kept part
  have hG : Summable (fun u : ℂ =>
      (Work.LinnikContract.zeroMult χ u : ℝ) * keptInd S s δ u * ((1 / (s - u)) ^ 2).re) := by
    refine Summable.of_norm_bounded (f := fun u : ℂ =>
      (Work.LinnikContract.zeroMult χ u : ℝ) * keptInd S s δ u * ((1 / (s - u)) ^ 2).re)
      (g := fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ) * |((1 / (s - u)) ^ 2).re|) ?_ ?_
    · exact hRf.norm.congr (fun u => by
        rw [Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (show (0:ℝ) ≤ (Work.LinnikContract.zeroMult χ u : ℝ) by positivity)])
    · intro u
      rw [Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg (show (0:ℝ) ≤ (Work.LinnikContract.zeroMult χ u : ℝ) by positivity),
        abs_of_nonneg (keptInd_nonneg S s δ u)]
      have h2 : keptInd S s δ u ≤ 1 := keptInd_le_one S s δ u
      have h5 : 0 ≤ ((Work.LinnikContract.zeroMult χ u : ℝ)) := by positivity
      have h3 : keptInd S s δ u * |((1 / (s - u)) ^ 2).re| ≤ 1 * |((1 / (s - u)) ^ 2).re| :=
        mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
      calc (Work.LinnikContract.zeroMult χ u : ℝ) * keptInd S s δ u * |((1 / (s - u)) ^ 2).re|
          = (Work.LinnikContract.zeroMult χ u : ℝ)
              * (keptInd S s δ u * |((1 / (s - u)) ^ 2).re|) := by ring
        _ ≤ (Work.LinnikContract.zeroMult χ u : ℝ) * (1 * |((1 / (s - u)) ^ 2).re|) :=
            mul_le_mul_of_nonneg_left h3 h5
        _ = (Work.LinnikContract.zeroMult χ u : ℝ) * |((1 / (s - u)) ^ 2).re| := by ring
  -- the pointwise bound
  have hpt : ∀ u : ℂ, 0 ≤ (Work.LinnikContract.zeroMult χ u : ℝ) * ((1 / (s - u)) ^ 2).re
      - (Work.LinnikContract.zeroMult χ u : ℝ) * keptInd S s δ u * ((1 / (s - u)) ^ 2).re
      + (1 + 4 / δ ^ 2) * ((Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2))) := by
    intro u
    have hMnn : (0 : ℝ) ≤ (Work.LinnikContract.zeroMult χ u : ℝ) := by positivity
    by_cases hkeep : u ∈ S ∨ ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
    · have hki : keptInd S s δ u = 1 := by rw [keptInd_eq_ite, if_pos hkeep]
      rw [hki]
      have : 0 ≤ (1 + 4 / δ ^ 2) * ((Work.LinnikContract.zeroMult χ u : ℝ)
          * (1 / (1 + ‖s - u‖ ^ 2))) := by positivity
      nlinarith
    · have hki : keptInd S s δ u = 0 := by rw [keptInd_eq_ite, if_neg hkeep]
      have hfar : δ < ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ := by
        by_contra h
        exact hkeep (Or.inr (not_lt.mp h))
      rw [hki]
      simp only [mul_zero, mul_one, sub_zero]
      by_cases hM : Work.LinnikContract.zeroMult χ u = 0
      · rw [hM]; simp
      · have hMpos : (0 : ℝ) < (Work.LinnikContract.zeroMult χ u : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero hM
        have hu : u.re < 1 := zeroMult_re_lt_one χ hχ hprim hM
        have hb := quad_far_re_bound hδ hs.le hsδ hfar
        have hge : 0 ≤ ((1 / (s - u)) ^ 2).re
            + (1 + 4 / δ ^ 2) * (1 / (1 + ‖s - u‖ ^ 2)) := by
          rw [mul_one_div]; linarith
        have hstep : 0 ≤ (Work.LinnikContract.zeroMult χ u : ℝ)
            * (((1 / (s - u)) ^ 2).re + (1 + 4 / δ ^ 2) * (1 / (1 + ‖s - u‖ ^ 2))) :=
          mul_nonneg hMpos.le hge
        have hgoal : (Work.LinnikContract.zeroMult χ u : ℝ) * ((1 / (s - u)) ^ 2).re
            + (1 + 4 / δ ^ 2) * ((Work.LinnikContract.zeroMult χ u : ℝ)
              * (1 / (1 + ‖s - u‖ ^ 2)))
            = (Work.LinnikContract.zeroMult χ u : ℝ)
              * (((1 / (s - u)) ^ 2).re + (1 + 4 / δ ^ 2) * (1 / (1 + ‖s - u‖ ^ 2))) := by ring
        rw [hgoal] at *
        linarith [hstep]
  -- sum
  have hsumm2 : Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ) * ((1 / (s - u)) ^ 2).re
      - (Work.LinnikContract.zeroMult χ u : ℝ) * keptInd S s δ u * ((1 / (s - u)) ^ 2).re
      + (1 + 4 / δ ^ 2) * ((Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2)))) :=
    ((hRf.sub hG).add (hK.mul_left (1 + 4 / δ ^ 2)))
  have hnn : 0 ≤ ∑' u : ℂ, ((Work.LinnikContract.zeroMult χ u : ℝ) * ((1 / (s - u)) ^ 2).re
      - (Work.LinnikContract.zeroMult χ u : ℝ) * keptInd S s δ u * ((1 / (s - u)) ^ 2).re
      + (1 + 4 / δ ^ 2) * ((Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2)))) :=
    tsum_nonneg hpt
  have hsplit : (∑' u : ℂ, ((Work.LinnikContract.zeroMult χ u : ℝ) * ((1 / (s - u)) ^ 2).re
      - (Work.LinnikContract.zeroMult χ u : ℝ) * keptInd S s δ u * ((1 / (s - u)) ^ 2).re
      + (1 + 4 / δ ^ 2) * ((Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2)))))
      = (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * ((1 / (s - u)) ^ 2).re)
        - (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * keptInd S s δ u * ((1 / (s - u)) ^ 2).re)
        + (1 + 4 / δ ^ 2) * (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ)
            * (1 / (1 + ‖s - u‖ ^ 2))) := by
    rw [Summable.tsum_add (hRf.sub hG) (hK.mul_left (1 + 4 / δ ^ 2)),
      Summable.tsum_sub hRf hG, Summable.tsum_mul_left (1 + 4 / δ ^ 2) hK]
  rw [hsplit] at hnn
  have hre : (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 2).re
      = ∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * ((1 / (s - u)) ^ 2).re := by
    rw [Complex.re_tsum hsum]
    exact tsum_congr (fun u => by simp [Complex.mul_re])
  rw [hre]
  linarith [hnn]

/-- **Near/far for the cube term, with a prescribed kept set.** -/
theorem cubicNearFar_kept {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {s : ℂ} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hs : 1 < s.re)
    (hsδ : s.re ≤ 1 + δ / 2)
    (hsum : Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 3))
    (S : Finset ℂ) :
    -(∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 3).re
      ≤ -(∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * keptInd S s δ u
            * ((1 / (s - u)) ^ 3).re)
        + (2 / δ) * (1 + 4 / δ ^ 2) * (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ)
            * (1 / (1 + ‖s - u‖ ^ 2))) := by
  classical
  have hRf : Summable (fun u : ℂ =>
      (Work.LinnikContract.zeroMult χ u : ℝ) * ((1 / (s - u)) ^ 3).re) := by
    have h1 : Summable (fun u : ℂ =>
        ((Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 3).re) :=
      Summable.of_norm_bounded hsum.norm
        (fun u => by rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _)
    exact h1.congr (fun u => by simp [Complex.mul_re])
  have hK : Summable (fun u : ℂ =>
      (Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2))) :=
    invSq_summable χ hχ hprim s
  -- the far part (complement of the kept set)
  have hHnorm : ∀ u : ℂ,
      ‖(Work.LinnikContract.zeroMult χ u : ℝ) * (1 - keptInd S s δ u)
          * ((1 / (s - u)) ^ 3).re‖
        ≤ (2 / δ) * (1 + 4 / δ ^ 2)
          * ((Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2))) := by
    intro u
    have hb := cubicKept_far_bound hδ hs.le hsδ (S := S) (u := u)
    have ha : 0 ≤ (Work.LinnikContract.zeroMult χ u : ℝ) := Nat.cast_nonneg _
    have hN : ‖(Work.LinnikContract.zeroMult χ u : ℝ)
          * (1 - keptInd S s δ u) * ((1 / (s - u)) ^ 3).re‖
        = (Work.LinnikContract.zeroMult χ u : ℝ)
          * |(1 - keptInd S s δ u) * ((1 / (s - u)) ^ 3).re| := by
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg ha]
      ring
    rw [hN]
    calc (Work.LinnikContract.zeroMult χ u : ℝ)
          * |(1 - keptInd S s δ u) * ((1 / (s - u)) ^ 3).re|
        ≤ (Work.LinnikContract.zeroMult χ u : ℝ)
          * ((2 / δ) * (1 + 4 / δ ^ 2) * (1 / (1 + ‖s - u‖ ^ 2))) :=
          mul_le_mul_of_nonneg_left hb ha
      _ = (2 / δ) * (1 + 4 / δ ^ 2)
          * ((Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2))) := by ring
  have hH : Summable (fun u : ℂ =>
      (Work.LinnikContract.zeroMult χ u : ℝ) * (1 - keptInd S s δ u)
        * ((1 / (s - u)) ^ 3).re) :=
    Summable.of_norm_bounded (hK.mul_left ((2 / δ) * (1 + 4 / δ ^ 2))) hHnorm
  -- the kept part is the real part minus the far part
  have hG : Summable (fun u : ℂ =>
      (Work.LinnikContract.zeroMult χ u : ℝ) * keptInd S s δ u * ((1 / (s - u)) ^ 3).re) :=
    (hRf.sub hH).congr (fun u => by ring)
  have hHlow : -((2 / δ) * (1 + 4 / δ ^ 2) * (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ)
        * (1 / (1 + ‖s - u‖ ^ 2))))
      ≤ (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * (1 - keptInd S s δ u)
          * ((1 / (s - u)) ^ 3).re) := by
    have hle : ∀ u : ℂ, -((2 / δ) * (1 + 4 / δ ^ 2)
          * ((Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2))))
        ≤ (Work.LinnikContract.zeroMult χ u : ℝ) * (1 - keptInd S s δ u)
          * ((1 / (s - u)) ^ 3).re := by
      intro u
      have hb := cubicKept_far_bound hδ hs.le hsδ (S := S) (u := u)
      have ha : 0 ≤ (Work.LinnikContract.zeroMult χ u : ℝ) := Nat.cast_nonneg _
      have hx : -|(1 - keptInd S s δ u) * ((1 / (s - u)) ^ 3).re|
          ≤ (1 - keptInd S s δ u) * ((1 / (s - u)) ^ 3).re := neg_abs_le _
      have h1 : (Work.LinnikContract.zeroMult χ u : ℝ)
            * (-|(1 - keptInd S s δ u) * ((1 / (s - u)) ^ 3).re|)
          ≤ (Work.LinnikContract.zeroMult χ u : ℝ)
            * ((1 - keptInd S s δ u) * ((1 / (s - u)) ^ 3).re) :=
        mul_le_mul_of_nonneg_left hx ha
      have h2 : (Work.LinnikContract.zeroMult χ u : ℝ)
            * |(1 - keptInd S s δ u) * ((1 / (s - u)) ^ 3).re|
          ≤ (2 / δ) * (1 + 4 / δ ^ 2)
            * ((Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2))) := by
        calc (Work.LinnikContract.zeroMult χ u : ℝ)
              * |(1 - keptInd S s δ u) * ((1 / (s - u)) ^ 3).re|
            ≤ (Work.LinnikContract.zeroMult χ u : ℝ)
              * ((2 / δ) * (1 + 4 / δ ^ 2) * (1 / (1 + ‖s - u‖ ^ 2))) :=
              mul_le_mul_of_nonneg_left hb ha
          _ = (2 / δ) * (1 + 4 / δ ^ 2)
              * ((Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2))) := by ring
      nlinarith [h1, h2]
    have hsumneg : Summable (fun u : ℂ => -((2 / δ) * (1 + 4 / δ ^ 2)
        * ((Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2))))) :=
      (hK.mul_left ((2 / δ) * (1 + 4 / δ ^ 2))).neg
    have h2 := Summable.tsum_le_tsum hle hsumneg hH
    have e1 : (∑' u : ℂ, -((2 / δ) * (1 + 4 / δ ^ 2)
          * ((Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2)))))
        = -((2 / δ) * (1 + 4 / δ ^ 2) * (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ)
            * (1 / (1 + ‖s - u‖ ^ 2)))) := by
      rw [tsum_neg, tsum_mul_left]
    rwa [e1] at h2
  -- assemble
  have hfin : (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * keptInd S s δ u
      * ((1 / (s - u)) ^ 3).re)
      = (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * ((1 / (s - u)) ^ 3).re)
        - (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * (1 - keptInd S s δ u)
          * ((1 / (s - u)) ^ 3).re) := by
    rw [← Summable.tsum_sub hRf hH]
    exact tsum_congr (fun u => by ring)
  have hre : (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 3).re
      = ∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * ((1 / (s - u)) ^ 3).re := by
    rw [Complex.re_tsum hsum]
    exact tsum_congr (fun u => by simp [Complex.mul_re])
  rw [hre, hfin]
  linarith [hHlow]

end Work.ZeroFreeTables.Table4
