/-
# `APSwitchUpper.level_bounds` — the crude bounds `Cv n ≤ 4`, `Tv n ≤ 6`

The level constants of the delay calculus (`riPhiLevelCore`)

```
Cv n = ∫_2^{2n+4} oddSum n,      Tv n = ∫_3^{2n+3} evenSum n
```

are the partial sums of `∫_2^∞ riPsi` and `∫_3^∞ riPhi`; both are *increasing* and bounded,
so any crude pair of bounds makes the monotone-convergence argument run.  The true limits are
`C = 0.6409…` and `T = 0.0785…`; here we only need `Cv n ≤ 4` and `Tv n ≤ 6`.

* `Cv`: the *moment inequality* `moment_ineq` of `riPhiLevelCore`,

  `2·Cv (n+1) ≤ (4 − 3 log 3) + Cv n·(2 − log 3) − Tv (n+1)`,

  upgrades the hypothesis `Cv n ≤ 4` to `Cv (n+1) ≤ (4−3log3 + 4(2−log3))/2 = (12 − 7 log 3)/2 < 4`
  (using `log 3 > 1`), so only the base case `Cv 0 = ∫_2^4 profC 1 ≤ 4` must be checked by hand.
  That is done through the odd recursion `u·profC 1 u = ∫_{u-1}^3 profC 0` and the elementary
  pointwise bound `profC 0 t = (3−t)/t ≤ 2` on `[1,3]`.

* `Tv`: the crude supersolution pair `crudeU`, `crudeV` of `riPhiSharpCrude` dominates the
  partial sums (`crudePairHypotheses` + `apart_bpart_le_of_supersolution`), and
  `evenSum n s = apart (2n+2) s ≤ crudeU s`, whence

  `Tv n ≤ ∫_3^{2n+3} crudeU = 2·(1 − exp (3 − (2n+3))) ≤ 2 ≤ 6`.
-/
import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiLevelCore
import Submission.Work.NumberTheory.Chen.APSwitchUpper.moment_ineq
import Submission.Work.NumberTheory.Chen.APSwitchUpper.crudePairHypotheses
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhi_supersolution

namespace Work.NumberTheory.Chen.APSwitchUpper

open MeasureTheory Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## §1  `evenSum` is the `apart` partial sum -/

theorem level_evenSum_eq_apart (N : ℕ) (s : ℝ) : evenSum N s = apart (2 * N + 2) s := by
  unfold evenSum apart
  have hsub : (Finset.range (2 * N + 2)).filter (fun j => j % 2 = 0)
      = (Finset.range (N + 1)).image (fun k => 2 * k) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hj, hje⟩
      refine ⟨j / 2, by omega, ?_⟩
      rw [Nat.mul_comm]
      exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hje)
    · rintro ⟨k, hk, rfl⟩
      exact ⟨by omega, Nat.mul_mod_right 2 k⟩
  rw [hsub, Finset.sum_image]
  intro a _ b _ hab
  exact Nat.mul_left_cancel (by norm_num : 0 < 2) hab

/-! ## §2  The crude majorant bounds the partial sums -/

/-- **Comparison principle, level by level** (verbatim copy of
`crudeLevelBounds.apart_bpart_le_of_supersolution`, inlined here so that every module in this
file's import closure is fully proved).

If `U, V ≥ 0` satisfy the two supersolution inequalities of the delay system at `s ≥ 2` and the
linear bound `t·U t ≥ 3 − t + 3U 3` on `[1,3]`, then every partial level of the `profC` family
is dominated by `U`, `V`. -/
theorem level_apart_bpart_le_of_supersolution {U V : ℝ → ℝ}
    (hU0 : ∀ s, 0 ≤ U s) (hV0 : ∀ s, 0 ≤ V s)
    (hVint : ∀ a b : ℝ, IntervalIntegrable V volume a b)
    (hUint : ∀ a b : ℝ, IntervalIntegrable U volume a b)
    (hUV : ∀ s : ℝ, 2 ≤ s → ∀ b : ℝ, max (s - 1) 2 ≤ b →
      (3 - s) * (if s ≤ 3 then (1:ℝ) else 0) + ∫ u in (max (s - 1) 2)..b, V u ≤ s * U s)
    (hVU : ∀ s : ℝ, 2 ≤ s → ∀ b : ℝ, s - 1 ≤ b → ∫ u in (s - 1)..b, U u ≤ s * V s)
    (hlin : ∀ t : ℝ, 1 ≤ t → t ≤ 3 → (3 - t + 3 * U 3) / t ≤ U t) :
    (∀ N : ℕ, ∀ s : ℝ, 2 ≤ s → apart N s ≤ U s)
      ∧ (∀ N : ℕ, ∀ s : ℝ, 2 ≤ s → bpart N s ≤ V s) := by
  have key : ∀ N : ℕ, ∀ t : ℝ, 2 ≤ t → apart N t ≤ U t ∧ bpart N t ≤ V t := by
    intro N
    induction N with
    | zero => intro t ht; exact ⟨by simp [apart, hU0 t], by simp [bpart, hV0 t]⟩
    | succ N ih =>
      intro t ht
      have hN1 : 1 ≤ N + 1 := Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero N)
      have hsub : (N + 1 : ℕ) - 1 = N := by omega
      constructor
      · by_cases hbig : (((N + 1 : ℕ)) : ℝ) + 2 < t
        · rw [apart_eq_zero (le_of_lt hbig)]; exact hU0 t
        · have htN : t ≤ (((N + 1 : ℕ)) : ℝ) + 2 := le_of_not_gt hbig
          have h := apart_mul_eq (N := N + 1) ht hN1 htN
          rw [hsub] at h
          have hN2 : max (t - 1) 2 ≤ (((N + 1 : ℕ)) : ℝ) + 1 := by
            refine max_le (by linarith [htN]) ?_
            push_cast; exact_mod_cast (by omega : 2 ≤ N + 1 + 1)
          have hmono : (∫ u in (max (t - 1) 2)..((((N + 1 : ℕ)) : ℝ) + 1), bpart N u)
              ≤ ∫ u in (max (t - 1) 2)..((((N + 1 : ℕ)) : ℝ) + 1), V u := by
            refine intervalIntegral.integral_mono_on (by linarith)
              (bpart_intervalIntegrable N _ _) (hVint _ _) ?_
            intro x hx
            have hx2 : (2:ℝ) ≤ x := le_trans (le_max_right _ _) hx.1
            exact (ih x hx2).2
          have h3 : (3 - t) * (if t ≤ 3 then (1:ℝ) else 0)
              = (if t ≤ 3 then 3 - t else 0) := by
            by_cases h : t ≤ 3
            · rw [if_pos h, if_pos h]; ring
            · rw [if_neg h, if_neg h]; ring
          have hb := hUV t ht ((((N + 1 : ℕ)) : ℝ) + 1) hN2
          rw [h3] at hb
          have hmul : apart (N + 1) t * t ≤ U t * t := by
            rw [mul_comm (apart (N + 1) t) t, h, mul_comm (U t) t]
            exact le_trans (add_le_add (le_refl _) hmono) hb
          exact le_of_mul_le_mul_right hmul (by linarith : (0:ℝ) < t)
      · by_cases hbig : (((N + 1 : ℕ)) : ℝ) + 2 < t
        · rw [bpart_eq_zero (le_of_lt hbig)]; exact hV0 t
        · have htN : t ≤ (((N + 1 : ℕ)) : ℝ) + 2 := le_of_not_gt hbig
          have h := bpart_mul_eq (N := N + 1) ht hN1 htN
          rw [hsub] at h
          have hN2 : t - 1 ≤ (((N + 1 : ℕ)) : ℝ) + 1 := by linarith [htN]
          have hmono : (∫ u in (t - 1)..((((N + 1 : ℕ)) : ℝ) + 1), apart N u)
              ≤ ∫ u in (t - 1)..((((N + 1 : ℕ)) : ℝ) + 1), U u := by
            refine intervalIntegral.integral_mono_on (by linarith)
              (apart_intervalIntegrable N _ _) (hUint _ _) ?_
            intro x hx
            by_cases hx2 : (2:ℝ) ≤ x
            · exact (ih x hx2).1
            · by_cases hN0 : 1 ≤ N
              · have hx3 : x ≤ 3 := by linarith [hx2]
                have hx1 : 1 ≤ x := by linarith [hx.1, ht]
                have hA3 : apart N 3 ≤ U 3 := (ih 3 (by norm_num)).1
                have hlin' := hlin x hx1 hx3
                have hclamp := apart_linear hN0 hx1 hx3
                have hxpos : (0:ℝ) < x := by linarith
                rw [div_le_iff₀ hxpos] at hlin'
                have hxx : x * apart N x = (3 - x) + 3 * apart N 3 := by linarith
                have : x * apart N x ≤ x * U x := by
                  rw [hxx]; nlinarith [hA3, hlin']
                exact le_of_mul_le_mul_left this hxpos
              · have hNz : N = 0 := by omega
                subst hNz
                simp only [apart, Finset.range_zero, Finset.filter_empty, Finset.sum_empty]
                exact hU0 x
          have hb := hVU t ht ((((N + 1 : ℕ)) : ℝ) + 1) hN2
          have hmul : bpart (N + 1) t * t ≤ V t * t := by
            rw [mul_comm (bpart (N + 1) t) t, h, mul_comm (V t) t]
            exact le_trans hmono hb
          exact le_of_mul_le_mul_right hmul (by linarith : (0:ℝ) < t)
  exact ⟨fun N s hs => (key N s hs).1, fun N s hs => (key N s hs).2⟩

theorem level_apart_bpart_crude :
    (∀ N : ℕ, ∀ s : ℝ, 2 ≤ s → apart N s ≤ crudeU s)
      ∧ (∀ N : ℕ, ∀ s : ℝ, 2 ≤ s → bpart N s ≤ crudeV s) :=
  level_apart_bpart_le_of_supersolution crudeU_nonneg crudeV_nonneg
    crudePairHypotheses.2.1 crudePairHypotheses.1
    crudePairHypotheses.2.2.2.2.1 crudePairHypotheses.2.2.2.2.2
    (fun t h1 h3 => crudeU_linear t h1 h3)

theorem level_evenSum_le_crudeU (n : ℕ) {s : ℝ} (hs : 2 ≤ s) : evenSum n s ≤ crudeU s := by
  rw [level_evenSum_eq_apart]
  exact level_apart_bpart_crude.1 (2 * n + 2) s hs

/-! ## §3  `Tv n ≤ 2` -/

theorem level_crudeU_integral (M : ℝ) (hM : 3 ≤ M) :
    ∫ u in (3 : ℝ)..M, crudeU u = 2 * (1 - Real.exp (3 - M)) := by
  have hcongr : (∫ u in (3 : ℝ)..M, crudeU u)
      = ∫ u in (3 : ℝ)..M, 2 * Real.exp (3 - u) :=
    intervalIntegral.integral_congr (fun u hu => crudeU_of_three_le (uIcc_left hM hu))
  rw [hcongr, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_left (fun x : ℝ => Real.exp x) 3,
    integral_exp]
  rw [show (3 : ℝ) - 3 = 0 by norm_num, Real.exp_zero]

theorem level_Tv_le_two (n : ℕ) : Tv n ≤ 2 := by
  have hM : (3 : ℝ) ≤ ((2 * n + 3 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 3 ≤ 2 * n + 3)
  have hmono : (∫ u in (3 : ℝ)..((2 * n + 3 : ℕ) : ℝ), evenSum n u)
      ≤ ∫ u in (3 : ℝ)..((2 * n + 3 : ℕ) : ℝ), crudeU u :=
    intervalIntegral.integral_mono_on hM (evenSum_intervalIntegrable n _ _)
      (crudePairHypotheses.1 _ _) (fun u hu => level_evenSum_le_crudeU n (by linarith [hu.1]))
  have hcv := level_crudeU_integral ((2 * n + 3 : ℕ) : ℝ) hM
  rw [hcv] at hmono
  rw [Tv]
  have hpos : 0 < Real.exp (3 - ((2 * n + 3 : ℕ) : ℝ)) := Real.exp_pos _
  have hle1 : Real.exp (3 - ((2 * n + 3 : ℕ) : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  linarith

/-! ## §4  Two logarithm bounds -/

theorem level_log_three_gt_one : (1 : ℝ) < Real.log 3 :=
  (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).mpr Real.exp_one_lt_three

theorem level_log_three_le_two : Real.log 3 ≤ 2 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
  norm_num at h
  exact h

/-! ## §5  The base case `Cv 0 = ∫_2^4 profC 1 ≤ 4` -/

theorem level_profC_one_le_two {u : ℝ} (hu : 2 ≤ u) : profC 1 u ≤ 2 := by
  rcases le_or_gt u 4 with hu4 | hu4
  · have hmul : u * profC 1 u = ∫ t in (u - 1)..(3 : ℝ), profC 0 t := by
      have h := profC_odd_mul 0 u hu
      simpa only [profTail_eq_integral, Nat.mul_zero, Nat.zero_add, Nat.cast_zero, zero_add,
        Nat.add_zero] using h
    have hpt : ∀ t ∈ Set.Icc (u - 1) 3, profC 0 t ≤ (2 : ℝ) := by
      intro t ht
      have ht1 : (1 : ℝ) ≤ t := by linarith [ht.1, hu]
      rw [profC_zero, if_pos ⟨ht1, ht.2⟩]
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < t)]
      linarith
    have hmono : (∫ t in (u - 1)..(3 : ℝ), profC 0 t)
        ≤ ∫ t in (u - 1)..(3 : ℝ), (2 : ℝ) :=
      intervalIntegral.integral_mono_on (by linarith : u - 1 ≤ 3)
        (profC_intervalIntegrable 0 _ _) intervalIntegrable_const hpt
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    have hu0 : (0 : ℝ) < u := by linarith
    have key : u * profC 1 u ≤ u * 2 := by
      rw [hmul]
      nlinarith [hmono]
    exact le_of_mul_le_mul_left key hu0
  · have hz : profC 1 u = 0 := profC_support 1 u (by push_cast; linarith)
    rw [hz]; norm_num

theorem level_Cv_zero_le_four : Cv 0 ≤ 4 := by
  have hsum : oddSum 0 = profC 1 := by
    funext s
    rw [oddSum]
    rw [show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one]
  have hbound : ((2 * 0 + 4 : ℕ) : ℝ) = (4 : ℝ) := by norm_num
  have hCv : Cv 0 = ∫ u in (2 : ℝ)..(4 : ℝ), profC 1 u := by
    rw [Cv, hsum, hbound]
  rw [hCv]
  have hmono : (∫ u in (2 : ℝ)..(4 : ℝ), profC 1 u)
      ≤ ∫ u in (2 : ℝ)..(4 : ℝ), (2 : ℝ) :=
    intervalIntegral.integral_mono_on (by norm_num) (profC_intervalIntegrable 1 _ _)
      intervalIntegrable_const (fun u hu => level_profC_one_le_two hu.1)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  linarith

/-! ## §6  The induction for `Cv` and the theorem -/

theorem level_Cv_le_four (n : ℕ) : Cv n ≤ 4 := by
  induction n with
  | zero => exact level_Cv_zero_le_four
  | succ n ih =>
    have h := moment_ineq n
    have hTv : (0 : ℝ) ≤ Tv (n + 1) := Tv_nonneg (n + 1)
    have hlog : (0 : ℝ) ≤ 2 - Real.log 3 := by linarith [level_log_three_le_two]
    have hmul : Cv n * (2 - Real.log 3) ≤ 4 * (2 - Real.log 3) :=
      mul_le_mul_of_nonneg_right ih hlog
    have hkey : 2 * Cv (n + 1) ≤ 8 := by
      linarith [h, hmul, hTv, level_log_three_gt_one]
    linarith

theorem level_Tv_le_six (n : ℕ) : Tv n ≤ 6 :=
  le_trans (level_Tv_le_two n) (by norm_num)

theorem level_bounds :
    (∀ n : ℕ, Cv n ≤ 4) ∧ (∀ n : ℕ, Tv n ≤ 6) :=
  ⟨level_Cv_le_four, level_Tv_le_six⟩

end

end Work.NumberTheory.Chen.APSwitchUpper
