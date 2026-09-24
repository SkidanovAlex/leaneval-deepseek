/-
# `APSwitchUpper.crudeLevelBounds` — the levels `A_N`, `B_N` are bounded by the crude pair

`apart N = A_N = Σ_{j<N, j even} profC j` and `bpart N = B_N = Σ_{j<N, j odd} profC j` are the
partial sums of the Rosser–Iwaniec profile family `profC` (see `APSwitchUpper/riPhi_supersolution`).

This file shows that the *crude supersolution pair* `crudeU`, `crudeV` of
`APSwitchUpper/riPhiSharpCrude` dominates these partial sums level by level:

* `apart N s ≤ crudeU s` and `bpart N s ≤ crudeV s` for every `N` and every `s ≥ 2`.

The proof is the level-by-level induction on `N` (the same induction that
`riPhi_le_of_supersolution` carries out internally), isolated here as the general comparison
principle `apart_bpart_le_of_supersolution`: given `U, V ≥ 0` with

```
(3−s)·1_{s≤3} + ∫_{max(s−1,2)}^b V ≤ s·U(s),      ∫_{s−1}^b U ≤ s·V(s)     (s ≥ 2, all b)
```

and the linear bound `(3−t+3U(3))/t ≤ U(t)` on `[1,3]`, the levels never exceed `U`, `V`.

## The two analytic inputs

* `crudeUV_aux`: `(3−s)·1_{s≤3} + ∫_{max(s−1,2)}^b crudeV ≤ s·crudeU s`.  Since
  `crudeV u = 6e^{2−u}`, the integral is `6(e^{2−a} − e^{2−b}) ≤ 6e^{2−a}` with
  `a = max (s−1) 2`; for `s ≤ 3` one has `a = 2` and both sides equal `9 − s`, for `s > 3`
  one has `a = s−1` and `6 ≤ 2s`.
* `crudeVU_aux`: `∫_{s−1}^b crudeU ≤ s·crudeV s`.  Here `crudeU u = (9−u)/u` on `[1,3]` and
  `2e^{3−u}` for `u ≥ 3`, so for `2 ≤ s ≤ 4`

  `∫_{s−1}^b crudeU ≤ ∫_{s−1}^3 (9−u)/u + ∫_3^∞ 2e^{3−u} = 9·log(3/(s−1)) + s − 2`,

  and it remains to check `9·log(3/t) + t − 1 ≤ 6(t+1)e^{1−t}` for `t = s−1 ∈ [1,3]`
  (the companion files `logExpLeft`/`logExpRight`).  For `s ≥ 4` the integral is
  `≤ 2e^{4−s} ≤ 6s·e^{2−s}` since `e² ≤ 9 ≤ 3s`.
-/
import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiSharpCrude
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhi_supersolution
import Submission.Work.NumberTheory.Chen.APSwitchUpper.logExpLeft
import Submission.Work.NumberTheory.Chen.APSwitchUpper.logExpRight

namespace Work.NumberTheory.Chen.APSwitchUpper

noncomputable section

open MeasureTheory Finset
open scoped BigOperators

/-! ## Continuity and integrability of the crude pair -/

/-- `crudeU` is continuous (the three branches match at `1` and at `3`). -/
theorem crudeU_continuous : Continuous crudeU := by
  have hg : ContinuousOn (fun s : ℝ => if s ≤ 3 then (9 - s) / s else 2 * Real.exp (3 - s))
      (Set.Ici 1) := by
    refine ContinuousOn.if (p := fun s : ℝ => s ≤ 3) ?_ ?_ ?_
    · intro a ha
      obtain ⟨-, ha⟩ := ha
      rw [show {s : ℝ | s ≤ 3} = Set.Iic (3 : ℝ) by ext; simp] at ha
      rw [frontier_Iic] at ha
      rw [Set.mem_singleton_iff] at ha
      subst ha
      norm_num
    · rw [show {s : ℝ | s ≤ 3} = Set.Iic (3 : ℝ) by ext; simp, closure_Iic]
      refine ContinuousOn.div ?_ ?_ ?_
      · fun_prop
      · fun_prop
      · intro x hx
        have h1 : (1 : ℝ) ≤ x := hx.1
        exact ne_of_gt (by linarith)
    · rw [show {s : ℝ | ¬ s ≤ 3} = Set.Ioi (3 : ℝ) by ext x; simp, closure_Ioi]
      fun_prop
  unfold crudeU
  refine continuous_if (p := fun s : ℝ => s < 1) ?_ continuousOn_const ?_
  · intro a ha
    rw [show {s : ℝ | s < 1} = Set.Iio (1 : ℝ) by ext; simp] at ha
    rw [frontier_Iio] at ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    norm_num
  · rw [show {s : ℝ | ¬ s < 1} = Set.Ici (1 : ℝ) by ext x; simp, closure_Ici]
    exact hg

/-- `crudeV` is continuous. -/
theorem crudeV_continuous : Continuous crudeV := by
  unfold crudeV
  fun_prop

theorem crudeU_intervalIntegrable (a b : ℝ) : IntervalIntegrable crudeU volume a b :=
  crudeU_continuous.intervalIntegrable a b

theorem crudeV_intervalIntegrable (a b : ℝ) : IntervalIntegrable crudeV volume a b :=
  crudeV_continuous.intervalIntegrable a b

/-! ## The level-by-level comparison principle -/

/-- **Comparison principle, level by level.**  If `U, V ≥ 0` satisfy the two supersolution
inequalities of the delay system at `s ≥ 2` and the linear bound `t·U t ≥ 3 − t + 3U 3` on
`[1,3]`, then every partial level of the `profC` family is dominated by `U`, `V`. -/
theorem apart_bpart_le_of_supersolution {U V : ℝ → ℝ}
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
              · -- x ∈ [t-1, 2): the clamping identity
                have hx3 : x ≤ 3 := by linarith [hx2]
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

/-! ## Elementary facts about the crude pair used below -/

/-- `crudeU u = 2 exp (3 - u)` also at `u = 3`. -/
theorem crudeU_of_three_le {u : ℝ} (h : 3 ≤ u) : crudeU u = 2 * Real.exp (3 - u) := by
  rcases eq_or_lt_of_le h with h' | h'
  · rw [← h', crudeU_three]; norm_num
  · exact crudeU_of_three_lt h'

theorem setUcc_left {a b x : ℝ} (hab : a ≤ b) (hx : x ∈ Set.uIcc a b) : a ≤ x := by
  rw [Set.uIcc_of_le hab] at hx; exact hx.1

theorem setUcc_right {a b x : ℝ} (hab : a ≤ b) (hx : x ∈ Set.uIcc a b) : x ≤ b := by
  rw [Set.uIcc_of_le hab] at hx; exact hx.2

/-! ## The linear bound on `[1,3]` -/

theorem crudeU_lin {t : ℝ} (h1 : 1 ≤ t) (h3 : t ≤ 3) :
    (3 - t + 3 * crudeU 3) / t ≤ crudeU t := by
  have hkey : (3 : ℝ) - t + 3 * crudeU 3 = 9 - t := by rw [crudeU_three]; ring
  rw [hkey, crudeU_of_mem h1 h3]

/-! ## The three elementary integrals -/

/-- `∫_a^b crudeV = 6 (exp (2-a) - exp (2-b))`. -/
theorem integral_crudeV (a b : ℝ) :
    ∫ u in a..b, crudeV u = 6 * (Real.exp (2 - a) - Real.exp (2 - b)) := by
  rw [show (fun u => crudeV u) = fun u => 6 * Real.exp (2 - u) from by
    funext u; rw [crudeV]]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_left (fun x : ℝ => Real.exp x) 2, integral_exp]

/-- `∫_a^b 2 exp (3-u) = 2 (exp (3-a) - exp (3-b))`. -/
theorem integral_exp3 (a b : ℝ) :
    ∫ u in a..b, 2 * Real.exp (3 - u) = 2 * (Real.exp (3 - a) - Real.exp (3 - b)) := by
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_left (fun x : ℝ => Real.exp x) 3, integral_exp]

/-- `∫_a^b (9-u)/u = 9 log (b/a) - (b - a)` for `0 < a ≤ b`. -/
theorem integral_nine_sub_div (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∫ u in a..b, ((9 : ℝ) - u) / u = 9 * Real.log (b / a) - (b - a) := by
  have h0 : (0 : ℝ) ∉ Set.uIcc a b := by
    intro hmem
    have := setUcc_left hab hmem
    linarith
  have hcont : ContinuousOn (fun u : ℝ => 9 * u⁻¹) (Set.uIcc a b) := by
    refine ContinuousOn.const_mul ?_ 9
    refine ContinuousOn.inv₀ continuousOn_id ?_
    intro x hx
    exact ne_of_gt (lt_of_lt_of_le ha (setUcc_left hab hx))
  have hcongr : (∫ u in a..b, ((9 : ℝ) - u) / u) = ∫ u in a..b, (9 * u⁻¹ - 1) := by
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    have hu0 : u ≠ 0 := ne_of_gt (lt_of_lt_of_le ha (setUcc_left hab hu))
    rw [sub_div, div_self hu0, div_eq_mul_inv]
  have hI : IntervalIntegrable (fun u : ℝ => 9 * u⁻¹) volume a b := hcont.intervalIntegrable
  have hI2 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume a b := intervalIntegrable_const
  rw [hcongr, intervalIntegral.integral_sub hI hI2, intervalIntegral.integral_const_mul,
    integral_inv h0, intervalIntegral.integral_const, smul_eq_mul, mul_one]

/-! ## The one-variable inequality and its `s`-form -/

/-- `9 log (3/σ) + σ - 1 ≤ 6 (σ+1) exp (1-σ)` for `σ ∈ [1,3]`
(halves `logExpLeft`/`logExpRight`). -/
theorem crude_log_exp (σ : ℝ) (h1 : 1 ≤ σ) (h3 : σ ≤ 3) :
    9 * Real.log (3 / σ) + σ - 1 ≤ 6 * (σ + 1) * Real.exp (1 - σ) := by
  rcases le_or_gt σ 2 with h | h
  · exact logExpLeft σ h1 h
  · exact logExpRight σ (le_of_lt h) h3

/-- The form used below: for `2 ≤ s ≤ 4`, `9 log (3/(s-1)) + s - 2 ≤ 6 s exp (2-s)`. -/
theorem crude_log_exp' (s : ℝ) (h2 : 2 ≤ s) (h4 : s ≤ 4) :
    9 * Real.log (3 / (s - 1)) + s - 2 ≤ 6 * s * Real.exp (2 - s) := by
  have h1 : (1 : ℝ) ≤ s - 1 := by linarith
  have h3 : s - 1 ≤ 3 := by linarith
  have hkey := crude_log_exp (s - 1) h1 h3
  have e1 : (s - 1) + 1 = s := by ring
  have e2 : 1 - (s - 1) = 2 - s := by ring
  rw [e1, e2] at hkey
  linarith

/-! ## The two supersolution inequalities for the crude pair -/

/-- The first fixed-point inequality: `(3−s)⁺ + ∫_{max(s−1,2)}^b crudeV ≤ s·crudeU s`. -/
theorem crudeUV_aux :
    ∀ s : ℝ, 2 ≤ s → ∀ b : ℝ, max (s - 1) 2 ≤ b →
      (3 - s) * (if s ≤ 3 then (1 : ℝ) else 0)
        + ∫ u in (max (s - 1) 2)..b, crudeV u ≤ s * crudeU s := by
  intro s hs b hb
  have hInt : ∫ u in (max (s - 1) 2)..b, crudeV u ≤ 6 * Real.exp (2 - max (s - 1) 2) := by
    rw [integral_crudeV]
    have := Real.exp_nonneg (2 - b)
    linarith
  rcases le_or_gt s 3 with hs3 | hs3
  · have hmax : max (s - 1) 2 = 2 := max_eq_right (by linarith)
    rw [hmax] at hInt ⊢
    rw [show (2 : ℝ) - 2 = 0 by norm_num, Real.exp_zero] at hInt
    rw [if_pos hs3]
    have hU : crudeU s = (9 - s) / s := crudeU_of_mem (by linarith) hs3
    rw [hU]
    have hs0 : (0 : ℝ) < s := by linarith
    have heq : s * ((9 - s) / s) = 9 - s := by field_simp
    rw [heq]
    linarith
  · have hmax : max (s - 1) 2 = s - 1 := max_eq_left (by linarith)
    rw [hmax] at hInt ⊢
    rw [show 2 - (s - 1) = 3 - s by ring] at hInt
    rw [if_neg (not_le.mpr hs3), mul_zero, zero_add]
    have hU : crudeU s = 2 * Real.exp (3 - s) := crudeU_of_three_lt hs3
    rw [hU]
    have hexp : 0 < Real.exp (3 - s) := Real.exp_pos _
    nlinarith [hInt, hexp]

/-- The second fixed-point inequality: `∫_{s−1}^b crudeU ≤ s·crudeV s`. -/
theorem crudeVU_aux :
    ∀ s : ℝ, 2 ≤ s → ∀ b : ℝ, s - 1 ≤ b →
      ∫ u in (s - 1)..b, crudeU u ≤ s * crudeV s := by
  intro s hs b hb
  have hcv : s * crudeV s = 6 * s * Real.exp (2 - s) := by
    rw [crudeV]; ring
  rcases le_or_gt 4 s with hs4 | hs4
  · have hcongr : (∫ u in (s - 1)..b, crudeU u) = ∫ u in (s - 1)..b, 2 * Real.exp (3 - u) :=
      intervalIntegral.integral_congr
        (fun u hu => crudeU_of_three_le (by linarith [setUcc_left hb hu]))
    rw [hcongr, integral_exp3, hcv]
    have hstep : 2 * (Real.exp (3 - (s - 1)) - Real.exp (3 - b))
        ≤ 2 * Real.exp (3 - (s - 1)) := by
      have := Real.exp_pos (3 - b); linarith
    refine le_trans hstep ?_
    rw [show 3 - (s - 1) = 2 + (2 - s) by ring, Real.exp_add]
    have hexp2 : Real.exp 2 ≤ 9 := by
      have h3 := Real.exp_one_lt_three
      have hp := Real.exp_pos (1 : ℝ)
      calc Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        _ ≤ 9 := by nlinarith
    have hEs : 0 < Real.exp (2 - s) := Real.exp_pos _
    have h1 : 2 * Real.exp 2 ≤ 6 * s := by nlinarith
    calc 2 * (Real.exp 2 * Real.exp (2 - s)) = (2 * Real.exp 2) * Real.exp (2 - s) := by ring
      _ ≤ (6 * s) * Real.exp (2 - s) := mul_le_mul_of_nonneg_right h1 (le_of_lt hEs)
      _ = 6 * s * Real.exp (2 - s) := by ring
  · -- `2 ≤ s ≤ 4`: extend `b` to `B = max b 3` (nonnegative integrand) and split at `3`.
    have hs4' : s ≤ 4 := le_of_lt hs4
    set B : ℝ := max b 3 with hB
    have hBb : b ≤ B := le_max_left _ _
    have h3B : (3 : ℝ) ≤ B := le_max_right _ _
    have hmono : (∫ u in (s - 1)..b, crudeU u) ≤ ∫ u in (s - 1)..B, crudeU u := by
      have hadd : (∫ u in (s - 1)..b, crudeU u) + ∫ u in b..B, crudeU u
          = ∫ u in (s - 1)..B, crudeU u :=
        intervalIntegral.integral_add_adjacent_intervals (crudeU_intervalIntegrable _ _)
          (crudeU_intervalIntegrable _ _)
      have hnn : 0 ≤ ∫ u in b..B, crudeU u :=
        intervalIntegral.integral_nonneg_of_forall hBb (fun u => crudeU_nonneg u)
      linarith
    refine le_trans hmono ?_
    have h3s : s - 1 ≤ 3 := by linarith
    have hsplit : (∫ u in (s - 1)..(3 : ℝ), crudeU u) + ∫ u in (3 : ℝ)..B, crudeU u
        = ∫ u in (s - 1)..B, crudeU u :=
      intervalIntegral.integral_add_adjacent_intervals (crudeU_intervalIntegrable _ _)
        (crudeU_intervalIntegrable _ _)
    have hleft : (∫ u in (s - 1)..(3 : ℝ), crudeU u)
        = 9 * Real.log (3 / (s - 1)) - (3 - (s - 1)) := by
      refine Eq.trans (intervalIntegral.integral_congr
        (fun u hu => crudeU_of_mem (by linarith [setUcc_left h3s hu]) (setUcc_right h3s hu))) ?_
      exact integral_nine_sub_div (s - 1) 3 (by linarith) h3s
    have hright : (∫ u in (3 : ℝ)..B, crudeU u) ≤ 2 := by
      have hcongr : (∫ u in (3 : ℝ)..B, crudeU u) = ∫ u in (3 : ℝ)..B, 2 * Real.exp (3 - u) :=
        intervalIntegral.integral_congr
          (fun u hu => crudeU_of_three_le (setUcc_left h3B hu))
      rw [hcongr, integral_exp3]
      have hpos := Real.exp_pos (3 - B)
      have hone : Real.exp (3 - (3 : ℝ)) = 1 := by norm_num
      rw [hone]
      linarith
    rw [← hsplit, hleft, hcv]
    have hstar := crude_log_exp' s hs hs4'
    have h3s' : (3 : ℝ) - (s - 1) = 4 - s := by ring
    linarith [hright, hstar, h3s']

/-! ## The level bounds -/

theorem crudeLevelBounds :
    (∀ N : ℕ, ∀ s : ℝ, 2 ≤ s → Work.NumberTheory.Chen.APSwitchUpper.apart N s
        ≤ Work.NumberTheory.Chen.APSwitchUpper.crudeU s)
  ∧ (∀ N : ℕ, ∀ s : ℝ, 2 ≤ s → Work.NumberTheory.Chen.APSwitchUpper.bpart N s
        ≤ Work.NumberTheory.Chen.APSwitchUpper.crudeV s) := by
  refine apart_bpart_le_of_supersolution (U := crudeU) (V := crudeV)
    crudeU_nonneg crudeV_nonneg crudeV_intervalIntegrable crudeU_intervalIntegrable
    crudeUV_aux crudeVU_aux (fun t h1 h3 => crudeU_lin h1 h3)

end

end Work.NumberTheory.Chen.APSwitchUpper
