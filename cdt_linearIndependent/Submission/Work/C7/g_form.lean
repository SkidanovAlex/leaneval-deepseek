import Mathlib
import Submission.Work.C7.xdefs
import Submission.Work.C7.gsetup
import Submission.Work.Pure.pure_facts
import Submission.Work.Pure.b4_psi_rel
import Submission.Work.C7.B2sub_ode
import Submission.Work.C7.B3sub_ode
import Submission.Work.C7.B4sub_ode
import Submission.Work.C7.P1_zero
import Submission.Work.C7.P3_zero

/-!
# Area C7 — the pullback identities `g_form` of the pure functions `B₂, B₃, B₄`

`Work.C7.g i = B_{i+1} ∘ y` where `y = Work.C7.yps = x²/(x−1)`.  This module proves

```
g 1 = 2y − w·L,     g 2 = −L²/2,     g 3 = (x − φ)·(2Li₂ + ½L²)
```

(`w = cfun = x − φ`, `L = Lps = log(1−x)`, `Li₂ = Li2ps`).

The proofs of the three identities have the same shape.  The `x`-side right-hand sides
`R₁ = 2y − wL`, `R₂ = −L²/2`, `R₃ = (x−φ)(2Li₂ + ½L²)` are shown directly to satisfy the
`x`-form of the corresponding `y`-ODE,

```
x(2−x)·F' = (2−y)·F + y²,                (B₂)
x(2−x)·F' = 2y − B₂∘y,                   (B₃)
x(2−x)·F' = (2−y)·F + (4−y)·(B₂∘y) − 2y(4−y)   (B₄)
```

(the `y`-ODEs are `Work.Pure.relation_B2/B3/B4`, proved, and are transported by the chain rule
and `x(2−x)·y' = y(4−y)`, `Work.C7.X_mul_two_sub_mul_deriv_yps`), while `Bᵢ∘y` satisfies them by
construction.  The difference of two solutions of (B₂) (resp. (B₄)) satisfies the homogeneous
equation `x(2−x)h' = (2−y)h`, whose power-series solutions with `h(0) = h(1) = 0` vanish
(`ode_unique`); for (B₃) the equation is `x(2−x)h' = 0` and `h(0) = 0` suffices (`ode_unique_zero`).
Both sides have the required low coefficients (`Submission.Work.C7.gsetup`).
-/

namespace Work.C7

open PowerSeries

noncomputable section

/-! ## The index bookkeeping: `g i = Bᵢ₊₁ ∘ y` -/

private lemma g_one : g 1 = Submission.CDTPlan.B2.subst yps := by
  simp [Work.C7.g, Submission.CDTPlan.pureB]

private lemma g_two : g 2 = Submission.CDTPlan.B3.subst yps := by
  simp [Work.C7.g, Submission.CDTPlan.pureB]

private lemma g_three : g 3 = Submission.CDTPlan.B4.subst yps := by
  simp [Work.C7.g, Submission.CDTPlan.pureB]

/-! ## Coefficient helpers -/

private lemma coeff_XD (m : ℕ) (f : PowerSeries ℚ) :
    PowerSeries.coeff m (PowerSeries.X * PowerSeries.derivative (R := ℚ) f)
      = (m : ℚ) * PowerSeries.coeff m f := by
  rcases m with _ | k
  · rw [PowerSeries.coeff_zero_X_mul]; simp
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]; push_cast; ring

private lemma coeff_XsqD (m : ℕ) (f : PowerSeries ℚ) :
    PowerSeries.coeff m (PowerSeries.X ^ 2 * PowerSeries.derivative (R := ℚ) f)
      = ((m - 1 : ℕ) : ℚ) * PowerSeries.coeff (m - 1) f := by
  have h : (PowerSeries.X : PowerSeries ℚ) ^ 2 * PowerSeries.derivative (R := ℚ) f
      = PowerSeries.X * (PowerSeries.X * PowerSeries.derivative (R := ℚ) f) := by ring
  rw [h]
  rcases m with _ | k
  · rw [PowerSeries.coeff_zero_X_mul]; simp
  · rw [PowerSeries.coeff_succ_X_mul, coeff_XD]; simp only [Nat.add_sub_cancel]

private lemma coeff_Xmul (m : ℕ) (f : PowerSeries ℚ) :
    PowerSeries.coeff m (PowerSeries.X * f)
      = if 1 ≤ m then PowerSeries.coeff (m - 1) f else 0 := by
  simpa using PowerSeries.coeff_X_pow_mul' f 1 m

/-- Coefficient of the left-hand side of the homogeneous pullback equation. -/
private lemma coeff_ode_lhs (m : ℕ) (h : PowerSeries ℚ) :
    PowerSeries.coeff m (PowerSeries.X * (2 - PowerSeries.X) * PowerSeries.derivative (R := ℚ) h)
      = 2 * ((m : ℚ) * PowerSeries.coeff m h)
        - ((m - 1 : ℕ) : ℚ) * PowerSeries.coeff (m - 1) h := by
  rw [show PowerSeries.X * (2 - PowerSeries.X) * PowerSeries.derivative (R := ℚ) h
      = (2 : PowerSeries ℚ) * (PowerSeries.X * PowerSeries.derivative (R := ℚ) h)
        - PowerSeries.X ^ 2 * PowerSeries.derivative (R := ℚ) h by ring]
  rw [map_sub, coeff_two_mul, coeff_XD, coeff_XsqD]

/-- Uniqueness for the pullback of the `B₂`-ODE: the homogeneous equation has only the trivial
power-series solution with vanishing first two coefficients. -/
lemma ode_unique {h : PowerSeries ℚ}
    (hh : PowerSeries.X * (2 - PowerSeries.X) * PowerSeries.derivative (R := ℚ) h = (2 - yps) * h)
    (h0 : PowerSeries.coeff 0 h = 0) (h1 : PowerSeries.coeff 1 h = 0) : h = 0 := by
  have key : ∀ n : ℕ, PowerSeries.coeff n h = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases Nat.lt_or_ge n 2 with hn | hn
      · interval_cases n
        · exact h0
        · exact h1
      · have hsum : PowerSeries.coeff n (yps * h) = 0 := by
          rw [Commons.RingTheory.PowerSeries.coeff_mul_eq_sum_range]
          refine Finset.sum_eq_zero fun i hi => ?_
          rcases Nat.lt_or_ge i 2 with hi2 | hi2
          · interval_cases i
            · rw [coeff_zero_yps, zero_mul]
            · rw [coeff_one_yps, zero_mul]
          · rw [ih (n - i) (by omega), mul_zero]
        have hc := congrArg (fun f => PowerSeries.coeff n f) hh
        rw [coeff_ode_lhs n h] at hc
        rw [show (2 - yps) * h = (2 : PowerSeries ℚ) * h - yps * h by ring, map_sub,
          coeff_two_mul] at hc
        rw [hsum, sub_zero] at hc
        have hprev : PowerSeries.coeff (n - 1) h = 0 := ih (n - 1) (by omega)
        rw [hprev, mul_zero, sub_zero] at hc
        have hne : (2 * (n : ℚ) - 2) ≠ 0 := by
          have hn2 : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
          intro hc'
          linarith
        have hzero : (2 * (n : ℚ) - 2) * PowerSeries.coeff n h = 0 := by linear_combination hc
        exact (mul_eq_zero.mp hzero).resolve_left hne
  apply PowerSeries.ext
  intro n
  rw [key n]
  simp

/-- Uniqueness for the pullback of the `B₃`-ODE: `x(2−x)h' = 0` forces `h` to be constant. -/
lemma ode_unique_zero {h : PowerSeries ℚ}
    (hh : PowerSeries.X * (2 - PowerSeries.X) * PowerSeries.derivative (R := ℚ) h = 0)
    (h0 : PowerSeries.coeff 0 h = 0) : h = 0 := by
  have key : ∀ n : ℕ, PowerSeries.coeff n h = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · subst hn0
        exact h0
      · have hc := congrArg (fun f => PowerSeries.coeff n f) hh
        rw [coeff_ode_lhs n h] at hc
        simp only [map_zero] at hc
        have hprev : PowerSeries.coeff (n - 1) h = 0 := ih (n - 1) (by omega)
        rw [hprev, mul_zero, sub_zero] at hc
        have hne : (2 * (n : ℚ)) ≠ 0 := by
          have hn1 : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hnpos
          positivity
        have hzero : (2 * (n : ℚ)) * PowerSeries.coeff n h = 0 := by linear_combination hc
        exact (mul_eq_zero.mp hzero).resolve_left hne
  apply PowerSeries.ext
  intro n
  rw [key n]
  simp

/-! ## The `B₃` right-hand side satisfies its pulled-back equation -/

/-- `x(2−x)·(−L²/2)' = 2y − (2y − wL)`. -/
lemma P2_zero :
    PowerSeries.X * (2 - PowerSeries.X)
      * PowerSeries.derivative (R := ℚ) (-(PowerSeries.C (1 / 2 : ℚ)) * Lps ^ 2)
      = 2 * yps - (2 * yps - cfun * Lps) := by
  have hconst : (PowerSeries.derivative (R := ℚ)) (-(PowerSeries.C (1 / 2 : ℚ)) : PowerSeries ℚ) = 0 := by
    rw [show (-(PowerSeries.C (1 / 2 : ℚ)) : PowerSeries ℚ) = PowerSeries.C (-(1 / 2 : ℚ)) by simp,
      PowerSeries.derivative_C]
  have hd : PowerSeries.derivative (R := ℚ) (-(PowerSeries.C (1 / 2 : ℚ)) * (Lps * Lps))
      = -(PowerSeries.C (1 / 2 : ℚ)) * (Lps * gU + gU * Lps) := by
    rw [Work.Pure.b4_deriv_mul, Work.Pure.b4_deriv_mul, deriv_Lps_gU, hconst]
    ring
  have hmul : -(PowerSeries.C (1 / 2 : ℚ)) * (2 : PowerSeries ℚ) = -1 := by
    rw [show -(PowerSeries.C (1 / 2 : ℚ)) = PowerSeries.C (-(1 / 2 : ℚ)) by simp,
      show (2 : PowerSeries ℚ) = PowerSeries.C 2 from rfl, ← map_mul]
    norm_num
  rw [show -(PowerSeries.C (1 / 2 : ℚ)) * Lps ^ 2
      = -(PowerSeries.C (1 / 2 : ℚ)) * (Lps * Lps) by ring]
  rw [hd]
  rw [show -(PowerSeries.C (1 / 2 : ℚ)) * (Lps * gU + gU * Lps)
      = (-(PowerSeries.C (1 / 2 : ℚ)) * 2) * (Lps * gU) by ring, hmul]
  rw [cfun_eq]
  ring

/-! ## The reduction -/

/-- The three pullback identities, reduced to the five `x`-side verifications. -/
theorem g_form_aux
    (hB2 : PowerSeries.X * (2 - PowerSeries.X)
        * PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.B2.subst yps)
        = (2 - yps) * (Submission.CDTPlan.B2.subst yps) + yps ^ 2)
    (hB3 : PowerSeries.X * (2 - PowerSeries.X)
        * PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.B3.subst yps)
        = 2 * yps - Submission.CDTPlan.B2.subst yps)
    (hB4 : PowerSeries.X * (2 - PowerSeries.X)
        * PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.B4.subst yps)
        = (2 - yps) * (Submission.CDTPlan.B4.subst yps)
          + (4 - yps) * (Submission.CDTPlan.B2.subst yps) - 2 * yps * (4 - yps))
    (hP1 : PowerSeries.X * (2 - PowerSeries.X)
        * PowerSeries.derivative (R := ℚ) (2 * yps - cfun * Lps)
        = (2 - yps) * (2 * yps - cfun * Lps) + yps ^ 2)
    (hP3 : PowerSeries.X * (2 - PowerSeries.X)
        * PowerSeries.derivative (R := ℚ) ((PowerSeries.X - Submission.CDT.sympPhi)
            * (2 * Li2ps + PowerSeries.C (1 / 2 : ℚ) * Lps ^ 2))
        = (2 - yps) * ((PowerSeries.X - Submission.CDT.sympPhi)
            * (2 * Li2ps + PowerSeries.C (1 / 2 : ℚ) * Lps ^ 2))
          + (4 - yps) * (2 * yps - cfun * Lps) - 2 * yps * (4 - yps)) :
    g 1 = 2 * yps - cfun * Lps ∧
    g 2 = -(PowerSeries.C (1 / 2 : ℚ)) * Lps ^ 2 ∧
    g 3 = (PowerSeries.X - Submission.CDT.sympPhi)
      * (2 * Li2ps + PowerSeries.C (1 / 2 : ℚ) * Lps ^ 2) := by
  -- the `B₂` identity
  have h1 : Submission.CDTPlan.B2.subst yps = 2 * yps - cfun * Lps := by
    have hdiff : PowerSeries.X * (2 - PowerSeries.X)
        * PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.B2.subst yps - (2 * yps - cfun * Lps))
        = (2 - yps) * (Submission.CDTPlan.B2.subst yps - (2 * yps - cfun * Lps)) := by
      rw [map_sub]
      rw [show PowerSeries.X * (2 - PowerSeries.X)
            * (PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.B2.subst yps)
              - PowerSeries.derivative (R := ℚ) (2 * yps - cfun * Lps))
          = PowerSeries.X * (2 - PowerSeries.X)
              * PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.B2.subst yps)
            - PowerSeries.X * (2 - PowerSeries.X)
              * PowerSeries.derivative (R := ℚ) (2 * yps - cfun * Lps) by ring]
      rw [hB2, hP1]
      ring
    refine sub_eq_zero.mp (ode_unique hdiff ?_ ?_)
    · rw [coeff_zero_sub, coeff_zero_B2subst, coeff_zero_R1, sub_zero]
    · rw [coeff_one_sub, coeff_one_B2subst, coeff_one_R1, sub_zero]
  -- the `B₃` identity
  have h2 : Submission.CDTPlan.B3.subst yps = -(PowerSeries.C (1 / 2 : ℚ)) * Lps ^ 2 := by
    have hdiff : PowerSeries.X * (2 - PowerSeries.X)
        * PowerSeries.derivative (R := ℚ)
            (Submission.CDTPlan.B3.subst yps - (-(PowerSeries.C (1 / 2 : ℚ)) * Lps ^ 2))
        = 0 := by
      rw [map_sub]
      rw [show PowerSeries.X * (2 - PowerSeries.X)
            * (PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.B3.subst yps)
              - PowerSeries.derivative (R := ℚ) (-(PowerSeries.C (1 / 2 : ℚ)) * Lps ^ 2))
          = PowerSeries.X * (2 - PowerSeries.X)
              * PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.B3.subst yps)
            - PowerSeries.X * (2 - PowerSeries.X)
              * PowerSeries.derivative (R := ℚ) (-(PowerSeries.C (1 / 2 : ℚ)) * Lps ^ 2) by ring]
      rw [hB3, P2_zero, h1]
      ring
    refine sub_eq_zero.mp (ode_unique_zero hdiff ?_)
    · rw [coeff_zero_sub, coeff_zero_B3subst, coeff_zero_R2, sub_zero]
  -- the `B₄` identity
  have h3 : Submission.CDTPlan.B4.subst yps
      = (PowerSeries.X - Submission.CDT.sympPhi)
        * (2 * Li2ps + PowerSeries.C (1 / 2 : ℚ) * Lps ^ 2) := by
    have hdiff : PowerSeries.X * (2 - PowerSeries.X)
        * PowerSeries.derivative (R := ℚ)
            (Submission.CDTPlan.B4.subst yps - ((PowerSeries.X - Submission.CDT.sympPhi)
              * (2 * Li2ps + PowerSeries.C (1 / 2 : ℚ) * Lps ^ 2)))
        = (2 - yps) * (Submission.CDTPlan.B4.subst yps - ((PowerSeries.X - Submission.CDT.sympPhi)
              * (2 * Li2ps + PowerSeries.C (1 / 2 : ℚ) * Lps ^ 2))) := by
      rw [map_sub]
      rw [show PowerSeries.X * (2 - PowerSeries.X)
            * (PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.B4.subst yps)
              - PowerSeries.derivative (R := ℚ) ((PowerSeries.X - Submission.CDT.sympPhi)
                  * (2 * Li2ps + PowerSeries.C (1 / 2 : ℚ) * Lps ^ 2)))
          = PowerSeries.X * (2 - PowerSeries.X)
              * PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.B4.subst yps)
            - PowerSeries.X * (2 - PowerSeries.X)
              * PowerSeries.derivative (R := ℚ) ((PowerSeries.X - Submission.CDT.sympPhi)
                  * (2 * Li2ps + PowerSeries.C (1 / 2 : ℚ) * Lps ^ 2)) by ring]
      rw [hB4, hP3, h1]
      ring
    refine sub_eq_zero.mp (ode_unique hdiff ?_ ?_)
    · rw [coeff_zero_sub, coeff_zero_B4subst, coeff_zero_R3, sub_zero]
    · rw [coeff_one_sub, coeff_one_B4subst, coeff_one_R3, sub_zero]
  exact ⟨by rw [g_one]; exact h1, by rw [g_two]; exact h2, by rw [g_three]; exact h3⟩

/-- **The three pullback identities of `B₂, B₃, B₄`.** -/
theorem g_form :
    Work.C7.g 1 = 2 * Work.C7.yps - Work.C7.cfun * Work.C7.Lps ∧
    Work.C7.g 2 = -(PowerSeries.C (1/2 : ℚ)) * Work.C7.Lps ^ 2 ∧
    Work.C7.g 3 = (PowerSeries.X - Submission.CDT.sympPhi) * (2 * Work.C7.Li2ps + (PowerSeries.C (1/2 : ℚ)) * Work.C7.Lps ^ 2) :=
  g_form_aux B2sub_ode B3sub_ode B4sub_ode P1_zero P3_zero

end

end Work.C7
