/-
# ZeroFreeTables — tf72Phi_pos_upper

`tf72PhiUBpos y` is an upper bound for `tf72Phi y` on `0 ≤ y ≤ 2`.

Both sides are Laplace transforms of the polynomial body
`tf72Body s = (2-s)³(4+6s+s²)`:

  `tf72Phi y = (1/30) ∫₀² e^{-ys} tf72Body s ds`,
  `tf72PhiUBpos y = (1/30) ∫₀² (Σ_{m<9} (-ys)^m/m! + 2(ys)^9/9!) tf72Body s ds`.

The integrand comparison is pointwise on `[0,2]`: for `t ≥ 0`,

  `e^{-t} ≤ Σ_{m<9} (-t)^m/m! + 2 t^9/9!`   (`exp_neg_le_taylor_nine`),

the truncated alternating exponential series dominating `e^{-t}` from above (the
tail `Σ_{m≥9} (-t)^m/m!` has the sign of `(-1)^9 = -1`).  Since `tf72Body ≥ 0`
on `[0,2]`, multiplying by `tf72Body s` and integrating gives the claim, the
resulting polynomial integral being evaluated term-by-term with
`∫₀² s^m tf72Body s = tf72M m` (`tf72Phi_poly_sum_integral`).

Note that the hypothesis `y ≤ 2` is not needed: the pointwise exponential bound
holds for every `t ≥ 0`, hence the inequality holds for all `y ≥ 0`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.tf72Phi_defs

noncomputable section
open scoped Real
open MeasureTheory

namespace Work.ZeroFreeTables

private def altS (n : ℕ) (x : ℝ) : ℝ := ∑ m ∈ Finset.range n, (-x)^m / (m.factorial : ℝ)

private lemma hasDerivAt_term (m : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (-y)^(m+1) / ((m+1).factorial : ℝ))
      (-((-x)^m / (m.factorial : ℝ))) x := by
  have h : HasDerivAt (fun y : ℝ => (-y)^(m+1) / ((m+1).factorial : ℝ))
      ((((m+1 : ℕ) : ℝ) * (-x)^m * (-1)) / (((m+1).factorial : ℕ) : ℝ)) x := by
    have h' := (((hasDerivAt_id x).neg).pow (m+1)).div_const ((((m+1).factorial : ℕ) : ℝ))
    simpa using h'
  convert h using 1
  have hf : ((((m+1).factorial : ℕ) : ℝ)) = ((m:ℝ)+1) * (m.factorial:ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [Nat.cast_add, Nat.cast_one, hf]
  have h1 : ((m:ℝ)+1) ≠ 0 := by positivity
  have h2 : (m.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  field_simp

private lemma hasDerivAt_tail (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => ∑ m ∈ Finset.range n, (-y)^(m+1) / ((m+1).factorial : ℝ))
      (-(altS n x)) x := by
  have hsum : HasDerivAt (fun y : ℝ => ∑ m ∈ Finset.range n, (-y)^(m+1) / ((m+1).factorial : ℝ))
      (∑ m ∈ Finset.range n, -((-x)^m / (m.factorial : ℝ))) x :=
    HasDerivAt.fun_sum (fun m _ => hasDerivAt_term m x)
  convert hsum using 1
  rw [altS, Finset.sum_neg_distrib]

private lemma altS_diff (n : ℕ) (x : ℝ) :
    altS (n+1) x - altS n x = (-x)^n / (n.factorial : ℝ) := by
  rw [altS, altS, Finset.sum_range_succ]
  ring

private lemma altS_succ (n : ℕ) (x : ℝ) :
    altS (n+1) x = 1 + ∑ m ∈ Finset.range n, (-x)^(m+1) / ((m+1).factorial : ℝ) := by
  rw [altS, Finset.sum_range_succ']
  norm_num
  ring

private lemma hasDerivAt_altS (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => altS (n+1) y) (-(altS n x)) x := by
  have hfun : (fun y : ℝ => altS (n+1) y)
      = fun y : ℝ => 1 + ∑ m ∈ Finset.range n, (-y)^(m+1) / ((m+1).factorial : ℝ) := by
    funext y; rw [altS_succ]
  rw [hfun]
  exact (hasDerivAt_tail n x).const_add 1

private lemma hasDerivAt_u (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp y * altS (n+1) y)
      (Real.exp x * ((-x)^n / (n.factorial : ℝ))) x := by
  have hmul := (Real.hasDerivAt_exp x).mul (hasDerivAt_altS n x)
  have hv : Real.exp x * altS (n+1) x + Real.exp x * (-(altS n x))
      = Real.exp x * ((-x)^n / (n.factorial : ℝ)) := by
    calc Real.exp x * altS (n+1) x + Real.exp x * (-(altS n x))
        = Real.exp x * (altS (n+1) x - altS n x) := by ring
      _ = Real.exp x * ((-x)^n / (n.factorial : ℝ)) := by rw [altS_diff]
  rw [hv] at hmul
  exact hmul

/-- For `t ≥ 0` the degree-`8` partial sum of the exponential series with alternating
signs dominates `e^{-t}`: `e^{-t} ≤ Σ_{m<9} (-t)^m/m!`.  (Equivalently
`e^t · Σ_{m<9} (-t)^m/m!` is monotone, with derivative `e^t t^8/8! ≥ 0`, and equals
`1` at `t = 0`.) -/
lemma exp_neg_le_taylor_nine (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-t) ≤ ∑ m ∈ Finset.range 9, (-t) ^ m / (m.factorial : ℝ) := by
  have hderiv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Real.exp y * altS 9 y)
      (Real.exp x * (x^8 / ((Nat.factorial 8 : ℕ) : ℝ))) x := by
    intro x
    have h := hasDerivAt_u 8 x
    convert h using 1
    ring
  have hnonneg : ∀ x : ℝ, 0 ≤ Real.exp x * (x^8 / ((Nat.factorial 8 : ℕ) : ℝ)) := by
    intro x; positivity
  have hmono : Monotone (fun y : ℝ => Real.exp y * altS 9 y) :=
    monotone_of_hasDerivAt_nonneg hderiv hnonneg
  have h0 : altS 9 0 = 1 := by
    rw [altS]
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have h1 : (1:ℝ) ≤ Real.exp t * altS 9 t := by
    have h := hmono ht
    simpa [h0] using h
  have h2 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-t)).le
  calc Real.exp (-t) = Real.exp (-t) * 1 := by ring
    _ ≤ Real.exp (-t) * (Real.exp t * altS 9 t) := h2
    _ = altS 9 t := by rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    _ = ∑ m ∈ Finset.range 9, (-t) ^ m / (m.factorial : ℝ) := rfl

/-! ### 2. Integral linearity against the moment table -/

private lemma tf72Body_nonneg' {s : ℝ} (hs0 : 0 ≤ s) (hs2 : s ≤ 2) : 0 ≤ tf72Body s := by
  rw [tf72Body]
  have h1 : 0 ≤ 2 - s := by linarith
  have h2 : 0 ≤ 4 + 6*s + s^2 := by nlinarith [sq_nonneg (s + 3)]
  positivity

/-- Term-by-term integration of a polynomial multiple of the body `tf72Body` against the
moment table: `∫₀² (Σ_{m<N} c m s^m) tf72Body s ds = Σ_{m<N} c m tf72M m`. -/
lemma tf72Phi_poly_sum_integral (N : ℕ) (c : ℕ → ℝ) :
    (∫ s in (0:ℝ)..2, (∑ m ∈ Finset.range N, c m * s^m) * tf72Body s)
      = ∑ m ∈ Finset.range N, c m * tf72M m := by
  have hcongr : (∫ s in (0:ℝ)..2, (∑ m ∈ Finset.range N, c m * s^m) * tf72Body s)
      = ∫ s in (0:ℝ)..2, ∑ m ∈ Finset.range N, c m * (s^m * tf72Body s) := by
    apply intervalIntegral.integral_congr
    intro s _
    simp only []
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  have hfs : (∫ s in (0:ℝ)..2, ∑ m ∈ Finset.range N, c m * (s^m * tf72Body s))
      = ∑ m ∈ Finset.range N, ∫ s in (0:ℝ)..2, c m * (s^m * tf72Body s) :=
    intervalIntegral.integral_finsetSum (fun m _ => by
      apply Continuous.intervalIntegrable
      unfold tf72Body
      fun_prop)
  rw [hcongr, hfs]
  apply Finset.sum_congr rfl
  intro m hm
  rw [intervalIntegral.integral_const_mul, tf72M_eq_integral]

private lemma tf72Phi_rem_integral (y : ℝ) :
    (∫ s in (0:ℝ)..2, (2 * (y*s)^9 / ((Nat.factorial 9 : ℕ) : ℝ)) * tf72Body s)
      = 2 * y^9 * tf72M 9 / ((Nat.factorial 9 : ℕ) : ℝ) := by
  rw [show (fun s : ℝ => (2 * (y*s)^9 / ((Nat.factorial 9 : ℕ) : ℝ)) * tf72Body s)
      = fun s : ℝ => (2 * y^9 / ((Nat.factorial 9 : ℕ) : ℝ)) * (s^9 * tf72Body s) from by
    funext s; rw [mul_pow]; ring]
  rw [intervalIntegral.integral_const_mul, tf72M_eq_integral]
  ring

/-! ### 3. The target -/

private lemma exp_neg_le_taylor_nine_add (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-t) ≤ (∑ m ∈ Finset.range 9, (-t)^m/(m.factorial:ℝ))
      + 2 * t^9 / ((Nat.factorial 9 : ℕ) : ℝ) := by
  have h := exp_neg_le_taylor_nine t ht
  have h2 : 0 ≤ 2 * t^9 / ((Nat.factorial 9 : ℕ) : ℝ) := by positivity
  linarith

theorem tf72Phi_pos_upper (y : ℝ) (hy0 : 0 ≤ y) (hy2 : y ≤ 2) :
    tf72Phi y ≤ tf72PhiUBpos y := by
  have hbody : ∀ s : ℝ, 0 ≤ s → s ≤ 2 → 0 ≤ tf72Body s := fun s h1 h2 => tf72Body_nonneg' h1 h2
  have hint1 : IntervalIntegrable (fun s : ℝ => Real.exp (-(y*s)) * tf72Body s) volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    unfold tf72Body; fun_prop
  have hint2 : IntervalIntegrable
      (fun s : ℝ => ((∑ m ∈ Finset.range 9, (-(y*s))^m/(m.factorial:ℝ))
        + 2 * (y*s)^9 / ((Nat.factorial 9 : ℕ) : ℝ)) * tf72Body s) volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    unfold tf72Body; fun_prop
  have hpt : ∀ s ∈ Set.Icc (0:ℝ) 2,
      Real.exp (-(y*s)) * tf72Body s
        ≤ ((∑ m ∈ Finset.range 9, (-(y*s))^m/(m.factorial:ℝ))
          + 2 * (y*s)^9 / ((Nat.factorial 9 : ℕ) : ℝ)) * tf72Body s := by
    intro s hs
    obtain ⟨hs0, hs2⟩ := hs
    have ht : 0 ≤ y*s := mul_nonneg hy0 hs0
    exact mul_le_mul_of_nonneg_right (exp_neg_le_taylor_nine_add (y*s) ht) (hbody s hs0 hs2)
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (a := (0:ℝ)) (b := 2)
    (by norm_num) hint1 hint2 hpt
  have hA : IntervalIntegrable
      (fun s : ℝ => (∑ m ∈ Finset.range 9, (-(y*s))^m/(m.factorial:ℝ)) * tf72Body s)
      volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    unfold tf72Body; fun_prop
  have hB : IntervalIntegrable
      (fun s : ℝ => (2 * (y*s)^9 / ((Nat.factorial 9 : ℕ) : ℝ)) * tf72Body s)
      volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    unfold tf72Body; fun_prop
  have hsplit : (∫ s in (0:ℝ)..2, ((∑ m ∈ Finset.range 9, (-(y*s))^m/(m.factorial:ℝ))
        + 2 * (y*s)^9 / ((Nat.factorial 9 : ℕ) : ℝ)) * tf72Body s)
      = (∫ s in (0:ℝ)..2, (∑ m ∈ Finset.range 9, (-(y*s))^m/(m.factorial:ℝ)) * tf72Body s)
        + (∫ s in (0:ℝ)..2, (2 * (y*s)^9 / ((Nat.factorial 9 : ℕ) : ℝ)) * tf72Body s) := by
    have h1 : (∫ s in (0:ℝ)..2, ((∑ m ∈ Finset.range 9, (-(y*s))^m/(m.factorial:ℝ))
          + 2 * (y*s)^9 / ((Nat.factorial 9 : ℕ) : ℝ)) * tf72Body s)
        = ∫ s in (0:ℝ)..2, ((∑ m ∈ Finset.range 9, (-(y*s))^m/(m.factorial:ℝ)) * tf72Body s
          + (2 * (y*s)^9 / ((Nat.factorial 9 : ℕ) : ℝ)) * tf72Body s) := by
      apply intervalIntegral.integral_congr
      intro s _
      ring
    rw [h1, intervalIntegral.integral_add hA hB]
  have hsum : (∫ s in (0:ℝ)..2, (∑ m ∈ Finset.range 9, (-(y*s))^m/(m.factorial:ℝ)) * tf72Body s)
      = ∑ m ∈ Finset.range 9, (-y)^m * tf72M m / (m.factorial:ℝ) := by
    have hfun : (fun s : ℝ => (∑ m ∈ Finset.range 9, (-(y*s))^m/(m.factorial:ℝ)) * tf72Body s)
        = fun s : ℝ => (∑ m ∈ Finset.range 9, ((-y)^m/(m.factorial:ℝ)) * s^m) * tf72Body s := by
      funext s
      have hs : (∑ m ∈ Finset.range 9, (-(y*s))^m/(m.factorial:ℝ))
          = ∑ m ∈ Finset.range 9, ((-y)^m/(m.factorial:ℝ)) * s^m := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [show -(y*s) = (-y)*s by ring, mul_pow]
        ring
      rw [hs]
    rw [hfun, tf72Phi_poly_sum_integral]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  have hmain : (∫ s in (0:ℝ)..2, Real.exp (-(y*s)) * tf72Body s)
      ≤ (∑ m ∈ Finset.range 9, (-y)^m * tf72M m / (m.factorial:ℝ))
        + 2 * y^9 * tf72M 9 / ((Nat.factorial 9 : ℕ) : ℝ) := by
    linarith [hmono, hsplit, hsum, tf72Phi_rem_integral y]
  rw [tf72Phi, tf72PhiUBpos]
  exact mul_le_mul_of_nonneg_left hmain (by norm_num : (0:ℝ) ≤ 1/30)

end Work.ZeroFreeTables
