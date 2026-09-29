import Mathlib
import Submission.Work.ALift.bridge

/-!
# Area ALift — summability of the coefficient series of `H` at `‖q‖ ≤ 9/10`

Under the absurd relation `ARel a b c` the series `H = a H_A + b H_B + c H_C` overconverges to
radius `1` (`Work.ALift.coef_bound_A`): there is `C ≥ 0` with `‖hcoef a b c k‖ ≤ C·(11/10)^k` for
all `k`.  Hence for `‖q‖ ≤ 9/10` the three coefficient series defining `U₀, U₁, U₂`
(`Work.ALift.HU0`, `HU1`, `HU2`) converge absolutely: each summand is bounded by a *fixed
constant times a polynomial in `k` times `(99/100)^k`*, and `Σ kᵈ r^k` converges for `r < 1`.

This is the convergence input for the continuation `HLiftContA` of `H` along a lift of `φ_A`.
-/

namespace Work.ALift

private lemma norm_natCast_add (k : ℕ) (m : ℕ) :
    ‖((k : ℂ) + (m : ℂ))‖ = (k : ℝ) + m := by
  have h1 : ((k : ℂ) + (m : ℂ)) = (((k : ℝ) + m : ℝ) : ℂ) := by push_cast; ring
  rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

private lemma norm_natCast_add_one (k : ℕ) : ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 := by
  simpa using norm_natCast_add k 1

private lemma norm_natCast_add_two (k : ℕ) : ‖((k : ℂ) + 2)‖ = (k : ℝ) + 2 := by
  simpa using norm_natCast_add k 2

/-- `Σ (k+1) r^k` converges for `‖r‖ < 1`. -/
private lemma summable_add_one_mul_geom (r : ℝ) (hr : ‖r‖ < 1) :
    Summable (fun k : ℕ => ((k : ℝ) + 1) * r ^ k) := by
  have hA := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr
  have hB := summable_geometric_of_norm_lt_one hr
  exact hA.add hB |>.congr (fun k => by simp [pow_one, add_mul])

/-- `Σ (k+1)(k+2) r^k` converges for `‖r‖ < 1`. -/
private lemma summable_add_one_mul_add_two_mul_geom (r : ℝ) (hr : ‖r‖ < 1) :
    Summable (fun k : ℕ => ((k : ℝ) + 1) * ((k : ℝ) + 2) * r ^ k) := by
  have h2 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hr
  have h1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr
  have h0 := summable_geometric_of_norm_lt_one hr
  have h := (h2.add (h1.mul_left 3)).add (h0.mul_left 2)
  exact h.congr (fun k => by ring)

private lemma geom_shift (k : ℕ) :
    (11 / 10 : ℝ) ^ (k + 1) * (9 / 10) ^ k = (11 / 10) * (99 / 100) ^ k := by
  calc (11 / 10 : ℝ) ^ (k + 1) * (9 / 10) ^ k
      = (11 / 10) ^ k * (11 / 10) * (9 / 10) ^ k := by rw [pow_succ]
    _ = (11 / 10) * ((11 / 10) ^ k * (9 / 10) ^ k) := by ring
    _ = (11 / 10) * (99 / 100) ^ k := by rw [← mul_pow]; norm_num

private lemma geom_shift2 (k : ℕ) :
    (11 / 10 : ℝ) ^ (k + 2) * (9 / 10) ^ k = (11 / 10) ^ 2 * (99 / 100) ^ k := by
  calc (11 / 10 : ℝ) ^ (k + 2) * (9 / 10) ^ k
      = (11 / 10) ^ k * (11 / 10) ^ 2 * (9 / 10) ^ k := by rw [pow_add]
    _ = (11 / 10) ^ 2 * ((11 / 10) ^ k * (9 / 10) ^ k) := by ring
    _ = (11 / 10) ^ 2 * (99 / 100) ^ k := by rw [← mul_pow]; norm_num

private lemma bound2_eq (C : ℝ) (k : ℕ) :
    ((k : ℝ) + 1) * (C * (11 / 10 : ℝ) ^ (k + 1)) * (9 / 10) ^ k
      = (C * (11 / 10)) * (((k : ℝ) + 1) * (99 / 100 : ℝ) ^ k) := by
  calc ((k : ℝ) + 1) * (C * (11 / 10 : ℝ) ^ (k + 1)) * (9 / 10) ^ k
      = ((k : ℝ) + 1) * C * ((11 / 10 : ℝ) ^ (k + 1) * (9 / 10) ^ k) := by ring
    _ = ((k : ℝ) + 1) * C * ((11 / 10 : ℝ) * (99 / 100 : ℝ) ^ k) := by rw [geom_shift]
    _ = (C * (11 / 10 : ℝ)) * (((k : ℝ) + 1) * (99 / 100 : ℝ) ^ k) := by ring

private lemma bound3_eq (C : ℝ) (k : ℕ) :
    ((k : ℝ) + 1) * ((k : ℝ) + 2) * (C * (11 / 10 : ℝ) ^ (k + 2)) * (9 / 10) ^ k
      = (C * (11 / 10 : ℝ) ^ 2) * (((k : ℝ) + 1) * ((k : ℝ) + 2) * (99 / 100 : ℝ) ^ k) := by
  calc ((k : ℝ) + 1) * ((k : ℝ) + 2) * (C * (11 / 10 : ℝ) ^ (k + 2)) * (9 / 10) ^ k
      = ((k : ℝ) + 1) * ((k : ℝ) + 2) * C * ((11 / 10 : ℝ) ^ (k + 2) * (9 / 10) ^ k) := by ring
    _ = ((k : ℝ) + 1) * ((k : ℝ) + 2) * C * ((11 / 10 : ℝ) ^ 2 * (99 / 100 : ℝ) ^ k) := by
          rw [geom_shift2]
    _ = (C * (11 / 10 : ℝ) ^ 2) * (((k : ℝ) + 1) * ((k : ℝ) + 2) * (99 / 100 : ℝ) ^ k) := by ring

theorem summable_norm_HU (a b c : ℤ) (hRel : Submission.CDTPlan.ARel a b c) (q : ℂ) (hq : ‖q‖ ≤ 9 / 10) :
    Summable (fun k : ℕ => ‖Work.ALift.hcoef a b c k * q ^ k‖) ∧
      Summable (fun k : ℕ => ‖((k : ℂ) + 1) * Work.ALift.hcoef a b c (k + 1) * q ^ k‖) ∧
      Summable (fun k : ℕ => ‖((k : ℂ) + 1) * ((k : ℂ) + 2) * Work.ALift.hcoef a b c (k + 2) * q ^ k‖) := by
  obtain ⟨C, hC0, hCb⟩ := coef_bound_A a b c hRel
  have hq0 : 0 ≤ ‖q‖ := norm_nonneg q
  have h99 : ‖(99 / 100 : ℝ)‖ < 1 := by norm_num
  -- the three comparison series
  have hg1 : Summable (fun k : ℕ => C * (99 / 100 : ℝ) ^ k) :=
    (summable_geometric_of_norm_lt_one h99).mul_left C
  have hg2 : Summable (fun k : ℕ => (C * (11 / 10)) * (((k : ℝ) + 1) * (99 / 100 : ℝ) ^ k)) :=
    (summable_add_one_mul_geom (99 / 100) h99).mul_left (C * (11 / 10))
  have hg3 : Summable (fun k : ℕ => (C * (11 / 10) ^ 2) *
      (((k : ℝ) + 1) * ((k : ℝ) + 2) * (99 / 100 : ℝ) ^ k)) :=
    (summable_add_one_mul_add_two_mul_geom (99 / 100) h99).mul_left (C * (11 / 10) ^ 2)
  refine ⟨Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) hg1,
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) hg2,
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) hg3⟩
  · calc ‖hcoef a b c k * q ^ k‖ = ‖hcoef a b c k‖ * ‖q‖ ^ k := by rw [norm_mul, norm_pow]
      _ ≤ (C * (11 / 10 : ℝ) ^ k) * (9 / 10) ^ k :=
          mul_le_mul (hCb k) (pow_le_pow_left₀ hq0 hq k) (by positivity)
            (mul_nonneg hC0 (by positivity))
      _ = C * (99 / 100 : ℝ) ^ k := by rw [mul_assoc, ← mul_pow]; norm_num
  · calc ‖((k : ℂ) + 1) * hcoef a b c (k + 1) * q ^ k‖
        = ((k : ℝ) + 1) * ‖hcoef a b c (k + 1)‖ * ‖q‖ ^ k := by
          simp only [norm_mul, norm_pow, norm_natCast_add_one]
      _ ≤ ((k : ℝ) + 1) * (C * (11 / 10 : ℝ) ^ (k + 1)) * (9 / 10) ^ k := by
          have hb : ‖hcoef a b c (k + 1)‖ * ‖q‖ ^ k ≤
              (C * (11 / 10) ^ (k + 1)) * (9 / 10) ^ k :=
            mul_le_mul (hCb (k + 1)) (pow_le_pow_left₀ hq0 hq k) (by positivity)
              (mul_nonneg hC0 (by positivity))
          calc ((k : ℝ) + 1) * ‖hcoef a b c (k + 1)‖ * ‖q‖ ^ k
              = ((k : ℝ) + 1) * (‖hcoef a b c (k + 1)‖ * ‖q‖ ^ k) := by ring
            _ ≤ ((k : ℝ) + 1) * ((C * (11 / 10) ^ (k + 1)) * (9 / 10) ^ k) :=
                mul_le_mul_of_nonneg_left hb (by positivity)
            _ = ((k : ℝ) + 1) * (C * (11 / 10 : ℝ) ^ (k + 1)) * (9 / 10) ^ k := by ring
      _ = (C * (11 / 10)) * (((k : ℝ) + 1) * (99 / 100 : ℝ) ^ k) := bound2_eq C k
  · calc ‖((k : ℂ) + 1) * ((k : ℂ) + 2) * hcoef a b c (k + 2) * q ^ k‖
        = ((k : ℝ) + 1) * ((k : ℝ) + 2) * ‖hcoef a b c (k + 2)‖ * ‖q‖ ^ k := by
          simp only [norm_mul, norm_pow, norm_natCast_add_one, norm_natCast_add_two]
      _ ≤ ((k : ℝ) + 1) * ((k : ℝ) + 2) * (C * (11 / 10 : ℝ) ^ (k + 2)) * (9 / 10) ^ k := by
          have hb : ‖hcoef a b c (k + 2)‖ * ‖q‖ ^ k ≤
              (C * (11 / 10) ^ (k + 2)) * (9 / 10) ^ k :=
            mul_le_mul (hCb (k + 2)) (pow_le_pow_left₀ hq0 hq k) (by positivity)
              (mul_nonneg hC0 (by positivity))
          calc ((k : ℝ) + 1) * ((k : ℝ) + 2) * ‖hcoef a b c (k + 2)‖ * ‖q‖ ^ k
              = ((k : ℝ) + 1) * ((k : ℝ) + 2) * (‖hcoef a b c (k + 2)‖ * ‖q‖ ^ k) := by ring
            _ ≤ ((k : ℝ) + 1) * ((k : ℝ) + 2) * ((C * (11 / 10) ^ (k + 2)) * (9 / 10) ^ k) :=
                mul_le_mul_of_nonneg_left hb (by positivity)
            _ = ((k : ℝ) + 1) * ((k : ℝ) + 2) * (C * (11 / 10 : ℝ) ^ (k + 2)) * (9 / 10) ^ k := by
                  ring
      _ = (C * (11 / 10) ^ 2) * (((k : ℝ) + 1) * ((k : ℝ) + 2) * (99 / 100 : ℝ) ^ k) :=
            bound3_eq C k

end Work.ALift
