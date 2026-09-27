import Mathlib
import Submission.Work.EQ.Fatou.ParsevalAux

/-! The finite Parseval identity for a trigonometric polynomial:
`∫_0^{2π} ‖∑_{n<N} aₙ (ρ e^{iθ})ⁿ‖² dθ = 2π ∑_{n<N} ‖aₙ‖² ρ^{2n}`. -/

namespace Work.EQ.Fatou

open Complex MeasureTheory

/-- `Complex.ofReal` commutes with interval integrals. -/
lemma ofReal_intervalIntegral {a b : ℝ} {f : ℝ → ℝ} :
    Complex.ofReal (∫ x in a..b, f x) = ∫ x in a..b, (Complex.ofReal (f x)) :=
  (RCLike.intervalIntegral_ofReal (𝕜 := ℂ) (f := f) (a := a) (b := b)).symm

lemma star_exp' (z : ℂ) : (starRingEnd ℂ) (Complex.exp z) = Complex.exp ((starRingEnd ℂ) z) :=
  (Complex.exp_conj z).symm

lemma star_thetaI (θ : ℝ) : (starRingEnd ℂ) ((θ:ℂ) * Complex.I) = -((θ:ℂ) * Complex.I) := by
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring

lemma star_exp_thetaI (θ : ℝ) :
    (starRingEnd ℂ) (Complex.exp ((θ:ℂ) * Complex.I)) = Complex.exp (-((θ:ℂ) * Complex.I)) := by
  rw [star_exp', star_thetaI]

/-- Expansion of a single product term `(c wⁿ) · conj (d wᵐ)` with `w = ρ e^{iθ}`. -/
lemma mul_conj_term (c d : ℂ) (ρ θ : ℝ) (n m : ℕ) :
    (c * ((ρ:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))^n)
        * (starRingEnd ℂ) (d * ((ρ:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))^m)
      = (c * (starRingEnd ℂ) d) * (ρ:ℂ)^(n+m)
          * (Complex.exp ((n:ℂ) * (θ:ℂ) * Complex.I)
              * Complex.exp (-((m:ℂ) * (θ:ℂ) * Complex.I))) := by
  rw [map_mul, map_pow, map_mul, Complex.conj_ofReal, star_exp_thetaI]
  rw [mul_pow, mul_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  have e1 : (↑n : ℂ) * ((θ:ℂ) * Complex.I) = (n:ℂ) * (θ:ℂ) * Complex.I := by ring
  have e2 : (↑m : ℂ) * (-((θ:ℂ) * Complex.I)) = -((m:ℂ) * (θ:ℂ) * Complex.I) := by ring
  rw [e1, e2]
  ring

/-- Integral of the doubly indexed sum appearing in the expansion of `‖∑_{n<N} aₙ wⁿ‖²`. -/
lemma integral_double_sum_exp (a : ℕ → ℂ) (ρ : ℝ) (N : ℕ) :
    ∫ θ in (0:ℝ)..2 * Real.pi,
        ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
          (a n * (starRingEnd ℂ) (a m)) * (ρ:ℂ)^(n+m)
            * (Complex.exp ((n:ℂ) * (θ:ℂ) * Complex.I)
                * Complex.exp (-((m:ℂ) * (θ:ℂ) * Complex.I)))
      = (2 * Real.pi : ℂ) * ∑ n ∈ Finset.range N, (‖a n‖^2 : ℂ) * (ρ:ℂ)^(2*n) := by
  have hcont : ∀ n m : ℕ, Continuous (fun θ : ℝ =>
      (a n * (starRingEnd ℂ) (a m)) * (ρ:ℂ)^(n+m)
        * (Complex.exp ((n:ℂ) * (θ:ℂ) * Complex.I)
            * Complex.exp (-((m:ℂ) * (θ:ℂ) * Complex.I)))) := by
    intro n m; fun_prop
  have hcont' : ∀ n : ℕ, Continuous (fun θ : ℝ => ∑ m ∈ Finset.range N,
      (a n * (starRingEnd ℂ) (a m)) * (ρ:ℂ)^(n+m)
        * (Complex.exp ((n:ℂ) * (θ:ℂ) * Complex.I)
            * Complex.exp (-((m:ℂ) * (θ:ℂ) * Complex.I)))) := by
    intro n; fun_prop
  have hcollapse : (∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        (a n * (starRingEnd ℂ) (a m)) * (ρ:ℂ)^(n+m)
          * (if n = m then (2 * Real.pi : ℂ) else 0))
      = (2 * Real.pi : ℂ) * ∑ n ∈ Finset.range N, (‖a n‖^2 : ℂ) * (ρ:ℂ)^(2*n) := by
    have hinner : ∀ n, (∑ m ∈ Finset.range N,
          (a n * (starRingEnd ℂ) (a m)) * (ρ:ℂ)^(n+m)
            * (if n = m then (2 * Real.pi : ℂ) else 0))
        = if n ∈ Finset.range N
            then (a n * (starRingEnd ℂ) (a n)) * (ρ:ℂ)^(2*n) * (2 * Real.pi : ℂ) else 0 := by
      intro n
      rw [Finset.sum_congr rfl (fun m _ => by rw [mul_ite, mul_zero])]
      rw [Finset.sum_ite_eq]
      by_cases h : n ∈ Finset.range N
      · rw [if_pos h, if_pos h, show n + n = 2 * n from by ring]
      · rw [if_neg h, if_neg h]
    have hterm : ∀ n, (a n * (starRingEnd ℂ) (a n)) * (ρ:ℂ)^(2*n) * (2 * Real.pi : ℂ)
        = (2 * Real.pi : ℂ) * ((‖a n‖^2 : ℂ) * (ρ:ℂ)^(2*n)) := by
      intro n
      rw [show a n * (starRingEnd ℂ) (a n) = ((‖a n‖^2 : ℝ) : ℂ) from by
            rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]]
      rw [Complex.ofReal_pow]
      ring
    rw [Finset.sum_congr rfl (fun n _ => hinner n)]
    rw [Finset.sum_congr rfl (fun n hn => if_pos hn)]
    rw [Finset.sum_congr rfl (fun n _ => hterm n), Finset.mul_sum]
  have hG : ∀ n m : ℕ, IntervalIntegrable (fun θ : ℝ =>
      (a n * (starRingEnd ℂ) (a m)) * (ρ:ℂ)^(n+m)
        * (Complex.exp ((n:ℂ) * (θ:ℂ) * Complex.I)
            * Complex.exp (-((m:ℂ) * (θ:ℂ) * Complex.I)))) volume (0:ℝ) (2 * Real.pi) :=
    fun n m => (hcont n m).intervalIntegrable _ _
  have hG' : ∀ n : ℕ, IntervalIntegrable (fun θ : ℝ => ∑ m ∈ Finset.range N,
      (a n * (starRingEnd ℂ) (a m)) * (ρ:ℂ)^(n+m)
        * (Complex.exp ((n:ℂ) * (θ:ℂ) * Complex.I)
            * Complex.exp (-((m:ℂ) * (θ:ℂ) * Complex.I)))) volume (0:ℝ) (2 * Real.pi) :=
    fun n => (hcont' n).intervalIntegrable _ _
  have hstep : ∀ n : ℕ, (∫ θ in (0:ℝ)..2 * Real.pi, ∑ m ∈ Finset.range N,
        (a n * (starRingEnd ℂ) (a m)) * (ρ:ℂ)^(n+m)
          * (Complex.exp ((n:ℂ) * (θ:ℂ) * Complex.I)
              * Complex.exp (-((m:ℂ) * (θ:ℂ) * Complex.I))))
      = ∑ m ∈ Finset.range N, (a n * (starRingEnd ℂ) (a m)) * (ρ:ℂ)^(n+m)
          * (if n = m then (2 * Real.pi : ℂ) else 0) := by
    intro n
    rw [intervalIntegral.integral_finsetSum (fun m _ => hG n m)]
    apply Finset.sum_congr rfl
    intro m _
    rw [intervalIntegral.integral_const_mul, intervalIntegral_cexp_mul_conj]
  rw [intervalIntegral.integral_finsetSum (fun n _ => hG' n)]
  rw [Finset.sum_congr rfl (fun n _ => hstep n)]
  rw [hcollapse]

/-- **Finite Parseval identity.** -/
theorem integral_partialSum_normSq (a : ℕ → ℂ) (ρ : ℝ) (N : ℕ) :
    ∫ θ in (0:ℝ)..2 * Real.pi,
        ‖∑ n ∈ Finset.range N, a n * (ρ * Complex.exp ((θ:ℂ) * Complex.I))^n‖^2
      = 2 * Real.pi * ∑ n ∈ Finset.range N, ‖a n‖^2 * ρ^(2*n) := by
  have hmain : (∫ θ in (0:ℝ)..2 * Real.pi,
        (∑ n ∈ Finset.range N, a n * ((ρ:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))^n)
          * (starRingEnd ℂ) (∑ n ∈ Finset.range N,
              a n * ((ρ:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))^n))
      = (2 * Real.pi : ℂ) * ∑ n ∈ Finset.range N, (‖a n‖^2 : ℂ) * (ρ:ℂ)^(2*n) := by
    rw [show (fun θ : ℝ =>
          (∑ n ∈ Finset.range N, a n * ((ρ:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))^n)
            * (starRingEnd ℂ) (∑ n ∈ Finset.range N,
                a n * ((ρ:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))^n))
        = (fun θ : ℝ => ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
              (a n * (starRingEnd ℂ) (a m)) * (ρ:ℂ)^(n+m)
                * (Complex.exp ((n:ℂ) * (θ:ℂ) * Complex.I)
                    * Complex.exp (-((m:ℂ) * (θ:ℂ) * Complex.I)))) from by
        funext θ
        rw [map_sum, Finset.sum_mul_sum]
        apply Finset.sum_congr rfl; intro n _
        apply Finset.sum_congr rfl; intro m _
        exact mul_conj_term (a n) (a m) ρ θ n m]
    rw [integral_double_sum_exp]
  refine Complex.ofReal_inj.mp ?_
  rw [ofReal_intervalIntegral]
  rw [show (fun θ : ℝ => Complex.ofReal
          (‖∑ n ∈ Finset.range N, a n * ((ρ:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))^n‖^2))
      = (fun θ : ℝ =>
          (∑ n ∈ Finset.range N, a n * ((ρ:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))^n)
            * (starRingEnd ℂ) (∑ n ∈ Finset.range N,
                a n * ((ρ:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))^n)) from by
        funext θ
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]]
  rw [hmain]
  push_cast
  ring

end Work.EQ.Fatou
