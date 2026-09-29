import Mathlib
import Submission.Work.OdeCont.defs
import Submission.Work.OdeCont.iterAlong_continuousOn
import Submission.Work.OdeCont.iter_sub_eq_integral

/-!
# The Cauchy-type bound for the Picard iterates

For the initial value problem `X' = F(z, X)`, `X(z₀) = y`, with

`iter (n+1) z = y + ∫ t in 0..1, (z - z₀) • F (z₀ + t • (z - z₀)) (iter n (z₀ + t • (z - z₀)))`,

and with a convex `S ∋ z₀` contained in the disc of radius `D` around `z₀` on which `F` is
`K`-Lipschitz in its second variable and bounded by `B` at `y`, the successive differences of the
iterates satisfy

`‖iter (n+1) z - iter n z‖ ≤ (D * B) * K ^ n * ‖z - z₀‖ ^ n / n !`   for `z ∈ S`.

The proof is the standard one: `iter (n+2) z - iter (n+1) z` is the integral of
`(z - z₀) • (F (…) (iter (n+1) (…)) - F (…) (iter n (…)))` (`iter_sub_eq_integral`), the
integrand is bounded pointwise via the Lipschitz bound and the induction hypothesis, and
`∫_0^1 C * t ^ n = C / (n + 1)` (with `(n+1) ! = (n+1) · n !`) gives the induction step.

Note: the statement uses the Mathlib factorial notation `n !` (the source statement wrote it
without the space, which the parser of this module — `autoImplicit = false` — cannot read).
-/

open scoped Nat

noncomputable section

open MeasureTheory

namespace Work.OdeCont

/-- Convexity: the point `z₀ + t • (z - z₀)` of the segment from `z₀` to `z` lies in `S`
whenever `z₀, z ∈ S`, `S` is convex and `t ∈ [0,1]`. -/
lemma iter_bound_segment_mem {S : Set ℂ} (hS : Convex ℝ S) {z₀ z : ℂ} (hz₀ : z₀ ∈ S) (hz : z ∈ S)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) : z₀ + t • (z - z₀) ∈ S := by
  have h1 : (0:ℝ) ≤ 1 - t := by linarith [ht.2]
  have h2 : (0:ℝ) ≤ t := ht.1
  have h3 : (1 - t) + t = 1 := by ring
  have hh := hS hz₀ hz h1 h2 h3
  convert hh using 1
  module

/-- Monotonicity of the interval integral over `[0,1]` for continuous real-valued functions. -/
lemma iter_bound_integral_mono {f g : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1))
    (hg : ContinuousOn g (Set.Icc 0 1)) (hfg : ∀ t ∈ Set.Icc 0 1, f t ≤ g t) :
    ∫ t in (0:ℝ)..1, f t ≤ ∫ t in (0:ℝ)..1, g t := by
  have h01 : (0:ℝ) ≤ 1 := by norm_num
  have hui : Set.uIcc (0:ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le h01
  refine intervalIntegral.integral_mono_on h01 ?_ ?_ hfg
  · have : ContinuousOn f (Set.uIcc (0:ℝ) 1) := by rw [hui]; exact hf
    exact this.intervalIntegrable
  · have : ContinuousOn g (Set.uIcc (0:ℝ) 1) := by rw [hui]; exact hg
    exact this.intervalIntegrable

/-- `∫_0^1 C * t ^ n dt = C / (n + 1)`. -/
lemma iter_bound_integral_mul_pow (C : ℝ) (n : ℕ) :
    ∫ t in (0:ℝ)..1, C * t ^ n = C / ((n : ℝ) + 1) := by
  rw [intervalIntegral.integral_const_mul, integral_pow]
  simp only [one_pow, zero_pow (Nat.succ_ne_zero n), sub_zero]
  ring

/-- The arithmetic identity of the induction step:
`(c·K·(D·B·Kⁿ)·cⁿ / n!) / (n+1) = D·B·Kⁿ⁺¹·cⁿ⁺¹ / (n+1)!`. -/
lemma iter_bound_arith (c K D B : ℝ) (n : ℕ) :
    c * K * (D * B * K ^ n) * c ^ n / (Nat.factorial n : ℝ) / ((n:ℝ)+1)
      = (D * B) * K ^ (n+1) * c ^ (n+1) / (Nat.factorial (n+1) : ℝ) := by
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [pow_succ, pow_succ]
  have hnf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have hn1 : ((n:ℝ) + 1) ≠ 0 := by positivity
  field_simp

theorem iter_bound {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (F : ℂ → V → V) (z₀ : ℂ) (y : V) (S : Set ℂ) (K B D : ℝ)
    (hK : 0 ≤ K) (hB : 0 ≤ B) (hD0 : 0 ≤ D)
    (hS : Convex ℝ S) (hz₀ : z₀ ∈ S)
    (hD : ∀ z ∈ S, ‖z - z₀‖ ≤ D)
    (hLip : ∀ w ∈ S, ∀ x y : V, ‖F w x - F w y‖ ≤ K * ‖x - y‖)
    (hbase : ∀ w ∈ S, ‖F w y‖ ≤ B)
    (hGcont : ∀ n, ContinuousOn (fun w => F w (iter F z₀ y n w)) S) :
    ∀ n (z : ℂ), z ∈ S →
      ‖iter F z₀ y (n+1) z - iter F z₀ y n z‖ ≤ (D * B) * K ^ n * ‖z - z₀‖ ^ n / n ! := by
  intro n z hz
  induction n generalizing z with
  | zero =>
    simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one]
    have hdiff : iter F z₀ y (0+1) z - iter F z₀ y 0 z
        = ∫ t in (0:ℝ)..1, (z - z₀) • F (z₀ + t • (z - z₀)) y := by
      rw [iter_succ F z₀ y 0 z]
      simp only [iter_zero]
      abel
    rw [hdiff]
    have hcont0 := iterAlong_continuousOn F z₀ y S hS hz₀ hGcont 0 z hz
    have hcont : ContinuousOn (fun t : ℝ => (z - z₀) • F (z₀ + t • (z - z₀)) y) (Set.Icc 0 1) :=
      hcont0.const_smul (z - z₀)
    calc ‖∫ t in (0:ℝ)..1, (z - z₀) • F (z₀ + t • (z - z₀)) y‖
        ≤ ∫ t in (0:ℝ)..1, ‖(z - z₀) • F (z₀ + t • (z - z₀)) y‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by norm_num)
      _ ≤ ∫ t in (0:ℝ)..1, ‖z - z₀‖ * B := by
          refine iter_bound_integral_mono hcont.norm continuousOn_const ?_
          intro t ht
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_left (hbase _ (iter_bound_segment_mem hS hz₀ hz ht))
            (norm_nonneg _)
      _ = ‖z - z₀‖ * B := by
          rw [intervalIntegral.integral_const]
          simp
      _ ≤ D * B := mul_le_mul_of_nonneg_right (hD z hz) hB
  | succ n ih =>
    have hrepr : iter F z₀ y ((n+1)+1) z - iter F z₀ y (n+1) z
        = ∫ t in (0:ℝ)..1, (z - z₀) •
            (F (z₀ + t • (z - z₀)) (iter F z₀ y (n+1) (z₀ + t • (z - z₀)))
              - F (z₀ + t • (z - z₀)) (iter F z₀ y n (z₀ + t • (z - z₀)))) :=
      iter_sub_eq_integral F z₀ y S hS hz₀ hGcont n z hz
    rw [hrepr]
    set c : ℝ := ‖z - z₀‖ with hc
    have hc0 : 0 ≤ c := by rw [hc]; exact norm_nonneg _
    set C : ℝ := c * K * (D * B * K ^ n) * c ^ n / (Nat.factorial n : ℝ) with hC
    have hcont1 := iterAlong_continuousOn F z₀ y S hS hz₀ hGcont (n+1) z hz
    have hcont2 := iterAlong_continuousOn F z₀ y S hS hz₀ hGcont n z hz
    have hVcont : ContinuousOn (fun t : ℝ => (z - z₀) •
        (F (z₀ + t • (z - z₀)) (iter F z₀ y (n+1) (z₀ + t • (z - z₀)))
          - F (z₀ + t • (z - z₀)) (iter F z₀ y n (z₀ + t • (z - z₀))))) (Set.Icc 0 1) :=
      (hcont1.sub hcont2).const_smul (z - z₀)
    have hpoint : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖(z - z₀) •
        (F (z₀ + t • (z - z₀)) (iter F z₀ y (n+1) (z₀ + t • (z - z₀)))
          - F (z₀ + t • (z - z₀)) (iter F z₀ y n (z₀ + t • (z - z₀))))‖ ≤ C * t ^ n := by
      intro t ht
      have hwt : z₀ + t • (z - z₀) ∈ S := iter_bound_segment_mem hS hz₀ hz ht
      have h1 : ‖F (z₀ + t • (z - z₀)) (iter F z₀ y (n+1) (z₀ + t • (z - z₀)))
          - F (z₀ + t • (z - z₀)) (iter F z₀ y n (z₀ + t • (z - z₀)))‖
          ≤ K * ‖iter F z₀ y (n+1) (z₀ + t • (z - z₀)) - iter F z₀ y n (z₀ + t • (z - z₀))‖ :=
        hLip _ hwt _ _
      have h2 : ‖iter F z₀ y (n+1) (z₀ + t • (z - z₀)) - iter F z₀ y n (z₀ + t • (z - z₀))‖
          ≤ (D * B) * K ^ n * ‖z₀ + t • (z - z₀) - z₀‖ ^ n / (Nat.factorial n : ℝ) :=
        ih (z₀ + t • (z - z₀)) hwt
      have hw : ‖z₀ + t • (z - z₀) - z₀‖ = t * c := by
        rw [show z₀ + t • (z - z₀) - z₀ = t • (z - z₀) by abel]
        rw [norm_smul, Real.norm_of_nonneg ht.1, hc]
      rw [norm_smul, ← hc]
      calc c * ‖F (z₀ + t • (z - z₀)) (iter F z₀ y (n+1) (z₀ + t • (z - z₀)))
            - F (z₀ + t • (z - z₀)) (iter F z₀ y n (z₀ + t • (z - z₀)))‖
          ≤ c * (K * ‖iter F z₀ y (n+1) (z₀ + t • (z - z₀))
              - iter F z₀ y n (z₀ + t • (z - z₀))‖) :=
            mul_le_mul_of_nonneg_left h1 hc0
        _ ≤ c * (K * ((D * B) * K ^ n * ‖z₀ + t • (z - z₀) - z₀‖ ^ n / (Nat.factorial n : ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hK) hc0
        _ = C * t ^ n := by
            rw [hw, hC, mul_pow]
            ring
    calc ‖∫ t in (0:ℝ)..1, (z - z₀) •
            (F (z₀ + t • (z - z₀)) (iter F z₀ y (n+1) (z₀ + t • (z - z₀)))
              - F (z₀ + t • (z - z₀)) (iter F z₀ y n (z₀ + t • (z - z₀))))‖
        ≤ ∫ t in (0:ℝ)..1, ‖(z - z₀) •
            (F (z₀ + t • (z - z₀)) (iter F z₀ y (n+1) (z₀ + t • (z - z₀)))
              - F (z₀ + t • (z - z₀)) (iter F z₀ y n (z₀ + t • (z - z₀))))‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by norm_num)
      _ ≤ ∫ t in (0:ℝ)..1, C * t ^ n :=
          iter_bound_integral_mono hVcont.norm
            (continuousOn_const.mul (continuous_id.continuousOn.pow n)) hpoint
      _ = C / ((n : ℝ) + 1) := iter_bound_integral_mul_pow C n
      _ = (D * B) * K ^ (n+1) * ‖z - z₀‖ ^ (n+1) / (n+1) ! := by
          rw [hC, hc]
          exact iter_bound_arith ‖z - z₀‖ K D B n

end Work.OdeCont
