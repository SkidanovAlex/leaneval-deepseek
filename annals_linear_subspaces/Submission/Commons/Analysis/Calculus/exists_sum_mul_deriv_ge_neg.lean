import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

namespace Commons.Analysis.Calculus

open scoped BigOperators
open MeasureTheory

/-- If `Λ i` are `C`-Lipschitz functions `ℝ → ℝ`, then for every `c > 0` and `T` there is a
point `t ≥ T` at which all `Λ i` are differentiable and `∑ i, Λ i t * deriv (Λ i) t ≥ -c`. -/
theorem exists_sum_mul_deriv_ge_neg {d : ℕ} {Λ : Fin d → ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hΛ : ∀ (i : Fin d) (s t : ℝ), |Λ i s - Λ i t| ≤ C * |s - t|) {c : ℝ} (hc : 0 < c) (T : ℝ) :
    ∃ t : ℝ, T ≤ t ∧ (∀ i, DifferentiableAt ℝ (Λ i) t) ∧
      -c ≤ ∑ i, Λ i t * deriv (Λ i) t := by
  by_contra hcon
  push Not at hcon
  have hKC : (Real.toNNReal C : ℝ) = C := Real.coe_toNNReal C hC
  have hLip : ∀ i : Fin d, LipschitzWith (Real.toNNReal C) (Λ i) := fun i =>
    LipschitzWith.of_dist_le_mul (fun s t => by
      rw [Real.dist_eq, Real.dist_eq, hKC]
      exact hΛ i s t)
  let F : ℝ → ℝ := fun t => ∑ i, Λ i t * Λ i t
  have hFnn : ∀ t, 0 ≤ F t := fun t => Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hdiff_ae : ∀ᵐ t ∂volume, ∀ i, DifferentiableAt ℝ (Λ i) t :=
    Filter.eventually_all.2 fun i => (hLip i).ae_differentiableAt_real
  have hderiv_ae : ∀ᵐ t ∂volume, deriv F t = 2 * ∑ i, Λ i t * deriv (Λ i) t := by
    filter_upwards [hdiff_ae] with t ht
    have hA : ∀ i ∈ (Finset.univ : Finset (Fin d)),
        DifferentiableAt ℝ (fun s => Λ i s * Λ i s) t := fun i _ => (ht i).mul (ht i)
    have h1 : deriv F t = ∑ i, deriv (fun s => Λ i s * Λ i s) t := by
      have := deriv_fun_sum (u := Finset.univ) (A := fun i s => Λ i s * Λ i s) (x := t) hA
      simpa [F] using this
    have h2 : ∀ i : Fin d, deriv (fun s => Λ i s * Λ i s) t
        = 2 * (Λ i t * deriv (Λ i) t) := by
      intro i
      rw [deriv_fun_mul (ht i) (ht i)]
      ring
    rw [h1]
    simp only [h2]
    rw [Finset.mul_sum]
  set N : ℝ := F T / (2 * c) + 1 with hNdef
  have hAC_i : ∀ i : Fin d,
      AbsolutelyContinuousOnInterval (fun t => Λ i t * Λ i t) T (T + N) := fun i => by
    have hi : AbsolutelyContinuousOnInterval (Λ i) T (T + N) :=
      (hLip i).lipschitzOnWith.absolutelyContinuousOnInterval
    exact hi.mul hi
  have hAC_sum : ∀ s : Finset (Fin d),
      AbsolutelyContinuousOnInterval (fun t => ∑ i ∈ s, Λ i t * Λ i t) T (T + N) := by
    intro s
    induction s using Finset.induction with
    | empty =>
        have h0 : AbsolutelyContinuousOnInterval (fun _ : ℝ => (0 : ℝ)) T (T + N) :=
          (LipschitzWith.const (0 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
        simpa using h0
    | insert i s hi ih =>
        have h := (hAC_i i).add ih
        have hgoal : (fun t => ∑ k ∈ insert i s, Λ k t * Λ k t)
            = (fun t => Λ i t * Λ i t + ∑ k ∈ s, Λ k t * Λ k t) := by
          funext t; rw [Finset.sum_insert hi]
        rw [hgoal]
        exact h
  have hF_ac : AbsolutelyContinuousOnInterval F T (T + N) := by
    have := hAC_sum Finset.univ
    simpa [F] using this
  have hNpos : 0 < N := by
    have hnn : 0 ≤ F T / (2 * c) := div_nonneg (hFnn T) (by positivity)
    rw [hNdef]; linarith
  have hTle : T ≤ T + N := by linarith
  have hle_ae : (fun t => deriv F t) ≤ᵐ[volume.restrict (Set.Icc T (T + N))] (fun _ => -2 * c) := by
    change ∀ᵐ t ∂volume.restrict (Set.Icc T (T + N)), deriv F t ≤ -2 * c
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hdiff_ae, hderiv_ae] with t hd hdt ht
    have htT : T ≤ t := ht.1
    have hS : ∑ i, Λ i t * deriv (Λ i) t < -c := hcon t htT hd
    rw [hdt]
    linarith
  have hFTC : ∫ t in T..(T + N), deriv F t = F (T + N) - F T := hF_ac.integral_deriv_eq_sub
  have hmono : ∫ t in T..(T + N), deriv F t ≤ ∫ t in T..(T + N), (-2 * c) :=
    intervalIntegral.integral_mono_ae_restrict hTle hF_ac.intervalIntegrable_deriv
      intervalIntegrable_const hle_ae
  have hconst : ∫ t in T..(T + N), (-2 * c) = N * (-2 * c) := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  have h2cN : 2 * c * N = F T + 2 * c := by
    rw [hNdef]
    field_simp
  have hneg : N * (-2 * c) = -(F T + 2 * c) := by
    rw [← h2cN]; ring
  have hbound : F (T + N) - F T ≤ N * (-2 * c) := by
    rw [← hFTC, ← hconst]
    exact hmono
  have : F (T + N) < 0 := by
    rw [hneg] at hbound
    linarith [hFnn (T + N)]
  exact absurd (hFnn (T + N)) (not_le.mpr this)

end Commons.Analysis.Calculus