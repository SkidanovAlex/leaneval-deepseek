/-
# Area 5 (HB Lemma 13.3): the test functions `f₁`, `F₁` and the elementary layer

This file sets up the vocabulary of Heath-Brown's Lemma 13.3 (PLMS 64 (1992), §13, p. 81):

* `f1 K lam` is HB's `f₁(t) = sinh((K-t)λ)` on `[0,K]`, `0` for `t ≥ K`;
* `F1 K lam z = ∫₀^K e^{-zt} f₁(t) dt` is its Laplace transform;
* `g0 K` is the "λ → 0 limit" test function `t ↦ (K-t)/K` on `[0,K]` (normalised so that
  `g0 K 0 = 1`), whose Laplace transform is `G0 K`; it is the λ = 0 case of Lemma 13.3.

The key analytic input, HB's (13.2) (`Re F₁(z) ≥ (λ/2)e^{Kλ}|F₂(λ+z)|` for `Re z ≥ 0`),
is `F1_re_ge` below; it is the already-proved `tentF1_re_ge` of the commons, restated in the
vocabulary of this development.
-/
import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Commons.NumberTheory.Linnik.tentF1_re_ge

open Complex DirichletCharacter Metric
open scoped Interval Topology BigOperators

noncomputable section

namespace Work.LinnikAreas.A5

/-- HB's `f₁` of Lemma 13.3: `sinh((K-t)λ)` for `0 ≤ t ≤ K`, and `0` for `t ≥ K`. -/
def f1 (K lam t : ℝ) : ℝ := if t ≤ K then Real.sinh ((K - t) * lam) else 0

/-- HB's `F₁(z) = ∫₀^∞ e^{-zt} f₁(t) dt = ∫₀^K e^{-zt} sinh((K-t)λ) dt`. -/
def F1 (K lam : ℝ) (z : ℂ) : ℂ :=
  ∫ t in (0:ℝ)..K, Complex.exp (-(z * (t : ℂ))) * ((f1 K lam t : ℝ) : ℂ)

/-- The λ → 0 limit test function, normalised to `g₀(0) = 1`. -/
def g0 (K t : ℝ) : ℝ := if t ≤ K then (K - t) / K else 0

/-- Laplace transform of `g0`. -/
def G0 (K : ℝ) (z : ℂ) : ℂ :=
  ∫ t in (0:ℝ)..K, Complex.exp (-(z * (t : ℂ))) * ((g0 K t : ℝ) : ℂ)

lemma f1_of_le {K lam t : ℝ} (h : t ≤ K) : f1 K lam t = Real.sinh ((K - t) * lam) :=
  if_pos h

lemma f1_of_ge {K lam t : ℝ} (h : K ≤ t) : f1 K lam t = 0 := by
  by_cases ht : t ≤ K
  · rw [f1_of_le ht, le_antisymm ht h]; simp
  · rw [f1]; exact if_neg ht

lemma g0_of_le {K t : ℝ} (h : t ≤ K) : g0 K t = (K - t) / K := if_pos h

lemma g0_of_ge {K t : ℝ} (h : K ≤ t) : g0 K t = 0 := by
  by_cases ht : t ≤ K
  · rw [g0_of_le ht, le_antisymm ht h]; simp
  · rw [g0]; exact if_neg ht

lemma f1_zero {K lam : ℝ} (hK : 0 ≤ K) : f1 K lam 0 = Real.sinh (K * lam) := by
  rw [f1_of_le (K := K) (lam := lam) (t := 0) hK]; ring_nf

lemma g0_zero {K : ℝ} (hK : 0 < K) : g0 K 0 = 1 := by
  rw [g0_of_le (K := K) (t := 0) hK.le, sub_zero, div_self (ne_of_gt hK)]

/-- `f₁` is a continuous function of `t` (it vanishes at `t = K`, where the two branches meet). -/
lemma continuous_f1 (K lam : ℝ) : Continuous (f1 K lam) := by
  rw [show f1 K lam = fun t : ℝ => Real.sinh (max (K - t) 0 * lam) from ?_]
  · fun_prop
  · funext t
    by_cases h : t ≤ K
    · rw [f1_of_le h, max_eq_left (by linarith : (0:ℝ) ≤ K - t)]
    · rw [f1_of_ge (not_le.mp h).le, max_eq_right (by linarith : K - t ≤ 0), zero_mul,
        Real.sinh_zero]

/-- On `[0,K]` the Laplace transform is the integral of `e^{-zt} sinh((K-t)λ)`. -/
lemma F1_eq_integral {K lam : ℝ} (hK : 0 ≤ K) (z : ℂ) :
    F1 K lam z = ∫ t in (0:ℝ)..K,
      Complex.exp (-(z * (t : ℂ))) * ((Real.sinh ((K - t) * lam) : ℝ) : ℂ) := by
  rw [F1]
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  have h : t ≤ K := by
    rw [Set.uIcc_of_le hK] at ht
    exact ht.2
  rw [f1_of_le h]

/-- **HB (13.2)**, in the vocabulary of this file: for `Re z ≥ 0`,
`Re F₁(z) ≥ (λ/2) e^{Kλ} ‖F₂(λ+z)‖`. -/
theorem F1_re_ge {K lam : ℝ} (hK : 0 < K) (hlam : 0 < lam) (z : ℂ) (hz : 0 ≤ z.re) :
    (lam / 2) * Real.exp (lam * K) * ‖Work.LinnikContract.F2 K ((lam : ℂ) + z)‖ ≤
      (F1 K lam z).re := by
  have h := Commons.NumberTheory.Linnik.tentF1_re_ge hK lam hlam z hz
  have hnorm : ‖((1 - Complex.exp (-((K : ℂ) * ((lam : ℂ) + z)))) / ((lam : ℂ) + z)) ^ 2‖
      = ‖Work.LinnikContract.F2 K ((lam : ℂ) + z)‖ := by
    rw [Work.LinnikContract.F2]
    simp only [neg_mul]
  rw [hnorm] at h
  rw [F1_eq_integral hK.le]
  exact h

end Work.LinnikAreas.A5
