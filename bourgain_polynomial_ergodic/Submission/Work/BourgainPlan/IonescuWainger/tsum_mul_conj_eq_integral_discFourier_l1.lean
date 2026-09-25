import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.FreqArc

open MeasureTheory Finset
open scoped BigOperators

namespace Work.BourgainPlan.IonescuWainger

/-- The exponential monomials have modulus one: `‖e^{2πi n ξ}‖ = 1`. -/
private lemma norm_fourier_apply (n : ℤ) (ξ : Circle) : ‖fourier n ξ‖ = 1 := by
  rw [fourier_apply]
  exact Circle.norm_coe _

/-- Orthogonality of the characters with respect to the probability Haar measure on the circle:
`∫_𝕋 e^{2πi j ξ} dξ = δ_{j,0}`. -/
private lemma integral_fourier_eq_ite (j : ℤ) :
    ∫ ξ : Circle, fourier j ξ ∂AddCircle.haarAddCircle = if j = 0 then 1 else 0 := by
  have h := ContinuousMap.inner_toLp (μ := (AddCircle.haarAddCircle : Measure Circle))
    (fourier (0 : ℤ)) (fourier j)
  have h2 := (orthonormal_iff_ite.mp (orthonormal_fourier (T := 1))) (0 : ℤ) j
  rw [h2] at h
  simp only [fourier_zero, map_one, mul_one] at h
  rw [← h]
  by_cases hj : j = 0
  · simp [hj]
  · simp [hj, eq_comm]

/-- **Parseval's identity for `ℓ¹` sequences on `ℤ`, in the `star` form.**
For absolutely summable `h, k : ℤ → ℂ` the pairing `Σ_n h n · conj (k n)` computes the integral of
the product of the discrete Fourier transforms; equivalently, the pointwise product of the two
`discFourier` transforms is the double series `Σ_{n,m} h n · conj(k m) · e^{2πi(n-m)ξ}`. -/
private lemma discFourier_mul_star_eq_tsum (h k : ℤ → ℂ) (hh : Summable fun m => ‖h m‖)
    (hk : Summable fun m => ‖k m‖) (ξ : Circle) :
    discFourier h ξ * star (discFourier k ξ)
      = ∑' p : ℤ × ℤ, (h p.1 * star (k p.2)) * fourier (p.1 - p.2) ξ := by
  have hnorm : ∀ (n : ℤ), ‖fourier n ξ‖ = 1 := fun n => norm_fourier_apply n ξ
  have hAn : ∀ n, ‖h n * fourier n ξ‖ = ‖h n‖ := fun n => by rw [norm_mul, hnorm n, mul_one]
  have hBn : ∀ m, ‖star (k m) * fourier (-m) ξ‖ = ‖k m‖ := fun m => by
    rw [norm_mul, hnorm (-m), mul_one, norm_star]
  have hA : Summable (fun n : ℤ => h n * fourier n ξ) :=
    Summable.of_norm_bounded hh (fun n => by rw [hAn n])
  have hB : Summable (fun m : ℤ => star (k m) * fourier (-m) ξ) :=
    Summable.of_norm_bounded hk (fun m => by rw [hBn m])
  have hBstar : (∑' m : ℤ, star (k m) * fourier (-m) ξ) = star (discFourier k ξ) := by
    have hk' : Summable (fun m : ℤ => k m * fourier m ξ) := by
      apply Summable.of_norm_bounded hk
      intro m; rw [norm_mul, hnorm m, mul_one]
    have hmap := Summable.map_tsum hk' (starRingEnd ℂ) continuous_star
    change (∑' m : ℤ, star (k m) * fourier (-m) ξ)
        = (starRingEnd ℂ) (∑' i : ℤ, k i * fourier i ξ) at *
    rw [hmap]
    refine tsum_congr fun m => ?_
    rw [map_mul]; congr 1; exact fourier_neg
  have hAB : Summable (fun p : ℤ × ℤ =>
      (h p.1 * fourier p.1 ξ) * (star (k p.2) * fourier (-p.2) ξ)) := by
    apply Summable.of_norm_bounded
      (Summable.mul_of_nonneg hh hk (fun n => norm_nonneg _) (fun m => norm_nonneg _))
    intro p
    rw [norm_mul, hAn, hBn]
  rw [show discFourier h ξ = ∑' n, h n * fourier n ξ from rfl]
  rw [← hBstar]
  rw [Summable.tsum_mul_tsum hA hB hAB]
  refine tsum_congr fun p => ?_
  rw [sub_eq_add_neg, fourier_add]
  ring

/-- The diagonal extraction: a series over `ℤ × ℤ` whose term is supported on the diagonal
`p.1 = p.2` collapses to the series over `ℤ`. -/
private lemma tsum_mul_conj_diag (h k : ℤ → ℂ) (hh : Summable fun m => ‖h m‖)
    (hk : Summable fun m => ‖k m‖) :
    ∑' p : ℤ × ℤ, (h p.1 * star (k p.2)) * (if p.1 - p.2 = 0 then 1 else 0)
      = ∑' n : ℤ, h n * star (k n) := by
  have hD : Summable (fun p : ℤ × ℤ =>
      (h p.1 * star (k p.2)) * (if p.1 - p.2 = 0 then 1 else 0)) := by
    apply Summable.of_norm_bounded
      (Summable.mul_of_nonneg hh hk (fun n => norm_nonneg _) (fun m => norm_nonneg _))
    intro p
    rw [norm_mul, norm_mul, norm_star]
    split_ifs <;> simp only [norm_one, mul_one, norm_zero, mul_zero, le_refl]
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hDs : ∀ n, Summable (fun m : ℤ =>
      (h n * star (k m)) * (if n - m = 0 then 1 else 0)) := by
    intro n
    apply Summable.of_norm_bounded (hk.mul_left ‖h n‖)
    intro m
    rw [norm_mul, norm_mul, norm_star]
    split_ifs <;> simp only [norm_one, mul_one, norm_zero, mul_zero, le_refl]
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  rw [Summable.tsum_prod' hD hDs]
  refine tsum_congr fun n => ?_
  rw [tsum_eq_single n (fun m hm => by
    have h1 : n - m ≠ 0 := sub_ne_zero.mpr (Ne.symm hm)
    rw [if_neg h1, mul_zero])]
  rw [sub_self, if_pos rfl, mul_one]

/-- **Parseval's identity for absolutely summable sequences on `ℤ`.**

For `h, k : ℤ → ℂ` with `Σ_n ‖h n‖ < ∞` and `Σ_n ‖k n‖ < ∞`,

`Σ'_n h n · conj (k n) = ∫_𝕋 𝓕h ξ · conj (𝓕k ξ) dξ`,

where `discFourier f ξ = Σ'_n f n · e^{2πi n ξ}` and the integral is against the probability Haar
measure `AddCircle.haarAddCircle` on `𝕋 = ℝ/ℤ`.  This is the `ℓ¹` version of
`tsum_mul_conj_eq_integral_discFourier`; both sides are absolute-convergent series/integrals and the
identity follows by dominated convergence (`integral_tsum_of_summable_integral_norm`) applied to the
double series `Σ_{n,m} h n · conj (k m) · e^{2πi(n-m)ξ}` together with character orthogonality. -/
theorem tsum_mul_conj_eq_integral_discFourier_l1 {h k : ℤ → ℂ} (hh : Summable fun m => ‖h m‖)
    (hk : Summable fun m => ‖k m‖) :
    ∑' n : ℤ, h n * star (k n)
      = ∫ ξ : Circle, discFourier h ξ * star (discFourier k ξ) ∂AddCircle.haarAddCircle := by
  classical
  have hprod := discFourier_mul_star_eq_tsum h k hh hk
  have hGint : ∀ p : ℤ × ℤ,
      Integrable (fun ξ : Circle => (h p.1 * star (k p.2)) * fourier (p.1 - p.2) ξ)
        (AddCircle.haarAddCircle : Measure Circle) := by
    intro p
    apply Continuous.integrable_of_hasCompactSupport
    · fun_prop
    · exact HasCompactSupport.of_compactSpace _
  have hnormint : ∀ p : ℤ × ℤ,
      ∫ ξ : Circle, ‖(h p.1 * star (k p.2)) * fourier (p.1 - p.2) ξ‖
        ∂(AddCircle.haarAddCircle : Measure Circle) = ‖h p.1 * star (k p.2)‖ := by
    intro p
    have hconst : (fun ξ : Circle => ‖(h p.1 * star (k p.2)) * fourier (p.1 - p.2) ξ‖)
        = fun _ : Circle => ‖h p.1 * star (k p.2)‖ := by
      funext ξ
      rw [norm_mul, norm_fourier_apply, mul_one]
    rw [hconst, integral_const]
    simp [Measure.real, smul_eq_mul]
  have hGsum : Summable (fun p : ℤ × ℤ =>
      ∫ ξ : Circle, ‖(h p.1 * star (k p.2)) * fourier (p.1 - p.2) ξ‖
        ∂(AddCircle.haarAddCircle : Measure Circle)) := by
    refine (Summable.mul_of_nonneg hh hk (fun n => norm_nonneg _)
      (fun m => norm_nonneg _)).congr ?_
    intro p
    rw [hnormint p, norm_mul, norm_star]
  have hval : ∀ p : ℤ × ℤ,
      ∫ ξ : Circle, (h p.1 * star (k p.2)) * fourier (p.1 - p.2) ξ
        ∂(AddCircle.haarAddCircle : Measure Circle)
      = (h p.1 * star (k p.2)) * (if p.1 - p.2 = 0 then 1 else 0) := by
    intro p
    rw [integral_const_mul, integral_fourier_eq_ite]
  rw [show ∑' n : ℤ, h n * star (k n)
        = ∑' p : ℤ × ℤ, (h p.1 * star (k p.2)) * (if p.1 - p.2 = 0 then 1 else 0)
      from (tsum_mul_conj_diag h k hh hk).symm]
  rw [show (∑' p : ℤ × ℤ, (h p.1 * star (k p.2)) * (if p.1 - p.2 = 0 then 1 else 0))
        = ∑' p : ℤ × ℤ, ∫ ξ : Circle, (h p.1 * star (k p.2)) * fourier (p.1 - p.2) ξ
            ∂(AddCircle.haarAddCircle : Measure Circle)
      from tsum_congr (fun p => (hval p).symm)]
  rw [integral_tsum_of_summable_integral_norm hGint hGsum]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun ξ => (hprod ξ).symm))

end Work.BourgainPlan.IonescuWainger
