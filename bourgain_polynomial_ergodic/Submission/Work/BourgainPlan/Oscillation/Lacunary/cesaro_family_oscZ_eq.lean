import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs
import Submission.Work.BourgainPlan.Oscillation.oscZ_lacunary_defs

/-!
# The geometric-sum form of the Cesàro multiplier

The Cesàro multiplier at scale `N`,
`m_N(θ) = N⁻¹ (e(Nθ) - 1)/(e(θ) - 1)` with `e(t) = exp (2 π i t)`,
coincides with the average of the characters `N⁻¹ Σ_{n<N} e(nθ)` for every real `θ ∉ ℤ`
(the geometric-sum identity).  Consequently the two associated `oscZ` families are equal.
-/

namespace Work.BourgainPlan.Oscillation.Lacunary

open Finset MeasureTheory
open scoped BigOperators

noncomputable section

/-- `(e(θ))^N = e(N θ)`. -/
private lemma cexp_pow_natCast (N : ℕ) (θ : ℝ) :
    (Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ))) ^ N
      = Complex.exp (2 * Real.pi * Complex.I * ((N : ℝ) * θ)) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `(e(θ))^n = e(n θ)`. -/
private lemma cexp_pow_nat (n : ℕ) (θ : ℝ) :
    (Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ))) ^ n
      = Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) * (θ : ℂ))) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

/-- The geometric-sum identity for the Cesàro multiplier: for `θ ∉ ℤ`,
`(e(Nθ) - 1)/(e(θ) - 1) = Σ_{n<N} e(nθ)`. -/
private lemma cexp_geom_div (N : ℕ) (θ : ℝ)
    (hθ : Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ)) ≠ 1) :
    (Complex.exp (2 * Real.pi * Complex.I * ((N : ℝ) * θ)) - 1) /
        (Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ)) - 1)
      = ∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) * (θ : ℂ))) := by
  have hsum : (∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) * (θ : ℂ))))
      = ∑ n ∈ Finset.range N, (Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ))) ^ n := by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [cexp_pow_nat]
  rw [hsum, geom_sum_eq hθ N, cexp_pow_natCast]

/-- `e(θ) = 1` forces `θ ∈ ℤ`; hence for non-integral `θ` the previous identity applies. -/
private lemma cexp_ne_one_of_not_int {θ : ℝ} (h : ∀ n : ℤ, θ ≠ (n : ℝ)) :
    Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ)) ≠ 1 := by
  intro hc
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hc
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Complex.I_ne_zero]
  have h' : (2 * (Real.pi : ℂ) * Complex.I) * (θ : ℂ)
      = (2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) := by
    rw [hn]; ring
  have hθc : (θ : ℂ) = (n : ℂ) := mul_left_cancel₀ h2 h'
  rw [← Complex.ofReal_intCast n] at hθc
  exact h n (Complex.ofReal_injective hθc)

private lemma range_int_volume_zero :
    MeasureTheory.volume (Set.range (fun n : ℤ => (n : ℝ))) = 0 :=
  Set.Countable.measure_zero (Set.countable_range (fun n : ℤ => (n : ℝ))) MeasureTheory.volume

theorem cesaro_family_oscZ_eq (ρ : ℝ) (hρ : 1 < ρ) (J : ℕ) (k : ℕ → ℕ)
    (f : ℤ → ℂ) (s : Finset ℤ) (hs : ∀ n, n ∉ s → f n = 0) :
    Work.BourgainPlan.Oscillation.oscZ (fun i x =>
        ∫ θ in (0:ℝ)..1,
          (((Work.BourgainPlan.Oscillation.lacScale ρ i : ℂ))⁻¹ *
            ((Complex.exp (2 * Real.pi * Complex.I *
                ((Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) * θ)) - 1) /
             (Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ)) - 1))) *
          (∑ j ∈ s, f j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))) *
          Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))) J k
      = Work.BourgainPlan.Oscillation.oscZ (fun i x =>
        ∫ θ in (0:ℝ)..1,
          (((Work.BourgainPlan.Oscillation.lacScale ρ i : ℂ))⁻¹ *
            ∑ n ∈ Finset.range (Work.BourgainPlan.Oscillation.lacScale ρ i),
              Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) * (θ : ℂ)))) *
          (∑ j ∈ s, f j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))) *
          Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))) J k := by
  refine congrArg (fun F : ℕ → ℤ → ℂ => Work.BourgainPlan.Oscillation.oscZ F J k) ?_
  funext i x
  apply intervalIntegral.integral_congr_ae
  have hae : (fun θ : ℝ =>
        (((Work.BourgainPlan.Oscillation.lacScale ρ i : ℂ))⁻¹ *
            ((Complex.exp (2 * Real.pi * Complex.I *
                ((Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) * θ)) - 1) /
             (Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ)) - 1))) *
          (∑ j ∈ s, f j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))) *
          Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ))))
      =ᵐ[MeasureTheory.volume] (fun θ : ℝ =>
        (((Work.BourgainPlan.Oscillation.lacScale ρ i : ℂ))⁻¹ *
            ∑ n ∈ Finset.range (Work.BourgainPlan.Oscillation.lacScale ρ i),
              Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) * (θ : ℂ)))) *
          (∑ j ∈ s, f j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))) *
          Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))) := by
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ range_int_volume_zero
    intro θ hθ
    simp only [Set.mem_ofPred_eq] at hθ ⊢
    by_contra hcon
    have hθne : ∀ n : ℤ, θ ≠ (n : ℝ) := by
      intro n hn
      exact hcon (by rw [Set.mem_range]; exact ⟨n, hn.symm⟩)
    have hc : Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ)) ≠ 1 :=
      cexp_ne_one_of_not_int hθne
    exact hθ (by rw [cexp_geom_div (Work.BourgainPlan.Oscillation.lacScale ρ i) θ hc])
  filter_upwards [hae] with θ hθ _
  exact hθ

end

end Work.BourgainPlan.Oscillation.Lacunary
