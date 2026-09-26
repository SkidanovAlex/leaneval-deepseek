import Mathlib
import Submission.Work.FunctionalEquations.Basic
import Submission.Work.FunctionalEquations.EqZeroOfTsumExp

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap
open MeasureTheory

set_option linter.unusedVariables false

theorem GenEqZeroOfTsumExp {k₀ : ℕ} {c : Set.Ici k₀ → ℂ} {y : ℝ} (hy : 0 < y)
    (hsum : Summable fun m : Set.Ici k₀ =>
      c m * Complex.exp (-(2 * (Real.pi : ℂ) * (y : ℂ) * (m.1 : ℝ))))
    (hzero : ∀ t : ℝ, ∑' m : Set.Ici k₀, c m * Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℝ) * ((t : ℂ) + (y : ℂ) * Complex.I)) = 0) :
    ∀ m, c m = 0 := by
  let b : Set.Ici k₀ → ℂ := fun m =>
    c m * Complex.exp (-(2 * (Real.pi : ℂ) * (y : ℂ) * (m.1 : ℝ)))
  have hbsum : Summable b := hsum
  -- Rewrite the vanishing hypothesis into a Fourier series with coefficients `b`.
  have hz : ∀ t : ℝ, ∑' m : Set.Ici k₀,
      b m * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℝ) * (t : ℂ)) = 0 := by
    intro t
    rw [← hzero t]
    apply tsum_congr
    intro m
    change c m * Complex.exp (-(2 * (Real.pi : ℂ) * (y : ℂ) * (m.1 : ℝ))) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℝ) * (t : ℂ))
        = c m * Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℝ) * ((t : ℂ) + (y : ℂ) * Complex.I))
    rw [mul_assoc, exp_neg_mul_exp_eq m.1 y t]
  intro k
  let fm : Set.Ici k₀ → ℝ → ℂ := fun m t =>
    (b m * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℝ) * (t : ℂ))) *
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k.1 : ℝ) * (t : ℂ)))
  -- The pointwise Fourier sum is identically zero.
  have hzfm : ∀ t : ℝ, ∑' m : Set.Ici k₀, fm m t = 0 := by
    intro t
    rw [show (∑' m : Set.Ici k₀, fm m t)
        = (∑' m : Set.Ici k₀,
            b m * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℝ) * (t : ℂ)))
          * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k.1 : ℝ) * (t : ℂ))) from by
      rw [← tsum_mul_right]]
    rw [hz t, zero_mul]
  -- Integrability of each summand.
  have hint : ∀ m : Set.Ici k₀,
      Integrable (fm m) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    intro m
    have hcont : Continuous (fm m) := by
      rw [show fm m = (fun t : ℝ =>
          (b m * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℝ) * (t : ℂ))) *
            Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k.1 : ℝ) * (t : ℂ)))) from rfl]
      fun_prop
    exact (hcont.continuousOn.integrableOn_Icc (a := (0 : ℝ)) (b := 1)).mono_set
      (fun x hx => ⟨hx.1.le, hx.2⟩)
  -- The norm integrals are summable, with value `‖b m‖`.
  have hterm : ∀ m : Set.Ici k₀,
      ∫ a, ‖fm m a‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) = ‖b m‖ := by
    intro m
    have hpt : ∀ a : ℝ, ‖fm m a‖ = ‖b m‖ := by
      intro a
      rw [show fm m a = (b m * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℝ) * (a : ℂ))) *
            Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k.1 : ℝ) * (a : ℂ))) from rfl]
      rw [norm_mul, norm_mul, norm_exp_two_pi_I, norm_exp_neg_two_pi_I]
      ring
    rw [show (fun a : ℝ => ‖fm m a‖) = (fun _ : ℝ => ‖b m‖) from funext hpt]
    rw [MeasureTheory.integral_const]
    simp [MeasureTheory.Measure.real]
  have hF_sum : Summable (fun m : Set.Ici k₀ =>
      ∫ a, ‖fm m a‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
    hbsum.norm.congr (fun m => (hterm m).symm)
  -- Interchange the integral with the series.
  have hHL := MeasureTheory.hasSum_integral_of_summable_integral_norm hint hF_sum
  have hintzero : ∫ a, ∑' m : Set.Ici k₀, fm m a
      ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) = 0 := by
    rw [show (fun a : ℝ => ∑' m : Set.Ici k₀, fm m a) = 0 from funext hzfm]
    simp
  have hHL0 : HasSum (fun m : Set.Ici k₀ =>
      ∫ a, fm m a ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) 0 := by
    rw [← hintzero]; exact hHL
  have htsum : ∑' m : Set.Ici k₀,
      ∫ a, fm m a ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) = 0 := hHL0.tsum_eq
  -- Evaluate each integral.
  have hfm_int : ∀ m : Set.Ici k₀,
      ∫ a, fm m a ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) = b m * (if m = k then 1 else 0) := by
    intro m
    have hexp : (fun a : ℝ => fm m a) = (fun a : ℝ =>
        (b m * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℝ) * (a : ℂ))) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k.1 : ℝ) * (a : ℂ)))) := by
      funext a; rfl
    rw [hexp, integral_fm]
    congr 1
    rcases eq_or_ne m k with h | h
    · subst h; simp
    · rw [if_neg h, if_neg (fun hc => h (Subtype.ext hc))]
  -- Sum the evaluated integrals.
  have hcongr : (∑' m : Set.Ici k₀, b m * (if m = k then 1 else 0))
      = ∑' m : Set.Ici k₀,
          ∫ a, fm m a ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    apply tsum_congr
    intro m
    exact (hfm_int m).symm
  have hbk : b k = 0 := by
    have h1 : (∑' m : Set.Ici k₀, b m * (if m = k then 1 else 0)) = b k := by
      rw [tsum_eq_single k (fun m hm => by rw [if_neg hm, mul_zero])]
      simp
    rw [h1] at hcongr
    rw [htsum] at hcongr
    exact hcongr
  -- Extract `c k = 0`.
  have hbk_eq : b k = c k * Complex.exp (-(2 * (Real.pi : ℂ) * (y : ℂ) * (k.1 : ℝ))) := rfl
  rw [hbk_eq] at hbk
  rcases mul_eq_zero.mp hbk with h | h
  · exact h
  · exact absurd h (Complex.exp_ne_zero _)

end Work.FunctionalEquations
