import Mathlib
import Submission.Work.KMTAreas.A4.lip2MainDefs
import Submission.Work.KMTAreas.A4.lip2PlancherelIcc
import Submission.Work.KMTAreas.A4.lip2Kernel

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators
open MeasureTheory
open Filter

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-- Lebesgue measure restricted to the frequency interval `(0,1]`. -/
noncomputable abbrev omegaMassNu : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)

theorem omegaMassNu_finite : IsFiniteMeasure omegaMassNu := by
  rw [omegaMassNu, isFiniteMeasure_restrict, Real.volume_Ioc]
  simp

/-! ## Boundedness of the interval window sum -/

theorem winSumIcc_norm_bound : ∃ K : ℝ, 0 < K ∧ ∀ (M : ℝ) (γ : FreqCircle) (ξ : ℝ)
    (P : Polynomial ℤ) (s a b : ℤ), 2 ≤ M → ‖winSumIcc M γ ξ P s a b‖ ≤ K := by
  obtain ⟨C, hCpos, hC⟩ := win_tsum_le
  refine ⟨C, hCpos, ?_⟩
  intro M γ ξ P s a b hM
  have hM1 : (1 : ℝ) ≤ M := by linarith
  have hshift_eq : (∑' n : ℤ, ‖win M γ (n - s)‖) = ∑' m : ℤ, ‖win M γ m‖ := by
    have h2 : ((fun m : ℤ => ‖win M γ m‖) ∘ (Equiv.addRight (-s) : ℤ → ℤ))
        = fun n : ℤ => ‖win M γ (n - s)‖ := by
      funext n
      simp [Function.comp, sub_eq_add_neg]
    calc (∑' n : ℤ, ‖win M γ (n - s)‖)
        = ∑' n : ℤ, ((fun m : ℤ => ‖win M γ m‖) ∘ (Equiv.addRight (-s) : ℤ → ℤ)) n := by
          rw [h2]
      _ = ∑' m : ℤ, ‖win M γ m‖ :=
          Equiv.tsum_eq (Equiv.addRight (-s)) (fun m : ℤ => ‖win M γ m‖)
  have htsum : (∑' n : ℤ, ‖win M γ (n - s)‖) ≤ C := by
    rw [hshift_eq]
    exact hC M γ hM1
  have hsum : Summable fun n : ℤ => ‖win M γ (n - s)‖ := win_summable_shift hM1 γ s
  have hterm : ∀ n : ℤ, ‖win M γ (n - s) *
      Complex.exp (2 * Real.pi * Complex.I * ((ξ * (P.eval n : ℤ) : ℝ) : ℂ))‖
      = ‖win M γ (n - s)‖ := by
    intro n
    rw [norm_mul, norm_cexp_eq_one_of_re_zero (by simp [Complex.mul_re]), mul_one]
  calc ‖winSumIcc M γ ξ P s a b‖
      = ‖∑ n ∈ Finset.Icc a b, win M γ (n - s) *
          Complex.exp (2 * Real.pi * Complex.I * ((ξ * (P.eval n : ℤ) : ℝ) : ℂ))‖ := by
        rw [winSumIcc]
    _ ≤ ∑ n ∈ Finset.Icc a b, ‖win M γ (n - s) *
          Complex.exp (2 * Real.pi * Complex.I * ((ξ * (P.eval n : ℤ) : ℝ) : ℂ))‖ :=
        norm_sum_le _ _
    _ = ∑ n ∈ Finset.Icc a b, ‖win M γ (n - s)‖ := Finset.sum_congr rfl (fun n _ => hterm n)
    _ ≤ ∑' n : ℤ, ‖win M γ (n - s)‖ :=
        Summable.sum_le_tsum (Finset.Icc a b) (fun n _ => norm_nonneg _) hsum
    _ ≤ C := htsum

/-! ## Integrability of the mass integrands -/

theorem integrable_omega (g : ℤ → ℂ) (hg : Summable fun x : ℤ => ‖g x‖)
    (γ : FreqCircle) (P : Polynomial ℤ) (s a b : ℤ) {K M : ℝ}
    (hWbd : ∀ t : ℝ, ‖winSumIcc M γ t P s a b‖ ≤ K) :
    Integrable (fun t : ℝ => ‖Work.A3.kmtFhat g t‖ ^ 2) omegaMassNu ∧
    Integrable (fun t : ℝ => ‖Work.A3.kmtFhat g t‖ ^ 2 *
      ‖winSumIcc M γ t P s a b‖ ^ 2) omegaMassNu ∧
    (∀ ε : ℝ, Integrable (fun t : ℝ =>
      if ε ≤ ‖winSumIcc M γ t P s a b‖ then ‖Work.A3.kmtFhat g t‖ ^ 2 else 0) omegaMassNu) := by
  haveI : IsFiniteMeasure omegaMassNu := omegaMassNu_finite
  obtain ⟨⟨Cg, hCgpos, hCgb⟩, hkgm⟩ := kmtFhat_bounded (g := g) hg
  have hcont : Continuous fun t : ℝ => ‖winSumIcc M γ t P s a b‖ := by
    have hunf : ∀ t : ℝ, winSumIcc M γ t P s a b = ∑ n ∈ Finset.Icc a b, win M γ (n - s) *
        Complex.exp (2 * Real.pi * Complex.I * ((t * (P.eval n : ℤ) : ℝ) : ℂ)) :=
      fun t => by rw [winSumIcc]
    have h2 : (fun t : ℝ => ‖winSumIcc M γ t P s a b‖) = fun t : ℝ =>
        ‖∑ n ∈ Finset.Icc a b, win M γ (n - s) *
          Complex.exp (2 * Real.pi * Complex.I * ((t * (P.eval n : ℤ) : ℝ) : ℂ))‖ := by
      funext t
      rw [hunf t]
    rw [h2]
    exact Continuous.norm (continuous_finsetSum (Finset.Icc a b)
      (fun n _ => continuous_const.mul (Complex.continuous_exp.comp (by fun_prop))))
  have hm1 : AEStronglyMeasurable (fun t : ℝ => ‖Work.A3.kmtFhat g t‖ ^ 2) omegaMassNu :=
    hkgm.norm.pow 2
  have hm2 : AEStronglyMeasurable (fun t : ℝ => ‖winSumIcc M γ t P s a b‖) omegaMassNu :=
    hcont.aestronglyMeasurable
  have hI1 : Integrable (fun t : ℝ => ‖Work.A3.kmtFhat g t‖ ^ 2) omegaMassNu := by
    refine Integrable.of_bound hm1 (Cg ^ 2) (Eventually.of_forall fun t => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hCgb t) 2
  refine ⟨hI1, ?_, ?_⟩
  · refine Integrable.of_bound (hm1.mul (hm2.pow 2)) (Cg ^ 2 * K ^ 2)
      (Eventually.of_forall fun t => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    have h1 : ‖Work.A3.kmtFhat g t‖ ^ 2 ≤ Cg ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hCgb t) 2
    have h2 : ‖winSumIcc M γ t P s a b‖ ^ 2 ≤ K ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hWbd t) 2
    exact mul_le_mul h1 h2 (sq_nonneg _) (sq_nonneg Cg)
  · intro ε
    have hms : MeasurableSet {t : ℝ | ε ≤ ‖winSumIcc M γ t P s a b‖} :=
      measurableSet_le measurable_const hcont.measurable
    have hind := hI1.indicator hms
    refine hind.congr (Eventually.of_forall fun t => ?_)
    simp only [Set.indicator_apply, Set.mem_setOf_eq]

/-! ## The main lemma -/

end Work.KMTAreas.A4
