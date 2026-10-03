import Mathlib
import Submission.Work.KMTAreas.A4.lip2Defs
import Submission.Work.A3.Defs
import Submission.Work.KMTAreas.A4.winFourierCoeff

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators
open MeasureTheory

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-! ## Auxiliary lemmas: exponentials of purely imaginary numbers

The two exponentials occurring in `winSum` and in `A3.kmtFhat` have real part `0` in their
exponent, hence modulus `1`.  Stating this with a hypothesis `w.re = 0` keeps the lemma
independent of the exact shape in which the exponent is written. -/

theorem norm_cexp_eq_one_of_re_zero {w : ℂ} (hw : w.re = 0) : ‖Complex.exp w‖ = 1 := by
  rw [Complex.norm_exp, hw, Real.exp_zero]

/-! ## Summability and boundedness of the window -/

theorem norm_win_le {M : ℝ} (hM : 1 ≤ M) (γ : FreqCircle) (m : ℤ) :
    ‖win M γ m‖ ≤ ‖(lipSchPsi : ℝ → ℂ) ((m : ℝ) / M)‖ := by
  have hMpos : 0 < M := by linarith
  rw [win, norm_mul, norm_mul]
  have hf : ‖(fourier m γ : ℂ)‖ = 1 := by simp only [fourier_apply, Circle.norm_coe]
  rw [hf, mul_one]
  have hMn : ‖((M : ℝ) : ℂ)⁻¹‖ = M⁻¹ := by
    rw [norm_inv]; simp [abs_of_pos hMpos]
  rw [hMn]
  calc M⁻¹ * ‖(lipSchPsi : ℝ → ℂ) ((m : ℝ) / M)‖
      ≤ 1 * ‖(lipSchPsi : ℝ → ℂ) ((m : ℝ) / M)‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [inv_le_one₀ hMpos]; exact hM
    _ = ‖(lipSchPsi : ℝ → ℂ) ((m : ℝ) / M)‖ := one_mul _

theorem win_summable_aux {M : ℝ} (hM : 1 ≤ M) (γ : FreqCircle) :
    Summable (fun m : ℤ => ‖win M γ m‖) := by
  have hMpos : 0 < M := by linarith
  have hψ : Summable (fun m : ℤ => ‖(lipSchPsi : ℝ → ℂ) ((m : ℝ) / M)‖) := by
    have h := schwartzSamplingSummable (φ := lipSchPsi) (c := M⁻¹) (a := 0)
      (inv_ne_zero (ne_of_gt hMpos))
    refine h.congr (fun m => ?_)
    rw [zero_add, div_eq_inv_mul]
  exact Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => norm_win_le hM γ m) hψ

theorem win_summable_shift {M : ℝ} (hM : 1 ≤ M) (γ : FreqCircle) (s : ℤ) :
    Summable (fun n : ℤ => ‖win M γ (n - s)‖) := by
  have h : Summable ((fun m : ℤ => ‖win M γ m‖) ∘ (Equiv.addRight (-s) : ℤ → ℤ)) :=
    (Equiv.summable_iff (Equiv.addRight (-s)) (f := fun m : ℤ => ‖win M γ m‖)).mpr
      (win_summable_aux hM γ)
  have h2 : ((fun m : ℤ => ‖win M γ m‖) ∘ (Equiv.addRight (-s) : ℤ → ℤ))
      = fun n : ℤ => ‖win M γ (n - s)‖ := by
    funext n
    simp [Function.comp, sub_eq_add_neg]
  rwa [h2] at h

theorem winSum_bounded (M : ℝ) (hM : 1 ≤ M) (γ : FreqCircle) (P : Polynomial ℤ) (s : ℤ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, ‖winSum M γ t P s‖ ≤ C := by
  have hsum := win_summable_shift hM γ s
  refine ⟨(∑' n : ℤ, ‖win M γ (n - s)‖) + 1, by positivity, fun t => ?_⟩
  have hterm : ∀ n : ℤ,
      ‖win M γ (n - s) * Complex.exp (2 * Real.pi * Complex.I * (t * (P.eval n : ℤ) : ℝ))‖
        = ‖win M γ (n - s)‖ := by
    intro n
    rw [norm_mul, norm_cexp_eq_one_of_re_zero (by simp [Complex.mul_re]), mul_one]
  calc ‖winSum M γ t P s‖
      = ‖∑' n : ℤ, win M γ (n - s) *
          Complex.exp (2 * Real.pi * Complex.I * (t * (P.eval n : ℤ) : ℝ))‖ := rfl
    _ ≤ ∑' n : ℤ, ‖win M γ (n - s) *
          Complex.exp (2 * Real.pi * Complex.I * (t * (P.eval n : ℤ) : ℝ))‖ :=
        norm_tsum_le_tsum_norm (hsum.congr (fun n => (hterm n).symm))
    _ = ∑' n : ℤ, ‖win M γ (n - s)‖ := tsum_congr hterm
    _ ≤ (∑' n : ℤ, ‖win M γ (n - s)‖) + 1 := by
        have : (0:ℝ) ≤ ∑' n : ℤ, ‖win M γ (n - s)‖ := tsum_nonneg (fun n => norm_nonneg _)
        linarith

theorem winSum_aestronglyMeasurable (M : ℝ) (γ : FreqCircle) (P : Polynomial ℤ) (s : ℤ) :
    AEStronglyMeasurable (fun t : ℝ => winSum M γ t P s)
      (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
  rw [show (fun t : ℝ => winSum M γ t P s)
      = fun t : ℝ => ∑' n : ℤ, win M γ (n - s) *
          Complex.exp (2 * Real.pi * Complex.I * (t * (P.eval n : ℤ) : ℝ)) from rfl]
  refine MeasureTheory.AEStronglyMeasurable.tsum (f := fun n : ℤ => fun t : ℝ =>
    win M γ (n - s) * Complex.exp (2 * Real.pi * Complex.I * (t * (P.eval n : ℤ) : ℝ))) ?_
  intro n
  exact (continuous_const.mul (by fun_prop)).aestronglyMeasurable

/-! ## Boundedness and measurability of the Fourier transform of an `ℓ¹` function -/

theorem kmtFhat_bounded {g : ℤ → ℂ} (hg : Summable fun x : ℤ => ‖g x‖) :
    (∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, ‖Work.A3.kmtFhat g t‖ ≤ C) ∧
    AEStronglyMeasurable (fun t : ℝ => Work.A3.kmtFhat g t)
      (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
  have hterm : ∀ (x : ℤ) (t : ℝ),
      ‖g x * Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℝ) * t)))‖ = ‖g x‖ := by
    intro x t
    rw [norm_mul, norm_cexp_eq_one_of_re_zero (by simp [Complex.mul_re]), mul_one]
  have hbd : ∀ t : ℝ, ‖Work.A3.kmtFhat g t‖ ≤ (∑' x : ℤ, ‖g x‖) + 1 := by
    intro t
    calc ‖Work.A3.kmtFhat g t‖
        = ‖∑' x : ℤ, g x * Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℝ) * t)))‖ := rfl
      _ ≤ ∑' x : ℤ, ‖g x * Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℝ) * t)))‖ :=
          norm_tsum_le_tsum_norm (hg.congr fun x => (hterm x t).symm)
      _ = ∑' x : ℤ, ‖g x‖ := tsum_congr (fun x => hterm x t)
      _ ≤ (∑' x : ℤ, ‖g x‖) + 1 := by
          have : (0:ℝ) ≤ ∑' x : ℤ, ‖g x‖ := tsum_nonneg (fun x => norm_nonneg _)
          linarith
  refine ⟨⟨(∑' x : ℤ, ‖g x‖) + 1, by positivity, hbd⟩, ?_⟩
  rw [show (fun t : ℝ => Work.A3.kmtFhat g t)
      = fun t : ℝ => ∑' x : ℤ, g x *
          Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℝ) * t))) from rfl]
  refine MeasureTheory.AEStronglyMeasurable.tsum (f := fun x : ℤ => fun t : ℝ =>
    g x * Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℝ) * t)))) ?_
  intro x
  exact (continuous_const.mul (by fun_prop)).aestronglyMeasurable

/-! ## Plancherel on the circle in real form -/

/-- Parseval/Plancherel on `(0,1]`: the sum of the squared moduli of the Fourier coefficients
of `m`, reindexed by `n ↦ -n`, is the `L²` norm of `m`. -/
theorem tsum_fourierCoeffOn_neg (m : ℝ → ℂ) (hab : (0 : ℝ) < 1)
    (hm : MemLp m 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))) :
    (∑' x : ℤ, ‖fourierCoeffOn hab m (-x)‖ ^ 2) = ∫ t in (0 : ℝ)..1, ‖m t‖ ^ 2 := by
  have h := (hasSum_sq_fourierCoeffOn hab hm).tsum_eq
  rw [show (∑' x : ℤ, ‖fourierCoeffOn hab m (-x)‖ ^ 2)
      = ∑' i : ℤ, ‖fourierCoeffOn hab m i‖ ^ 2 from by
        simpa using Equiv.tsum_eq (Equiv.neg ℤ) (fun i : ℤ => ‖fourierCoeffOn hab m i‖ ^ 2)]
  rw [h]
  norm_num

/-- **Plancherel identity for the windowed polynomial average.** -/
theorem lip2Plancherel (g : ℤ → ℂ) (hg : Summable fun x : ℤ => ‖g x‖)
    (hg2 : Summable fun x : ℤ => ‖g x‖ ^ 2) (P : Polynomial ℤ) {M : ℝ} (hM : 2 ≤ M)
    (γ : Work.Analysis.InverseTheory.FreqCircle) (s : ℤ) :
    (∑' x : ℤ, ‖∑' n : ℤ, Work.KMTAreas.A4.win M γ (n - s) * g (x + P.eval n)‖ ^ 2)
      = ∫ t in (0 : ℝ)..1,
          ‖Work.A3.kmtFhat g t‖ ^ 2 * ‖Work.KMTAreas.A4.winSum M γ t P s‖ ^ 2 := by
  classical
  have hM1 : (1 : ℝ) ≤ M := by linarith
  have hab : (0 : ℝ) < 1 := by norm_num
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    rw [MeasureTheory.isFiniteMeasure_restrict, Real.volume_Ioc]
    simp
  -- the shifted window is summable; the windowed exponential sum is bounded and measurable
  have hws : Summable (fun n : ℤ => ‖win M γ (n - s)‖) := win_summable_shift hM1 γ s
  obtain ⟨Cw, _hCwpos, hCwb⟩ := winSum_bounded M hM1 γ P s
  have hwsm : AEStronglyMeasurable (fun t : ℝ => winSum M γ t P s)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := winSum_aestronglyMeasurable M γ P s
  obtain ⟨⟨Cg, _hCgpos, hCgb⟩, hkgm⟩ := kmtFhat_bounded (g := g) hg
  -- the Fourier multiplier of the windowed average
  let m : ℝ → ℂ := fun t => winSum M γ t P s * Work.A3.kmtFhat g t
  have hmLp : MemLp m 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    have h1 : MemLp (fun t : ℝ => winSum M γ t P s) ⊤ (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      MemLp.of_bound hwsm Cw (Filter.Eventually.of_forall hCwb)
    have h2 : MemLp (fun t : ℝ => Work.A3.kmtFhat g t) 2
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      MemLp.of_bound hkgm Cg (Filter.Eventually.of_forall hCgb)
    exact MemLp.fun_mul (r := 2) h1 h2
  -- the windowed average is the `(-x)`-th Fourier coefficient of the multiplier
  have hcoef : ∀ x : ℤ, (∑' n : ℤ, win M γ (n - s) * g (x + P.eval n))
      = fourierCoeffOn hab m (-x) := by
    intro x
    have hfc := winFourierCoeff g hg (fun n : ℤ => win M γ (n - s)) hws
      (fun n : ℤ => P.eval n) x
    have hwin : ∀ t : ℝ,
        (∑' n : ℤ, win M γ (n - s) *
            Complex.exp (2 * Real.pi * Complex.I * (t * ((fun n : ℤ => P.eval n) n : ℝ))))
          = winSum M γ t P s := by
      intro t
      rw [winSum]
      refine tsum_congr (fun n => ?_)
      congr 1
      congr 1
      push_cast
      ring
    have hkmt : ∀ t : ℝ,
        (∑' y : ℤ, g y * Complex.exp (-(2 * Real.pi * Complex.I * ((y : ℝ) * t))))
          = Work.A3.kmtFhat g t := fun t => rfl
    have hE : ∀ t : ℝ, fourier (-(-x)) (t : AddCircle (1 - 0 : ℝ))
        = Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) * t)) := by
      intro t
      rw [fourier_coe_apply]
      congr 1
      push_cast
      ring
    have hpoint : ∀ t : ℝ,
        fourier (-(-x)) (t : AddCircle (1 - 0 : ℝ)) • m t
          = (∑' n : ℤ, win M γ (n - s) *
                Complex.exp (2 * Real.pi * Complex.I * (t * ((fun n : ℤ => P.eval n) n : ℝ)))) *
              (∑' y : ℤ, g y * Complex.exp (-(2 * Real.pi * Complex.I * ((y : ℝ) * t)))) *
              Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) * t)) := by
      intro t
      rw [hE t, hwin t, hkmt t]
      show Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) * t)) *
          (winSum M γ t P s * Work.A3.kmtFhat g t)
        = winSum M γ t P s * Work.A3.kmtFhat g t *
            Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) * t))
      ring
    have h2 : (∫ t in (0 : ℝ)..1, fourier (-(-x)) (t : AddCircle (1 - 0 : ℝ)) • m t)
        = ∫ t in (0 : ℝ)..1, (∑' n : ℤ, win M γ (n - s) *
              Complex.exp (2 * Real.pi * Complex.I * (t * ((fun n : ℤ => P.eval n) n : ℝ)))) *
            (∑' y : ℤ, g y * Complex.exp (-(2 * Real.pi * Complex.I * ((y : ℝ) * t)))) *
            Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) * t)) :=
      intervalIntegral.integral_congr (fun t _ => hpoint t)
    calc (∑' n : ℤ, win M γ (n - s) * g (x + P.eval n))
        = ∫ t in (0 : ℝ)..1, (∑' n : ℤ, win M γ (n - s) *
              Complex.exp (2 * Real.pi * Complex.I * (t * ((fun n : ℤ => P.eval n) n : ℝ)))) *
            (∑' y : ℤ, g y * Complex.exp (-(2 * Real.pi * Complex.I * ((y : ℝ) * t)))) *
            Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) * t)) := hfc.symm
      _ = ∫ t in (0 : ℝ)..1, fourier (-(-x)) (t : AddCircle (1 - 0 : ℝ)) • m t := h2.symm
      _ = fourierCoeffOn hab m (-x) := by
            rw [fourierCoeffOn_eq_integral]
            rw [show (1 : ℝ) / (1 - 0) = 1 by norm_num, one_smul]
  calc (∑' x : ℤ, ‖∑' n : ℤ, win M γ (n - s) * g (x + P.eval n)‖ ^ 2)
      = ∑' x : ℤ, ‖fourierCoeffOn hab m (-x)‖ ^ 2 :=
        tsum_congr (fun x => by rw [hcoef x])
    _ = ∫ t in (0 : ℝ)..1, ‖m t‖ ^ 2 := tsum_fourierCoeffOn_neg m hab hmLp
    _ = ∫ t in (0 : ℝ)..1,
          ‖Work.A3.kmtFhat g t‖ ^ 2 * ‖Work.KMTAreas.A4.winSum M γ t P s‖ ^ 2 := by
        refine intervalIntegral.integral_congr (fun t _ => ?_)
        show ‖winSum M γ t P s * Work.A3.kmtFhat g t‖ ^ 2
          = ‖Work.A3.kmtFhat g t‖ ^ 2 * ‖Work.KMTAreas.A4.winSum M γ t P s‖ ^ 2
        rw [norm_mul, mul_pow]
        ring

end Work.KMTAreas.A4
