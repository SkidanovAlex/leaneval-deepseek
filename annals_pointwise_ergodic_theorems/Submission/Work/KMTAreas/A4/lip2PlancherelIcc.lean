import Mathlib
import Submission.Work.KMTAreas.A4.lip2Plancherel

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators
open MeasureTheory

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-! ## The Plancherel identity for an arbitrary summable phase and window

`Work.KMTAreas.A4.lip2Plancherel` proves

  `∑'_x ‖∑'_n win M γ (n - s) g (x + P n)‖² = ∫₀¹ ‖kmtFhat g t‖² ‖winSum M γ t P s‖² dt`

for the *shifted reproducing window* `n ↦ win M γ (n - s)`.  The only property of the window that
is used is absolute summability, so here we record the identity for an **arbitrary** absolutely
summable window `w : ℤ → ℂ` and an arbitrary phase `Q : ℤ → ℤ`:

  `∑'_x ‖∑'_n w n g (x + Q n)‖² = ∫₀¹ ‖kmtFhat g t‖² ‖∑'_n w n e (t Q n)‖² dt`.

The proof is Plancherel on the circle: the `ℤ`-Fourier transform of `x ↦ g (x + Q n)` is
`t ↦ e (t Q n) · kmtFhat g t`, so the multiplier of the windowed average is
`(∑'_n w n e (t Q n)) · kmtFhat g t`, and the `ℓ²` norm of the average is the `L²` norm of its
multiplier.  The bridge between the average and the Fourier coefficients of the multiplier is
`Work.KMTAreas.A4.winFourierCoeff`. -/

theorem lip2PlancherelSummable (g : ℤ → ℂ) (hg : Summable fun x : ℤ => ‖g x‖)
    (w : ℤ → ℂ) (hw : Summable fun n : ℤ => ‖w n‖) (Q : ℤ → ℤ) :
    (∑' x : ℤ, ‖∑' n : ℤ, w n * g (x + Q n)‖ ^ 2)
      = ∫ t in (0 : ℝ)..1, ‖Work.A3.kmtFhat g t‖ ^ 2 *
          ‖(∑' n : ℤ, w n * winExp t (Q n))‖ ^ 2 := by
  classical
  have hab : (0 : ℝ) < 1 := by norm_num
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    rw [MeasureTheory.isFiniteMeasure_restrict, Real.volume_Ioc]
    simp
  -- the multiplier `W t = ∑'_n w n e (t Q n)` is bounded and a.e. strongly measurable
  have hterm : ∀ (t : ℝ) (n : ℤ), ‖w n * winExp t (Q n)‖ = ‖w n‖ := by
    intro t n
    rw [norm_mul, norm_winExp, mul_one]
  have hWb : ∀ t : ℝ, ‖∑' n : ℤ, w n * winExp t (Q n)‖ ≤ (∑' n : ℤ, ‖w n‖) + 1 := by
    intro t
    calc ‖∑' n : ℤ, w n * winExp t (Q n)‖
        ≤ ∑' n : ℤ, ‖w n * winExp t (Q n)‖ :=
          norm_tsum_le_tsum_norm (hw.congr (fun n => (hterm t n).symm))
      _ = ∑' n : ℤ, ‖w n‖ := tsum_congr (hterm t)
      _ ≤ (∑' n : ℤ, ‖w n‖) + 1 := by
          have : (0 : ℝ) ≤ ∑' n : ℤ, ‖w n‖ := tsum_nonneg (fun n => norm_nonneg _)
          linarith
  have hWm : AEStronglyMeasurable (fun t : ℝ => ∑' n : ℤ, w n * winExp t (Q n))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    refine MeasureTheory.AEStronglyMeasurable.tsum
      (f := fun n : ℤ => fun t : ℝ => w n * winExp t (Q n)) ?_
    intro n
    exact (continuous_const.mul (continuous_winExp (Q n))).aestronglyMeasurable
  obtain ⟨⟨Cg, _hCgpos, hCgb⟩, hkgm⟩ := kmtFhat_bounded (g := g) hg
  -- the Fourier multiplier of the windowed average
  let m : ℝ → ℂ := fun t => (∑' n : ℤ, w n * winExp t (Q n)) * Work.A3.kmtFhat g t
  have hmLp : MemLp m 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    have h1 : MemLp (fun t : ℝ => ∑' n : ℤ, w n * winExp t (Q n)) ⊤
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      MemLp.of_bound hWm _ (Filter.Eventually.of_forall hWb)
    have h2 : MemLp (fun t : ℝ => Work.A3.kmtFhat g t) 2
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      MemLp.of_bound hkgm Cg (Filter.Eventually.of_forall hCgb)
    exact MemLp.fun_mul (r := 2) h1 h2
  -- the windowed average is the `(-x)`-th Fourier coefficient of the multiplier
  have hcoef : ∀ x : ℤ, (∑' n : ℤ, w n * g (x + Q n)) = fourierCoeffOn hab m (-x) := by
    intro x
    have hfc := winFourierCoeff g hg w hw Q x
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
          = (∑' n : ℤ, w n * winExp t (Q n)) *
              (∑' y : ℤ, g y * Complex.exp (-(2 * Real.pi * Complex.I * ((y : ℝ) * t)))) *
              Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) * t)) := by
      intro t
      rw [hE t, hkmt t]
      show Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) * t)) *
          ((∑' n : ℤ, w n * winExp t (Q n)) * Work.A3.kmtFhat g t)
        = (∑' n : ℤ, w n * winExp t (Q n)) * Work.A3.kmtFhat g t *
            Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) * t))
      ring
    have h2 : (∫ t in (0 : ℝ)..1, fourier (-(-x)) (t : AddCircle (1 - 0 : ℝ)) • m t)
        = ∫ t in (0 : ℝ)..1, (∑' n : ℤ, w n * winExp t (Q n)) *
            (∑' y : ℤ, g y * Complex.exp (-(2 * Real.pi * Complex.I * ((y : ℝ) * t)))) *
            Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) * t)) :=
      intervalIntegral.integral_congr (fun t _ => hpoint t)
    calc (∑' n : ℤ, w n * g (x + Q n))
        = ∫ t in (0 : ℝ)..1, (∑' n : ℤ, w n * winExp t (Q n)) *
            (∑' y : ℤ, g y * Complex.exp (-(2 * Real.pi * Complex.I * ((y : ℝ) * t)))) *
            Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) * t)) := hfc.symm
      _ = ∫ t in (0 : ℝ)..1, fourier (-(-x)) (t : AddCircle (1 - 0 : ℝ)) • m t := h2.symm
      _ = fourierCoeffOn hab m (-x) := by
            rw [fourierCoeffOn_eq_integral]
            rw [show (1 : ℝ) / (1 - 0) = 1 by norm_num, one_smul]
  calc (∑' x : ℤ, ‖∑' n : ℤ, w n * g (x + Q n)‖ ^ 2)
      = ∑' x : ℤ, ‖fourierCoeffOn hab m (-x)‖ ^ 2 :=
        tsum_congr (fun x => by rw [hcoef x])
    _ = ∫ t in (0 : ℝ)..1, ‖m t‖ ^ 2 := tsum_fourierCoeffOn_neg m hab hmLp
    _ = ∫ t in (0 : ℝ)..1, ‖Work.A3.kmtFhat g t‖ ^ 2 *
          ‖(∑' n : ℤ, w n * winExp t (Q n))‖ ^ 2 := by
        refine intervalIntegral.integral_congr (fun t _ => ?_)
        show ‖(∑' n : ℤ, w n * winExp t (Q n)) * Work.A3.kmtFhat g t‖ ^ 2
          = ‖Work.A3.kmtFhat g t‖ ^ 2 * ‖(∑' n : ℤ, w n * winExp t (Q n))‖ ^ 2
        rw [norm_mul, mul_pow]
        ring

/-! ## The interval (`Icc`) form

The bilinear average `AhalfZ` of the inverse theorem of §5.2 only involves the *upper half* of the
shifts, so the Plancherel identity is needed for the interval-restricted window
`n ↦ (if n ∈ Icc a b then win M γ (n - s) else 0)`.  That is an absolutely summable window, so the
lemma above applies with `Q = P.eval`; the only bookkeeping left is rewriting the two `tsum`s as
`Icc`-sums and identifying the multiplier with `winSumIcc`. -/

theorem lip2PlancherelIcc (g : ℤ → ℂ) (hg : Summable fun x : ℤ => ‖g x‖)
    (hg2 : Summable fun x : ℤ => ‖g x‖ ^ 2) (P : Polynomial ℤ) {M : ℝ} (hM : 2 ≤ M)
    (γ : Work.Analysis.InverseTheory.FreqCircle) (s : ℤ) (a b : ℤ) :
    (∑' x : ℤ, ‖∑ n ∈ Finset.Icc a b, Work.KMTAreas.A4.win M γ (n - s) * g (x + P.eval n)‖ ^ 2)
      = ∫ t in (0 : ℝ)..1,
          ‖Work.A3.kmtFhat g t‖ ^ 2 * ‖Work.KMTAreas.A4.winSumIcc M γ t P s a b‖ ^ 2 := by
  classical
  have hM1 : (1 : ℝ) ≤ M := by linarith
  set w : ℤ → ℂ := fun n => if n ∈ Finset.Icc a b then win M γ (n - s) else 0 with hwdef
  have hweq : ∀ n : ℤ,
      w n = (if n ∈ Finset.Icc a b then win M γ (n - s) else 0) := fun n => rfl
  have hw : Summable fun n : ℤ => ‖w n‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      (win_summable_shift hM1 γ s)
    by_cases h : n ∈ Finset.Icc a b
    · rw [hweq n, if_pos h]
    · rw [hweq n, if_neg h, norm_zero]
      exact norm_nonneg _
  have hz : ∀ n : ℤ, n ∉ Finset.Icc a b → w n = 0 := by
    intro n hn
    rw [hweq n, if_neg hn]
  have hgen := lip2PlancherelSummable g hg w hw (fun n : ℤ => P.eval n)
  -- the `Icc`-restricted average is the `w`-average
  have hL : (∑' x : ℤ, ‖∑ n ∈ Finset.Icc a b,
        Work.KMTAreas.A4.win M γ (n - s) * g (x + P.eval n)‖ ^ 2)
      = ∑' x : ℤ, ‖∑' n : ℤ, w n * g (x + P.eval n)‖ ^ 2 := by
    refine tsum_congr (fun x => ?_)
    have hinner : (∑ n ∈ Finset.Icc a b, win M γ (n - s) * g (x + P.eval n))
        = ∑' n : ℤ, w n * g (x + P.eval n) := by
      rw [tsum_eq_sum (s := Finset.Icc a b) (fun n hn => by rw [hz n hn, zero_mul])]
      refine Finset.sum_congr rfl (fun n hn => ?_)
      rw [hweq n, if_pos hn]
    rw [hinner]
  -- the `Icc`-restricted multiplier is the `w`-multiplier
  have hR : ∀ t : ℝ,
      (∑' n : ℤ, w n * winExp t ((fun n : ℤ => P.eval n) n))
        = Work.KMTAreas.A4.winSumIcc M γ t P s a b := by
    intro t
    rw [tsum_eq_sum (s := Finset.Icc a b) (fun n hn => by rw [hz n hn, zero_mul]),
      Work.KMTAreas.A4.winSumIcc]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [hweq n, if_pos hn]
    congr 1
    rw [winExp]
    congr 1
    rw [Complex.ofReal_mul]
  rw [hL, hgen]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  rw [hR t]

end Work.KMTAreas.A4
