import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.L1Tails.DefsC
import Submission.Work.BoseFixB1S.integral_sq_le_measure_mul_integral_sq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.L1Tails.hPairSqLe

open MeasureTheory

set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- Cauchy–Schwarz bound for a single lattice coefficient of the pairing: given the Fubini
identity `hident` for `hPair ℓ H n` and the `L²` bound `hMlp` for the slice transform, the
`y`-integrand vanishes off `boxL ℓ` (from `hHs`), so Hölder with the indicator of `boxL ℓ`
(`MeasureTheory.integral_mul_norm_le_Lp_mul_Lq`, `Real.HolderConjugate.two_two`,
`∫ ‖1_{boxL ℓ}‖² = ℓ³`) gives `‖hPair ℓ H n‖² ≤ ℓ³ ∫_y ‖kinFT (conj ∘ H · y) κ_n‖²`. -/
theorem norm_hPair_sq_le {ℓ : ℝ} (hℓ : 0 < ℓ)
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry H))
    (hHs : ∀ w y, H w y ≠ 0 →
      w ∈ Work.BoseK15.corpusBox.boxL ℓ ∧ y ∈ Work.BoseK15.corpusBox.boxL ℓ)
    (n : Fin 3 → ℤ)
    (hMlp : MeasureTheory.MemLp (fun y : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.kinFT (fun w => (starRingEnd ℂ) (H w y))
        (Work.BoseBoxFock.kappaL ℓ n)) 2 MeasureTheory.volume)
    (hident : Work.BoseBoxFock.L1Tails.hPair ℓ H n
      = ∫ y : EuclideanSpace ℝ (Fin 3),
          Complex.exp (-(Complex.I * ((inner ℝ (Work.BoseBoxFock.kappaL ℓ n) y : ℝ) : ℂ)))
            * (starRingEnd ℂ) (Submission.BoseGases.kinFT (fun w => (starRingEnd ℂ) (H w y))
                (Work.BoseBoxFock.kappaL ℓ n))) :
    ‖Work.BoseBoxFock.L1Tails.hPair ℓ H n‖ ^ 2
      ≤ ℓ ^ 3 * ∫ y : EuclideanSpace ℝ (Fin 3),
          ‖Submission.BoseGases.kinFT (fun w => (starRingEnd ℂ) (H w y))
            (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2 := by
  classical
  -- the slice transform, as a function of the `y`-variable
  set f : E3 → ℂ := fun y => Submission.BoseGases.kinFT (fun w => (starRingEnd ℂ) (H w y))
      (Work.BoseBoxFock.kappaL ℓ n) with hf
  -- the two hypotheses, in the vocabulary of `f`
  have hMlf : MeasureTheory.MemLp f 2 MeasureTheory.volume := hMlp
  have hid : Work.BoseBoxFock.L1Tails.hPair ℓ H n
      = ∫ y : E3,
          Complex.exp (-(Complex.I * ((inner ℝ (Work.BoseBoxFock.kappaL ℓ n) y : ℝ) : ℂ)))
            * (starRingEnd ℂ) (f y) := hident
  -- the phase factor has modulus one
  have hexp : ∀ y : E3,
      ‖Complex.exp (-(Complex.I * ((inner ℝ (Work.BoseBoxFock.kappaL ℓ n) y : ℝ) : ℂ)))‖ = 1 := by
    intro y
    have hkey : -(Complex.I * ((inner ℝ (Work.BoseBoxFock.kappaL ℓ n) y : ℝ) : ℂ))
        = (((-(inner ℝ (Work.BoseBoxFock.kappaL ℓ n) y)) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hkey, Complex.norm_exp_ofReal_mul_I]
  -- the slice transform vanishes off the box (its `w`-support is inside the box)
  have hzero : ∀ y : E3, y ∉ Work.BoseK15.corpusBox.boxL ℓ → f y = 0 := by
    intro y hy
    have hfun : (fun w => (starRingEnd ℂ) (H w y)) = 0 := by
      funext w
      have hw : H w y = 0 := by
        by_contra hne
        exact hy (hHs w y hne).2
      simp [hw]
    have hgoal : Submission.BoseGases.kinFT (fun w => (starRingEnd ℂ) (H w y))
        (Work.BoseBoxFock.kappaL ℓ n) = 0 := by
      rw [hfun]
      simp [Submission.BoseGases.kinFT]
    simpa only [hf] using hgoal
  -- Cauchy–Schwarz on `L²` with the indicator of the box
  have hs : MeasurableSet (Work.BoseK15.corpusBox.boxL ℓ) :=
    Work.BoseK15.corpusBox.boxL_measurableSet ℓ
  have hfin : MeasureTheory.volume (Work.BoseK15.corpusBox.boxL ℓ) ≠ ⊤ := by
    rw [Work.BoseK15.corpusBox.volume_boxL hℓ]
    exact ENNReal.ofReal_ne_top
  have hmem : MeasureTheory.MemLp (fun y : E3 => ‖f y‖) 2 MeasureTheory.volume := hMlf.norm
  have hcs := Work.BoseFixB1S.integral_sq_le_measure_mul_integral_sq
    (μ := MeasureTheory.volume) hs hfin hmem
    (fun y hy => by rw [hzero y hy, norm_zero])
  have hvol : (MeasureTheory.volume (Work.BoseK15.corpusBox.boxL ℓ)).toReal = ℓ ^ 3 :=
    Work.BoseK15.corpusBox.volume_boxL_toReal hℓ
  rw [hvol] at hcs
  -- the norm of the pairing is dominated by the `L¹`-norm of the slice transform
  have hbound : ‖Work.BoseBoxFock.L1Tails.hPair ℓ H n‖ ≤ ∫ y : E3, ‖f y‖ := by
    rw [hid]
    refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
    apply integral_congr_ae
    filter_upwards with y
    have hc : ‖(starRingEnd ℂ) (f y)‖ = ‖f y‖ := Complex.norm_conj (f y)
    rw [norm_mul, hc, hexp y, one_mul]
  calc ‖Work.BoseBoxFock.L1Tails.hPair ℓ H n‖ ^ 2
      ≤ (∫ y : E3, ‖f y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hbound 2
    _ ≤ (∫ y : E3, ‖f y‖ ^ 2) * ℓ ^ 3 := hcs
    _ = ℓ ^ 3 * ∫ y : E3, ‖f y‖ ^ 2 := by ring

end Work.BoseBoxFock.L1Tails.hPairSqLe
