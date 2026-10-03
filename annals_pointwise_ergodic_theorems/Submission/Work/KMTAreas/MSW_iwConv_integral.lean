import Mathlib
import Submission.Work.KMTAreas.MSW_defs

open scoped BigOperators ENNReal NNReal FourierTransform
open MeasureTheory

namespace Work.KMTAreas

/-- **The Ionescu–Wainger convolution as a Fourier integral.**  For an integrable symbol `Ψ` on
the frequency circle and a sequence `f` supported on a finite set `s`, the convolution of `f`
with the kernel `iwKernel Ψ j = \hat Ψ(j)` of `Ψ` is the integral against `Ψ` of the
trigonometric polynomial `mswTrigC s f` modulated by the character `e(-n·)`:

`∑_j \hat Ψ(j) · f(n - j) = ∫ Ψ(t) · (∑_{m ∈ s} f m · e(m t)) · e(-n t) dt`.

Both sides are the finite sum `∑_{m ∈ s} f m · \hat Ψ(n - m)`: the left hand side because `f`
vanishes off `s`, the right hand side by expanding the trigonometric polynomial and using the
additivity of the characters, `e(m t) e(-n t) = e((m - n) t)`. -/
theorem MSW_iwConv_integral {Ψ : Work.Analysis.IonescuWainger.Circle → ℂ}
    (hΨ : MeasureTheory.Integrable Ψ Work.Analysis.IonescuWainger.circleMeasure)
    {s : Finset ℤ} {f : ℤ → ℂ} (hs : ∀ m, m ∉ s → f m = 0) (n : ℤ) :
    tsum (fun j : ℤ => Work.Analysis.IWMultiplier.iwKernel Ψ j • f (n - j))
      = ∫ t : Work.Analysis.IonescuWainger.Circle,
          Ψ t * mswTrigC s f t * (fourier (-n) t)
        ∂Work.Analysis.IonescuWainger.circleMeasure := by
  -- The left-hand side is the finite sum `∑_{m ∈ s} \hat Ψ(n - m) · f m`.
  have hL : tsum (fun j : ℤ => Work.Analysis.IWMultiplier.iwKernel Ψ j • f (n - j))
      = ∑ m ∈ s, Work.Analysis.IWMultiplier.iwKernel Ψ (n - m) * f m := by
    rw [tsum_eq_sum (L := SummationFilter.unconditional ℤ)
      (s := s.image (fun m => n - m)) ?_]
    · rw [Finset.sum_image (sub_right_injective (b := n)).injOn]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [show n - (n - m) = m by ring, smul_eq_mul]
    · intro j hj
      have hz : f (n - j) = 0 := by
        by_contra hne
        exact hj (Finset.mem_image.mpr ⟨n - j, by_contra (fun h => hne (hs _ h)), by ring⟩)
      rw [hz, smul_zero]
  -- The right-hand side is the same finite sum.
  have hR : (∫ t : Work.Analysis.IonescuWainger.Circle,
        Ψ t * mswTrigC s f t * (fourier (-n) t)
        ∂Work.Analysis.IonescuWainger.circleMeasure)
      = ∑ m ∈ s, f m * Work.Analysis.IWMultiplier.iwKernel Ψ (n - m) := by
    -- Expand the trigonometric polynomial inside the integral.
    have hpt : (fun t : Work.Analysis.IonescuWainger.Circle =>
          Ψ t * mswTrigC s f t * (fourier (-n) t))
        = fun t => ∑ m ∈ s, f m * (Ψ t * fourier m t * (fourier (-n) t)) := by
      funext t
      simp only [mswTrigC, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      ring
    rw [hpt]
    rw [MeasureTheory.integral_finsetSum s ?_]
    · refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [integral_const_mul]
      congr 1
      -- Identify `∫ Ψ · e(m·) · e(-n·)` with the Fourier coefficient `\hat Ψ(n - m)`.
      rw [Work.Analysis.IWMultiplier.iwKernel]
      show (∫ t : Work.Analysis.IonescuWainger.Circle,
              Ψ t * fourier m t * (fourier (-n) t)
            ∂Work.Analysis.IonescuWainger.circleMeasure)
        = ∫ t : Work.Analysis.IonescuWainger.Circle,
              fourier (-(n - m)) t • Ψ t
            ∂Work.Analysis.IonescuWainger.circleMeasure
      apply integral_congr_ae
      filter_upwards with t
      rw [smul_eq_mul]
      have h := fourier_add (T := 1) (m := m) (n := -n) (x := t)
      rw [show m + -n = m - n by ring] at h
      rw [show -(n - m) = m - n by ring, h]
      ring
    · -- Integrability of the summands: `Ψ` times a bounded continuous factor.
      intro m _
      have hbase : Integrable (fun t : Work.Analysis.IonescuWainger.Circle =>
          Ψ t * fourier m t) Work.Analysis.IonescuWainger.circleMeasure :=
        hΨ.mul_bdd ((map_continuous (fourier m)).aestronglyMeasurable)
          (Filter.Eventually.of_forall fun t => by
            rw [fourier_apply, Circle.norm_coe])
      have hbase2 : Integrable (fun t : Work.Analysis.IonescuWainger.Circle =>
          Ψ t * fourier m t * (fourier (-n) t))
          Work.Analysis.IonescuWainger.circleMeasure :=
        hbase.mul_bdd ((map_continuous (fourier (-n))).aestronglyMeasurable)
          (Filter.Eventually.of_forall fun t => by
            rw [fourier_apply, Circle.norm_coe])
      exact hbase2.const_mul (f m)
  rw [hL, hR]
  exact Finset.sum_congr rfl (fun m _ => mul_comm _ _)

end Work.KMTAreas
