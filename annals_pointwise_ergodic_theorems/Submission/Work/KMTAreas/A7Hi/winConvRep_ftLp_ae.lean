import Mathlib
import Submission.Work.KMTAreas.A7Rep.FiberVarSamplingGRepRotation
import Submission.Work.KMTAreas.A7.FiberOpWideCutEqSelf
import Submission.Work.KMTAreas.A7Rep.envAux

namespace Work.KMTAreas.A7Hi

open MeasureTheory
open scoped BigOperators ENNReal

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

theorem winConvRep_ftLp_ae (m : ℝ → ℂ) (hm : MeasureTheory.Integrable m)
    (hΨ : MeasureTheory.MemLp (Work.Analysis.IonescuWainger.periodize m) ⊤
      Work.Analysis.IonescuWainger.circleMeasure)
    {v : ℤ → ℂ} (hv : Memℓp v 2) :
    ∃ hw : Memℓp (Work.KMTAreas.A7Rep.winConvRep m v) 2,
      (Work.BourgainPlan.IonescuWainger.ftLp (Work.KMTAreas.A7Rep.winConvRep m v) hw
          : Work.Analysis.IonescuWainger.Circle → ℂ)
        =ᵐ[Work.Analysis.IonescuWainger.circleMeasure]
          fun ξ => Work.Analysis.IonescuWainger.periodize m ξ
            * (Work.BourgainPlan.IonescuWainger.ftLp v hv
                : Work.Analysis.IonescuWainger.Circle → ℂ) ξ := by
  -- ## Step 1: `cw m` is square summable, because `periodize m` is an `L²` function
  -- whose Fourier coefficients are `cw m`.
  have hper2 : MemLp (Work.Analysis.IonescuWainger.periodize m) 2
      Work.Analysis.IonescuWainger.circleMeasure := hΨ.mono_exponent le_top
  have hbase : ∀ j : ℤ, fourierCoeff (↑↑(hper2.toLp (Work.Analysis.IonescuWainger.periodize m))) j
      = Work.KMTAreas.A7.cw m j := fun j =>
    (congrFun (fourierCoeff_congr_ae hper2.coeFn_toLp) j).trans
      (Work.KMTPlan.A6.fourierCoeff_periodize_eq_cw hm j)
  have hcw : Memℓp (fun j : ℤ => Work.KMTAreas.A7.cw m j) 2 := by
    refine memℓp_gen ?_
    refine ((hasSum_sq_fourierCoeff
      (hper2.toLp (Work.Analysis.IonescuWainger.periodize m))).summable).congr (fun j => ?_)
    rw [hbase j, ENNReal.toReal_ofNat, show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num,
      Real.rpow_natCast]
  -- ## Step 2: the product `periodize m · 𝓕v` is an `L²` function
  set G : Circ → ℂ := fun ξ => Work.Analysis.IonescuWainger.periodize m ξ
    * (Work.BourgainPlan.IonescuWainger.ftLp v hv : Circ → ℂ) ξ with hGdef
  have hG : MemLp G 2 Work.Analysis.IonescuWainger.circleMeasure := by
    rw [hGdef]
    exact MemLp.fun_mul hΨ (Lp.memLp (Work.BourgainPlan.IonescuWainger.ftLp v hv))
      (hpqr := (inferInstance : (⊤ : ENNReal).HolderTriple 2 2))
  -- ## Step 3: the Fourier coefficients of the product are the window convolution
  set W : ℤ → ℂ := Work.KMTAreas.A7Rep.winConvRep m v with hWdef
  have hcoe : ∀ n : ℤ, fourierCoeff (↑↑(hG.toLp G)) n = W n := by
    intro n
    rw [congrFun (fourierCoeff_congr_ae hG.coeFn_toLp) n]
    change (∫ t : Circ, fourier (-n) t • G t
        ∂Work.Analysis.IonescuWainger.circleMeasure) = W n
    trans ∫ t : Circ, Work.Analysis.IonescuWainger.periodize m t
        * (Work.BourgainPlan.IonescuWainger.ftLp v hv : Circ → ℂ) t * star (fourier n t)
        ∂Work.Analysis.IonescuWainger.circleMeasure
    · refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only [hGdef, smul_eq_mul, fourier_neg, starRingEnd_apply]
      ring
    · rw [hWdef]
      exact Work.KMTAreas.A7Rep.circleValue hm hcw hv n
  -- ## Step 4: hence `W` is square summable
  have hsumm : Summable (fun n : ℤ => ‖W n‖ ^ (2 : ℝ)) := by
    refine ((hasSum_sq_fourierCoeff (hG.toLp G)).summable).congr (fun n => ?_)
    rw [hcoe n, show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
  have hW : Memℓp W 2 := memℓp_gen hsumm
  -- ## Step 5: `𝓕W` and the product have the same Fourier coefficients, so they coincide
  have hLp : Work.BourgainPlan.IonescuWainger.ftLp W hW = hG.toLp G := by
    refine (fourierBasis (T := 1)).repr.injective ?_
    ext n
    rw [HilbertBasis.repr_apply_apply, Work.BourgainPlan.IonescuWainger.ftLp_coeff hW n,
      fourierBasis_repr]
    exact (hcoe n).symm
  have hae : (Work.BourgainPlan.IonescuWainger.ftLp W hW : Circ → ℂ)
      =ᵐ[Work.Analysis.IonescuWainger.circleMeasure] G :=
    (Lp.ext_iff.1 hLp).trans (MemLp.coeFn_toLp hG)
  exact ⟨hW, hae⟩

end Work.KMTAreas.A7Hi
