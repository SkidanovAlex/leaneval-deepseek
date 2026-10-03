import Mathlib
import Submission.Work.KMTAreas.A7.ModelApproxHiDefs
import Submission.Work.KMTAreas.A7.SmallKernMassBasics
import Submission.Work.A7.varphiN_integrable_measurable

namespace Work.KMTAreas.A7

open MeasureTheory

/-- **The exact-height Ionescu--Wainger kernel of the modulated bump `φ̃_{N,t}` is a uniformly
`ℓ¹` family, with measurable parameter dependence.**

For the kernel `hiKer ρ l (φ̃_{N,t})` of the exact-height projection `Tex ρ l (φ̃_{N,t})`
(`hiKer = iwKernel ∘ iwSymbolSet (diffFreqs ρ l) ∘ periodize`, `ModelApproxHiDefs.lean`), the
integrand of the §6 model operator `hiKmod` (which is the `t`-integral over `(1/2,1]` of the
composition of `hiTwKernel` with the two kernels `hiKer ρ l₁ (φ_{N,t})`,
`hiKer ρ l₂ (φ̃_{N,t})`), we prove the three facts needed to apply the dominated-convergence /
Fubini toolbox of `Work.KMTPlan.A6.{bilinOp_intervalIntegral, vpc_bilinOp_intervalIntegral}`:

* absolute summability in `j` for every `t ∈ (1/2, 1]`;
* one bound `B` for the `ℓ¹`-norm, uniform in `t ∈ (1/2,1]`;
* a.e. measurability of each coefficient `t ↦ hiKer ρ l (φ̃_{N,t}) j`.

The decay is `‖hiKer ρ l (φ̃_{N,t}) j‖ ≤ C / (1 + |j|)²` with `C` independent of `t`, which is
`Work.KMTAreas.A7.tmKernel_varphitildeNt_decay` (the same statement for the raw `iwKernel`; `hiKer`
is definitionally that object).  Summability and the uniform `ℓ¹`-bound follow by comparison with
the convergent series `∑_j 1/(1+|j|)²` (`Work.KMTContract.kernel_l1_of_decay`,
`Work.KMTAreas.A7.summable_one_div_sq_int`).  Measurability is
`Work.KMTAreas.A7.measurable_fourierCoeff_iwSymbolSet` applied to the jointly measurable family
`(t, ξ) ↦ φ̃_{N,t}(ξ)` (`Work.KMTAreas.A7.measurable_varphitildeNt_uncurry`). -/
theorem hiKer_varphitildeNt_spec (ρ : ℝ) (P : Polynomial ℤ) (l N k : ℕ) :
    (∀ t ∈ Set.Ioc (1/2 : ℝ) 1, Summable fun j : ℤ =>
        ‖Work.KMTAreas.A7.hiKer ρ l
          (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t) j‖)
      ∧ (∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Set.Ioc (1/2 : ℝ) 1,
          (∑' j : ℤ, ‖Work.KMTAreas.A7.hiKer ρ l
            (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t) j‖) ≤ B)
      ∧ (∀ j : ℤ, AEMeasurable
          (fun t : ℝ => Work.KMTAreas.A7.hiKer ρ l
            (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t) j)
          MeasureTheory.volume) := by
  classical
  obtain ⟨C, hCpos, hdec⟩ := tmKernel_varphitildeNt_decay P ρ l N k
  have hCnn : 0 ≤ C := hCpos.le
  refine ⟨?_, ?_, ?_⟩
  · -- absolute summability of the kernel for each `t ∈ (1/2, 1]`
    intro t ht
    exact Work.KMTContract.kernel_l1_of_decay
      (fun j => hdec t (Set.Ioc_subset_Icc_self ht) j)
  · -- one uniform `ℓ¹`-bound on `(1/2, 1]`, by comparison with `∑_j 1/(1+|j|)^2`
    refine ⟨C * (∑' j : ℤ, 1 / (1 + |(j : ℝ)|) ^ 2), ?_, ?_⟩
    · exact mul_nonneg hCnn (tsum_nonneg fun _ => by positivity)
    · intro t ht
      have ht' : t ∈ Set.Icc (1/2 : ℝ) 1 := Set.Ioc_subset_Icc_self ht
      have hsum1 : Summable fun j : ℤ =>
          ‖Work.KMTAreas.A7.hiKer ρ l
            (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t) j‖ :=
        Work.KMTContract.kernel_l1_of_decay (fun j => hdec t ht' j)
      have hsum2 : Summable fun j : ℤ => C * (1 / (1 + |(j : ℝ)|) ^ 2) :=
        summable_one_div_sq_int.mul_left C
      calc (∑' j : ℤ, ‖Work.KMTAreas.A7.hiKer ρ l
              (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t) j‖)
          ≤ ∑' j : ℤ, C * (1 / (1 + |(j : ℝ)|) ^ 2) := by
            refine Summable.tsum_le_tsum (fun j => ?_) hsum1 hsum2
            have h := hdec t ht' j
            rwa [div_eq_mul_one_div] at h
        _ = C * (∑' j : ℤ, 1 / (1 + |(j : ℝ)|) ^ 2) := tsum_mul_left
  · -- measurability of each coefficient in the modulation parameter
    intro j
    have h : Measurable (fun t : ℝ => Work.KMTAreas.A7.hiKer ρ l
        (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t) j) :=
      measurable_fourierCoeff_iwSymbolSet (diffFreqs ρ l) j
        (φ := fun t ξ => Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t ξ)
        (measurable_varphitildeNt_uncurry P N k)
    exact h.aemeasurable

end Work.KMTAreas.A7
