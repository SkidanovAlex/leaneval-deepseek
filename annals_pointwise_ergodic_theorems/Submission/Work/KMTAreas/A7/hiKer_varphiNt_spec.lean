import Mathlib
import Submission.Work.KMTAreas.A7.ModelApproxHiDefs
import Submission.Work.KMTAreas.A7.SmallKernMassBasics
import Submission.Work.A7.varphiN_integrable_measurable

namespace Work.KMTAreas.A7

open MeasureTheory

/-- Joint measurability of the modulated bump `(t, ξ) ↦ φ_{N,t}(ξ)`. -/
private lemma measurable_varphiNt_uncurry_spec (N k : ℕ) :
    Measurable fun q : ℝ × ℝ => varphiNt N k q.1 q.2 := by
  have hee : Measurable ee := by unfold ee; fun_prop
  have hφN : Measurable (varphiN N k) := (Work.A7.varphiN_integrable_measurable N k).2
  have hmod : Measurable fun q : ℝ × ℝ => ee ((N : ℝ) * q.1 * q.2) :=
    hee.comp ((measurable_fst.const_mul (N : ℝ)).mul measurable_snd)
  exact (hφN.comp measurable_snd).mul hmod

/-- The exact-height IW kernel of the modulated bump `φ_{N,t}` is `ℓ¹` with a `t`-uniform bound,
and its coefficients are `AEMeasurable` in `t` (`hiKer ρ l φ = tmKernel ρ l φ` definitionally,
`tmKernel_varphiNt_decay` for the decay), -/
theorem hiKer_varphiNt_spec (ρ : ℝ) (l N k : ℕ) :
    (∀ t ∈ Set.Ioc (1/2 : ℝ) 1, Summable fun j : ℤ =>
        ‖Work.KMTAreas.A7.hiKer ρ l (Work.KMTAreas.A7.varphiNt N k t) j‖)
      ∧ (∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Set.Ioc (1/2 : ℝ) 1,
          (∑' j : ℤ, ‖Work.KMTAreas.A7.hiKer ρ l (Work.KMTAreas.A7.varphiNt N k t) j‖) ≤ B)
      ∧ (∀ j : ℤ, AEMeasurable
          (fun t : ℝ => Work.KMTAreas.A7.hiKer ρ l (Work.KMTAreas.A7.varphiNt N k t) j)
          MeasureTheory.volume) := by
  obtain ⟨C, hC0, hdec⟩ := tmKernel_varphiNt_decay ρ l N k
  have hdec' : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ j : ℤ,
      ‖hiKer ρ l (varphiNt N k t) j‖ ≤ C * ‖kmtKernWeight j‖ := by
    intro t ht j
    exact hdec t ht j
  have hsumm : ∀ t ∈ Set.Ioc (1/2 : ℝ) 1, Summable fun j : ℤ =>
      ‖hiKer ρ l (varphiNt N k t) j‖ := by
    intro t ht
    exact Summable.of_nonneg_of_le (fun j => norm_nonneg _)
      (fun j => hdec' t (Set.Ioc_subset_Icc_self ht) j) (summable_kmtKernWeight.mul_left C)
  refine ⟨hsumm, ⟨C * (∑' j : ℤ, ‖kmtKernWeight j‖), ?_, ?_⟩, ?_⟩
  · exact mul_nonneg hC0 (tsum_nonneg (fun _ => norm_nonneg _))
  · intro t ht
    calc (∑' j : ℤ, ‖hiKer ρ l (varphiNt N k t) j‖)
        ≤ ∑' j : ℤ, C * ‖kmtKernWeight j‖ :=
          Summable.tsum_le_tsum (fun j => hdec' t (Set.Ioc_subset_Icc_self ht) j)
            (hsumm t ht) (summable_kmtKernWeight.mul_left C)
      _ = C * (∑' j : ℤ, ‖kmtKernWeight j‖) := tsum_mul_left
  · intro j
    exact (measurable_fourierCoeff_iwSymbolSet (diffFreqs ρ l) j
      (φ := fun t ξ => varphiNt N k t ξ) (measurable_varphiNt_uncurry_spec N k)).aemeasurable

end Work.KMTAreas.A7
