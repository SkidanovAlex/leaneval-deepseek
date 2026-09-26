import Submission.Work.FunctionalEquations.DecayExpansionDifference
import Submission.Work.CKFinal.Shadow.Util
import Submission.Work.CKFinal.Shadow.Basic
import Submission.Work.CKFinal.Shadow.BasisCoeffsDelta
import Submission.Work.CKFinal.Shadow.BasisCoeffsDeltaAux
import Submission.Work.CKFinal.Shadow.Gap
import Submission.Work.CKFinal.Shadow.Gen
import Submission.Work.CKFinal.Shadow.Main
import Submission.Work.CKFinal.Shadow.ReconstructionCLM
import Submission.Work.CKFinal.Shadow.ReconstructionGaussian
import Submission.Work.CKFinal.Shadow.ReconstructionGaussianGen
import Submission.Work.CKFinal.Shadow.Section8ValueDataOfRigidity
import Submission.Work.CKFinal.Shadow.SummableExpansionTerms

open scoped ContDiff
set_option linter.dupNamespace false

namespace Work.CKFinal.Shadow

namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (rate_nonneg)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (tendsToZero_tsum_sub_gen)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (tendsToZero_tau_tsum_sub_gen)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (rate_le_add_one)
end Work.FunctionalEquations

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

noncomputable section

theorem DecayExpansionDifference {n : ℕ} [NeZero n] {k₀ : ℕ} (hk : 1 ≤ k₀)
    (S : Work.FE.FunctionalEquationSolution n) (basis : Work.Core.SampleIdx k₀ → Work.Core.RSch n)
    (hExp : Work.FE.ExpansionDataGen n k₀ S basis)
    (hb : ∀ j : Fin 4, ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ (m : Set.Ici k₀)
        (x : EuclideanSpace ℝ (Fin n)),
        ‖(FourierTransform.fourierCLM ℂ (SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ)
            (basis (m, j)).1) x‖
          ≤ C * ((m.1 : ℝ) + 1) ^ N) :
    Work.FE.TendsToZeroInStrip n ((k₀ : ℝ) - 1)
        (fun τ x => S.F τ x - Work.FE.fourierExpansionTildeGen k₀ basis τ x) ∧
    Work.FE.TendsToZeroInStrip n ((k₀ : ℝ) - 1)
        (fun τ x => S.Ftilde τ x - Work.FE.fourierExpansionGen k₀ basis τ x) := by
  obtain ⟨hF, hFt, hDF, hDFt, hGrow⟩ := hExp
  obtain ⟨Cb, Nb, hCb, hGb⟩ := hGrow 0 0
  -- the polynomial bound on the values of the four basis families
  have hval : ∀ (j : Fin 4) (m : Set.Ici k₀) (x : E n),
      ‖(basis (m, j)).1 x‖ ≤ Cb * ((m.1 : ℝ) + 1) ^ Nb := by
    intro j m x
    have hx := hGb m j x
    simp only [pow_zero, one_mul] at hx
    have hrad : radialDeriv 0 (⇑(basis (m, j)).1) x = (basis (m, j)).1 x := by
      simp only [radialDeriv, iteratedDeriv_zero]
      exact (basis (m, j)).2 _ _ (by
        rw [Work.Sampling.realIncl_norm, abs_of_nonneg (norm_nonneg x)])
    rwa [hrad] at hx
  -- the polynomial bound on the Fourier transforms of the four basis families
  have hFT : ∀ (j : Fin 4) (x : E n), ∃ C N, 0 ≤ C ∧ ∀ m : Set.Ici k₀,
      ‖(FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, j)).1) x‖
        ≤ C * ((m.1 : ℝ) + 1) ^ N := by
    intro j x
    obtain ⟨C, N, hC, hbC⟩ := hb j
    exact ⟨C, N, hC, fun m => hbC m x⟩
  -- a uniform polynomial bound for `(2πi · √(2m)) · basis (·, j)`
  have hrate : ∀ (j : Fin 4) (x : E n), ∃ C N, 0 ≤ C ∧ ∀ m : Set.Ici k₀,
      ‖((2 * (Real.pi : ℂ) * Complex.I) * (rate m.1 : ℂ)) * (basis (m, j)).1 x‖
        ≤ C * ((m.1 : ℝ) + 1) ^ N := by
    intro j x
    refine ⟨2 * Real.pi * Cb, Nb + 1, mul_nonneg (by positivity) hCb, fun m => ?_⟩
    have h2 : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
      rw [show (2 * (Real.pi : ℂ) * Complex.I) = ((2 * Real.pi : ℝ) : ℂ) * Complex.I by
            push_cast; ring,
          norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
    rw [norm_mul, norm_mul, h2, Complex.norm_real, Real.norm_of_nonneg (rate_nonneg m.1)]
    have hpos : (0 : ℝ) ≤ (m.1 : ℝ) + 1 := by positivity
    have h2pi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    calc 2 * Real.pi * rate m.1 * ‖(basis (m, j)).1 x‖
        = (2 * Real.pi) * (rate m.1 * ‖(basis (m, j)).1 x‖) := by ring
      _ ≤ (2 * Real.pi) * (((m.1 : ℝ) + 1) * (Cb * ((m.1 : ℝ) + 1) ^ Nb)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul (rate_le_add_one m.1) (hval j m x) (norm_nonneg _) hpos) h2pi
      _ = (2 * Real.pi * Cb) * ((m.1 : ℝ) + 1) ^ (Nb + 1) := by rw [pow_succ]; ring
  have hrateFT : ∀ (j : Fin 4) (x : E n), ∃ C N, 0 ≤ C ∧ ∀ m : Set.Ici k₀,
      ‖((2 * (Real.pi : ℂ) * Complex.I) * (rate m.1 : ℂ))
          * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, j)).1) x‖
        ≤ C * ((m.1 : ℝ) + 1) ^ N := by
    intro j x
    obtain ⟨C, N, hC, hbC⟩ := hFT j x
    refine ⟨2 * Real.pi * C, N + 1, mul_nonneg (by positivity) hC, fun m => ?_⟩
    have h2 : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
      rw [show (2 * (Real.pi : ℂ) * Complex.I) = ((2 * Real.pi : ℝ) : ℂ) * Complex.I by
            push_cast; ring,
          norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
    rw [norm_mul, norm_mul, h2, Complex.norm_real, Real.norm_of_nonneg (rate_nonneg m.1)]
    have hpos : (0 : ℝ) ≤ (m.1 : ℝ) + 1 := by positivity
    have h2pi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    calc 2 * Real.pi * rate m.1
            * ‖(FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, j)).1) x‖
        = (2 * Real.pi) * (rate m.1
            * ‖(FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, j)).1) x‖) := by ring
      _ ≤ (2 * Real.pi) * (((m.1 : ℝ) + 1) * (C * ((m.1 : ℝ) + 1) ^ N)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul (rate_le_add_one m.1) (hbC m) (norm_nonneg _) hpos) h2pi
      _ = (2 * Real.pi * C) * ((m.1 : ℝ) + 1) ^ (N + 1) := by rw [pow_succ]; ring
  constructor
  · -- first conjunct: `F` versus the tilde expansion (`basis (·,1)`, `basis (·,3)`)
    have hA : TendsToZeroInStrip n ((k₀ : ℝ) - 1)
        (fun τ x => (∑' m : Set.Ici k₀, (basis (m, 0)).1 x * dirichletTerm m.1 τ)
          - (∑' m : Set.Ici k₀,
              (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 1)).1) x
                * dirichletTerm m.1 τ)) :=
      tendsToZero_tsum_sub_gen (k₀ := k₀)
        (c := fun x m => (basis (m, 0)).1 x)
        (c' := fun x m => (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 1)).1) x)
        (fun x => ⟨Cb, Nb, hCb, fun m => hval 0 m x⟩)
        (fun x => hFT 1 x)
    have hB : TendsToZeroInStrip n ((k₀ : ℝ) - 1)
        (fun τ x => τ * ((∑' m : Set.Ici k₀,
              ((2 * (Real.pi : ℂ) * Complex.I) * (rate m.1 : ℂ)) * (basis (m, 2)).1 x
                * dirichletTerm m.1 τ)
          - (∑' m : Set.Ici k₀,
              ((2 * (Real.pi : ℂ) * Complex.I) * (rate m.1 : ℂ))
                * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 3)).1) x
                * dirichletTerm m.1 τ))) :=
      tendsToZero_tau_tsum_sub_gen (k₀ := k₀)
        (c := fun x m => ((2 * (Real.pi : ℂ) * Complex.I) * (rate m.1 : ℂ)) * (basis (m, 2)).1 x)
        (c' := fun x m => ((2 * (Real.pi : ℂ) * Complex.I) * (rate m.1 : ℂ))
            * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 3)).1) x)
        (fun x => hrate 2 x) (fun x => hrateFT 3 x)
    refine TendsToZeroInStrip.congr (Work.FunctionalEquations.TendsToZeroInStrip.add hA hB) (fun τ x hτ => ?_)
    rw [Work.FE.fourierExpansionTildeGen, hF τ x hτ]
    obtain ⟨C3, N3, hC3, hbC3⟩ := hFT 3 x
    have hb2 : (∑' m : Set.Ici k₀,
          ((2 * (Real.pi : ℂ) * Complex.I) * (rate m.1 : ℂ)) * (basis (m, 2)).1 x
            * dirichletTerm m.1 τ)
        = (2 * (Real.pi : ℂ) * Complex.I)
          * (∑' m : Set.Ici k₀, (rate m.1 : ℂ) * (basis (m, 2)).1 x
              * dirichletTerm m.1 τ) := by
      rw [show (∑' m : Set.Ici k₀,
            ((2 * (Real.pi : ℂ) * Complex.I) * (rate m.1 : ℂ)) * (basis (m, 2)).1 x
              * dirichletTerm m.1 τ)
          = ∑' m : Set.Ici k₀, (2 * (Real.pi : ℂ) * Complex.I)
              * ((rate m.1 : ℂ) * (basis (m, 2)).1 x * dirichletTerm m.1 τ) from
          tsum_congr fun m => by ring]
      rw [tsum_mul_left]
    have hb3 : (∑' m : Set.Ici k₀,
          ((2 * (Real.pi : ℂ) * Complex.I) * (rate m.1 : ℂ))
            * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 3)).1) x
            * dirichletTerm m.1 τ)
        = (2 * (Real.pi : ℂ) * Complex.I)
          * (∑' m : Set.Ici k₀, (rate m.1 : ℂ)
              * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 3)).1) x
              * dirichletTerm m.1 τ) := by
      rw [show (∑' m : Set.Ici k₀,
            ((2 * (Real.pi : ℂ) * Complex.I) * (rate m.1 : ℂ))
              * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 3)).1) x
              * dirichletTerm m.1 τ)
          = ∑' m : Set.Ici k₀, (2 * (Real.pi : ℂ) * Complex.I)
              * ((rate m.1 : ℂ)
                * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 3)).1) x
                * dirichletTerm m.1 τ) from
          tsum_congr fun m => by ring]
      rw [tsum_mul_left]
    rw [hb2, hb3]
    ring
  · -- second conjunct: `F̃` versus the plain expansion (`basis (·,0)`, `basis (·,2)`)
    have hA : TendsToZeroInStrip n ((k₀ : ℝ) - 1)
        (fun τ x => (∑' m : Set.Ici k₀, (basis (m, 1)).1 x * dirichletTerm m.1 τ)
          - (∑' m : Set.Ici k₀,
              (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 0)).1) x
                * dirichletTerm m.1 τ)) :=
      tendsToZero_tsum_sub_gen (k₀ := k₀)
        (c := fun x m => (basis (m, 1)).1 x)
        (c' := fun x m => (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 0)).1) x)
        (fun x => ⟨Cb, Nb, hCb, fun m => hval 1 m x⟩)
        (fun x => hFT 0 x)
    have hB : TendsToZeroInStrip n ((k₀ : ℝ) - 1)
        (fun τ x => τ * ((∑' m : Set.Ici k₀,
              ((2 * (Real.pi : ℂ) * Complex.I) * (rate m.1 : ℂ)) * (basis (m, 3)).1 x
                * dirichletTerm m.1 τ)
          - (∑' m : Set.Ici k₀,
              ((2 * (Real.pi : ℂ) * Complex.I) * (rate m.1 : ℂ))
                * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 2)).1) x
                * dirichletTerm m.1 τ))) :=
      tendsToZero_tau_tsum_sub_gen (k₀ := k₀)
        (c := fun x m => ((2 * (Real.pi : ℂ) * Complex.I) * (rate m.1 : ℂ)) * (basis (m, 3)).1 x)
        (c' := fun x m => ((2 * (Real.pi : ℂ) * Complex.I) * (rate m.1 : ℂ))
            * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 2)).1) x)
        (fun x => hrate 3 x) (fun x => hrateFT 2 x)
    refine TendsToZeroInStrip.congr (Work.FunctionalEquations.TendsToZeroInStrip.add hA hB) (fun τ x hτ => ?_)
    rw [Work.FE.fourierExpansionGen, hFt τ x hτ]
    have hb3 : (∑' m : Set.Ici k₀,
          ((2 * (Real.pi : ℂ) * Complex.I) * (rate m.1 : ℂ)) * (basis (m, 3)).1 x
            * dirichletTerm m.1 τ)
        = (2 * (Real.pi : ℂ) * Complex.I)
          * (∑' m : Set.Ici k₀, (rate m.1 : ℂ) * (basis (m, 3)).1 x
              * dirichletTerm m.1 τ) := by
      rw [show (∑' m : Set.Ici k₀,
            ((2 * (Real.pi : ℂ) * Complex.I) * (rate m.1 : ℂ)) * (basis (m, 3)).1 x
              * dirichletTerm m.1 τ)
          = ∑' m : Set.Ici k₀, (2 * (Real.pi : ℂ) * Complex.I)
              * ((rate m.1 : ℂ) * (basis (m, 3)).1 x * dirichletTerm m.1 τ) from
          tsum_congr fun m => by ring]
      rw [tsum_mul_left]
    have hb2 : (∑' m : Set.Ici k₀,
          ((2 * (Real.pi : ℂ) * Complex.I) * (rate m.1 : ℂ))
            * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 2)).1) x
            * dirichletTerm m.1 τ)
        = (2 * (Real.pi : ℂ) * Complex.I)
          * (∑' m : Set.Ici k₀, (rate m.1 : ℂ)
              * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 2)).1) x
              * dirichletTerm m.1 τ) := by
      rw [show (∑' m : Set.Ici k₀,
            ((2 * (Real.pi : ℂ) * Complex.I) * (rate m.1 : ℂ))
              * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 2)).1) x
              * dirichletTerm m.1 τ)
          = ∑' m : Set.Ici k₀, (2 * (Real.pi : ℂ) * Complex.I)
              * ((rate m.1 : ℂ)
                * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 2)).1) x
                * dirichletTerm m.1 τ) from
          tsum_congr fun m => by ring]
      rw [tsum_mul_left]
    rw [hb3, hb2]
    ring

end

end Work.FunctionalEquations


end Work.CKFinal.Shadow
