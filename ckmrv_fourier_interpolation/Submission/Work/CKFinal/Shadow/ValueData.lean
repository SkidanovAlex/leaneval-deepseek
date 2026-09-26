import Submission.Work.Section8P.ValueData
import Submission.Work.CKFinal.Shadow.Util
import Submission.Work.CKFinal.Shadow.Basic
import Submission.Work.CKFinal.Shadow.BasisCoeffsDelta
import Submission.Work.CKFinal.Shadow.BasisCoeffsDeltaAux
import Submission.Work.CKFinal.Shadow.Coefficients
import Submission.Work.CKFinal.Shadow.DecayExpansionDifference
import Submission.Work.CKFinal.Shadow.Defs
import Submission.Work.CKFinal.Shadow.DeltaGen
import Submission.Work.CKFinal.Shadow.DifferenceExpansionF
import Submission.Work.CKFinal.Shadow.DifferenceExpansionFtilde
import Submission.Work.CKFinal.Shadow.ExpansionData
import Submission.Work.CKFinal.Shadow.ExpansionDataShiftTwo
import Submission.Work.CKFinal.Shadow.ExpansionDataTwoOfDecay
import Submission.Work.CKFinal.Shadow.ExpansionFromFunctionalEquations
import Submission.Work.CKFinal.Shadow.FourierDataExtraction
import Submission.Work.CKFinal.Shadow.FourierExpansionSatisfiesFE
import Submission.Work.CKFinal.Shadow.FunctionCoefficients
import Submission.Work.CKFinal.Shadow.FunctionDerivExpansion
import Submission.Work.CKFinal.Shadow.FunctionExpansion
import Submission.Work.CKFinal.Shadow.Gap
import Submission.Work.CKFinal.Shadow.Gen
import Submission.Work.CKFinal.Shadow.HasDerivAtParametricIntegral
import Submission.Work.CKFinal.Shadow.InPExpansion
import Submission.Work.CKFinal.Shadow.Main
import Submission.Work.CKFinal.Shadow.MainGen
import Submission.Work.CKFinal.Shadow.ParametricDerivBounds
import Submission.Work.CKFinal.Shadow.ReconstructionCLM
import Submission.Work.CKFinal.Shadow.ReconstructionCLMGen
import Submission.Work.CKFinal.Shadow.ReconstructionGaussian
import Submission.Work.CKFinal.Shadow.ReconstructionGaussianGen
import Submission.Work.CKFinal.Shadow.Reduction
import Submission.Work.CKFinal.Shadow.Section8ValueDataOfRigidity
import Submission.Work.CKFinal.Shadow.SummableExpansionTerms
import Submission.Work.CKFinal.Shadow.TauDiffSetup
import Submission.Work.CKFinal.Shadow.TauDifferenceExpansionF
import Submission.Work.CKFinal.Shadow.TauDifferenceExpansionFtilde
import Submission.Work.CKFinal.Shadow.Thm31Adapter
import Submission.Work.CKFinal.Shadow.ValuePatternGen
import Submission.Work.CKFinal.Shadow.growth_combination
import Submission.Work.CKFinal.Shadow.kernel_isSchwartz
import Submission.Work.CKFinal.Shadow.psi_deriv_bound
import Submission.Work.CKFinal.Shadow.psi_smooth

open scoped ContDiff
set_option linter.dupNamespace false

namespace Work.CKFinal.Shadow

namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (tendsToZero_tau_dirichletSeries)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (tendsToZero_dirichletSeries_sub_single)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (tendsToZero_dirichletSeries)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (differentiable_dirichletTerm)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (gaussianFun_samplePoint)
end Work.FunctionalEquations
namespace Work.Section8P
export _root_.Work.Section8P (InP_dirichletTerm)
end Work.Section8P
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (tsum_sub_delta_single)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (differentiableOn_dirichletSeries)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (differentiableOn_tau_dirichletSeries)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (radialDeriv_one_combination_eq_zero)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (radialDeriv_one_const_mul)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (radialDeriv_one_add)
end Work.FunctionalEquations
namespace Work.Section8P
export _root_.Work.Section8P (InP_two_pi_I_tau_mul_dirichletTerm)
end Work.Section8P
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (polyBoundSubGen')
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (radialDeriv_gaussianFun_samplePoint)
end Work.FunctionalEquations

/-
# Section 8 value normalisations from the paper-faithful rigidity lemma

`Submission/Work/FunctionalEquations/Section8ValueDataOfRigidity.lean` derives the value
normalisations of Section 8 of CKMRV (`F(τ,√(2m)) = e^{2πimτ}`, `F̃(τ,√(2m)) = 0`, and the
corresponding first radial derivatives) from the *`InP`-free* uniqueness statement
`Work.FE.HomogeneousRigidity`, which is false
(`Submission/Work/Rigidity/Counterexample.lean`).  This file redoes the same argument for
the paper-faithful statement `Work.Rigidity.HomogeneousRigidityP`, whose extra hypotheses
are exactly the two `𝒫`-membership conditions of `Work.Kernels.InP` that the argument must
now supply.

The pairs to which the uniqueness lemma is applied are
`(τ ↦ F(τ,√(2m)) − e^{2πimτ}, τ ↦ F̃(τ,√(2m)))` and its radial-derivative analogue; each
component is a Dirichlet expansion of the shape `A + 2πiτ·B` with polynomially bounded
coefficients, and `Work.Section8P.InP_dirichletExpansion`
(`Submission/Work/Section8P/InPExpansion.lean`) supplies the required `𝒫`-membership.

## Main results

* `Work.Section8P.value_data_at_P`, `Work.Section8P.deriv_data_at_P` : the pointwise
  normalisations at a sample radius `√(2m)`, `m ≥ k₀`.
* `Work.Section8P.Section8ValueDataGen_of_rigidityP` : their conjunction, in the form
  `Work.FE.Section8ValueDataGen n k₀ S basis`.
-/

namespace Work.Section8P

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Work.FunctionalEquations
open Filter Topology
open scoped FourierTransform SchwartzMap UpperHalfPlane

noncomputable section

/-! ## The value normalisations from rigidity -/

lemma value_data_at_P {n : ℕ} [NeZero n] {k₀ : ℕ} (hk : 1 ≤ k₀)
    (hR : Work.Rigidity.HomogeneousRigidityP n ((k₀ : ℝ) - 1)) (S : FunctionalEquationSolution n)
    (basis : SampleIdx k₀ → RSch n) (hExp : ExpansionDataGen n k₀ S basis)
    (m : Set.Ici k₀) :
    (∀ τ : ℂ, 0 < τ.im → S.F τ (samplePoint (n := n) (m.1 : ℝ)) = dirichletTerm m.1 τ) ∧
    (∀ τ : ℂ, 0 < τ.im → S.Ftilde τ (samplePoint (n := n) (m.1 : ℝ)) = 0) := by
  obtain ⟨hF, hFt, hDF, hDFt, hGrow⟩ := hExp
  set x₀ : E n := samplePoint (n := n) (m.1 : ℝ) with hx₀
  obtain ⟨C0, N0, hC0, hb0⟩ := hGrow 0 0
  have hval : ∀ (j : Fin 4) (m' : Set.Ici k₀),
      ‖(basis (m', j)).1 x₀‖ ≤ C0 * ((m'.1:ℝ)+1)^N0 := by
    intro j m'
    have h := hb0 m' j x₀
    rw [pow_zero, one_mul] at h
    have hx : realIncl (n := n) ‖x₀‖ = x₀ := by rw [hx₀]; exact realIncl_norm_samplePoint _
    rwa [radialDeriv_zero_apply (⇑(basis (m',j)).1) x₀ hx] at h
  have hdec_tau : ∀ (j : Fin 4), TendsToZeroInStrip n ((k₀:ℝ)-1)
      (fun τ (_ : E n) => τ * ∑' m' : Set.Ici k₀,
        ((2*(Real.pi:ℂ)*Complex.I) * ((rate m'.1 : ℂ) * (basis (m', j)).1 x₀))
          * dirichletTerm m'.1 τ) := by
    intro j
    refine tendsToZero_tau_dirichletSeries (k₀ := k₀) (C := 2*Real.pi*C0) (N := N0+1)
      (by positivity) (fun m' => ?_) n
    have hb := hval j m'
    have hr0 : 0 ≤ rate m'.1 := Real.sqrt_nonneg _
    have hrle : rate m'.1 ≤ (m'.1:ℝ) + 1 := rate_le_add_one m'.1
    have hpos : 0 ≤ ((m'.1:ℝ)+1) := by positivity
    have h2pi : ‖(2*(Real.pi:ℂ)*Complex.I)‖ = 2*Real.pi := by
      rw [show (2*(Real.pi:ℂ)*Complex.I) = ((2*Real.pi:ℝ):ℂ) * Complex.I by push_cast; ring,
        norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [norm_mul, h2pi, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0]
    calc 2*Real.pi * (rate m'.1 * ‖(basis (m',j)).1 x₀‖)
        ≤ 2*Real.pi * (((m'.1:ℝ)+1) * (C0*((m'.1:ℝ)+1)^N0)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hrle hb (norm_nonneg _) hpos) (by positivity)
      _ = (2*Real.pi*C0) * ((m'.1:ℝ)+1)^(N0+1) := by rw [pow_succ]; ring
  have hdecF : TendsToZeroInStrip n ((k₀:ℝ)-1)
      (fun τ (_ : E n) => S.F τ x₀ - dirichletTerm m.1 τ) := by
    have hbase := TendsToZeroInStrip.add
      (tendsToZero_dirichletSeries_sub_single (k₀ := k₀) hC0 (fun m' => hval 0 m') m n)
      (hdec_tau 2)
    refine TendsToZeroInStrip.congr hbase (fun τ x hτ => ?_)
    have hsm : Summable fun m' : Set.Ici k₀ =>
        (rate m'.1 : ℂ) * (basis (m',2)).1 x₀ * dirichletTerm m'.1 τ :=
      summable_rate_mul_dirichletTerm_gen hC0 (fun m' => hval 2 m') τ hτ
    have hsum2 : (∑' m' : Set.Ici k₀,
          ((2*(Real.pi:ℂ)*Complex.I) * ((rate m'.1 : ℂ) * (basis (m',2)).1 x₀))
            * dirichletTerm m'.1 τ)
        = (2*(Real.pi:ℂ)*Complex.I) *
          (∑' m' : Set.Ici k₀, (rate m'.1 : ℂ) * (basis (m',2)).1 x₀ * dirichletTerm m'.1 τ) := by
      have hshape : (fun m' : Set.Ici k₀ =>
            ((2*(Real.pi:ℂ)*Complex.I) * ((rate m'.1 : ℂ) * (basis (m',2)).1 x₀)) * dirichletTerm m'.1 τ)
          = fun m' : Set.Ici k₀ => (2*(Real.pi:ℂ)*Complex.I) *
              (((rate m'.1 : ℂ) * (basis (m',2)).1 x₀) * dirichletTerm m'.1 τ) :=
        funext fun m' => by ring
      rw [hshape, hsm.tsum_mul_left (2*(Real.pi:ℂ)*Complex.I)]
    rw [hF τ x₀ hτ, hsum2]
    ring
  have hdecFt : TendsToZeroInStrip n ((k₀:ℝ)-1) (fun τ (_ : E n) => S.Ftilde τ x₀) := by
    have hbase := TendsToZeroInStrip.add
      (tendsToZero_dirichletSeries (k₀ := k₀) hC0 (fun m' => hval 1 m') n) (hdec_tau 3)
    refine TendsToZeroInStrip.congr hbase (fun τ x hτ => ?_)
    have hsm : Summable fun m' : Set.Ici k₀ =>
        (rate m'.1 : ℂ) * (basis (m',3)).1 x₀ * dirichletTerm m'.1 τ :=
      summable_rate_mul_dirichletTerm_gen hC0 (fun m' => hval 3 m') τ hτ
    have hsum2 : (∑' m' : Set.Ici k₀,
          ((2*(Real.pi:ℂ)*Complex.I) * ((rate m'.1 : ℂ) * (basis (m',3)).1 x₀))
            * dirichletTerm m'.1 τ)
        = (2*(Real.pi:ℂ)*Complex.I) *
          (∑' m' : Set.Ici k₀, (rate m'.1 : ℂ) * (basis (m',3)).1 x₀ * dirichletTerm m'.1 τ) := by
      have hshape : (fun m' : Set.Ici k₀ =>
            ((2*(Real.pi:ℂ)*Complex.I) * ((rate m'.1 : ℂ) * (basis (m',3)).1 x₀)) * dirichletTerm m'.1 τ)
          = fun m' : Set.Ici k₀ => (2*(Real.pi:ℂ)*Complex.I) *
              (((rate m'.1 : ℂ) * (basis (m',3)).1 x₀) * dirichletTerm m'.1 τ) :=
        funext fun m' => by ring
      rw [hshape, hsm.tsum_mul_left (2*(Real.pi:ℂ)*Complex.I)]
    rw [hFt τ x₀ hτ, hsum2]
    ring
  have hd1 : ∀ x : E n, DifferentiableOn ℂ
      (fun τ : ℂ => (fun τ (_ : E n) => S.F τ x₀ - dirichletTerm m.1 τ) τ x)
      {τ : ℂ | 0 < τ.im} :=
    fun x => (S.holomorphic_F x₀).sub (differentiable_dirichletTerm m.1).differentiableOn
  have hd2 : ∀ x : E n, DifferentiableOn ℂ
      (fun τ : ℂ => (fun τ (_ : E n) => S.Ftilde τ x₀) τ x) {τ : ℂ | 0 < τ.im} :=
    fun x => S.holomorphic_Ftilde x₀
  have hrec1 : ∀ (τ : ℂ) (x : E n), 0 < τ.im →
      (fun τ (_ : E n) => S.F τ x₀ - dirichletTerm m.1 τ) (τ+2) x
        - 2 * (fun τ (_ : E n) => S.F τ x₀ - dirichletTerm m.1 τ) (τ+1) x
        + (fun τ (_ : E n) => S.F τ x₀ - dirichletTerm m.1 τ) τ x = 0 := by
    intro τ x hτ
    have hrec := S.recur_F τ x₀ hτ
    have d1 : dirichletTerm m.1 (τ+1) = dirichletTerm m.1 τ := dirichletTerm_add_one _ _
    have d2 : dirichletTerm m.1 (τ+2) = dirichletTerm m.1 τ := by
      rw [show τ+2 = (τ+1)+1 by ring, dirichletTerm_add_one, dirichletTerm_add_one]
    show (S.F (τ+2) x₀ - dirichletTerm m.1 (τ+2)) - 2 * (S.F (τ+1) x₀ - dirichletTerm m.1 (τ+1))
        + (S.F τ x₀ - dirichletTerm m.1 τ) = 0
    rw [d1, d2,
      show (S.F (τ+2) x₀ - dirichletTerm m.1 τ) - 2 * (S.F (τ+1) x₀ - dirichletTerm m.1 τ)
          + (S.F τ x₀ - dirichletTerm m.1 τ)
        = (S.F (τ+2) x₀ - 2 * S.F (τ+1) x₀ + S.F τ x₀) from by ring,
      hrec]
  have hrec2 : ∀ (τ : ℂ) (x : E n), 0 < τ.im →
      (fun τ (_ : E n) => S.Ftilde τ x₀) (τ+2) x
        - 2 * (fun τ (_ : E n) => S.Ftilde τ x₀) (τ+1) x
        + (fun τ (_ : E n) => S.Ftilde τ x₀) τ x = 0 := by
    intro τ x hτ
    show S.Ftilde (τ+2) x₀ - 2 * S.Ftilde (τ+1) x₀ + S.Ftilde τ x₀ = 0
    rw [S.recur_Ftilde τ x₀ hτ]
  have hslash : ∀ (τ : ℂ) (x : E n), 0 < τ.im →
      (fun τ (_ : E n) => S.F τ x₀ - dirichletTerm m.1 τ) τ x
        + slashFactor n τ * (fun τ (_ : E n) => S.Ftilde τ x₀) (-1/τ) x = 0 := by
    intro τ x hτ
    have hfe := S.functional_equation τ x₀ hτ
    have hg : Work.Core.gaussianFun n τ x₀ = dirichletTerm m.1 τ := by
      rw [hx₀]; exact gaussianFun_samplePoint τ m.1
    show (S.F τ x₀ - dirichletTerm m.1 τ) + slashFactor n τ * S.Ftilde (-1/τ) x₀ = 0
    rw [← hg, ← hfe]; ring
  -- the expansions in the `dirichletExpansion` normal form
  have hFdir : ∀ τ : ℂ, 0 < τ.im → S.F τ x₀ = dirichletExpansion k₀
      (fun m : Set.Ici k₀ => (basis (m, 0)).1 x₀)
      (fun m : Set.Ici k₀ => (rate m.1 : ℂ) * (basis (m, 2)).1 x₀) τ := by
    intro τ hτ
    rw [hF τ x₀ hτ]
    rfl
  have hFtdir : ∀ τ : ℂ, 0 < τ.im → S.Ftilde τ x₀ = dirichletExpansion k₀
      (fun m : Set.Ici k₀ => (basis (m, 1)).1 x₀)
      (fun m : Set.Ici k₀ => (rate m.1 : ℂ) * (basis (m, 3)).1 x₀) τ := by
    intro τ hτ
    rw [hFt τ x₀ hτ]
    rfl
  -- the two pairs of Section 8 lie in `𝒫`
  have hInPF : Work.Kernels.InP (fun τ : ℍ => S.F (τ : ℂ) x₀) :=
    InP_F_at (k₀ := k₀) (S := S) (basis := basis) (x₀ := x₀)
      (C₀ := C0) (N₀ := N0) (C₂ := C0) (N₂ := N0) hC0
      (fun m => hval 0 m) hC0 (fun m => hval 2 m)
      hFdir
  have hInPFt : Work.Kernels.InP (fun τ : ℍ => S.Ftilde (τ : ℂ) x₀) :=
    InP_Ftilde_at (k₀ := k₀) (S := S) (basis := basis) (x₀ := x₀)
      (C₁ := C0) (N₁ := N0) (C₃ := C0) (N₃ := N0) hC0
      (fun m => hval 1 m) hC0 (fun m => hval 3 m)
      hFtdir
  have hInPval : Work.Kernels.InP
      (fun τ : ℍ => S.F (τ : ℂ) x₀ - dirichletTerm m.1 (τ : ℂ)) :=
    hInPF.sub (InP_dirichletTerm m)
  have hres := hR (fun τ (_ : E n) => S.F τ x₀ - dirichletTerm m.1 τ)
      (fun τ (_ : E n) => S.Ftilde τ x₀) (fun _ => hInPval) (fun _ => hInPFt)
      hrec1 hrec2 hslash hdecF hdecFt
  refine ⟨fun τ hτ => ?_, fun τ hτ => ?_⟩
  · exact sub_eq_zero.mp (hres τ 0 hτ).1
  · exact (hres τ 0 hτ).2

/-! ## The radial-derivative normalisations from rigidity -/

lemma deriv_data_at_P {n : ℕ} [NeZero n] {k₀ : ℕ} (hk : 1 ≤ k₀)
    (hR : Work.Rigidity.HomogeneousRigidityP n ((k₀ : ℝ) - 1)) (S : FunctionalEquationSolution n)
    (basis : SampleIdx k₀ → RSch n) (hExp : ExpansionDataGen n k₀ S basis)
    (m : Set.Ici k₀) :
    (∀ τ : ℂ, 0 < τ.im →
      radialDeriv 1 (S.F τ) (samplePoint (n := n) (m.1 : ℝ))
        = (2*(Real.pi:ℂ)*Complex.I*τ*(rate m.1 : ℂ)) * dirichletTerm m.1 τ) ∧
    (∀ τ : ℂ, 0 < τ.im →
      radialDeriv 1 (S.Ftilde τ) (samplePoint (n := n) (m.1 : ℝ)) = 0) := by
  obtain ⟨hF, hFt, hDF, hDFt, hGrow⟩ := hExp
  set x₀ : E n := samplePoint (n := n) (m.1 : ℝ) with hx₀
  obtain ⟨C1, N1, hC1, hb1⟩ := hGrow 0 1
  have hder : ∀ (j : Fin 4) (m' : Set.Ici k₀),
      ‖radialDeriv 1 (⇑(basis (m', j)).1) x₀‖ ≤ C1 * ((m'.1:ℝ)+1)^N1 := by
    intro j m'
    have h := hb1 m' j x₀
    rwa [pow_zero, one_mul] at h
  have h2pi : ‖(2*(Real.pi:ℂ)*Complex.I)‖ = 2*Real.pi := by
    rw [show (2*(Real.pi:ℂ)*Complex.I) = ((2*Real.pi:ℝ):ℂ) * Complex.I by push_cast; ring,
      norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hrate_der : ∀ (j : Fin 4) (m' : Set.Ici k₀),
      ‖(rate m'.1 : ℂ) * radialDeriv 1 (⇑(basis (m',j)).1) x₀‖ ≤ C1 * ((m'.1:ℝ)+1)^(N1+1) := by
    intro j m'
    have hr0 : 0 ≤ rate m'.1 := Real.sqrt_nonneg _
    have hrle : rate m'.1 ≤ (m'.1:ℝ) + 1 := rate_le_add_one m'.1
    have hpos : 0 ≤ ((m'.1:ℝ)+1) := by positivity
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0]
    calc rate m'.1 * ‖radialDeriv 1 (⇑(basis (m',j)).1) x₀‖
        ≤ ((m'.1:ℝ)+1) * (C1*((m'.1:ℝ)+1)^N1) :=
          mul_le_mul hrle (hder j m') (norm_nonneg _) hpos
      _ = C1 * ((m'.1:ℝ)+1)^(N1+1) := by rw [pow_succ]; ring
  have htau_bound : ∀ (j : Fin 4) (m' : Set.Ici k₀),
      ‖(2*(Real.pi:ℂ)*Complex.I) * ((rate m'.1 : ℂ) * radialDeriv 1 (⇑(basis (m',j)).1) x₀)‖
        ≤ (2*Real.pi*C1) * ((m'.1:ℝ)+1)^(N1+1) := by
    intro j m'
    rw [norm_mul, h2pi]
    calc 2*Real.pi * ‖(rate m'.1 : ℂ) * radialDeriv 1 (⇑(basis (m',j)).1) x₀‖
        ≤ 2*Real.pi * (C1 * ((m'.1:ℝ)+1)^(N1+1)) :=
          mul_le_mul_of_nonneg_left (hrate_der j m') (by positivity)
      _ = (2*Real.pi*C1) * ((m'.1:ℝ)+1)^(N1+1) := by ring
  -- decay of the `a`-series and the `τ`-series of the derivative of `F`
  have hdecA : TendsToZeroInStrip n ((k₀:ℝ)-1)
      (fun τ (_ : E n) =>
        ∑' m' : Set.Ici k₀, radialDeriv 1 (⇑(basis (m',0)).1) x₀ * dirichletTerm m'.1 τ) :=
    tendsToZero_dirichletSeries (k₀ := k₀) hC1 (fun m' => hder 0 m') n
  have hdecCtau : TendsToZeroInStrip n ((k₀:ℝ)-1)
      (fun τ (_ : E n) => τ * ∑' m' : Set.Ici k₀,
        ((2*(Real.pi:ℂ)*Complex.I) * ((rate m'.1 : ℂ) * radialDeriv 1 (⇑(basis (m',2)).1) x₀)
          - (if m = m' then (2*(Real.pi:ℂ)*Complex.I) * (rate m.1 : ℂ) else 0))
          * dirichletTerm m'.1 τ) := by
    refine tendsToZero_tau_dirichletSeries (k₀ := k₀) (C := 2*Real.pi*C1 + 2*Real.pi*rate m.1)
      (N := max (N1+1) 0) ?_ (fun m' => ?_) n
    · have h1 : (0:ℝ) ≤ 2*Real.pi*C1 := mul_nonneg (by positivity) hC1
      have h2 : (0:ℝ) ≤ 2*Real.pi*rate m.1 := mul_nonneg (by positivity) (rate_nonneg m.1)
      exact add_nonneg h1 h2
    · have h1 : ∀ m' : Set.Ici k₀,
          ‖(2*(Real.pi:ℂ)*Complex.I) * ((rate m'.1 : ℂ) * radialDeriv 1 (⇑(basis (m',2)).1) x₀)‖
            ≤ (2*Real.pi*C1) * ((m'.1:ℝ)+1)^(N1+1) := fun m' => htau_bound 2 m'
      have h2 : ∀ m' : Set.Ici k₀,
          ‖(if m = m' then (2*(Real.pi:ℂ)*Complex.I) * (rate m.1 : ℂ) else 0)‖
            ≤ (2*Real.pi*rate m.1) * ((m'.1:ℝ)+1)^(0:ℕ) := by
        intro m'
        rw [pow_zero, mul_one]
        by_cases hmm : m = m'
        · rw [if_pos hmm, norm_mul, h2pi, Complex.norm_real, Real.norm_of_nonneg (rate_nonneg m.1)]
        · rw [if_neg hmm, norm_zero]
          have h1 : (0:ℝ) ≤ 2*Real.pi := by positivity
          have h2 : (0:ℝ) ≤ rate m.1 := rate_nonneg m.1
          exact mul_nonneg h1 h2
      have hC1' : (0:ℝ) ≤ 2*Real.pi*C1 := mul_nonneg (by positivity) hC1
      have hC2' : (0:ℝ) ≤ 2*Real.pi*rate m.1 := mul_nonneg (by positivity) (rate_nonneg m.1)
      exact polyBoundSubGen' hC1' hC2' h1 h2 m'
  have hdecD : TendsToZeroInStrip n ((k₀:ℝ)-1)
      (fun τ (_ : E n) => radialDeriv 1 (S.F τ) x₀
        - (2*(Real.pi:ℂ)*Complex.I*τ*(rate m.1 : ℂ)) * dirichletTerm m.1 τ) := by
    refine TendsToZeroInStrip.congr (TendsToZeroInStrip.add hdecA hdecCtau) (fun τ x hτ => ?_)
    have hsm : Summable fun m' : Set.Ici k₀ =>
        (rate m'.1 : ℂ) * radialDeriv 1 (⇑(basis (m',2)).1) x₀ * dirichletTerm m'.1 τ :=
      summable_rate_mul_dirichletTerm_gen hC1 (fun m' => hder 2 m') τ hτ
    have hsm' : Summable fun m' : Set.Ici k₀ =>
        ((2*(Real.pi:ℂ)*Complex.I) * ((rate m'.1 : ℂ) * radialDeriv 1 (⇑(basis (m',2)).1) x₀))
          * dirichletTerm m'.1 τ :=
      (hsm.mul_left (2*(Real.pi:ℂ)*Complex.I)).congr (fun m' => by ring)
    have hsum2 : (∑' m' : Set.Ici k₀,
          ((2*(Real.pi:ℂ)*Complex.I) * ((rate m'.1 : ℂ) * radialDeriv 1 (⇑(basis (m',2)).1) x₀))
            * dirichletTerm m'.1 τ)
        = (2*(Real.pi:ℂ)*Complex.I) *
          (∑' m' : Set.Ici k₀,
            (rate m'.1 : ℂ) * radialDeriv 1 (⇑(basis (m',2)).1) x₀ * dirichletTerm m'.1 τ) := by
      have hshape : (fun m' : Set.Ici k₀ =>
            ((2*(Real.pi:ℂ)*Complex.I) * ((rate m'.1 : ℂ) * radialDeriv 1 (⇑(basis (m',2)).1) x₀))
              * dirichletTerm m'.1 τ)
          = fun m' : Set.Ici k₀ => (2*(Real.pi:ℂ)*Complex.I) *
              (((rate m'.1 : ℂ) * radialDeriv 1 (⇑(basis (m',2)).1) x₀) * dirichletTerm m'.1 τ) :=
        funext fun m' => by ring
      rw [hshape, hsm.tsum_mul_left (2*(Real.pi:ℂ)*Complex.I)]
    have hsub := tsum_sub_delta_single
      (c := fun m' => (2*(Real.pi:ℂ)*Complex.I) * ((rate m'.1 : ℂ) * radialDeriv 1 (⇑(basis (m',2)).1) x₀))
      ((2*(Real.pi:ℂ)*Complex.I) * (rate m.1 : ℂ)) m τ hsm'
    rw [hDF 1 τ x₀ hτ, hsub, hsum2]
    ring
  have hdecDt : TendsToZeroInStrip n ((k₀:ℝ)-1)
      (fun τ (_ : E n) => radialDeriv 1 (S.Ftilde τ) x₀) := by
    have hbase := TendsToZeroInStrip.add
      (tendsToZero_dirichletSeries (k₀ := k₀) hC1 (fun m' => hder 1 m') n)
      (tendsToZero_tau_dirichletSeries (k₀ := k₀) (C := 2*Real.pi*C1) (N := N1+1)
        (by positivity) (fun m' => htau_bound 3 m') n)
    refine TendsToZeroInStrip.congr hbase (fun τ x hτ => ?_)
    have hsm : Summable fun m' : Set.Ici k₀ =>
        (rate m'.1 : ℂ) * radialDeriv 1 (⇑(basis (m',3)).1) x₀ * dirichletTerm m'.1 τ :=
      summable_rate_mul_dirichletTerm_gen hC1 (fun m' => hder 3 m') τ hτ
    have hsum2 : (∑' m' : Set.Ici k₀,
          ((2*(Real.pi:ℂ)*Complex.I) * ((rate m'.1 : ℂ) * radialDeriv 1 (⇑(basis (m',3)).1) x₀))
            * dirichletTerm m'.1 τ)
        = (2*(Real.pi:ℂ)*Complex.I) *
          (∑' m' : Set.Ici k₀,
            (rate m'.1 : ℂ) * radialDeriv 1 (⇑(basis (m',3)).1) x₀ * dirichletTerm m'.1 τ) := by
      have hshape : (fun m' : Set.Ici k₀ =>
            ((2*(Real.pi:ℂ)*Complex.I) * ((rate m'.1 : ℂ) * radialDeriv 1 (⇑(basis (m',3)).1) x₀))
              * dirichletTerm m'.1 τ)
          = fun m' : Set.Ici k₀ => (2*(Real.pi:ℂ)*Complex.I) *
              (((rate m'.1 : ℂ) * radialDeriv 1 (⇑(basis (m',3)).1) x₀) * dirichletTerm m'.1 τ) :=
        funext fun m' => by ring
      rw [hshape, hsm.tsum_mul_left (2*(Real.pi:ℂ)*Complex.I)]
    rw [hDFt 1 τ x₀ hτ, hsum2]
    ring
  -- differentiability in `τ`
  have hdd : ∀ x : E n, DifferentiableOn ℂ
      (fun τ : ℂ => (fun τ (_ : E n) => radialDeriv 1 (S.F τ) x₀
        - (2*(Real.pi:ℂ)*Complex.I*τ*(rate m.1 : ℂ)) * dirichletTerm m.1 τ) τ x)
      {τ : ℂ | 0 < τ.im} := by
    intro x
    have hA : DifferentiableOn ℂ (fun τ : ℂ =>
        ∑' m' : Set.Ici k₀, radialDeriv 1 (⇑(basis (m',0)).1) x₀ * dirichletTerm m'.1 τ)
        {τ : ℂ | 0 < τ.im} := differentiableOn_dirichletSeries hC1 (fun m' => hder 0 m')
    have hB : DifferentiableOn ℂ (fun τ : ℂ => (2*(Real.pi:ℂ)*Complex.I*τ) *
        ∑' m' : Set.Ici k₀,
          (rate m'.1 : ℂ) * radialDeriv 1 (⇑(basis (m',2)).1) x₀ * dirichletTerm m'.1 τ)
        {τ : ℂ | 0 < τ.im} :=
      differentiableOn_tau_dirichletSeries hC1 (fun m' => hrate_der 2 m')
    have hC : DifferentiableOn ℂ (fun τ : ℂ =>
        (2*(Real.pi:ℂ)*Complex.I*τ*(rate m.1 : ℂ)) * dirichletTerm m.1 τ)
        {τ : ℂ | 0 < τ.im} := by
      have h1 : Differentiable ℂ (fun τ : ℂ => τ * dirichletTerm m.1 τ) :=
        differentiable_id.mul (differentiable_dirichletTerm m.1)
      refine DifferentiableOn.congr
        ((h1.const_mul (2*(Real.pi:ℂ)*Complex.I*(rate m.1:ℂ))).differentiableOn)
        (fun τ _ => ?_)
      ring
    refine DifferentiableOn.congr ((hA.add hB).sub hC) (fun τ hτ => ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    beta_reduce
    rw [hDF 1 τ x₀ hτ]
  have hddt : ∀ x : E n, DifferentiableOn ℂ
      (fun τ : ℂ => (fun τ (_ : E n) => radialDeriv 1 (S.Ftilde τ) x₀) τ x)
      {τ : ℂ | 0 < τ.im} := by
    intro x
    have hA : DifferentiableOn ℂ (fun τ : ℂ =>
        ∑' m' : Set.Ici k₀, radialDeriv 1 (⇑(basis (m',1)).1) x₀ * dirichletTerm m'.1 τ)
        {τ : ℂ | 0 < τ.im} := differentiableOn_dirichletSeries hC1 (fun m' => hder 1 m')
    have hB : DifferentiableOn ℂ (fun τ : ℂ => (2*(Real.pi:ℂ)*Complex.I*τ) *
        ∑' m' : Set.Ici k₀,
          (rate m'.1 : ℂ) * radialDeriv 1 (⇑(basis (m',3)).1) x₀ * dirichletTerm m'.1 τ)
        {τ : ℂ | 0 < τ.im} :=
      differentiableOn_tau_dirichletSeries hC1 (fun m' => hrate_der 3 m')
    refine DifferentiableOn.congr (hA.add hB) (fun τ hτ => ?_)
    simp only [Pi.add_apply]
    beta_reduce
    rw [hDFt 1 τ x₀ hτ]
  -- the functional equations
  have hr1 : ∀ (τ : ℂ) (x : E n), 0 < τ.im →
      (fun τ (_ : E n) => radialDeriv 1 (S.F τ) x₀
        - (2*(Real.pi:ℂ)*Complex.I*τ*(rate m.1 : ℂ)) * dirichletTerm m.1 τ) (τ+2) x
        - 2 * (fun τ (_ : E n) => radialDeriv 1 (S.F τ) x₀
            - (2*(Real.pi:ℂ)*Complex.I*τ*(rate m.1 : ℂ)) * dirichletTerm m.1 τ) (τ+1) x
        + (fun τ (_ : E n) => radialDeriv 1 (S.F τ) x₀
            - (2*(Real.pi:ℂ)*Complex.I*τ*(rate m.1 : ℂ)) * dirichletTerm m.1 τ) τ x = 0 := by
    intro τ x hτ
    have hcomb := radialDeriv_one_combination_eq_zero (A := S.F (τ+2)) (B := S.F (τ+1))
      (C := S.F τ) (x := x₀)
      (differentiableAt_profile (S.smooth_F (τ+2)) x₀)
      (differentiableAt_profile (S.smooth_F (τ+1)) x₀)
      (differentiableAt_profile (S.smooth_F τ) x₀)
      (fun y => S.recur_F τ y hτ)
    have d1 : dirichletTerm m.1 (τ+1) = dirichletTerm m.1 τ := dirichletTerm_add_one _ _
    have d2 : dirichletTerm m.1 (τ+2) = dirichletTerm m.1 τ := by
      rw [show τ+2 = (τ+1)+1 by ring, dirichletTerm_add_one, dirichletTerm_add_one]
    show (radialDeriv 1 (S.F (τ+2)) x₀
          - (2*(Real.pi:ℂ)*Complex.I*(τ+2)*(rate m.1 : ℂ)) * dirichletTerm m.1 (τ+2))
        - 2 * (radialDeriv 1 (S.F (τ+1)) x₀
          - (2*(Real.pi:ℂ)*Complex.I*(τ+1)*(rate m.1 : ℂ)) * dirichletTerm m.1 (τ+1))
        + (radialDeriv 1 (S.F τ) x₀
          - (2*(Real.pi:ℂ)*Complex.I*τ*(rate m.1 : ℂ)) * dirichletTerm m.1 τ) = 0
    rw [d1, d2]
    rw [show (radialDeriv 1 (S.F (τ+2)) x₀
            - 2*(Real.pi:ℂ)*Complex.I*(τ+2)*(rate m.1 : ℂ)*dirichletTerm m.1 τ)
          - 2 * (radialDeriv 1 (S.F (τ+1)) x₀
            - 2*(Real.pi:ℂ)*Complex.I*(τ+1)*(rate m.1 : ℂ)*dirichletTerm m.1 τ)
          + (radialDeriv 1 (S.F τ) x₀
            - 2*(Real.pi:ℂ)*Complex.I*τ*(rate m.1 : ℂ)*dirichletTerm m.1 τ)
        = radialDeriv 1 (S.F (τ+2)) x₀ - 2 * radialDeriv 1 (S.F (τ+1)) x₀
          + radialDeriv 1 (S.F τ) x₀ from by ring,
      hcomb]
  have hr2 : ∀ (τ : ℂ) (x : E n), 0 < τ.im →
      (fun τ (_ : E n) => radialDeriv 1 (S.Ftilde τ) x₀) (τ+2) x
        - 2 * (fun τ (_ : E n) => radialDeriv 1 (S.Ftilde τ) x₀) (τ+1) x
        + (fun τ (_ : E n) => radialDeriv 1 (S.Ftilde τ) x₀) τ x = 0 := by
    intro τ x hτ
    have hcomb := radialDeriv_one_combination_eq_zero (A := S.Ftilde (τ+2)) (B := S.Ftilde (τ+1))
      (C := S.Ftilde τ) (x := x₀)
      (differentiableAt_profile (S.smooth_Ftilde (τ+2)) x₀)
      (differentiableAt_profile (S.smooth_Ftilde (τ+1)) x₀)
      (differentiableAt_profile (S.smooth_Ftilde τ) x₀)
      (fun y => S.recur_Ftilde τ y hτ)
    exact hcomb
  have hslash : ∀ (τ : ℂ) (x : E n), 0 < τ.im →
      (fun τ (_ : E n) => radialDeriv 1 (S.F τ) x₀
        - (2*(Real.pi:ℂ)*Complex.I*τ*(rate m.1 : ℂ)) * dirichletTerm m.1 τ) τ x
        + slashFactor n τ * (fun τ (_ : E n) => radialDeriv 1 (S.Ftilde τ) x₀) (-1/τ) x = 0 := by
    intro τ x hτ
    have hfe : (fun y : E n => S.F τ y + slashFactor n τ * S.Ftilde (-1/τ) y)
        = fun y => Work.Core.gaussianFun n τ y := by
      funext y; rw [S.functional_equation τ y hτ]
    have hdFt : DifferentiableAt ℝ (fun r : ℝ => S.Ftilde (-1/τ) (realIncl (n:=n) r)) ‖x₀‖ :=
      differentiableAt_profile (S.smooth_Ftilde (-1/τ)) x₀
    have hg : radialDeriv 1 (fun y : E n => slashFactor n τ * S.Ftilde (-1/τ) y) x₀
        = slashFactor n τ * radialDeriv 1 (S.Ftilde (-1/τ)) x₀ :=
      radialDeriv_one_const_mul (slashFactor n τ) hdFt
    have h1 : radialDeriv 1 (S.F τ) x₀ + slashFactor n τ * radialDeriv 1 (S.Ftilde (-1/τ)) x₀
        = (2*(Real.pi:ℂ)*Complex.I*τ*(rate m.1 : ℂ)) * dirichletTerm m.1 τ := by
      rw [← hg, ← radialDeriv_one_add (differentiableAt_profile (S.smooth_F τ) x₀)
        (hdFt.const_mul (slashFactor n τ)), hfe]
      exact radialDeriv_gaussianFun_samplePoint τ m.1
    show (radialDeriv 1 (S.F τ) x₀ - (2*(Real.pi:ℂ)*Complex.I*τ*(rate m.1 : ℂ)) * dirichletTerm m.1 τ)
      + slashFactor n τ * radialDeriv 1 (S.Ftilde (-1/τ)) x₀ = 0
    linear_combination h1
  -- the radial-derivative expansions in the `dirichletExpansion` normal form
  have hDFdir : ∀ τ : ℂ, 0 < τ.im → radialDeriv 1 (S.F τ) x₀ = dirichletExpansion k₀
      (fun m : Set.Ici k₀ => radialDeriv 1 (⇑(basis (m, 0)).1) x₀)
      (fun m : Set.Ici k₀ => (rate m.1 : ℂ) * radialDeriv 1 (⇑(basis (m, 2)).1) x₀) τ := by
    intro τ hτ
    rw [hDF 1 τ x₀ hτ]
    rfl
  have hDFtdir : ∀ τ : ℂ, 0 < τ.im → radialDeriv 1 (S.Ftilde τ) x₀ = dirichletExpansion k₀
      (fun m : Set.Ici k₀ => radialDeriv 1 (⇑(basis (m, 1)).1) x₀)
      (fun m : Set.Ici k₀ => (rate m.1 : ℂ) * radialDeriv 1 (⇑(basis (m, 3)).1) x₀) τ := by
    intro τ hτ
    rw [hDFt 1 τ x₀ hτ]
    rfl
  -- the two derivative pairs of Section 8 lie in `𝒫`
  have hInPD : Work.Kernels.InP (fun τ : ℍ => radialDeriv 1 (S.F (τ : ℂ)) x₀) :=
    InP_radialDeriv_F_at (k₀ := k₀) (S := S) (basis := basis) (x₀ := x₀)
      (C₀ := C1) (N₀ := N1) (C₂ := C1) (N₂ := N1) hC1
      (fun m => hder 0 m) hC1 (fun m => hder 2 m)
      hDFdir
  have hInPDt : Work.Kernels.InP (fun τ : ℍ => radialDeriv 1 (S.Ftilde (τ : ℂ)) x₀) :=
    InP_radialDeriv_Ftilde_at (k₀ := k₀) (S := S) (basis := basis) (x₀ := x₀)
      (C₁ := C1) (N₁ := N1) (C₃ := C1) (N₃ := N1) hC1
      (fun m => hder 1 m) hC1 (fun m => hder 3 m)
      hDFtdir
  have hInPDsub : Work.Kernels.InP (fun τ : ℍ => radialDeriv 1 (S.F (τ : ℂ)) x₀
      - (2*(Real.pi:ℂ)*Complex.I*(τ : ℂ)*(rate m.1 : ℂ)) * dirichletTerm m.1 (τ : ℂ)) :=
    hInPD.sub (InP_two_pi_I_tau_mul_dirichletTerm m (rate m.1))
  have hres := hR (fun τ (_ : E n) => radialDeriv 1 (S.F τ) x₀
        - (2*(Real.pi:ℂ)*Complex.I*τ*(rate m.1 : ℂ)) * dirichletTerm m.1 τ)
      (fun τ (_ : E n) => radialDeriv 1 (S.Ftilde τ) x₀)
      (fun _ => hInPDsub) (fun _ => hInPDt) hr1 hr2 hslash hdecD hdecDt
  refine ⟨fun τ hτ => ?_, fun τ hτ => ?_⟩
  · exact sub_eq_zero.mp (hres τ 0 hτ).1
  · exact (hres τ 0 hτ).2

/-- **The value normalisations of Section 8 from the paper-faithful uniqueness lemma.** -/
theorem Section8ValueDataGen_of_rigidityP {n : ℕ} [NeZero n] {k₀ : ℕ} {c : ℝ}
    (hk : 1 ≤ k₀) (hc : (k₀ : ℝ) - 1 = c) (hR : Work.Rigidity.HomogeneousRigidityP n c)
    (S : FunctionalEquationSolution n) (basis : SampleIdx k₀ → RSch n)
    (hExp : ExpansionDataGen n k₀ S basis) :
    Section8ValueDataGen n k₀ S basis := by
  rw [← hc] at hR
  refine ⟨fun m τ hτ => (value_data_at_P hk hR S basis hExp m).1 τ hτ,
    fun m τ hτ => (value_data_at_P hk hR S basis hExp m).2 τ hτ,
    fun m τ hτ => (deriv_data_at_P hk hR S basis hExp m).1 τ hτ,
    fun m τ hτ => (deriv_data_at_P hk hR S basis hExp m).2 τ hτ⟩

end

end Work.Section8P


end Work.CKFinal.Shadow
