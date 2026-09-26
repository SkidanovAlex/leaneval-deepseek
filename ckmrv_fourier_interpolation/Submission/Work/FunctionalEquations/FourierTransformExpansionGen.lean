import Mathlib
import Submission.Work.FunctionalEquations.Gap
import Submission.Work.FunctionalEquations.FourierExpansion
import Submission.Work.Summability.exists_schwartz_tsum
import Submission.Work.FunctionalEquations.SummableSchwartzBasisSmul
import Submission.Work.FunctionalEquations.SummableExpansionTerms

/-!
# The Fourier transform of the expansion series

This file proves `Work.FunctionalEquations.FourierTransformExpansionGen`: given a solution
`S` of the functional equations together with an expansion basis `basis` (the hypotheses
`Work.FE.ExpansionDataGen`: the two Fourier expansions of Steps 1--2 of the paper with
radial Schwartz coefficients whose radial seminorms grow at most polynomially), the
functions `x ↦ S.F τ x` and `x ↦ S.Ftilde τ x` (for `Im τ > 0`) are Schwartz functions whose
Fourier transforms are the corresponding Dirichlet series
`Work.FE.fourierExpansionGen` / `Work.FE.fourierExpansionTildeGen`.

The proof is the interchange of the (Schwartz-space) sum with the Fourier transform:

* `Work.FunctionalEquations.SummableSchwartzBasisSmul` shows that the seminorm-summability
  needed for `Work.Summability.schwartzSum` holds, since
  `‖e^{2 π i m τ}‖ = e^{-2 π m Im τ}` decays geometrically in `m` while the coefficients
  grow at most polynomially;
* the sum in the Schwartz space is the series itself by `Work.Summability.schwartzSum_apply`;
* the Fourier transform is continuous linear, so it commutes with the sum, and evaluating
  the transform of the sum is the series of the transforms of the coefficients.
-/

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

noncomputable section

/-- The Dirichlet term `e^{2 π i m τ}` has norm the `m`-th power of the geometric ratio
`e^{-2 π Im τ}`. -/
private lemma dirichletTerm_norm_eq (m : ℕ) (τ : ℂ) :
    ‖dirichletTerm m τ‖ = Real.exp (-(2 * Real.pi * τ.im)) ^ m := by
  rw [normDirichletTermAux]
  have h : -(2 * Real.pi * (m : ℝ) * τ.im) = (m : ℝ) * (-(2 * Real.pi * τ.im)) := by ring
  rw [h, Real.exp_nat_mul]

theorem FourierTransformExpansionGen {n : ℕ} [NeZero n] {k₀ : ℕ}
    (S : FunctionalEquationSolution n) (basis : SampleIdx k₀ → RSch n)
    (hExp : ExpansionDataGen n k₀ S basis)
    {τ : ℂ} (hτ : 0 < τ.im) :
    ∃ G Gt : 𝓢(E n, ℂ),
      (∀ x, G x = S.F τ x) ∧
      (∀ x, Gt x = S.Ftilde τ x) ∧
      (∀ y, (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) G) y = fourierExpansionGen k₀ basis τ y) ∧
      (∀ y, (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) Gt) y
        = fourierExpansionTildeGen k₀ basis τ y) := by
  obtain ⟨hF, hFt, _, _, hgrow⟩ := hExp
  have ht0 : 0 ≤ Real.exp (-(2 * Real.pi * τ.im)) := (Real.exp_pos _).le
  have ht1 : Real.exp (-(2 * Real.pi * τ.im)) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos, hτ]
  -- The two coefficient bounds feeding `SummableSchwartzBasisSmul`.
  have hct1 : ∀ m : Set.Ici k₀, ‖dirichletTerm m.1 τ‖
      ≤ 1 * ((m.1 : ℝ) + 1) ^ 0 * Real.exp (-(2 * Real.pi * τ.im)) ^ (m.1) :=
    fun m => by rw [dirichletTerm_norm_eq]; simp
  have hct2 : ∀ m : Set.Ici k₀, ‖(rate m.1 : ℂ) * dirichletTerm m.1 τ‖
      ≤ 1 * ((m.1 : ℝ) + 1) ^ 1 * Real.exp (-(2 * Real.pi * τ.im)) ^ (m.1) := by
    intro m
    rw [norm_mul, dirichletTerm_norm_eq]
    have hr : ‖(rate m.1 : ℂ)‖ = rate m.1 := by
      rw [show ‖(rate m.1 : ℂ)‖ = |rate m.1| by simp]
      exact abs_of_nonneg (Real.sqrt_nonneg _)
    rw [hr, one_mul, pow_one]
    exact mul_le_mul_of_nonneg_right (rate_le_add_one m.1) (pow_nonneg ht0 _)
  -- Seminorm summability of the four families of series terms.
  have hvF : ∀ k l : ℕ, Summable fun m : Set.Ici k₀ =>
      (SchwartzMap.seminorm ℂ k l) ((dirichletTerm m.1 τ) • (basis (m, 0)).1) :=
    SummableSchwartzBasisSmul basis hgrow (c := fun m => dirichletTerm m.1 τ) (K := 1) (N := 0)
      (t := Real.exp (-(2 * Real.pi * τ.im))) zero_le_one ht0 ht1 hct1 0
  have hvFt : ∀ k l : ℕ, Summable fun m : Set.Ici k₀ =>
      (SchwartzMap.seminorm ℂ k l) ((dirichletTerm m.1 τ) • (basis (m, 1)).1) :=
    SummableSchwartzBasisSmul basis hgrow (c := fun m => dirichletTerm m.1 τ) (K := 1) (N := 0)
      (t := Real.exp (-(2 * Real.pi * τ.im))) zero_le_one ht0 ht1 hct1 1
  have hvF2 : ∀ k l : ℕ, Summable fun m : Set.Ici k₀ =>
      (SchwartzMap.seminorm ℂ k l) (((rate m.1 : ℂ) * dirichletTerm m.1 τ) • (basis (m, 2)).1) :=
    SummableSchwartzBasisSmul basis hgrow (c := fun m => (rate m.1 : ℂ) * dirichletTerm m.1 τ)
      (K := 1) (N := 1) (t := Real.exp (-(2 * Real.pi * τ.im))) zero_le_one ht0 ht1 hct2 2
  have hvFt2 : ∀ k l : ℕ, Summable fun m : Set.Ici k₀ =>
      (SchwartzMap.seminorm ℂ k l) (((rate m.1 : ℂ) * dirichletTerm m.1 τ) • (basis (m, 3)).1) :=
    SummableSchwartzBasisSmul basis hgrow (c := fun m => (rate m.1 : ℂ) * dirichletTerm m.1 τ)
      (K := 1) (N := 1) (t := Real.exp (-(2 * Real.pi * τ.im))) zero_le_one ht0 ht1 hct2 3
  -- The four sums in the Schwartz space.
  set c : ℂ := 2 * (Real.pi : ℂ) * Complex.I * τ with hc
  set SF : 𝓢(E n, ℂ) := Work.Summability.schwartzSum
    (fun m : Set.Ici k₀ => (dirichletTerm m.1 τ) • (basis (m, 0)).1) hvF with hSF
  set SFt : 𝓢(E n, ℂ) := Work.Summability.schwartzSum
    (fun m : Set.Ici k₀ => (dirichletTerm m.1 τ) • (basis (m, 1)).1) hvFt with hSFt
  set Sg : 𝓢(E n, ℂ) := Work.Summability.schwartzSum
    (fun m : Set.Ici k₀ => ((rate m.1 : ℂ) * dirichletTerm m.1 τ) • (basis (m, 2)).1) hvF2 with hSg
  set Sgt : 𝓢(E n, ℂ) := Work.Summability.schwartzSum
    (fun m : Set.Ici k₀ => ((rate m.1 : ℂ) * dirichletTerm m.1 τ) • (basis (m, 3)).1) hvFt2 with hSgt
  refine ⟨SF + c • Sg, SFt + c • Sgt, ?_, ?_, ?_, ?_⟩
  · -- the value of the first sum
    intro x
    have e1 : (∑' m : Set.Ici k₀, ((dirichletTerm m.1 τ) • (basis (m, 0)).1) x)
        = ∑' m : Set.Ici k₀, (basis (m, 0)).1 x * dirichletTerm m.1 τ :=
      tsum_congr fun m => by simp only [smul_apply, smul_eq_mul]; ring
    have e2 : (∑' m : Set.Ici k₀, (((rate m.1 : ℂ) * dirichletTerm m.1 τ) • (basis (m, 2)).1) x)
        = ∑' m : Set.Ici k₀, (rate m.1 : ℂ) * (basis (m, 2)).1 x * dirichletTerm m.1 τ :=
      tsum_congr fun m => by simp only [smul_apply, smul_eq_mul]; ring
    have hGx : (SF + c • Sg) x
        = (∑' m : Set.Ici k₀, (basis (m, 0)).1 x * dirichletTerm m.1 τ)
          + c * ∑' m : Set.Ici k₀, (rate m.1 : ℂ) * (basis (m, 2)).1 x * dirichletTerm m.1 τ := by
      rw [hSF, hSg, add_apply, smul_apply, smul_eq_mul, Work.Summability.schwartzSum_apply,
        Work.Summability.schwartzSum_apply, e1, e2]
    rw [hGx, hF τ x hτ, hc]
  · -- the value of the second sum
    intro x
    have e1 : (∑' m : Set.Ici k₀, ((dirichletTerm m.1 τ) • (basis (m, 1)).1) x)
        = ∑' m : Set.Ici k₀, (basis (m, 1)).1 x * dirichletTerm m.1 τ :=
      tsum_congr fun m => by simp only [smul_apply, smul_eq_mul]; ring
    have e2 : (∑' m : Set.Ici k₀, (((rate m.1 : ℂ) * dirichletTerm m.1 τ) • (basis (m, 3)).1) x)
        = ∑' m : Set.Ici k₀, (rate m.1 : ℂ) * (basis (m, 3)).1 x * dirichletTerm m.1 τ :=
      tsum_congr fun m => by simp only [smul_apply, smul_eq_mul]; ring
    have hGx : (SFt + c • Sgt) x
        = (∑' m : Set.Ici k₀, (basis (m, 1)).1 x * dirichletTerm m.1 τ)
          + c * ∑' m : Set.Ici k₀, (rate m.1 : ℂ) * (basis (m, 3)).1 x * dirichletTerm m.1 τ := by
      rw [hSFt, hSgt, add_apply, smul_apply, smul_eq_mul, Work.Summability.schwartzSum_apply,
        Work.Summability.schwartzSum_apply, e1, e2]
    rw [hGx, hFt τ x hτ, hc]
  · -- the Fourier transform of the first sum
    intro y
    have h1 : (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) SF) y
        = ∑' m : Set.Ici k₀,
            (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 0)).1) y
              * dirichletTerm m.1 τ := by
      have hsum : HasSum (fun m : Set.Ici k₀ => (dirichletTerm m.1 τ) • (basis (m, 0)).1) SF := by
        rw [hSF]
        exact Work.Summability.hasSum_schwartzSum _ hvF
      have hev := (hsum.mapL (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)))).mapL
        (Work.Sampling.evalAtCLM y)
      have heq : (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) SF) y
          = ∑' m : Set.Ici k₀,
              (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ))
                ((dirichletTerm m.1 τ) • (basis (m, 0)).1)) y := by
        simpa only [Work.Sampling.evalAtCLM_apply] using hev.tsum_eq.symm
      rw [heq]
      refine tsum_congr fun m => ?_
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring
    have h2 : (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) Sg) y
        = ∑' m : Set.Ici k₀, (rate m.1 : ℂ)
            * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 2)).1) y
            * dirichletTerm m.1 τ := by
      have hsum : HasSum (fun m : Set.Ici k₀ =>
          ((rate m.1 : ℂ) * dirichletTerm m.1 τ) • (basis (m, 2)).1) Sg := by
        rw [hSg]
        exact Work.Summability.hasSum_schwartzSum _ hvF2
      have hev := (hsum.mapL (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)))).mapL
        (Work.Sampling.evalAtCLM y)
      have heq : (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) Sg) y
          = ∑' m : Set.Ici k₀,
              (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ))
                (((rate m.1 : ℂ) * dirichletTerm m.1 τ) • (basis (m, 2)).1)) y := by
        simpa only [Work.Sampling.evalAtCLM_apply] using hev.tsum_eq.symm
      rw [heq]
      refine tsum_congr fun m => ?_
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring
    have hmain : (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (SF + c • Sg)) y
        = (∑' m : Set.Ici k₀,
            (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 0)).1) y
              * dirichletTerm m.1 τ)
          + c * ∑' m : Set.Ici k₀, (rate m.1 : ℂ)
              * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 2)).1) y
              * dirichletTerm m.1 τ := by
      rw [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, h1, h2]
    rw [hmain, hc]
    rfl
  · -- the Fourier transform of the second sum
    intro y
    have h1 : (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) SFt) y
        = ∑' m : Set.Ici k₀,
            (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 1)).1) y
              * dirichletTerm m.1 τ := by
      have hsum : HasSum (fun m : Set.Ici k₀ => (dirichletTerm m.1 τ) • (basis (m, 1)).1) SFt := by
        rw [hSFt]
        exact Work.Summability.hasSum_schwartzSum _ hvFt
      have hev := (hsum.mapL (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)))).mapL
        (Work.Sampling.evalAtCLM y)
      have heq : (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) SFt) y
          = ∑' m : Set.Ici k₀,
              (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ))
                ((dirichletTerm m.1 τ) • (basis (m, 1)).1)) y := by
        simpa only [Work.Sampling.evalAtCLM_apply] using hev.tsum_eq.symm
      rw [heq]
      refine tsum_congr fun m => ?_
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring
    have h2 : (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) Sgt) y
        = ∑' m : Set.Ici k₀, (rate m.1 : ℂ)
            * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 3)).1) y
            * dirichletTerm m.1 τ := by
      have hsum : HasSum (fun m : Set.Ici k₀ =>
          ((rate m.1 : ℂ) * dirichletTerm m.1 τ) • (basis (m, 3)).1) Sgt := by
        rw [hSgt]
        exact Work.Summability.hasSum_schwartzSum _ hvFt2
      have hev := (hsum.mapL (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)))).mapL
        (Work.Sampling.evalAtCLM y)
      have heq : (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) Sgt) y
          = ∑' m : Set.Ici k₀,
              (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ))
                (((rate m.1 : ℂ) * dirichletTerm m.1 τ) • (basis (m, 3)).1)) y := by
        simpa only [Work.Sampling.evalAtCLM_apply] using hev.tsum_eq.symm
      rw [heq]
      refine tsum_congr fun m => ?_
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring
    have hmain : (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (SFt + c • Sgt)) y
        = (∑' m : Set.Ici k₀,
            (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 1)).1) y
              * dirichletTerm m.1 τ)
          + c * ∑' m : Set.Ici k₀, (rate m.1 : ℂ)
              * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 3)).1) y
              * dirichletTerm m.1 τ := by
      rw [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, h1, h2]
    rw [hmain, hc]
    rfl

end

end Work.FunctionalEquations
