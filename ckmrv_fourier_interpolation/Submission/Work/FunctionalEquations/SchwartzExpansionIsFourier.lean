import Mathlib
import Submission.Work.FunctionalEquations.Gap
import Submission.Work.FunctionalEquations.FourierExpansion
import Submission.Work.FunctionalEquations.FourierSeriesHelpers
import Submission.Work.FunctionalEquations.SeminormGrowthOfRadialGrowth
import Submission.Work.FunctionalEquations.SummableExpansionTerms
import Submission.Work.FunctionalEquations.SummableSchwartzBasisSmul
import Submission.Work.Summability.exists_schwartz_tsum

/-!
# `x ↦ F(τ,x)` is Schwartz with Fourier transform the Dirichlet series

This file proves `Work.FunctionalEquations.SchwartzExpansionIsFourier`: from the Fourier
expansions of Steps 1--2 of the paper (`Work.FE.ExpansionDataGen`, whose growth half gives
that the coefficient functions have polynomially growing radial seminorms), for every `τ`
in the upper half plane the functions `x ↦ S.F τ x` and `x ↦ S.Ftilde τ x` are Schwartz
functions whose Fourier transforms are the Dirichlet series `Work.FE.fourierExpansionGen`
and `Work.FE.fourierExpansionTildeGen`.

The proof is the interchange of the (Schwartz-space) sum with the Fourier transform:

* `Work.FunctionalEquations.SummableSchwartzBasisSmul` shows that the seminorm-summability
  needed for `Work.Summability.schwartzSum` holds, because `‖e^{2πimτ}‖ = e^{-2πm Im τ}`
  decays geometrically in `m` while the coefficients grow at most polynomially;
* the sum in the Schwartz space is the series itself by
  `Work.Summability.schwartzSum_apply`;
* the Fourier transform is continuous linear, so it commutes with the sum, and evaluating
  the transform of the sum gives the series of the transforms of the coefficients.

The extra hypothesis of `SchwartzExpansionIsFourier` (polynomial growth of the Schwartz
seminorms of the Fourier transforms of the basis functions) is not needed for this
conclusion; it is carried along because the downstream argument uses it elsewhere.
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

/-- The norm of the complex number `rate m` is `rate m`. -/
private lemma norm_rate_cast (m : ℕ) : ‖(rate m : ℂ)‖ = rate m := by
  have h : ‖(rate m : ℂ)‖ = |rate m| := by simp
  rw [h]
  exact abs_of_nonneg (Real.sqrt_nonneg _)

/-- **The Fourier transform of the expansion series.**  Under the hypotheses
`Work.FE.ExpansionDataGen` (the two Fourier expansions of Steps 1--2 of the paper with
radial Schwartz coefficients whose radial seminorms grow at most polynomially), for every
`τ` with `Im τ > 0` the functions `x ↦ S.F τ x` and `x ↦ S.Ftilde τ x` are Schwartz
functions whose Fourier transforms are the corresponding Dirichlet series
`Work.FE.fourierExpansionGen` / `Work.FE.fourierExpansionTildeGen`. -/
private lemma fourierCLM_expansion {n : ℕ} [NeZero n] {k₀ : ℕ}
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
    rw [norm_mul, dirichletTerm_norm_eq, norm_rate_cast, one_mul, pow_one]
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

/-- **Solution of the functional equations, seen through its expansion, is Schwartz with
the Fourier transform the Dirichlet series of the Fourier transforms.**  Under the
hypotheses `Work.FE.ExpansionDataGen` (the Fourier expansions of Steps 1--2 of the paper
with radial Schwartz coefficients whose radial seminorms grow at most polynomially) and the
polynomial growth of the Schwartz seminorms of the Fourier transforms of the basis
functions, for every `τ` in the upper half plane the functions `x ↦ S.F τ x` and
`x ↦ S.Ftilde τ x` are Schwartz functions whose Fourier transforms are
`Work.FE.fourierExpansionGen` and `Work.FE.fourierExpansionTildeGen`. -/
theorem SchwartzExpansionIsFourier {n : ℕ} [NeZero n] {k₀ : ℕ}
    (S : Work.FE.FunctionalEquationSolution n) (basis : Work.Core.SampleIdx k₀ → Work.Core.RSch n)
    (hExp : Work.FE.ExpansionDataGen n k₀ S basis)
    (hb : ∀ k l : ℕ, ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ (m : Set.Ici k₀) (j : Fin 4),
        (SchwartzMap.seminorm ℂ k l)
            (FourierTransform.fourierCLM ℂ (SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) (basis (m, j)).1)
          ≤ C * ((m.1 : ℝ) + 1) ^ N) :
    ∀ (τ : ℂ), 0 < τ.im →
      (∃ Fs : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
          (∀ x : EuclideanSpace ℝ (Fin n), Fs x = S.F τ x) ∧
          (∀ x : EuclideanSpace ℝ (Fin n),
            (FourierTransform.fourierCLM ℂ (SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) Fs) x
            = Work.FE.fourierExpansionGen k₀ basis τ x)) ∧
      (∃ Fs : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
          (∀ x : EuclideanSpace ℝ (Fin n), Fs x = S.Ftilde τ x) ∧
          (∀ x : EuclideanSpace ℝ (Fin n),
            (FourierTransform.fourierCLM ℂ (SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) Fs) x
            = Work.FE.fourierExpansionTildeGen k₀ basis τ x)) := by
  -- `hb` (the polynomial growth of the Schwartz seminorms of the Fourier transforms of
  -- the basis functions) is not needed for this conclusion.
  have _ := hb
  intro τ hτ
  obtain ⟨G, Gt, hG, hGt, hGF, hGFt⟩ := fourierCLM_expansion S basis hExp hτ
  exact ⟨⟨G, hG, hGF⟩, ⟨Gt, hGt, hGFt⟩⟩

end

end Work.FunctionalEquations
