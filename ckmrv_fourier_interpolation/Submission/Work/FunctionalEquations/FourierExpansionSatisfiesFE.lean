import Mathlib
import Submission.Work.FunctionalEquations.FourierExpansion
import Submission.Work.FunctionalEquations.Gap
import Submission.Work.FunctionalEquations.SlashFactorMul
import Submission.Work.FunctionalEquations.SummableSchwartzBasisSmul
import Submission.Work.Core.Gaussian
import Submission.Work.Summability.exists_schwartz_tsum

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

noncomputable section

/-!
# The functional equations satisfied by the Fourier expansions

Let `F`, `F̃` be the two generating functions of a solution of the functional equations
of CKMRV Theorem 3.1 and let `basis` be the coefficient family of their Fourier
expansions (`Work.FE.ExpansionDataGen`).  Writing `𝓕_x F` for the Dirichlet series whose
coefficients are the Fourier transforms of the coefficients of `F`
(`Work.FE.fourierExpansionGen`), this file proves that the pair `(𝓕_x F̃, 𝓕_x F)`
satisfies the same three functional equations as `(F, F̃)`:

* the second difference equation `g (τ+2) - 2 g (τ+1) + g τ = 0` in `τ`, for both
  `𝓕_x F` and `𝓕_x F̃` (immediate from the form `A(τ) + 2π i τ B(τ)` with `A`, `B`
  periodic of period `1`);
* the Poisson-type equation

  `𝓕_x F̃(τ) + slashFactor n τ · 𝓕_x F(−1/τ) = gaussianFun n τ`,

  which is the Fourier transform in `x` of the functional equation at `−1/τ`, using
  `slashFactor n τ · slashFactor n (−1/τ) = 1` and the Fourier transform of the Gaussian.
-/

/-! ## The Dirichlet kernel is periodic in `τ` -/

/-- `e^{2π i m (τ+k)} = e^{2π i m τ}` for natural `k`: the Dirichlet kernel has period `1`. -/
private lemma dirichletTerm_add_nat (m k : ℕ) (τ : ℂ) :
    dirichletTerm m (τ + k) = dirichletTerm m τ := by
  simp only [dirichletTerm]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (τ + (k : ℂ))
      = 2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * τ
        + ((m * k : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) from by push_cast; ring]
  rw [Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

/-! ## The shifted Fourier expansions -/

/-- The `k`-shifted Fourier expansion of `F` has the same Dirichlet series. -/
private lemma fourierExpansionGen_add_nat {n : ℕ} [NeZero n] {k₀ : ℕ}
    (basis : SampleIdx k₀ → RSch n) (k : ℕ) (τ : ℂ) (x : E n) :
    fourierExpansionGen k₀ basis (τ + k) x
      = (∑' m : Set.Ici k₀,
            (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 0)).1) x
              * dirichletTerm m.1 τ)
        + (2 * (Real.pi : ℂ) * Complex.I * (τ + k))
          * ∑' m : Set.Ici k₀, (rate m.1 : ℂ)
              * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 2)).1) x
              * dirichletTerm m.1 τ := by
  simp only [fourierExpansionGen]
  rw [show (∑' m : Set.Ici k₀,
          (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 0)).1) x
            * dirichletTerm m.1 (τ + k))
        = (∑' m : Set.Ici k₀,
          (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 0)).1) x
            * dirichletTerm m.1 τ) from
      tsum_congr fun m => by rw [dirichletTerm_add_nat m.1 k τ]]
  rw [show (∑' m : Set.Ici k₀, (rate m.1 : ℂ)
          * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 2)).1) x
          * dirichletTerm m.1 (τ + k))
        = (∑' m : Set.Ici k₀, (rate m.1 : ℂ)
          * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 2)).1) x
          * dirichletTerm m.1 τ) from
      tsum_congr fun m => by rw [dirichletTerm_add_nat m.1 k τ]]

/-- The `k`-shifted Fourier expansion of `F̃` has the same Dirichlet series. -/
private lemma fourierExpansionTildeGen_add_nat {n : ℕ} [NeZero n] {k₀ : ℕ}
    (basis : SampleIdx k₀ → RSch n) (k : ℕ) (τ : ℂ) (x : E n) :
    fourierExpansionTildeGen k₀ basis (τ + k) x
      = (∑' m : Set.Ici k₀,
            (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 1)).1) x
              * dirichletTerm m.1 τ)
        + (2 * (Real.pi : ℂ) * Complex.I * (τ + k))
          * ∑' m : Set.Ici k₀, (rate m.1 : ℂ)
              * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 3)).1) x
              * dirichletTerm m.1 τ := by
  simp only [fourierExpansionTildeGen]
  rw [show (∑' m : Set.Ici k₀,
          (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 1)).1) x
            * dirichletTerm m.1 (τ + k))
        = (∑' m : Set.Ici k₀,
          (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 1)).1) x
            * dirichletTerm m.1 τ) from
      tsum_congr fun m => by rw [dirichletTerm_add_nat m.1 k τ]]
  rw [show (∑' m : Set.Ici k₀, (rate m.1 : ℂ)
          * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 3)).1) x
          * dirichletTerm m.1 (τ + k))
        = (∑' m : Set.Ici k₀, (rate m.1 : ℂ)
          * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 3)).1) x
          * dirichletTerm m.1 τ) from
      tsum_congr fun m => by rw [dirichletTerm_add_nat m.1 k τ]]

/-! ## The Fourier transform of a Dirichlet series of Schwartz functions -/

/-- Pointwise evaluation of a Schwartz function, as a continuous linear functional. -/
private noncomputable def evalCLM {n : ℕ} (y : E n) : 𝓢(E n, ℂ) →L[ℂ] ℂ :=
  (BoundedContinuousFunction.evalCLM ℂ y).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (E n) ℂ)

private lemma evalCLM_apply {n : ℕ} (y : E n) (f : 𝓢(E n, ℂ)) : evalCLM y f = f y := rfl

/-- **The Fourier transform of a Dirichlet series with Schwartz coefficients.**  For a
family `u` of Schwartz functions and scalars `c` whose products with the Dirichlet kernel
have summable Schwartz seminorms, the pointwise series `∑_m c m · u m x · e^{2π i m τ}`
(and the Dirichlet series of the Fourier transforms) is the sum of the seminorm-summable
family in the Schwartz space, and the Fourier transform acts termwise. -/
private lemma schwartzSum_dirichlet {n : ℕ} [NeZero n] {k₀ : ℕ} (τ : ℂ)
    (c : Set.Ici k₀ → ℂ) (u : Set.Ici k₀ → 𝓢(E n, ℂ))
    (hu : ∀ k l : ℕ, Summable fun m : Set.Ici k₀ =>
      (SchwartzMap.seminorm ℂ k l) ((c m * dirichletTerm m.1 τ) • u m)) :
    (∀ x, (Work.Summability.schwartzSum
        (fun m : Set.Ici k₀ => (c m * dirichletTerm m.1 τ) • u m) hu) x
        = ∑' m : Set.Ici k₀, c m * u m x * dirichletTerm m.1 τ) ∧
    (∀ y, (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ))
        (Work.Summability.schwartzSum
          (fun m : Set.Ici k₀ => (c m * dirichletTerm m.1 τ) • u m) hu)) y
        = ∑' m : Set.Ici k₀,
            c m * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (u m)) y
              * dirichletTerm m.1 τ) := by
  constructor
  · intro x
    rw [Work.Summability.schwartzSum_apply]
    exact tsum_congr fun m => by rw [smul_apply, smul_eq_mul]; ring
  · intro y
    have hsum : Summable fun m : Set.Ici k₀ => (c m * dirichletTerm m.1 τ) • u m :=
      Work.Summability.summable_schwartz_of_summable_seminorm _ hu
    have hsch : Work.Summability.schwartzSum
          (fun m : Set.Ici k₀ => (c m * dirichletTerm m.1 τ) • u m) hu
        = ∑' m : Set.Ici k₀, (c m * dirichletTerm m.1 τ) • u m :=
      (Work.Summability.hasSum_schwartzSum _ hu).tsum_eq.symm
    have hmap : (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)))
          (∑' m : Set.Ici k₀, (c m * dirichletTerm m.1 τ) • u m)
        = ∑' m : Set.Ici k₀, (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)))
            ((c m * dirichletTerm m.1 τ) • u m) :=
      ContinuousLinearMap.map_tsum _ hsum
    rw [hsch, hmap]
    have hsum2 : Summable fun m : Set.Ici k₀ =>
        (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)))
          ((c m * dirichletTerm m.1 τ) • u m) :=
      ContinuousLinearMap.summable _ hsum
    have hev : (∑' m : Set.Ici k₀, (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)))
            ((c m * dirichletTerm m.1 τ) • u m)) y
        = ∑' m : Set.Ici k₀, ((FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)))
            ((c m * dirichletTerm m.1 τ) • u m)) y := by
      simpa only [evalCLM_apply] using ContinuousLinearMap.map_tsum (evalCLM y) hsum2
    rw [hev]
    refine tsum_congr fun m => ?_
    rw [ContinuousLinearMap.map_smul]
    simp only [smul_apply, smul_eq_mul]
    ring

/-- **The Fourier transforms of the two generating functions, through their expansions.**
Under `Work.FE.ExpansionDataGen` the function `x ↦ F(τ,x)` has a Schwartz representative
`G` (the sum of the two Dirichlet series in the Schwartz space), and the Fourier transform
of `G` is the Dirichlet series of the Fourier transforms, i.e. `fourierExpansionGen`;
likewise for `F̃` and `fourierExpansionTildeGen`. -/
private theorem fourierTransform_expansion_aux {n : ℕ} [NeZero n] {k₀ : ℕ}
    (S : FunctionalEquationSolution n) (basis : SampleIdx k₀ → RSch n)
    (hExp : ExpansionDataGen n k₀ S basis) {τ : ℂ} (hτ : 0 < τ.im) :
    ∃ G Gt : 𝓢(E n, ℂ),
      (∀ x, G x = S.F τ x) ∧
      (∀ x, Gt x = S.Ftilde τ x) ∧
      (∀ y, (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) G) y = fourierExpansionGen k₀ basis τ y) ∧
      (∀ y, (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) Gt) y
              = fourierExpansionTildeGen k₀ basis τ y) := by
  obtain ⟨hF, hFt, -, -, hG⟩ := hExp
  -- the geometric decay of the Dirichlet kernel
  set t : ℝ := Real.exp (-(2 * Real.pi * τ.im)) with ht
  have ht0 : (0 : ℝ) ≤ t := (Real.exp_pos _).le
  have ht1 : t < 1 := by rw [ht, Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, hτ]
  have hnorm : ∀ m : ℕ, ‖dirichletTerm m τ‖ = t ^ m := by
    intro m
    rw [normDirichletTermAux, ht, ← Real.exp_nat_mul]
    congr 1
    ring
  have hrate : ∀ m : ℕ, ‖(rate m : ℂ)‖ = rate m := by
    intro m
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (Real.sqrt_nonneg _)
  -- summability of the terms of the four series
  have hu0 : ∀ k l : ℕ, Summable fun m : Set.Ici k₀ =>
      (SchwartzMap.seminorm ℂ k l) (((1 : ℂ) * dirichletTerm m.1 τ) • (basis (m, 0)).1) :=
    SummableSchwartzBasisSmul basis hG (c := fun m : Set.Ici k₀ => (1 : ℂ) * dirichletTerm m.1 τ)
      (K := 1) (N := 0) (t := t) zero_le_one ht0 ht1
      (fun m => by rw [norm_mul, norm_one, one_mul, hnorm m.1]; simp) 0
  have hu1 : ∀ k l : ℕ, Summable fun m : Set.Ici k₀ =>
      (SchwartzMap.seminorm ℂ k l) (((1 : ℂ) * dirichletTerm m.1 τ) • (basis (m, 1)).1) :=
    SummableSchwartzBasisSmul basis hG (c := fun m : Set.Ici k₀ => (1 : ℂ) * dirichletTerm m.1 τ)
      (K := 1) (N := 0) (t := t) zero_le_one ht0 ht1
      (fun m => by rw [norm_mul, norm_one, one_mul, hnorm m.1]; simp) 1
  have hu2 : ∀ k l : ℕ, Summable fun m : Set.Ici k₀ =>
      (SchwartzMap.seminorm ℂ k l)
        (((rate m.1 : ℂ) * dirichletTerm m.1 τ) • (basis (m, 2)).1) :=
    SummableSchwartzBasisSmul basis hG
      (c := fun m : Set.Ici k₀ => (rate m.1 : ℂ) * dirichletTerm m.1 τ)
      (K := 1) (N := 1) (t := t) zero_le_one ht0 ht1
      (fun m => by
        rw [norm_mul, hrate m.1, hnorm m.1]
        calc rate m.1 * t ^ (m.1) ≤ ((m.1 : ℝ) + 1) * t ^ (m.1) :=
              mul_le_mul_of_nonneg_right (rate_le_add_one m.1) (pow_nonneg ht0 _)
          _ = 1 * ((m.1 : ℝ) + 1) ^ 1 * t ^ (m.1) := by ring) 2
  have hu3 : ∀ k l : ℕ, Summable fun m : Set.Ici k₀ =>
      (SchwartzMap.seminorm ℂ k l)
        (((rate m.1 : ℂ) * dirichletTerm m.1 τ) • (basis (m, 3)).1) :=
    SummableSchwartzBasisSmul basis hG
      (c := fun m : Set.Ici k₀ => (rate m.1 : ℂ) * dirichletTerm m.1 τ)
      (K := 1) (N := 1) (t := t) zero_le_one ht0 ht1
      (fun m => by
        rw [norm_mul, hrate m.1, hnorm m.1]
        calc rate m.1 * t ^ (m.1) ≤ ((m.1 : ℝ) + 1) * t ^ (m.1) :=
              mul_le_mul_of_nonneg_right (rate_le_add_one m.1) (pow_nonneg ht0 _)
          _ = 1 * ((m.1 : ℝ) + 1) ^ 1 * t ^ (m.1) := by ring) 3
  -- the four summand families and their sums
  let g1 : 𝓢(E n, ℂ) := Work.Summability.schwartzSum
    (fun m : Set.Ici k₀ => ((1 : ℂ) * dirichletTerm m.1 τ) • (basis (m, 0)).1) hu0
  let g2 : 𝓢(E n, ℂ) := Work.Summability.schwartzSum
    (fun m : Set.Ici k₀ => ((rate m.1 : ℂ) * dirichletTerm m.1 τ) • (basis (m, 2)).1) hu2
  let g3 : 𝓢(E n, ℂ) := Work.Summability.schwartzSum
    (fun m : Set.Ici k₀ => ((1 : ℂ) * dirichletTerm m.1 τ) • (basis (m, 1)).1) hu1
  let g4 : 𝓢(E n, ℂ) := Work.Summability.schwartzSum
    (fun m : Set.Ici k₀ => ((rate m.1 : ℂ) * dirichletTerm m.1 τ) • (basis (m, 3)).1) hu3
  have hg1val : ∀ x, g1 x = ∑' m : Set.Ici k₀,
      (basis (m, 0)).1 x * dirichletTerm m.1 τ := by
    intro x
    have h := (schwartzSum_dirichlet τ (fun _ : Set.Ici k₀ => (1 : ℂ))
      (fun m => (basis (m, 0)).1) hu0).1 x
    show (Work.Summability.schwartzSum _ hu0) x = _
    rw [h]
    exact tsum_congr fun m => by ring
  have hg2val : ∀ x, g2 x = ∑' m : Set.Ici k₀,
      (rate m.1 : ℂ) * (basis (m, 2)).1 x * dirichletTerm m.1 τ := by
    intro x
    have h := (schwartzSum_dirichlet τ (fun m : Set.Ici k₀ => (rate m.1 : ℂ))
      (fun m => (basis (m, 2)).1) hu2).1 x
    exact h
  have hg3val : ∀ x, g3 x = ∑' m : Set.Ici k₀,
      (basis (m, 1)).1 x * dirichletTerm m.1 τ := by
    intro x
    have h := (schwartzSum_dirichlet τ (fun _ : Set.Ici k₀ => (1 : ℂ))
      (fun m => (basis (m, 1)).1) hu1).1 x
    show (Work.Summability.schwartzSum _ hu1) x = _
    rw [h]
    exact tsum_congr fun m => by ring
  have hg4val : ∀ x, g4 x = ∑' m : Set.Ici k₀,
      (rate m.1 : ℂ) * (basis (m, 3)).1 x * dirichletTerm m.1 τ := by
    intro x
    have h := (schwartzSum_dirichlet τ (fun m : Set.Ici k₀ => (rate m.1 : ℂ))
      (fun m => (basis (m, 3)).1) hu3).1 x
    exact h
  have hFg1 : ∀ y, (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) g1) y
      = ∑' m : Set.Ici k₀,
          (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 0)).1) y
            * dirichletTerm m.1 τ := by
    intro y
    have h := (schwartzSum_dirichlet τ (fun _ : Set.Ici k₀ => (1 : ℂ))
      (fun m => (basis (m, 0)).1) hu0).2 y
    show (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ))
      (Work.Summability.schwartzSum _ hu0)) y = _
    rw [h]
    exact tsum_congr fun m => by ring
  have hFg2 : ∀ y, (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) g2) y
      = ∑' m : Set.Ici k₀,
          (rate m.1 : ℂ)
            * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 2)).1) y
            * dirichletTerm m.1 τ := by
    intro y
    have h := (schwartzSum_dirichlet τ (fun m : Set.Ici k₀ => (rate m.1 : ℂ))
      (fun m => (basis (m, 2)).1) hu2).2 y
    exact h
  have hFg3 : ∀ y, (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) g3) y
      = ∑' m : Set.Ici k₀,
          (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 1)).1) y
            * dirichletTerm m.1 τ := by
    intro y
    have h := (schwartzSum_dirichlet τ (fun _ : Set.Ici k₀ => (1 : ℂ))
      (fun m => (basis (m, 1)).1) hu1).2 y
    show (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ))
      (Work.Summability.schwartzSum _ hu1)) y = _
    rw [h]
    exact tsum_congr fun m => by ring
  have hFg4 : ∀ y, (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) g4) y
      = ∑' m : Set.Ici k₀,
          (rate m.1 : ℂ)
            * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 3)).1) y
            * dirichletTerm m.1 τ := by
    intro y
    have h := (schwartzSum_dirichlet τ (fun m : Set.Ici k₀ => (rate m.1 : ℂ))
      (fun m => (basis (m, 3)).1) hu3).2 y
    exact h
  refine ⟨g1 + (2 * (Real.pi : ℂ) * Complex.I * τ) • g2,
          g3 + (2 * (Real.pi : ℂ) * Complex.I * τ) • g4, ?_, ?_, ?_, ?_⟩
  · intro x
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [hg1val x, hg2val x, hF τ x hτ]
  · intro x
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [hg3val x, hg4val x, hFt τ x hτ]
  · intro y
    rw [map_add, map_smul]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [hFg1 y, hFg2 y]
    rfl
  · intro y
    rw [map_add, map_smul]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [hFg3 y, hFg4 y]
    rfl

/-! ## The main theorem -/

theorem FourierExpansionSatisfiesFE {n : ℕ} [NeZero n] {k₀ : ℕ}
    (S : FunctionalEquationSolution n) (basis : SampleIdx k₀ → RSch n)
    (hExp : ExpansionDataGen n k₀ S basis) :
    (∀ (τ : ℂ) (x : E n), 0 < τ.im →
      fourierExpansionTildeGen k₀ basis (τ + 2) x
        - 2 * fourierExpansionTildeGen k₀ basis (τ + 1) x
        + fourierExpansionTildeGen k₀ basis τ x = 0) ∧
    (∀ (τ : ℂ) (x : E n), 0 < τ.im →
      fourierExpansionGen k₀ basis (τ + 2) x
        - 2 * fourierExpansionGen k₀ basis (τ + 1) x
        + fourierExpansionGen k₀ basis τ x = 0) ∧
    (∀ (τ : ℂ) (x : E n), 0 < τ.im →
      fourierExpansionTildeGen k₀ basis τ x
        + slashFactor n τ * fourierExpansionGen k₀ basis (-1 / τ) x
        = Work.Core.gaussianFun n τ x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro τ x hτ
    have e2 : (τ + ((2 : ℕ) : ℂ)) = (τ + 2 : ℂ) := by norm_num
    have e1 : (τ + ((1 : ℕ) : ℂ)) = (τ + 1 : ℂ) := by norm_num
    have h2 := fourierExpansionTildeGen_add_nat basis 2 τ x
    have h1 := fourierExpansionTildeGen_add_nat basis 1 τ x
    have h0 : fourierExpansionTildeGen k₀ basis τ x
        = (∑' m : Set.Ici k₀,
              (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 1)).1) x
                * dirichletTerm m.1 τ)
          + (2 * (Real.pi : ℂ) * Complex.I * τ)
            * ∑' m : Set.Ici k₀, (rate m.1 : ℂ)
                * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 3)).1) x
                * dirichletTerm m.1 τ := by
      simpa using fourierExpansionTildeGen_add_nat basis 0 τ x
    rw [← e2, ← e1, h2, h1, h0]
    ring
  · intro τ x hτ
    have e2 : (τ + ((2 : ℕ) : ℂ)) = (τ + 2 : ℂ) := by norm_num
    have e1 : (τ + ((1 : ℕ) : ℂ)) = (τ + 1 : ℂ) := by norm_num
    have h2 := fourierExpansionGen_add_nat basis 2 τ x
    have h1 := fourierExpansionGen_add_nat basis 1 τ x
    have h0 : fourierExpansionGen k₀ basis τ x
        = (∑' m : Set.Ici k₀,
              (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 0)).1) x
                * dirichletTerm m.1 τ)
          + (2 * (Real.pi : ℂ) * Complex.I * τ)
            * ∑' m : Set.Ici k₀, (rate m.1 : ℂ)
                * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 2)).1) x
                * dirichletTerm m.1 τ := by
      simpa using fourierExpansionGen_add_nat basis 0 τ x
    rw [← e2, ← e1, h2, h1, h0]
    ring
  · intro τ x hτ
    have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτ; simp at hτ
    have hτ' : 0 < (-1 / τ).im := by
      have hns : 0 < Complex.normSq τ := Complex.normSq_pos.mpr hτ0
      rw [show -1 / τ = -(1 / τ) from by ring, Complex.neg_im, one_div, Complex.inv_im,
        neg_div, neg_neg]
      exact div_pos hτ hns
    obtain ⟨G, Gt, hGval, hGtval, hFG, hFGt⟩ := fourierTransform_expansion_aux S basis hExp hτ
    obtain ⟨G₂, -, hG₂val, -, hFG₂, -⟩ := fourierTransform_expansion_aux S basis hExp hτ'
    -- the functional equation at `-1/τ`, multiplied by `slashFactor n τ`
    have hFE : ∀ y : E n,
        slashFactor n τ * S.F (-1 / τ) y + S.Ftilde τ y
          = slashFactor n τ * Work.Core.gaussianFun n (-1 / τ) y := by
      intro y
      have h := S.functional_equation (-1 / τ) y hτ'
      rw [show -1 / (-1 / τ) = τ from by field_simp] at h
      have hs := SlashFactorMul (n := n) hτ
      have h2 : slashFactor n τ
            * (S.F (-1 / τ) y + slashFactor n (-1 / τ) * S.Ftilde τ y)
          = slashFactor n τ * S.F (-1 / τ) y + S.Ftilde τ y := by
        rw [mul_add]
        rw [show slashFactor n τ * (slashFactor n (-1 / τ) * S.Ftilde τ y)
              = (slashFactor n τ * slashFactor n (-1 / τ)) * S.Ftilde τ y from by ring]
        rw [hs, one_mul]
      rw [← h2, h]
    -- as an identity of Schwartz functions
    have heq : slashFactor n τ • G₂ + Gt
        = slashFactor n τ • Work.Core.gaussianSchwartz n (-1 / τ) hτ' := by
      ext y
      simp only [add_apply, smul_apply, smul_eq_mul,
        Work.Core.gaussianSchwartz_apply]
      rw [hG₂val y, hGtval y]
      exact hFE y
    have hmap : (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ))
          (slashFactor n τ • G₂ + Gt)) x
        = (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ))
          (slashFactor n τ • Work.Core.gaussianSchwartz n (-1 / τ) hτ')) x := by
      rw [heq]
    have h1 : (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ))
          (slashFactor n τ • G₂ + Gt)) x
        = slashFactor n τ * fourierExpansionGen k₀ basis (-1 / τ) x
          + fourierExpansionTildeGen k₀ basis τ x := by
      rw [map_add, map_smul]
      simp only [add_apply, smul_apply, smul_eq_mul]
      rw [hFG₂ x, hFGt x]
    have h2 : (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ))
          (slashFactor n τ • Work.Core.gaussianSchwartz n (-1 / τ) hτ')) x
        = Work.Core.gaussianFun n τ x := by
      rw [map_smul]
      simp only [smul_apply, smul_eq_mul]
      rw [Work.Core.fourier_gaussianSchwartz n (-1 / τ) hτ' x]
      rw [show -1 / (-1 / τ) = τ from by field_simp]
      rw [← mul_assoc,
        show slashFactor n τ * (Complex.I / (-1 / τ)) ^ ((n : ℂ) / 2) = 1 from by
          simpa only [slashFactor] using SlashFactorMul (n := n) hτ,
        one_mul]
    have hval : slashFactor n τ * fourierExpansionGen k₀ basis (-1 / τ) x
          + fourierExpansionTildeGen k₀ basis τ x = Work.Core.gaussianFun n τ x := by
      rw [← h1, hmap, h2]
    rw [show fourierExpansionTildeGen k₀ basis τ x
          + slashFactor n τ * fourierExpansionGen k₀ basis (-1 / τ) x
        = slashFactor n τ * fourierExpansionGen k₀ basis (-1 / τ) x
          + fourierExpansionTildeGen k₀ basis τ x from by ring]
    exact hval

end

end Work.FunctionalEquations
