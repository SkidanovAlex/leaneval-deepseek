import Mathlib
import Submission.Work.FunctionalEquations.Gap
import Submission.Work.FunctionalEquations.FourierExpansion
import Submission.Work.FunctionalEquations.FourierSeriesHelpers

/-!
# Holomorphy of the Fourier expansions `𝓕_x F`, `𝓕_x F̃` of Section 8

`Work.FE.fourierExpansionGen` (resp. `fourierExpansionTildeGen`) evaluates the expansion of
`𝓕_x F` (resp. `𝓕_x F̃`) at a point `x`, as the sum of two Dirichlet series

  `A(τ) + (2 π i τ) · B(τ)`,  `A(τ) = ∑_m c_m e^{2 π i m τ}`,  `B(τ) = ∑_m d_m e^{2 π i m τ}`,

whose coefficients `c_m`, `d_m` are the Fourier transforms of the radial Schwartz coefficient
functions, evaluated at `x`.  Hypothesis `hb` of the statement says that the Schwartz
seminorms of those coefficient functions grow at most polynomially in the index `m`; since
the evaluation at `x` is bounded by the `(0,0)` seminorm, both families `c`, `d` are
polynomially bounded.

The content of this file is therefore the elementary but fundamental fact that a Dirichlet
series with polynomially bounded coefficients is holomorphic on the upper half plane: the
terms are entire functions and, on every half plane `Im τ > y₀` with `y₀ > 0`, they are
dominated by the summable sequence `C (m+1)^N e^{-2 π m y₀}`, so
`Complex.differentiableOn_tsum_of_summable_norm` applies.  This is the `x`-differentiated
form of the statement that `𝓕_x F` and `𝓕_x F̃` solve the same functional equations as
`F` and `F̃` (paper Section 8).

## Main results

* `Work.FunctionalEquations.differentiableOn_tsum_dirichletTerm`: a Dirichlet series with
  polynomially bounded coefficients is holomorphic on the upper half plane.
* `Work.FunctionalEquations.differentiableOn_tsum_dirichletTerm_rate`: the same with the
  additional rate factor `√(2m)`.
* `Work.FunctionalEquations.HolomorphicFourierExpansion`: the two Fourier expansions are
  holomorphic in `τ` on the upper half plane.
-/

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

noncomputable section

/-- **Holomorphy of a Dirichlet series with polynomially bounded coefficients.**  If
`‖c m‖ ≤ C (m+1)^N` for all `m ≥ k₀`, then `τ ↦ ∑_m c_m e^{2 π i m τ}` is differentiable
on the upper half plane.

The proof is a dominated convergence argument at the level of functions: fix a point `τ`
of the upper half plane and let `y₀ = Im τ / 2 > 0`; on the open half plane
`U = {w | y₀ < w.im}` each term `w ↦ c_m e^{2 π i m w}` is entire and bounded by the
`m`-th term of the summable sequence `‖c m‖ e^{-2 π m y₀}`. -/
lemma differentiableOn_tsum_dirichletTerm {k₀ : ℕ} (c : Set.Ici k₀ → ℂ)
    (hc : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ m : Set.Ici k₀, ‖c m‖ ≤ C * ((m.1 : ℝ) + 1) ^ N) :
    DifferentiableOn ℂ (fun τ : ℂ => ∑' m : Set.Ici k₀, c m * dirichletTerm m.1 τ)
      {τ : ℂ | 0 < τ.im} := by
  obtain ⟨C, N, hC, hc⟩ := hc
  intro τ hτ
  have hτpos : 0 < τ.im := hτ
  set d : ℝ := τ.im / 2 with hd
  have hdpos : 0 < d := by rw [hd]; linarith
  set U : Set ℂ := {w : ℂ | d < w.im} with hU
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hτU : τ ∈ U := by rw [hU]; simp only [Set.mem_ofPred_eq]; linarith
  have hsummable : Summable fun m : Set.Ici k₀ =>
      ‖c m‖ * Real.exp (-(2 * Real.pi * d * (m.1 : ℝ))) :=
    SummableRealMulExpNeg (N := N) (C := C) hC (fun m => norm_nonneg _) hc hdpos
  have hterm : ∀ m : Set.Ici k₀,
      DifferentiableOn ℂ (fun w : ℂ => c m * dirichletTerm m.1 w) U := by
    intro m
    refine ((differentiable_const (c m)).mul ?_).differentiableOn
    show Differentiable ℂ
      (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℂ) * w))
    fun_prop
  have hbound : ∀ (m : Set.Ici k₀) (w : ℂ), w ∈ U →
      ‖c m * dirichletTerm m.1 w‖ ≤ ‖c m‖ * Real.exp (-(2 * Real.pi * d * (m.1 : ℝ))) := by
    intro m w hw
    have hw' : d < w.im := hw
    rw [norm_mul, norm_dirichletTerm]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have hm : (0:ℝ) ≤ (m.1 : ℝ) := Nat.cast_nonneg _
    have h1 : 2 * Real.pi * d ≤ 2 * Real.pi * w.im := by nlinarith [Real.pi_pos]
    have h2 := mul_le_mul_of_nonneg_right h1 hm
    linarith
  have hdiff := Complex.differentiableOn_tsum_of_summable_norm hsummable hterm hUopen hbound
  exact (hdiff.differentiableAt (hUopen.mem_nhds hτU)).differentiableWithinAt

/-- **Holomorphy of a Dirichlet series with the rate factor `√(2m)`.**  If
`‖c m‖ ≤ C (m+1)^N` for all `m ≥ k₀`, then `τ ↦ ∑_m √(2m) c_m e^{2 π i m τ}` is
differentiable on the upper half plane.  This is the previous lemma applied to the
coefficients `√(2m) c_m`, which satisfy `‖√(2m) c_m‖ ≤ (m+1) · C (m+1)^N` by
`rate_le`. -/
lemma differentiableOn_tsum_dirichletTerm_rate {k₀ : ℕ} (c : Set.Ici k₀ → ℂ)
    (hc : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ m : Set.Ici k₀, ‖c m‖ ≤ C * ((m.1 : ℝ) + 1) ^ N) :
    DifferentiableOn ℂ
      (fun τ : ℂ => ∑' m : Set.Ici k₀, (rate m.1 : ℂ) * c m * dirichletTerm m.1 τ)
      {τ : ℂ | 0 < τ.im} := by
  obtain ⟨C, N, hC, hc⟩ := hc
  refine differentiableOn_tsum_dirichletTerm (fun m => (rate m.1 : ℂ) * c m)
    ⟨C, N + 1, hC, fun m => ?_⟩
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (rate_nonneg _)]
  calc rate m.1 * ‖c m‖ ≤ ((m.1 : ℝ) + 1) * (C * ((m.1 : ℝ) + 1) ^ N) :=
        mul_le_mul (rate_le m.1) (hc m) (norm_nonneg _) (by positivity)
    _ = C * ((m.1 : ℝ) + 1) ^ (N + 1) := by rw [pow_succ]; ring

/-- **The Fourier expansions of `F` and `F̃` are holomorphic in `τ` on the upper half
plane.**  The coefficients are the Fourier transforms of the radial Schwartz coefficient
functions, evaluated at `x`; by hypothesis their Schwartz seminorms grow at most
polynomially in the index, and the evaluation at `x` is bounded by the `(0,0)` seminorm,
so `differentiableOn_tsum_dirichletTerm` applies to each of the four Dirichlet series
appearing in `fourierExpansionGen` and `fourierExpansionTildeGen`. -/
theorem HolomorphicFourierExpansion {n : ℕ} [NeZero n] {k₀ : ℕ} (hk : 1 ≤ k₀)
    (basis : Work.Core.SampleIdx k₀ → Work.Core.RSch n)
    (hb : ∀ k l : ℕ, ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ (m : Set.Ici k₀) (j : Fin 4),
        (SchwartzMap.seminorm ℂ k l)
            (FourierTransform.fourierCLM ℂ (SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) (basis (m, j)).1)
          ≤ C * ((m.1 : ℝ) + 1) ^ N)
    (x : EuclideanSpace ℝ (Fin n)) :
    DifferentiableOn ℂ (fun τ : ℂ => Work.FE.fourierExpansionGen k₀ basis τ x) {τ : ℂ | 0 < τ.im} ∧
    DifferentiableOn ℂ (fun τ : ℂ => Work.FE.fourierExpansionTildeGen k₀ basis τ x)
      {τ : ℂ | 0 < τ.im} := by
  have _ : (1 : ℕ) ≤ k₀ := hk
  -- The evaluation at `x` of a Schwartz function is bounded by its `(0,0)` seminorm,
  -- so the hypothesis on the seminorms gives a polynomial bound on the coefficients.
  have hbnd : ∀ j : Fin 4, ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ m : Set.Ici k₀,
      ‖(FourierTransform.fourierCLM ℂ (SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ)
          (basis (m, j)).1) x‖ ≤ C * ((m.1 : ℝ) + 1) ^ N := by
    intro j
    obtain ⟨C, N, hC, hCN⟩ := hb 0 0
    refine ⟨C, N, hC, fun m => ?_⟩
    have h1 : ‖x‖ ^ 0 * ‖(FourierTransform.fourierCLM ℂ
        (SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) (basis (m, j)).1) x‖ ≤
        (SchwartzMap.seminorm ℂ 0 0)
          (FourierTransform.fourierCLM ℂ (SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ)
            (basis (m, j)).1) :=
      SchwartzMap.norm_pow_mul_le_seminorm ℂ _ 0 x
    have h2 : (SchwartzMap.seminorm ℂ 0 0)
        (FourierTransform.fourierCLM ℂ (SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ)
          (basis (m, j)).1) ≤ C * ((m.1 : ℝ) + 1) ^ N := hCN m j
    simpa using h1.trans h2
  -- The linear factor `2 π i τ` is entire.
  have hlin : DifferentiableOn ℂ (fun τ : ℂ => 2 * (Real.pi : ℂ) * Complex.I * τ)
      {τ : ℂ | 0 < τ.im} :=
    ((differentiable_const (2 * (Real.pi : ℂ) * Complex.I)).mul differentiable_id).differentiableOn
  constructor
  · have h0 := differentiableOn_tsum_dirichletTerm (k₀ := k₀)
      (fun m : Set.Ici k₀ => (FourierTransform.fourierCLM ℂ
        (SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) (basis (m, 0)).1) x) (hbnd 0)
    have h2 := differentiableOn_tsum_dirichletTerm_rate (k₀ := k₀)
      (fun m : Set.Ici k₀ => (FourierTransform.fourierCLM ℂ
        (SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) (basis (m, 2)).1) x) (hbnd 2)
    change DifferentiableOn ℂ (fun τ : ℂ =>
        (∑' m : Set.Ici k₀, (FourierTransform.fourierCLM ℂ
          (SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) (basis (m, 0)).1) x
            * dirichletTerm m.1 τ) +
        (2 * (Real.pi : ℂ) * Complex.I * τ) *
          (∑' m : Set.Ici k₀, (rate m.1 : ℂ) * (FourierTransform.fourierCLM ℂ
            (SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) (basis (m, 2)).1) x
              * dirichletTerm m.1 τ))
      {τ : ℂ | 0 < τ.im}
    exact h0.add (hlin.mul h2)
  · have h1 := differentiableOn_tsum_dirichletTerm (k₀ := k₀)
      (fun m : Set.Ici k₀ => (FourierTransform.fourierCLM ℂ
        (SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) (basis (m, 1)).1) x) (hbnd 1)
    have h3 := differentiableOn_tsum_dirichletTerm_rate (k₀ := k₀)
      (fun m : Set.Ici k₀ => (FourierTransform.fourierCLM ℂ
        (SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) (basis (m, 3)).1) x) (hbnd 3)
    change DifferentiableOn ℂ (fun τ : ℂ =>
        (∑' m : Set.Ici k₀, (FourierTransform.fourierCLM ℂ
          (SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) (basis (m, 1)).1) x
            * dirichletTerm m.1 τ) +
        (2 * (Real.pi : ℂ) * Complex.I * τ) *
          (∑' m : Set.Ici k₀, (rate m.1 : ℂ) * (FourierTransform.fourierCLM ℂ
            (SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) (basis (m, 3)).1) x
              * dirichletTerm m.1 τ))
      {τ : ℂ | 0 < τ.im}
    exact h1.add (hlin.mul h3)

end

end Work.FunctionalEquations
