/-
# `𝒫`-membership of the Section 8 difference pairs

**Why this file exists.**  Section 8 of CKMRV deduces the Kronecker-delta pattern of the
interpolation basis from the uniqueness lemma `lem:noPsolutions`.  The paper-faithful form
of that lemma, `Work.Rigidity.HomogeneousRigidityP n c`
(`Submission/Work/Rigidity/ModerateGrowth.lean`), carries the moderate-growth hypothesis
`g(τ,·), g̃(τ,·) ∈ 𝒫` (`Work.Kernels.InP`) which the `InP`-free variant drops (and which,
as `Submission/Work/Rigidity/Counterexample.lean` shows, cannot be dropped).

The pairs to which Section 8 applies the lemma are differences of the generating functions
from their Fourier expansions:

* `τ ↦ F(τ,√(2m)) − e^{2πimτ}` and `τ ↦ F̃(τ,√(2m))`,
* `τ ↦ D F(τ,√(2m)) − 2πi√(2m)τ e^{2πimτ}` and `τ ↦ D F̃(τ,√(2m))`,
* `τ ↦ F(τ,x) − 𝓕_x F̃(τ,x)` and `τ ↦ F̃(τ,x) − 𝓕_x F(τ,x)`.

Every one of these is a Dirichlet series of the shape `A(τ) + 2πiτ·B(τ)` with
polynomially bounded coefficients, so `Work.Rigidity.InP_of_dirichletExpansion` gives
membership in `𝒫`.  This file packages that shape and the four discharges needed by the
Section 8 arguments.

## Main definitions

* `Work.Section8P.dirichletExpansion k₀ a b` : the shape `A + 2πiτ·B` of the paper's
  generating functions, with `A = Σ aₙ e^{2πinτ}` and `B = Σ bₙ e^{2πinτ}`.

## Main results

* `Work.Section8P.InP_dirichletExpansion` : `dirichletExpansion k₀ a b ∈ 𝒫` when
  `‖a n‖, ‖b n‖` grow at most polynomially.
* `Work.Section8P.InP_of_eq_dirichletExpansion` : transfer along an equality on `ℍ`.
* `Work.Section8P.InP_of_eq_dirichletExpansion_sub` : the same, minus a `𝒫` correction
  (the single Dirichlet term which is normalised away).
* `Work.Section8P.rate_bound_of` : multiplication by `rate m = √(2m)` costs one power.
* `Work.Section8P.InP_fourierExpansionGen`, `…TildeGen` : the crossed Fourier expansions of
  Section 8 lie in `𝒫`.
-/
import Mathlib
import Submission.Work.Rigidity.All
import Submission.Work.FunctionalEquations.All
import Submission.Work.Kernels.All

namespace Work.Section8P

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Work.FunctionalEquations
open Filter Topology
open scoped FourierTransform SchwartzMap UpperHalfPlane

noncomputable section

/-! ## The shape `A + 2πiτ·B` of the generating functions -/

/-- The shape `A(τ) + 2πiτ·B(τ)` of the paper's generating functions, where
`A = Σ_{n ≥ k₀} aₙ e^{2πinτ}` and `B = Σ_{n ≥ k₀} bₙ e^{2πinτ}` are Dirichlet series with
coefficients indexed from `k₀`. -/
def dirichletExpansion (k₀ : ℕ) (a b : Set.Ici k₀ → ℂ) (τ : ℂ) : ℂ :=
  (∑' n : Set.Ici k₀, a n * dirichletTerm n.1 τ)
    + (2 * (Real.pi : ℂ) * Complex.I * τ)
        * ∑' n : Set.Ici k₀, b n * dirichletTerm n.1 τ

/-- `dirichletExpansion` agrees with the definition of the crossed Fourier expansion
`𝓕_x F` of Section 8, coefficient family by coefficient family. -/
lemma fourierExpansionGen_eq_dirichletExpansion {n : ℕ} [NeZero n] (k₀ : ℕ)
    (basis : SampleIdx k₀ → RSch n) (τ : ℂ) (x : E n) :
    fourierExpansionGen k₀ basis τ x
      = dirichletExpansion k₀
          (fun m : Set.Ici k₀ =>
            (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 0)).1) x)
          (fun m : Set.Ici k₀ =>
            (rate m.1 : ℂ) * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 2)).1) x)
          τ := rfl

/-- `dirichletExpansion` agrees with the definition of the crossed Fourier expansion
`𝓕_x F̃` of Section 8. -/
lemma fourierExpansionTildeGen_eq_dirichletExpansion {n : ℕ} [NeZero n] (k₀ : ℕ)
    (basis : SampleIdx k₀ → RSch n) (τ : ℂ) (x : E n) :
    fourierExpansionTildeGen k₀ basis τ x
      = dirichletExpansion k₀
          (fun m : Set.Ici k₀ =>
            (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 1)).1) x)
          (fun m : Set.Ici k₀ =>
            (rate m.1 : ℂ) * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 3)).1) x)
          τ := rfl

/-! ## Two elementary bound manipulations -/

/-- Two polynomial bounds give a common one. -/
lemma polyLe_max {k₀ : ℕ} {c : Set.Ici k₀ → ℂ} {C C' : ℝ} {N N' : ℕ} (hC : 0 ≤ C)
    (hC' : 0 ≤ C') (h : ∀ n : Set.Ici k₀, ‖c n‖ ≤ C * ((n.1 : ℝ) + 1) ^ N) :
    ∀ n : Set.Ici k₀, ‖c n‖ ≤ (C + C') * ((n.1 : ℝ) + 1) ^ (max N N') := by
  intro n
  have h1 : (1 : ℝ) ≤ (n.1 : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n.1 : ℝ) := Nat.cast_nonneg _
    linarith
  have hp : ((n.1 : ℝ) + 1) ^ N ≤ ((n.1 : ℝ) + 1) ^ (max N N') :=
    pow_le_pow_right₀ h1 (le_max_left N N')
  calc ‖c n‖ ≤ C * ((n.1 : ℝ) + 1) ^ N := h n
    _ ≤ (C + C') * ((n.1 : ℝ) + 1) ^ (max N N') := by
        refine le_trans (mul_le_mul_of_nonneg_left hp hC) ?_
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC') (by positivity)

/-- Multiplying a polynomially bounded family by `rate m = √(2m)` costs one power. -/
lemma rate_bound_of {k₀ : ℕ} {c : Set.Ici k₀ → ℂ} {C : ℝ} {N : ℕ} (_hC : 0 ≤ C)
    (h : ∀ m : Set.Ici k₀, ‖c m‖ ≤ C * ((m.1 : ℝ) + 1) ^ N) :
    ∀ m : Set.Ici k₀, ‖(rate m.1 : ℂ) * c m‖ ≤ C * ((m.1 : ℝ) + 1) ^ (N + 1) := by
  intro m
  have hm0 : (0 : ℝ) ≤ (m.1 : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (m.1 : ℝ) := Nat.cast_nonneg _
    linarith
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (rate_nonneg m.1)]
  calc rate m.1 * ‖c m‖ ≤ ((m.1 : ℝ) + 1) * (C * ((m.1 : ℝ) + 1) ^ N) :=
        mul_le_mul (rate_le_add_one m.1) (h m) (norm_nonneg _) hm0
    _ = C * ((m.1 : ℝ) + 1) ^ (N + 1) := by rw [pow_succ]; ring

/-! ## `𝒫` for the Dirichlet expansion shape -/

/-- **`𝒫` for a Dirichlet expansion with polynomially bounded coefficients.** -/
theorem InP_dirichletExpansion {k₀ : ℕ} {a b : Set.Ici k₀ → ℂ} {Ca Cb : ℝ} {Na Nb : ℕ}
    (hCa : 0 ≤ Ca) (ha : ∀ n : Set.Ici k₀, ‖a n‖ ≤ Ca * ((n.1 : ℝ) + 1) ^ Na)
    (hCb : 0 ≤ Cb) (hb : ∀ n : Set.Ici k₀, ‖b n‖ ≤ Cb * ((n.1 : ℝ) + 1) ^ Nb) :
    Work.Kernels.InP (fun τ : ℍ => dirichletExpansion k₀ a b (τ : ℂ)) := by
  have h1 : ∀ n : Set.Ici k₀, ‖a n‖ ≤ (Ca + Cb) * ((n.1 : ℝ) + 1) ^ (max Na Nb) :=
    polyLe_max hCa hCb ha
  have h2 : ∀ n : Set.Ici k₀, ‖b n‖ ≤ (Ca + Cb) * ((n.1 : ℝ) + 1) ^ (max Na Nb) := by
    intro n
    simpa only [add_comm, Nat.max_comm] using
      polyLe_max (C := Cb) (C' := Ca) (N := Nb) (N' := Na) hCb hCa hb n
  exact Work.Rigidity.InP_of_dirichletExpansion k₀ a b (add_nonneg hCa hCb) h1 h2

/-- Membership in `𝒫` transfers along an equality on the upper half plane. -/
theorem InP_of_eq_dirichletExpansion {k₀ : ℕ} {a b : Set.Ici k₀ → ℂ} {Ca Cb : ℝ}
    {Na Nb : ℕ} (hCa : 0 ≤ Ca)
    (ha : ∀ n : Set.Ici k₀, ‖a n‖ ≤ Ca * ((n.1 : ℝ) + 1) ^ Na) (hCb : 0 ≤ Cb)
    (hb : ∀ n : Set.Ici k₀, ‖b n‖ ≤ Cb * ((n.1 : ℝ) + 1) ^ Nb) {f : ℂ → ℂ}
    (hf : ∀ τ : ℂ, 0 < τ.im → f τ = dirichletExpansion k₀ a b τ) :
    Work.Kernels.InP (fun τ : ℍ => f (τ : ℂ)) := by
  have h := InP_dirichletExpansion (k₀ := k₀) (a := a) (b := b) hCa ha hCb hb
  have heq : (fun τ : ℍ => f (τ : ℂ)) = fun τ : ℍ => dirichletExpansion k₀ a b (τ : ℂ) :=
    funext fun τ => hf (τ : ℂ) τ.im_pos
  rw [heq]
  exact h

/-- Membership in `𝒫` for a Dirichlet expansion minus a `𝒫` correction. -/
theorem InP_of_eq_dirichletExpansion_sub {k₀ : ℕ} {a b : Set.Ici k₀ → ℂ} {Ca Cb : ℝ}
    {Na Nb : ℕ} (hCa : 0 ≤ Ca)
    (ha : ∀ n : Set.Ici k₀, ‖a n‖ ≤ Ca * ((n.1 : ℝ) + 1) ^ Na) (hCb : 0 ≤ Cb)
    (hb : ∀ n : Set.Ici k₀, ‖b n‖ ≤ Cb * ((n.1 : ℝ) + 1) ^ Nb) {f P : ℂ → ℂ}
    (hP : Work.Kernels.InP (fun τ : ℍ => P (τ : ℂ)))
    (hf : ∀ τ : ℂ, 0 < τ.im → f τ = dirichletExpansion k₀ a b τ - P τ) :
    Work.Kernels.InP (fun τ : ℍ => f (τ : ℂ)) := by
  have h := InP_dirichletExpansion (k₀ := k₀) (a := a) (b := b) hCa ha hCb hb
  have h' : Work.Kernels.InP
      (fun τ : ℍ => dirichletExpansion k₀ a b (τ : ℂ) - P (τ : ℂ)) := h.sub hP
  have heq : (fun τ : ℍ => f (τ : ℂ))
      = fun τ : ℍ => dirichletExpansion k₀ a b (τ : ℂ) - P (τ : ℂ) :=
    funext fun τ => hf (τ : ℂ) τ.im_pos
  rw [heq]
  exact h'

/-! ## The elementary `𝒫` members used as corrections -/

/-- The upper half plane variable is in `𝒫`. -/
lemma InP_coe : Work.Kernels.InP (fun τ : ℍ => (τ : ℂ)) := by
  refine ⟨UpperHalfPlane.mdifferentiable_coe, ?_⟩
  refine ⟨1, 1, 1, by norm_num, by norm_num, by norm_num, fun τ _ => ?_⟩
  rw [Real.rpow_one, Real.rpow_one, one_mul]
  exact le_add_of_nonneg_left (Work.Kernels.inv_im_nonneg τ)

/-- A single Dirichlet term lies in `𝒫`. -/
theorem InP_dirichletTerm {k₀ : ℕ} (m : Set.Ici k₀) :
    Work.Kernels.InP (fun τ : ℍ => dirichletTerm m.1 (τ : ℂ)) := by
  have hb0 : ∀ n : Set.Ici k₀, ‖(0 : ℂ)‖ ≤ (0 : ℝ) * ((n.1 : ℝ) + 1) ^ (0 : ℕ) := by
    intro n; simp
  have ha : ∀ n : Set.Ici k₀,
      ‖(if n = m then (1 : ℂ) else 0)‖ ≤ (1 : ℝ) * ((n.1 : ℝ) + 1) ^ (0 : ℕ) := by
    intro n
    by_cases h : n = m <;> simp [h]
  have h := InP_dirichletExpansion (k₀ := k₀)
    (a := fun n : Set.Ici k₀ => if n = m then (1 : ℂ) else 0) (b := fun _ => 0)
    (by norm_num) ha (by norm_num) hb0
  have hgoal : (fun τ : ℍ => dirichletExpansion k₀
      (fun n : Set.Ici k₀ => if n = m then (1 : ℂ) else 0) (fun _ => 0) (τ : ℂ))
      = fun τ : ℍ => dirichletTerm m.1 (τ : ℂ) := by
    funext τ
    have h1 : (∑' n : Set.Ici k₀, (if n = m then (1 : ℂ) else 0) * dirichletTerm n.1 (τ : ℂ))
        = dirichletTerm m.1 (τ : ℂ) := by
      rw [tsum_eq_single m]
      · simp
      · intro b hb
        rw [if_neg hb, zero_mul]
    have h2 : (∑' n : Set.Ici k₀, (0 : ℂ) * dirichletTerm n.1 (τ : ℂ)) = 0 := by simp
    simp only [dirichletExpansion, h1, h2, mul_zero, add_zero]
  rw [← hgoal]
  exact h

/-- `2πiτ·c·e^{2πimτ}` lies in `𝒫`. -/
theorem InP_two_pi_I_tau_mul_dirichletTerm {k₀ : ℕ} (m : Set.Ici k₀) (c : ℂ) :
    Work.Kernels.InP (fun τ : ℍ =>
      (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) * c) * dirichletTerm m.1 (τ : ℂ)) := by
  have hτ : Work.Kernels.InP (fun τ : ℍ => (2 * (Real.pi : ℂ) * Complex.I) * (τ : ℂ)) :=
    InP_coe.const_mul (2 * (Real.pi : ℂ) * Complex.I)
  have he : Work.Kernels.InP (fun τ : ℍ => c * dirichletTerm m.1 (τ : ℂ)) :=
    (InP_dirichletTerm m).const_mul c
  have h : Work.Kernels.InP (fun τ : ℍ =>
      (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)) * (c * dirichletTerm m.1 (τ : ℂ))) :=
    hτ.mul he
  have heq : (fun τ : ℍ =>
        (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)) * (c * dirichletTerm m.1 (τ : ℂ)))
      = fun τ : ℍ =>
        (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) * c) * dirichletTerm m.1 (τ : ℂ) :=
    funext fun τ => by ring
  rw [← heq]
  exact h

/-! ## The four expansions of Section 8 lie in `𝒫` -/

/-- The expansion of `F` at a point, and hence `τ ↦ F(τ,x₀)`, lies in `𝒫`. -/
theorem InP_F_at {n : ℕ} [NeZero n] {k₀ : ℕ} {S : FunctionalEquationSolution n}
    {basis : SampleIdx k₀ → RSch n} {x₀ : E n} {C₀ : ℝ} {N₀ : ℕ} {C₂ : ℝ} {N₂ : ℕ}
    (hC₀ : 0 ≤ C₀)
    (h₀ : ∀ m : Set.Ici k₀, ‖(basis (m, 0)).1 x₀‖ ≤ C₀ * ((m.1 : ℝ) + 1) ^ N₀)
    (hC₂ : 0 ≤ C₂)
    (h₂ : ∀ m : Set.Ici k₀, ‖(basis (m, 2)).1 x₀‖ ≤ C₂ * ((m.1 : ℝ) + 1) ^ N₂)
    (hF : ∀ τ : ℂ, 0 < τ.im → S.F τ x₀ = dirichletExpansion k₀
      (fun m : Set.Ici k₀ => (basis (m, 0)).1 x₀)
      (fun m : Set.Ici k₀ => (rate m.1 : ℂ) * (basis (m, 2)).1 x₀) τ) :
    Work.Kernels.InP (fun τ : ℍ => S.F (τ : ℂ) x₀) :=
  InP_of_eq_dirichletExpansion (k₀ := k₀)
    (a := fun m : Set.Ici k₀ => (basis (m, 0)).1 x₀)
    (b := fun m : Set.Ici k₀ => (rate m.1 : ℂ) * (basis (m, 2)).1 x₀)
    hC₀ h₀ hC₂ (fun m => rate_bound_of hC₂ h₂ m) (f := fun τ => S.F τ x₀) hF

/-- The expansion of `F̃` at a point, and hence `τ ↦ F̃(τ,x₀)`, lies in `𝒫`. -/
theorem InP_Ftilde_at {n : ℕ} [NeZero n] {k₀ : ℕ} {S : FunctionalEquationSolution n}
    {basis : SampleIdx k₀ → RSch n} {x₀ : E n} {C₁ : ℝ} {N₁ : ℕ} {C₃ : ℝ} {N₃ : ℕ}
    (hC₁ : 0 ≤ C₁)
    (h₁ : ∀ m : Set.Ici k₀, ‖(basis (m, 1)).1 x₀‖ ≤ C₁ * ((m.1 : ℝ) + 1) ^ N₁)
    (hC₃ : 0 ≤ C₃)
    (h₃ : ∀ m : Set.Ici k₀, ‖(basis (m, 3)).1 x₀‖ ≤ C₃ * ((m.1 : ℝ) + 1) ^ N₃)
    (hFt : ∀ τ : ℂ, 0 < τ.im → S.Ftilde τ x₀ = dirichletExpansion k₀
      (fun m : Set.Ici k₀ => (basis (m, 1)).1 x₀)
      (fun m : Set.Ici k₀ => (rate m.1 : ℂ) * (basis (m, 3)).1 x₀) τ) :
    Work.Kernels.InP (fun τ : ℍ => S.Ftilde (τ : ℂ) x₀) :=
  InP_of_eq_dirichletExpansion (k₀ := k₀)
    (a := fun m : Set.Ici k₀ => (basis (m, 1)).1 x₀)
    (b := fun m : Set.Ici k₀ => (rate m.1 : ℂ) * (basis (m, 3)).1 x₀)
    hC₁ h₁ hC₃ (fun m => rate_bound_of hC₃ h₃ m) (f := fun τ => S.Ftilde τ x₀) hFt

/-- The radial derivative of the expansion of `F` at a point lies in `𝒫`. -/
theorem InP_radialDeriv_F_at {n : ℕ} [NeZero n] {k₀ : ℕ} {S : FunctionalEquationSolution n}
    {basis : SampleIdx k₀ → RSch n} {x₀ : E n} {C₀ : ℝ} {N₀ : ℕ} {C₂ : ℝ} {N₂ : ℕ}
    (hC₀ : 0 ≤ C₀)
    (h₀ : ∀ m : Set.Ici k₀, ‖radialDeriv 1 (⇑(basis (m, 0)).1) x₀‖ ≤ C₀ * ((m.1 : ℝ) + 1) ^ N₀)
    (hC₂ : 0 ≤ C₂)
    (h₂ : ∀ m : Set.Ici k₀, ‖radialDeriv 1 (⇑(basis (m, 2)).1) x₀‖ ≤ C₂ * ((m.1 : ℝ) + 1) ^ N₂)
    (hDF : ∀ τ : ℂ, 0 < τ.im → radialDeriv 1 (S.F τ) x₀ = dirichletExpansion k₀
      (fun m : Set.Ici k₀ => radialDeriv 1 (⇑(basis (m, 0)).1) x₀)
      (fun m : Set.Ici k₀ => (rate m.1 : ℂ) * radialDeriv 1 (⇑(basis (m, 2)).1) x₀) τ) :
    Work.Kernels.InP (fun τ : ℍ => radialDeriv 1 (S.F (τ : ℂ)) x₀) :=
  InP_of_eq_dirichletExpansion (k₀ := k₀)
    (a := fun m : Set.Ici k₀ => radialDeriv 1 (⇑(basis (m, 0)).1) x₀)
    (b := fun m : Set.Ici k₀ => (rate m.1 : ℂ) * radialDeriv 1 (⇑(basis (m, 2)).1) x₀)
    hC₀ h₀ hC₂ (fun m => rate_bound_of hC₂ h₂ m) (f := fun τ => radialDeriv 1 (S.F τ) x₀) hDF

/-- The radial derivative of the expansion of `F̃` at a point lies in `𝒫`. -/
theorem InP_radialDeriv_Ftilde_at {n : ℕ} [NeZero n] {k₀ : ℕ} {S : FunctionalEquationSolution n}
    {basis : SampleIdx k₀ → RSch n} {x₀ : E n} {C₁ : ℝ} {N₁ : ℕ} {C₃ : ℝ} {N₃ : ℕ}
    (hC₁ : 0 ≤ C₁)
    (h₁ : ∀ m : Set.Ici k₀, ‖radialDeriv 1 (⇑(basis (m, 1)).1) x₀‖ ≤ C₁ * ((m.1 : ℝ) + 1) ^ N₁)
    (hC₃ : 0 ≤ C₃)
    (h₃ : ∀ m : Set.Ici k₀, ‖radialDeriv 1 (⇑(basis (m, 3)).1) x₀‖ ≤ C₃ * ((m.1 : ℝ) + 1) ^ N₃)
    (hDFt : ∀ τ : ℂ, 0 < τ.im → radialDeriv 1 (S.Ftilde τ) x₀ = dirichletExpansion k₀
      (fun m : Set.Ici k₀ => radialDeriv 1 (⇑(basis (m, 1)).1) x₀)
      (fun m : Set.Ici k₀ => (rate m.1 : ℂ) * radialDeriv 1 (⇑(basis (m, 3)).1) x₀) τ) :
    Work.Kernels.InP (fun τ : ℍ => radialDeriv 1 (S.Ftilde (τ : ℂ)) x₀) :=
  InP_of_eq_dirichletExpansion (k₀ := k₀)
    (a := fun m : Set.Ici k₀ => radialDeriv 1 (⇑(basis (m, 1)).1) x₀)
    (b := fun m : Set.Ici k₀ => (rate m.1 : ℂ) * radialDeriv 1 (⇑(basis (m, 3)).1) x₀)
    hC₁ h₁ hC₃ (fun m => rate_bound_of hC₃ h₃ m) (f := fun τ => radialDeriv 1 (S.Ftilde τ) x₀) hDFt

/-! ## The crossed Fourier expansions of Section 8 lie in `𝒫` -/

/-- The crossed Fourier expansion `𝓕_x F` of Section 8 lies in `𝒫`. -/
theorem InP_fourierExpansionGen {n : ℕ} [NeZero n] {k₀ : ℕ} (basis : SampleIdx k₀ → RSch n)
    {C₀ : ℝ} {N₀ : ℕ} {C₂ : ℝ} {N₂ : ℕ} (hC₀ : 0 ≤ C₀)
    (h₀ : ∀ (m : Set.Ici k₀) (x : E n),
      ‖(FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 0)).1) x‖
        ≤ C₀ * ((m.1 : ℝ) + 1) ^ N₀)
    (hC₂ : 0 ≤ C₂)
    (h₂ : ∀ (m : Set.Ici k₀) (x : E n),
      ‖(FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 2)).1) x‖
        ≤ C₂ * ((m.1 : ℝ) + 1) ^ N₂) :
    ∀ x : E n, Work.Kernels.InP (fun τ : ℍ => fourierExpansionGen k₀ basis (τ : ℂ) x) := by
  intro x
  have h := InP_dirichletExpansion (k₀ := k₀)
    (a := fun m : Set.Ici k₀ => (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 0)).1) x)
    (b := fun m : Set.Ici k₀ =>
      (rate m.1 : ℂ) * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 2)).1) x)
    hC₀ (fun m => h₀ m x) hC₂ (fun m => rate_bound_of hC₂ (fun m' => h₂ m' x) m)
  have heq : (fun τ : ℍ => dirichletExpansion k₀
        (fun m : Set.Ici k₀ => (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 0)).1) x)
        (fun m : Set.Ici k₀ =>
          (rate m.1 : ℂ) * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 2)).1) x) (τ : ℂ))
      = fun τ : ℍ => fourierExpansionGen k₀ basis (τ : ℂ) x := by
    funext τ
    rw [fourierExpansionGen_eq_dirichletExpansion]
  rw [← heq]
  exact h

/-- The crossed Fourier expansion `𝓕_x F̃` of Section 8 lies in `𝒫`. -/
theorem InP_fourierExpansionTildeGen {n : ℕ} [NeZero n] {k₀ : ℕ}
    (basis : SampleIdx k₀ → RSch n)
    {C₁ : ℝ} {N₁ : ℕ} {C₃ : ℝ} {N₃ : ℕ} (hC₁ : 0 ≤ C₁)
    (h₁ : ∀ (m : Set.Ici k₀) (x : E n),
      ‖(FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 1)).1) x‖
        ≤ C₁ * ((m.1 : ℝ) + 1) ^ N₁)
    (hC₃ : 0 ≤ C₃)
    (h₃ : ∀ (m : Set.Ici k₀) (x : E n),
      ‖(FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 3)).1) x‖
        ≤ C₃ * ((m.1 : ℝ) + 1) ^ N₃) :
    ∀ x : E n, Work.Kernels.InP (fun τ : ℍ => fourierExpansionTildeGen k₀ basis (τ : ℂ) x) := by
  intro x
  have h := InP_dirichletExpansion (k₀ := k₀)
    (a := fun m : Set.Ici k₀ => (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 1)).1) x)
    (b := fun m : Set.Ici k₀ =>
      (rate m.1 : ℂ) * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 3)).1) x)
    hC₁ (fun m => h₁ m x) hC₃ (fun m => rate_bound_of hC₃ (fun m' => h₃ m' x) m)
  have heq : (fun τ : ℍ => dirichletExpansion k₀
        (fun m : Set.Ici k₀ => (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 1)).1) x)
        (fun m : Set.Ici k₀ =>
          (rate m.1 : ℂ) * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 3)).1) x) (τ : ℂ))
      = fun τ : ℍ => fourierExpansionTildeGen k₀ basis (τ : ℂ) x := by
    funext τ
    rw [fourierExpansionTildeGen_eq_dirichletExpansion]
  rw [← heq]
  exact h

end

end Work.Section8P
