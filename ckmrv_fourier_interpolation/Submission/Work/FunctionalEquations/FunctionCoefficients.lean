import Mathlib
import Submission.Work.FunctionalEquations.Coefficients
import Submission.Work.FunctionalEquations.ExpansionFromFunctionalEquations
import Submission.Work.RadialSpace.RadialSeminormEquiv
import Submission.Work.RadialSpace.EvenRadial
import Submission.Work.RadialSpace.RSch
import Submission.Work.FunctionalEquations.KernelSchwartz.kernel_isSchwartz
import Submission.Work.FunctionalEquations.KernelSchwartz.growth_combination

/-!
# The coefficient functions of CKMRV Theorem 3.1 are radial Schwartz functions

This file proves `Work.FunctionalEquations.FunctionCoefficients`: for every solution
`S` of the functional equations (hypotheses (i)--(v) of CKMRV Theorem 3.1), the four
coefficient families `aCoeff S`, `aTildeCoeff S`, `bCoeff S`, `bTildeCoeff S` defined by
the contour integrals of `Coefficients.lean` are radial Schwartz functions, and their
radial seminorms grow at most polynomially in the index.

The paper's argument (proof of Theorem 3.1) is: the coefficients equal the contour
integrals along *any* horizontal line `Im = y > 0`; differentiating under the integral
sign in `x` and applying hypothesis (iii) bounds all radial seminorms; taking
`y = 1/(m+1)` makes the exponential factor `e^{2π m y}` bounded and turns the bound into
a polynomial one in `m`.

The analytic core is isolated in the delegated lemmas
`Work.FunctionalEquations.KernelSchwartz.kernel_isSchwartz` (abstract version of the
argument for a general kernel) and `Work.FunctionalEquations.KernelSchwartz.growth_combination`
(the growth hypothesis for the two combinations `Φ - τ(Φ(τ+1) - Φ τ)` and
`Φ(τ+1) - Φ τ`); this file supplies the four concrete kernels and the bookkeeping.
-/

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

noncomputable section

variable {n : ℕ} [NeZero n]

/-- Bundled regularity of the generating function `F` or `F̃`. -/
structure FData (n : ℕ) [NeZero n] where
  /-- The generating function. -/
  Φ : ℂ → E n → ℂ
  /-- Holomorphy in `τ` on the upper half plane. -/
  holo : ∀ x : E n, DifferentiableOn ℂ (fun τ : ℂ => Φ τ x) {τ : ℂ | 0 < τ.im}
  /-- Smoothness in `x`. -/
  smooth : ∀ τ : ℂ, ContDiff ℝ ⊤ (Φ τ)
  /-- Radiality in `x`. -/
  radial : ∀ τ : ℂ, Radial (Φ τ)
  /-- The radial-derivative growth bounds (iii). -/
  growth : ∀ k ℓ : ℕ, ∃ α β γ δ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ 0 ≤ δ ∧
      ∀ (τ : ℂ) (x : E n), 0 < τ.im →
        ‖x‖ ^ k * ‖radialDeriv ℓ (Φ τ) x‖ ≤ α * τ.im ^ (-β) + γ * ‖τ‖ ^ δ

/-- The data of `F`. -/
def FData.ofF (S : FunctionalEquationSolution n) : FData n where
  Φ := S.F
  holo := S.holomorphic_F
  smooth := S.smooth_F
  radial := S.radial_F
  growth := S.growth_F

/-- The data of `F̃`. -/
def FData.ofFtilde (S : FunctionalEquationSolution n) : FData n where
  Φ := S.Ftilde
  holo := S.holomorphic_Ftilde
  smooth := S.smooth_Ftilde
  radial := S.radial_Ftilde
  growth := S.growth_Ftilde

/-- The `a`-kernel attached to a generating function: `Φ τ x - τ(Φ(τ+1)x - Φ τ x)`. -/
def aKernelGen (D : FData n) (τ : ℂ) (x : E n) : ℂ :=
  D.Φ τ x - τ * (D.Φ (τ + 1) x - D.Φ τ x)

/-- The `b`-kernel attached to a generating function: `Φ(τ+1)x - Φ τ x`. -/
def bKernelGen (D : FData n) (τ : ℂ) (x : E n) : ℂ :=
  D.Φ (τ + 1) x - D.Φ τ x

/-- The scalar multiplying the `b`-coefficients: `(2πi√(2m))⁻¹`. -/
def cB (m : Set.Ici (1 : ℕ)) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I * (rate m.1 : ℂ))⁻¹

lemma cB_norm_le_one (m : Set.Ici (1 : ℕ)) : ‖cB m‖ ≤ 1 := by
  have hpos : (0 : ℝ) < rate m.1 := by
    rw [rate]
    apply Real.sqrt_pos.mpr
    have : (1 : ℝ) ≤ (m.1 : ℝ) := by exact_mod_cast m.2
    linarith
  have hne : (2 * (Real.pi : ℂ) * Complex.I * (rate m.1 : ℂ)) ≠ 0 := by
    simp [Complex.I_ne_zero, Real.pi_ne_zero, ne_of_gt hpos]
  rw [cB, norm_inv, inv_le_one₀ (norm_pos_iff.mpr hne)]
  have hnorm : ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I * (rate m.1 : ℂ)‖
      = 2 * Real.pi * rate m.1 := by
    rw [show (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (rate m.1 : ℂ)
        = ((2 * Real.pi * rate m.1 : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
  rw [hnorm]
  have h1 : (1:ℝ) ≤ rate m.1 := by
    rw [rate]
    apply Real.one_le_sqrt.mpr
    have : (1 : ℝ) ≤ (m.1 : ℝ) := by exact_mod_cast m.2
    linarith
  nlinarith [Real.pi_gt_three, h1, hpos]

lemma shift_mem (τ : ℂ) (hτ : 0 < τ.im) : 0 < (τ + 1).im := by simpa using hτ

lemma FData.diffOn_shift (D : FData n) (x : E n) :
    DifferentiableOn ℂ (fun τ : ℂ => D.Φ (τ + 1) x) {τ : ℂ | 0 < τ.im} := by
  have h : DifferentiableOn ℂ (fun τ : ℂ => τ + 1) {τ : ℂ | 0 < τ.im} :=
    differentiableOn_id.add_const 1
  exact (D.holo x).comp h (fun τ hτ => shift_mem τ hτ)

lemma FData.cont_a (D : FData n) (x : E n) :
    ContinuousOn (fun τ : ℂ => aKernelGen D τ x) {τ : ℂ | 0 < τ.im} := by
  have h1 : ContinuousOn (fun τ : ℂ => D.Φ τ x) {τ : ℂ | 0 < τ.im} := (D.holo x).continuousOn
  have h2 : ContinuousOn (fun τ : ℂ => D.Φ (τ + 1) x) {τ : ℂ | 0 < τ.im} :=
    (D.diffOn_shift x).continuousOn
  have h3 : ContinuousOn (fun τ : ℂ => τ) {τ : ℂ | 0 < τ.im} := continuousOn_id
  exact h1.sub (h3.mul (h2.sub h1))

lemma FData.cont_b (D : FData n) (x : E n) :
    ContinuousOn (fun τ : ℂ => bKernelGen D τ x) {τ : ℂ | 0 < τ.im} := by
  have h1 : ContinuousOn (fun τ : ℂ => D.Φ τ x) {τ : ℂ | 0 < τ.im} := (D.holo x).continuousOn
  have h2 : ContinuousOn (fun τ : ℂ => D.Φ (τ + 1) x) {τ : ℂ | 0 < τ.im} :=
    (D.diffOn_shift x).continuousOn
  exact h2.sub h1

lemma FData.smooth_a (D : FData n) (τ : ℂ) :
    ContDiff ℝ ⊤ (fun x : E n => aKernelGen D τ x) := by
  have : aKernelGen D τ = fun x : E n => D.Φ τ x - τ * (D.Φ (τ + 1) x - D.Φ τ x) := rfl
  rw [this]
  exact (D.smooth τ).sub (contDiff_const.mul ((D.smooth (τ+1)).sub (D.smooth τ)))

lemma FData.smooth_b (D : FData n) (τ : ℂ) :
    ContDiff ℝ ⊤ (fun x : E n => bKernelGen D τ x) := by
  have : bKernelGen D τ = fun x : E n => D.Φ (τ + 1) x - D.Φ τ x := rfl
  rw [this]
  exact (D.smooth (τ+1)).sub (D.smooth τ)

lemma FData.radial_a (D : FData n) (τ : ℂ) :
    Radial (fun x : E n => aKernelGen D τ x) := by
  intro e e' h
  have : aKernelGen D τ = fun x : E n => D.Φ τ x - τ * (D.Φ (τ + 1) x - D.Φ τ x) := rfl
  rw [this]
  simp only [D.radial τ e e' h, D.radial (τ+1) e e' h]

lemma FData.radial_b (D : FData n) (τ : ℂ) :
    Radial (fun x : E n => bKernelGen D τ x) := by
  intro e e' h
  have : bKernelGen D τ = fun x : E n => D.Φ (τ + 1) x - D.Φ τ x := rfl
  rw [this]
  simp only [D.radial τ e e' h, D.radial (τ+1) e e' h]

lemma aKernel_eq (S : FunctionalEquationSolution n) (u : ℝ) (x : E n) :
    aKernel S u x = aKernelGen (FData.ofF S) ((u : ℂ) + Complex.I) x := by
  simp [aKernel, aKernelGen, FData.ofF]

lemma bKernel_eq (S : FunctionalEquationSolution n) (u : ℝ) (x : E n) :
    bKernel S u x = bKernelGen (FData.ofF S) ((u : ℂ) + Complex.I) x := by
  simp [bKernel, bKernelGen, FData.ofF]

/-- The contour-integral representation of `aCoeff` at any positive height. -/
lemma aCoeff_eq_height (S : FunctionalEquationSolution n) (m : Set.Ici (1:ℕ)) (x : E n)
    (y : ℝ) (hy : 0 < y) :
    aCoeff S m x = ∫ u in (0:ℝ)..1, aKernelGen (FData.ofF S) ((u : ℂ) + (y : ℂ) * Complex.I) x
      * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℂ)
          * ((u : ℂ) + (y : ℂ) * Complex.I))) := by
  obtain ⟨a, b, atil, btil, hF, hFt, hFd, hFtd, hb, ha, hbt, hat⟩ :=
    ExpansionFromFunctionalEquations S x
  have h1 : aCoeff S m x = a m := by
    rw [ha m (1:ℝ) (by norm_num)]
    unfold aCoeff
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    simp [aKernel]
  rw [h1, ha m y hy]
  refine intervalIntegral.integral_congr (fun u _ => ?_)
  simp only [aKernelGen, FData.ofF]

/-- The contour-integral representation of `bCoeff` at any positive height. -/
lemma bCoeff_eq_height (S : FunctionalEquationSolution n) (m : Set.Ici (1:ℕ)) (x : E n)
    (y : ℝ) (hy : 0 < y) :
    bCoeff S m x = cB m * ∫ u in (0:ℝ)..1,
      bKernelGen (FData.ofF S) ((u : ℂ) + (y : ℂ) * Complex.I) x
        * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℂ)
            * ((u : ℂ) + (y : ℂ) * Complex.I))) := by
  obtain ⟨a, b, atil, btil, hF, hFt, hFd, hFtd, hb, ha, hbt, hat⟩ :=
    ExpansionFromFunctionalEquations S x
  have h1 : bCoeff S m x = b m := by
    rw [hb m (1:ℝ) (by norm_num)]
    unfold bCoeff bKernel
    congr 1
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    simp
  rw [h1, hb m y hy]
  congr 1

/-- The contour-integral representation of `aTildeCoeff` at any positive height. -/
lemma aTildeCoeff_eq_height (S : FunctionalEquationSolution n) (m : Set.Ici (1:ℕ)) (x : E n)
    (y : ℝ) (hy : 0 < y) :
    aTildeCoeff S m x = ∫ u in (0:ℝ)..1,
      aKernelGen (FData.ofFtilde S) ((u : ℂ) + (y : ℂ) * Complex.I) x
        * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℂ)
            * ((u : ℂ) + (y : ℂ) * Complex.I))) := by
  obtain ⟨a, b, atil, btil, hF, hFt, hFd, hFtd, hb, ha, hbt, hat⟩ :=
    ExpansionFromFunctionalEquations S x
  have h1 : aTildeCoeff S m x = atil m := by
    rw [hat m (1:ℝ) (by norm_num)]
    unfold aTildeCoeff
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    simp
  rw [h1, hat m y hy]
  refine intervalIntegral.integral_congr (fun u _ => ?_)
  simp only [aKernelGen, FData.ofFtilde]

/-- The contour-integral representation of `bTildeCoeff` at any positive height. -/
lemma bTildeCoeff_eq_height (S : FunctionalEquationSolution n) (m : Set.Ici (1:ℕ)) (x : E n)
    (y : ℝ) (hy : 0 < y) :
    bTildeCoeff S m x = cB m * ∫ u in (0:ℝ)..1,
      bKernelGen (FData.ofFtilde S) ((u : ℂ) + (y : ℂ) * Complex.I) x
        * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℂ)
            * ((u : ℂ) + (y : ℂ) * Complex.I))) := by
  obtain ⟨a, b, atil, btil, hF, hFt, hFd, hFtd, hb, ha, hbt, hat⟩ :=
    ExpansionFromFunctionalEquations S x
  have h1 : bTildeCoeff S m x = btil m := by
    rw [hbt m (1:ℝ) (by norm_num)]
    unfold bTildeCoeff
    congr 1
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    simp
  rw [h1, hbt m y hy]
  congr 1

theorem FunctionCoefficients {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n) :
    ∃ basis : SampleIdx 1 → RSch n,
      (∀ (m : Set.Ici (1 : ℕ)) (x : E n), (basis (m, 0)).1 x = aCoeff S m x) ∧
      (∀ (m : Set.Ici (1 : ℕ)) (x : E n), (basis (m, 1)).1 x = aTildeCoeff S m x) ∧
      (∀ (m : Set.Ici (1 : ℕ)) (x : E n), (basis (m, 2)).1 x = bCoeff S m x) ∧
      (∀ (m : Set.Ici (1 : ℕ)) (x : E n), (basis (m, 3)).1 x = bTildeCoeff S m x) ∧
      (∀ k ℓ : ℕ, ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
        ∀ (m : Set.Ici (1 : ℕ)) (j : Fin 4) (x : E n),
          ‖x‖ ^ k * ‖radialDeriv ℓ (⇑(basis (m, j)).1) x‖ ≤ C * ((m.1 : ℝ) + 1) ^ N) := by
  obtain ⟨Ga, hGa, hGaG⟩ := KernelSchwartz.kernel_isSchwartz (N := aKernelGen (FData.ofF S))
    (fun _ => 1) (aCoeff S)
    (fun x => FData.cont_a (FData.ofF S) x)
    (fun τ => FData.smooth_a (FData.ofF S) τ)
    (fun τ => FData.radial_a (FData.ofF S) τ)
    ((KernelSchwartz.growth_combination (FData.ofF S).Φ (FData.ofF S).smooth
      (FData.ofF S).growth).1)
    (fun m => by simp)
    (fun m x y hy => by rw [one_mul]; exact aCoeff_eq_height S m x y hy)
  obtain ⟨Gat, hGat, hGatG⟩ := KernelSchwartz.kernel_isSchwartz (N := aKernelGen (FData.ofFtilde S))
    (fun _ => 1) (aTildeCoeff S)
    (fun x => FData.cont_a (FData.ofFtilde S) x)
    (fun τ => FData.smooth_a (FData.ofFtilde S) τ)
    (fun τ => FData.radial_a (FData.ofFtilde S) τ)
    ((KernelSchwartz.growth_combination (FData.ofFtilde S).Φ (FData.ofFtilde S).smooth
      (FData.ofFtilde S).growth).1)
    (fun m => by simp)
    (fun m x y hy => by rw [one_mul]; exact aTildeCoeff_eq_height S m x y hy)
  obtain ⟨Gb, hGb, hGbG⟩ := KernelSchwartz.kernel_isSchwartz (N := bKernelGen (FData.ofF S))
    (cB) (bCoeff S)
    (fun x => FData.cont_b (FData.ofF S) x)
    (fun τ => FData.smooth_b (FData.ofF S) τ)
    (fun τ => FData.radial_b (FData.ofF S) τ)
    ((KernelSchwartz.growth_combination (FData.ofF S).Φ (FData.ofF S).smooth
      (FData.ofF S).growth).2)
    (cB_norm_le_one)
    (fun m x y hy => bCoeff_eq_height S m x y hy)
  obtain ⟨Gbt, hGbt, hGbtG⟩ := KernelSchwartz.kernel_isSchwartz (N := bKernelGen (FData.ofFtilde S))
    (cB) (bTildeCoeff S)
    (fun x => FData.cont_b (FData.ofFtilde S) x)
    (fun τ => FData.smooth_b (FData.ofFtilde S) τ)
    (fun τ => FData.radial_b (FData.ofFtilde S) τ)
    ((KernelSchwartz.growth_combination (FData.ofFtilde S).Φ (FData.ofFtilde S).smooth
      (FData.ofFtilde S).growth).2)
    (cB_norm_le_one)
    (fun m x y hy => bTildeCoeff_eq_height S m x y hy)
  refine ⟨fun p => ![Ga p.1, Gat p.1, Gb p.1, Gbt p.1] p.2, ?_, ?_, ?_, ?_, ?_⟩
  · intro m x
    simpa using hGa m x
  · intro m x
    simpa using hGat m x
  · intro m x
    simpa using hGb m x
  · intro m x
    simpa using hGbt m x
  · intro k ℓ
    obtain ⟨Ca, Na, hCa, hA⟩ := hGaG k ℓ
    obtain ⟨Cat, Nat, hCat, hAt⟩ := hGatG k ℓ
    obtain ⟨Cb, Nb, hCb, hB⟩ := hGbG k ℓ
    obtain ⟨Cbt, Nbt, hCbt, hBt⟩ := hGbtG k ℓ
    set Ctot : ℝ := Ca + Cat + Cb + Cbt with hCtot
    set N0 : ℕ := max (max Na Nat) (max Nb Nbt) with hN0
    have hCtot0 : 0 ≤ Ctot := by rw [hCtot]; linarith
    have hCaC : Ca ≤ Ctot := by rw [hCtot]; linarith
    have hCatC : Cat ≤ Ctot := by rw [hCtot]; linarith
    have hCbC : Cb ≤ Ctot := by rw [hCtot]; linarith
    have hCbtC : Cbt ≤ Ctot := by rw [hCtot]; linarith
    have hNa0 : Na ≤ N0 := by rw [hN0]; exact le_trans (le_max_left _ _) (le_max_left _ _)
    have hNat0 : Nat ≤ N0 := by rw [hN0]; exact le_trans (le_max_right _ _) (le_max_left _ _)
    have hNb0 : Nb ≤ N0 := by rw [hN0]; exact le_trans (le_max_left _ _) (le_max_right _ _)
    have hNbt0 : Nbt ≤ N0 := by rw [hN0]; exact le_trans (le_max_right _ _) (le_max_right _ _)
    refine ⟨Ctot, N0, hCtot0, ?_⟩
    intro m j x
    have hp1 : (1:ℝ) ≤ (m.1:ℝ) + 1 := by
      have h : (0:ℝ) ≤ (m.1:ℝ) := by positivity
      linarith
    have hCtot0' : 0 ≤ Ctot := hCtot0
    fin_cases j
    · refine le_trans (hA m x) ?_
      calc Ca * ((m.1 : ℝ) + 1) ^ Na
          ≤ Ctot * ((m.1 : ℝ) + 1) ^ Na :=
            mul_le_mul_of_nonneg_right hCaC (by positivity)
        _ ≤ Ctot * ((m.1 : ℝ) + 1) ^ N0 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hp1 hNa0) hCtot0'
    · refine le_trans (hAt m x) ?_
      calc Cat * ((m.1 : ℝ) + 1) ^ Nat
          ≤ Ctot * ((m.1 : ℝ) + 1) ^ Nat :=
            mul_le_mul_of_nonneg_right hCatC (by positivity)
        _ ≤ Ctot * ((m.1 : ℝ) + 1) ^ N0 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hp1 hNat0) hCtot0'
    · refine le_trans (hB m x) ?_
      calc Cb * ((m.1 : ℝ) + 1) ^ Nb
          ≤ Ctot * ((m.1 : ℝ) + 1) ^ Nb :=
            mul_le_mul_of_nonneg_right hCbC (by positivity)
        _ ≤ Ctot * ((m.1 : ℝ) + 1) ^ N0 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hp1 hNb0) hCtot0'
    · refine le_trans (hBt m x) ?_
      calc Cbt * ((m.1 : ℝ) + 1) ^ Nbt
          ≤ Ctot * ((m.1 : ℝ) + 1) ^ Nbt :=
            mul_le_mul_of_nonneg_right hCbtC (by positivity)
        _ ≤ Ctot * ((m.1 : ℝ) + 1) ^ N0 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hp1 hNbt0) hCtot0'

end

end Work.FunctionalEquations
