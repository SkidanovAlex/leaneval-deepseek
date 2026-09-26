/-
# The `T`-cocycles of the two components of the pair gate, and the strip reduction

The two components of the pair gate behave differently under the translation `T : τ ↦ τ+1`:

* the second component `G_{1,1} = (i/3456)F24` is *affine*: `F24(τ+1) = F24 τ - 2πi A24 τ` with
  `A24` invariant, so that `F24(τ+n) = F24 τ - 2πin A24 τ` for every integer `n`;
* the first component `G_{1,0}` is also affine, with difference
  `2(G_{1,0}(τ+1) - G_{1,0}(τ)) = Pnum τ + i·Xnum τ/1152`, where
  `Pnum = -(i/288)(E₄²E₆+E₂²E₄E₆) + (i/144)E₂E₄³ - 7iE₂Δ` and `Xnum = ξ₂E₁₀ - ξ₄E₈`
  are both `T`-invariant.

The affine laws are obtained from the "periodic completion" trick: `τ ↦ F24 τ + 2πiτA24 τ` and
`τ ↦ G_{1,0} τ - τ·(G_{1,0}(τ+1)-G_{1,0}(τ))` are `1`-periodic, and
`Work.Rigidity.PeriodicDecay.vadd_int_eq` propagates `1`-periodicity to integer shifts.
-/
import Mathlib
import Submission.Work.Asymptotics.PGFar.Defs
import Submission.Work.Kernels.KernelFacts.psi2_T2
import Submission.Work.Rigidity.PeriodicDecay.periodic_bound_all

namespace Work.Asymptotics

open UpperHalfPlane ModularGroup ModularForm

open scoped MatrixGroups ModularForm Modular Manifold Bundle

noncomputable section

/-! ## `A24` is `T`-invariant -/

lemma A24_vadd_one (τ : UpperHalfPlane) : A24 ((1 : ℝ) +ᵥ τ) = A24 τ := by
  simp only [A24, Work.Kernels.E2Fun_vadd_one, Work.Kernels.KernelFacts.E4Fun_vadd_one,
    Work.Kernels.KernelFacts.E6Fun_vadd_one]

lemma A24_vadd_int (m : ℤ) (τ : UpperHalfPlane) : A24 ((m : ℝ) +ᵥ τ) = A24 τ :=
  Work.Rigidity.PeriodicDecay.vadd_int_eq A24_vadd_one τ m

/-! ## The affine law of `F24` (and hence of `G_{1,1}`) -/

/-- `τ ↦ F24 τ + 2πiτ A24 τ` is `1`-periodic. -/
lemma F24_periodic_completion (τ : UpperHalfPlane) :
    F24 ((1 : ℝ) +ᵥ τ) + 2 * (Real.pi : ℂ) * Complex.I * (((1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ)
        * A24 ((1 : ℝ) +ᵥ τ)
      = F24 τ + 2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) * A24 τ := by
  rw [F24_vadd_one, A24_vadd_one, UpperHalfPlane.coe_vadd]
  push_cast
  ring

/-- **Affine law of `F24`.** -/
lemma F24_vadd_int (m : ℤ) (τ : UpperHalfPlane) :
    F24 ((m : ℝ) +ᵥ τ) = F24 τ - 2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * A24 τ := by
  have h := Work.Rigidity.PeriodicDecay.vadd_int_eq
    (f := fun σ : UpperHalfPlane => F24 σ + 2 * (Real.pi : ℂ) * Complex.I * (σ : ℂ) * A24 σ)
    F24_periodic_completion τ m
  rw [A24_vadd_int m τ, UpperHalfPlane.coe_vadd] at h
  linear_combination h

/-- **Affine law of the second component of the pair gate.** -/
lemma Gcusp11_vadd_int (ℓ : Work.Kernels.LogLambdaData) (m : ℤ) (τ : UpperHalfPlane) :
    Gcusp ℓ 24 1 1 ((m : ℝ) +ᵥ τ)
      = Gcusp ℓ 24 1 1 τ - (Complex.I / 3456) * (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)) * A24 τ := by
  have h24 : ∀ σ : UpperHalfPlane, Gcusp ℓ 24 1 1 σ = Gcusp24 ℓ 1 1 σ := fun σ => rfl
  rw [h24 ((m : ℝ) +ᵥ τ), h24 τ, Gcusp24_one_one, Gcusp24_one_one, F24_vadd_int m τ]
  ring

/-! ## The `T`-difference of the `ψ`-terms and the affine law of `G_{1,0}` -/

/-- `ξ₄ = U²+W²-2V²` is `T`-invariant. -/
lemma xi4Fun_vadd_one (τ : UpperHalfPlane) :
    Work.Kernels.xi4Fun ((1 : ℝ) +ᵥ τ) = Work.Kernels.xi4Fun τ := by
  simp only [Work.Kernels.xi4Fun, Work.Kernels.KernelFacts.UFun_vadd_one,
    Work.Kernels.KernelFacts.WFun_vadd_one, Work.Kernels.KernelFacts.VFun_vadd_one]
  ring

lemma E8Fun_vadd_one (τ : UpperHalfPlane) :
    Work.Kernels.E8Fun ((1 : ℝ) +ᵥ τ) = Work.Kernels.E8Fun τ := by
  simp only [Work.Kernels.E8Fun, Work.Kernels.KernelFacts.E4Fun_vadd_one]

lemma E10Fun_vadd_one (τ : UpperHalfPlane) :
    Work.Kernels.E10Fun ((1 : ℝ) +ᵥ τ) = Work.Kernels.E10Fun τ := by
  simp only [Work.Kernels.E10Fun, Work.Kernels.KernelFacts.E4Fun_vadd_one,
    Work.Kernels.KernelFacts.E6Fun_vadd_one]

/-- The bracket whose `T`-difference drives `G_{1,0}`. -/
def Xnum (τ : UpperHalfPlane) : ℂ :=
  Work.Kernels.xi2Fun τ * Work.Kernels.E10Fun τ - Work.Kernels.xi4Fun τ * Work.Kernels.E8Fun τ

/-- The explicit `τ`-coefficient of the reduced formula for `2·G_{1,0}`. -/
def Pnum (τ : UpperHalfPlane) : ℂ :=
  -(Complex.I / 288) * (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ
      + Work.Kernels.E2Fun τ ^ 2 * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ)
    + (Complex.I / 144) * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ ^ 3)
    - 7 * Complex.I * (Work.Kernels.E2Fun τ * Work.Kernels.DeltaFun τ)

lemma Pnum_vadd_one (τ : UpperHalfPlane) : Pnum ((1 : ℝ) +ᵥ τ) = Pnum τ := by
  simp only [Pnum, Work.Kernels.E2Fun_vadd_one, Work.Kernels.KernelFacts.E4Fun_vadd_one,
    Work.Kernels.KernelFacts.E6Fun_vadd_one, Work.Kernels.KernelFacts.DeltaFun_vadd_one]

lemma Xnum_vadd_one (τ : UpperHalfPlane) : Xnum ((1 : ℝ) +ᵥ τ) = Xnum τ := by
  simp only [Xnum, Work.Kernels.KernelFacts.xi2Fun_vadd_one, xi4Fun_vadd_one,
    E10Fun_vadd_one, E8Fun_vadd_one]

/-- `(ξ₂|₂S)(τ+1) = V τ - W τ`. -/
lemma xi2S_vadd_one (τ : UpperHalfPlane) :
    (Work.Kernels.xi2Fun ∣[(2 : ℤ)] ModularGroup.S) ((1 : ℝ) +ᵥ τ)
      = Work.Kernels.VFun τ - Work.Kernels.WFun τ := by
  rw [Work.Kernels.KernelFacts.xi2Fun_slash_S, Work.Kernels.KernelFacts.UFun_vadd_one,
    Work.Kernels.KernelFacts.VFun_vadd_one]
  ring

/-- **The `T`-difference of `ψ₂`.** -/
lemma psi2_vadd_one_sub (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) :
    Work.Kernels.psi2 ℓ ((1 : ℝ) +ᵥ τ) - Work.Kernels.psi2 ℓ τ
      = (Real.pi : ℂ) * Complex.I * Work.Kernels.xi2Fun τ := by
  have hL := Work.Kernels.KernelFacts.L_vadd_one ℓ τ
  have hLS := Work.Kernels.KernelFacts.L_S_vadd_one ℓ τ
  have hxi := Work.Kernels.KernelFacts.xi2Fun_vadd_one τ
  have hS := xi2S_vadd_one τ
  have hS0 := Work.Kernels.KernelFacts.xi2Fun_slash_S τ
  simp only [Work.Kernels.psi2]
  rw [hL, hLS, hxi, hS, hS0]
  ring

/-- `(ξ₄|₄S)(τ+1) = W² + V² - 2U²`. -/
lemma xi4S_vadd_one (τ : UpperHalfPlane) :
    (Work.Kernels.xi4Fun ∣[(4 : ℤ)] ModularGroup.S) ((1 : ℝ) +ᵥ τ)
      = Work.Kernels.WFun τ ^ 2 + Work.Kernels.VFun τ ^ 2 - 2 * Work.Kernels.UFun τ ^ 2 := by
  rw [Work.Kernels.KernelFacts.xi4S_apply, Work.Kernels.KernelFacts.UFun_vadd_one,
    Work.Kernels.KernelFacts.WFun_vadd_one, Work.Kernels.KernelFacts.VFun_vadd_one]
  ring

/-- **The `T`-difference of `ψ₄`.** -/
lemma psi4_vadd_one_sub (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) :
    Work.Kernels.psi4 ℓ ((1 : ℝ) +ᵥ τ) - Work.Kernels.psi4 ℓ τ
      = (Real.pi : ℂ) * Complex.I * Work.Kernels.xi4Fun τ := by
  have hL := Work.Kernels.KernelFacts.L_vadd_one ℓ τ
  have hLS := Work.Kernels.KernelFacts.L_S_vadd_one ℓ τ
  have hxi := xi4Fun_vadd_one τ
  have hS := xi4S_vadd_one τ
  have hS0 := Work.Kernels.KernelFacts.xi4S_apply τ
  simp only [Work.Kernels.psi4]
  rw [hL, hLS, hxi, hS, hS0]
  ring

/-- **The `T`-difference of `ψ₂E₁₀ - ψ₄E₈` is `πi(ξ₂E₁₀ - ξ₄E₈)`.**  The `𝓛_S`-terms cancel
exactly. -/
lemma dXnum (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) :
    (Work.Kernels.psi2 ℓ ((1 : ℝ) +ᵥ τ) * Work.Kernels.E10Fun ((1 : ℝ) +ᵥ τ)
        - Work.Kernels.psi4 ℓ ((1 : ℝ) +ᵥ τ) * Work.Kernels.E8Fun ((1 : ℝ) +ᵥ τ))
      - (Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ
          - Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ)
      = (Real.pi : ℂ) * Complex.I * Xnum τ := by
  rw [E10Fun_vadd_one, E8Fun_vadd_one]
  have h2 := psi2_vadd_one_sub ℓ τ
  have h4 := psi4_vadd_one_sub ℓ τ
  simp only [Xnum]
  linear_combination Work.Kernels.E10Fun τ * h2 - Work.Kernels.E8Fun τ * h4

/-- The `τ`-independent part of the reduced formula for `2·G_{1,0}`. -/
def Cnum (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  (Work.Kernels.E4Fun τ ^ 3
      - Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ) / (48 * (Real.pi : ℂ))
    + Work.Kernels.DeltaFun τ * (cuspL ℓ - 22) / (Real.pi : ℂ)

/-- The `ψ`-part of the reduced formula for `2·G_{1,0}`. -/
def W3 (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  (Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ - Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ)
    / (1152 * (Real.pi : ℂ))

lemma Cnum_vadd_one (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) :
    Cnum ℓ ((1 : ℝ) +ᵥ τ) = Cnum ℓ τ := by
  simp only [Cnum, Work.Kernels.E2Fun_vadd_one, Work.Kernels.KernelFacts.E4Fun_vadd_one,
    Work.Kernels.KernelFacts.E6Fun_vadd_one, Work.Kernels.KernelFacts.DeltaFun_vadd_one]

lemma W3_vadd_one_sub (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) :
    W3 ℓ ((1 : ℝ) +ᵥ τ) - W3 ℓ τ = Complex.I * Xnum τ / 1152 := by
  have h := dXnum ℓ τ
  rw [E10Fun_vadd_one, E8Fun_vadd_one] at h
  simp only [W3, E10Fun_vadd_one, E8Fun_vadd_one]
  rw [← sub_div, h]
  field_simp

/-- The reduced formula for `2·G_{1,0}`, in the notation `Pnum, Cnum, W3`. -/
lemma Gcusp10_reduced (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) :
    2 * Gcusp24 ℓ 1 0 τ = (τ : ℂ) * Pnum τ + Cnum ℓ τ + W3 ℓ τ := by
  rw [Gcusp24_one_zero_reduced]
  simp only [Pnum, Cnum, W3]
  ring

/-- **The `T`-difference of the two components' coefficient functions.** -/
lemma dg10_eq (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) :
    2 * (Gcusp ℓ 24 1 0 ((1 : ℝ) +ᵥ τ) - Gcusp ℓ 24 1 0 τ)
      = Pnum τ + Complex.I * Xnum τ / 1152 := by
  have h24 : ∀ σ : UpperHalfPlane, Gcusp ℓ 24 1 0 σ = Gcusp24 ℓ 1 0 σ := fun σ => rfl
  have hv : (((1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ) = 1 + (τ : ℂ) := by
    rw [UpperHalfPlane.coe_vadd]; push_cast; ring
  rw [h24, h24, mul_sub, Gcusp10_reduced ℓ ((1 : ℝ) +ᵥ τ), Gcusp10_reduced ℓ τ,
    Pnum_vadd_one τ, hv]
  linear_combination W3_vadd_one_sub ℓ τ + Cnum_vadd_one ℓ τ

/-- The `T`-difference of the first component of the pair gate is `1`-periodic. -/
lemma dg10_periodic (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) :
    (Gcusp ℓ 24 1 0 ((1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ τ)) - Gcusp ℓ 24 1 0 ((1 : ℝ) +ᵥ τ))
      = Gcusp ℓ 24 1 0 ((1 : ℝ) +ᵥ τ) - Gcusp ℓ 24 1 0 τ := by
  have h1 := dg10_eq ℓ ((1 : ℝ) +ᵥ τ)
  have h0 := dg10_eq ℓ τ
  rw [Pnum_vadd_one τ, Xnum_vadd_one τ] at h1
  linear_combination (1 / 2) * h1 - (1 / 2) * h0

/-- **The affine law of the first component of the pair gate.** -/
lemma Gcusp10_vadd_int (ℓ : Work.Kernels.LogLambdaData) (m : ℤ) (τ : UpperHalfPlane) :
    Gcusp ℓ 24 1 0 ((m : ℝ) +ᵥ τ)
      = Gcusp ℓ 24 1 0 τ
        + (m : ℂ) * (Gcusp ℓ 24 1 0 ((1 : ℝ) +ᵥ τ) - Gcusp ℓ 24 1 0 τ) := by
  set D : UpperHalfPlane → ℂ := fun σ => Gcusp ℓ 24 1 0 ((1 : ℝ) +ᵥ σ) - Gcusp ℓ 24 1 0 σ
  have hper : ∀ σ : UpperHalfPlane, D ((1 : ℝ) +ᵥ σ) = D σ := dg10_periodic ℓ
  have hD : D ((m : ℝ) +ᵥ τ) = D τ := Work.Rigidity.PeriodicDecay.vadd_int_eq hper τ m
  have hPsi : ∀ σ : UpperHalfPlane,
      (fun σ : UpperHalfPlane => Gcusp ℓ 24 1 0 σ - (σ : ℂ) * D σ) ((1 : ℝ) +ᵥ σ)
        = (fun σ : UpperHalfPlane => Gcusp ℓ 24 1 0 σ - (σ : ℂ) * D σ) σ := by
    intro σ
    show Gcusp ℓ 24 1 0 ((1 : ℝ) +ᵥ σ) - (((1 : ℝ) +ᵥ σ : UpperHalfPlane) : ℂ) * D ((1 : ℝ) +ᵥ σ)
      = Gcusp ℓ 24 1 0 σ - (σ : ℂ) * D σ
    rw [hper σ, UpperHalfPlane.coe_vadd]
    push_cast
    ring
  have hPsi' := Work.Rigidity.PeriodicDecay.vadd_int_eq
    (f := fun σ : UpperHalfPlane => Gcusp ℓ 24 1 0 σ - (σ : ℂ) * D σ) hPsi τ m
  rw [hD, UpperHalfPlane.coe_vadd] at hPsi'
  linear_combination hPsi'


end

end Work.Asymptotics
