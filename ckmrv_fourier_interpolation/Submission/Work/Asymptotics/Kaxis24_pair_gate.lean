import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.Kernels.LogLambdaInstance
import Submission.Work.Kernels.E2Laws
import Submission.Work.Kernels.KernelFacts.KPlus_T2

namespace Work.Asymptotics

open UpperHalfPlane

/-- **The leading cusp datum of the dimension-`24` kernel** (the paper's `𝔸`):
`𝔸(τ) = (E₂E₄-E₆)(E₂E₆-E₄²)`.  It is the weight-`12` quasimodular factor appearing both in the
`T`-cocycle of `G_{1,1}` and in the Fricke (`S`)-cocycle of `G_{1,1}`. -/
noncomputable def A24 (τ : UpperHalfPlane) : ℂ :=
  (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ - Work.Kernels.E6Fun τ)
    * (Work.Kernels.E2Fun τ * Work.Kernels.E6Fun τ - Work.Kernels.E4Fun τ ^ 2)

/-- **The `exp(2πt)`-coefficient function of the dimension-`24` kernel** (the paper's `F`):
`F(τ) = 𝔹(τ) - 2πiτ𝔸(τ)` with `𝔹 = 7E₄³+5E₆²-12E₂E₄E₆`.  It is free of the `LogLambdaData`
parameter and `G_{1,1} = (i/3456)F` (`Gcusp24_one_one`). -/
noncomputable def F24 (τ : UpperHalfPlane) : ℂ :=
  7 * Work.Kernels.E4Fun τ ^ 3 + 5 * Work.Kernels.E6Fun τ ^ 2
    - 12 * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ)
    - 2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) * A24 τ

/-- **The second component of the pair is `(i/3456)·F`.**

`Gcusp ℓ 24 1 1` (the coefficient of `z¹e^{2πiz}` in the cusp-`i∞` expansion of the CKMRV
kernel) is *free of the `LogLambdaData` parameter* and equals `(i/3456)·F24` with
`F24 = 𝔹 - 2πiτ𝔸`.  Consequently the zero set of the second component of the pair gate is
exactly `{τ : F24 τ = 0}`, and the pair gate is equivalent to "`Gcusp ℓ 24 1 0` does not vanish
on the zero set of `F24`" (the proven `pair_gate_iff`).

This is the algebraic reduction that isolates the *mathematical* content of
`Kaxis24_pair_gate`: everything `LogLambdaData`-dependent sits in the *first* component. -/
theorem Gcusp24_one_one (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) :
    Work.Asymptotics.Gcusp24 ℓ 1 1 τ = (Complex.I / 3456) * F24 τ := by
  rw [Work.Asymptotics.Gcusp24]
  norm_num
  rw [ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq τ]
  simp only [F24, A24, Work.Kernels.phiVec, Work.Kernels.phiNeg2, Work.Kernels.phi0,
    Work.Kernels.phi2, Work.Kernels.E2Fun, Work.Kernels.E4Fun, Work.Kernels.E6Fun,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **The `T`-cocycle of `F24`.**  `E₂, E₄, E₆` (hence `𝔹` and `𝔸`) are `T`-invariant while the
explicit `τ` in `-2πiτ𝔸` shifts, so `F24(τ+1) = F24 τ - 2πi𝔸 τ`.  Consequently `F24` vanishes at
exactly one point of every `T`-orbit: `F24(τ+n) = F24 τ - 2πin𝔸 τ` and `𝔸` does not vanish at a
zero of `F24` (if `𝔸(τ) = 0` then `F24 = 𝔹 = 7(E₄³-E₆²)` or `-5(E₄³-E₆²)`, both nonzero since
`Δ ≠ 0`).  This is what makes the zero set of `F24` discrete: it is the image of the `1`-periodic
fixed point equation `τ = 𝔹(τ)/(2πi𝔸(τ))`. -/
theorem F24_vadd_one (τ : UpperHalfPlane) :
    F24 ((1 : ℝ) +ᵥ τ) = F24 τ - 2 * (Real.pi : ℂ) * Complex.I * A24 τ := by
  simp only [F24, A24, Work.Kernels.E2Fun_vadd_one, Work.Kernels.KernelFacts.E4Fun_vadd_one,
    Work.Kernels.KernelFacts.E6Fun_vadd_one, UpperHalfPlane.coe_vadd, Complex.ofReal_one]
  ring

-- The two lemmas below are the ones the *arithmetic* of the remaining (numerical) content needs:
-- `Gcusp ℓ 24 1 1 = (i/3456)F24` together with the exact form of the first component
-- `2·G_{1,0} = τ·P + Q + ...` reduce the pair gate to an explicit equation in `(E₂,E₄,E₆,𝓛,𝓛_S)`.

/-- **The first component in reduced form.**  With `P = -(i/288)(E₄²E₆+E₂²E₄E₆) + (i/144)E₂E₄³
- 7iE₂Δ` one has

  `2·G_{1,0} = τ·P + (E₄³-E₂E₄E₆)/(48π) + Δ(c_L-22)/π + (ψ₂E₁₀-ψ₄E₈)/(1152π)`.

Since `F24 = 𝔹 - 2πiτ𝔸`, at a zero of `F24` the `τ` appearing explicitly can be eliminated
(`2πiζ𝔸(ζ) = 𝔹(ζ)`), which gives the *single* equation that the pair gate has to exclude:

  `𝔹P + i𝔸(E₄³-E₂E₁₀)/24 + 2i𝔸Δ(c_L-22) + i𝔸(ψ₂E₁₀-ψ₄E₈)/576 = 0`  at `ζ`.

This identity is what makes the remaining content a concrete question about the zero set of the
single (parameter-free) function `F24`. -/
theorem Gcusp24_one_zero_reduced (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) :
    2 * Work.Asymptotics.Gcusp24 ℓ 1 0 τ
      = (τ : ℂ) * (-(Complex.I / 288)
            * (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ
                + Work.Kernels.E2Fun τ ^ 2 * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ)
          + (Complex.I / 144) * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ ^ 3)
          - 7 * Complex.I * (Work.Kernels.E2Fun τ * Work.Kernels.DeltaFun τ))
        + (Work.Kernels.E4Fun τ ^ 3
            - Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ)
          / (48 * (Real.pi : ℂ))
        + Work.Kernels.DeltaFun τ * (cuspL ℓ - 22) / (Real.pi : ℂ)
        + (Work.Kernels.psi2 ℓ τ * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ)
            - Work.Kernels.psi4 ℓ τ * Work.Kernels.E4Fun τ ^ 2)
          / (1152 * (Real.pi : ℂ)) := by
  rw [Work.Asymptotics.Gcusp24]
  norm_num
  simp only [Work.Kernels.phiVec, Work.Kernels.phiNeg2, Work.Kernels.phi0, Work.Kernels.phi2,
    Work.Kernels.E2Fun, Work.Kernels.E4Fun, Work.Kernels.E6Fun,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring


end Work.Asymptotics
