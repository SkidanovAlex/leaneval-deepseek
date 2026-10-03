/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Shifted Calderón–Zygmund kernels: definitions

This module sets up the vocabulary for the shifted Calderón–Zygmund estimates of
Appendix B of Krause–Mirek–Tao, *Pointwise ergodic theorems for non-conventional
bilinear polynomial averages*, Annals of Math. **195** (2022) — the theorem there
called `cz-shift`.

The multiplier with symbol `φ_N(ξ) = ψ(A N^d ξ) e(λ_N A N^d ξ)` is convolution with
the explicit kernel

  `K_N(x) = (A N^d)⁻¹ Ψ((x − λ_N A N^d)/(A N^d))`,  `Ψ = 𝓕⁻¹ψ`.

Everything below is phrased in terms of the kernel `Ψ` and of the *scales*
`σ_N = A N^d`: all statements are about an abstract finite family of positive
scales `σ : ι → ℝ` (so that the Euclidean/polynomial structure of the paper enters
only through the instantiation `σ N = A * N ^ d`).

## Main definitions

* `Work.Analysis.CzShift.scale A d N` : the scale `A * N ^ d`.
* `Work.Analysis.CzShift.Lacunary λ D` : finiteness/lacunarity of a set of scales.
* `Work.Analysis.CzShift.LacunaryFam λ D σ` : the same, for an abstract family `σ`.
* `Work.Analysis.CzShift.shiftKernel Ψ σ t` : the shifted kernel
  `x ↦ σ⁻¹ Ψ((x − t σ)/σ)`.
* `Work.Analysis.CzShift.czOp D K ε f` : the convolution operator
  `x ↦ ∑_{i ∈ D} ε i • ∫ y, K i (x − y) • f y`.
* `Work.Analysis.CzShift.sqFn D g` : the `ℓ²(D;H)`-norm of the vector of functions `g`.
-/

namespace Work.Analysis.CzShift

open MeasureTheory Finset

set_option autoImplicit false

variable {ι : Type*}

/-- The spatial scale `σ_N = A * N ^ d` attached to a lacunary scale `N ≥ 1`. -/
noncomputable def scale (A : ℝ) (d : ℕ) (N : ℝ) : ℝ := A * N ^ d

/-- `Lacunary λ D` says that `D` is a finite `λ`-lacunary set of scales `≥ 1`: any two
distinct elements of `D` differ by a factor at least `λ`. -/
def Lacunary (lam : ℝ) (D : Finset ℝ) : Prop :=
  (∀ N ∈ D, 1 ≤ N) ∧ ∀ N ∈ D, ∀ M ∈ D, N ≠ M → lam * min N M ≤ max N M

/-- `LacunaryFam λ D σ` says that the scales `σ i`, `i ∈ D`, are positive and that any two
distinct ones differ by a factor at least `λ`. -/
def LacunaryFam (lam : ℝ) (D : Finset ι) (σ : ι → ℝ) : Prop :=
  (∀ i ∈ D, 0 < σ i) ∧ ∀ i ∈ D, ∀ j ∈ D, i ≠ j → lam * min (σ i) (σ j) ≤ max (σ i) (σ j)

/-- `LacunaryFam` is monotone in the lacunarity parameter. -/
theorem LacunaryFam.mono {lam lam' : ℝ} (h : lam ≤ lam') {D : Finset ι} {σ : ι → ℝ}
    (hl : LacunaryFam lam' D σ) : LacunaryFam lam D σ :=
  ⟨hl.1, fun i hi j hj hij => le_trans (mul_le_mul_of_nonneg_right h (le_min (hl.1 i hi).le
    (hl.1 j hj).le)) (hl.2 i hi j hj hij)⟩

/-- The hypotheses on the rescaled kernel `Ψ` of Appendix B of Krause--Mirek--Tao: `Ψ` is a
(real-valued) rescaled Schwartz kernel whose derivative `Ψ'` obeys the pointwise decay
`|Ψ u| ≤ B/(1+u²)`, `|Ψ' u| ≤ B/(1+u²)`, with `B ≥ 1`.

For `Ψ = 𝓕⁻¹ψ` these bounds are consequences of the hypotheses on `ψ` (support in `[-C,C]`,
`|ψ^{(j)}| ≤ C`, `ψ(0) = 0`). -/
structure IsCZSeed (Ψ Ψ' : ℝ → ℝ) (B : ℝ) : Prop where
  /-- The size parameter is at least `1`. -/
  one_le : 1 ≤ B
  /-- `Ψ'` is the derivative of `Ψ`. -/
  hasDerivAt : ∀ u, HasDerivAt Ψ (Ψ' u) u
  /-- Pointwise decay of `Ψ`. -/
  bound : ∀ u, |Ψ u| ≤ B / (1 + u ^ 2)
  /-- Pointwise decay of `Ψ'`. -/
  bound' : ∀ u, |Ψ' u| ≤ B / (1 + u ^ 2)

/-- The shifted Calderón–Zygmund kernel attached to the scale `σ` and the shift `t`:
`x ↦ σ⁻¹ Ψ((x − t σ)/σ)`.  It is the convolution kernel of the Fourier multiplier
`ξ ↦ ψ(σ ξ) e(t σ ξ)` with `ψ = 𝓕Ψ`. -/
noncomputable def shiftKernel (Ψ : ℝ → ℝ) (σ t : ℝ) : ℝ → ℂ :=
  fun x => ((σ⁻¹ * Ψ ((x - t * σ) / σ) : ℝ) : ℂ)

/-- The complex-valued version of the shifted kernel, used for the Fourier transform: it is the
same formula `x ↦ σ⁻¹ Ψ((x − tσ)/σ)` for a complex-valued `Ψ`. -/
noncomputable def shiftKernelC (Ψ : ℝ → ℂ) (σ t : ℝ) : ℝ → ℂ :=
  fun x => (σ : ℂ)⁻¹ * Ψ ((x - t * σ) / σ)

/-- `shiftKernel` for a real-valued seed is `shiftKernelC` for its complexification. -/
theorem shiftKernel_eq_shiftKernelC (Ψ : ℝ → ℝ) (σ t : ℝ) :
    shiftKernel Ψ σ t = shiftKernelC (fun u => (Ψ u : ℂ)) σ t := by
  funext x
  simp only [shiftKernel, shiftKernelC, Complex.ofReal_mul, Complex.ofReal_inv]

/-- The family of shifted kernels attached to an abstract family of scales `σ` and shifts `t`. -/
noncomputable def shiftKernelFam (Ψ : ℝ → ℝ) (σ t : ι → ℝ) (i : ι) : ℝ → ℂ :=
  shiftKernel Ψ (σ i) (t i)

/-- The convolution operator with kernel family `K` and signs `ε` over the finite set `D`:
`x ↦ ∑_{i ∈ D} ε i • ∫ y, K i (x − y) • f y`.  This is
`∑_{i ∈ D} ε_i T_{K_i} f`, i.e. the operator `T_{∑_i ε_i φ_i}` of the paper. -/
noncomputable def czOp {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (D : Finset ι) (K : ι → ℝ → ℂ) (ε : ι → ℂ) (f : ℝ → H) : ℝ → H :=
  fun x => ∑ i ∈ D, ε i • ∫ y, K i (x - y) • f y

/-- The `ℓ²(D;H)`-norm of the vector of values `g i`: the square function
`(∑_{i ∈ D} ‖g i‖²)^{1/2}`.  For `g i = T_i f` this is the square function of the
operator family `(T_i)_{i∈D}`, i.e. the `L^p(ℝ;ℓ²(D;H))` norm of `(T_i f)_i`. -/
noncomputable def sqFn {H : Type*} [NormedAddCommGroup H] (D : Finset ι) (g : ι → H) : ℝ :=
  (∑ i ∈ D, ‖g i‖ ^ 2) ^ (1 / 2 : ℝ)

/-- The single-scale operator `T_{K} f x = ∫ y, K (x − y) • f y`. -/
noncomputable def czOpOne {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (K : ℝ → ℂ) (f : ℝ → H) : ℝ → H :=
  fun x => ∫ y, K (x - y) • f y

end Work.Analysis.CzShift
