/-
# Tensor-product norms (the paper's `ttensor`, `ttensor-bil`, `ttensor-lin`)

This module develops the elementary, finite-dimensional tensor-product norm factorisations of
the Notation section of Krause--Mirek--Tao, *Pointwise ergodic theorems for non-conventional
bilinear polynomial averages*, Annals of Math. 195 (2022) (arXiv:2008.00857).

The paper's identities are

* `ttensor`     : `‖T₁ ⊗ T₂‖ = ‖T₁‖ ‖T₂‖` for linear integral operators,
* `ttensor-bil` : the same for bilinear operators, with (say) `B₁` arising from a non-negative
  kernel,
* together with the "test on tensor products" lower bound.

We work concretely in finite dimensions: functions on finite types carrying the normalised
counting (probability) measure `lpNormFin`, and linear/bilinear operators presented by their
kernels (`bilinKernelOp`, `linKernelOp`).  This is exactly the setting of the applications in
Sections 9--10 of the paper (finite cyclic groups `ℤ/qℤ`, and finite products of them).

## Main definitions

* `vTensor`        : the tensor product `x ⊗ y` of two vectors, as a matrix;
* `l2Norm`, `hsNorm` : the `ℓ²` norm of a vector and the Hilbert--Schmidt norm of a matrix;
* `kron`           : the Kronecker product of two matrices;
* `lpNormFin`      : the normalised `L^p` norm on functions on a finite type;
* `bilinKernelOp`  : the bilinear kernel operator `(f,g) ↦ (z ↦ ∑_{x,y} K z x y f x g y)`;
* `linKernelOp`    : the linear kernel operator `(f ↦ (z ↦ ∑_x K z x f x))`;
* `tensorKernel`   : the tensor product of two bilinear kernels.

## Main results

* `hsNorm_vTensor`  : `‖x ⊗ y‖ = ‖x‖ ‖y‖` (Hilbert--Schmidt tensor norm is multiplicative);
* `lpNormFin_prod_tensor` : `‖f ⊗ g‖_{L^p} = ‖f‖_{L^p} ‖g‖_{L^p}` (the paper's `ttensor-lin`);
* `bilinKernelOp_tensorKernel_le` : the upper bound half of the paper's `ttensor-bil`, stated in
  the hypothesis form used in Section 10;
* `bilinKernelOp_tensorKernel_pure` : the lower bound half (the identity on pure tensors).
-/
import Mathlib

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped BigOperators ENNReal
open Finset

namespace Work.Analysis.Paraproduct

noncomputable section

/-! ## The tensor product of two vectors, and the Hilbert--Schmidt norm -/

/-- The tensor product `x ⊗ y` of two vectors, realised as the matrix `(i,j) ↦ x i * y j`. -/
def vTensor {α β : Type*} (x : α → ℂ) (y : β → ℂ) : α → β → ℂ :=
  fun i j => x i * y j

/-- The `ℓ²` norm of a finite complex vector. -/
def l2Norm {α : Type*} [Fintype α] (x : α → ℂ) : ℝ := Real.sqrt (∑ i, ‖x i‖ ^ 2)

/-- The Hilbert--Schmidt (Frobenius) norm of a finite complex matrix. -/
def hsNorm {α β : Type*} [Fintype α] [Fintype β] (M : α → β → ℂ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, ‖M i j‖ ^ 2)

/-- **`ttensor-lin`, vector form.**  The Hilbert--Schmidt norm of a rank-one tensor is the
product of the `ℓ²` norms: `‖x ⊗ y‖ = ‖x‖ ‖y‖`.  In particular `‖x ⊗ y‖ ≤ ‖x‖ ‖y‖`, with
equality for the Hilbert tensor norm. -/
theorem hsNorm_vTensor {α β : Type*} [Fintype α] [Fintype β]
    (x : α → ℂ) (y : β → ℂ) : hsNorm (vTensor x y) = l2Norm x * l2Norm y := by
  have hsum : ∀ i, (∑ j : β, ‖x i * y j‖ ^ 2) = ‖x i‖ ^ 2 * (∑ j : β, ‖y j‖ ^ 2) := by
    intro i
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [norm_mul]; ring)
  have h : (∑ i : α, ∑ j : β, ‖x i * y j‖ ^ 2)
      = (∑ i : α, ‖x i‖ ^ 2) * (∑ j : β, ‖y j‖ ^ 2) := by
    rw [Finset.sum_congr rfl (fun i _ => hsum i), Finset.sum_mul]
  simp only [hsNorm, l2Norm, vTensor]
  rw [h, Real.sqrt_mul (Finset.sum_nonneg (fun i _ => by positivity))]

/-- `‖x ⊗ y‖ ≤ ‖x‖ ‖y‖` for the `ℓ²`/Hilbert--Schmidt tensor norm (the `ttensor` inequality). -/
theorem hsNorm_vTensor_le {α β : Type*} [Fintype α] [Fintype β]
    (x : α → ℂ) (y : β → ℂ) : hsNorm (vTensor x y) ≤ l2Norm x * l2Norm y :=
  le_of_eq (hsNorm_vTensor x y)

/-- The Hilbert--Schmidt norm is non-negative. -/
theorem hsNorm_nonneg {α β : Type*} [Fintype α] [Fintype β] (M : α → β → ℂ) : 0 ≤ hsNorm M :=
  Real.sqrt_nonneg _

/-- Cauchy--Schwarz, in the elementary `ℓ²`-sum form used for tensor norms. -/
theorem sum_mul_le_sqrt {ι : Type*} [Fintype ι] (f g : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) :
    (∑ i, f i * g i) ≤ Real.sqrt (∑ i, f i ^ 2) * Real.sqrt (∑ i, g i ^ 2) := by
  have h1 : 0 ≤ ∑ i, f i ^ 2 := Finset.sum_nonneg (fun i _ => by positivity)
  have h2 : 0 ≤ ∑ i, g i ^ 2 := Finset.sum_nonneg (fun i _ => by positivity)
  have h3 : 0 ≤ ∑ i, f i * g i := Finset.sum_nonneg (fun i _ => mul_nonneg (hf i) (hg i))
  rw [← Real.sqrt_mul h1]
  rw [Real.le_sqrt h3 (mul_nonneg h1 h2)]
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g

/-- **The duality identity for the Hilbert--Schmidt norm.**  For matrices `M, N`,
`|⟨M, N⟩| ≤ ‖M‖ ‖N‖` where `⟨M,N⟩ = ∑_{i,j} M i j * conj (N i j)` is the Hilbert--Schmidt
inner product.  This is one half of the identity `‖M‖ = sup_{‖N‖ ≤ 1} |⟨M,N⟩|`. -/
theorem abs_pairing_le {α β : Type*} [Fintype α] [Fintype β] (M N : α → β → ℂ) :
    ‖∑ i, ∑ j, M i j * star (N i j)‖ ≤ hsNorm M * hsNorm N := by
  classical
  have h1 : ‖∑ i, ∑ j, M i j * star (N i j)‖ ≤ ∑ i, ∑ j, ‖M i j‖ * ‖N i j‖ := by
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum (fun i _ => ?_)
    refine le_trans (norm_sum_le _ _) ?_
    exact Finset.sum_le_sum (fun j _ => le_of_eq (by rw [norm_mul, norm_star]))
  have hflat : (∑ i, ∑ j, ‖M i j‖ * ‖N i j‖)
      = ∑ p : α × β, ‖M p.1 p.2‖ * ‖N p.1 p.2‖ := by
    rw [Fintype.sum_prod_type]
  rw [hflat] at h1
  have h2 : (∑ p : α × β, ‖M p.1 p.2‖ * ‖N p.1 p.2‖)
      ≤ Real.sqrt (∑ i, ∑ j, ‖M i j‖ ^ 2) * Real.sqrt (∑ i, ∑ j, ‖N i j‖ ^ 2) := by
    simpa only [Fintype.sum_prod_type]
      using sum_mul_le_sqrt (fun p : α × β => ‖M p.1 p.2‖)
        (fun p : α × β => ‖N p.1 p.2‖) (fun p => norm_nonneg _) (fun p => norm_nonneg _)
  simp only [hsNorm]
  exact le_trans h1 h2

/-! ## The Kronecker product of matrices -/

/-- The Kronecker (tensor) product of two matrices. -/
def kron {α β α' β' : Type*} (A : α → β → ℂ) (B : α' → β' → ℂ) :
    (α × α') → (β × β') → ℂ := fun i j => A i.1 j.1 * B i.2 j.2

/-- The bilinear-form rearrangement `(∑_{a,b} f a b) * (∑_{a',b'} g a' b')
`= ∑_{a,b,a',b'} f a b * g a' b'`. -/
theorem sum_mul_sum_sum {α β α' β' : Type*} [Fintype α] [Fintype β] [Fintype α'] [Fintype β']
    (f : α → β → ℝ) (g : α' → β' → ℝ) :
    (∑ a, ∑ b, f a b) * (∑ a', ∑ b', g a' b')
      = ∑ a, ∑ b, ∑ a', ∑ b', f a b * g a' b' := by
  have h1 : (∑ a, ∑ b, f a b) * (∑ a' : α', ∑ b' : β', g a' b')
      = ∑ a, (∑ b, f a b) * (∑ a' : α', ∑ b' : β', g a' b') :=
    Finset.sum_mul Finset.univ (fun a => ∑ b : β, f a b) _
  rw [h1]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have h2 : (∑ b, f a b) * (∑ a' : α', ∑ b' : β', g a' b')
      = ∑ b, f a b * (∑ a' : α', ∑ b' : β', g a' b') :=
    Finset.sum_mul Finset.univ (fun b => f a b) _
  rw [h2]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp only [Finset.mul_sum]

/-- Swapping the two middle sums of a fourfold sum. -/
theorem sum_swap_middle {α β α' β' : Type*} [Fintype α] [Fintype β] [Fintype α'] [Fintype β']
    (h : α → β → α' → β' → ℝ) :
    (∑ a, ∑ b, ∑ a', ∑ b', h a b a' b') = ∑ a, ∑ a', ∑ b, ∑ b', h a b a' b' := by
  refine Finset.sum_congr rfl (fun _a _ => ?_)
  rw [Finset.sum_comm]

/-- **`ttensor`, matrix form.**  The Hilbert--Schmidt norm is multiplicative under the Kronecker
product: `‖A ⊗ B‖ = ‖A‖ ‖B‖`. -/
theorem hsNorm_kron {α β α' β' : Type*} [Fintype α] [Fintype β] [Fintype α'] [Fintype β']
    (A : α → β → ℂ) (B : α' → β' → ℂ) :
    hsNorm (kron A B) = hsNorm A * hsNorm B := by
  have h : (∑ i : α × α', ∑ j : β × β', ‖A i.1 j.1 * B i.2 j.2‖ ^ 2)
      = (∑ i : α, ∑ j : β, ‖A i j‖ ^ 2) * (∑ i : α', ∑ j : β', ‖B i j‖ ^ 2) := by
    simp only [Fintype.sum_prod_type, norm_mul, mul_pow]
    rw [← sum_swap_middle (fun a b a' b' => ‖A a b‖ ^ 2 * ‖B a' b'‖ ^ 2)]
    rw [← sum_mul_sum_sum (fun a b => ‖A a b‖ ^ 2) (fun a' b' => ‖B a' b'‖ ^ 2)]
  simp only [hsNorm, kron]
  rw [h, Real.sqrt_mul (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by positivity)))]

/-! ## The normalised `L^p` norm on a finite type -/

/-- The normalised `L^p` "norm" on the finite type `α` equipped with the uniform probability
measure: `‖f‖_p = (card α)⁻¹ᐟᵖ (∑_a ‖f a‖^p)^{1/p}`.  (For `α = ZMod Q` this is
`Work.Analysis.Concentration.LpNormZMod`, see `lpNormFin_zmod`.) -/
def lpNormFin (α : Type*) [Fintype α] (p : ℝ) (f : α → ℂ) : ℝ :=
  (((Fintype.card α : ℝ))⁻¹ * ∑ a, ‖f a‖ ^ p) ^ (1 / p)

/-- The normalised `L^p` norm is non-negative. -/
theorem lpNormFin_nonneg {α : Type*} [Fintype α] (p : ℝ) (f : α → ℂ) :
    0 ≤ lpNormFin α p f :=
  Real.rpow_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg (fun a _ => Real.rpow_nonneg (norm_nonneg _) _))) _

/-- Homogeneity of the normalised `L^p` norm. -/
theorem lpNormFin_const_mul {α : Type*} [Fintype α] {p : ℝ} (hp : 0 < p) (c : ℂ)
    (f : α → ℂ) : lpNormFin α p (fun a => c * f a) = ‖c‖ * lpNormFin α p f := by
  have hS : 0 ≤ ∑ a : α, ‖f a‖ ^ p :=
    Finset.sum_nonneg (fun a _ => Real.rpow_nonneg (norm_nonneg _) _)
  simp only [lpNormFin, norm_mul]
  rw [show (∑ a : α, (‖c‖ * ‖f a‖) ^ p) = ‖c‖ ^ p * ∑ a : α, ‖f a‖ ^ p from by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun a _ => by
      rw [Real.mul_rpow (norm_nonneg _) (norm_nonneg _)])]
  rw [show ((Fintype.card α : ℝ))⁻¹ * (‖c‖ ^ p * ∑ a : α, ‖f a‖ ^ p)
      = ‖c‖ ^ p * (((Fintype.card α : ℝ))⁻¹ * ∑ a : α, ‖f a‖ ^ p) from by ring]
  rw [show (‖c‖ ^ p * (((Fintype.card α : ℝ))⁻¹ * ∑ a : α, ‖f a‖ ^ p)) ^ (1 / p)
      = (‖c‖ ^ p) ^ (1 / p)
        * (((Fintype.card α : ℝ))⁻¹ * ∑ a : α, ‖f a‖ ^ p) ^ (1 / p) from
    Real.mul_rpow (Real.rpow_nonneg (norm_nonneg c) p)
      (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) hS)]
  rw [show (‖c‖ ^ p) ^ (1 / p) = ‖c‖ from by
    rw [← Real.rpow_mul (norm_nonneg c), mul_one_div, div_self hp.ne', Real.rpow_one]]

/-! ## Kernel operators -/

/-- The linear kernel operator `f ↦ (z ↦ ∑_x K z x * f x)`. -/
def linKernelOp {α γ : Type*} [Fintype α] (K : γ → α → ℂ) (f : α → ℂ) : γ → ℂ :=
  fun z => ∑ x, K z x * f x

/-- The bilinear kernel operator `(f,g) ↦ (z ↦ ∑_{x,y} K z x y * f x * g y)`. -/
def bilinKernelOp {α β γ : Type*} [Fintype α] [Fintype β] (K : γ → α → β → ℂ)
    (f : α → ℂ) (g : β → ℂ) : γ → ℂ :=
  fun z => ∑ x, ∑ y, K z x y * f x * g y

/-- The tensor product of two bilinear kernels. -/
def tensorKernel {α β γ α' β' γ' : Type*}
    (K₁ : γ → α → β → ℂ) (K₂ : γ' → α' → β' → ℂ) :
    (γ × γ') → (α × α') → (β × β') → ℂ :=
  fun z x y => K₁ z.1 x.1 y.1 * K₂ z.2 x.2 y.2

/-- The slice of a function at a point of the first factor. -/
def slice {α β : Type*} (F : α × β → ℂ) (a : α) : β → ℂ := fun b => F (a, b)

/-- **The slicing identity.**  The bilinear kernel operator of a tensor kernel acts on the second
factor by the second kernel operator applied to the slices.  This is the technical heart of the
tensor-product norm factorisation `ttensor-bil`. -/
theorem bilinKernelOp_tensorKernel_apply {α β γ α' β' γ' : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype α'] [Fintype β'] [Fintype γ']
    (K₁ : γ → α → β → ℂ) (K₂ : γ' → α' → β' → ℂ) (F : α × α' → ℂ) (G : β × β' → ℂ)
    (z : γ × γ') :
    bilinKernelOp (tensorKernel K₁ K₂) F G z
      = ∑ x, ∑ y, K₁ z.1 x y * bilinKernelOp K₂ (slice F x) (slice G y) z.2 := by
  have hL : bilinKernelOp (tensorKernel K₁ K₂) F G z
      = ∑ x : α, ∑ x' : α', ∑ y : β, ∑ y' : β',
          K₁ z.1 x y * K₂ z.2 x' y' * F (x, x') * G (y, y') := by
    simp only [bilinKernelOp, tensorKernel, Fintype.sum_prod_type]
  have hR : (∑ x : α, ∑ y : β, K₁ z.1 x y *
        bilinKernelOp K₂ (slice F x) (slice G y) z.2)
      = ∑ x : α, ∑ x' : α', ∑ y : β, ∑ y' : β',
          K₁ z.1 x y * K₂ z.2 x' y' * F (x, x') * G (y, y') := by
    simp only [bilinKernelOp, slice]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x' _ => ?_)
    refine Finset.sum_congr rfl (fun y _ => ?_)
    exact Finset.sum_congr rfl (fun y' _ => by ring)
  rw [hL, hR]

end

end Work.Analysis.Paraproduct
