import Mathlib
import Submission.Work.Analysis.Paraproduct.bilinKernelOp_arithAvgKernel
import Submission.Work.Analysis.Paraproduct.bilinKernelOp_tensorKernel_le

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `ttensor-bil` for the arithmetic bilinear averaging operators (`bilinearAverageLq_prod`)

This module proves the tensor-product factorisation `ttensor-bil` of Krause--Mirek--Tao
(*Pointwise ergodic theorems for non-conventional bilinear polynomial averages*, Annals 195
(2022), Section 10) for the arithmetic bilinear averaging operators
`A^{P₁,P₂}_{ℤ/Qℤ} : (f,g) ↦ (x ↦ Q⁻¹ ∑_n f (x - P₁(n)) g (x - P₂(n)))`:

if `BilinearAverageLq P m q C₁` and `BilinearAverageLq P n q C₂`, then the operator on
`ℤ/mℤ × ℤ/nℤ` obtained as the tensor product of the two averaging operators satisfies the
same `L² × L² → L^q` estimate with constant `C₁ * C₂`.

The proof is the assembly of three previously proved pieces:

* `bilinKernelOp_arithAvgKernel` identifies the arithmetic averaging operator with the
  bilinear kernel operator of the kernel `arithAvgKernel X P Q`;
* `arithAvgKernelReal`/`arithAvgKernelReal_cast` exhibit `arithAvgKernel X P Q` as the cast
  of a **non-negative real** kernel (the structural hypothesis of the tensor-norm estimate);
* `bilinKernelOp_tensorKernel_le` (`ttensor-bil`, upper bound) then factors the norm.
-/

namespace Work.Analysis.Paraproduct

open Work.Analysis.Concentration

noncomputable section

/-- The arithmetic bilinear averaging kernel `arithAvgKernel`, read as a **real** kernel: the
same formula with the two `0`/`1` "deltas" evaluated in `ℝ` rather than in `ℂ`.  It is
non-negative, and `arithAvgKernelReal_cast` shows that `arithAvgKernel` is its cast to `ℂ`. -/
noncomputable def arithAvgKernelReal (P₁ P₂ : Polynomial ℤ) (Q : ℕ) [NeZero Q] :
    ZMod Q → ZMod Q → ZMod Q → ℝ :=
  fun x y w => (Q : ℝ)⁻¹ * ∑ n : ZMod Q,
    (if x - polyEvalZMod P₁ Q n = y then (1 : ℝ) else 0) *
      (if x - polyEvalZMod P₂ Q n = w then (1 : ℝ) else 0)

/-- The real kernel `arithAvgKernelReal` is non-negative everywhere. -/
lemma arithAvgKernelReal_nonneg (P₁ P₂ : Polynomial ℤ) (Q : ℕ) [NeZero Q]
    (x y w : ZMod Q) : 0 ≤ arithAvgKernelReal P₁ P₂ Q x y w := by
  refine mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg Q)) (Finset.sum_nonneg ?_)
  intro n _
  refine mul_nonneg ?_ ?_ <;> split_ifs <;> norm_num

/-- The arithmetic averaging kernel `arithAvgKernel` is the cast to `ℂ` of the non-negative
real kernel `arithAvgKernelReal`. -/
lemma arithAvgKernelReal_cast (P₁ P₂ : Polynomial ℤ) (Q : ℕ) [NeZero Q]
    (x y w : ZMod Q) :
    arithAvgKernel P₁ P₂ Q x y w = (arithAvgKernelReal P₁ P₂ Q x y w : ℂ) := by
  have hterm : ∀ n : ZMod Q,
      Complex.ofReal ((if x - polyEvalZMod P₁ Q n = y then (1 : ℝ) else 0) *
          (if x - polyEvalZMod P₂ Q n = w then (1 : ℝ) else 0))
        = (if x - polyEvalZMod P₁ Q n = y then (1 : ℂ) else 0) *
            (if x - polyEvalZMod P₂ Q n = w then (1 : ℂ) else 0) := by
    intro n
    rw [Complex.ofReal_mul]
    split_ifs <;> simp
  simp only [arithAvgKernel, arithAvgKernelReal]
  rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_sum]
  refine congrArg (fun t => (Q : ℂ)⁻¹ * t) (Finset.sum_congr rfl fun n _ => (hterm n).symm)

/-- **`ttensor-bil` for the arithmetic bilinear averaging operators.**  The tensor product of the
arithmetic averaging operators over `ℤ/mℤ` and `ℤ/nℤ` (with `P₁ = X`, `P₂ = P`) inherits the
`L² × L² → L^q` bound with the product of the two constants. -/
theorem bilinearAverageLq_prod (P : Polynomial ℤ) {m n : ℕ} [NeZero m] [NeZero n] {q C₁ C₂ : ℝ}
    (hq : 1 ≤ q)
    (h₁ : Work.Analysis.Concentration.BilinearAverageLq P m q C₁)
    (h₂ : Work.Analysis.Concentration.BilinearAverageLq P n q C₂) :
    BilinearAverageLqProd P m n q (C₁ * C₂) := by
  have h₁' : ∀ f g : ZMod m → ℂ,
      lpNormFin (ZMod m) q (bilinKernelOp (arithAvgKernel Polynomial.X P m) f g)
        ≤ C₁ * lpNormFin (ZMod m) 2 f * lpNormFin (ZMod m) 2 g := by
    intro f g
    rw [bilinKernelOp_arithAvgKernel]
    rw [lpNormFin_zmod m q (polyBilinearAverageZMod Polynomial.X P m f g)]
    rw [lpNormFin_zmod m 2 f, lpNormFin_zmod m 2 g]
    exact h₁ f g
  have h₂' : ∀ f g : ZMod n → ℂ,
      lpNormFin (ZMod n) q (bilinKernelOp (arithAvgKernel Polynomial.X P n) f g)
        ≤ C₂ * lpNormFin (ZMod n) 2 f * lpNormFin (ZMod n) 2 g := by
    intro f g
    rw [bilinKernelOp_arithAvgKernel]
    rw [lpNormFin_zmod n q (polyBilinearAverageZMod Polynomial.X P n f g)]
    rw [lpNormFin_zmod n 2 f, lpNormFin_zmod n 2 g]
    exact h₂ f g
  exact bilinKernelOp_tensorKernel_le (p := 2) (q := 2) (r := q) (hp := by norm_num)
    (hq := by norm_num) (hr := hq) (K₁ := arithAvgKernel Polynomial.X P m)
    (K₂ := arithAvgKernel Polynomial.X P n)
    (hK₁ := ⟨arithAvgKernelReal Polynomial.X P m, arithAvgKernelReal_nonneg Polynomial.X P m,
      arithAvgKernelReal_cast Polynomial.X P m⟩)
    (h₁ := h₁') (h₂ := h₂')

end

end Work.Analysis.Paraproduct
