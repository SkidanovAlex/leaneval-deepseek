import Mathlib
import Submission.Work.Analysis.Paraproduct.CrtFactor

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The arithmetic averaging operator is the bilinear kernel operator of its kernel

This file identifies the arithmetic (polynomial) bilinear averaging operator of
Krause--Mirek--Tao, *Pointwise ergodic theorems for non-conventional bilinear polynomial
averages*, Annals of Math. **195** (2022), Section 10, with the bilinear kernel operator
`bilinKernelOp` of the kernel `arithAvgKernel`:

`A(f,g)(x) = Q⁻¹ ∑_{n} f (x - P₁(n)) g (x - P₂(n))
          = ∑_{u,w} (Q⁻¹ ∑_{n} [x - P₁(n) = u] [x - P₂(n) = w]) f u g w`.

The content is a two-fold interchange of summation: distribute the product `f u · g w` into the
sum over `n`, swap the outer sums `∑_u ∑_w` with `∑_n` (finite sums over `ℤ/Qℤ` commute), and
evaluate the two resulting "delta" sums `∑_u [x - P₁(n) = u] f u = f (x - P₁(n))`.

This is the bridge that lets the (non-negative) tensor-norm factorisation
`bilinKernelOp_tensorKernel_le` be applied to the arithmetic averaging operators.

## Main result

* `bilinKernelOp_arithAvgKernel` : `bilinKernelOp (arithAvgKernel P₁ P₂ Q) f g` is the
  arithmetic bilinear averaging operator `polyBilinearAverageZMod P₁ P₂ Q f g`.
-/

namespace Work.Analysis.Paraproduct

open Work.Analysis.Concentration

/-- A `ℂ`-valued `0`/`1` "delta": summing `(if c = u then 1 else 0) * F u` over `u` picks out
`F c`. -/
private lemma sum_boole_univ {Q : ℕ} [NeZero Q] (c : ZMod Q) (F : ZMod Q → ℂ) :
    ∑ u : ZMod Q, (if c = u then (1 : ℂ) else 0) * F u = F c := by
  rw [Finset.sum_boole_mul]
  simp

/-- Interchange of a triple sum over `ℤ/Qℤ`: `∑_u ∑_w ∑_n = ∑_n ∑_u ∑_w`.
Two applications of `Finset.sum_comm` (the inner pair, then the outer pair). -/
private lemma sum_comm3 {Q : ℕ} [NeZero Q] (T : ZMod Q → ZMod Q → ZMod Q → ℂ) :
    (∑ u : ZMod Q, ∑ w : ZMod Q, ∑ n : ZMod Q, T n u w)
      = (∑ n : ZMod Q, ∑ u : ZMod Q, ∑ w : ZMod Q, T n u w) := by
  have s1 : (∑ u : ZMod Q, ∑ w : ZMod Q, ∑ n : ZMod Q, T n u w)
      = (∑ u : ZMod Q, ∑ n : ZMod Q, ∑ w : ZMod Q, T n u w) :=
    Finset.sum_congr rfl fun u _ => Finset.sum_comm
  have s2 : (∑ u : ZMod Q, ∑ n : ZMod Q, ∑ w : ZMod Q, T n u w)
      = (∑ n : ZMod Q, ∑ u : ZMod Q, ∑ w : ZMod Q, T n u w) := Finset.sum_comm
  exact s1.trans s2

/-- The kernel form of the arithmetic averaging operator is the interchanged sum: distribute the
factors `f u`, `g w` into the inner sum over `n`, then move `∑_n` to the outside. -/
private lemma arith_kernel_distrib {Q : ℕ} [NeZero Q] (c : ℂ) (f g : ZMod Q → ℂ)
    (A B : ZMod Q → ZMod Q → ℂ) :
    (∑ u : ZMod Q, ∑ w : ZMod Q, (c * ∑ n : ZMod Q, A n u * B n w) * f u * g w)
      = (∑ n : ZMod Q, ∑ u : ZMod Q, ∑ w : ZMod Q,
          c * ((A n u * f u) * (B n w * g w))) := by
  have hdist : ∀ u w : ZMod Q,
      ((c * ∑ n : ZMod Q, A n u * B n w) * f u * g w)
        = (∑ n : ZMod Q, c * ((A n u * f u) * (B n w * g w))) := by
    intro u w
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun n _ => by ring
  calc (∑ u : ZMod Q, ∑ w : ZMod Q, (c * ∑ n : ZMod Q, A n u * B n w) * f u * g w)
      = (∑ u : ZMod Q, ∑ w : ZMod Q, ∑ n : ZMod Q,
          c * ((A n u * f u) * (B n w * g w))) :=
        Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => hdist u w
    _ = (∑ n : ZMod Q, ∑ u : ZMod Q, ∑ w : ZMod Q,
          c * ((A n u * f u) * (B n w * g w))) :=
        sum_comm3 (fun n u w => c * ((A n u * f u) * (B n w * g w)))

/-- Factorisation of a triple sum with a constant factor: the double `(u,w)`-sum of the product
`p n u · q n w` separates as the product of the two sums. -/
private lemma triple_factor {Q : ℕ} [NeZero Q] (c : ℂ) (p q : ZMod Q → ZMod Q → ℂ) :
    (∑ n : ZMod Q, ∑ u : ZMod Q, ∑ w : ZMod Q, c * (p n u * q n w))
      = c * (∑ n : ZMod Q, (∑ u : ZMod Q, p n u) * (∑ w : ZMod Q, q n w)) := by
  have hper : ∀ n : ZMod Q, (∑ u : ZMod Q, ∑ w : ZMod Q, c * (p n u * q n w))
      = c * ((∑ u : ZMod Q, p n u) * (∑ w : ZMod Q, q n w)) := by
    intro n
    have h1 : (∑ u : ZMod Q, ∑ w : ZMod Q, c * (p n u * q n w))
        = (∑ u : ZMod Q, c * (∑ w : ZMod Q, p n u * q n w)) :=
      Finset.sum_congr rfl fun u _ =>
        (Finset.mul_sum (Finset.univ : Finset (ZMod Q))
          (fun w : ZMod Q => p n u * q n w) c).symm
    have h2 : (∑ u : ZMod Q, c * (∑ w : ZMod Q, p n u * q n w))
        = c * (∑ u : ZMod Q, ∑ w : ZMod Q, p n u * q n w) :=
      (Finset.mul_sum (Finset.univ : Finset (ZMod Q))
        (fun u : ZMod Q => ∑ w : ZMod Q, p n u * q n w) c).symm
    have h3 : (∑ u : ZMod Q, ∑ w : ZMod Q, p n u * q n w)
        = (∑ u : ZMod Q, p n u) * (∑ w : ZMod Q, q n w) :=
      (Finset.sum_mul_sum (Finset.univ : Finset (ZMod Q)) (Finset.univ : Finset (ZMod Q))
        (fun u : ZMod Q => p n u) (fun w : ZMod Q => q n w)).symm
    rw [h1, h2, h3]
  calc (∑ n : ZMod Q, ∑ u : ZMod Q, ∑ w : ZMod Q, c * (p n u * q n w))
      = (∑ n : ZMod Q, c * ((∑ u : ZMod Q, p n u) * (∑ w : ZMod Q, q n w))) :=
        Finset.sum_congr rfl fun n _ => hper n
    _ = c * (∑ n : ZMod Q, (∑ u : ZMod Q, p n u) * (∑ w : ZMod Q, q n w)) :=
        (Finset.mul_sum (Finset.univ : Finset (ZMod Q))
          (fun n : ZMod Q => (∑ u : ZMod Q, p n u) * (∑ w : ZMod Q, q n w)) c).symm

/-- **The kernel of the arithmetic averaging operator is that operator.**  The bilinear kernel
operator of `arithAvgKernel P₁ P₂ Q` is exactly the arithmetic bilinear polynomial average
`polyBilinearAverageZMod P₁ P₂ Q` of Section 10 of Krause--Mirek--Tao. -/
theorem bilinKernelOp_arithAvgKernel (P₁ P₂ : Polynomial ℤ) (Q : ℕ) [NeZero Q]
    (f g : ZMod Q → ℂ) :
    bilinKernelOp (arithAvgKernel P₁ P₂ Q) f g
      = Work.Analysis.Concentration.polyBilinearAverageZMod P₁ P₂ Q f g := by
  funext x
  show (∑ u : ZMod Q, ∑ w : ZMod Q,
        ((Q : ℂ)⁻¹ * ∑ n : ZMod Q,
          (if x - polyEvalZMod P₁ Q n = u then (1 : ℂ) else 0) *
          (if x - polyEvalZMod P₂ Q n = w then (1 : ℂ) else 0)) * f u * g w)
     = (Q : ℂ)⁻¹ * ∑ n : ZMod Q,
        f (x - polyEvalZMod P₁ Q n) * g (x - polyEvalZMod P₂ Q n)
  have step1 : (∑ u : ZMod Q, ∑ w : ZMod Q,
        ((Q : ℂ)⁻¹ * ∑ n : ZMod Q,
          (if x - polyEvalZMod P₁ Q n = u then (1 : ℂ) else 0) *
          (if x - polyEvalZMod P₂ Q n = w then (1 : ℂ) else 0)) * f u * g w)
      = (∑ n : ZMod Q, ∑ u : ZMod Q, ∑ w : ZMod Q, (Q : ℂ)⁻¹ *
          (((if x - polyEvalZMod P₁ Q n = u then (1 : ℂ) else 0) * f u) *
           ((if x - polyEvalZMod P₂ Q n = w then (1 : ℂ) else 0) * g w))) :=
    arith_kernel_distrib (Q : ℂ)⁻¹ f g
      (fun n u => (if x - polyEvalZMod P₁ Q n = u then (1 : ℂ) else 0))
      (fun n w => (if x - polyEvalZMod P₂ Q n = w then (1 : ℂ) else 0))
  rw [step1]
  have step2 : (∑ n : ZMod Q, ∑ u : ZMod Q, ∑ w : ZMod Q, (Q : ℂ)⁻¹ *
          (((if x - polyEvalZMod P₁ Q n = u then (1 : ℂ) else 0) * f u) *
           ((if x - polyEvalZMod P₂ Q n = w then (1 : ℂ) else 0) * g w)))
      = (Q : ℂ)⁻¹ * (∑ n : ZMod Q,
          (∑ u : ZMod Q, (if x - polyEvalZMod P₁ Q n = u then (1 : ℂ) else 0) * f u) *
          (∑ w : ZMod Q, (if x - polyEvalZMod P₂ Q n = w then (1 : ℂ) else 0) * g w)) :=
    triple_factor (Q : ℂ)⁻¹
      (fun n u => (if x - polyEvalZMod P₁ Q n = u then (1 : ℂ) else 0) * f u)
      (fun n w => (if x - polyEvalZMod P₂ Q n = w then (1 : ℂ) else 0) * g w)
  rw [step2]
  have hfac : ∀ n : ZMod Q,
      (∑ u : ZMod Q, (if x - polyEvalZMod P₁ Q n = u then (1 : ℂ) else 0) * f u) *
      (∑ w : ZMod Q, (if x - polyEvalZMod P₂ Q n = w then (1 : ℂ) else 0) * g w)
        = f (x - polyEvalZMod P₁ Q n) * g (x - polyEvalZMod P₂ Q n) := by
    intro n
    rw [sum_boole_univ, sum_boole_univ]
  have step3 : (Q : ℂ)⁻¹ * (∑ n : ZMod Q,
          (∑ u : ZMod Q, (if x - polyEvalZMod P₁ Q n = u then (1 : ℂ) else 0) * f u) *
          (∑ w : ZMod Q, (if x - polyEvalZMod P₂ Q n = w then (1 : ℂ) else 0) * g w))
      = (Q : ℂ)⁻¹ * (∑ n : ZMod Q,
          f (x - polyEvalZMod P₁ Q n) * g (x - polyEvalZMod P₂ Q n)) :=
    congrArg (fun t => (Q : ℂ)⁻¹ * t) (Finset.sum_congr rfl fun n _ => hfac n)
  rw [step3]

end Work.Analysis.Paraproduct
