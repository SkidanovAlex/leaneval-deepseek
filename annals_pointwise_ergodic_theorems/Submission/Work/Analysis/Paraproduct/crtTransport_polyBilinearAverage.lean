import Mathlib
import Submission.Work.Analysis.Paraproduct.bilinKernelOp_arithAvgKernel
import Submission.Work.Analysis.Concentration.Fiber

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped BigOperators
open Finset

namespace Work.Analysis.Paraproduct

noncomputable section

open Work.Analysis.Concentration
open Polynomial

/-- Interchange of a triple sum over independent finite types: the innermost summation index is
moved to the front, the relative order of the other two being preserved. -/
private lemma sum_swap_inner_to_outer {ι κ ν M : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    [AddCommMonoid M] (f : ι → κ → ν → M) :
    (∑ x : ι, ∑ y : κ, ∑ b : ν, f x y b) = (∑ b : ν, ∑ x : ι, ∑ y : κ, f x y b) := by
  have s1 : (∑ x : ι, ∑ y : κ, ∑ b : ν, f x y b)
      = ∑ y : κ, ∑ x : ι, ∑ b : ν, f x y b := Finset.sum_comm
  have s2 : (∑ y : κ, ∑ x : ι, ∑ b : ν, f x y b)
      = ∑ y : κ, ∑ b : ν, ∑ x : ι, f x y b :=
    Finset.sum_congr rfl (fun y _ => Finset.sum_comm)
  have s3 : (∑ y : κ, ∑ b : ν, ∑ x : ι, f x y b)
      = ∑ b : ν, ∑ y : κ, ∑ x : ι, f x y b := Finset.sum_comm
  have s4 : (∑ b : ν, ∑ y : κ, ∑ x : ι, f x y b)
      = ∑ b : ν, ∑ x : ι, ∑ y : κ, f x y b :=
    Finset.sum_congr rfl (fun b _ => Finset.sum_comm)
  rw [s1, s2, s3, s4]

/-- Reindexing a sum over `ZMod (m * n)` along the inverse Chinese-remainder isomorphism. -/
private lemma crt_sum_reindex {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n) {γ : Type*}
    [AddCommMonoid γ] (G : ZMod (m * n) → γ) :
    (∑ u : ZMod (m * n), G u)
      = ∑ v : ZMod m × ZMod n, G ((ZMod.chineseRemainder h).symm v) := by
  rw [← Equiv.sum_comp ((ZMod.chineseRemainder h).symm.toEquiv) G]
  exact Finset.sum_congr rfl (fun i _ => rfl)

/-- The first component of the Chinese-remainder isomorphism is the reduction modulo `m`. -/
private lemma crt_fst_apply {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n)
    (x : ZMod (m * n)) :
    (ZMod.chineseRemainder h x).1 = ZMod.castHom (dvd_mul_right m n) (ZMod m) x := by
  simp [ZMod.chineseRemainder, ZMod.castHom_apply, Prod.fst_zmod_cast]

/-- The second component of the Chinese-remainder isomorphism is the reduction modulo `n`. -/
private lemma crt_snd_apply {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n)
    (x : ZMod (m * n)) :
    (ZMod.chineseRemainder h x).2 = ZMod.castHom (dvd_mul_left n m) (ZMod n) x := by
  simp [ZMod.chineseRemainder, ZMod.castHom_apply, Prod.snd_zmod_cast]

/-- Polynomial evaluation is transported by the Chinese-remainder isomorphism to the pair of
the evaluations modulo `m` and modulo `n`. -/
private lemma crt_polyEval {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n)
    (P : Polynomial ℤ) (v : ZMod m × ZMod n) :
    ZMod.chineseRemainder h (polyEvalZMod P (m * n) ((ZMod.chineseRemainder h).symm v))
      = (polyEvalZMod P m v.1, polyEvalZMod P n v.2) := by
  apply Prod.ext
  · show (ZMod.chineseRemainder h (polyEvalZMod P (m * n) ((ZMod.chineseRemainder h).symm v))).1
      = polyEvalZMod P m v.1
    rw [crt_fst_apply h,
      polyEvalZMod_castHom P (dvd_mul_right m n) ((ZMod.chineseRemainder h).symm v)]
    rw [← crt_fst_apply h]
    simp
  · show (ZMod.chineseRemainder h (polyEvalZMod P (m * n) ((ZMod.chineseRemainder h).symm v))).2
      = polyEvalZMod P n v.2
    rw [crt_snd_apply h,
      polyEvalZMod_castHom P (dvd_mul_left n m) ((ZMod.chineseRemainder h).symm v)]
    rw [← crt_snd_apply h]
    simp

/-- Subtracting a transported polynomial value: on `ZMod (m * n)` the subtraction of
`P (e.symm v)` from `e.symm z` corresponds to the componentwise subtraction on the product. -/
private lemma crt_sub {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n)
    (P : Polynomial ℤ) (z v : ZMod m × ZMod n) :
    (ZMod.chineseRemainder h).symm z - polyEvalZMod P (m * n) ((ZMod.chineseRemainder h).symm v)
      = (ZMod.chineseRemainder h).symm
          (z.1 - polyEvalZMod P m v.1, z.2 - polyEvalZMod P n v.2) := by
  apply (ZMod.chineseRemainder h).injective
  rw [map_sub, RingEquiv.apply_symm_apply, crt_polyEval h P v, RingEquiv.apply_symm_apply]
  exact Prod.ext rfl rfl

/-- Multiplying a bilinear kernel by a constant multiplies its kernel operator by it. -/
private lemma bilinKernelOp_const_smul {α β γ : Type*} [Fintype α] [Fintype β] (c : ℂ)
    (K : γ → α → β → ℂ) (u : α → ℂ) (v : β → ℂ) (z : γ) :
    bilinKernelOp (fun z x y => c * K z x y) u v z = c * bilinKernelOp K u v z := by
  simp only [bilinKernelOp]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => by ring))

/-- **The arithmetic bilinear average, transported along the Chinese-remainder isomorphism.**
Expanding the average over `ZMod (m * n)` along `e.symm` turns it into the double average over
the two factors `ZMod m` and `ZMod n` of the two transported functions. -/
private theorem polyBilinearAverageZMod_crt_aux (P₁ P₂ : Polynomial ℤ) {m n : ℕ} [NeZero m]
    [NeZero n] (h : m.Coprime n) (F G : ZMod (m * n) → ℂ) (z : ZMod m × ZMod n) :
    polyBilinearAverageZMod P₁ P₂ (m * n) F G ((ZMod.chineseRemainder h).symm z)
      = ∑ a : ZMod m, ∑ b : ZMod n,
          ((m : ℂ)⁻¹ * (n : ℂ)⁻¹) *
            (F ((ZMod.chineseRemainder h).symm
                (z.1 - polyEvalZMod P₁ m a, z.2 - polyEvalZMod P₁ n b)) *
             G ((ZMod.chineseRemainder h).symm
                (z.1 - polyEvalZMod P₂ m a, z.2 - polyEvalZMod P₂ n b))) := by
  have hunfold : polyBilinearAverageZMod P₁ P₂ (m * n) F G ((ZMod.chineseRemainder h).symm z)
      = ((m * n : ℕ) : ℂ)⁻¹ * ∑ u : ZMod (m * n),
          F ((ZMod.chineseRemainder h).symm z - polyEvalZMod P₁ (m * n) u) *
          G ((ZMod.chineseRemainder h).symm z - polyEvalZMod P₂ (m * n) u) := rfl
  rw [hunfold, Nat.cast_mul, mul_inv]
  conv_lhs => rw [Finset.mul_sum]
  rw [crt_sum_reindex h (fun u : ZMod (m * n) =>
        ((m : ℂ)⁻¹ * (n : ℂ)⁻¹) *
          (F ((ZMod.chineseRemainder h).symm z - polyEvalZMod P₁ (m * n) u) *
           G ((ZMod.chineseRemainder h).symm z - polyEvalZMod P₂ (m * n) u)))]
  rw [Fintype.sum_prod_type]
  have hterm : ∀ a : ZMod m, ∀ b : ZMod n,
      ((m : ℂ)⁻¹ * (n : ℂ)⁻¹) *
          (F ((ZMod.chineseRemainder h).symm z -
              polyEvalZMod P₁ (m * n) ((ZMod.chineseRemainder h).symm (a, b))) *
           G ((ZMod.chineseRemainder h).symm z -
              polyEvalZMod P₂ (m * n) ((ZMod.chineseRemainder h).symm (a, b))))
        = ((m : ℂ)⁻¹ * (n : ℂ)⁻¹) *
            (F ((ZMod.chineseRemainder h).symm
                (z.1 - polyEvalZMod P₁ m a, z.2 - polyEvalZMod P₁ n b)) *
             G ((ZMod.chineseRemainder h).symm
                (z.1 - polyEvalZMod P₂ m a, z.2 - polyEvalZMod P₂ n b))) := by
    intro a b
    rw [crt_sub h P₁ z (a, b), crt_sub h P₂ z (a, b)]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hterm a b))]

/-- **The tensor-product kernel operator, expanded.**  The bilinear kernel operator of the
tensor product of the two arithmetic averaging kernels evaluated at any pair of test functions
is the double average of the two test functions over the shifted points of the two factors. -/
private theorem bilinKernelOp_tensor_arithAvg_aux (P₁ P₂ : Polynomial ℤ) {m n : ℕ} [NeZero m]
    [NeZero n] (F' G' : ZMod m × ZMod n → ℂ) (z : ZMod m × ZMod n) :
    bilinKernelOp (tensorKernel (arithAvgKernel P₁ P₂ m) (arithAvgKernel P₁ P₂ n)) F' G' z
      = ∑ a : ZMod m, ∑ b : ZMod n,
          ((m : ℂ)⁻¹ * (n : ℂ)⁻¹) *
            (F' (z.1 - polyEvalZMod P₁ m a, z.2 - polyEvalZMod P₁ n b) *
             G' (z.1 - polyEvalZMod P₂ m a, z.2 - polyEvalZMod P₂ n b)) := by
  rw [bilinKernelOp_tensorKernel_apply (arithAvgKernel P₁ P₂ m) (arithAvgKernel P₁ P₂ n) F' G' z]
  have hinner : ∀ x y : ZMod m,
      bilinKernelOp (arithAvgKernel P₁ P₂ n) (slice F' x) (slice G' y) z.2
        = (n : ℂ)⁻¹ * ∑ b : ZMod n,
            F' (x, z.2 - polyEvalZMod P₁ n b) * G' (y, z.2 - polyEvalZMod P₂ n b) := by
    intro x y
    rw [bilinKernelOp_arithAvgKernel]
    rfl
  have hprod : ∀ x y : ZMod m,
      arithAvgKernel P₁ P₂ m z.1 x y *
          bilinKernelOp (arithAvgKernel P₁ P₂ n) (slice F' x) (slice G' y) z.2
        = arithAvgKernel P₁ P₂ m z.1 x y *
            ((n : ℂ)⁻¹ * ∑ b : ZMod n,
              F' (x, z.2 - polyEvalZMod P₁ n b) * G' (y, z.2 - polyEvalZMod P₂ n b)) := by
    intro x y
    rw [hinner x y]
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => hprod x y))]
  have hxy : ∀ x y : ZMod m,
      arithAvgKernel P₁ P₂ m z.1 x y *
          ((n : ℂ)⁻¹ * ∑ b : ZMod n,
            F' (x, z.2 - polyEvalZMod P₁ n b) * G' (y, z.2 - polyEvalZMod P₂ n b))
        = ∑ b : ZMod n, (n : ℂ)⁻¹ * (arithAvgKernel P₁ P₂ m z.1 x y *
            (F' (x, z.2 - polyEvalZMod P₁ n b) * G' (y, z.2 - polyEvalZMod P₂ n b))) := by
    intro x y
    rw [show arithAvgKernel P₁ P₂ m z.1 x y *
          ((n : ℂ)⁻¹ * ∑ b : ZMod n,
            F' (x, z.2 - polyEvalZMod P₁ n b) * G' (y, z.2 - polyEvalZMod P₂ n b))
        = (n : ℂ)⁻¹ * (arithAvgKernel P₁ P₂ m z.1 x y *
              ∑ b : ZMod n,
                F' (x, z.2 - polyEvalZMod P₁ n b) * G' (y, z.2 - polyEvalZMod P₂ n b))
        from by ring, Finset.mul_sum, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => hxy x y))]
  rw [sum_swap_inner_to_outer]
  have hB : ∀ b : ZMod n,
      (∑ x : ZMod m, ∑ y : ZMod m, (n : ℂ)⁻¹ *
          (arithAvgKernel P₁ P₂ m z.1 x y *
           (F' (x, z.2 - polyEvalZMod P₁ n b) * G' (y, z.2 - polyEvalZMod P₂ n b))))
        = ∑ a : ZMod m, ((m : ℂ)⁻¹ * (n : ℂ)⁻¹) *
            (F' (z.1 - polyEvalZMod P₁ m a, z.2 - polyEvalZMod P₁ n b) *
             G' (z.1 - polyEvalZMod P₂ m a, z.2 - polyEvalZMod P₂ n b)) := by
    intro b
    rw [show (∑ x : ZMod m, ∑ y : ZMod m, (n : ℂ)⁻¹ *
          (arithAvgKernel P₁ P₂ m z.1 x y *
           (F' (x, z.2 - polyEvalZMod P₁ n b) * G' (y, z.2 - polyEvalZMod P₂ n b))))
        = bilinKernelOp (fun w x y => (n : ℂ)⁻¹ * arithAvgKernel P₁ P₂ m w x y)
            (fun x : ZMod m => F' (x, z.2 - polyEvalZMod P₁ n b))
            (fun y : ZMod m => G' (y, z.2 - polyEvalZMod P₂ n b)) z.1 from by
          simp only [bilinKernelOp]
          exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => by ring))]
    rw [bilinKernelOp_const_smul, bilinKernelOp_arithAvgKernel]
    show (n : ℂ)⁻¹ * ((m : ℂ)⁻¹ * ∑ a : ZMod m,
          F' (z.1 - polyEvalZMod P₁ m a, z.2 - polyEvalZMod P₁ n b) *
          G' (z.1 - polyEvalZMod P₂ m a, z.2 - polyEvalZMod P₂ n b))
        = ∑ a : ZMod m, ((m : ℂ)⁻¹ * (n : ℂ)⁻¹) *
          (F' (z.1 - polyEvalZMod P₁ m a, z.2 - polyEvalZMod P₁ n b) *
           G' (z.1 - polyEvalZMod P₂ m a, z.2 - polyEvalZMod P₂ n b))
    rw [show (n : ℂ)⁻¹ * ((m : ℂ)⁻¹ * ∑ a : ZMod m,
          F' (z.1 - polyEvalZMod P₁ m a, z.2 - polyEvalZMod P₁ n b) *
          G' (z.1 - polyEvalZMod P₂ m a, z.2 - polyEvalZMod P₂ n b))
        = ((m : ℂ)⁻¹ * (n : ℂ)⁻¹) * ∑ a : ZMod m,
          F' (z.1 - polyEvalZMod P₁ m a, z.2 - polyEvalZMod P₁ n b) *
          G' (z.1 - polyEvalZMod P₂ m a, z.2 - polyEvalZMod P₂ n b) from by ring,
      Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun b _ => hB b)]
  rw [Finset.sum_comm]

theorem crtTransport_polyBilinearAverage (P₁ P₂ : Polynomial ℤ) {m n : ℕ} [NeZero m]
    [NeZero n] (h : m.Coprime n) (F G : ZMod (m * n) → ℂ) :
    (fun z : ZMod m × ZMod n =>
        Work.Analysis.Concentration.polyBilinearAverageZMod P₁ P₂ (m * n) F G
          ((ZMod.chineseRemainder h).symm z))
      = bilinKernelOp (tensorKernel (arithAvgKernel P₁ P₂ m) (arithAvgKernel P₁ P₂ n))
          (fun z => F ((ZMod.chineseRemainder h).symm z))
          (fun z => G ((ZMod.chineseRemainder h).symm z)) := by
  funext z
  rw [polyBilinearAverageZMod_crt_aux P₁ P₂ h F G z,
    bilinKernelOp_tensor_arithAvg_aux P₁ P₂ (fun w => F ((ZMod.chineseRemainder h).symm w))
      (fun w => G ((ZMod.chineseRemainder h).symm w)) z]

end

end Work.Analysis.Paraproduct
