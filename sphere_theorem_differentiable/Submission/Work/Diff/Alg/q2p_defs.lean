import Mathlib
import Submission.Diff.Interfaces

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Algebraic core for `Work.Diff.Alg.quarter_to_pic2`

This module sets up the quartic form `EFun` whose nonnegativity is exactly the `PIC2` condition of
`Submission.Diff.Alg`, together with the elementary symmetry/multilinearity API of `R4`, and the
dictionary between real four-tuples and pairs of complex vectors.
-/

namespace Work.Diff.Alg.Q2P

open Submission.Diff.Alg Finset

variable {n : ℕ}

/-- The integrand of the `PIC2` condition (real form of the isotropic curvature of `ζ = x+iy`,
`η = z+iw`). -/
noncomputable def EFun (R : Curv4 n) (x y z w : Fin n → ℝ) : ℝ :=
  R4 R x z x z + R4 R x w x w + R4 R y z y z + R4 R y w y w - 2 * R4 R x y z w

theorem inPIC2_iff (R : Curv4 n) : InPIC2 R ↔ ∀ x y z w : Fin n → ℝ, 0 ≤ EFun R x y z w :=
  Iff.rfl

/-- Four mutually orthonormal vectors of `ℝⁿ`. -/
def IsON4 (e1 e2 e3 e4 : Fin n → ℝ) : Prop :=
  dot e1 e1 = 1 ∧ dot e2 e2 = 1 ∧ dot e3 e3 = 1 ∧ dot e4 e4 = 1 ∧
    dot e1 e2 = 0 ∧ dot e1 e3 = 0 ∧ dot e1 e4 = 0 ∧ dot e2 e3 = 0 ∧ dot e2 e4 = 0 ∧
    dot e3 e4 = 0

/-- Four mutually orthogonal (not necessarily unit) vectors. -/
def PairwiseOrth (x y z w : Fin n → ℝ) : Prop :=
  dot x y = 0 ∧ dot x z = 0 ∧ dot x w = 0 ∧ dot y z = 0 ∧ dot y w = 0 ∧ dot z w = 0

/-! ## Multilinearity of `R4` -/

theorem R4_add₁ (R : Curv4 n) (a a' b c d : Fin n → ℝ) :
    R4 R (a + a') b c d = R4 R a b c d + R4 R a' b c d := by
  simp only [R4, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem R4_add₂ (R : Curv4 n) (a b b' c d : Fin n → ℝ) :
    R4 R a (b + b') c d = R4 R a b c d + R4 R a b' c d := by
  simp only [R4, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem R4_add₃ (R : Curv4 n) (a b c c' d : Fin n → ℝ) :
    R4 R a b (c + c') d = R4 R a b c d + R4 R a b c' d := by
  simp only [R4, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem R4_add₄ (R : Curv4 n) (a b c d d' : Fin n → ℝ) :
    R4 R a b c (d + d') = R4 R a b c d + R4 R a b c d' := by
  simp only [R4, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem R4_smul₁ (R : Curv4 n) (t : ℝ) (a b c d : Fin n → ℝ) :
    R4 R (t • a) b c d = t * R4 R a b c d := by
  simp only [R4, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro l _
  ring

theorem R4_smul₂ (R : Curv4 n) (t : ℝ) (a b c d : Fin n → ℝ) :
    R4 R a (t • b) c d = t * R4 R a b c d := by
  simp only [R4, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro l _
  ring

theorem R4_smul₃ (R : Curv4 n) (t : ℝ) (a b c d : Fin n → ℝ) :
    R4 R a b (t • c) d = t * R4 R a b c d := by
  simp only [R4, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro l _
  ring

theorem R4_smul₄ (R : Curv4 n) (t : ℝ) (a b c d : Fin n → ℝ) :
    R4 R a b c (t • d) = t * R4 R a b c d := by
  simp only [R4, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro l _
  ring

theorem R4_zero₁ (R : Curv4 n) (b c d : Fin n → ℝ) : R4 R 0 b c d = 0 := by
  have := R4_smul₁ R 0 (0 : Fin n → ℝ) b c d
  simpa using this

theorem R4_neg₁ (R : Curv4 n) (a b c d : Fin n → ℝ) : R4 R (-a) b c d = - R4 R a b c d := by
  have := R4_smul₁ R (-1) a b c d
  simpa using this

/-! ## Index reordering lemmas for four-fold sums -/

theorem sum_swap2 (g : Fin n → Fin n → ℝ) : (∑ k, ∑ l, g k l) = ∑ k, ∑ l, g l k := by
  rw [Finset.sum_comm]

theorem sum4_swap12 (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, F i j k l) = ∑ i, ∑ j, ∑ k, ∑ l, F j i k l := by
  rw [Finset.sum_comm]

theorem sum4_swap34 (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, F i j k l) = ∑ i, ∑ j, ∑ k, ∑ l, F i j l k := by
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  exact sum_swap2 (fun k l => F i j k l)

theorem sum4_swap23 (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, F i j k l) = ∑ i, ∑ j, ∑ k, ∑ l, F i k j l := by
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]

/-- Cyclic shift `(i,j,k,l) ↦ (j,k,i,l)` of the summation variables. -/
theorem sum4_cycle (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, F i j k l) = ∑ i, ∑ j, ∑ k, ∑ l, F j k i l := by
  rw [sum4_swap23 F]
  exact sum4_swap12 (fun i j k l => F i k j l)

/-- Cyclic shift `(i,j,k,l) ↦ (k,i,j,l)` of the summation variables. -/
theorem sum4_cycle2 (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, F i j k l) = ∑ i, ∑ j, ∑ k, ∑ l, F k i j l := by
  rw [sum4_cycle F]
  exact sum4_cycle (fun i j k l => F j k i l)

theorem block_swap (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, F i j k l) = ∑ k, ∑ l, ∑ i, ∑ j, F i j k l := by
  have h1 : (∑ p : Fin n × Fin n, ∑ q : Fin n × Fin n, F p.1 p.2 q.1 q.2)
      = ∑ i, ∑ j, ∑ k, ∑ l, F i j k l := by
    rw [Fintype.sum_prod_type]; simp only [Fintype.sum_prod_type]
  have h2 : (∑ p : Fin n × Fin n, ∑ q : Fin n × Fin n, F p.1 p.2 q.1 q.2)
      = ∑ k, ∑ l, ∑ i, ∑ j, F i j k l := by
    rw [Finset.sum_comm]
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type]
  exact h1.symm.trans h2

theorem block_rename (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, F i j k l) = ∑ i, ∑ j, ∑ k, ∑ l, F k l i j := by
  rw [block_swap]

/-! ## Symmetry lemmas for algebraic curvature tensors -/

theorem R4_antisym₁₂ (R : Curv4 n) (hR : IsAlgCurv R) (x y z w : Fin n → ℝ) :
    R4 R y x z w = - R4 R x y z w := by
  calc R4 R y x z w = ∑ i, ∑ j, ∑ k, ∑ l, R i j k l * y i * x j * z k * w l := rfl
    _ = ∑ i, ∑ j, ∑ k, ∑ l, R j i k l * y j * x i * z k * w l := sum4_swap12 _
    _ = ∑ i, ∑ j, ∑ k, ∑ l, -(R i j k l * x i * y j * z k * w l) := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro k _
        apply Finset.sum_congr rfl; intro l _
        rw [hR.1 i j k l]; ring
    _ = - R4 R x y z w := by
        simp only [R4, Finset.sum_neg_distrib]

/-- Antisymmetry of an algebraic curvature tensor in the last two slots. -/
theorem IsAlgCurv_antisym₃₄ {R : Curv4 n} (hR : IsAlgCurv R) (i j k l : Fin n) :
    R i j l k = - R i j k l := by
  rw [← hR.2.1 i j l k, hR.1 k l i j, hR.2.1 i j k l]

theorem R4_antisym₃₄ (R : Curv4 n) (hR : IsAlgCurv R) (x y z w : Fin n → ℝ) :
    R4 R x y w z = - R4 R x y z w := by
  calc R4 R x y w z = ∑ i, ∑ j, ∑ k, ∑ l, R i j k l * x i * y j * w k * z l := rfl
    _ = ∑ i, ∑ j, ∑ k, ∑ l, R i j l k * x i * y j * w l * z k := sum4_swap34 _
    _ = ∑ i, ∑ j, ∑ k, ∑ l, -(R i j k l * x i * y j * z k * w l) := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro k _
        apply Finset.sum_congr rfl; intro l _
        rw [IsAlgCurv_antisym₃₄ hR i j k l]; ring
    _ = - R4 R x y z w := by
        simp only [R4, Finset.sum_neg_distrib]

theorem R4_pair_symm (R : Curv4 n) (hR : IsAlgCurv R) (x y z w : Fin n → ℝ) :
    R4 R z w x y = R4 R x y z w := by
  calc R4 R z w x y = ∑ i, ∑ j, ∑ k, ∑ l, R i j k l * z i * w j * x k * y l := rfl
    _ = ∑ i, ∑ j, ∑ k, ∑ l, R k l i j * z i * w j * x k * y l := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro k _
        apply Finset.sum_congr rfl; intro l _
        rw [← hR.2.1 i j k l]
    _ = ∑ i, ∑ j, ∑ k, ∑ l, R i j k l * z k * w l * x i * y j := block_rename _
    _ = R4 R x y z w := by
        simp only [R4]
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro k _
        apply Finset.sum_congr rfl; intro l _
        ring

theorem R4_self₁ (R : Curv4 n) (hR : IsAlgCurv R) (x y z : Fin n → ℝ) :
    R4 R x x y z = 0 := by
  have h := R4_antisym₁₂ R hR x x y z
  linarith [h]

theorem R4_self₂ (R : Curv4 n) (hR : IsAlgCurv R) (x y z : Fin n → ℝ) :
    R4 R x y z z = 0 := by
  have h := R4_antisym₃₄ R hR x y z z
  linarith [h]

theorem R4_exchange_yxyx (R : Curv4 n) (hR : IsAlgCurv R) (x y : Fin n → ℝ) :
    R4 R y x y x = R4 R x y x y := by
  have h1 := R4_antisym₁₂ R hR y x y x
  have h2 := R4_antisym₃₄ R hR x y x y
  linarith

/-! ## Complex vectors and the dictionary -/

/-- Real part of a complex vector. -/
def cRe (z : Fin n → ℂ) : Fin n → ℝ := fun i => (z i).re

/-- Imaginary part of a complex vector. -/
def cIm (z : Fin n → ℂ) : Fin n → ℝ := fun i => (z i).im

/-- Hermitian pairing `∑ zᵢ conj(wᵢ)`. -/
noncomputable def cHerm (z w : Fin n → ℂ) : ℂ := ∑ i, z i * star (w i)

/-- Complex bilinear pairing `∑ zᵢ wᵢ`. -/
noncomputable def cBil (z w : Fin n → ℂ) : ℂ := ∑ i, z i * w i

/-- Complex linear combination `a • z + b • w`. -/
def comb (a b : ℂ) (z w : Fin n → ℂ) : Fin n → ℂ := fun i => a * z i + b * w i

/-- `EFun` on complex vectors: `EFunC R z w = EFun R (Re z) (Im z) (Re w) (Im w)`. -/
noncomputable def EFunC (R : Curv4 n) (z w : Fin n → ℂ) : ℝ :=
  EFun R (cRe z) (cIm z) (cRe w) (cIm w)

theorem inPIC2_iff_c (R : Curv4 n) : InPIC2 R ↔ ∀ z w : Fin n → ℂ, 0 ≤ EFunC R z w := by
  rw [inPIC2_iff]
  constructor
  · intro h z w; exact h (cRe z) (cIm z) (cRe w) (cIm w)
  · intro h x y z w
    have h1 : cRe (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) = x := by ext i; simp [cRe]
    have h2 : cIm (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) = y := by ext i; simp [cIm]
    have h3 : cRe (fun i => (z i : ℂ) + (w i : ℂ) * Complex.I) = z := by ext i; simp [cRe]
    have h4 : cIm (fun i => (z i : ℂ) + (w i : ℂ) * Complex.I) = w := by ext i; simp [cIm]
    have := h (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)
      (fun i => (z i : ℂ) + (w i : ℂ) * Complex.I)
    rw [EFunC, h1, h2, h3, h4] at this
    exact this

@[simp] theorem cRe_comb (a b : ℂ) (z w : Fin n → ℂ) :
    cRe (comb a b z w) = a.re • cRe z - a.im • cIm z + b.re • cRe w - b.im • cIm w := by
  ext i
  simp only [cRe, cIm, comb, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Complex.add_re, Complex.mul_re]
  ring

@[simp] theorem cIm_comb (a b : ℂ) (z w : Fin n → ℂ) :
    cIm (comb a b z w) = a.im • cRe z + a.re • cIm z + b.im • cRe w + b.re • cIm w := by
  ext i
  simp only [cRe, cIm, comb, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Complex.add_im, Complex.mul_im]
  ring

/-! ## Component form of the complex pairings -/

theorem cHerm_re (z w : Fin n → ℂ) :
    (cHerm z w).re = dot (cRe z) (cRe w) + dot (cIm z) (cIm w) := by
  simp only [cHerm, dot, cRe, cIm, Complex.star_def, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, Complex.re_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  ring

theorem cHerm_im (z w : Fin n → ℂ) :
    (cHerm z w).im = dot (cIm z) (cRe w) - dot (cRe z) (cIm w) := by
  simp only [cHerm, dot, cRe, cIm, Complex.star_def, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.im_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro i _
  ring

theorem cBil_re (z w : Fin n → ℂ) :
    (cBil z w).re = dot (cRe z) (cRe w) - dot (cIm z) (cIm w) := by
  simp only [cBil, dot, cRe, cIm, Complex.mul_re, Complex.re_sum]
  rw [← Finset.sum_sub_distrib]

theorem cBil_im (z w : Fin n → ℂ) :
    (cBil z w).im = dot (cRe z) (cIm w) + dot (cIm z) (cRe w) := by
  simp only [cBil, dot, cRe, cIm, Complex.mul_im, Complex.im_sum]
  rw [← Finset.sum_add_distrib]

theorem dot_comm' (u v : Fin n → ℝ) : dot u v = dot v u := by
  simp only [dot]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- `Re z ⊥ Im z` iff the "square" `∑ zᵢ²` is real. -/
theorem cBil_self_im (z : Fin n → ℂ) : (cBil z z).im = 2 * dot (cRe z) (cIm z) := by
  rw [cBil_im z z, dot_comm' (cIm z) (cRe z)]
  ring

/-- The two complex orthogonality conditions are the four cross-orthogonality conditions of the
four real vectors. -/
theorem cross_iff (z w : Fin n → ℂ) :
    cHerm z w = 0 ∧ cBil z w = 0 ↔
      (dot (cRe z) (cRe w) = 0 ∧ dot (cIm z) (cIm w) = 0 ∧
       dot (cIm z) (cRe w) = 0 ∧ dot (cRe z) (cIm w) = 0) := by
  constructor
  · rintro ⟨h1, h2⟩
    have a1 := congrArg Complex.re h1
    have a2 := congrArg Complex.im h1
    have a3 := congrArg Complex.re h2
    have a4 := congrArg Complex.im h2
    simp only [Complex.zero_re, Complex.zero_im, cHerm_re, cHerm_im, cBil_re, cBil_im] at a1 a2 a3 a4
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨a1, a2, a3, a4⟩
    constructor
    · apply Complex.ext
      · simpa [cHerm_re] using
          (show dot (cRe z) (cRe w) + dot (cIm z) (cIm w) = 0 by linarith)
      · simpa [cHerm_im] using
          (show dot (cIm z) (cRe w) - dot (cRe z) (cIm w) = 0 by linarith)
    · apply Complex.ext
      · simpa [cBil_re] using
          (show dot (cRe z) (cRe w) - dot (cIm z) (cIm w) = 0 by linarith)
      · simpa [cBil_im] using
          (show dot (cRe z) (cIm w) + dot (cIm z) (cRe w) = 0 by linarith)

/-- `EFunC` is symmetric in the pair. -/
theorem EFunC_comm (R : Curv4 n) (hR : IsAlgCurv R) (z w : Fin n → ℂ) :
    EFunC R w z = EFunC R z w := by
  simp only [EFunC, EFun]
  rw [R4_pair_symm R hR (cRe w) (cIm w) (cRe z) (cIm z),
    R4_exchange_yxyx R hR (cRe w) (cRe z), R4_exchange_yxyx R hR (cRe w) (cIm z),
    R4_exchange_yxyx R hR (cIm w) (cRe z), R4_exchange_yxyx R hR (cIm w) (cIm z)]
  ring

/-- `EFunC R z z = 0` (a ℂ-dependent pair is isotropic-flat). -/
theorem EFunC_self (R : Curv4 n) (hR : IsAlgCurv R) (z : Fin n → ℂ) :
    EFunC R z z = 0 := by
  simp only [EFunC, EFun]
  rw [R4_self₁ R hR (cRe z) (cRe z) (cRe z), R4_self₁ R hR (cIm z) (cIm z) (cIm z),
    R4_exchange_yxyx R hR (cRe z) (cIm z)]
  ring

end Work.Diff.Alg.Q2P
