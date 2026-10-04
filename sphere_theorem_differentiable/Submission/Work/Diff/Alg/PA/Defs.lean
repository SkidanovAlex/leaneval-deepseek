import Mathlib
import Submission.Diff.Grad

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Definitions and tensor algebra for `Work.Diff.Alg.pinching_algebra`

Vocabulary and the elementary multilinear algebra of `R4` used by the proof of
`PinchingAlgebra n` (contract `PA` in `Submission/Diff/Grad.lean`).

Conventions are those of `Submission.Diff.Alg`: for an orthonormal frame `e`,
`R i j k l = ⟪R(eᵢ,eⱼ)eₗ, eₖ⟫`, so `secK R u v = R4 R u v u v` is the sectional curvature of the
plane of `(u,v)` and `Iso n` is the unit round sphere.

The `R4`-API lemmas (`R4_add*`, `R4_smul*`, the four-fold-sum reorderings, the symmetry lemmas and
the two polarization identities) are the elementary part of a curvature-tensor chapter; they are
stated here so that every lemma below can use them.
-/

namespace Work.Diff.Alg.PA

open Finset Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology

variable {n : ℕ}

/-! ## The standard basis vectors -/

/-- The `i`-th standard basis vector of `ℝⁿ`. -/
noncomputable def stdB (n : ℕ) (i : Fin n) : Fin n → ℝ := Pi.single i 1

@[simp] theorem stdB_self (n : ℕ) (i : Fin n) : stdB n i i = 1 := Pi.single_eq_same ..

@[simp] theorem stdB_ne (n : ℕ) {i j : Fin n} (h : j ≠ i) : stdB n i j = 0 := Pi.single_eq_of_ne h ..

theorem dot_stdB_stdB (n : ℕ) (i j : Fin n) :
    dot (stdB n i) (stdB n j) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h
    simp only [dot, stdB]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · intro h'; exact absurd (Finset.mem_univ i) h'
  · simp only [dot, stdB]
    rw [if_neg h]
    refine Finset.sum_eq_zero (fun l _ => ?_)
    by_cases hl : l = i
    · subst hl
      rw [Pi.single_eq_same, Pi.single_eq_of_ne h, mul_zero]
    · rw [Pi.single_eq_of_ne hl, zero_mul]

theorem isONPair_stdB {i j : Fin n} (h : i ≠ j) : IsONPair (stdB n i) (stdB n j) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [dot_stdB_stdB]; simp
  · rw [dot_stdB_stdB]; simp
  · rw [dot_stdB_stdB]; simp [h]

/-- Component form of `secK` at a pair of standard basis vectors. -/
theorem secK_stdB (R : Curv4 n) (i j : Fin n) :
    secK R (stdB n i) (stdB n j) = R i j i j := by
  simp only [secK, R4, stdB]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · rw [Finset.sum_eq_single i]
      · rw [Finset.sum_eq_single j]
        · simp
        · intro l _ hl; simp [Pi.single_eq_of_ne hl]
        · intro h; exact absurd (Finset.mem_univ j) h
      · intro k _ hk; simp [Pi.single_eq_of_ne hk]
      · intro h; exact absurd (Finset.mem_univ i) h
    · intro l _ hl; simp [Pi.single_eq_of_ne hl]
    · intro h; exact absurd (Finset.mem_univ j) h
  · intro k _ hk; simp [Pi.single_eq_of_ne hk]
  · intro h; exact absurd (Finset.mem_univ i) h

/-! ## The tensor pairing and the polarization of `Q` -/

/-- The Frobenius pairing `⟪A,B⟫ = ∑ Aᵢⱼₖₗ Bᵢⱼₖₗ` of two 4-index arrays. -/
noncomputable def tpair (n : ℕ) (A B : Curv4 n) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l, A i j k l * B i j k l

theorem tpair_self (n : ℕ) (A : Curv4 n) : tpair n A A = frobSq A := by
  simp only [tpair, frobSq]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro l _
  ring

theorem tpair_comm (n : ℕ) (A B : Curv4 n) : tpair n A B = tpair n B A := by
  simp only [tpair]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro l _
  ring

/-- The symmetric bilinear form polarizing `Q`: `Qbil A B = (Q (A+B) - Q A - Q B)/2`. -/
noncomputable def Qbil (n : ℕ) (A B : Curv4 n) : Curv4 n :=
  (1 / 2 : ℝ) • (Q (A + B) - Q A - Q B)

theorem Q_add_Qbil (n : ℕ) (A B : Curv4 n) :
    Q (A + B) = Q A + Q B + (2 : ℝ) • Qbil n A B := by
  have h : (2 : ℝ) • Qbil n A B = Q (A + B) - Q A - Q B := by
    ext i j k l
    simp only [Qbil, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
    ring
  rw [h]
  ext i j k l
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

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

theorem sum4_cycle (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, F i j k l) = ∑ i, ∑ j, ∑ k, ∑ l, F j k i l := by
  rw [sum4_swap23 F]
  exact sum4_swap12 (fun i j k l => F i k j l)

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

/-! ## The symmetries of an algebraic curvature tensor, at the level of `R4` -/

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
        rw [hR.2.1 i j k l]
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

/-! ## `IsAlgCurv` is a linear condition -/

theorem isAlgCurv_zero (n : ℕ) : IsAlgCurv (0 : Curv4 n) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp

theorem IsAlgCurv.smul {R : Curv4 n} (hR : IsAlgCurv R) (c : ℝ) : IsAlgCurv (c • R) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j k l
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hR.1 i j k l]; ring
  · intro i j k l
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hR.2.1 i j k l]
  · intro i j k l
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination c * hR.2.2 i j k l

theorem IsAlgCurv.add {R S : Curv4 n} (hR : IsAlgCurv R) (hS : IsAlgCurv S) :
    IsAlgCurv (R + S) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j k l
    simp only [Pi.add_apply]
    rw [hR.1 i j k l, hS.1 i j k l]; ring
  · intro i j k l
    simp only [Pi.add_apply]
    rw [hR.2.1 i j k l, hS.2.1 i j k l]
  · intro i j k l
    simp only [Pi.add_apply]
    linear_combination hR.2.2 i j k l + hS.2.2 i j k l

theorem IsAlgCurv.sub {R S : Curv4 n} (hR : IsAlgCurv R) (hS : IsAlgCurv S) :
    IsAlgCurv (R - S) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j k l
    simp only [Pi.sub_apply]
    rw [hR.1 i j k l, hS.1 i j k l]; ring
  · intro i j k l
    simp only [Pi.sub_apply]
    rw [hR.2.1 i j k l, hS.2.1 i j k l]
  · intro i j k l
    simp only [Pi.sub_apply]
    linear_combination hR.2.2 i j k l - hS.2.2 i j k l

end Work.Diff.Alg.PA
