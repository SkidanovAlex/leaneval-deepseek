import Mathlib
import Submission.Work.Diff.Alg.Pinch.Q2Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Q2Trace` (self-contained copy)

This is a self-contained copy of the proof of `Work.Diff.Alg.Pinch.Q2Trace`
(`(Tmat R X * Rm R).trace = E1 - E2 - E3 + E4`), placed in the auxiliary namespace
`Work.Diff.Alg.Pinch.Q2Aux` so that it can be used without depending on
`Submission.Work.Diff.Alg.Pinch.Q2Trace`.
-/

namespace Work.Diff.Alg.Pinch.Q2Aux

open Finset Submission.Diff.Alg Matrix

variable {n : ℕ}

/-! ## Left and right matrix multiplication as operators on pair-indexed vectors -/

/-- Left multiplication by an `n × n` matrix, as a matrix on `Fin n × Fin n`:
`(Lmat A) (i,j) (k,l) = A i k δ_{jl}`. -/
noncomputable def Lmat (A : Fin n → Fin n → ℂ) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  fun p q => A p.1 q.1 * (if p.2 = q.2 then (1 : ℂ) else 0)

/-- Right multiplication by an `n × n` matrix: `(Rmat A) (i,j) (k,l) = δ_{ik} A l j`. -/
noncomputable def Rmat (A : Fin n → Fin n → ℂ) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  fun p q => (if p.1 = q.1 then (1 : ℂ) else 0) * A q.2 p.2

/-- `adMat` is the difference of left and right multiplication. -/
lemma adMat_eq_LR (X : Fin n × Fin n → ℂ) :
    adMat X = Lmat (fun i j => X (i,j)) - Rmat (fun i j => X (i,j)) := by
  ext p q
  simp only [adMat, Lmat, Rmat, Matrix.sub_apply]

lemma star_mul_comm' (a b : ℂ) : star (a * b) = star a * star b := by
  rw [star_mul, mul_comm]

lemma star_ite_one_zero (c : Prop) [Decidable c] :
    star (if c then (1 : ℂ) else 0) = if c then (1 : ℂ) else 0 := by
  split <;> simp

/-- The conjugate transpose of `adMat X` is `adMat` of the conjugate transpose of `X`. -/
lemma conjTranspose_adMat (X : Fin n × Fin n → ℂ) :
    (adMat X)ᴴ = adMat (bar (swapF X)) := by
  ext p q
  rw [Matrix.conjTranspose_apply]
  simp only [adMat, bar, swapF]
  rw [star_sub, star_mul_comm', star_mul_comm', star_ite_one_zero, star_ite_one_zero]
  rcases eq_or_ne p.2 q.2 with h | h <;>
    (first | rw [ite_eq_left h, ite_eq_left h.symm]
           | rw [ite_eq_right h, ite_eq_right (fun hh => h hh.symm)]) <;>
    (rcases eq_or_ne p.1 q.1 with h2 | h2 <;>
      (first | rw [ite_eq_left h2, ite_eq_left h2.symm]
             | rw [ite_eq_right h2, ite_eq_right (fun hh => h2 hh.symm)]))

/-! ## Kronecker-delta contraction and the four elementary matrix products -/

/-- Contraction of a Kronecker delta: `∑ x, δ_{y x} g x = g y`. -/
lemma sum_ite_one_mul {α : Type*} [Fintype α] [DecidableEq α] (y : α) (g : α → ℂ) :
    (∑ x, (if y = x then (1 : ℂ) else 0) * g x) = g y := by
  rw [show (∑ x, (if y = x then (1 : ℂ) else 0) * g x)
        = ∑ x, (if y = x then g x else 0) from by
      apply Finset.sum_congr rfl; intro x _
      rw [ite_mul, one_mul, zero_mul]]
  rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ y)]

lemma Lmat_mul_Rm (A : Fin n → Fin n → ℂ) (R : Curv4 n) (p s : Fin n × Fin n) :
    (Lmat A * Rm R) p s = ∑ a : Fin n, A p.1 a * (R a p.2 s.1 s.2 : ℂ) := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro q1 _
  rw [show (∑ q2 : Fin n, Lmat A p (q1, q2) * Rm R (q1, q2) s)
        = A p.1 q1 * (∑ q2 : Fin n,
            (if p.2 = q2 then (1 : ℂ) else 0) * (R q1 q2 s.1 s.2 : ℂ)) from by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro q2 _
      simp only [Lmat, Rm]; ring]
  exact congrArg (fun z => A p.1 q1 * z)
    (sum_ite_one_mul p.2 (fun q2 => (R q1 q2 s.1 s.2 : ℂ)))

lemma Rmat_mul_Rm (A : Fin n → Fin n → ℂ) (R : Curv4 n) (p s : Fin n × Fin n) :
    (Rmat A * Rm R) p s = ∑ a : Fin n, A a p.2 * (R p.1 a s.1 s.2 : ℂ) := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  rw [show (∑ q1 : Fin n, ∑ q2 : Fin n, Rmat A p (q1, q2) * Rm R (q1, q2) s)
        = ∑ q1 : Fin n, (if p.1 = q1 then (1 : ℂ) else 0)
            * (∑ q2 : Fin n, A q2 p.2 * (R q1 q2 s.1 s.2 : ℂ)) from by
      apply Finset.sum_congr rfl; intro q1 _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro q2 _
      simp only [Rmat, Rm]; ring]
  exact sum_ite_one_mul p.1 (fun q1 => ∑ q2 : Fin n, A q2 p.2 * (R q1 q2 s.1 s.2 : ℂ))

/-- The trace of a product of two pair-indexed matrices, expanded. -/
lemma trace_mul_eq_sum {ι : Type*} [Fintype ι] (M N : Matrix ι ι ℂ) :
    (M * N).trace = ∑ r, ∑ s, M r s * N s r := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]

/-! ## Permutations of the nested sums -/

/-- Move the last of four nested sums to the front. -/
lemma sum_rot4 {α M : Type*} [Fintype α] [AddCommMonoid M] (G : α → α → α → α → M) :
    (∑ i, ∑ j, ∑ k, ∑ l, G i j k l) = (∑ l, ∑ i, ∑ j, ∑ k, G i j k l) := by
  rw [show (∑ i, ∑ j, ∑ k, ∑ l, G i j k l) = ∑ i, ∑ j, ∑ l, ∑ k, G i j k l from
      Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => Finset.sum_comm))]
  rw [show (∑ i, ∑ j, ∑ l, ∑ k, G i j k l) = ∑ i, ∑ l, ∑ j, ∑ k, G i j k l from
      Finset.sum_congr rfl (fun i _ => Finset.sum_comm)]
  rw [show (∑ i, ∑ l, ∑ j, ∑ k, G i j k l) = ∑ l, ∑ i, ∑ j, ∑ k, G i j k l
        from Finset.sum_comm]

/-- Move the first of five nested sums to the end. -/
lemma sum_rot5b {α M : Type*} [Fintype α] [AddCommMonoid M] (G : α → α → α → α → α → M) :
    (∑ i, ∑ j, ∑ k, ∑ l, ∑ a, G i j k l a) = (∑ j, ∑ k, ∑ l, ∑ a, ∑ i, G i j k l a) := by
  rw [show (∑ i, ∑ j, ∑ k, ∑ l, ∑ a, G i j k l a) = ∑ j, ∑ i, ∑ k, ∑ l, ∑ a, G i j k l a
        from Finset.sum_comm]
  rw [show (∑ j, ∑ i, ∑ k, ∑ l, ∑ a, G i j k l a) = ∑ j, ∑ k, ∑ i, ∑ l, ∑ a, G i j k l a from
      Finset.sum_congr rfl (fun j _ => Finset.sum_comm)]
  rw [show (∑ j, ∑ k, ∑ i, ∑ l, ∑ a, G i j k l a) = ∑ j, ∑ k, ∑ l, ∑ i, ∑ a, G i j k l a from
      Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => Finset.sum_comm))]
  rw [show (∑ j, ∑ k, ∑ l, ∑ i, ∑ a, G i j k l a) = ∑ j, ∑ k, ∑ l, ∑ a, ∑ i, G i j k l a from
      Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ =>
        Finset.sum_congr rfl (fun l _ => Finset.sum_comm)))]

/-- Move the first of three nested sums to the end. -/
lemma sum_rot3b {α M : Type*} [Fintype α] [AddCommMonoid M] (G : α → α → α → M) :
    (∑ i, ∑ j, ∑ k, G i j k) = (∑ j, ∑ k, ∑ i, G i j k) := by
  rw [show (∑ i, ∑ j, ∑ k, G i j k) = ∑ j, ∑ i, ∑ k, G i j k from Finset.sum_comm]
  rw [show (∑ j, ∑ i, ∑ k, G i j k) = ∑ j, ∑ k, ∑ i, G i j k from
      Finset.sum_congr rfl (fun j _ => Finset.sum_comm)]

/-- The permutation of the summation variables used for `E1` and `E2`. -/
lemma perm_trace1 (F : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ p1, ∑ p2, ∑ s1, ∑ s2, ∑ a, ∑ b, F a p2 s1 s2 p1 b)
      = (∑ i, ∑ j, ∑ k, ∑ l, ∑ a, ∑ c, F i j k l a c) := by
  rw [show (∑ p1, ∑ p2, ∑ s1, ∑ s2, ∑ a, ∑ b, F a p2 s1 s2 p1 b)
        = ∑ p1, ∑ a, ∑ p2, ∑ s1, ∑ s2, ∑ b, F a p2 s1 s2 p1 b from
      Finset.sum_congr rfl (fun p1 _ => sum_rot4 (fun p2 s1 s2 a => ∑ b, F a p2 s1 s2 p1 b))]
  rw [show (∑ p1, ∑ a, ∑ p2, ∑ s1, ∑ s2, ∑ b, F a p2 s1 s2 p1 b)
        = ∑ a, ∑ p2, ∑ s1, ∑ s2, ∑ p1, ∑ b, F a p2 s1 s2 p1 b from
      sum_rot5b (fun p1 a p2 s1 s2 => ∑ b, F a p2 s1 s2 p1 b)]

/-- The permutation of the summation variables used for `E3` and `E4`. -/
lemma perm_trace2 (F : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ p1, ∑ p2, ∑ s1, ∑ s2, ∑ a, ∑ b, F p1 a s1 s2 p2 b)
      = (∑ i, ∑ j, ∑ k, ∑ l, ∑ b, ∑ c, F i j k l b c) := by
  rw [show (∑ p1, ∑ p2, ∑ s1, ∑ s2, ∑ a, ∑ b, F p1 a s1 s2 p2 b)
        = ∑ p1, ∑ a, ∑ p2, ∑ s1, ∑ s2, ∑ b, F p1 a s1 s2 p2 b from
      Finset.sum_congr rfl (fun p1 _ => sum_rot4 (fun p2 s1 s2 a => ∑ b, F p1 a s1 s2 p2 b))]
  rw [show (∑ p1, ∑ a, ∑ p2, ∑ s1, ∑ s2, ∑ b, F p1 a s1 s2 p2 b)
        = ∑ p1, ∑ a, ∑ s1, ∑ s2, ∑ p2, ∑ b, F p1 a s1 s2 p2 b from
      Finset.sum_congr rfl (fun p1 _ => Finset.sum_congr rfl (fun a _ =>
        sum_rot3b (fun p2 s1 s2 => ∑ b, F p1 a s1 s2 p2 b)))]

/-! ## The four traces -/

lemma trace_LL (R : Curv4 n) (A B : Fin n → Fin n → ℂ) :
    (Lmat A * Rm R * Lmat B * Rm R).trace
      = ∑ i, ∑ j, ∑ k, ∑ l, ∑ a, ∑ c,
          (R i j k l : ℂ) * (R c l a j : ℂ) * A a i * B k c := by
  rw [Matrix.mul_assoc (Lmat A * Rm R) (Lmat B) (Rm R), trace_mul_eq_sum]
  simp only [Fintype.sum_prod_type, Lmat_mul_Rm]
  simp only [Finset.sum_mul_sum]
  trans (∑ p1, ∑ p2, ∑ s1, ∑ s2, ∑ a, ∑ b,
          (R a p2 s1 s2 : ℂ) * (R b s2 p1 p2 : ℂ) * A p1 a * B s1 b)
  · apply Finset.sum_congr rfl; intro p1 _
    apply Finset.sum_congr rfl; intro p2 _
    apply Finset.sum_congr rfl; intro s1 _
    apply Finset.sum_congr rfl; intro s2 _
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    ring_nf
  · exact perm_trace1 (fun i j k l a c => (R i j k l : ℂ) * (R c l a j : ℂ) * A a i * B k c)

lemma trace_LR (R : Curv4 n) (A B : Fin n → Fin n → ℂ) :
    (Lmat A * Rm R * Rmat B * Rm R).trace
      = ∑ i, ∑ j, ∑ k, ∑ l, ∑ a, ∑ c,
          (R i j k l : ℂ) * (R k c a j : ℂ) * A a i * B c l := by
  rw [Matrix.mul_assoc (Lmat A * Rm R) (Rmat B) (Rm R), trace_mul_eq_sum]
  simp only [Fintype.sum_prod_type, Lmat_mul_Rm, Rmat_mul_Rm]
  simp only [Finset.sum_mul_sum]
  trans (∑ p1, ∑ p2, ∑ s1, ∑ s2, ∑ a, ∑ b,
          (R a p2 s1 s2 : ℂ) * (R s1 b p1 p2 : ℂ) * A p1 a * B b s2)
  · apply Finset.sum_congr rfl; intro p1 _
    apply Finset.sum_congr rfl; intro p2 _
    apply Finset.sum_congr rfl; intro s1 _
    apply Finset.sum_congr rfl; intro s2 _
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    ring_nf
  · exact perm_trace1 (fun i j k l a c => (R i j k l : ℂ) * (R k c a j : ℂ) * A a i * B c l)

lemma trace_RL (R : Curv4 n) (A B : Fin n → Fin n → ℂ) :
    (Rmat A * Rm R * Lmat B * Rm R).trace
      = ∑ i, ∑ j, ∑ k, ∑ l, ∑ b, ∑ c,
          (R i j k l : ℂ) * (R c l i b : ℂ) * A j b * B k c := by
  rw [Matrix.mul_assoc (Rmat A * Rm R) (Lmat B) (Rm R), trace_mul_eq_sum]
  simp only [Fintype.sum_prod_type, Rmat_mul_Rm, Lmat_mul_Rm]
  simp only [Finset.sum_mul_sum]
  trans (∑ p1, ∑ p2, ∑ s1, ∑ s2, ∑ a, ∑ b,
          (R p1 a s1 s2 : ℂ) * (R b s2 p1 p2 : ℂ) * A a p2 * B s1 b)
  · apply Finset.sum_congr rfl; intro p1 _
    apply Finset.sum_congr rfl; intro p2 _
    apply Finset.sum_congr rfl; intro s1 _
    apply Finset.sum_congr rfl; intro s2 _
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    ring_nf
  · exact perm_trace2 (fun i j k l b c => (R i j k l : ℂ) * (R c l i b : ℂ) * A j b * B k c)

lemma trace_RR (R : Curv4 n) (A B : Fin n → Fin n → ℂ) :
    (Rmat A * Rm R * Rmat B * Rm R).trace
      = ∑ i, ∑ j, ∑ k, ∑ l, ∑ b, ∑ d,
          (R i j k l : ℂ) * (R k d i b : ℂ) * A j b * B d l := by
  rw [Matrix.mul_assoc (Rmat A * Rm R) (Rmat B) (Rm R), trace_mul_eq_sum]
  simp only [Fintype.sum_prod_type, Rmat_mul_Rm]
  simp only [Finset.sum_mul_sum]
  trans (∑ p1, ∑ p2, ∑ s1, ∑ s2, ∑ a, ∑ b,
          (R p1 a s1 s2 : ℂ) * (R s1 b p1 p2 : ℂ) * A a p2 * B b s2)
  · apply Finset.sum_congr rfl; intro p1 _
    apply Finset.sum_congr rfl; intro p2 _
    apply Finset.sum_congr rfl; intro s1 _
    apply Finset.sum_congr rfl; intro s2 _
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    ring_nf
  · exact perm_trace2 (fun i j k l b d => (R i j k l : ℂ) * (R k d i b : ℂ) * A j b * B d l)

/-! ## The main identity -/

theorem Q2Trace (n : ℕ) (R : Submission.Diff.Alg.Curv4 n) (X : Fin n × Fin n → ℂ) :
    (Work.Diff.Alg.Pinch.Tmat R X * Work.Diff.Alg.Pinch.Rm R).trace
      = Work.Diff.Alg.Pinch.E1 R X - Work.Diff.Alg.Pinch.E2 R X
        - Work.Diff.Alg.Pinch.E3 R X + Work.Diff.Alg.Pinch.E4 R X := by
  -- `A` is the matrix of the pair-indexed vector `bar (swapF X)` (the conjugate transpose of `X`),
  -- `B` the matrix of `X`.
  set A : Fin n → Fin n → ℂ := fun u v => bar X (v,u) with hA
  set B : Fin n → Fin n → ℂ := fun k c => X (k,c) with hB
  have hAA : adMat (bar (swapF X)) = Lmat A - Rmat A := by
    rw [adMat_eq_LR]
    have h2 : (fun i j => bar (swapF X) (i,j)) = A := by
      rw [hA]; funext u v; simp [bar, swapF]
    rw [h2]
  have hBB : adMat X = Lmat B - Rmat B := by
    rw [adMat_eq_LR]
  have hT : Tmat R X = (Lmat A - Rmat A) * Rm R * (Lmat B - Rmat B) := by
    unfold Tmat
    rw [conjTranspose_adMat X, hAA, hBB]
  rw [hT]
  rw [show (Lmat A - Rmat A) * Rm R * (Lmat B - Rmat B) * Rm R
        = Lmat A * Rm R * Lmat B * Rm R - Lmat A * Rm R * Rmat B * Rm R
          - Rmat A * Rm R * Lmat B * Rm R + Rmat A * Rm R * Rmat B * Rm R from by
      noncomm_ring]
  simp only [Matrix.trace_add, Matrix.trace_sub]
  rw [trace_LL R A B, trace_LR R A B, trace_RL R A B, trace_RR R A B]
  simp only [E1, E2, E3, E4, hA, hB, bar]

end Work.Diff.Alg.Pinch.Q2Aux
