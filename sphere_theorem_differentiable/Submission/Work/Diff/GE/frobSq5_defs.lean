import Mathlib
import Submission.Work.Diff.GE.deps

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Reduction of the `(0,5)`-tensor Frobenius identities to a one-slot contraction

`N5 Γ T` and `frobSq5 S` (see `Work.Diff.GE.norms_defs`) are contractions of a `(0,5)`-tensor with
a positive definite matrix `Γ`.  To prove `N5 (A * Aᵀ) (rot5 A S) = frobSq5 S` we re-index the five
tensor slots by functions `x : Fin 5 → Fin n` and prove the *slot-wise* statement

* `rotA_QQ2_self k : QQ2 k Γ (rotA k A X) (rotA k A Y) = ∑ x, X x * Y x`,

which for `k = 5` is exactly the claim (the five individual contractions `Γ⁻¹ a b` with the five
change-of-frame factors `A` collapse, one slot at a time, to the Kronecker `δ`).

The two key definitions are `rotA` (the `k`-fold change of frame) and `QQ2` (the `k`-fold
contraction with `Γ⁻¹`).  Re-indexing `Fin (k+1) → Fin n` as `Fin n × (Fin k → Fin n)` is
`sum_pi_succ`.
-/

open Finset
open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

noncomputable section

variable {n : ℕ}

/-- The `k`-fold change of frame applied to a curried `k`-tensor
`T : (Fin k → Fin n) → ℝ`: contract every slot with `A`. -/
def rotA (k : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (T : (Fin k → Fin n) → ℝ) :
    (Fin k → Fin n) → ℝ :=
  fun x => ∑ y, (∏ d, A (x d) (y d)) * T y

/-- The `k`-fold contraction of a curried `k`-tensor with `Γ⁻¹` in every slot. -/
def QQ2 (k : ℕ) (Γ : Matrix (Fin n) (Fin n) ℝ) (X Y : (Fin k → Fin n) → ℝ) : ℝ :=
  ∑ x, ∑ y, (∏ d, Γ⁻¹ (x d) (y d)) * X x * Y y

/-- `Fin.cases` as a plain function `Fin (k+1) → Fin n` (avoids the dependent-type friction of
`Fin.cons`). -/
def consFn {k : ℕ} (a : Fin n) (x : Fin k → Fin n) : Fin (k+1) → Fin n :=
  fun i => Fin.cases a x i

@[simp] theorem consFn_zero {k : ℕ} (a : Fin n) (x : Fin k → Fin n) : consFn a x 0 = a := rfl

@[simp] theorem consFn_succ {k : ℕ} (a : Fin n) (x : Fin k → Fin n) (i : Fin k) :
    consFn a x i.succ = x i := rfl

theorem consFn_self_tail {k : ℕ} (f : Fin (k+1) → Fin n) :
    consFn (f 0) (fun i => f i.succ) = f := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

/-- The standard equivalence `(Fin (n+1) → α) ≃ α × (Fin n → α)`. -/
def piSuccEquiv (n : ℕ) (α : Type*) : (Fin (n+1) → α) ≃ α × (Fin n → α) where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp
  right_inv p := by
    ext <;> simp

/-- Re-index a sum over `Fin (k+1) → Fin n` by `(a, x) ↦ consFn a x`. -/
theorem sum_pi_succ {β : Type*} [AddCommMonoid β] (k : ℕ)
    (f : (Fin (k+1) → Fin n) → β) :
    ∑ x : Fin (k+1) → Fin n, f x = ∑ p : Fin n × (Fin k → Fin n), f (consFn p.1 p.2) := by
  refine Fintype.sum_equiv (piSuccEquiv k (Fin n)) f (fun p => f (consFn p.1 p.2)) (fun x => ?_)
  show f x = f (consFn (x 0) (fun i => x i.succ))
  rw [consFn_self_tail]

/-- Split the product over `Fin (k+1)` into the head and the tail. -/
theorem prod_cons {k : ℕ} (G : Fin n → Fin n → ℝ) (a b : Fin n) (x' y' : Fin k → Fin n) :
    (∏ d : Fin (k+1), G (consFn a x' d) (consFn b y' d))
      = G a b * ∏ d : Fin k, G (x' d) (y' d) := by
  rw [Fin.prod_univ_succ]
  simp

/-- One step of the recursion for `rotA`. -/
theorem rotA_succ {k : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (X : (Fin (k+1) → Fin n) → ℝ)
    (a : Fin n) (x' : Fin k → Fin n) :
    rotA (k+1) A X (consFn a x')
      = ∑ c : Fin n, A a c * rotA k A (fun u => X (consFn c u)) x' := by
  rw [rotA]
  rw [sum_pi_succ k]
  trans ∑ p : Fin n × (Fin k → Fin n),
      (A a p.1 * (∏ d : Fin k, A (x' d) (p.2 d))) * X (consFn p.1 p.2)
  · refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [show (∏ d : Fin (k+1), A (consFn a x' d) (consFn p.1 p.2 d))
          = A a p.1 * (∏ d : Fin k, A (x' d) (p.2 d)) from prod_cons A a p.1 x' p.2]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [rotA]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    ring

/-- The one-slot contraction: for `Γ = A * Aᵀ` and invertible `A`, the five-fold analogue of
`Aᵀ Γ⁻¹ A = 1` in components. -/
theorem contract_slot {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (c e : Fin n) :
    ∑ a : Fin n, ∑ b : Fin n, (A * Matrix.transpose A)⁻¹ a b * A a c * A b e
      = if c = e then 1 else 0 := by
  have hAtdet : IsUnit (Matrix.transpose A).det := by rw [Matrix.det_transpose]; exact hA
  have hAtinv : Matrix.transpose A * (Matrix.transpose A)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hAtdet
  have hAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv _ hA
  have hAinv' : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul _ hA
  have hGinv : (A * Matrix.transpose A)⁻¹ = (Matrix.transpose A)⁻¹ * A⁻¹ := by
    refine Matrix.inv_eq_right_inv ?_
    calc (A * Matrix.transpose A) * ((Matrix.transpose A)⁻¹ * A⁻¹)
        = A * (Matrix.transpose A * ((Matrix.transpose A)⁻¹ * A⁻¹)) := by rw [Matrix.mul_assoc]
      _ = A * ((Matrix.transpose A * (Matrix.transpose A)⁻¹) * A⁻¹) := by
            congr 1; rw [← Matrix.mul_assoc]
      _ = A * (1 * A⁻¹) := by rw [hAtinv]
      _ = A * A⁻¹ := by rw [Matrix.one_mul]
      _ = 1 := hAinv
  have hmat : Matrix.transpose A * (A * Matrix.transpose A)⁻¹ * A = 1 := by
    rw [hGinv]
    calc Matrix.transpose A * ((Matrix.transpose A)⁻¹ * A⁻¹) * A
        = Matrix.transpose A * (((Matrix.transpose A)⁻¹ * A⁻¹) * A) := by rw [Matrix.mul_assoc]
      _ = Matrix.transpose A * ((Matrix.transpose A)⁻¹ * (A⁻¹ * A)) := by
            congr 1; rw [← Matrix.mul_assoc]
      _ = Matrix.transpose A * ((Matrix.transpose A)⁻¹ * 1) := by rw [hAinv']
      _ = Matrix.transpose A * (Matrix.transpose A)⁻¹ := by rw [Matrix.mul_one]
      _ = 1 := hAtinv
  have h1 : (Matrix.transpose A * (A * Matrix.transpose A)⁻¹ * A) c e
      = ∑ a : Fin n, ∑ b : Fin n, (A * Matrix.transpose A)⁻¹ a b * A a c * A b e := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  rw [← h1, hmat, Matrix.one_apply]

lemma sum4_swap {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (T : α → β → γ → δ → ℝ) :
    (∑ i, ∑ j, ∑ a, ∑ b, T i j a b) = ∑ a, ∑ b, ∑ i, ∑ j, T i j a b := by
  rw [show (∑ i, ∑ j, ∑ a, ∑ b, T i j a b) = ∑ i, ∑ a, ∑ j, ∑ b, T i j a b from by
      refine Finset.sum_congr rfl (fun i _ => ?_); exact Finset.sum_comm]
  rw [show (∑ i, ∑ a, ∑ j, ∑ b, T i j a b) = ∑ a, ∑ i, ∑ j, ∑ b, T i j a b from Finset.sum_comm]
  rw [show (∑ a, ∑ i, ∑ j, ∑ b, T i j a b) = ∑ a, ∑ i, ∑ b, ∑ j, T i j a b from by
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun i _ => ?_))
      exact Finset.sum_comm]
  rw [show (∑ a, ∑ i, ∑ b, ∑ j, T i j a b) = ∑ a, ∑ b, ∑ i, ∑ j, T i j a b from by
      refine Finset.sum_congr rfl (fun a _ => ?_); exact Finset.sum_comm]

lemma sum_prod_split {α β : Type*} [Fintype α] [Fintype β] (T : (α × β) → (α × β) → ℝ) :
    (∑ p : α × β, ∑ q : α × β, T p q)
      = ∑ a : α, ∑ x : β, ∑ b : α, ∑ y : β, T (a, x) (b, y) := by
  trans ∑ a : α, ∑ x : β, ∑ q : α × β, T (a, x) q
  · exact Fintype.sum_prod_type _
  · refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun x _ => ?_))
    exact Fintype.sum_prod_type _

lemma sum_swap_mid {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (S : α → β → γ → δ → ℝ) :
    (∑ a, ∑ x, ∑ b, ∑ y, S a x b y) = ∑ a, ∑ b, ∑ x, ∑ y, S a x b y := by
  refine Finset.sum_congr rfl (fun a _ => ?_)
  exact Finset.sum_comm

lemma sum_factor4 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (c : α → β → ℝ) (Q : γ → δ → ℝ) :
    (∑ a, ∑ b, ∑ x, ∑ y, c a b * Q x y) = (∑ a, ∑ b, c a b) * (∑ x, ∑ y, Q x y) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.mul_sum]

theorem QQ2_rotA_succ {k : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (Γ : Matrix (Fin n) (Fin n) ℝ)
    (X Y : (Fin (k+1) → Fin n) → ℝ) :
    QQ2 (k+1) Γ (rotA (k+1) A X) (rotA (k+1) A Y)
    = ∑ c : Fin n, ∑ e : Fin n,
        (∑ a : Fin n, ∑ b : Fin n, Γ⁻¹ a b * A a c * A b e) *
        QQ2 k Γ (rotA k A (fun u => X (consFn c u))) (rotA k A (fun u => Y (consFn e u))) := by
  rw [QQ2]
  trans ∑ p : Fin n × (Fin k → Fin n), ∑ q : Fin n × (Fin k → Fin n),
      (∏ d : Fin (k+1), Γ⁻¹ (consFn p.1 p.2 d) (consFn q.1 q.2 d))
        * rotA (k+1) A X (consFn p.1 p.2) * rotA (k+1) A Y (consFn q.1 q.2)
  · rw [show (∑ x : Fin (k+1) → Fin n, ∑ y : Fin (k+1) → Fin n,
        (∏ d, Γ⁻¹ (x d) (y d)) * rotA (k+1) A X x * rotA (k+1) A Y y)
      = (∑ p : Fin n × (Fin k → Fin n), ∑ y : Fin (k+1) → Fin n,
        (∏ d, Γ⁻¹ (consFn p.1 p.2 d) (y d)) * rotA (k+1) A X (consFn p.1 p.2) * rotA (k+1) A Y y)
      from sum_pi_succ (n := n) k
        (fun x => ∑ y, (∏ d, Γ⁻¹ (x d) (y d)) * rotA (k+1) A X x * rotA (k+1) A Y y)]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    exact sum_pi_succ (n := n) k
      (fun y => (∏ d, Γ⁻¹ (consFn p.1 p.2 d) (y d)) * rotA (k+1) A X (consFn p.1 p.2) * rotA (k+1) A Y y)
  trans ∑ p : Fin n × (Fin k → Fin n), ∑ q : Fin n × (Fin k → Fin n),
      ((Γ⁻¹ p.1 q.1 * (∏ d : Fin k, Γ⁻¹ (p.2 d) (q.2 d)))
        * (∑ c : Fin n, A p.1 c * rotA k A (fun u => X (consFn c u)) p.2)
        * (∑ e : Fin n, A q.1 e * rotA k A (fun u => Y (consFn e u)) q.2))
  · refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    rw [show (∏ d : Fin (k+1), Γ⁻¹ (consFn p.1 p.2 d) (consFn q.1 q.2 d))
          = Γ⁻¹ p.1 q.1 * (∏ d : Fin k, Γ⁻¹ (p.2 d) (q.2 d)) from prod_cons (Γ⁻¹ : Matrix (Fin n) (Fin n) ℝ) p.1 q.1 p.2 q.2]
    rw [rotA_succ A X p.1 p.2, rotA_succ A Y q.1 q.2]
  trans ∑ p : Fin n × (Fin k → Fin n), ∑ q : Fin n × (Fin k → Fin n),
        ∑ c : Fin n, ∑ e : Fin n,
      ((Γ⁻¹ p.1 q.1 * (∏ d : Fin k, Γ⁻¹ (p.2 d) (q.2 d)))
        * (A p.1 c * rotA k A (fun u => X (consFn c u)) p.2)
        * (A q.1 e * rotA k A (fun u => Y (consFn e u)) q.2))
  · refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    rw [show (Γ⁻¹ p.1 q.1 * (∏ d : Fin k, Γ⁻¹ (p.2 d) (q.2 d)))
              * (∑ c : Fin n, A p.1 c * rotA k A (fun u => X (consFn c u)) p.2)
            = ∑ c : Fin n, (Γ⁻¹ p.1 q.1 * (∏ d : Fin k, Γ⁻¹ (p.2 d) (q.2 d)))
              * (A p.1 c * rotA k A (fun u => X (consFn c u)) p.2) from by rw [Finset.mul_sum]]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.mul_sum]
  · let T : (Fin n × (Fin k → Fin n)) → (Fin n × (Fin k → Fin n)) → Fin n → Fin n → ℝ :=
      fun p q c e => (Γ⁻¹ p.1 q.1 * (∏ d : Fin k, Γ⁻¹ (p.2 d) (q.2 d)))
        * (A p.1 c * rotA k A (fun u => X (consFn c u)) p.2)
        * (A q.1 e * rotA k A (fun u => Y (consFn e u)) q.2)
    change (∑ p, ∑ q, ∑ c, ∑ e, T p q c e) = _
    calc (∑ p, ∑ q, ∑ c, ∑ e, T p q c e)
        = ∑ c, ∑ e, ∑ p, ∑ q, T p q c e := sum4_swap T
      _ = ∑ c : Fin n, ∑ e : Fin n, ∑ a : Fin n, ∑ x' : Fin k → Fin n,
            ∑ b : Fin n, ∑ y' : Fin k → Fin n, T (a, x') (b, y') c e := by
            refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun e _ => ?_))
            exact sum_prod_split (fun p q => T p q c e)
      _ = ∑ c : Fin n, ∑ e : Fin n, ∑ a : Fin n, ∑ b : Fin n,
            ∑ x' : Fin k → Fin n, ∑ y' : Fin k → Fin n, T (a, x') (b, y') c e := by
            refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun e _ => ?_))
            exact sum_swap_mid (fun a x' b y' => T (a, x') (b, y') c e)
      _ = ∑ c : Fin n, ∑ e : Fin n, ∑ a : Fin n, ∑ b : Fin n,
            ∑ x' : Fin k → Fin n, ∑ y' : Fin k → Fin n,
            (Γ⁻¹ a b * A a c * A b e) * ((∏ d : Fin k, Γ⁻¹ (x' d) (y' d))
              * rotA k A (fun u => X (consFn c u)) x' * rotA k A (fun u => Y (consFn e u)) y') := by
            refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun e _ =>
              Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
              Finset.sum_congr rfl (fun x' _ => Finset.sum_congr rfl (fun y' _ => ?_))))))
            show (Γ⁻¹ a b * (∏ d : Fin k, Γ⁻¹ (x' d) (y' d)))
                  * (A a c * rotA k A (fun u => X (consFn c u)) x')
                  * (A b e * rotA k A (fun u => Y (consFn e u)) y')
                = (Γ⁻¹ a b * A a c * A b e) * ((∏ d : Fin k, Γ⁻¹ (x' d) (y' d))
                  * rotA k A (fun u => X (consFn c u)) x' * rotA k A (fun u => Y (consFn e u)) y')
            ring
      _ = ∑ c : Fin n, ∑ e : Fin n, (∑ a : Fin n, ∑ b : Fin n, Γ⁻¹ a b * A a c * A b e) *
            QQ2 k Γ (rotA k A (fun u => X (consFn c u))) (rotA k A (fun u => Y (consFn e u))) := by
            refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun e _ => ?_))
            rw [show QQ2 k Γ (rotA k A (fun u => X (consFn c u))) (rotA k A (fun u => Y (consFn e u)))
                  = ∑ x' : Fin k → Fin n, ∑ y' : Fin k → Fin n,
                      (∏ d : Fin k, Γ⁻¹ (x' d) (y' d))
                        * rotA k A (fun u => X (consFn c u)) x'
                        * rotA k A (fun u => Y (consFn e u)) y' from by rw [QQ2]]
            exact sum_factor4 (fun a b => Γ⁻¹ a b * A a c * A b e)
              (fun x' y' => (∏ d : Fin k, Γ⁻¹ (x' d) (y' d))
                * rotA k A (fun u => X (consFn c u)) x'
                * rotA k A (fun u => Y (consFn e u)) y')


/-- Collapsing a Kronecker delta in a double sum over a Fintype. -/
theorem sum_ite_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (F : ι → ι → ℝ) :
    (∑ c, ∑ e, (if c = e then (1 : ℝ) else 0) * F c e) = ∑ c, F c c := by
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_eq_single c]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · intro h; exact absurd (Finset.mem_univ c) h

end

end Work.Diff.GE
