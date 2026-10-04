import Mathlib
import Submission.Work.Diff.Alg.Pinch.BQDefs
import Submission.Work.Diff.Alg.Pinch.Delta

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary index lemmas for `Q (A ∧ id)`

Helpers for the identity `Q_knProd_id`: the square `sq2`, the Frobenius norm `fr2`, elementary
Kronecker-delta contractions, the symmetries of `knProd X (id2 n)`, and the master contraction

`∑ p q, (X ∧ id) i j p q * Y p q = ∑ p, X i p * (Y p j - Y j p) + ∑ p, X j p * (Y i p - Y p i)`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- The square of a `2`-tensor: `sq2 X i j = ∑ k, X i k * X k j`. -/
noncomputable def sq2 (X : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => ∑ k, X i k * X k j

/-- The squared Frobenius norm of a `2`-tensor: `fr2 X = ∑ i, ∑ j, X i j * X i j`. -/
noncomputable def fr2 (X : Fin n → Fin n → ℝ) : ℝ := ∑ i, ∑ j, X i j * X i j

lemma sq2_apply (X : Fin n → Fin n → ℝ) (i j : Fin n) :
    sq2 X i j = ∑ k, X i k * X k j := rfl

lemma fr2_apply (X : Fin n → Fin n → ℝ) : fr2 X = ∑ i, ∑ j, X i j * X i j := rfl

lemma sq2_symm {X : Fin n → Fin n → ℝ} (hX : ∀ i j, X i j = X j i) (i j : Fin n) :
    sq2 X i j = sq2 X j i := by
  simp only [sq2_apply]
  apply Finset.sum_congr rfl; intro k _
  rw [hX j k, hX k i]; ring

/-- The trace of `sq2 X` is the Frobenius norm of `X` (for symmetric `X`). -/
lemma trace_sq2 {X : Fin n → Fin n → ℝ} (hX : ∀ i j, X i j = X j i) :
    (∑ k, sq2 X k k) = fr2 X := by
  simp only [sq2_apply, fr2_apply]
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro j _
  rw [hX j k]

/-! ## Elementary Kronecker-delta contractions -/

lemma sum_id2_mul_right (f : Fin n → ℝ) (a : Fin n) :
    (∑ c, id2 n a c * f c) = f a := by
  rw [Finset.sum_eq_single a]
  · simp [id2]
  · intro c _ hc
    have hac : a ≠ c := fun h => hc h.symm
    rw [id2, if_neg hac, zero_mul]
  · intro h; exact absurd (Finset.mem_univ a) h

lemma sum_id2_mul_left (f : Fin n → ℝ) (a : Fin n) :
    (∑ c, f c * id2 n a c) = f a := by
  rw [Finset.sum_eq_single a]
  · simp [id2]
  · intro c _ hc
    have hac : a ≠ c := fun h => hc h.symm
    rw [id2, if_neg hac, mul_zero]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- Symmetric version: `∑ p, f p * δ_{p a} = f a`. -/
lemma sum_mul_id2_right (f : Fin n → ℝ) (a : Fin n) :
    (∑ p, f p * id2 n p a) = f a := by
  rw [← sum_id2_mul_left (n := n) f a]
  exact Finset.sum_congr rfl (fun p _ => by rw [id2_symm a p])

/-- `∑ p, X i p * X k p = sq2 X i k` for symmetric `X`. -/
lemma sum_swap_sq2 {X : Fin n → Fin n → ℝ} (hX : ∀ i j, X i j = X j i) (i k : Fin n) :
    (∑ p, X i p * X k p) = sq2 X i k := by
  simp only [sq2_apply]
  apply Finset.sum_congr rfl; intro p _
  rw [hX k p]

/-! ## Symmetries of `knProd X (id2 n)` -/

lemma knProd_id2_swap12 (X : Fin n → Fin n → ℝ) (i j k l : Fin n) :
    knProd X (id2 n) j i k l = - knProd X (id2 n) i j k l := by
  simp only [knProd]; ring

lemma knProd_id2_swap34 (X : Fin n → Fin n → ℝ) (i j k l : Fin n) :
    knProd X (id2 n) i j l k = - knProd X (id2 n) i j k l := by
  simp only [knProd]; ring

lemma knProd_id2_pair {X : Fin n → Fin n → ℝ} (hX : ∀ i j, X i j = X j i)
    (i j k l : Fin n) :
    knProd X (id2 n) k l i j = knProd X (id2 n) i j k l := by
  simp only [knProd]
  rw [hX k i, hX k j, hX l i, hX l j,
    show id2 n l j = id2 n j l from id2_symm l j,
    show id2 n l i = id2 n i l from id2_symm l i,
    show id2 n k j = id2 n j k from id2_symm k j,
    show id2 n k i = id2 n i k from id2_symm k i]
  ring

/-! ## The master contraction -/

/-- Contracting `knProd X (id2 n)` in its last two slots against an arbitrary array `Y`. -/
lemma sum_knProd_id2_mul (X Y : Fin n → Fin n → ℝ) (i j : Fin n) :
    (∑ p, ∑ q, knProd X (id2 n) i j p q * Y p q)
      = (∑ p, X i p * (Y p j - Y j p)) + (∑ p, X j p * (Y i p - Y p i)) := by
  have h1 : ∀ p, (∑ q, (X i p * id2 n j q) * Y p q) = X i p * Y p j := by
    intro p
    rw [show (∑ q, (X i p * id2 n j q) * Y p q)
        = X i p * (∑ q, id2 n j q * Y p q) from by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring]
    rw [sum_id2_mul_right (fun q => Y p q) j]
  have h3 : ∀ p, (∑ q, (X j p * id2 n i q) * Y p q) = X j p * Y p i := by
    intro p
    rw [show (∑ q, (X j p * id2 n i q) * Y p q)
        = X j p * (∑ q, id2 n i q * Y p q) from by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring]
    rw [sum_id2_mul_right (fun q => Y p q) i]
  have h2 : ∀ p, (∑ q, (X i q * id2 n j p) * Y p q)
      = id2 n j p * (∑ q, X i q * Y p q) := by
    intro p
    rw [show (∑ q, (X i q * id2 n j p) * Y p q)
        = id2 n j p * (∑ q, X i q * Y p q) from by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring]
  have h4 : ∀ p, (∑ q, (X j q * id2 n i p) * Y p q)
      = id2 n i p * (∑ q, X j q * Y p q) := by
    intro p
    rw [show (∑ q, (X j q * id2 n i p) * Y p q)
        = id2 n i p * (∑ q, X j q * Y p q) from by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring]
  have hexp : ∀ p q : Fin n, knProd X (id2 n) i j p q * Y p q
      = (X i p * id2 n j q) * Y p q - (X i q * id2 n j p) * Y p q
        - (X j p * id2 n i q) * Y p q + (X j q * id2 n i p) * Y p q := by
    intro p q; simp only [knProd]; ring
  rw [Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => hexp p q))]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl (fun p _ => h1 p),
      Finset.sum_congr rfl (fun p _ => h2 p),
      Finset.sum_congr rfl (fun p _ => h3 p),
      Finset.sum_congr rfl (fun p _ => h4 p)]
  rw [sum_id2_mul_right (fun p => ∑ q, X i q * Y p q) j,
      sum_id2_mul_right (fun p => ∑ q, X j q * Y p q) i]
  rw [show (∑ p, X i p * (Y p j - Y j p))
        = (∑ p, X i p * Y p j) - (∑ p, X i p * Y j p) from by
      rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro p _; ring,
      show (∑ p, X j p * (Y i p - Y p i))
        = (∑ p, X j p * Y i p) - (∑ p, X j p * Y p i) from by
      rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro p _; ring]
  ring

/-- Contracting `knProd X (id2 n)` in its last slot against a vector. -/
lemma sum_knProd_id2_last (X : Fin n → Fin n → ℝ) (W : Fin n → ℝ) (a b c : Fin n) :
    (∑ q, knProd X (id2 n) a b c q * W q)
      = X a c * W b - id2 n b c * (∑ q, X a q * W q)
        - X b c * W a + id2 n a c * (∑ q, X b q * W q) := by
  have h1 : (∑ q, X a c * id2 n b q * W q) = X a c * W b := by
    rw [show (∑ q, X a c * id2 n b q * W q) = X a c * (∑ q, id2 n b q * W q) from by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring]
    rw [sum_id2_mul_right W b]
  have h2 : (∑ q, X a q * id2 n b c * W q) = id2 n b c * (∑ q, X a q * W q) := by
    rw [show (∑ q, X a q * id2 n b c * W q) = id2 n b c * (∑ q, X a q * W q) from by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring]
  have h3 : (∑ q, X b c * id2 n a q * W q) = X b c * W a := by
    rw [show (∑ q, X b c * id2 n a q * W q) = X b c * (∑ q, id2 n a q * W q) from by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring]
    rw [sum_id2_mul_right W a]
  have h4 : (∑ q, X b q * id2 n a c * W q) = id2 n a c * (∑ q, X b q * W q) := by
    rw [show (∑ q, X b q * id2 n a c * W q) = id2 n a c * (∑ q, X b q * W q) from by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring]
  have hexp : ∀ q : Fin n, knProd X (id2 n) a b c q * W q
      = X a c * id2 n b q * W q - X a q * id2 n b c * W q
        - X b c * id2 n a q * W q + X b q * id2 n a c * W q := by
    intro q; simp only [knProd]; ring
  rw [Finset.sum_congr rfl (fun q _ => hexp q)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [h1, h2, h3, h4]

/-! ## Linearity of `knProd` and of `Q` -/

lemma knProd_add_left (A B C : Fin n → Fin n → ℝ) :
    knProd (A + B) C = knProd A C + knProd B C := by
  funext i j k l; simp only [knProd, Pi.add_apply]; ring

lemma knProd_smul_left (c : ℝ) (A B : Fin n → Fin n → ℝ) :
    knProd (c • A) B = c • knProd A B := by
  funext i j k l; simp only [knProd, Pi.smul_apply, smul_eq_mul]; ring

/-- `Q` is homogeneous of degree two. -/
lemma Q_smul (c : ℝ) (R : Curv4 n) : Q (c • R) = (c ^ 2) • Q R := by
  funext i j k l
  simp only [Q, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro p _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro q _
  ring

/-- `knProd (id2 n) (id2 n) = 2 • Iso n`. -/
lemma knProd_id2_id2 : knProd (id2 n) (id2 n) = (2 : ℝ) • Iso n := by
  funext i j k l
  simp only [knProd, Pi.smul_apply, smul_eq_mul, Iso_eq_id2]
  ring

end Work.Diff.Alg.Pinch
