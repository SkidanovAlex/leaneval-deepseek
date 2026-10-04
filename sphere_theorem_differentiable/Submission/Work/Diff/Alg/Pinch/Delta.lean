import Mathlib
import Submission.Diff.Alg
import Submission.Work.Diff.Alg.Pinch.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Kronecker-delta summation lemmas

The round-sphere curvature tensor `Iso n i j k l = δᵢₖ δⱼₗ − δᵢₗ δⱼₖ` and Hamilton's reaction term
`Q` are polynomials in the Kronecker delta `id2 n a b = δ_{ab}`.  This module collects the handful
of elementary summation identities needed to evaluate such expressions: the basic contraction
`∑ p, δ_{ap} δ_{pb} = δ_{ab}`, its row/column variants, the trace `∑ p ∑ q, δ_{pq} = n`, and a few
generic lemmas that factor a double sum of a product of a `p`-factor and a `q`-factor.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- `Iso` expressed through the Kronecker delta `id2`: `Iso n i j k l = δᵢₖ δⱼₗ − δᵢₗ δⱼₖ`. -/
lemma Iso_eq_id2 (i j k l : Fin n) :
    Iso n i j k l = id2 n i k * id2 n j l - id2 n i l * id2 n j k := rfl

/-- The Kronecker delta is symmetric. -/
lemma id2_symm (i j : Fin n) : id2 n i j = id2 n j i := by
  by_cases h : i = j
  · subst h; rfl
  · simp [id2, h, Ne.symm h]

/-- The Kronecker delta is idempotent. -/
lemma id2_mul_self (i j : Fin n) : id2 n i j * id2 n i j = id2 n i j := by
  by_cases h : i = j <;> simp [id2, h]

/-- The fundamental contraction `∑ p, δ_{a p} δ_{p b} = δ_{a b}`. -/
lemma sum_id2_mul_id2 (a b : Fin n) : ∑ p, id2 n a p * id2 n p b = id2 n a b := by
  by_cases h : a = b
  · subst h
    rw [Finset.sum_eq_single a]
    · simp [id2]
    · intro c _ hc; have : a ≠ c := fun h => hc h.symm; simp [id2, this]
    · intro h'; exact absurd (Finset.mem_univ a) h'
  · rw [id2]
    simp only [ite_eq_right (show ¬ (a = b) from h)]
    apply Finset.sum_eq_zero
    intro p _
    by_cases hp : a = p
    · subst hp; simp [id2, h]
    · simp [id2, hp]

/-- Row contraction: `∑ p, δ_{i p} δ_{j p} = δ_{i j}`. -/
lemma sum_id2_row (i j : Fin n) : ∑ p, id2 n i p * id2 n j p = id2 n i j := by
  rw [← sum_id2_mul_id2 (n := n) i j]
  exact Finset.sum_congr rfl (fun p _ => by rw [id2_symm j p])

/-- Column contraction: `∑ p, δ_{p i} δ_{p j} = δ_{i j}`. -/
lemma sum_id2_col (i j : Fin n) : ∑ p, id2 n p i * id2 n p j = id2 n i j := by
  rw [← sum_id2_row (n := n) i j]
  exact Finset.sum_congr rfl (fun p _ => by rw [id2_symm p i, id2_symm p j])

/-- `∑ p, δ_{i p} = 1`. -/
lemma sum_id2 (i : Fin n) : ∑ p, id2 n i p = 1 := by
  simp [id2, Finset.sum_ite_eq]

/-- `∑ p, δ_{p i} = 1`. -/
lemma sum_id2_right (i : Fin n) : ∑ p, id2 n p i = 1 := by
  simp [id2, Finset.sum_ite_eq']

/-- The trace of the Kronecker delta: `∑ p ∑ q, δ_{p q} = n`. -/
lemma sum_id2_trace (n : ℕ) : (∑ p : Fin n, ∑ q : Fin n, id2 n p q) = (n : ℝ) := by
  have h : ∀ p : Fin n, (∑ q, id2 n p q) = 1 := fun p => sum_id2 (n := n) p
  simp [h]

/-- `∑ p ∑ q, δ_{p q}² = n`. -/
lemma sum_id2_sq (n : ℕ) : (∑ p : Fin n, ∑ q : Fin n, id2 n p q * id2 n p q) = (n : ℝ) := by
  rw [← sum_id2_trace n]
  exact Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => id2_mul_self p q))

/-- Mixed contraction: `∑ p ∑ q, δ_{p q} δ_{p a} δ_{b q} = δ_{b a}`. -/
lemma sum_id2_mixed (a b : Fin n) :
    ∑ p, ∑ q, id2 n p q * id2 n p a * id2 n b q = id2 n b a := by
  rw [Finset.sum_comm]
  have hinner : ∀ q : Fin n,
      (∑ p, id2 n p q * id2 n p a * id2 n b q) = id2 n q a * id2 n b q := by
    intro q
    rw [← Finset.sum_mul, sum_id2_col]
  simp only [hinner]
  rw [← sum_id2_mul_id2 (n := n) b a]
  exact Finset.sum_congr rfl (fun q _ => by rw [mul_comm])

/-- A double sum of a product of a `p`-factor and a `q`-factor factors. -/
lemma sum_sum_mul (f g : Fin n → ℝ) :
    (∑ p, ∑ q, f p * g q) = (∑ p, f p) * (∑ q, g q) := by
  rw [Finset.sum_mul_sum]

/-- A constant pulls out of a double sum. -/
lemma pullconst2 (c : ℝ) (F : Fin n → Fin n → ℝ) :
    (∑ p, ∑ q, c * F p q) = c * (∑ p, ∑ q, F p q) := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun p _ => by rw [Finset.mul_sum])

/-- Distribution of a double sum of a four-term combination. -/
lemma sum4 (A B C E : Fin n → Fin n → ℝ) :
    ∑ p, ∑ q, (A p q - B p q - C p q + E p q)
      = (∑ p, ∑ q, A p q) - (∑ p, ∑ q, B p q) - (∑ p, ∑ q, C p q)
        + (∑ p, ∑ q, E p q) := by
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- Distribution of a double sum of `A + 2 B - 2 C`. -/
lemma sum_lin (A B C : Fin n → Fin n → ℝ) :
    ∑ p, ∑ q, (A p q + 2 * B p q - 2 * C p q)
      = (∑ p, ∑ q, A p q) + 2 * (∑ p, ∑ q, B p q) - 2 * (∑ p, ∑ q, C p q) := by
  have h1 : ∀ p, (∑ q, (A p q + 2 * B p q - 2 * C p q))
      = (∑ q, A p q) + 2 * (∑ q, B p q) - 2 * (∑ q, C p q) := by
    intro p
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [h1]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

end Work.Diff.Alg.Pinch
