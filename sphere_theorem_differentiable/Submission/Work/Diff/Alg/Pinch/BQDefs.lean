import Mathlib
import Submission.Work.Diff.Alg.Pinch.Linv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The polarization `BQ` of Hamilton's reaction term `Q`

`BQ R S` is the symmetric bilinear form associated with the quadratic map `Q`:
`Q (R + S) = Q R + Q S + 2 • BQ R S`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- The polarization of Hamilton's quadratic term `Q`. -/
noncomputable def BQ (R S : Curv4 n) : Curv4 n := fun i j k l =>
  ∑ p, ∑ q, ( (R i j p q * S k l p q + S i j p q * R k l p q) / 2
             + (R i p k q * S j p l q + S i p k q * R j p l q)
             - (R i p l q * S j p k q + S i p l q * R j p k q) )


/-- The traceless part `A - (tr A / n) • id` of a `2`-tensor. -/
noncomputable def traceless (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => A i j - ((∑ k, A k k) / (n : ℝ)) * id2 n i j

/-- The Böhm–Wilking correction tensor `D_{a,b}(R)` of Theorem 2: the difference between
`linv a b (Q (ell a b R))` and `Q R`. -/
noncomputable def bwCorr (a b : ℝ) (R : Curv4 n) : Curv4 n :=
  (((n : ℝ) - 2) * b ^ 2 - 2 * (a - b)) • knProd (ric0 R) (ric0 R)
  + (2 * a) • knProd (ric R) (ric R)
  + (2 * b ^ 2) • knProd (ric0sq R) (id2 n)
  + ((((n : ℝ) * b ^ 2 * (1 - 2 * b) - 2 * (a - b) * (1 - 2 * b + (n : ℝ) * b ^ 2))
        / ((n : ℝ) * (1 + 2 * ((n : ℝ) - 1) * a))) * ric0Frob2 R)
      • knProd (id2 n) (id2 n)


lemma BQ_apply (R S : Curv4 n) (i j k l : Fin n) :
    BQ R S i j k l =
      ∑ p, ∑ q, ( (R i j p q * S k l p q + S i j p q * R k l p q) / 2
             + (R i p k q * S j p l q + S i p k q * R j p l q)
             - (R i p l q * S j p k q + S i p l q * R j p k q) ) := rfl

lemma BQ_symm (R S : Curv4 n) : BQ R S = BQ S R := by
  funext i j k l
  simp only [BQ_apply]
  apply Finset.sum_congr rfl; intro p _
  apply Finset.sum_congr rfl; intro q _
  ring

lemma BQ_self (R : Curv4 n) : BQ R R = Q R := by
  funext i j k l
  simp only [BQ_apply, Q]
  apply Finset.sum_congr rfl; intro p _
  apply Finset.sum_congr rfl; intro q _
  ring

theorem Q_add_polarize (R S : Curv4 n) :
    Q (R + S) = Q R + Q S + BQ R S + BQ R S := by
  funext i j k l
  simp only [Q, BQ_apply, Pi.add_apply]
  trans ∑ p, ∑ q, ((R i j p q * R k l p q + 2 * R i p k q * R j p l q - 2 * R i p l q * R j p k q)
        + (S i j p q * S k l p q + 2 * S i p k q * S j p l q - 2 * S i p l q * S j p k q)
        + ((R i j p q * S k l p q + S i j p q * R k l p q) / 2
          + (R i p k q * S j p l q + S i p k q * R j p l q)
          - (R i p l q * S j p k q + S i p l q * R j p k q))
        + ((R i j p q * S k l p q + S i j p q * R k l p q) / 2
          + (R i p k q * S j p l q + S i p k q * R j p l q)
          - (R i p l q * S j p k q + S i p l q * R j p k q)))
  · apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _
    ring
  · simp only [Finset.sum_add_distrib]

lemma BQ_add_left (R S T : Curv4 n) : BQ (R + S) T = BQ R T + BQ S T := by
  funext i j k l
  simp only [BQ_apply, Pi.add_apply, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro p _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro q _
  ring

lemma BQ_smul_left (c : ℝ) (R S : Curv4 n) : BQ (c • R) S = c • BQ R S := by
  funext i j k l
  simp only [BQ_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro p _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro q _
  ring

lemma BQ_add_right (R S T : Curv4 n) : BQ R (S + T) = BQ R S + BQ R T := by
  rw [BQ_symm R (S+T), BQ_add_left, BQ_symm S R, BQ_symm T R]

lemma BQ_smul_right (c : ℝ) (R S : Curv4 n) : BQ R (c • S) = c • BQ R S := by
  rw [BQ_symm R (c • S), BQ_smul_left, BQ_symm S R]

end Work.Diff.Alg.Pinch
