import Mathlib
import Submission.Work.PTCert.OrderUnit

/-!
# Cauchy–Schwarz in the `Σ²` order

The paper's step (3) of the order-unit lemma: for elements `aᵢ` of a star-ring `A` which is
an `ℝ`-algebra,
`n · ∑ᵢ star aᵢ * aᵢ - star (∑ᵢ aᵢ) * (∑ᵢ aᵢ)` is a sum of hermitian squares, because it is
`(1/2) • ∑_{i,j} star (aᵢ - aⱼ) * (aᵢ - aⱼ)` and the double sum is a sum of hermitian squares.

The identity behind it is the classical Cauchy–Schwarz expansion
`∑_{i,j} star (aᵢ - aⱼ) (aᵢ - aⱼ) = 2 (n ∑ᵢ star aᵢ aᵢ - star (∑ aᵢ) (∑ aᵢ))`.
-/

namespace Work.PTCert

set_option autoImplicit false

open scoped BigOperators

/-- **The Cauchy–Schwarz identity.**  The double sum of the hermitian squares of the
differences is twice the target expression. -/
private lemma sosCS_identity {A : Type*} [Ring A] [StarRing A] [Algebra ℝ A] [StarModule ℝ A]
    [DecidableEq A] {n : ℕ} (a : Fin n → A) :
    (∑ p : Fin n × Fin n, star (a p.1 - a p.2) * (a p.1 - a p.2))
      = (2 : ℝ) • ((n : ℝ) • (∑ i, star (a i) * a i) - star (∑ i, a i) * (∑ i, a i)) := by
  -- the pointwise expansion `star (x - y) * (x - y) = star x * x + star y * y - star x * y - star y * x`
  have hterm : ∀ i j : Fin n, star (a i - a j) * (a i - a j)
      = star (a i) * a i + star (a j) * a j - star (a i) * a j - star (a j) * a i := by
    intro i j
    rw [star_sub]
    noncomm_ring
  -- `∑_{i,j} star (a i) * a j = star (∑ a) * (∑ a)`
  have hA : (∑ i : Fin n, ∑ j : Fin n, star (a i) * a j) = star (∑ i, a i) * (∑ i, a i) := by
    rw [star_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  -- `∑_{i,j} star (a j) * a i = star (∑ a) * (∑ a)`
  have hB : (∑ i : Fin n, ∑ j : Fin n, star (a j) * a i) = star (∑ i, a i) * (∑ i, a i) := by
    rw [star_sum]
    rw [show (∑ i : Fin n, ∑ j : Fin n, star (a j) * a i)
          = ∑ i : Fin n, (∑ j : Fin n, star (a j)) * a i from
        Finset.sum_congr rfl
          (fun i _ => (Finset.sum_mul Finset.univ (fun j => star (a j)) (a i)).symm)]
    exact (Finset.mul_sum Finset.univ a (∑ j : Fin n, star (a j))).symm
  -- `∑_{i,j} star (a i) * a i = (n : A) * ∑ aᵢ*aᵢ`
  have hC : (∑ i : Fin n, ∑ j : Fin n, star (a i) * a i)
      = (n : A) * (∑ i, star (a i) * a i) := by
    have hinner : ∀ i : Fin n, (∑ j : Fin n, star (a i) * a i)
        = (n : A) * (star (a i) * a i) :=
      fun i => by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.sum_congr rfl (fun i _ => hinner i), ← Finset.mul_sum]
  -- `∑_{i,j} star (a j) * a j = (n : A) * ∑ aᵢ*aᵢ`
  have hD : (∑ i : Fin n, ∑ j : Fin n, star (a j) * a j)
      = (n : A) * (∑ i, star (a i) * a i) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Fintype.sum_prod_type]
  simp only [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hA, hB, hC, hD]
  -- `(n:A)*S + (n:A)*S - b - b = 2 • ((n:ℝ)•S - b)`
  rw [two_smul ℝ, ← Submission.RouteB.real_smul_eq_natCast_mul n (∑ i, star (a i) * a i)]
  abel

/-- **Cauchy–Schwarz in the Σ²-order.**  `n ∑ᵢ star aᵢ * aᵢ - star (∑ᵢ aᵢ) * (∑ᵢ aᵢ)` is a sum
of hermitian squares — the Cauchy–Schwarz step of the order-unit lemma. -/
theorem sosCauchySchwarz {A : Type*} [Ring A] [StarRing A] [Algebra ℝ A] [StarModule ℝ A] [DecidableEq A] {n : ℕ} (a : Fin n → A) : Submission.RouteB.IsSOS ((n : ℝ) • (Finset.univ.sum (fun i : Fin n => star (a i) * a i)) - star (Finset.univ.sum a) * (Finset.univ.sum a)) := by
  have hD2 : Submission.RouteB.IsSOS
      (∑ p : Fin n × Fin n, star (a p.1 - a p.2) * (a p.1 - a p.2)) :=
    Submission.RouteB.isSOS_of_fintype _
  have hhalf : Submission.RouteB.IsSOS
      ((1 / 2 : ℝ) • (∑ p : Fin n × Fin n, star (a p.1 - a p.2) * (a p.1 - a p.2))) :=
    Submission.RouteB.IsSOS.smul (r := (1 / 2 : ℝ)) (by norm_num) hD2
  rw [sosCS_identity a] at hhalf
  rw [smul_smul] at hhalf
  rw [show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul] at hhalf
  exact hhalf

end Work.PTCert
