import Mathlib
import Submission.Work.Diff.Alg.Pinch.Qop
import Submission.Work.Diff.Alg.q2p_transform

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary lemmas for `Work.Diff.Alg.Pinch.Phi_wedge`

The target `Phi R (ζ ∧ η) (conj (ζ ∧ η)) = 4 · EFun R (Re ζ) (Im ζ) (Re η) (Im η)` splits into
* the wedge expansion `Phi R (ζ ∧ η) (ζ' ∧ η') = 4 · cR4 R ζ η ζ' η'`, a purely index-theoretic
  statement about `Phi`, `wedgeF` and the complexified curvature tensor `cR4` of
  `Work.Diff.Alg.q2p_transform`;
* the reality/dictionary statement `cR4 R ζ η (star ζ) (star η) = (EFun R … : ℂ)`.

This module collects the small shared vocabulary: the four-fold sum form of `Phi`, the behaviour of
`bar` on a wedge, the pair symmetry of `cR4` and the fact that `star` intertwines `cR4` with
componentwise `star`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg
open Work.Diff.Alg (cR4)

variable {n : ℕ}

/-- `Phi` as a four-fold sum over the individual indices. -/
theorem Phi_quad (R : Curv4 n) (X Y : Fin n × Fin n → ℂ) :
    Phi R X Y = ∑ a, ∑ b, ∑ c, ∑ d, (R a b c d : ℂ) * X (a, b) * Y (c, d) := by
  simp only [Phi, Fintype.sum_prod_type]

/-- Componentwise `star` of a wedge is the wedge of the componentwise `star`s. -/
theorem bar_wedgeF (ζ η : Fin n → ℂ) :
    bar (wedgeF ζ η) = wedgeF (star ζ) (star η) := by
  funext p
  show star (ζ p.1 * η p.2 - ζ p.2 * η p.1)
      = star (ζ p.1) * star (η p.2) - star (ζ p.2) * star (η p.1)
  rw [star_sub, star_mul, star_mul]
  ring

/-- Renaming the two index blocks of a four-fold sum. -/
theorem sum4_block_renameC {A : Type*} [AddCommMonoid A]
    (F : Fin n → Fin n → Fin n → Fin n → A) :
    (∑ i, ∑ j, ∑ k, ∑ l, F i j k l) = ∑ i, ∑ j, ∑ k, ∑ l, F k l i j := by
  have h1 : (∑ p : Fin n × Fin n, ∑ q : Fin n × Fin n, F p.1 p.2 q.1 q.2)
      = ∑ i, ∑ j, ∑ k, ∑ l, F i j k l := by
    rw [Fintype.sum_prod_type]; simp only [Fintype.sum_prod_type]
  have h2 : (∑ p : Fin n × Fin n, ∑ q : Fin n × Fin n, F p.1 p.2 q.1 q.2)
      = ∑ i, ∑ j, ∑ k, ∑ l, F k l i j := by
    rw [Finset.sum_comm]
    rw [Fintype.sum_prod_type]; simp only [Fintype.sum_prod_type]
  exact h1.symm.trans h2

/-- Pair symmetry of the complexified curvature tensor. -/
theorem cR4_pair (R : Curv4 n) (hR : IsAlgCurv R) (a b c d : Fin n → ℂ) :
    cR4 R a b c d = cR4 R c d a b := by
  have h1 : cR4 R a b c d
      = ∑ i, ∑ j, ∑ k, ∑ l, (R k l i j : ℂ) * a i * b j * c k * d l := by
    rw [cR4]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    rw [hR.2.1 i j k l]
  have h2 : cR4 R c d a b
      = ∑ i, ∑ j, ∑ k, ∑ l, (R k l i j : ℂ) * a i * b j * c k * d l := by
    rw [cR4, sum4_block_renameC (F := fun i j k l => (R i j k l : ℂ) * c i * d j * a k * b l)]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    ring
  rw [h1, h2]

/-- `star` interchanges `cR4` with componentwise `star` (the coefficients are real). -/
theorem cR4_star (R : Curv4 n) (a b c d : Fin n → ℂ) :
    star (cR4 R a b c d) = cR4 R (star a) (star b) (star c) (star d) := by
  rw [cR4, cR4, star_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [star_sum]
  apply Finset.sum_congr rfl; intro j _
  rw [star_sum]
  apply Finset.sum_congr rfl; intro k _
  rw [star_sum]
  apply Finset.sum_congr rfl; intro l _
  simp

end Work.Diff.Alg.Pinch
