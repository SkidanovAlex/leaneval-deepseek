import Mathlib
import Submission.Diff.Alg
import Submission.Work.Diff.Alg.Pinch.Qint
import Submission.Work.Diff.Alg.Pinch.Qbian_antisymm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Hamilton's reaction term `Q` preserves algebraic curvature tensors

Hamilton's quadratic reaction term
`Q(R)ᵢⱼₖₗ = ∑_{p,q} (Rᵢⱼₚq Rₖₗₚq + 2 Rᵢₚₖq Rⱼₚₗq − 2 Rᵢₚₗq Rⱼₚₖq)`
(`Submission.Diff.Alg.Q`) maps the space of algebraic curvature tensors into itself: the
antisymmetry in the first pair, the pair symmetry and the first Bianchi identity of `Q R` all
follow from the corresponding identities of `R` by index gymnastics on the double sum.

* **Antisymmetry in the first pair** (`Q_antisym_first`): the summand `Qterm R j i k l p q` is the
  negative of `Qterm R i j k l p q`, pointwise in `(p,q)`.
* **Pair symmetry** (`Q_pair_symm`): the summand `Qterm R k l i j p q` equals
  `Qterm R i j k l q p`, so the two double sums agree after exchanging the summation variables.
* **First Bianchi identity** (`Q_bianchi`): the integrand `Qbian` of the cyclic sum
  `Q R i j k l + Q R j k i l + Q R k i j l` is *antisymmetric* in `(p,q)`
  (`Qbian_antisymm`), so the double sum vanishes.  This is the only place where the first Bianchi
  identity of `R` is used; it enters through the antisymmetrised form
  `R a b p q = R a p b q − R a q b p` (`algCurv_bianchi`), after which the integrand is a
  polynomial identity in the components `R a p b q` (`Work.Diff.Alg.Pinch.Qbian_antisymm`).
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- Antisymmetry of an algebraic curvature tensor in its *last* pair, deduced from the
antisymmetry in the first pair and the pair symmetry: `R a b d c = - R a b c d`. -/
private lemma algCurv_antisym_last {R : Curv4 n} (hR : IsAlgCurv R) (a b c d : Fin n) :
    R a b d c = - R a b c d := by
  have h1 := hR.2.1 d c a b
  have h2 := hR.1 d c a b
  have h3 := hR.2.1 c d a b
  linarith

/-- The first Bianchi identity in the antisymmetrised form `R a b p q = R a p b q − R a q b p`. -/
private lemma algCurv_bianchi {R : Curv4 n} (hR : IsAlgCurv R) (a b p q : Fin n) :
    R a b p q = R a p b q - R a q b p := by
  have h2 : R p b a q = - R a q b p := by
    rw [← hR.2.1 p b a q, algCurv_antisym_last hR a q b p]
  linarith [hR.2.2 a p b q, h2, hR.1 b a p q]

/-- Merging two double sums of the same shape. -/
private lemma sum2_add {n : ℕ} (f g : Fin n → Fin n → ℝ) :
    (∑ p, ∑ q, f p q) + (∑ p, ∑ q, g p q) = ∑ p, ∑ q, (f p q + g p q) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro p _
  rw [← Finset.sum_add_distrib]

/-- A double sum of a function antisymmetric in its two indices vanishes. -/
private lemma sum2_eq_zero_of_antisymm {n : ℕ} (S : Fin n → Fin n → ℝ)
    (h : ∀ p q : Fin n, S p q + S q p = 0) : (∑ p, ∑ q, S p q) = 0 := by
  have h1 : (∑ p, ∑ q, S p q) = ∑ p, ∑ q, S q p := by rw [Finset.sum_comm]
  have h2 : (∑ p, ∑ q, S q p) = - (∑ p, ∑ q, S p q) := by
    rw [show (∑ p, ∑ q, S q p) = ∑ p, ∑ q, (- S p q) from
      Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => by
        have := h p q; linarith))]
    simp only [Finset.sum_neg_distrib]
  linarith

/-- `Q R` is antisymmetric in the first pair of its indices. -/
theorem Q_antisym_first (n : ℕ) (R : Curv4 n) (hR : IsAlgCurv R) (i j k l : Fin n) :
    Q R j i k l = - Q R i j k l := by
  have hpt : ∀ p q : Fin n, Qterm R j i k l p q = - Qterm R i j k l p q := by
    intro p q
    simp only [Qterm]
    rw [hR.1 i j p q]
    ring
  rw [Q_eq_sum_Qterm R j i k l, Q_eq_sum_Qterm R i j k l]
  rw [show (∑ p, ∑ q, Qterm R j i k l p q) = ∑ p, ∑ q, (- Qterm R i j k l p q) from
    Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => hpt p q))]
  simp only [Finset.sum_neg_distrib]

/-- `Q R` is symmetric under exchanging its two index pairs. -/
theorem Q_pair_symm (n : ℕ) (R : Curv4 n) (hR : IsAlgCurv R) (i j k l : Fin n) :
    Q R k l i j = Q R i j k l := by
  have hpt : ∀ p q : Fin n, Qterm R k l i j p q = Qterm R i j k l q p := by
    intro p q
    simp only [Qterm]
    rw [hR.2.1 k p i q, hR.2.1 l p j q, hR.2.1 k p j q, hR.2.1 l p i q,
      algCurv_antisym_last hR i j p q, algCurv_antisym_last hR k l p q]
    ring
  rw [Q_eq_sum_Qterm R k l i j, Q_eq_sum_Qterm R i j k l]
  rw [show (∑ p, ∑ q, Qterm R k l i j p q) = ∑ p, ∑ q, Qterm R i j k l q p from
    Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => hpt p q))]
  rw [Finset.sum_comm]

/-- The integrand of the cyclic sum of `Q R` is antisymmetric in `(p,q)` for an algebraic
curvature tensor `R`.  On a fixed pair `(p,q)` the components of `R` that occur are all read off
from the `2`-tensor `A a b = R a p b q`, through the antisymmetrised Bianchi identity
(`h1`, `h2`) and the definition of `A` combined with pair symmetry (`h3`, `h4`). -/
theorem Qbian_pointwise (n : ℕ) (R : Curv4 n) (hR : IsAlgCurv R) (i j k l p q : Fin n) :
    Qbian R i j k l p q + Qbian R i j k l q p = 0 := by
  refine Qbian_antisymm n R (fun a b : Fin n => R a p b q) i j k l p q ?_ ?_ ?_ ?_
  · intro a b
    rw [algCurv_bianchi hR a b p q, ← hR.2.1 a q b p]
  · intro a b
    rw [algCurv_antisym_last hR a b p q, algCurv_bianchi hR a b p q, ← hR.2.1 a q b p]
    ring
  · intro a b
    rfl
  · intro a b
    rw [← hR.2.1 a q b p]

/-- `Q R` satisfies the first Bianchi identity when `R` does. -/
theorem Q_bianchi (n : ℕ) (R : Curv4 n) (hR : IsAlgCurv R) (i j k l : Fin n) :
    Q R i j k l + Q R j k i l + Q R k i j l = 0 := by
  have hsum : (∑ p, ∑ q, (Qterm R i j k l p q + Qterm R j k i l p q
      + Qterm R k i j l p q)) = 0 :=
    sum2_eq_zero_of_antisymm _
      (fun p q => by simpa only [Qbian] using Qbian_pointwise n R hR i j k l p q)
  rw [Q_eq_sum_Qterm R i j k l, Q_eq_sum_Qterm R j k i l, Q_eq_sum_Qterm R k i j l]
  rw [sum2_add (f := fun p q : Fin n => Qterm R i j k l p q)
        (g := fun p q : Fin n => Qterm R j k i l p q),
      sum2_add (f := fun p q : Fin n => Qterm R i j k l p q + Qterm R j k i l p q)
        (g := fun p q : Fin n => Qterm R k i j l p q)]
  exact hsum

/-- Hamilton's reaction term preserves algebraic curvature tensors. -/
theorem Q_isAlgCurv (n : ℕ) {R : Submission.Diff.Alg.Curv4 n}
    (hR : Submission.Diff.Alg.IsAlgCurv R) :
    Submission.Diff.Alg.IsAlgCurv (Submission.Diff.Alg.Q R) :=
  ⟨fun i j k l => Q_antisym_first n R hR i j k l,
   fun i j k l => Q_pair_symm n R hR i j k l,
   fun i j k l => Q_bianchi n R hR i j k l⟩

end Work.Diff.Alg.Pinch
