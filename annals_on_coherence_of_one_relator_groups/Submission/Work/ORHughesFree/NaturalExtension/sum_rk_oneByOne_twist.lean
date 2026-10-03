import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.rk_oneByOne_twist_pow
import Submission.Work.ORHughesFree.SylvesterRank

namespace Work.ORHughesFree.NaturalExtension

theorem sum_rk_oneByOne_twist {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    (rk : Work.ORHughesFree.SylvesterRank U)
    (hτ : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) U),
      rk.rk n m (A.map (fun a => (Multiplicative.ofAdd (1 : ℤ)) • a)) = rk.rk n m A)
    (a : U) (K pp : ℕ) :
    ∑ c : Fin K, rk.rk 1 1 (Work.ORHughesFree.oneByOne ((Multiplicative.ofAdd ((pp + c.1 : ℕ) : ℤ)) • a))
      = (K : ℝ) * rk.rk 1 1 (Work.ORHughesFree.oneByOne a) := by
  -- Each summand is the rank of `oneByOne a`, by invariance under the generator twist.
  have hsum : (∑ c : Fin K,
        rk.rk 1 1 (Work.ORHughesFree.oneByOne ((Multiplicative.ofAdd ((pp + c.1 : ℕ) : ℤ)) • a)))
      = ∑ _ : Fin K, rk.rk 1 1 (Work.ORHughesFree.oneByOne a) :=
    Finset.sum_congr rfl fun c _ =>
      rk_oneByOne_twist_pow rk hτ a (pp + c.1)
  rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Work.ORHughesFree.NaturalExtension
