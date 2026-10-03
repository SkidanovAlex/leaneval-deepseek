import Mathlib

namespace Work.ORLyndon

theorem finsupp_sum_erase_add {X : Type*} [DecidableEq X]
    {M N : Type*} [AddZeroClass M] [AddCommMonoid N]
    (f : X →₀ M) (i : X) (g : X → M → N)
    (hg0 : ∀ x, g x 0 = 0) (hgadd : ∀ x a b, g x (a + b) = g x a + g x b) :
    f.sum g = (f.erase i).sum g + g i (f i) := by
  rw [add_comm]
  exact (Finsupp.add_sum_erase' f i g hg0).symm

end Work.ORLyndon
