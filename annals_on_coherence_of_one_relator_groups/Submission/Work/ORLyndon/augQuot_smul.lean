import Mathlib
import Submission.Work.ORLyndon.AugQuot

/-!
# The `K[G]`-action on `K[G] ⧸ I` is compatible with the augmentation quotient map

The quotient `K[G] ⧸ I_{K[G]}` carries its natural `K[G]`-module structure, inherited from
`K[G]`.  Under the identification `augQuot : K[G] ⧸ I ≃ₗ[K] K` with the trivial module `K`
(via `smul_mk_augIdeal` on representatives), the action of `a : K[G]` becomes multiplication by
the augmentation `ε a`.  This file records that compatibility:

`augQuot K G (a • n) = augmentation K G a * augQuot K G n`.
-/

set_option autoImplicit false

namespace Work.ORLyndon

universe u v

theorem augQuot_smul {K : Type v} [Field K] {G : Type u} [Group G]
    (a : MonoidAlgebra K G) (n : MonoidAlgebra K G ⧸ Work.ORLyndon.augIdeal K G) :
    Work.ORLyndon.augQuot K G (a • n)
      = Work.ORLyndon.augmentation K G a * Work.ORLyndon.augQuot K G n := by
  -- every element of the quotient is the class of a representative
  induction n using Submodule.Quotient.induction_on with
  | H x =>
    -- rewrite `Submodule.Quotient.mk` as `Ideal.Quotient.mk` so that the quotient API applies
    change augQuot K G (a • Ideal.Quotient.mk (augIdeal K G) x)
      = augmentation K G a * augQuot K G (Ideal.Quotient.mk (augIdeal K G) x)
    -- the action on classes is multiplication, and `augQuot` is the augmentation
    rw [smul_mk_augIdeal, augQuot_mk, augQuot_mk, augmentation_mul]

end Work.ORLyndon
