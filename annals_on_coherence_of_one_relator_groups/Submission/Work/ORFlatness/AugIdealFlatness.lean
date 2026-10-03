/-
# The flat modules of Jaikin-Zapirain--Linton, instantiated at the augmentation ideal

Jaikin-Zapirain--Linton construct, for `G` the fundamental group of a reducible two-complex
without proper powers and `D_{K[G]}` the Linnell division `K[G]`-ring, the flat `K[G]`-modules
`D_{K[G]} ⊗_K I_{K[G]}` (Theorem 5.3) and their right-module mirror (Theorem 1.7, "by
symmetry").  Here `I_{K[G]}` is the augmentation ideal of `K[G]`, `Work.ORFP2.augIdeal K G`.

The general results of this area are stated for an arbitrary `K[G]`-module `C` in place of
`I_{K[G]}`:
* left flatness: `Work.ORFlatness.leftFlat_diagonal_jl_of_testFamily`;
* right flatness: `Work.ORFlatness.rightFlat_diagonal_jl`;
* `Tor₂`-vanishing: `Work.ORFlatness.torTwoVanishes_diagonal_jl_right`.

This file records the instantiation at `C := ↥(augIdeal K G)`.  The augmentation ideal is
two-sided (it is the kernel of the augmentation `K[G] → K`), so it carries both a left
`K[G]`-module structure (used on the right-hand side) and a right `K[G]`-module structure
(used on the left-hand side; see `Work.ORFlatness.exists_augIdeal_rightModule`, which produces
such a structure and its compatibility with the `K`-module structure).

Neither instantiation needs any new mathematical input: they only fix the module `C`.
-/
import Submission.Work.ORFP2.Basic
import Submission.Work.ORFlatness.Diagonal
import Submission.Work.ORFlatness.DiagonalRight
import Submission.Work.ORFlatness.JLMain
import Submission.Work.ORFlatness.JLRightMain
import Submission.Work.ORFlatness.leftFlat_diagonal_jl_of_testFamily

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open TensorProduct MulOpposite

universe u

namespace Work.ORFlatness

variable (K : Type u) [CommRing K] (G : Type u) [Group G]
variable (S : Type u) [Ring S] [Algebra K S] (φ : MonoidAlgebra K G →ₐ[K] S)

section Left

variable [instR : Module ((MonoidAlgebra K G)ᵐᵒᵖ) ↥(Work.ORFP2.augIdeal K G)]
variable [IsScalarTower K (MonoidAlgebra K G)ᵐᵒᵖ ↥(Work.ORFP2.augIdeal K G)]
variable [SMulCommClass K (MonoidAlgebra K G)ᵐᵒᵖ ↥(Work.ORFP2.augIdeal K G)]

/-- **Jaikin-Zapirain--Linton, Theorem 5.6** at the augmentation ideal: the left `K[G]`-module
`S ⊗[K] I_{K[G]}` is flat, where the augmentation ideal is regarded as a right `K[G]`-module
(via right multiplication; such a structure exists by
`Work.ORFlatness.exists_augIdeal_rightModule`). -/
theorem leftFlat_diagonal_augIdeal
    [Jinst : Module (MonoidAlgebra K G) (S ⊗[K] ↥(Work.ORFP2.augIdeal K G))]
    {A B : Type u} [AddCommGroup A] [Module (MonoidAlgebra K G)ᵐᵒᵖ A]
    [AddCommGroup B] [Module (MonoidAlgebra K G)ᵐᵒᵖ B]
    (f : A →ₗ[(MonoidAlgebra K G)ᵐᵒᵖ] B)
    (g : B →ₗ[(MonoidAlgebra K G)ᵐᵒᵖ] ↥(Work.ORFP2.augIdeal K G))
    (hg : Function.Surjective g) (hfg : f.range = g.ker)
    (hB : ∀ (L : Type u) [AddCommGroup L] [Module K L] [Module (MonoidAlgebra K G)ᵐᵒᵖ L]
      [IsScalarTower K (MonoidAlgebra K G)ᵐᵒᵖ L]
      [SMulCommClass K (MonoidAlgebra K G)ᵐᵒᵖ L],
      letI := diagModule K G S φ L
      Tor1Vanishes (MonoidAlgebra K G) B (S ⊗[K] L))
    (hA : ∀ (L : Type u) [AddCommGroup L] [Module K L] [Module (MonoidAlgebra K G)ᵐᵒᵖ L]
      [IsScalarTower K (MonoidAlgebra K G)ᵐᵒᵖ L]
      [SMulCommClass K (MonoidAlgebra K G)ᵐᵒᵖ L],
      letI := diagModule K G S φ L
      Function.Injective (BalTensor.map (MonoidAlgebra K G) f
        (LinearMap.id : (S ⊗[K] L) →ₗ[MonoidAlgebra K G] (S ⊗[K] L))))
    (hswap : ∀ (L : Type u) [AddCommGroup L] [Module K L] [Module (MonoidAlgebra K G)ᵐᵒᵖ L]
      [IsScalarTower K (MonoidAlgebra K G)ᵐᵒᵖ L]
      [SMulCommClass K (MonoidAlgebra K G)ᵐᵒᵖ L],
      letI := diagModule K G S φ L
      (Tor1Vanishes (MonoidAlgebra K G) L (S ⊗[K] ↥(Work.ORFP2.augIdeal K G)) ↔
        Tor1Vanishes (MonoidAlgebra K G) ↥(Work.ORFP2.augIdeal K G) (S ⊗[K] L))) :
    LeftFlat (MonoidAlgebra K G) (S ⊗[K] ↥(Work.ORFP2.augIdeal K G)) :=
  leftFlat_diagonal_jl_of_testFamily K G S φ f g hg hfg hB hA hswap

end Left

section Right

/-- **Jaikin-Zapirain--Linton, Theorem 1.7** at the augmentation ideal: the right `K[G]`-module
`S ⊗[K] I_{K[G]}` is flat, where the augmentation ideal is regarded as a left `K[G]`-module
(its canonical structure). -/
theorem rightFlat_diagonal_augIdeal
    [Jinst : Module ((MonoidAlgebra K G)ᵐᵒᵖ) (S ⊗[K] ↥(Work.ORFP2.augIdeal K G))]
    {A B : Type u} [AddCommGroup A] [Module (MonoidAlgebra K G) A]
    [AddCommGroup B] [Module (MonoidAlgebra K G) B]
    (f : A →ₗ[MonoidAlgebra K G] B)
    (g : B →ₗ[MonoidAlgebra K G] ↥(Work.ORFP2.augIdeal K G))
    (hg : Function.Surjective g) (hfg : f.range = g.ker)
    (hB : ∀ (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
      [IsScalarTower K (MonoidAlgebra K G) M] [SMulCommClass K (MonoidAlgebra K G) M],
      letI := diagRightModule K G S φ M
      Tor1Vanishes (MonoidAlgebra K G) (S ⊗[K] M) B)
    (hA : ∀ (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
      [IsScalarTower K (MonoidAlgebra K G) M] [SMulCommClass K (MonoidAlgebra K G) M],
      letI := diagRightModule K G S φ M
      Function.Injective (BalTensor.map (MonoidAlgebra K G)
        (LinearMap.id : (S ⊗[K] M) →ₗ[(MonoidAlgebra K G)ᵐᵒᵖ] (S ⊗[K] M)) f))
    (hswap : ∀ (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
      [IsScalarTower K (MonoidAlgebra K G) M] [SMulCommClass K (MonoidAlgebra K G) M],
      letI := diagRightModule K G S φ M
      (Tor1Vanishes (MonoidAlgebra K G) (S ⊗[K] M) ↥(Work.ORFP2.augIdeal K G) ↔
        Tor1Vanishes (MonoidAlgebra K G) (S ⊗[K] ↥(Work.ORFP2.augIdeal K G)) M)) :
    RightFlat (MonoidAlgebra K G) (S ⊗[K] ↥(Work.ORFP2.augIdeal K G)) :=
  rightFlat_diagonal_jl K G S φ f g hg hfg hB hA hswap

end Right

end Work.ORFlatness
