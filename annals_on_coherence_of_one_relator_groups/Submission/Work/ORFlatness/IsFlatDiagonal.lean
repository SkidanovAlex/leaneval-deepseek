/-
# The flat modules of Theorem 5.6 in the vocabulary of N1 (`Work.ORHomAlg`)

`Work.ORFlatness.LeftFlat` and `Work.ORFlatness.RightFlat` agree with the canonical flatness
notions `Work.ORHomAlg.IsFlatLeft` and `Work.ORHomAlg.IsFlatRight` of the noncommutative
homological algebra chapter N1 (`Work.ORFlatness.leftFlat_iff_isFlatLeft`,
`Work.ORFlatness.rightFlat_iff_isFlatRight`).  This file restates the main flatness theorems of
this area in that vocabulary, so that they can be consumed by anything phrased for
`Work.ORHomAlg`.
-/
import Submission.Work.ORHomAlg.Flat
import Submission.Work.ORFlatness.leftFlat_iff_isFlatLeft
import Submission.Work.ORFlatness.rightFlat_iff_isFlatRight
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

/-- **Jaikin-Zapirain--Linton, Theorem 5.6**, in the vocabulary of `Work.ORHomAlg`: the left
`K[G]`-module `S ⊗[K] C` (diagonal action of `Submission.Work.ORFlatness/Diagonal.lean`, `C` a
right `K[G]`-module) is flat.  Same hypotheses as
`Work.ORFlatness.leftFlat_diagonal_jl_of_testFamily`. -/
theorem isFlatLeft_diagonal_jl
    {A B C : Type u} [AddCommGroup A] [Module (MonoidAlgebra K G)ᵐᵒᵖ A]
    [AddCommGroup B] [Module (MonoidAlgebra K G)ᵐᵒᵖ B]
    [AddCommGroup C] [Module K C] [Module (MonoidAlgebra K G)ᵐᵒᵖ C]
    [IsScalarTower K (MonoidAlgebra K G)ᵐᵒᵖ C] [SMulCommClass K (MonoidAlgebra K G)ᵐᵒᵖ C]
    [Jinst : Module (MonoidAlgebra K G) (S ⊗[K] C)]
    (f : A →ₗ[(MonoidAlgebra K G)ᵐᵒᵖ] B) (g : B →ₗ[(MonoidAlgebra K G)ᵐᵒᵖ] C)
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
      (Tor1Vanishes (MonoidAlgebra K G) L (S ⊗[K] C) ↔
        Tor1Vanishes (MonoidAlgebra K G) C (S ⊗[K] L))) :
    Work.ORHomAlg.IsFlatLeft (MonoidAlgebra K G) (S ⊗[K] C) := by
  have h : LeftFlat (MonoidAlgebra K G) (S ⊗[K] C) :=
    leftFlat_diagonal_jl_of_testFamily K G S φ f g hg hfg hB hA hswap
  exact (leftFlat_iff_isFlatLeft (MonoidAlgebra K G)).mp h

/-- **Jaikin-Zapirain--Linton, Theorem 5.6**, right-module mirror, in the vocabulary of
`Work.ORHomAlg`: the right `K[G]`-module `S ⊗[K] C` (diagonal action of
`Submission.Work.ORFlatness/DiagonalRight.lean`, `C` a left `K[G]`-module) is flat.  Same
hypotheses as `Work.ORFlatness.rightFlat_diagonal_jl`. -/
theorem isFlatRight_diagonal_jl
    {A B C : Type u} [AddCommGroup A] [Module (MonoidAlgebra K G) A]
    [AddCommGroup B] [Module (MonoidAlgebra K G) B]
    [AddCommGroup C] [Module K C] [Module (MonoidAlgebra K G) C]
    [IsScalarTower K (MonoidAlgebra K G) C] [SMulCommClass K (MonoidAlgebra K G) C]
    [Jinst : Module ((MonoidAlgebra K G)ᵐᵒᵖ) (S ⊗[K] C)]
    (f : A →ₗ[MonoidAlgebra K G] B) (g : B →ₗ[MonoidAlgebra K G] C)
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
      (Tor1Vanishes (MonoidAlgebra K G) (S ⊗[K] M) C ↔
        Tor1Vanishes (MonoidAlgebra K G) (S ⊗[K] C) M)) :
    Work.ORHomAlg.IsFlatRight (MonoidAlgebra K G) (S ⊗[K] C) := by
  rw [← rightFlat_iff_isFlatRight (MonoidAlgebra K G)]
  exact rightFlat_diagonal_jl K G S φ f g hg hfg hB hA hswap

end Work.ORFlatness
