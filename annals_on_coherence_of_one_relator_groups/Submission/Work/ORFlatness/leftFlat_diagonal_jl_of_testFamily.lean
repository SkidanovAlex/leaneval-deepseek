/-
# Jaikin-Zapirain--Linton, Theorem 5.6 (single two-cell case), flatness form without the
  reduction hypothesis

`Work.ORFlatness.leftFlat_diagonal_jl` (`Submission/Work/ORFlatness/JLMain.lean`) proves the
flatness of the left `K[G]`-module `S ⊗[K] C` from the hypotheses `hB` (Claim 5.8), `hA`
(Lemma 5.1 + Claim 5.9) and `hswap` (Lemma 5.2), but takes as an additional hypothesis `hred`
the reduction that flatness of a left `K[G]`-module may be tested against right `K[G]`-modules
carrying a compatible `K`-module structure.

Here we remove that hypothesis, using `Work.ORFlatness.leftFlat_of_testFamily`
(`Submission/Work/ORFlatness/leftFlat_of_testFamily.lean`), which shows that `Tor₁`-vanishing
against that family of test modules already implies flatness, because every right `K[G]`-module
carries such a `K`-structure by restriction of scalars.

The diagonal module structure on `S ⊗[K] C` is passed as an explicit instance argument `Jinst`
(an instance-implicit binder), so that neither the statement nor its use requires a `letI`
binding: `Jinst` is `diagModule K G S φ C`.
-/
import Submission.Work.ORFlatness.Flat
import Submission.Work.ORFlatness.Diagonal
import Submission.Work.ORFlatness.JLMain
import Submission.Work.ORFlatness.leftFlat_of_testFamily

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open TensorProduct MulOpposite

universe u

namespace Work.ORFlatness

variable (K : Type u) [CommRing K] (G : Type u) [Group G]
variable (S : Type u) [Ring S] [Algebra K S] (φ : MonoidAlgebra K G →ₐ[K] S)

/-- **Jaikin-Zapirain--Linton, Theorem 5.6 (single two-cell case)**: flatness of the left
`K[G]`-module `S ⊗[K] C`, without the auxiliary reduction hypothesis.  Compare
`Work.ORFlatness.leftFlat_diagonal_jl`. -/
theorem leftFlat_diagonal_jl_of_testFamily
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
    LeftFlat (MonoidAlgebra K G) (S ⊗[K] C) := by
  refine leftFlat_of_testFamily K G (S ⊗[K] C) ?_
  intro X _ _ _ _ _
  haveI := diagModule K G S φ X
  rw [hswap X]
  exact tor1Vanishes_diagonal_jl K G S φ f g hg hfg X (hB X) (hA X)

end Work.ORFlatness
