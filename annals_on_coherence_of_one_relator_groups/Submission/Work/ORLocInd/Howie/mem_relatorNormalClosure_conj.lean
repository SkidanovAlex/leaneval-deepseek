import Mathlib
import Submission.Work.ORLocInd.Howie.exists_labelling

universe u

namespace Work.ORLocInd.Howie

theorem mem_relatorNormalClosure_conj {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Work.ORLocInd.Howie.Presentation V) (x : V) (i : P.ι) (δ : Quiver.Path x (P.base i)) :
    (⟨Work.ORLocInd.Howie.pmul (Work.ORLocInd.Howie.pmul δ (P.path i)) δ.reverse,
      Work.ORLocInd.Howie.pmul_isReduced _ _⟩ : Work.ORLocInd.Howie.VertexGroup x)
      ∈ P.relatorNormalClosure x := by
  -- The element is a conjugate of the relator `P.path i` by the (reduced) path `red δ`; the
  -- definition of `P.relatorSet` asks for a *reduced* conjugating path, so we first replace `δ`
  -- by its reduced form, which does not change `pmul` (on either side).
  refine Subgroup.subset_normalClosure ⟨i, red δ, isReduced_red δ, ?_⟩
  apply Subtype.ext
  show pmul (pmul δ (P.path i)) δ.reverse =
    pmul (red δ) (pmul (P.path i) (red δ).reverse)
  calc pmul (pmul δ (P.path i)) δ.reverse
      = pmul (pmul (red δ) (P.path i)) δ.reverse := by
        rw [← pmul_red_left δ (P.path i)]
    _ = pmul (pmul (red δ) (P.path i)) (red δ).reverse :=
        pmul_congr_right (pmul (red δ) (P.path i))
          (Quiver.Path.ReducesTo.reverse (reducesTo_red δ))
    _ = pmul (red δ) (pmul (P.path i) (red δ).reverse) := pmul_assoc _ _ _

end Work.ORLocInd.Howie
