import Mathlib
import Submission.Work.ORLocInd.Howie.PathSumHom
import Submission.Work.ORLocInd.Howie.CoverPresentation
import Submission.Work.ORLocInd.Howie.Relator

namespace Work.ORLocInd.Howie

/-- **A labelling which vanishes on the relators kills their normal closure.**  If the balanced
labelling `L` has level `0` on every relator of `P`, then the level of every conjugate
`δ · r_i · δ⁻¹` of a relator is `0` as well: the levels add
(`pathSum_pmul`), the level of the reversed path `δ⁻¹` is the negative of that of `δ`
(`pathSum_reverse`, using balancedness), and the level of `r_i` vanishes by hypothesis.  Since the
kernel of `pathSumHom L.toFun L.isBalanced x` is a normal subgroup of the vertex group `F(Γ)_x`
containing every such conjugate, it contains the normal closure of the relators.

This is the statement that the level homomorphism descends to the presented vertex group
`π₁(⟨Γ | R⟩, x)`. -/
theorem relatorNormalClosure_le_ker_pathSumHom {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Work.ORLocInd.Howie.Presentation V) (L : Work.ORLocInd.Howie.Labelling V)
    (hL : Work.ORLocInd.Howie.VanishOnRelators L P) (x : V) :
    P.relatorNormalClosure x ≤ (Work.ORLocInd.Howie.pathSumHom L.toFun L.isBalanced x).ker := by
  -- the kernel is a normal subgroup, so it suffices to contain the relator-conjugates
  refine Subgroup.normalClosure_le_normal ?_
  rintro g ⟨i, δ, hδ, hg⟩
  -- rewrite the membership in the kernel as the vanishing of the level
  change (Work.ORLocInd.Howie.pathSumHom L.toFun L.isBalanced x) g = 1
  refine (pathSumHom_eq_one_iff L.toFun L.isBalanced x g).mpr ?_
  -- `g` is the conjugate `δ · r_i · δ⁻¹`, built from the reduced path `δ`
  have hg' : g.1 = pmul δ (pmul (P.path i) δ.reverse) := congrArg Subtype.val hg
  rw [hg', pathSum_pmul L.toFun L.isBalanced, pathSum_pmul L.toFun L.isBalanced,
      pathSum_reverse L.toFun L.isBalanced, hL i]
  ring

end Work.ORLocInd.Howie
