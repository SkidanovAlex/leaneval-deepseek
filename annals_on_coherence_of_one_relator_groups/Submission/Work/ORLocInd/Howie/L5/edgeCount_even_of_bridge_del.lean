import Mathlib
import Submission.Work.ORLocInd.Howie.DelReach
import Submission.Work.ORLocInd.Howie.edgeCount_cons
import Submission.Work.ORLocInd.Howie.Defs2
import Submission.Work.ORLocInd.Howie.edgeCount_even_of_bridge_avoid

namespace Work.ORLocInd.Howie.L5

/-- L5b of `N4_LOCIND_LEAD.md`, for the *honest* bridge hypothesis `hbr`: if no path of `Γ` from
`e.right` back to `e.left` avoids the unoriented edge `{e, e⁻¹}`, then every closed path crosses
`{e, e⁻¹}` an even number of times.  This is the statement of
`Work.ORLocInd.Howie.edgeCount_even_of_bridge_avoid`, which is proved in full in
`Submission/Work/ORLocInd/Howie/edgeCount_even_of_bridge_avoid.lean`: the crossing count of `e`
along a path has the parity of the number of flips of `DelReach P e` (reachability from `e.left`
inside `Γ ∖ e`), and a closed path has no flip overall. -/
theorem edgeCount_even_of_bridge_del {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Work.ORLocInd.Howie.Presentation V) (hsep : P.CodeSeparates) (e : Quiver.Total V)
    (hbr : ∀ q : Quiver.Path e.right e.left, Work.ORLocInd.Howie.Avoids P e q → False)
    {w : V} (r : Quiver.Path w w) :
    Even (Work.ORLocInd.Howie.edgeCount P.edgeOf r e) :=
  Work.ORLocInd.Howie.edgeCount_even_of_bridge_avoid P hsep e hbr r

end Work.ORLocInd.Howie.L5
