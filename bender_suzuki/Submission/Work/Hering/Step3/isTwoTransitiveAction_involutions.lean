import Mathlib
import Submission.Work.Hering.Step3.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.Step3

/-- The double-transitivity hypothesis `DTInv G` on the involutions of `G`, read through the
conjugation action of `G` on the subtype `{x : G // x ∈ involutions G}`: this is precisely the
statement that `G` acts doubly transitively on its set of involutions. -/
theorem isTwoTransitiveAction_involutions {G : Type*} [Group G] (hDT : DTInv G) :
    IsTwoTransitiveAction G {x : G // x ∈ involutions G} := by
  intro a b c d hab hcd
  obtain ⟨g, hg1, hg2⟩ :=
    hDT a b c d a.2 b.2 c.2 d.2 (fun h => hab (Subtype.ext h)) (fun h => hcd (Subtype.ext h))
  exact ⟨g, Subtype.ext hg1, Subtype.ext hg2⟩

end Work.Hering.Step3
