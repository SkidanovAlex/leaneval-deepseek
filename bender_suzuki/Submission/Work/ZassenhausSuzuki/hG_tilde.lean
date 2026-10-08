import Mathlib
import Submission.Work.ZassenhausSuzuki.SzTildeDefs
import Submission.Work.ZassenhausSuzuki.szTildeAux
import Submission.Work.ZassenhausSuzuki.canon_aux
import Submission.Work.ZassenhausSuzuki.szMuCenter
import Submission.Work.ZassenhausSuzuki.hG_tilde_eq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

theorem hG_tilde {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (C : Work.ZassenhausPSL2.Canon H Q t) {z : Q}
    (hz1 : z ≠ 1) (hz2 : z * z = 1) (hacen : z ∈ Subgroup.center Q) :
    Work.ZassenhausSuzuki.hG C (Work.ZassenhausSuzuki.tildeOf C z)
      = Work.ZassenhausSuzuki.hG C z := by
  have hzG : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  exact hG_tilde_eq hsplit hzass h2 C hzG

end Work.ZassenhausSuzuki
