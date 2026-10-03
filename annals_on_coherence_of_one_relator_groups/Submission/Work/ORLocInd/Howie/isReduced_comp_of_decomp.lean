import Mathlib
import Submission.Work.ORLocInd.Howie.Defs2
import Submission.Work.ORLocInd.Howie.PathReduced
import Submission.Work.ORLocInd.Howie.isReduced_comp
import Submission.Work.ORLocInd.Howie.endsWith_comp
import Submission.Work.ORLocInd.Howie.startsWith_comp

namespace Work.ORLocInd.Howie

theorem isReduced_comp_of_decomp {V : Type*}
    [Quiver V] [Quiver.HasInvolutiveReverse V]
    (e : Quiver.Total V) {w : V}
    (q : Quiver.Path w (e.left : V)) (s : Quiver.Path (e.right : V) w)
    (hr : (q.comp (e.hom.toPath.comp s)).IsReduced)
    (hcr : Work.ORLocInd.Howie.IsCyclicallyReduced (q.comp (e.hom.toPath.comp s))) :
    (s.comp q).IsReduced := by
  -- `s.comp q` is a factor of the reduced closed path `q.comp (e.hom.toPath.comp s)`:
  -- a backtrack of `s.comp q` is either inside `s`, inside `q`, or straddles the join.
  -- The first two are excluded by `hr`, and the straddling one is exactly the cyclic
  -- decomposition of `q.comp (e.hom.toPath.comp s)` excluded by `hcr`.
  refine Quiver.Path.isReduced_comp_iff.2 ⟨?_, ?_, ?_⟩
  · -- `s` is a reduced, being a right factor of the reduced path `q.comp (e.hom.toPath.comp s)`
    have h2 : ((q.comp e.hom.toPath).comp s).IsReduced := by
      rw [Quiver.Path.comp_assoc]; exact hr
    intro t ht
    exact h2 ((q.comp e.hom.toPath).comp t) (ht.comp_left (q.comp e.hom.toPath))
  · -- `q` is reduced, being a left factor of the reduced path `q.comp (e.hom.toPath.comp s)`
    exact hr.of_comp
  · -- no backtrack of `s.comp q` straddles the join: that would display
    -- `q.comp (e.hom.toPath.comp s)` as `g.toPath.comp (r.cons (reverse g))`
    rintro ⟨x, s', f, q', hs, hq⟩
    refine hcr ⟨x, Quiver.reverse f, q'.comp (e.hom.toPath.comp s'), ?_⟩
    rw [hs, hq]
    simp only [Quiver.Path.comp_assoc, Quiver.Path.comp_cons, Quiver.reverse_reverse]

end Work.ORLocInd.Howie
