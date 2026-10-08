import Mathlib
import Submission.Work.Zassenhaus.Basic

namespace Work.ZASS

/-- If `g` lies in the Borel `B = G_∞` (so `g` fixes `∞`) and `g` fixes at most two
points in total, then `g` fixes at most one point other than `∞`.

Indeed the set of fixed points of `g` outside `∞` is obtained from the full fixed-point
set by deleting the (fixed) point `∞`. -/
theorem ncard_fixed_ne_inf_le_one {G X : Type} [Group G] [MulAction G X] {inf : X} {g : G}
    (hg : g ∈ Work.Zassenhaus.borel G inf)
    (h2 : ({x : X | g • x = x} : Set X).ncard ≤ 2) :
    ({x : X | x ≠ inf ∧ g • x = x} : Set X).ncard ≤ 1 := by
  have hinf : g • inf = inf := by simpa [Work.Zassenhaus.borel] using hg
  have hset : {x : X | x ≠ inf ∧ g • x = x} = {x : X | g • x = x} \ {inf} := by
    ext x; simp [and_comm]
  rw [hset, Set.ncard_sdiff_singleton_of_mem (show inf ∈ {x : X | g • x = x} from hinf)]
  omega

end Work.ZASS
