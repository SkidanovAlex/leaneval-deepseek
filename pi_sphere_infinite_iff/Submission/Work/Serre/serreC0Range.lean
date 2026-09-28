import Mathlib
import Submission.Work.Serre.Models
import Submission.Work.Serre.serrePostnikovTower
import Submission.Work.RatHurewicz.AttachCells
import Submission.Work.Serre.serreC0Defs
import Submission.Work.Serre.serreC0Cover
import Submission.Work.Serre.serreC0Tools
import Submission.Work.Serre.serreC0Main
import Submission.Work.Serre.serreC0Moore

/-!
# C0 in range form

`Work.Serre.serreC0Range`: for `1 ≤ m ≤ N` every abelian group `A` has a model of `K(A,m)` up to
degree `N`, i.e. a space `X` with `π_m(X) ≃* A` and `π_i(X) = 0` for `i < m` and `m < i ≤ N`.

For `m ≥ 2` this is `Work.Serre.exists_isEMSpaceUpTo_succ` (the Moore space `M(A,m)`, built as a
wedge of spheres with the relations of a presentation of `A` attached as cells, followed by the
Postnikov truncation).  The case `m = 1` is reduced to `m = 2`: the loop space of a model of
`K(A,2)` (up to degree `N+1`) is a model of `K(A,1)` up to degree `N`
(`Work.Serre.exists_isEMSpaceUpTo_one`).
-/

namespace Work.Serre

open scoped Topology unitInterval

theorem serreC0Range : Work.Serre.SerreC0Range := by
  intro A _ m N hm hmN
  rcases m with _ | k
  · omega
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · -- `m = 1`: reduce to the case `m = 2` by looping
    subst hk0
    have hN : 1 ≤ N := by omega
    obtain ⟨X, tX, x, hx⟩ := exists_isEMSpaceUpTo_succ A 1 (by norm_num) (N + 1) (by omega)
    exact @exists_isEMSpaceUpTo_one A _ N hN X tX x hx
  · -- `m = k + 1` with `k ≥ 1`
    exact exists_isEMSpaceUpTo_succ A k hk N (by omega)

end Work.Serre
