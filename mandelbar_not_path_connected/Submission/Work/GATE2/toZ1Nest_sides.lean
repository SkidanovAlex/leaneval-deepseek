import Mathlib
import Submission.Work.GATE2.landing_succ_mem
import Submission.Work.ELAssembly.Z1

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2

/-- **The side memberships of the consecutive landing points, for the assembled nest.**

For the `Z1Nest` assembled from a `NestData` by `Work.ELAssembly.toZ1Nest` (whose `Q` is `S.Qp`
and whose `P0` is `S.P0`), the level-`(n+1)` landing point lies in the near side of the `α`-pair
and in the near side of the level-`n` pair: `(S.Qp (n+1)).y ∈ S.Q n` by
`Work.GATE2.landing_succ_mem`, and `S.Qmem n` identifies `S.Q n` with the intersection of the two
near sides. -/
theorem toZ1Nest_sides {c : ℂ} (S : Work.ELNest.NestData c) (hJ : Work.Top.JordanForm)
    (hnd : ∀ n : ℕ, Work.EL.arcLen (S.Qp n).a (S.Qp n).b ≠ 0) :
    (∀ n : ℕ, ((Work.ELAssembly.toZ1Nest S hJ hnd).Q (n + 1)).y ∈
        Work.EL.pairSideNear (Work.ELAssembly.toZ1Nest S hJ hnd).P0) ∧
      (∀ n : ℕ, ((Work.ELAssembly.toZ1Nest S hJ hnd).Q (n + 1)).y ∈
        Work.EL.pairSideNear ((Work.ELAssembly.toZ1Nest S hJ hnd).Q n)) := by
  constructor
  · intro n
    change (S.Qp (n + 1)).y ∈ Work.EL.pairSideNear S.P0
    have h := landing_succ_mem S n
    rw [Work.ELNest.NestData.mem_Q_iff] at h
    rw [S.Qmem n] at h
    exact h.1.1
  · intro n
    change (S.Qp (n + 1)).y ∈ Work.EL.pairSideNear (S.Qp n)
    have h := landing_succ_mem S n
    rw [Work.ELNest.NestData.mem_Q_iff] at h
    rw [S.Qmem n] at h
    exact h.1.2

end Work.GATE2
