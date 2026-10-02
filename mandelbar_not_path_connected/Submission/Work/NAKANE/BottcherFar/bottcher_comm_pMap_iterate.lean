import Mathlib
import Submission.Work.NAKANE.Defs
import Submission.Work.Bottcher.CritBasic
import Submission.Work.Bottcher.Core.bottcher_comm_pMap_domain

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.NAKANE.BottcherFar

/-- **The iterated functional equation of the product formula**, on the critical domain.
For `z ∈ critDomain c` and every `n`,
`bottcher c z ^ (4 ^ n) = bottcher c ((pMap c)^[n] z)`.

Route: bridge `Work.ParamRays.critDomain c` to `Work.Bottcher.CritDomain c` with
`Work.Bottcher.CritBasic.critDomain_eq`; then `Work.Bottcher.Core.bottcher_comm_pMap_domain c w hw`
gives `bottcher c (pMap c w) = bottcher c w ^ 4` for `w ∈ Work.Bottcher.CritDomain c`, the orbit
stays in the critical domain (`Work.Bottcher.Critical.CritDomain_pMap_mem` /
`CritBasic.pMap_iterate_mem_CritDomain`), and the statement follows by induction on `n`
(`pow_mul`, `pow_succ`, `Function.iterate_succ_apply`). -/
theorem bottcher_comm_pMap_iterate {c z : ℂ} (hz : z ∈ Work.ParamRays.critDomain c) (n : ℕ) :
    (Work.Bottcher.bottcher c z) ^ (4 ^ n) = Work.Bottcher.bottcher c ((Work.Bottcher.pMap c)^[n] z) := by
  have hz' : z ∈ Work.Bottcher.CritDomain c := by
    rw [Work.Bottcher.CritBasic.critDomain_eq]; exact hz
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', Nat.pow_succ, pow_mul, ih]
    exact (Work.Bottcher.Core.bottcher_comm_pMap_domain c ((Work.Bottcher.pMap c)^[k] z)
      (Work.Bottcher.CritBasic.pMap_iterate_mem_CritDomain hz' k)).symm

end Work.NAKANE.BottcherFar
