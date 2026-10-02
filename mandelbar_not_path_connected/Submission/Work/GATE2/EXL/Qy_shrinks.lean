import Mathlib
import Submission.Work.GATE2.EXL.shrinks_esc
import Submission.Work.GATE2.Inputs
import Submission.Work.ELTop.landsN_mem_K

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Metric
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE2.EXL

/-! ## The landing points of the nest shrink to the parabolic point

The landing points `(Q n).y` of the levels of the nest converge to the parabolic point `z₁`.

This is immediate from the shrink field `Z1Nest.shrinks`, which controls the whole piece of `K c`
lying between the near side of the `α`-pair `P0` and the near side of the level-`n` pair `Q n`:
the hypotheses `hP` and `hQ` of the statement say exactly that the landing point
`(Q (n+1)).y` is such a point of `K c` at level `n`, and a landing point of a ray is in `K c`
(`Work.ELTop.landsN_mem_K`). -/
theorem Qy_shrinks {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (z₁ : ℂ) (Pa : Set ℂ)
    (nest : Work.EL.Z1Nest hN z₁ Pa)
    (hP : ∀ n : ℕ, (nest.Q (n + 1)).y ∈ Work.EL.pairSideNear nest.P0)
    (hQ : ∀ n : ℕ, (nest.Q (n + 1)).y ∈ Work.EL.pairSideNear (nest.Q n)) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ‖(nest.Q n).y - z₁‖ < ε := by
  intro ε hε
  obtain ⟨N, hN'⟩ := nest.shrinks ε hε
  refine ⟨N + 1, ?_⟩
  intro n hn
  -- at level `n ≥ 1` we look at the level `n - 1` of the nest, one step below
  have h1 : 1 ≤ n := by omega
  have hm : N ≤ n - 1 := by omega
  have hn' : n - 1 + 1 = n := Nat.sub_add_cancel h1
  -- the landing point of a ray lies in the filled Julia set
  have hzK : (nest.Q n).y ∈ Work.EL.K c :=
    Work.ELTop.landsN_mem_K hN (nest.Q n).lands_a
  have hQside : (nest.Q n).y ∈ Work.EL.pairSideNear (nest.Q (n - 1)) := by
    simpa [hn'] using hQ (n - 1)
  have hPside : (nest.Q n).y ∈ Work.EL.pairSideNear nest.P0 := by
    simpa [hn'] using hP (n - 1)
  exact hN' (n - 1) hm (nest.Q n).y hzK hQside hPside

end Work.GATE2.EXL
