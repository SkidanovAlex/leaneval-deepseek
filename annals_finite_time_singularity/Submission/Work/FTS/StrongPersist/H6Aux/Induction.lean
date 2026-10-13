/-
# `Work.FTS.StrongPersist.H6Aux.Induction` — the commutator induction for `Lhat`

The paper's one-sided bound at level six is the statement `H6Lin`, and it is proved here by
running the paper's *commutator* induction on the family `IPnG 1 1 α n`, `n ≤ 5`, for the
clean operator `Lhat = 𝓛 − Transport`, whose two defect identities

  `Dth (Lhat h) = Lhat (Dth h)`,   `Dz (Lhat h) = Lhat (Dz h) + Ê₂ h`

are supplied by `LhatCommOpen`.  The recursion

  `IPnG (n+1) u v = IPnG n u v + IPnG n (Dth u) (Dth v) + IPnG n (Dz u) (Dz v)`

turns the pairing with `Lhat h` into the level-`n` pairings with `Lhat h`, `Lhat (Dth h)` and
`Lhat (Dz h)` (shifted by the explicit defect `Ê₂ h`), so the induction hypothesis applied to
`h`, `Dth h`, `Dz h` gives the level-`(n+1)` pairing with `Lhat h` up to the single correction
`IPnG n (Ê₂ h) (Dz h)`, which Cauchy–Schwarz and the defect bound `HkSq_E2hat_le` price by the
diagonal `IPnG (n+1) h h` (through the slot cover `lo_IPnG`).

The base case `n = 0` is the *level-one* estimate `base_R`, proved from the two integration by
parts `wip_Dz_ibp`, `wip_Dth_ibp`.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongPersist.H6Aux.IPChains
import Submission.Work.FTS.StrongPersist.H6Aux.Facts
import Submission.Work.FTS.StrongPersist.H6Aux.E2Facts
import Submission.Work.FTS.StrongPersist.H6Aux.LhatFacts
import Submission.Work.FTS.StrongPersist.H6Aux.RStep
import Submission.Work.FTS.StrongPersist.H6Aux.base_R

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Aux

open Work.FTS.Galerkin (Fn)
open Work.FTS.IPGen (IPnG IPnG_zero IPnG_succ)
open Work.FTS.CoercivityFix.Transfer (CommSm CSQ AddOKSm)

set_option autoImplicit false

/-- **The commutator induction.**  For every `n ≤ 5` there is a constant `r > 0` with
`IPnG 1 1 α n (Lhat h) h ≥ -r · IPnG 1 1 α n h h` for every `h` of class `SmoothOpen` with
honest `ℋ^{n+2}`-integral. -/
theorem R_ind : ∀ n : ℕ, n ≤ 5 → ∃ r : ℝ, 0 < r ∧ ∀ α ∈ Set.Ioc 0 1, ∀ h : Fn,
    Work.FTS.EllipticEst.SmoothOpen h → Work.Spaces.HkMem α (n + 2) h →
      -r * IPnG 1 1 α n h h ≤ IPnG 1 1 α n (Work.FTS.CoercivityFix.Lhat h) h := by
  intro n hn
  induction n with
  | zero =>
      obtain ⟨r, hr, h⟩ := base_R
      exact ⟨r, hr, fun α hα h' hs hm => by
        simpa only [IPnG_zero] using h α hα h' hs hm⟩
  | succ n ih =>
      exact R_step n (by omega) (ih (by omega))

end Work.FTS.StrongPersist.H6Aux
