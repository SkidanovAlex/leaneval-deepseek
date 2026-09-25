import Mathlib
import Submission.Work.ProPDeficiency.Basic
import Submission.Commons.GroupTheory.PGroup.burnside_basis

namespace Work.ProPDeficiency

-- File: Submission/Work/ProPDeficiency/dGens_eq_log_card_frattini.lean, namespace `Work.ProPDeficiency`.
-- Burnside's basis result in counting form: for a finite `p`-group `G`, the elementary abelian
-- `p`-group `G ⧸ Φ(G)` has order `p ^ dGens G`.
-- `dGens` and `IsMinimalGeneratingSet` are defined in `Submission.Work.ProPDeficiency.Basic`
-- (`dGens G = sInf {card S | S generates G}`, and `IsMinimalGeneratingSet.dGens_eq` computes
-- `dGens G` from a minimal generating set).
-- The workspace commons already has `Commons.GroupTheory.PGroup.burnside_basis`, so add the import
-- `Submission.Commons.GroupTheory.PGroup.burnside_basis` to the file's import list yourself.  Its
-- conclusion is
--   `∃ S : Finset G, Nat.card (G ⧸ frattini G) = p ^ S.card ∧ Subgroup.closure (S : Set G) = ⊤ ∧
--      ∀ T : Finset G, Subgroup.closure (T : Set G) = ⊤ → S.card ≤ T.card`
-- so the work is: take that `S`, observe it is a minimal generating set, and rewrite `S.card` as
-- `dGens G` via `IsMinimalGeneratingSet.dGens_eq`.
theorem dGens_eq_log_card_frattini {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup p G) : Nat.card (G ⧸ frattini G) = p ^ dGens G := by
  obtain ⟨S, hcard, hgen, hmin⟩ := Commons.GroupTheory.PGroup.burnside_basis (p := p) hG
  have hminimal : IsMinimalGeneratingSet S := ⟨hgen, fun T hT => hmin T hT⟩
  rw [hcard, ← hminimal.dGens_eq]

end Work.ProPDeficiency
