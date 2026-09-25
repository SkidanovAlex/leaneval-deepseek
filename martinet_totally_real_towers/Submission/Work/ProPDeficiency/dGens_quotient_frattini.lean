import Mathlib
import Submission.Work.ProPDeficiency.Basic
import Submission.Work.ProPDeficiency.dGens_eq_log_card_frattini
import Submission.Commons.GroupTheory.Frattini.frattini_quotient_eq_map

namespace Work.ProPDeficiency

-- File: Submission/Work/ProPDeficiency/dGens_quotient_frattini.lean, namespace `Work.ProPDeficiency`.
-- The Frattini subgroup of a finite `p`-group is a non-generator, in the counting form:
-- `dGens (G ⧸ Φ(G)) = dGens G`.  (`dGens` is in `Submission.Work.ProPDeficiency.Basic`;
-- `Work.ProPDeficiency.dGens_eq_log_card_frattini`, module
-- `Submission.Work.ProPDeficiency.dGens_eq_log_card_frattini`, gives
-- `Nat.card (G ⧸ Φ(G)) = p ^ dGens G` for finite `p`-groups `G`.)
--
-- Proof (route (b) of the sketch, i.e. Burnside's basis theorem in counting form, applied twice).
-- The quotient map `G ↠ Q := G ⧸ Φ(G)` is surjective, so `Q` is again a finite `p`-group
-- (`IsPGroup.to_quotient`).  Since `Φ(G) ≤ Φ(G)`, the commons lemma
-- `Commons.GroupTheory.Frattini.frattini_quotient_eq_map` (with `N := Φ(G)`) computes
-- `Φ(Q) = Φ(G)·Φ(G)/Φ(G) = ⊥`.  Applying `dGens_eq_log_card_frattini` to `G` and to `Q` gives
--   `Nat.card (G ⧸ Φ(G)) = p ^ dGens G`   and
--   `Nat.card (Q ⧸ Φ(Q)) = p ^ dGens Q`,
-- and the left hand sides agree because `Q ⧸ Φ(Q) = Q ⧸ ⊥ ≃* Q` (`QuotientGroup.quotientBot`).
-- Comparing the two powers of the prime `p` via `Nat.pow_right_injective` yields the result.
theorem dGens_quotient_frattini {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup p G) : dGens (G ⧸ frattini G) = dGens G := by
  -- `G ⧸ Φ(G)` is a finite `p`-group.
  have hQp : IsPGroup p (G ⧸ frattini G) := hG.to_quotient (frattini G)
  -- `Φ(G ⧸ Φ(G)) = Φ(G)·Φ(G)/Φ(G) = ⊥`.
  have hfratt : frattini (G ⧸ frattini G) = ⊥ := by
    rw [← Commons.GroupTheory.Frattini.frattini_quotient_eq_map (N := frattini G) le_rfl,
      Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  -- Burnside's basis theorem in counting form, for `G` ...
  have h1 : Nat.card (G ⧸ frattini G) = p ^ dGens G := dGens_eq_log_card_frattini hG
  -- ... and for `Q = G ⧸ Φ(G)`.
  have h2 : Nat.card ((G ⧸ frattini G) ⧸ frattini (G ⧸ frattini G)) =
      p ^ dGens (G ⧸ frattini G) := dGens_eq_log_card_frattini hQp
  -- `Q ⧸ Φ(Q) = Q ⧸ ⊥ ≃* Q`.
  rw [hfratt, Nat.card_congr QuotientGroup.quotientBot.toEquiv] at h2
  -- Hence `p ^ dGens (G ⧸ Φ(G)) = p ^ dGens G`, and `p ^ ·` is injective for a prime `p`.
  exact Nat.pow_right_injective (Fact.out : p.Prime).two_le (h2.symm.trans h1)

end Work.ProPDeficiency
