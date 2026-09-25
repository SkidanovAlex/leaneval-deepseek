import Mathlib
import Submission.Work.ProPDeficiency.Basic
import Submission.Work.ProPDeficiency.dGens_eq_log_card_frattini
import Submission.Commons.GroupTheory.PGroup.quotient_frattini_exponent_p
import Submission.Commons.GroupTheory.Nilpotent.isNilpotent_iff_commutator_le_frattini

namespace Work.ProPDeficiency

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped IsMulCommutative

-- File: Submission/Work/ProPDeficiency/nonempty_equiv_frattini_zmod_pow.lean, namespace `Work.ProPDeficiency`.
-- Burnside's basis result in the literal "dimension" form: for a finite `p`-group `G`, the
-- elementary abelian `p`-group `G ⧸ Φ(G)` is isomorphic to the `dGens G`-dimensional `𝔽_p`-vector
-- space `Fin (dGens G) → Multiplicative (ZMod p)`, so `dGens G = dim_{𝔽_p} (G ⧸ Φ(G))`.
-- `dGens` is defined in `Submission.Work.ProPDeficiency.Basic`, and
-- `Work.ProPDeficiency.dGens_eq_log_card_frattini` (module
-- `Submission.Work.ProPDeficiency.dGens_eq_log_card_frattini`, already proved) gives
-- `Nat.card (G ⧸ frattini G) = p ^ dGens G`.
-- The extra ingredients used here, both from the commons:
-- * `Commons.GroupTheory.PGroup.quotient_frattini_exponent_p` : `G ⧸ Φ(G)` has exponent `p`;
-- * `Commons.GroupTheory.Nilpotent.isNilpotent_iff_commutator_le_frattini` : `[G,G] ≤ Φ(G)`, so
--   `G ⧸ Φ(G)` is abelian.
-- Together these exhibit `Additive (G ⧸ Φ(G))` as a finite `𝔽_p`-vector space of cardinality
-- `p ^ Module.finrank`, compare with `Nat.card (G ⧸ Φ(G)) = p ^ dGens G`, and conclude
-- `finrank = dGens G` by injectivity of `p ^ ·`; a `Module.finBasis` then gives the linear
-- equivalence which transports to the asserted group isomorphism.
theorem nonempty_equiv_frattini_zmod_pow {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup p G) :
    Nonempty (G ⧸ frattini G ≃* (Fin (dGens G) → Multiplicative (ZMod p))) := by
  classical
  -- `G ⧸ Φ(G)` is abelian ...
  haveI hcomm : IsMulCommutative (G ⧸ frattini G) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := frattini G)).mpr
      ((Commons.GroupTheory.Nilpotent.isNilpotent_iff_commutator_le_frattini (G := G)).mp
        hG.isNilpotent)
  -- ... and of exponent `p`.
  have hexp : ∀ x : G ⧸ frattini G, x ^ p = 1 :=
    fun x => Commons.GroupTheory.PGroup.quotient_frattini_exponent_p hG x
  have hpV : ∀ x : Additive (G ⧸ frattini G), p • x = 0 := by
    intro x
    exact Additive.toMul.injective (by simp [toMul_nsmul, hexp x.toMul])
  -- Hence an `𝔽_p`-vector space.
  letI hmod : Module (ZMod p) (Additive (G ⧸ frattini G)) := AddCommGroup.zmodModule hpV
  haveI hfin : Module.Finite (ZMod p) (Additive (G ⧸ frattini G)) := Module.Finite.of_finite
  haveI hfree : Module.Free (ZMod p) (Additive (G ⧸ frattini G)) :=
    Module.Free.of_divisionRing (ZMod p) (Additive (G ⧸ frattini G))
  -- Its cardinality is `p ^ finrank`.
  have hcardV : Nat.card (Additive (G ⧸ frattini G)) =
      p ^ @Module.finrank (ZMod p) (Additive (G ⧸ frattini G)) _ _ hmod := by
    rw [@Module.natCard_eq_pow_finrank (ZMod p) (Additive (G ⧸ frattini G)) _ _ hmod hfin,
      Nat.card_eq_fintype_card, ZMod.card]
  -- Burnside's basis theorem gives the same cardinality as `p ^ dGens G`.
  have hcardQ : Nat.card (Additive (G ⧸ frattini G)) = p ^ dGens G := by
    rw [Nat.card_congr Additive.ofMul]
    exact dGens_eq_log_card_frattini (p := p) hG
  -- Injectivity of `p ^ ·` yields the dimension count `finrank = dGens G`.
  have hfr : @Module.finrank (ZMod p) (Additive (G ⧸ frattini G)) _ _ hmod = dGens G :=
    Nat.pow_right_injective (Fact.out : p.Prime).two_le (hcardV.symm.trans hcardQ)
  -- A basis realises the quotient as `Fin (dGens G) → 𝔽_p`, and `Additive`/`Multiplicative`
  -- translate the linear equivalence into the asserted group isomorphism.
  let b := @Module.finBasis (ZMod p) (Additive (G ⧸ frattini G)) _ _ hmod hfree _ hfin
  let e := b.equivFun
  have he : (Additive (G ⧸ frattini G)) ≃ₗ[ZMod p] (Fin (dGens G) → ZMod p) := by
    rw [← hfr]
    exact e
  exact ⟨he.toAddEquiv.toMultiplicative⟩

end Work.ProPDeficiency
