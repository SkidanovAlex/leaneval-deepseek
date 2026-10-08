/-
# Frobenius' condition at `p = 2` for a cyclic `2`-subgroup

Let `G` be a finite group and `Q ≤ G` a cyclic `2`-subgroup.  Then
`N_G(Q)/C_G(Q)`, the group of automorphisms of `Q` induced by conjugation, is a `2`-group:
`Work.NPC.IsConjPGroup 2 Q`.

This is the "local" form of the restriction appearing in the Brauer–Suzuki classification:
the hypothesis that a Sylow `2`-subgroup is cyclic is used only through the fact that every
`2`-subgroup is cyclic, and for a cyclic `2`-subgroup the conclusion is elementary.

## The argument

* `Q` is a finite `2`-group, so `|Q| = 2 ^ k`.
* Conjugation gives `N_G(Q) →* MulAut Q` with kernel `C_G(Q)`; hence `|N_G(Q)/C_G(Q)|` divides
  `|Aut Q|` (Mathlib: `card_normalizerQuotientCentralizer_dvd_card_mulAut`).
* For a cyclic group `Q`, `|Aut Q| = φ(|Q|)` (Mathlib: `IsCyclic.card_mulAut`), and
  `φ (2 ^ k) = 2 ^ (k - 1)` (`totient_two_pow`).

Hence `|N_G(Q)/C_G(Q)|` divides the power of two `2 ^ (k - 1)` and `N_G(Q)/C_G(Q)` is a
`2`-group.

Note that no hypothesis `Q ≠ ⊥` is needed: for `Q = ⊥` the quotient is trivial.
-/
import Mathlib
import Submission.Work.NPC.Defs
import Submission.Work.BrauerSuzuki.Sylow.hasFrobeniusCondition_two_of_cyclic_sylow

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Sylow

/-- If a finite group `G` has a cyclic `2`-subgroup `Q`, then `N_G(Q)/C_G(Q)` is a `2`-group.

Indeed `N_G(Q)/C_G(Q)` embeds into `Aut(Q)`, a group of order `φ(|Q|) = φ(2 ^ k) = 2 ^ (k - 1)`,
since `Q` is a `2`-group. -/
theorem isConjPGroup_two_of_isCyclic_of_isPGroup {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) (hQcyc : IsCyclic ↥Q) (hQ2 : IsPGroup 2 Q) :
    Work.NPC.IsConjPGroup 2 Q := by
  show IsPGroup 2 (Subgroup.normalizer (Q : Set G) ⧸
    (Subgroup.centralizer (Q : Set G)).subgroupOf (Subgroup.normalizer (Q : Set G)))
  obtain ⟨k, hk⟩ := hQ2.exists_card_eq
  refine IsPGroup.of_card_dvd_pow (n := k - 1) ?_
  have h := card_normalizerQuotientCentralizer_dvd_card_mulAut Q
  rwa [@IsCyclic.card_mulAut ↥Q _ _ hQcyc, hk, totient_two_pow] at h

end Work.BrauerSuzuki.Sylow
