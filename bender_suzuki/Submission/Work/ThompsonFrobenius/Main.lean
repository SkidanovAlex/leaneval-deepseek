import Submission.Work.ThompsonFrobenius.Defs
import Submission.Work.ThompsonFrobenius.Structure
import Submission.Work.ThompsonFrobenius.Minimal
import Submission.Work.ThompsonFrobenius.card_modEq_one
import Submission.Work.ThompsonFrobenius.induced_isFpf
import Submission.Work.ThompsonFrobenius.hasNormalPComplement_of_isNilpotent
import Submission.Work.ThompsonFrobenius.isSolvable_of_minimal_oddCore_ne_bot
import Submission.Work.ThompsonFrobenius.invariant_normal_eq_bot_or_top
import Submission.Work.ThompsonFrobenius.oddCore_eq_bot
import Submission.Work.ThompsonFrobenius.ZJ_subgroupOf
import Submission.Work.ThompsonFrobenius.Prelim
import Submission.Work.ThompsonFrobenius.subgroupOfMulEquivInf
import Submission.Work.ThompsonFrobenius.hasNormalPComplement_normalizer_subgroupOf
import Submission.Work.ThompsonFrobenius.npc_of_le
import Submission.Work.ThompsonFrobenius.npc_normalizer_of_not_normal
import Submission.Work.ThompsonFrobenius.pCore_ne_bot
import Submission.Work.ThompsonFrobenius.pCore_lt
import Submission.Work.ThompsonFrobenius.pPrimeCore_eq_bot
import Submission.Work.ThompsonFrobenius.npc_quotient
import Submission.Work.ThompsonFrobenius.normalizer_sup_of_coprime
import Submission.Work.ThompsonFrobenius.centralizer_pCore_le
import Submission.Work.ThompsonFrobenius.isInv_of_isNormalPComplement
import Submission.Work.ThompsonFrobenius.isSolvable_of_nilpotent_normal
import Submission.Work.ThompsonFrobenius.eq_of_le
import Submission.Work.ThompsonFrobenius.commutator_le
import Submission.Work.ThompsonFrobenius.isSolvable
import Submission.Work.ThompsonFrobenius.abelianSylowTwo
import Submission.Work.ThompsonFrobenius.gtMinimal_false
import Submission.Work.ThompsonFrobenius.glauberman_thompson
import Submission.Work.ThompsonFrobenius.isNilpotent_of_fpf_pow
import Submission.Work.ThompsonFrobenius.thompsonFrobenius

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Area `ThompsonFrobenius`: assembly

Thompson (1959): a finite group admitting a fixed-point-free automorphism of prime order is
nilpotent (the blueprint's `Submission.Blueprint.ThompsonFrobeniusProp`).

## The area theorem (DONE)

```lean
theorem Work.ThompsonFrobenius.thompsonFrobenius
    (hFT : Submission.Blueprint.FeitThompsonProp)
    (hZJ : Submission.Blueprint.GlaubermanZJProp) :
    Submission.Blueprint.ThompsonFrobeniusProp
```
in `Submission/Work/ThompsonFrobenius/thompsonFrobenius.lean`.  Following
`NOTES_LEAD_bs_thompson.md`, the theorem is deduced from the **Glauberman–Thompson normal
`p`-complement theorem (Glauberman 1968, Theorem D, `p` odd)** — exported as
`Work.ThompsonFrobenius.glauberman_thompson` — with the `ZJ` input taken from `GlaubermanZJProp`
(hence the extra hypothesis `hZJ`; the graph edge `ThompsonFrobenius → GlaubermanZJ` is acyclic).
`hFT` is carried for the blueprint's convention but is *not used* by this route.

## Interface of the area

* **Theorem D** — `Work.ThompsonFrobenius.GTStatement`, `Work.ThompsonFrobenius.GTMinimal`
  (`GTDefs.lean`) and `Work.ThompsonFrobenius.glauberman_thompson` (`glauberman_thompson.lean`):
  for an odd prime `p` and a finite group `G`, `N_G(Z(J(P)))` `p`-nilpotent implies `G`
  `p`-nilpotent.  Its minimal-counterexample steps (each its own module/lemma):
  `npc_of_le` (GT-c), `npc_normalizer_of_not_normal` (GT-d), `pCore_ne_bot` (GT-1),
  `pPrimeCore_eq_bot` (GT-2), `pCore_lt` (GT-2'), `npc_quotient` (GT-3),
  `centralizer_pCore_le` (GT-4), `eq_of_le` (GT-5), `commutator_le` (GT-6),
  `isSolvable` (GT-7a), `abelianSylowTwo` (GT-7b), `gtMinimal_false` (GT-8).
* **Thompson's theorem** — `Work.ThompsonFrobenius.isNilpotent_of_fpf_pow`
  (`isNilpotent_of_fpf_pow.lean`): strong induction on `|K|` for `α ^ q = 1`, `q` prime, `α`
  fixed-point-free.  Supporting: `restrictEquiv_pow_eq_one` (M1), `isInv_of_isNormalPComplement`
  (M2), `isSolvable_of_nilpotent_normal` (M3), `induced_isFpf`, plus the delivered
  `Work.Frobenius.Fpf.{isNilpotent_of_fpf_prime, isFpf_restrict, exists_invariant_sylow}` and
  `Work.GlaubermanZJ.isAbelianSubgroup_ZJ`.
* `hasNormalPComplement_of_isNilpotent` (M2b) — a finite nilpotent group is `p`-nilpotent.
* Further special cases and tools kept from the earlier route (still valid, sorry-free):
  `isNilpotent_of_orderOf_eq_two` (order-two automorphisms, proved outright),
  `isNilpotent_of_fpf_of_odd` / `isNilpotent_of_fpf_of_solvable` (from `FeitThompsonProp` /
  from solvability), `ThmBelow`/`IsMinimalCounterexample` (`Minimal.lean`),
  `invariant_normal_eq_bot_or_top`, `oddCore_eq_bot`, `card_modEq_one`,
  `hasNormalPComplement_of_normalizers`.
* Auxiliary transport lemmas built for the area: `ZJ_subgroupOf`, `normalizer_le_normalizer_ZJ`,
  `ZJ_map_of_ker_inf_eq_bot`, `ZJ_map_mulAut`, `ZJ_le`, `ZJ_ne_bot`, `Prelim.lean`
  (`isPGroup_of_le`, `isPiNat_card_of_isPGroup`, `exists_map_conj_le_sylow`,
  `hasNormalPComplement_normalizer_map_conj_iff`, `card_le_card_sylow_of_isPGroup`),
  `subgroupOfMulEquivInf.lean`, `hasNormalPComplement_normalizer_subgroupOf.lean`,
  `normalizer_sup_of_coprime.lean` (a Frattini computation).
* `Defs.lean` still records the *abandoned* route through `SolvabilityStep`
  (`thompsonFrobenius_of_solvability`); it is superseded by the files above and kept only to avoid
  deleting anything.
-/

set_option autoImplicit false
