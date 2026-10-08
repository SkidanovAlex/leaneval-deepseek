import Mathlib
import Submission.Work.ThompsonFrobenius.Defs
import Submission.Work.ThompsonFrobenius.induced_isFpf
import Submission.Work.Frobenius.Fpf.isNilpotent_of_fpf_prime
import Submission.Work.HallHigman.piCore_isPiNat

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Thompson's theorem: a minimal counterexample has `O(G) = 1`

Thompson's theorem (a finite group with a fixed-point-free automorphism of prime order is
nilpotent) is proved by induction on `|Q|`; the induction step shows that a minimal
counterexample cannot have a non-trivial normal subgroup of odd order.

This file proves the corresponding step.  Let `Q` be finite with `O(Q) = O_{2'}(Q) ≠ 1` (the
largest normal subgroup of odd order) and let `α` be a fixed-point-free automorphism of `Q` of
prime order, such that every group of smaller order with a fixed-point-free automorphism of
prime order is solvable (`hbelow`).  Then `Q` is solvable:

* `O(Q)` is odd, hence solvable by Feit–Thompson (`hFT`), and
* `O(Q)` is normal and `α`-invariant, so `α` induces a fixed-point-free automorphism of prime
  order on `Q ⧸ O(Q)` (`induced_isFpf`), whence `Q ⧸ O(Q)` is solvable by `hbelow`.

If `O(Q) = ⊤` there is nothing to do: `|Q|` is odd and `hFT` applies directly.  A group extending
a solvable normal subgroup with solvable quotient is solvable
(`Group.isSolvable_of_subgroup_quotient`).
-/

set_option autoImplicit false

namespace Work.ThompsonFrobenius

variable {G : Type*}

/-! ## The odd core `O(G) = O_{2'}(G)` -/

/-- Every automorphism of `G` maps `O(G)` into `O(G)`: the defining family
`{N | N.Normal ∧ Odd (Nat.card N)}` is stable under `Subgroup.map` of an automorphism, because
normality is preserved under surjective homomorphisms and `Subgroup.map` of an injective map
preserves cardinality. -/
theorem map_oddCore_le_oddCore [Group G] (α : MulAut G) :
    (Submission.Blueprint.oddCore G).map α.toMonoidHom ≤ Submission.Blueprint.oddCore G := by
  unfold Submission.Blueprint.oddCore
  rw [(Subgroup.gc_map_comap α.toMonoidHom).l_sSup]
  refine iSup_le fun N => iSup_le fun hN => le_sSup ?_
  exact ⟨hN.1.map α.toMonoidHom α.surjective,
    by rw [Subgroup.card_map_of_injective α.injective]; exact hN.2⟩

/-- `O(G)` is invariant under every automorphism of `G` (apply the previous lemma to `α` and to
`α⁻¹`). -/
theorem isInv_oddCore [Group G] (α : MulAut G) :
    Work.NPC.Fpf.IsInv α (Submission.Blueprint.oddCore G) := by
  intro x
  constructor
  · intro hx
    have h := map_oddCore_le_oddCore (G := G) (α := α⁻¹)
      (Subgroup.mem_map_of_mem (α⁻¹).toMonoidHom hx)
    simpa using h
  · intro hx
    exact map_oddCore_le_oddCore (G := G) (α := α) (Subgroup.mem_map_of_mem α.toMonoidHom hx)

/-- `O(G) = O_{2'}(G)`: for a subgroup, "odd order" is the same as "no prime divisor equal to
`2`". -/
theorem oddCore_eq_opCore_two (G : Type*) [Group G] :
    Submission.Blueprint.oddCore G = Work.HallHigman.opCore 2 G := by
  have hset : {N : Subgroup G | N.Normal ∧ Odd (Nat.card ↥N)}
      = {N : Subgroup G | N.Normal ∧ Work.HallHigman.IsPiNat (fun p => p ≠ 2) (Nat.card ↥N)} := by
    ext N
    constructor
    · rintro ⟨hN, hodd⟩
      refine ⟨hN, fun p _ hp2 hpe => ?_⟩
      rw [hpe] at hp2
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hp2)
    · rintro ⟨hN, hpi⟩
      exact ⟨hN, Nat.not_even_iff_odd.mp fun he =>
        hpi 2 Nat.prime_two (even_iff_two_dvd.mp he) rfl⟩
  unfold Submission.Blueprint.oddCore Work.HallHigman.opCore
  rw [hset]
  rfl

/-- `O(G)` has odd order in a finite group: it is the `2'`-core, which is a `2'`-group
(`Work.HallHigman.piCore_isPiNat`). -/
theorem odd_oddCore (G : Type*) [Group G] [Finite G] :
    Odd (Nat.card (Submission.Blueprint.oddCore G)) := by
  have h1 : Work.HallHigman.IsPiNat (fun p => p ≠ 2)
      (Nat.card ↥(Work.HallHigman.opCore 2 G)) :=
    Work.HallHigman.piCore_isPiNat
  rw [← oddCore_eq_opCore_two] at h1
  exact Nat.not_even_iff_odd.mp fun he => h1 2 Nat.prime_two (even_iff_two_dvd.mp he) rfl

/-! ## The induction step -/

theorem isSolvable_of_minimal_oddCore_ne_bot (hFT : Submission.Blueprint.FeitThompsonProp) {Q : Type} [Group Q] [Finite Q] {α : MulAut Q} (hprime : (orderOf α).Prime) (hfpf : Work.NPC.Fpf.IsFpf α) (hbelow : ∀ (K : Type) [Group K] [Finite K] (β : MulAut K), Nat.card K < Nat.card Q → (orderOf β).Prime → Work.NPC.Fpf.IsFpf β → Group.IsSolvable K) (hcore : Submission.Blueprint.oddCore Q ≠ ⊥) : Group.IsSolvable Q := by
  set O : Subgroup Q := Submission.Blueprint.oddCore Q with hOdef
  have hOnormal : O.Normal := by
    rw [hOdef]
    exact Subgroup.sSup_normal _ fun N hN => hN.1
  have hOodd : Odd (Nat.card ↥O) := by
    rw [hOdef]
    exact odd_oddCore Q
  have hOinv : Work.NPC.Fpf.IsInv α O := by
    rw [hOdef]
    exact isInv_oddCore α
  haveI : O.Normal := hOnormal
  have hOsolv : Group.IsSolvable ↥O := hFT ↥O hOodd
  rcases eq_or_ne O ⊤ with htop | htop
  · -- `O = ⊤`, so `Q` has odd order
    have hoddQ : Odd (Nat.card Q) := by
      rw [← Subgroup.card_top (G := Q), ← htop]
      exact hOodd
    exact hFT Q hoddQ
  · -- `O ≠ ⊤`: induction on `O` and on `Q ⧸ O`
    obtain ⟨hβord, hβfpf⟩ :=
      induced_isFpf (G := Q) (q := orderOf α) hprime (pow_orderOf_eq_one α) hfpf
        (H := O) hOinv htop
    have hlt : Nat.card (Q ⧸ O) < Nat.card Q := by
      have hpos : 0 < Nat.card (Q ⧸ O) := Nat.card_pos
      have hone : 1 < Nat.card ↥O := (Subgroup.one_lt_card_iff_ne_bot O).2 hcore
      rw [← Subgroup.index_eq_card O, ← Subgroup.index_mul_card O]
      exact (Nat.lt_mul_iff_one_lt_right hpos).2 hone
    have hquot : Group.IsSolvable (Q ⧸ O) :=
      hbelow (Q ⧸ O) (QuotientGroup.congr O O α (by simpa using hOinv.map_eq))
        hlt (by rw [hβord]; exact hprime) hβfpf
    haveI := hOsolv
    haveI := hquot
    exact Group.isSolvable_of_subgroup_quotient O

end Work.ThompsonFrobenius
