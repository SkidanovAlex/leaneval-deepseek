import Mathlib
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.exists_conj_mem_sylow

/-!
# CORE3: `2`-elements of `Ĥ` are conjugate into `S` inside `Ĥ`

Bender's notation: `S` is a Sylow `2`-subgroup, `S₀ ≤ S` cyclic of index `2`, `t ∈ S₀` an
involution, and `Ĥ` a maximal subgroup with `C_G(t) ≤ Ĥ`.  From the axioms of `BenderSetup`
one gets `S ≤ C_G(t) ≤ Ĥ` (`Work.CORE2A.bSetup_S_le_Hhat`): the involution of a cyclic group
is unique, so `t` is central in `S`.  Consequently `S` is *also* a Sylow `2`-subgroup of `Ĥ`,
and Sylow conjugacy for the finite group `Ĥ` (`Work.CORE2A.exists_conj_mem_sylow`) conjugates
every `2`-element of `Ĥ` into `S` by an element of `Ĥ`.

The statement is phrased with `orderOf g = 2 ^ v` rather than `g` a `2`-element so that the
conclusion can be fed to the coset-counting arguments of §3, where the elements indexed by
`n = 2^v` are involutions of `Ĥ`.
-/

namespace Work.CORE3

open Subgroup

theorem ConjMemSOfOrderTwoPow {G : Type} [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) {g : G} (hg : g ∈ B.Hhat) {v : ℕ} (hord : orderOf g = 2 ^ v) :
    ∃ c ∈ B.Hhat, c * g * c⁻¹ ∈ (B.S : Subgroup G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxp : IsPGroup 2 ↥(Subgroup.zpowers g) := by
    refine (IsPGroup.iff_card).mpr ⟨v, ?_⟩
    simp [Nat.card_zpowers, hord]
  exact Work.CORE2A.exists_conj_mem_sylow 2 B.S (Work.CORE2A.bSetup_S_le_Hhat B) hg hxp

end Work.CORE3
