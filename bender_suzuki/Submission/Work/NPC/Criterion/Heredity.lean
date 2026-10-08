/-
Area A9, sub-area `Criterion`: the transfer criterion is inherited by subgroups containing a Sylow.

If `(P : Subgroup G).focalSubgroup = ⁅P, P⁆` for a Sylow `p`-subgroup `P` of `G`, then for every
subgroup `H` with `P ≤ H ≤ G` one has `⁅H, H⁆ ⊓ P = ⁅P, P⁆`.  (Note that `P` is a Sylow
`p`-subgroup of `H` as well, so this says precisely that the criterion holds for `H`.)

Proof: `⁅P, P⁆ ≤ ⁅H, H⁆ ⊓ P` because `P ≤ H`, and `⁅H, H⁆ ≤ G'` so
`⁅H, H⁆ ⊓ P ≤ G' ⊓ P = P* = ⁅P, P⁆` by the focal subgroup theorem and the hypothesis.

This heredity is *false* if one replaces `P ≤ H` by an arbitrary subgroup, and it is the key
observation behind the minimal-counterexample analysis of the criterion (see `HINTS.md` §2).
-/
import Mathlib
import Submission.Work.NPC.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise commutatorElement

namespace Work.NPC.Criterion

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- **Heredity of the transfer criterion.**  If `P` is a Sylow `p`-subgroup of `G` with
`P* = ⁅P, P⁆`, then every subgroup `H` with `P ≤ H ≤ G` satisfies the criterion for its Sylow
subgroup `P`: `⁅H, H⁆ ⊓ P = ⁅P, P⁆`. -/
theorem commutator_inf_eq_of_focalSubgroup_eq_commutator (P : Sylow p G)
    (h : (P : Subgroup G).focalSubgroup = ⁅(P : Subgroup G), (P : Subgroup G)⁆)
    {H : Subgroup G} (hPH : (P : Subgroup G) ≤ H) :
    ⁅H, H⁆ ⊓ (P : Subgroup G) = ⁅(P : Subgroup G), (P : Subgroup G)⁆ := by
  refine le_antisymm ?_ ?_
  · -- `⁅H, H⁆ ⊓ P ≤ G' ⊓ P = P* = ⁅P, P⁆`
    have h1 : ⁅H, H⁆ ⊓ (P : Subgroup G) ≤ _root_.commutator G ⊓ (P : Subgroup G) :=
      inf_le_inf (Subgroup.commutator_mono le_top le_top) le_rfl
    rw [Subgroup.commutator_inf_eq_focalSubgroup, h] at h1
    exact h1
  · -- `⁅P, P⁆ ≤ ⁅H, H⁆ ⊓ P` since `P ≤ H`
    exact le_inf (Subgroup.commutator_mono hPH hPH)
      (Subgroup.commutator_le_self (P : Subgroup G))

/-- The criterion for every subgroup containing a Sylow, in the `HasNormalPComplement`-free form:
the commutator subgroups computed in `G` and in `H` agree on `P`. -/
theorem commutator_inf_eq_commutator_of_focalSubgroup_eq_commutator (P : Sylow p G)
    (h : (P : Subgroup G).focalSubgroup = ⁅(P : Subgroup G), (P : Subgroup G)⁆)
    {H : Subgroup G} (hPH : (P : Subgroup G) ≤ H) :
    ⁅H, H⁆ ⊓ (P : Subgroup G) = _root_.commutator G ⊓ (P : Subgroup G) := by
  rw [commutator_inf_eq_of_focalSubgroup_eq_commutator P h hPH,
    Subgroup.commutator_inf_eq_focalSubgroup, h]

end Work.NPC.Criterion
