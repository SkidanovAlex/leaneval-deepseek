/-
Area A9 (normal `p`-complement theorems): fusion of a conjugacy-closed Sylow subgroup.

If two elements of `P` that are conjugate in `G` are already conjugate in `P` (i.e. `P` is
*conjugacy-closed* in `G`), then every focal generator `⁅x, u⁆` (`x, u ∈ G`, `⁅x, u⁆ ∈ P`) can be
rewritten as `⁅x, c⁆` with `c ∈ P`, so the focal subgroup of `P` is contained in `⁅P, P⁆`; conversely
`⁅P, P⁆ ≤ P*` always holds, hence `P* = ⁅P, P⁆`.

Combined with `Work.NPC.hasNormalPComplement_of_focalSubgroup_eq_commutator` (the transfer
criterion `G' ∩ P = P' ⟹ G` has a normal `p`-complement) this yields the classical theorem that a
group with a conjugacy-closed Sylow `p`-subgroup has a normal `p`-complement.
-/
import Submission.Work.NPC.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

noncomputable section

open scoped Pointwise commutatorElement

namespace Work.NPC

variable {G : Type*} [Group G]

/-- If `P` is conjugacy-closed in `G`, then the focal subgroup of `P` is contained in the
commutator subgroup `⁅P, P⁆`: every focal generator `⁅x, u⁆` with `x, ⁅x, u⁆ ∈ P` equals `⁅x, c⁆`
for some `c ∈ P`. -/
theorem focalSubgroup_le_commutator_of_conjugacyClosed {P : Subgroup G}
    (h : ∀ x y : ↥P, IsConj (x : G) (y : G) → IsConj x y) :
    P.focalSubgroup ≤ ⁅P, P⁆ := by
  rw [Subgroup.focalSubgroup_def]
  refine (Subgroup.closure_le ⁅P, P⁆).mpr ?_
  rintro g ⟨hgP, x, hxP, u, rfl⟩
  -- the conjugate `u * x * u⁻¹` of `x` lies in `P`
  have hy : u * x * u⁻¹ ∈ P := by
    have h1 : u * x * u⁻¹ = ⁅x, u⁆⁻¹ * x := by rw [commutatorElement_def]; group
    rw [h1]
    exact P.mul_mem (P.inv_mem hgP) hxP
  -- conjugacy-closedness rewrites the conjugation by `u` as a conjugation by `c ∈ P`
  have hconj : IsConj (x : G) (u * x * u⁻¹ : G) :=
    isConj_iff.mpr ⟨(⟨u, u⁻¹, mul_inv_cancel u, inv_mul_cancel u⟩ : Gˣ), by simp⟩
  obtain ⟨c, hc⟩ := isConj_iff.mp (h ⟨x, hxP⟩ ⟨u * x * u⁻¹, hy⟩ hconj)
  have hy_eq : u * x * u⁻¹ = ((c : ↥P) : G) * x * (((c : ↥P) : G))⁻¹ := by
    simpa using (congrArg Subtype.val hc).symm
  have h3 : ⁅x, u⁆ = x * (u * x * u⁻¹)⁻¹ := by rw [commutatorElement_def]; group
  have h4 : x * ((((c : ↥P) : G)) * x * (((c : ↥P) : G))⁻¹)⁻¹ = ⁅x, ((c : ↥P) : G)⁆ := by
    rw [commutatorElement_def]; group
  rw [h3, hy_eq, h4]
  exact Subgroup.commutator_mem_commutator hxP (c : ↥P).2

/-- For a conjugacy-closed subgroup `P ≤ G`, the focal subgroup of `P` is exactly its commutator
subgroup `⁅P, P⁆`. -/
theorem focalSubgroup_eq_commutator_of_conjugacyClosed {P : Subgroup G}
    (h : ∀ x y : ↥P, IsConj (x : G) (y : G) → IsConj x y) :
    P.focalSubgroup = ⁅P, P⁆ :=
  le_antisymm (focalSubgroup_le_commutator_of_conjugacyClosed h)
    (Subgroup.commutator_le_focalSubgroup P)

end Work.NPC
