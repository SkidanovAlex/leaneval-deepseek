import Mathlib
import Submission.Work.HallHigman.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.HallHigman

/-- Cardinal identity for the join of two subgroups, the second being normal:
`|A ⊔ B| * |A ⊓ B| = |A| * |B|`. Equivalently `|A ⊔ B| = |B| * [B : A]`. -/
lemma card_sup_mul_card_inf {G : Type*} [Group G] (A B : Subgroup G) [B.Normal] :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  have hcard : ∀ {H K : Subgroup G}, Nat.card ↥(H.subgroupOf K) = Nat.card ↥(H ⊓ K) := by
    intro H K
    rw [← Subgroup.inf_subgroupOf_right H K]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := H ⊓ K) (K := K) inf_le_right).toEquiv
  have h1 : Nat.card ↥(A ⊔ B) = B.relIndex A * Nat.card ↥B := by
    rw [← Subgroup.index_mul_card (B.subgroupOf (A ⊔ B)),
      show (B.subgroupOf (A ⊔ B)).index = B.relIndex A from
        Subgroup.relIndex_sup_right (H := A) (K := B),
      hcard (H := B) (K := A ⊔ B), inf_of_le_left le_sup_right]
  have h2 : Nat.card ↥A = B.relIndex A * Nat.card ↥(A ⊓ B) := by
    rw [← Subgroup.index_mul_card (B.subgroupOf A),
      show (B.subgroupOf A).index = B.relIndex A from rfl,
      hcard (H := B) (K := A), inf_comm]
  rw [h1, h2]; ring

/-- The join of two normal `π`-subgroups is a normal `π`-subgroup. -/
lemma sup_mem_piSet {π : ℕ → Prop} {G : Type*} [Group G] {N M : Subgroup G}
    (hN : N.Normal ∧ IsPiNat π (Nat.card ↥N)) (hM : M.Normal ∧ IsPiNat π (Nat.card ↥M)) :
    (N ⊔ M).Normal ∧ IsPiNat π (Nat.card ↥(N ⊔ M)) := by
  haveI : N.Normal := hN.1
  haveI : M.Normal := hM.1
  refine ⟨inferInstance, ?_⟩
  have hdvd : Nat.card ↥(N ⊔ M) ∣ Nat.card ↥N * Nat.card ↥M :=
    ⟨Nat.card ↥(N ⊓ M), (card_sup_mul_card_inf N M).symm⟩
  exact (IsPiNat.mul hN.2 hM.2).of_dvd hdvd

/-- `O_π(G)`, defined as the supremum of the normal `π`-subgroups, is a `π`-group. -/
lemma piCore_isPiNat {π : ℕ → Prop} {G : Type*} [Group G] [Finite G] :
    IsPiNat π (Nat.card ↥(piCore π G)) := by
  classical
  -- The normal `π`-subgroups form a set which is closed under joins (whence directed)
  -- and finite, so it has a maximal element `N`.
  let S : Set (Subgroup G) := {N | N.Normal ∧ IsPiNat π (Nat.card ↥N)}
  have hSne : S.Nonempty :=
    ⟨⊥, Subgroup.normal_bot, by simpa using (IsPiNat.one (π := π))⟩
  obtain ⟨N, hNmax⟩ := (Set.toFinite S).exists_maximal hSne
  have hNnor : N.Normal := hNmax.1.1
  have hNpi : IsPiNat π (Nat.card ↥N) := hNmax.1.2
  haveI : N.Normal := hNnor
  -- `N` contains every normal `π`-subgroup, because `N ⊔ M` is again one.
  have hle : piCore π G ≤ N := by
    rw [piCore]
    apply sSup_le
    intro M hM
    exact le_sup_right.trans (hNmax.2 (sup_mem_piSet hNmax.1 hM) le_sup_left)
  have hge : N ≤ piCore π G := le_piCore hNnor hNpi
  have heq : piCore π G = N := le_antisymm hle hge
  rw [heq]
  exact hNpi

end Work.HallHigman
