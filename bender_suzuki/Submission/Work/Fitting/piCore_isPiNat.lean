import Mathlib
import Submission.Work.Fitting.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

noncomputable section

open Classical

namespace Work.Fitting

/-!
# `O_π(G)` is a `π`-group

For a finite group `G`, the `π`-core `O_π(G) = O_π` — defined as the supremum of the normal
`π`-subgroups — is itself a normal `π`-subgroup, i.e. `|O_π(G)|` is a `π`-number.

The mathematical content is that the set `piCoreSet π G` of normal `π`-subgroups is closed
under joins: if `N` and `M` are normal with `|N|`, `|M|` `π`-numbers then so is `N ⊔ M`, because
`|N ⊔ M|` divides `|N| * |M|`.  Since `Subgroup G` is finite, `piCoreSet π G` has a maximal
element `N`, which therefore contains every member of the set, and `O_π(G) = N`.
-/

variable {G : Type*} [Group G]

/-- Cardinal identity for the join of two subgroups, the second being normal:
`|A ⊔ B| * |A ⊓ B| = |A| * |B|`. -/
private lemma card_sup_mul_card_inf (A B : Subgroup G) [B.Normal] :
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
theorem sup_mem_piCoreSet {π : ℕ → Prop} {N M : Subgroup G} [Finite G]
    (hN : N ∈ piCoreSet π G) (hM : M ∈ piCoreSet π G) : N ⊔ M ∈ piCoreSet π G := by
  haveI : N.Normal := hN.1
  haveI : M.Normal := hM.1
  refine ⟨inferInstance, ?_⟩
  have hdvd : Nat.card ↥(N ⊔ M) ∣ Nat.card ↥N * Nat.card ↥M :=
    ⟨Nat.card ↥(N ⊓ M), (card_sup_mul_card_inf N M).symm⟩
  exact isPiNat_of_dvd hdvd (IsPiNat.mul hN.2 hM.2)

/-- `O_π(G)`, the supremum of the normal `π`-subgroups, is a `π`-group. -/
theorem piCore_isPiNat (G : Type*) [Group G] [Finite G] (π : ℕ → Prop) :
    Work.Fitting.IsPiNat π (Nat.card ↥(Work.Fitting.piCore π G)) := by
  -- The set of normal `π`-subgroups is nonempty and closed under joins (whence directed),
  -- and it is finite, so it has a maximal element `N`.
  have hSne : (piCoreSet π G).Nonempty :=
    ⟨⊥, Subgroup.normal_bot, by simpa using (isPiNat_one π)⟩
  obtain ⟨N, hNmax⟩ := (Set.toFinite (piCoreSet π G)).exists_maximal hSne
  have hNnor : N.Normal := hNmax.1.1
  have hNpi : IsPiNat π (Nat.card ↥N) := hNmax.1.2
  haveI : N.Normal := hNnor
  -- `N` contains every normal `π`-subgroup, since `N ⊔ M` is again one.
  have hle : piCore π G ≤ N := by
    rw [piCore]
    refine sSup_le fun M hM => ?_
    exact le_sup_right.trans (hNmax.2 (sup_mem_piCoreSet hNmax.1 hM) le_sup_left)
  have hge : N ≤ piCore π G := le_piCore hNnor hNpi
  rw [le_antisymm hle hge]
  exact hNpi

end Work.Fitting
