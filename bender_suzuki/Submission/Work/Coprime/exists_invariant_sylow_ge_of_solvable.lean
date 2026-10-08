import Mathlib
import Submission.Work.Coprime.Defs
import Submission.Work.Coprime.Basic
import Submission.Work.Coprime.Normalizer
import Submission.Work.Coprime.exists_invariant_sylow
import Submission.Work.Coprime.lt_inf_normalizer_of_lt
import Submission.Work.Coprime.isInvariant_map_subtype

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

open scoped Pointwise

namespace Work.Coprime

/-- **Coprime action: an `A`-invariant `p`-subgroup lies in an `A`-invariant Sylow `p`-subgroup**
(assuming `A` or `G` solvable, as needed for the existence half of Glauberman's lemma).

Let `A` act by automorphisms on the finite group `G` with `|A|` coprime to `|G|`, and suppose that
`A` or `G` is solvable.  If `Q ≤ G` is an `A`-invariant `p`-subgroup, then there is an
`A`-invariant Sylow `p`-subgroup `P` of `G` with `Q ≤ P`.

Proof: take `R` maximal among the `A`-invariant `p`-subgroups of `G` containing `Q`, and let
`N = N_G(R)`.  Since `R ◁ N`, an `A`-invariant Sylow `S` of `N` contains `R`; the image of `S`
in `G` is an `A`-invariant `p`-subgroup containing `R`, so by maximality it equals `R`, whence
`S = R` and `R` is a *Sylow* subgroup of `N`.  If `R` were properly contained in a `p`-subgroup
`T` of `G`, the normalizer condition in `T` would give a `p`-subgroup `T ⊓ N_G(R)` of `N`
strictly containing `R`, a contradiction.  So `R` is a Sylow subgroup of `G`, and any Sylow
containing it is equal to it. -/
theorem exists_invariant_sylow_ge_of_solvable (A : Type*) {G : Type*} [Group A] [Group G] [Finite A]
    [Finite G] [MulDistribMulAction A G] (hcop : (Nat.card A).Coprime (Nat.card G))
    (hsol : Group.IsSolvable A ∨ Group.IsSolvable G) (p : ℕ) [Fact p.Prime]
    (Q : Subgroup G) [FT.IsInvariant A Q] (hQ : IsPGroup p Q) :
    ∃ P : Sylow p G, Q ≤ P ∧ ∀ a : A, a • P = P := by
  classical
  -- the maximal `A`-invariant `p`-subgroup containing `Q`
  let Sset : Set (Subgroup G) := {H | Q ≤ H ∧ IsPGroup p H ∧ FT.IsInvariant A H}
  have hne : Sset.Nonempty := ⟨Q, le_rfl, hQ, inferInstance⟩
  obtain ⟨R, hRmax⟩ := Set.Finite.exists_maximal (Set.toFinite Sset) hne
  obtain ⟨hQR, hRp, hRinv⟩ := hRmax.1
  have hmaxA : ∀ H : Subgroup G, Q ≤ H → FT.IsInvariant A H → IsPGroup p H → R ≤ H → H ≤ R :=
    fun H hQH hHinv hHp hRH => hRmax.2 ⟨hQH, hHp, hHinv⟩ hRH
  -- `R` is a Sylow `p`-subgroup of `G`
  have hRsyl : ∀ T : Subgroup G, IsPGroup p T → R ≤ T → T ≤ R := by
    intro T hTp hRT
    haveI : FT.IsInvariant A R := hRinv
    let N : Subgroup G := Subgroup.normalizer (R : Set G)
    have hRleN : R ≤ N := Subgroup.le_normalizer
    haveI hIN : FT.IsInvariant A N := inferInstance
    have hcopN : (Nat.card A).Coprime (Nat.card ↥N) :=
      hcop.coprime_dvd_right (Subgroup.card_subgroup_dvd_card N)
    have hsolN : Group.IsSolvable A ∨ Group.IsSolvable ↥N := by
      rcases hsol with h | h
      · exact Or.inl h
      · exact Or.inr (by
          haveI : Group.IsSolvable G := h
          exact Group.isSolvable_of_isSolvable_injective N.subtype_injective)
    obtain ⟨Sy, hSy⟩ := exists_invariant_sylow A hcopN hsolN p (G := ↥N)
    -- `R ◁ N` is a normal `p`-subgroup of `N`, so it lies in every Sylow of `N`
    have hKp : IsPGroup p (R.subgroupOf N) := hRp.comap_subtype (K := N)
    haveI hKN : (R.subgroupOf N).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hRleN).mpr le_rfl
    have hKle : R.subgroupOf N ≤ (Sy : Subgroup ↥N) := IsPGroup.le_sylow_of_normal hKp Sy
    haveI hISy : FT.IsInvariant A (Sy : Subgroup ↥N) := ⟨fun a => by
      rw [← Sylow.pointwise_smul_def]
      exact congrArg (fun T : Sylow p ↥N => (T : Subgroup ↥N)) (hSy a)⟩
    -- hence `Sy = R`: otherwise its image in `G` would be a bigger `A`-invariant `p`-subgroup
    have hUSyl : (Sy : Subgroup ↥N) = R.subgroupOf N := by
      have hUinv : FT.IsInvariant A ((Sy : Subgroup ↥N).map N.subtype) :=
        isInvariant_map_subtype N (Sy : Subgroup ↥N)
      have hUp : IsPGroup p ((Sy : Subgroup ↥N).map N.subtype) := Sy.isPGroup'.map N.subtype
      have hmapR : (R.subgroupOf N).map N.subtype = R := Subgroup.map_subgroupOf_eq_of_le hRleN
      have hRU : R ≤ (Sy : Subgroup ↥N).map N.subtype := by
        rw [← hmapR]; exact Subgroup.map_mono hKle
      have hUR : (Sy : Subgroup ↥N).map N.subtype ≤ R :=
        hmaxA _ (hQR.trans hRU) hUinv hUp hRU
      have h1 : (Sy : Subgroup ↥N) ≤ R.subgroupOf N := by
        intro x hx
        rw [Subgroup.mem_subgroupOf]
        exact hUR (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
      exact le_antisymm h1 hKle
    -- so no `p`-subgroup of `N` properly contains `R`
    have hNmax : ∀ U : Subgroup G, IsPGroup p U → R ≤ U → U ≤ N → U ≤ R := by
      intro U hUp hRU hUN
      have hUsub : IsPGroup p (U.subgroupOf N) := hUp.comap_subtype
      have hle : (Sy : Subgroup ↥N) ≤ U.subgroupOf N := by
        rw [hUSyl]; exact Subgroup.subgroupOf_mono N hRU
      have h2 : U.subgroupOf N = R.subgroupOf N := by
        rw [← hUSyl]; exact Sy.is_maximal' hUsub hle
      intro x hx
      have hxN : x ∈ N := hUN hx
      have hx2 : (⟨x, hxN⟩ : ↥N) ∈ U.subgroupOf N := by rwa [Subgroup.mem_subgroupOf]
      have hx3 : (⟨x, hxN⟩ : ↥N) ∈ R.subgroupOf N := h2 ▸ hx2
      rwa [Subgroup.mem_subgroupOf] at hx3
    -- a proper containment of `p`-subgroups would violate this
    by_contra hTR
    have hlt : R < T := lt_of_le_of_ne hRT (fun h => hTR h.ge)
    let W : Subgroup G := T ⊓ N
    have hW : R < W := lt_inf_normalizer_of_lt hTp hlt
    have hWp : IsPGroup p W := hTp.to_le inf_le_left
    have hRW : R ≤ W := le_inf hRT Subgroup.le_normalizer
    exact (ne_of_lt hW) (le_antisymm hRW (hNmax W hWp hRW inf_le_right))
  -- any Sylow containing `R` equals `R`
  obtain ⟨P, hRP⟩ := hRp.exists_le_sylow
  have hPR : (P : Subgroup G) ≤ R := hRsyl P P.isPGroup' hRP
  have hcoe : (P : Subgroup G) = R := le_antisymm hPR hRP
  refine ⟨P, ?_, ?_⟩
  · rw [hcoe]; exact hQR
  · intro a
    apply Sylow.ext
    rw [Sylow.pointwise_smul_def, hcoe]
    exact hRinv.smul_eq_self a

end Work.Coprime

