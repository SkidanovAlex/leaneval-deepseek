import Mathlib
import Submission.Work.COPR.Glue

namespace Work.COPR

/-- Bender 1981, 1.1(ii), existence part: if the `p`-group `P` acts coprimely on the `p'`-group
`K` (`P ≤ N_G(K)`), then every `P`-invariant `q`-subgroup `Q ≤ K` is contained in a `P`-invariant
Sylow `q`-subgroup `R` of `K` (i.e. `q ∤ [K : R]`).  First half of
`Work.GW2.Coprime11iiProp` of area COPR.

Suggested route: apply Isaacs Corollary 3.25
`OddOrder.Isaacs.Ch04.aInvariant_pSubgroup_le_aInvariant_sylow`
(`Submission/OddOrder/Isaacs/Ch04_Commutators/ForwardFromCh03.lean`) with `G := ↥K`, `A := ↥P`
and `p := q`: it needs coprimality `Nat.Coprime (Nat.card ↥P) (Nat.card ↥K)`
(`Work.COPR.coprime_card_of_isPGroup`), solvability of `↥P` (`Work.COPR.isSolvable_of_isPGroup`),
and the `P`-invariance of `Q` (from `P ≤ N_G(Q)`); it returns a `P`-invariant Sylow `q`-subgroup of
`↥K` containing `Q`.  A `Sylow q ↥K` satisfies `¬ q ∣ R.relIndex K` once transported along
`K.subtype` (`Sylow.not_dvd_index'`, and `(S : Subgroup G).relIndex K = [K : S]` for `S ≤ K`). -/
theorem coprime11ii_exists (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (P K : Subgroup G) (hP : IsPGroup p P) (hcop : Nat.Coprime p (Nat.card K))
    (hN : P ≤ Subgroup.normalizer (K : Set G)) :
    ∀ (q : ℕ) [Fact q.Prime] (Q : Subgroup G), Q ≤ K → IsPGroup q Q →
      P ≤ Subgroup.normalizer (Q : Set G) →
      ∃ R : Subgroup G, Q ≤ R ∧ R ≤ K ∧ P ≤ Subgroup.normalizer (R : Set G) ∧
        IsPGroup q R ∧ ¬ q ∣ R.relIndex K := by
  intro q _ Q hQK hQq hQN
  classical
  -- Coprimality `|P| ⊥ |K|` and solvability of the acting `p`-group `P`.
  have hcard : Nat.Coprime (Nat.card ↥P) (Nat.card ↥K) := coprime_card_of_isPGroup p hP hcop
  have hsolv : Group.IsSolvable ↥P ∨ Group.IsSolvable ↥K :=
    Or.inl (isSolvable_of_isPGroup p hP)
  -- `Q.subgroupOf K` is a `q`-subgroup of `↥K` invariant under the conjugation action of `P`.
  have hQinv : OddOrder.Isaacs.Ch03.IsAInvariant (conjAct P K hN) (Q.subgroupOf K) := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro a x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [conjAct_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp (hQN a.2) (x : G)).mp hx
  have hQqK : IsPGroup q (Q.subgroupOf K) := hQq.comap_subtype
  -- Isaacs Cor 3.25 in the group `↥K`: an invariant Sylow `q`-subgroup `S ⊇ Q` of `↥K`.
  obtain ⟨S, hSinv, hQS⟩ :=
    OddOrder.Isaacs.Ch04.aInvariant_pSubgroup_le_aInvariant_sylow (φ := conjAct P K hN)
      hcard hsolv hQqK hQinv
  -- Transport `S` back to the ambient group: `R := S ↾ K`.
  set R : Subgroup G := (S : Subgroup ↥K).map K.subtype with hRdef
  have hQR : Q ≤ R := by
    intro x hx
    exact ⟨⟨x, hQK hx⟩, hQS (by rw [Subgroup.mem_subgroupOf]; exact hx), rfl⟩
  have hRK : R ≤ K := Subgroup.map_subtype_le _
  have hRN : P ≤ Subgroup.normalizer (R : Set G) := by
    intro g hg
    have := OddOrder.Isaacs.Ch03.IsAInvariant.mem_normalizer_map_subtype_of_smul_val
      (W := K) (L := (S : Subgroup ↥K)) hSinv (a := ⟨g, hg⟩) (g := g)
      (fun k => by rw [conjAct_apply_coe])
    simpa [hRdef] using this
  have hRq : IsPGroup q R := by rw [hRdef]; exact S.isPGroup'.map K.subtype
  -- `R.relIndex K` is the index of `S` in `↥K`, hence prime to `q`.
  have hsub : R.subgroupOf K = (S : Subgroup ↥K) := by
    rw [hRdef]
    ext x
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  have hrel : R.relIndex K = (S : Subgroup ↥K).index := congrArg Subgroup.index hsub
  refine ⟨R, hQR, hRK, hRN, hRq, ?_⟩
  rw [hrel]
  exact Sylow.not_dvd_index S

end Work.COPR
