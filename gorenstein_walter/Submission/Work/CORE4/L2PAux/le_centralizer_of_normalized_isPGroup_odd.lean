import Mathlib
import Submission.Work.L2F.BridgeAddOn
import Submission.Work.CORE4.L2PAux.le_centralizer_of_odd_le_normalizer_of_card_two_mul
import Submission.Work.CORE4.L2PAux.exists_subgroup_card_prime_normalizer_of_isCyclic_isPGroup

namespace Work.CORE4.L2PAux

local notation "PSL2(" ρ "," k ")" => Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField ρ k)

/-- **Gorenstein–Walter, structure input for `L₂(q)`.**

Let `q = ρ ^ k` with `ρ` an odd prime and `q ≥ 5`, let `ℓ` be an odd prime distinct from `ρ`, let
`P ≤ L₂(q)` be an `ℓ`-subgroup and `T ≤ L₂(q)` a subgroup of odd order normalising `P`.  Then `P`
centralises `T`.

Proof.  Since `ℓ ≠ 2, ρ`, every `ℓ`-subgroup of `L₂(q)` is cyclic
(`Work.L2F.Props.isCyclic_subgroup_psl`, from the torus structure of `L₂(q)`), so `P` is cyclic —
say of order `ℓ ^ m`, `m ≥ 1`.  The (unique) subgroup `Y ≤ P` of order `ℓ` is characteristic in
`P`, hence normalised by `T ≤ N(P)`, and is centralised by `P` (cyclic groups are abelian)
(`exists_subgroup_card_prime_normalizer_of_isCyclic_isPGroup`).  For a subgroup of order the odd
prime `ℓ ≠ ρ`, the centralizer `C(Y)` is cyclic and the normalizer `N(Y)` is dihedral of order
`2 |C(Y)|` (`Work.L2F.Props.L2TorusNormalizer`).  An odd-order subgroup of a group `N` in which
`C` has index two lies in `C` (`le_centralizer_of_odd_le_normalizer_of_card_two_mul`), so
`T ≤ C(Y)`; as `C(Y)` is abelian we get `[P, T] = 1`, i.e. `P ≤ C(T)`. -/
theorem le_centralizer_of_normalized_isPGroup_odd {ρ k ℓ : ℕ} [Fact ρ.Prime] (hρ : Odd ρ)
    (hk : 5 ≤ ρ ^ k) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓρ : ℓ ≠ ρ)
    (P T : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField ρ k)))
    (hP : IsPGroup ℓ P) (hT : Odd (Nat.card T))
    (hTN : T ≤ Subgroup.normalizer (P : Set _)) :
    P ≤ Subgroup.centralizer (T : Set _) := by
  classical
  haveI hFactℓ : Fact ℓ.Prime := ⟨hℓ⟩
  haveI hFintype : Fintype (GaloisField ρ k) := Fintype.ofFinite _
  -- `2 ≠ 0` and `ℓ ≠ 0` in `GF(ρ, k)`, from `ρ` odd and `ℓ ≠ ρ`.
  have h2 : (2 : GaloisField ρ k) ≠ 0 := by
    intro h
    have hdiv : ρ ∣ 2 := (CharP.cast_eq_zero_iff (GaloisField ρ k) ρ 2).mp h
    have hle : ρ ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    have hge : 2 ≤ ρ := (Fact.out : ρ.Prime).two_le
    have hρ2 : ρ = 2 := le_antisymm hle hge
    rw [hρ2] at hρ
    exact (by decide : ¬ Odd 2) hρ
  have hℓ0 : (ℓ : GaloisField ρ k) ≠ 0 := by
    intro h
    have hdiv : ρ ∣ ℓ := (CharP.cast_eq_zero_iff (GaloisField ρ k) ρ ℓ).mp h
    exact hℓρ ((Nat.prime_dvd_prime_iff_eq (Fact.out : ρ.Prime) hℓ).mp hdiv).symm
  by_cases hPbot : P = ⊥
  · rw [hPbot]; exact bot_le
  · -- `P` is cyclic, of order `ℓ ^ m` with `m ≥ 1`.
    have hcyc : IsCyclic P :=
      Work.L2F.Props.isCyclic_subgroup_psl (GaloisField ρ k) h2 ℓ hℓ0 hℓ2 P hP
    obtain ⟨m, hmcard⟩ := IsPGroup.iff_card.mp hP
    have hm : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · exfalso
        rw [h0, pow_zero] at hmcard
        exact hPbot (Subgroup.card_eq_one.mp hmcard)
      · exact h0
    -- the order-`ℓ` subgroup `Y ≤ P`, normalised by `T` and centralised by `P`
    obtain ⟨Y, _hYP, hYcard, hTYN, hPYC⟩ :=
      exists_subgroup_card_prime_normalizer_of_isCyclic_isPGroup hℓ P T hcyc hmcard hm hTN
    -- the torus structure attached to `Y`: `C(Y)` cyclic, `N(Y)` dihedral of order `2 |C(Y)|`
    have hL2 := Work.L2F.Props.L2TorusNormalizer ρ k hρ hk ℓ hℓ hℓ2 hℓρ Y hYcard
    obtain ⟨hcycC, _hcardC, hdih⟩ := hL2
    have hcardN : Nat.card (Subgroup.normalizer (Y : Set (PSL2(ρ, k)))) =
        2 * Nat.card (Subgroup.centralizer (Y : Set (PSL2(ρ, k)))) := by
      obtain ⟨e⟩ := hdih
      rw [Nat.card_congr (MulEquiv.toEquiv e), DihedralGroup.nat_card]
    -- an odd-order subgroup of `N(Y)` lies in `C(Y)`
    have hTC := le_centralizer_of_odd_le_normalizer_of_card_two_mul hTYN hT hcardN
    -- `C(Y)` is abelian, and both `P` and `T` lie in it
    haveI : IsCyclic ↥(Subgroup.centralizer (Y : Set (PSL2(ρ, k)))) := hcycC
    letI : CommGroup ↥(Subgroup.centralizer (Y : Set (PSL2(ρ, k)))) := IsCyclic.commGroup
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val
      (mul_comm (⟨t, hTC ht⟩ : ↥(Subgroup.centralizer (Y : Set (PSL2(ρ, k)))))
        (⟨p, hPYC hp⟩ : ↥(Subgroup.centralizer (Y : Set (PSL2(ρ, k))))))

end Work.CORE4.L2PAux
