import Mathlib
import Submission.Work.COPR.Coprime11i

namespace Work.COPR

/-- Bender 1981, 1.1(iv): if a `p`-group `P` acts coprimely on a `p'`-group `K`
(`P ≤ N_G(K)`), centralizes a normal subgroup `K0 ≤ K`, and `C_K(K0) ≤ K0`, then `P` centralizes
`K`.  Deliverable `Work.GW2.Coprime11ivProp` of area COPR.

Proof route.  (i) The three-subgroups identity applied to `(P, K0, K)` gives
`[[K,P],K0] = 1` from `[P,K0] = 1` (hypothesis `hC`) and `[K0,K] ≤ K0 ≤ C_K(P)`
(`Subgroup.commutator_commutator_eq_bot_of_rotate`, or `Subgroup.commutator_le` twice); hence
`[K,P] ≤ C_K(K0)` and, by `hself`, `[K,P] ≤ K0`.  (ii) `P` centralizes `K0 ⊇ [K,P]`, so
`[P,[K,P]] = 1`; combined with `[K,P] = [[K,P],P]` (`Work.COPR.commutator_iterated_eq` from
`Submission.Work.COPR.Coprime11i`) this gives `[K,P] = 1`, i.e. `P ≤ C_G(K)`.
`Work.COPR.commutator_sup_fixed_eq_top` may also be used to that end. -/
theorem coprime11iv (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (P K K0 : Subgroup G) (hP : IsPGroup p P) (hcop : Nat.Coprime p (Nat.card K))
    (hN : P ≤ Subgroup.normalizer (K : Set G)) (hK0 : K0 ≤ K)
    (hnorm : (K0.subgroupOf K).Normal) (hC : P ≤ Subgroup.centralizer (K0 : Set G))
    (hself : K ⊓ Subgroup.centralizer (K0 : Set G) ≤ K0) :
    P ≤ Subgroup.centralizer (K : Set G) := by
  -- `[P,K0] = 1`, equivalently `K0 ≤ C_G(P)`.
  have hPK0 : ⁅P, K0⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hC
  have hK0C : K0 ≤ Subgroup.centralizer (P : Set G) := Subgroup.le_centralizer_iff.mp hC
  -- `[K,P] ≤ K`, since `P ≤ N_G(K)`.
  have hKP_le_K : ⁅K, P⁆ ≤ K := Subgroup.le_normalizer_iff_commutator_le_left.mp hN
  -- `K0 ◁ K`, so `[K0,K] ≤ K0`.
  have hK_le_normK0 : K ≤ Subgroup.normalizer (K0 : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK0).mp hnorm
  have hK0K_le : ⁅K0, K⁆ ≤ K0 :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hK_le_normK0
  -- Step (i): the three-subgroups lemma gives `[[K,P],K0] = 1`, hence `[K,P] ≤ K0`.
  have hKP_le_K0 : ⁅K, P⁆ ≤ K0 := by
    have h1 : ⁅⁅P, K0⁆, K⁆ = ⊥ := by rw [hPK0, Subgroup.commutator_bot_left]
    have h2 : ⁅⁅K0, K⁆, P⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hK0K_le.trans hK0C)
    have h3 : ⁅⁅K, P⁆, K0⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    exact (le_inf hKP_le_K (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3)).trans hself
  -- Step (ii): `[[K,P],P] = 1` since `[K,P] ≤ K0 ≤ C_G(P)`, and `[[K,P],P] = [K,P]`.
  have hiter : ⁅⁅K, P⁆, P⁆ = ⁅K, P⁆ := commutator_iterated_eq p P K hP hcop hN
  have hzero : ⁅⁅K, P⁆, P⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hKP_le_K0.trans hK0C)
  have hKP_bot : ⁅K, P⁆ = ⊥ := by rw [← hiter, hzero]
  rw [Subgroup.le_centralizer_iff, ← Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact hKP_bot

end Work.COPR
