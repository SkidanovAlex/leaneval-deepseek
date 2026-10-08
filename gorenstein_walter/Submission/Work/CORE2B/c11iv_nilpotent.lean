import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.L29_tower_normcond

namespace Work.CORE2B

/-- Cardinal divisibility `|H| ∣ |K|` when `H ≤ K`.  Obtained from
`Subgroup.card_subgroup_dvd_card` applied to `H.subgroupOf K`, whose cardinality is `|H|`
(`Subgroup.subgroupOfEquivOfLe`). -/
theorem card_dvd_card_of_le {G : Type*} [Group G] {H K : Subgroup G} (h : H ≤ K) :
    Nat.card H ∣ Nat.card K := by
  have hcard : Nat.card ↥(H.subgroupOf K) = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv
  have hdiv := Subgroup.card_subgroup_dvd_card (H.subgroupOf K)
  rwa [hcard] at hdiv

-- Leaf N1 of the lead's design pass 12 (`_design_gw/Core12L27.lean`), pure group theory:
-- Bender 1.1(iv) with a self-centralizing `K₀` inside a nilpotent `K`.
-- Route: induction on `|K| - |K₀|`; if `K₀ < K`, put `L := K ⊓ N_G(K₀)`; `K₀ < L` (normalizer
-- condition for the nilpotent `K`), `P` normalizes `L`, `K₀ ⊴ L`, `L ⊓ C(K₀) ≤ K₀`, so `T.c11iv`
-- gives `P ≤ C(L)`; and `K ⊓ C(L) ≤ K ⊓ C(K₀) ≤ K₀ ≤ L`, so recurse with `K₀ := L`.
-- (`Group.normalizerCondition_of_isNilpotent` is available in Mathlib, cf. the area's
-- `L29_tower_normcond.lean`.)
theorem c11iv_nilpotent (T : Work.GW2.LocalToolkit) {G : Type} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (P K K0 : Subgroup G) (hP : IsPGroup p P)
    (hcop : Nat.Coprime p (Nat.card K)) (hPK : P ≤ Subgroup.normalizer (K : Set G))
    (hKnil : Group.IsNilpotent ↥K) (hK0 : K0 ≤ K)
    (hPK0 : P ≤ Subgroup.centralizer (K0 : Set G))
    (hself : K ⊓ Subgroup.centralizer (K0 : Set G) ≤ K0) :
    P ≤ Subgroup.centralizer (K : Set G) := by
  -- Prove the statement for the fixed data `P, p, hP, hcop, hPK` by strong induction on
  -- `Nat.card K - Nat.card K0`; in the recursion `K` is replaced by a strictly larger subgroup
  -- `L ≤ K` (so the second argument stays inside the same finite group `K`).
  suffices aux : ∀ (n : ℕ) (K K0 : Subgroup G), Nat.card K - Nat.card K0 = n →
      K0 ≤ K → Group.IsNilpotent ↥K → P ≤ Subgroup.centralizer (K0 : Set G) →
      K ⊓ Subgroup.centralizer (K0 : Set G) ≤ K0 →
      Nat.Coprime p (Nat.card K) → P ≤ Subgroup.normalizer (K : Set G) →
      P ≤ Subgroup.centralizer (K : Set G) from
    aux (Nat.card K - Nat.card K0) K K0 rfl hK0 hKnil hPK0 hself hcop hPK
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro K K0 hcard hK0 hKnil hPK0 hself hcop hPK
    by_cases hKK : K0 = K
    · subst hKK
      exact hPK0
    · -- `K0` is a proper subgroup of the nilpotent group `K`
      have hlt : K0 < K := lt_of_le_of_ne hK0 hKK
      -- the normalizer condition: `K0 < N_K(K0) = K ⊓ N_G(K0)`
      have hnn : K0 < K ⊓ Subgroup.normalizer (K0 : Set G) :=
        L29_tower_normcond K K0 hKnil hK0 hKK
      set L : Subgroup G := K ⊓ Subgroup.normalizer (K0 : Set G) with hLdef
      have hK0L : K0 ≤ L := hnn.le
      have hLK : L ≤ K := inf_le_left
      -- `P` normalizes `L = K ⊓ N_G(K0)`
      have hPL : P ≤ Subgroup.normalizer (L : Set G) := by
        intro x hx
        have hxK : x ∈ Subgroup.normalizer (K : Set G) := hPK hx
        have hxK0 : x ∈ Subgroup.normalizer (K0 : Set G) :=
          Subgroup.centralizer_le_normalizer (K0 : Set G) (hPK0 hx)
        have hxNN : x ∈ Subgroup.normalizer (Subgroup.normalizer (K0 : Set G) : Set G) :=
          (Subgroup.le_normalizer (H := Subgroup.normalizer (K0 : Set G))) hxK0
        exact (Subgroup.inf_normalizer_le_normalizer_inf (H := K)
          (K := Subgroup.normalizer (K0 : Set G))) ⟨hxK, hxNN⟩
      -- `p` is still coprime to the order of `L`
      have hLcop : Nat.Coprime p (Nat.card L) :=
        Nat.Coprime.coprime_dvd_right (card_dvd_card_of_le hLK) hcop
      -- `K0` is normal in `L`
      have hnorm : (K0.subgroupOf L).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hK0L).mpr inf_le_right
      -- `L ⊓ C(K0) ≤ K0`
      have hinf : L ⊓ Subgroup.centralizer (K0 : Set G) ≤ K0 := by
        intro x hx
        exact hself ⟨hLK hx.1, hx.2⟩
      -- Bender 1.1(iv) for the pair `(L, K0)`
      have hPL' : P ≤ Subgroup.centralizer (L : Set G) :=
        T.c11iv G p P L K0 hP hLcop hPL hK0L hnorm hPK0 hinf
      -- `K ⊓ C(L) ≤ K ⊓ C(K0) ≤ K0 ≤ L`, so the induction hypothesis applies with `K0 := L`
      have hCL : Subgroup.centralizer (L : Set G) ≤ Subgroup.centralizer (K0 : Set G) :=
        Subgroup.centralizer_le (fun x hx => hK0L hx)
      have hKL : K ⊓ Subgroup.centralizer (L : Set G) ≤ L := by
        intro x hx
        exact hK0L (hself ⟨hx.1, hCL hx.2⟩)
      -- the measure strictly decreases
      have hdecr : Nat.card K - Nat.card L < n := by
        rw [← hcard]
        exact Nat.sub_lt_sub_left (Subgroup.card_lt_of_lt hlt) (Subgroup.card_lt_of_lt hnn)
      exact ih (Nat.card K - Nat.card L) hdecr K L rfl hLK hKnil hPL' hKL hcop hPK

end Work.CORE2B
