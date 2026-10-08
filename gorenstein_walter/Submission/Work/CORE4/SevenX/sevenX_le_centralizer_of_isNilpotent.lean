import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE2B.L29_tower_normcond

namespace Work.CORE4.SevenX

open Subgroup

/-- Cardinal divisibility `|H| ∣ |K|` when `H ≤ K`; obtained from
`Subgroup.card_subgroup_dvd_card` applied to `H.subgroupOf K`, whose cardinality is `|H|`. -/
private theorem card_dvd_card_of_le' {G : Type*} [Group G] {H K : Subgroup G} (h : H ≤ K) :
    Nat.card ↥H ∣ Nat.card ↥K := by
  have hcard : Nat.card ↥(H.subgroupOf K) = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv
  have hdiv := Subgroup.card_subgroup_dvd_card (H.subgroupOf K)
  rwa [hcard] at hdiv

/-- Bender 1.1(iv) for a nilpotent `K`, in the form needed for §4 (7): if a `p`-group `P` with
`p ∤ |K|` normalizes the nilpotent subgroup `K` and centralizes a subgroup `K₀ ≤ K` whose
centralizer in `K` is contained in `K₀`, then `P` centralizes `K`.  (`Coprime11ivProp` — Bender
1.1(iv) — is the special case `K₀ ⊴ K`; the nilpotent case needs no normality because in a
nilpotent group the normalizer chain from `K₀` climbs to `K`, by induction on `|K| - |K₀|`.)

Suggestion: the same statement is proved in `Submission/Work/CORE2B/c11iv_nilpotent.lean` as
`Work.CORE2B.c11iv_nilpotent` (taking `T : Work.GW2.LocalToolkit` and `[Fact p.Prime]`); the proof
there uses `Work.CORE2B.L29_tower_normcond` for the normalizer step and can be adapted (pass
`hp` as `haveI : Fact p.Prime := ⟨hp⟩`, use `hc11iv` in place of `T.c11iv`).  Do NOT assume a
`LocalToolkit` here. -/
theorem sevenX_le_centralizer_of_isNilpotent (hc11iv : Work.GW2.Coprime11ivProp)
    {G : Type} [Group G] [Finite G] (K K0 P : Subgroup G)
    (hKnil : Group.IsNilpotent ↥K) (hK0 : K0 ≤ K)
    (hsc : K ⊓ Subgroup.centralizer (K0 : Set G) ≤ K0)
    {p : ℕ} (hp : p.Prime) (hP : IsPGroup p P)
    (hcop : Nat.Coprime p (Nat.card ↥K))
    (hPN : P ≤ Subgroup.normalizer (K : Set G))
    (hPC : P ≤ Subgroup.centralizer (K0 : Set G)) :
    P ≤ Subgroup.centralizer (K : Set G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  -- Prove the statement for the fixed data `P, p, hP, hcop, hPN` by strong induction on
  -- `Nat.card K - Nat.card K0`; in the recursion `K` is replaced by a strictly larger subgroup
  -- `L ≤ K` (so the second argument stays inside the same finite group `K`).
  suffices aux : ∀ (n : ℕ) (K K0 : Subgroup G), Nat.card K - Nat.card K0 = n →
      K0 ≤ K → Group.IsNilpotent ↥K → P ≤ Subgroup.centralizer (K0 : Set G) →
      K ⊓ Subgroup.centralizer (K0 : Set G) ≤ K0 →
      Nat.Coprime p (Nat.card K) → P ≤ Subgroup.normalizer (K : Set G) →
      P ≤ Subgroup.centralizer (K : Set G) from
    aux (Nat.card K - Nat.card K0) K K0 rfl hK0 hKnil hPC hsc hcop hPN
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
        Work.CORE2B.L29_tower_normcond K K0 hKnil hK0 hKK
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
        Nat.Coprime.coprime_dvd_right (card_dvd_card_of_le' hLK) hcop
      -- `K0` is normal in `L`
      have hnorm : (K0.subgroupOf L).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hK0L).mpr inf_le_right
      -- `L ⊓ C(K0) ≤ K0`
      have hinf : L ⊓ Subgroup.centralizer (K0 : Set G) ≤ K0 := by
        intro x hx
        exact hself ⟨hLK hx.1, hx.2⟩
      -- Bender 1.1(iv) for the pair `(L, K0)`
      have hPL' : P ≤ Subgroup.centralizer (L : Set G) :=
        hc11iv G p P L K0 hP hLcop hPL hK0L hnorm hPK0 hinf
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

end Work.CORE4.SevenX
