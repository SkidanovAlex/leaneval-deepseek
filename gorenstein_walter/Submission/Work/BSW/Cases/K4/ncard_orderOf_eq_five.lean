import Mathlib

set_option linter.style.haveILetI false

namespace Work.BSW.Cases.K4

/-- For a finite group `G` of order `360` (so that every Sylow `5`-subgroup of `G` has order exactly
`5`), the number of elements of order `5` is `4 · n₅`.

Each Sylow `5`-subgroup `P` has order `5` by Lagrange (`360 = 2³·3²·5` and
`Sylow.card_eq_multiplicity`), so `P` consists of the identity together with four elements of order
`5`; two distinct Sylow `5`-subgroups of order `5` intersect trivially, and every element of order
`5` lies in some Sylow `5`-subgroup.  Hence the sets of nonidentity elements of the Sylow
`5`-subgroups partition the set of elements of order `5`, and a disjoint-union count
(`Set.ncard_iUnion_of_finite`, `Set.ncard_sdiff_singleton_of_mem`) gives the claim. -/
theorem ncard_orderOf_eq_five {G : Type} [Group G] [Finite G] (hG : Nat.card G = 360) :
    {x : G | orderOf x = 5}.ncard = 4 * Nat.card (Sylow 5 G) := by
  haveI : Fact (Nat.Prime 5) := Fact.mk (by norm_num)
  -- Every Sylow `5`-subgroup has order `5`.
  have hcard : ∀ P : Sylow 5 G, Nat.card P = 5 := by
    intro P
    have hfac : Nat.factorization 360 5 = 1 := by
      rw [Nat.factorization_def 360 (by norm_num),
        show (360 : ℕ) = 72 * 5 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
        padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 5 ∣ 72), padicValNat_self]
    rw [Sylow.card_eq_multiplicity P, hG, hfac, pow_one]
  -- A nonidentity element of a Sylow `5`-subgroup has order `5`.
  have hord : ∀ {x : G} {P : Sylow 5 G}, x ∈ (P : Set G) → x ≠ 1 → orderOf x = 5 := by
    intro x P hxP hx1
    have hle : Subgroup.zpowers x ≤ (P : Subgroup G) := Subgroup.zpowers_le.mpr hxP
    have hdvd : orderOf x ∣ 5 := by
      have h := Subgroup.card_dvd_of_le hle
      rwa [Nat.card_zpowers, hcard P] at h
    rcases (by norm_num : Nat.Prime 5).eq_one_or_self_of_dvd (orderOf x) hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  -- The elements of order `5` are the nonidentity elements of the Sylow `5`-subgroups.
  have hmem : ∀ x : G, (∃ P : Sylow 5 G, x ∈ (P : Set G) \ {1}) ↔ orderOf x = 5 := by
    intro x
    constructor
    · rintro ⟨P, hxP, hx1⟩
      exact hord hxP (by simpa using hx1)
    · intro hx
      have hisP : IsPGroup 5 (Subgroup.zpowers x) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
      obtain ⟨Q, hQ⟩ := hisP.exists_le_sylow
      refine ⟨Q, hQ (Subgroup.mem_zpowers x), ?_⟩
      simp only [Set.mem_singleton_iff]
      intro h1
      rw [← orderOf_eq_one_iff] at h1
      omega
  have hunion : (⋃ P : Sylow 5 G, ((P : Set G) \ {1})) = {x : G | orderOf x = 5} := by
    ext x
    rw [Set.mem_iUnion]
    exact hmem x
  -- Nonidentity parts of distinct Sylow `5`-subgroups are disjoint.
  have hdisj : Pairwise (Function.onFun Disjoint (fun P : Sylow 5 G => ((P : Set G) \ {1}))) := by
    intro P Q hPQ
    change Disjoint ((P : Set G) \ {1}) ((Q : Set G) \ {1})
    rw [Set.disjoint_left]
    intro x hxP hxQ
    exfalso
    rw [Set.mem_sdiff, Set.mem_singleton_iff] at hxP hxQ
    obtain ⟨hxP', hxPn1⟩ := hxP
    obtain ⟨hxQ', _⟩ := hxQ
    have hle : Subgroup.zpowers x ≤ (P : Subgroup G) ⊓ (Q : Subgroup G) :=
      le_inf (Subgroup.zpowers_le.mpr hxP') (Subgroup.zpowers_le.mpr hxQ')
    have hdvd1 : Nat.card ↥((P : Subgroup G) ⊓ (Q : Subgroup G)) ∣ 5 := by
      have h := Subgroup.card_dvd_of_le (H := (P : Subgroup G) ⊓ (Q : Subgroup G))
        (K := (P : Subgroup G)) inf_le_left
      rwa [hcard P] at h
    have hdvd2 : 5 ∣ Nat.card ↥((P : Subgroup G) ⊓ (Q : Subgroup G)) := by
      have h := Subgroup.card_dvd_of_le hle
      rw [Nat.card_zpowers, hord hxP' hxPn1] at h
      exact h
    have heq5 : Nat.card ↥((P : Subgroup G) ⊓ (Q : Subgroup G)) = 5 :=
      Nat.dvd_antisymm hdvd1 hdvd2
    have hPeq : ((P : Subgroup G) ⊓ (Q : Subgroup G)) = (P : Subgroup G) :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [heq5, hcard P])
    have hQeq : ((P : Subgroup G) ⊓ (Q : Subgroup G)) = (Q : Subgroup G) :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [heq5, hcard Q])
    exact hPQ (Sylow.ext (by rw [← hPeq, hQeq]))
  have hfin : ∀ P : Sylow 5 G, ((P : Set G) \ {1}).Finite :=
    fun P => Set.finite_univ.subset (Set.subset_univ _)
  -- Each nonidentity part has `4` elements.
  have hFcard : ∀ P : Sylow 5 G, ((P : Set G) \ {1}).ncard = 4 := by
    intro P
    have hP : (P : Set G).ncard = 5 := by
      have h2 : (P : Set G).ncard = Nat.card (P : Subgroup G) := by
        rw [← Nat.card_coe_set_eq]; exact Nat.card_congr (Equiv.refl _)
      rw [h2]
      exact hcard P
    rw [Set.ncard_sdiff_singleton_of_mem (s := (P : Set G)) P.one_mem, hP]
  calc {x : G | orderOf x = 5}.ncard
      = (⋃ P : Sylow 5 G, ((P : Set G) \ {1})).ncard := by rw [hunion]
    _ = ∑ᶠ P : Sylow 5 G, ((P : Set G) \ {1}).ncard :=
          Set.ncard_iUnion_of_finite hfin hdisj
    _ = ∑ᶠ P : Sylow 5 G, (4 : ℕ) := by
          apply finsum_congr; intro P; exact hFcard P
    _ = 4 * Nat.card (Sylow 5 G) := by
          classical
          haveI := Fintype.ofFinite (Sylow 5 G)
          rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ,
            Nat.card_eq_fintype_card, smul_eq_mul, Nat.mul_comm]

end Work.BSW.Cases.K4
