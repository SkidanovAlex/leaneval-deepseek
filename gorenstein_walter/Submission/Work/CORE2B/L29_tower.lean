import Mathlib
import Submission.Work.CORE2B.Defs

/-!
# `Work.CORE2B.L29_tower`

The tower step of Bender's Lemma 2.9 (Bender 1981, p. 222; see `NOTES_L29_contra.md` §10).

**Statement.**  If `A ≤ G` is nilpotent of odd order, `t ∈ G` is an involution normalizing `A`
and `X ≤ A` satisfies `N_G(X) ⊓ A ≤ C_G(t)`, then `t` centralizes all of `A`.

**Proof.**  Write `N_A(Y) = A ⊓ N_G(Y)`.  The argument iterates Bender 1.1(iv) (the hypothesis
`Coprime11ivProp`) along the *normalizer tower*

`K₁ = N_A(X) < K₂ = N_A(K₁) < K₃ = N_A(K₂) < ⋯ ≤ A`

which reaches `A` by the normalizer condition for the nilpotent group `↥A` (Mathlib's
`Group.normalizerCondition_of_isNilpotent`).

Two facts make each step work:

* `t` centralizes `K₁` by hypothesis, and `K₁` is *self-centralizing in `A`*: an element of `A`
  centralizing `N_A(X)` centralizes `X`, hence lies in `N_A(X)`.
* If `t` centralizes `K` then `t ∈ N_G(N_A(K))` (conjugation by `t` is an automorphism of `G`
  fixing `K` pointwise, so it normalizes `N_G(K)`), and `K ⊴ N_A(K)`; moreover
  `C_A(N_A(K)) ≤ C_A(K) ≤ K ≤ N_A(K)`.  So 1.1(iv) (with `p = 2`, `P = ⟨t⟩`, `K₀ = K`,
  `K = N_A(K)`) gives that `t` centralizes `N_A(K)`.

Iterating until `K = A` gives `t ∈ C_G(A)`, i.e. `A ≤ C_G(t)`.
-/

namespace Work.CORE2B

open Subgroup

/-- Normalizer condition, in the form used by the tower: a proper subgroup `K ≤ A` of the
nilpotent group `↥A` is properly contained in `A ⊓ N_G(K)`. -/
private theorem lt_inf_normalizer_of_ne {G : Type*} [Group G] (A K : Subgroup G)
    (hnil : Group.IsNilpotent ↥A) (hK : K ≤ A) (hne : K ≠ A) :
    K < A ⊓ Subgroup.normalizer (K : Set G) := by
  have hne_top : K.subgroupOf A ≠ ⊤ := by
    intro h
    exact hne (le_antisymm hK (Subgroup.subgroupOf_eq_top.mp h))
  have hlt : K.subgroupOf A < Subgroup.normalizer (K.subgroupOf A) :=
    @Group.normalizerCondition_of_isNilpotent ↥A _ hnil (K.subgroupOf A)
      (by rw [lt_top_iff_ne_top]; exact hne_top)
  rw [← Subgroup.subgroupOf_normalizer_eq hK] at hlt
  obtain ⟨x, hxN, hxK⟩ := IsConcreteLE.exists_of_lt hlt
  have hxN' : (x : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.mem_subgroupOf.mp hxN
  have hxK' : (x : G) ∉ K := fun h => hxK (Subgroup.mem_subgroupOf.mpr h)
  refine lt_of_le_of_ne (le_inf hK Subgroup.le_normalizer) fun heq => ?_
  apply hxK'
  rw [heq]
  exact ⟨x.2, hxN'⟩

/-- An element normalizing both `A` and `K` normalizes `A ⊓ N_G(K)`.  (The normalizer of `K` is
closed under conjugation by its own elements, so this is only subgroup closure.) -/
private theorem mem_normalizer_inf_normalizer {G : Type*} [Group G] (A K : Subgroup G) (t : G)
    (htA : t ∈ Subgroup.normalizer (A : Set G))
    (htK : t ∈ Subgroup.normalizer (K : Set G)) :
    t ∈ Subgroup.normalizer ((A ⊓ Subgroup.normalizer (K : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at htA htK ⊢
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(htA x).mp h1, (Subgroup.normalizer (K : Set G)).mul_mem
      ((Subgroup.normalizer (K : Set G)).mul_mem htK h2)
      ((Subgroup.normalizer (K : Set G)).inv_mem htK)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨(htA x).mpr h1, ?_⟩
    have h3 : t⁻¹ * (t * x * t⁻¹) * t ∈ Subgroup.normalizer (K : Set G) :=
      (Subgroup.normalizer (K : Set G)).mul_mem
        ((Subgroup.normalizer (K : Set G)).mul_mem
          ((Subgroup.normalizer (K : Set G)).inv_mem htK) h2)
        htK
    rwa [show t⁻¹ * (t * x * t⁻¹) * t = x from by group] at h3

theorem L29_tower (h11iv : Work.GW2.Coprime11ivProp) {G : Type} [Group G] [Finite G]
    (A : Subgroup G) (hnil : Group.IsNilpotent ↥A) (hodd : Odd (Nat.card A))
    (t : G) (ht : orderOf t = 2) (htA : t ∈ Subgroup.normalizer (A : Set G))
    (X : Subgroup G) (hX : X ≤ A)
    (hcent : Subgroup.normalizer (X : Set G) ⊓ A ≤ Subgroup.centralizer ({t} : Set G)) :
    A ≤ Subgroup.centralizer ({t} : Set G) := by
  classical
  -- `⟨t⟩` is a `2`-group
  have hisP : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht]; norm_num)
  -- subgroups of `A` have odd order, hence are coprime to `2`
  have hcop : ∀ K : Subgroup G, K ≤ A → Nat.Coprime 2 (Nat.card K) := by
    intro K hK
    have hdvd : Nat.card K ∣ Nat.card A := by
      have h := Subgroup.card_subgroup_dvd_card (K.subgroupOf A)
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv] at h
    exact Nat.coprime_two_left.mpr (Odd.of_dvd_nat hodd hdvd)
  -- the base of the tower: `K₁ = N_A(X)`
  set K₁ : Subgroup G := A ⊓ Subgroup.normalizer (X : Set G) with hK₁def
  have hcent₁ : t ∈ Subgroup.centralizer (K₁ : Set G) := by
    have hle : K₁ ≤ Subgroup.normalizer (X : Set G) ⊓ A := by
      rw [hK₁def]
      exact le_inf inf_le_right inf_le_left
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h1 := hcent (hle hk)
    rwa [Subgroup.mem_centralizer_singleton_iff] at h1
  have hself₁ : A ⊓ Subgroup.centralizer (K₁ : Set G) ≤ K₁ := by
    intro h hh
    have hhA : h ∈ A := (Subgroup.mem_inf.mp hh).1
    have hhC : h ∈ Subgroup.centralizer (K₁ : Set G) := (Subgroup.mem_inf.mp hh).2
    have hsub : (X : Set G) ⊆ (K₁ : Set G) := by
      intro x hx
      have hxK : x ∈ A ⊓ Subgroup.normalizer (X : Set G) :=
        ⟨hX hx, (Subgroup.le_normalizer (H := X)) hx⟩
      rwa [hK₁def]
    have hNX : h ∈ Subgroup.normalizer (X : Set G) :=
      Subgroup.centralizer_le_normalizer (s := (X : Set G))
        (Subgroup.centralizer_le (s := (X : Set G)) (t := (K₁ : Set G)) hsub hhC)
    have hK₁ : h ∈ A ⊓ Subgroup.normalizer (X : Set G) := ⟨hhA, hNX⟩
    rwa [hK₁def]
  -- the induction along the normalizer tower
  have key : ∀ (n : ℕ) (K : Subgroup G), Nat.card A - Nat.card K ≤ n → K ≤ A →
      t ∈ Subgroup.centralizer (K : Set G) →
      A ⊓ Subgroup.centralizer (K : Set G) ≤ K →
      t ∈ Subgroup.centralizer (A : Set G) := by
    intro n
    induction n with
    | zero =>
      intro K hle hKA htK _
      have hcard : Nat.card K = Nat.card A :=
        le_antisymm (Subgroup.card_le_of_le hKA)
          (Nat.sub_eq_zero_iff_le.mp (Nat.le_zero.mp hle))
      have hEq : K = A := Subgroup.eq_of_le_of_card_ge hKA hcard.symm.le
      rwa [hEq] at htK
    | succ n ih =>
      intro K hle hKA htK hself
      by_cases hsub : Nat.card A - Nat.card K = 0
      · have hcard : Nat.card K = Nat.card A :=
          le_antisymm (Subgroup.card_le_of_le hKA) (Nat.sub_eq_zero_iff_le.mp hsub)
        have hEq : K = A := Subgroup.eq_of_le_of_card_ge hKA hcard.symm.le
        rwa [hEq] at htK
      · have hKne : K ≠ A := by
          intro hEq
          rw [hEq, Nat.sub_self] at hsub
          exact hsub rfl
        -- one step of the tower: `K' = N_A(K)`
        set K' : Subgroup G := A ⊓ Subgroup.normalizer (K : Set G) with hK'def
        have hlt : K < K' := by
          rw [hK'def]
          exact lt_inf_normalizer_of_ne A K hnil hKA hKne
        have hK'le : K' ≤ A := by rw [hK'def]; exact inf_le_left
        have hK'K : K ≤ K' := le_of_lt hlt
        -- `t` normalizes `K` and hence `K'`
        have htNK : t ∈ Subgroup.normalizer (K : Set G) :=
          Subgroup.centralizer_le_normalizer (s := (K : Set G)) htK
        have htNK' : t ∈ Subgroup.normalizer (K' : Set G) := by
          rw [hK'def]
          exact mem_normalizer_inf_normalizer A K t htA htNK
        have hnorm : (K.subgroupOf K').Normal :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hK'K).mpr
            (by rw [hK'def]; exact inf_le_right)
        have hself' : K' ⊓ Subgroup.centralizer (K : Set G) ≤ K :=
          le_trans (inf_le_inf hK'le le_rfl) hself
        -- Bender 1.1(iv): `t` centralizes `K'`
        have hres := h11iv G 2 (Subgroup.zpowers t) K' K hisP (hcop K' hK'le)
          (by rwa [Subgroup.zpowers_le]) hK'K hnorm (by rwa [Subgroup.zpowers_le]) hself'
        have htK' : t ∈ Subgroup.centralizer (K' : Set G) := by
          rwa [Subgroup.zpowers_le] at hres
        have hself'' : A ⊓ Subgroup.centralizer (K' : Set G) ≤ K' := by
          intro h hh
          have hhA : h ∈ A := (Subgroup.mem_inf.mp hh).1
          have hhC : h ∈ Subgroup.centralizer (K' : Set G) := (Subgroup.mem_inf.mp hh).2
          have hNK : h ∈ Subgroup.normalizer (K : Set G) :=
            Subgroup.centralizer_le_normalizer (s := (K : Set G))
              (Subgroup.centralizer_le (s := (K : Set G)) (t := (K' : Set G)) hK'K hhC)
          have hK' : h ∈ A ⊓ Subgroup.normalizer (K : Set G) := ⟨hhA, hNK⟩
          rwa [hK'def]
        -- the tower has strictly grown, so the induction measure has strictly decreased
        have hdist : Nat.card A - Nat.card K' ≤ n := by
          have h1 : Nat.card K' ≤ Nat.card A := Subgroup.card_le_of_le hK'le
          have h2 : Nat.card K < Nat.card K' := Subgroup.card_lt_of_lt hlt
          omega
        exact ih K' hdist hK'le htK' hself''
  -- run the tower from `K₁ = N_A(X)` up to `A`
  have htCA : t ∈ Subgroup.centralizer (A : Set G) :=
    key (Nat.card A - Nat.card K₁) K₁ le_rfl (by rw [hK₁def]; exact inf_le_left) hcent₁ hself₁
  intro a ha
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp htCA) a ha

end Work.CORE2B
