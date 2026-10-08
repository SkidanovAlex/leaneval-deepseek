import Mathlib
import Submission.Work.BSW.Vocab

open scoped MatrixGroups
open scoped IsMulCommutative

namespace Work.BSW.Char

open Subgroup Work.GW2
open Work.BSW

set_option linter.style.haveILetI false

/-- Bender 1974 §2 (p. 230).  For `k = |K| ≥ 6` there are linear characters `ρ₁`, `ρ₂` of `K` with
`ρ₁(t) = 1`, `ρ₂(t) = -1`, neither fixed by conjugation by `s` (i.e. `ρᵢ ∘ conjHomK ≠ ρᵢ`).

Indeed `K` is abelian of order `k` with the unique involution `t`, so it has `k` linear characters,
`k/2 ≥ 3` of which take the value `1` at `t` and `k/2 ≥ 3` the value `-1`; the `s`-stable
characters are exactly those trivial on `K²` (there are two, both with value `1` at `t` when
`t ∈ K²`, and one with value `1`, one with value `-1` otherwise), so a non-stable character with
each of the two values exists. -/
theorem exists_linear_characters {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) (hk : 6 ≤ Nat.card ↥K) :
    ∃ ρ₁ ρ₂ : ↥K →* ℂˣ,
      ρ₁ ⟨t, Work.BSW.t_mem_K h⟩ = 1 ∧ ρ₂ ⟨t, Work.BSW.t_mem_K h⟩ = -1 ∧
      (∃ y : ↥K, ρ₁ y ≠ ρ₁ (Work.BSW.conjHomK h y)) ∧
      (∃ y : ↥K, ρ₂ y ≠ ρ₂ (Work.BSW.conjHomK h y)) := by
  classical
  haveI hcomm : IsMulCommutative ↥K := isMulCommutative_K h
  letI : CommGroup ↥K := IsMulCommutative.instCommGroup
  have hroot : HasEnoughRootsOfUnity ℂ (Monoid.exponent ↥K) := inferInstance
  -- the dual group is finite
  have hcardK : Nat.card ↥K ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  haveI hfinD : Finite (↥K →* ℂˣ) := (Nat.card_ne_zero.mp (by
    rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity ↥K ℂ]; exact hcardK)).2
  let tK : ↥K := ⟨t, t_mem_K h⟩
  have hconj : ∀ y : ↥K, conjHomK h y = y⁻¹ := fun y => by
    ext; rw [conjHomK_apply]; exact inverts_s_K h y y.2
  have hord : orderOf tK = 2 := by
    rw [← Subgroup.orderOf_coe tK]; exact orderOf_t h
  have htne : tK ≠ 1 := by
    intro hh; rw [hh, orderOf_one] at hord; exact absurd hord (by norm_num)
  have ht2 : tK * tK = 1 := by
    have := pow_orderOf_eq_one tK
    rw [hord] at this
    simpa [pow_two] using this
  -- (1) the squaring set on `K` has two elements
  have hsqcard : Nat.card {y : ↥K // y * y = 1} = 2 := by
    have hset : ({y : ↥K | y * y = 1} : Set ↥K) = {1, tK} := by
      ext y
      show y * y = 1 ↔ y ∈ ({1, tK} : Set ↥K)
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hy
        have hy' : (y : G) * (y : G) = 1 := congrArg Subtype.val hy
        rcases involution_mem_K h y.2 hy' with h1 | h1
        · exact Or.inl (Subtype.ext h1)
        · exact Or.inr (Subtype.ext h1)
      · rintro (rfl | rfl)
        · simp
        · exact ht2
    have hn : ({y : ↥K | y * y = 1} : Set ↥K).ncard = 2 := by
      rw [hset, Set.ncard_pair]
      intro hcontra
      exact htne (by simpa using (congrArg (fun x : ↥K => (x : G)) hcontra).symm)
    have hcoe := Nat.card_coe_set_eq ({y : ↥K | y * y = 1} : Set ↥K)
    rw [hn] at hcoe
    exact hcoe
  -- (2) the two-torsion of the dual group has two elements, via duality
  have he : (↥K →* ℂˣ) ≃* ↥K :=
    (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity ↥K ℂ).some
  have hD2 : Nat.card {ρ : ↥K →* ℂˣ // ρ * ρ = 1} = 2 := by
    rw [Nat.card_congr
      ({ toFun := fun ρ => ⟨he ρ.1, by
            show he ρ.1 * he ρ.1 = 1; rw [← map_mul, ρ.2, map_one]⟩
         invFun := fun y => ⟨he.symm y.1, by
            show he.symm y.1 * he.symm y.1 = 1; rw [← map_mul, y.2, map_one]⟩
         left_inv := by intro ρ; ext; simp
         right_inv := by intro y; ext; simp } :
          {ρ : ↥K →* ℂˣ // ρ * ρ = 1} ≃ {y : ↥K // y * y = 1}), hsqcard]
  -- (3) `ρ * ρ = 1` iff `ρ` is fixed by `s`-conjugation
  have hfix : ∀ ρ : ↥K →* ℂˣ, ρ * ρ = 1 ↔ ∀ y, ρ (conjHomK h y) = ρ y := by
    intro ρ
    rw [MonoidHom.ext_iff]
    constructor
    · intro hh y
      have h1 : ρ y * ρ y = 1 := by
        have := hh y; rwa [MonoidHom.mul_apply, MonoidHom.one_apply] at this
      rw [hconj y, map_inv, inv_eq_of_mul_eq_one_left h1]
    · intro hh y
      have h1 : (ρ y)⁻¹ = ρ y := by rw [← map_inv, ← hconj y]; exact hh y
      rw [MonoidHom.mul_apply, MonoidHom.one_apply]
      nth_rewrite 2 [← h1]
      rw [mul_inv_cancel]
  -- (4) the annihilator of `⟨t⟩` inside the dual group
  let Z : Subgroup ↥K := Subgroup.zpowers tK
  have hZcard : Nat.card Z = 2 := by
    show Nat.card (Subgroup.zpowers tK) = 2
    rw [Nat.card_zpowers, hord]
  have hm2 : Nat.card (↥K ⧸ Z) * 2 = Nat.card ↥K := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
    rw [hZcard] at h1
    exact h1.symm
  have hm3 : 3 ≤ Nat.card (↥K ⧸ Z) := by omega
  let S1 : Subgroup (↥K →* ℂˣ) := (CommGroup.subgroupOrderIsoSubgroupMonoidHom ↥K ℂ Z).ofDual
  have hS1mem : ∀ ρ : ↥K →* ℂˣ, ρ ∈ S1 ↔ ρ tK = 1 := by
    intro ρ
    show ρ ∈ (CommGroup.subgroupOrderIsoSubgroupMonoidHom ↥K ℂ Z).ofDual ↔ ρ tK = 1
    rw [CommGroup.mem_subgroupOrderIsoSubgroupMonoidHom_iff]
    constructor
    · intro hh; exact hh _ (Subgroup.mem_zpowers _)
    · intro hh g hg
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
      rw [← hk, map_zpow, hh, one_zpow]
  have hS1card : Nat.card S1 = Nat.card (↥K ⧸ Z) := by
    show Nat.card ((CommGroup.subgroupOrderIsoSubgroupMonoidHom ↥K ℂ Z).ofDual) = Nat.card (↥K ⧸ Z)
    exact CommGroup.card_subgroupOrderIsoSubgroupMonoidHom ℂ Z
  have hS1lb : 3 ≤ Nat.card S1 := by rw [hS1card]; exact hm3
  have hcc : (S1 : Set (↥K →* ℂˣ)).ncard = Nat.card S1 :=
    (Nat.card_coe_set_eq (S1 : Set (↥K →* ℂˣ))).symm
  have hF2 : ({ρ : ↥K →* ℂˣ | ρ * ρ = 1} : Set (↥K →* ℂˣ)).ncard = 2 := by
    rw [← Nat.card_coe_set_eq]; exact hD2
  -- (5) a character with value `-1` at `t`
  obtain ⟨ρ₀, hρ₀⟩ : ∃ ρ₀ : ↥K →* ℂˣ, ρ₀ tK = -1 := by
    obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity ↥K ℂ (a := tK) htne
    refine ⟨φ, ?_⟩
    apply Units.ext
    have hsq : φ tK * φ tK = 1 := by rw [← map_mul, ht2, map_one]
    have h2 : (↑(φ tK) : ℂ)^2 = 1 := by
      have := congrArg (fun x : ℂˣ => (x : ℂ)) hsq
      simpa [pow_two] using this
    rcases (sq_eq_one_iff.mp h2) with h1 | h1
    · exact absurd h1 (by intro hc'; exact hφ (Units.ext hc'))
    · simpa using h1
  -- (6) select a non-fixed character with value `1` at `t`
  have hex1 : ∃ ρ₁ : ↥K →* ℂˣ, ρ₁ tK = 1 ∧ ¬ (ρ₁ * ρ₁ = 1) := by
    by_contra hcon
    push Not at hcon
    have hsub : (S1 : Set (↥K →* ℂˣ)) ⊆ {ρ | ρ * ρ = 1} := fun ρ hρ =>
      hcon ρ ((hS1mem ρ).mp hρ)
    have h3 : 3 ≤ (S1 : Set (↥K →* ℂˣ)).ncard := by rw [hcc]; exact hS1lb
    have := Set.ncard_le_ncard hsub
    rw [hF2] at this
    omega
  -- (7) select a non-fixed character with value `-1` at `t`
  have hex2 : ∃ ρ₂ : ↥K →* ℂˣ, ρ₂ tK = -1 ∧ ¬ (ρ₂ * ρ₂ = 1) := by
    by_contra hcon
    push Not at hcon
    have hinj : Function.Injective
        (fun σ : S1 => (⟨ρ₀ * σ.1, hcon (ρ₀ * σ.1) (by
            rw [MonoidHom.mul_apply, hρ₀, (hS1mem σ.1).mp σ.2, mul_one])⟩ :
          {ρ : ↥K →* ℂˣ // ρ * ρ = 1})) := by
      intro σ₁ σ₂ hh
      have h1 : ρ₀ * σ₁.1 = ρ₀ * σ₂.1 := congrArg Subtype.val hh
      exact Subtype.ext (mul_left_cancel h1)
    have := Nat.card_le_card_of_injective _ hinj
    rw [hD2] at this
    omega
  obtain ⟨ρ₁, hρ₁t, hρ₁nf⟩ := hex1
  obtain ⟨ρ₂, hρ₂t, hρ₂nf⟩ := hex2
  refine ⟨ρ₁, ρ₂, hρ₁t, hρ₂t, ?_, ?_⟩
  · have hnf : ¬ ∀ y, ρ₁ (conjHomK h y) = ρ₁ y := fun hh => hρ₁nf ((hfix ρ₁).mpr hh)
    push Not at hnf
    obtain ⟨y, hy⟩ := hnf
    exact ⟨y, hy.symm⟩
  · have hnf : ¬ ∀ y, ρ₂ (conjHomK h y) = ρ₂ y := fun hh => hρ₂nf ((hfix ρ₂).mpr hh)
    push Not at hnf
    obtain ⟨y, hy⟩ := hnf
    exact ⟨y, hy.symm⟩

end Work.BSW.Char
