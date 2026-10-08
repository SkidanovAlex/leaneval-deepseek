import Mathlib

set_option linter.style.haveILetI false

namespace Work.A7REC.Char

/-- Auxiliary statement: if `K ≤ N_G(U)` with `|U| = 3`, `K ⊓ C_G(U) = ⊥`, and `K` contains an
element `τ` of order `2`, then `|K| = 2`.

The conjugation action of `K` on `U` gives an injective map `K → Aut(U)`, and `Aut(U)` has
order `2` because `U` is cyclic of order `3`. Hence `|K| ≤ 2`, while `τ ∈ K` gives `|K| ≥ 2`. -/
theorem card_eq_two_of_le_normalizer {G : Type*} [Group G] {U K : Subgroup G} {τ : G}
    (hU3 : Nat.card U = 3) (hτK : τ ∈ K) (hτ2 : orderOf τ = 2)
    (hKN : K ≤ Subgroup.normalizer (U : Set G))
    (hdisj : K ⊓ Subgroup.centralizer (U : Set G) = ⊥) :
    Nat.card ↥K = 2 := by
  -- `U` is a finite cyclic group of order `3`.
  have hUfin : Finite ↥U := Nat.finite_of_card_ne_zero (by rw [hU3]; norm_num)
  haveI := hUfin
  haveI hcyc : IsCyclic ↥U := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact isCyclic_of_prime_card hU3
  -- consequently `Aut(U)` has order `2`.
  have hAut : Nat.card (MulAut ↥U) = 2 := by
    rw [IsCyclic.card_mulAut ↥U, hU3]
    decide
  -- the conjugation homomorphism `K →* Aut(U)`
  let φ : ↥K →* MulAut ↥U := (Subgroup.normalizerMonoidHom U).comp (Subgroup.inclusion hKN)
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff φ, Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    -- `x` acts trivially on `U`, hence lies in `C_G(U)`
    have hcent : (x : G) ∈ Subgroup.centralizer (U : Set G) := by
      have hx' : Subgroup.normalizerMonoidHom U (Subgroup.inclusion hKN x) = 1 := hx
      have hmem : Subgroup.inclusion hKN x ∈ (Subgroup.normalizerMonoidHom U).ker :=
        MonoidHom.mem_ker.mpr hx'
      rw [Subgroup.normalizerMonoidHom_ker U] at hmem
      have h' := Subgroup.mem_subgroupOf.mp hmem
      simpa [Subgroup.coe_inclusion] using h'
    -- but also `x ∈ K`, so `x ∈ K ⊓ C_G(U) = ⊥`
    have hxK : (x : G) ∈ K := x.2
    have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
      have : (x : G) ∈ K ⊓ Subgroup.centralizer (U : Set G) := ⟨hxK, hcent⟩
      rwa [hdisj] at this
    exact Subtype.ext (Subgroup.mem_bot.mp hxbot)
  haveI : Finite ↥K := Finite.of_injective φ hφinj
  -- upper bound `|K| ≤ 2`
  have hle2 : Nat.card ↥K ≤ 2 := by
    have h := Nat.card_le_card_of_injective (φ : ↥K → MulAut ↥U) hφinj
    rwa [hAut] at h
  -- lower bound `|K| ≥ 2` from `τ`
  have hzp : Subgroup.zpowers τ ≤ K := Subgroup.zpowers_le.mpr hτK
  have hge2 : 2 ≤ Nat.card ↥K := by
    calc (2 : ℕ) = orderOf τ := hτ2.symm
      _ = Nat.card ↥(Subgroup.zpowers τ) := (Nat.card_zpowers τ).symm
      _ ≤ Nat.card ↥K :=
          Nat.card_le_card_of_injective (Subgroup.inclusion hzp) (Subgroup.inclusion_injective hzp)
  exact le_antisymm hle2 hge2

theorem card_inf_normalizer_eq_two {G : Type*} [Group G] {U S : Subgroup G} {τ : G}
    (hU3 : Nat.card U = 3) (hτS : τ ∈ S) (hτ2 : orderOf τ = 2)
    (hτN : τ ∈ Subgroup.normalizer (U : Set G))
    (hdisj : S ⊓ Subgroup.centralizer (U : Set G) = ⊥) :
    Nat.card ↥(S ⊓ Subgroup.normalizer (U : Set G)) = 2 := by
  refine card_eq_two_of_le_normalizer (U := U) (τ := τ)
    (K := S ⊓ Subgroup.normalizer (U : Set G)) hU3 ?_ hτ2 inf_le_right ?_
  · exact Subgroup.mem_inf.mpr ⟨hτS, hτN⟩
  · have hle : (S ⊓ Subgroup.normalizer (U : Set G)) ⊓ Subgroup.centralizer (U : Set G)
        ≤ ⊥ := by
      calc (S ⊓ Subgroup.normalizer (U : Set G)) ⊓ Subgroup.centralizer (U : Set G)
          ≤ S ⊓ Subgroup.centralizer (U : Set G) := inf_le_inf inf_le_left le_rfl
        _ = ⊥ := hdisj
    exact le_antisymm hle bot_le

end Work.A7REC.Char
