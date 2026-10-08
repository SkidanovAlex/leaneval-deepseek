import Mathlib
import Submission.Work.A7REC.Char.a7Excl120Common

namespace Work.A7REC.Char

/-- A finite group `G` with a normal subgroup `H` of order `3` satisfies
`|G| ≤ 2 * |C_G(H)|`: conjugation gives a homomorphism `G →* MulAut H`, whose kernel is
the centralizer of `H`, and `|MulAut H| = 2` because a group of order `3` is cyclic. -/
theorem card_le_two_mul_centralizer_of_normal_card_three {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [H.Normal] (h3 : Nat.card H = 3) :
    Nat.card G ≤ 2 * Nat.card (Subgroup.centralizer (H : Set G)) := by
  have hcyc : IsCyclic H := isCyclic_of_prime_card (p := 3) (hp := ⟨by norm_num⟩) h3
  have haut : Nat.card (MulAut H) = 2 := by
    rw [IsCyclic.card_mulAut H, h3]
    decide
  let φ : G →* MulAut H := MulAut.conjNormal
  have hker : φ.ker = Subgroup.centralizer (H : Set G) := by
    have hφ : φ = MulAut.conjNormal := rfl
    rw [hφ]
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
    constructor
    · intro hg u hu
      have h1 : (MulAut.conjNormal g) (⟨u, hu⟩ : H) = (1 : MulAut H) ⟨u, hu⟩ := by rw [hg]
      have h2 : (g * u * g⁻¹ : G) = u := by
        have := congr_arg (fun x : H => (x : G)) h1
        simpa [MulAut.conjNormal_apply] using this
      calc u * g = (g * u * g⁻¹) * g := by rw [h2]
        _ = g * u := by group
    · intro hg
      apply MulEquiv.ext
      intro u
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      show g * ↑u * g⁻¹ = ↑u
      rw [← hg u.1 u.2]
      group
  have h1 : Nat.card φ.ker * Nat.card φ.range = Nat.card G := Subgroup.card_ker_mul_card_range φ
  have h2 : Nat.card φ.range ≤ 2 := by
    have := Nat.card_le_card_of_injective (fun x : φ.range => (x : MulAut H)) Subtype.val_injective
    rwa [haut] at this
  calc Nat.card G = Nat.card φ.ker * Nat.card φ.range := h1.symm
    _ ≤ Nat.card φ.ker * 2 := Nat.mul_le_mul_left _ h2
    _ = 2 * Nat.card φ.ker := by ring
    _ = 2 * Nat.card (Subgroup.centralizer (H : Set G)) := by rw [hker]

/-
Case `n₃ = 1` of the exclusion of `|H| = 120`: the index of `N_C(U)` is `1`, i.e. `U ⊴ C`.
Plan: `C/C_C(U) ↪ Aut(U) ≅ C₂`, so `|C_C(U)| ≥ 60`; since `C_C(U) ⊓ S = ⊥` (from `disj`), the
product map `C_C(U) × S → C` is injective, giving `60 * 8 ≤ 120`, absurd.
-/
theorem a7Excl120IdxOne {C : Type*} [Group C] [Finite C] {U S : Subgroup C} {τ : C}
    (h : Work.A7REC.Char.Excl120Setup U S τ)
    (hi : (Subgroup.normalizer (U : Set C)).index = 1) : False := by
  -- `hi` says `N_C(U) = ⊤`, i.e. `U` is normal in `C`.
  have htop : Subgroup.normalizer (U : Set C) = ⊤ := Subgroup.index_eq_one.mp hi
  have hNormal : U.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  -- `hNormal` is picked up as the `U.Normal` instance by typeclass search below.
  -- `C/C_C(U)` embeds into `Aut(U)`, of order `2`, so `|C| ≤ 2 * |C_C(U)|`.
  have hbound : Nat.card C ≤ 2 * Nat.card (Subgroup.centralizer (U : Set C)) :=
    card_le_two_mul_centralizer_of_normal_card_three U h.card_U
  rw [h.card_eq] at hbound
  -- The product map `C_C(U) × S → C` is injective because `C_C(U) ⊓ S = ⊥`.
  have hinj : Function.Injective (fun x : Subgroup.centralizer (U : Set C) × S =>
      ((x.1 : C) * (x.2 : C))) := by
    rintro ⟨k1, s1⟩ ⟨k2, s2⟩ hxy
    simp only at hxy
    have key : ((k2 : C)⁻¹ * (k1 : C)) ∈ S ⊓ Subgroup.centralizer (U : Set C) := by
      refine ⟨?_, ?_⟩
      · have heq : (k2 : C)⁻¹ * (k1 : C) = (s2 : C) * (s1 : C)⁻¹ := by
          have := congr_arg (fun z => (k2 : C)⁻¹ * z * (s1 : C)⁻¹) hxy
          simpa [mul_assoc] using this
        rw [heq]
        exact Subgroup.mul_mem _ s2.2 (Subgroup.inv_mem _ s1.2)
      · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ k2.2) k1.2
    rw [h.disj, Subgroup.mem_bot] at key
    have hk : (k1 : C) = (k2 : C) := by
      have := congr_arg (fun z => (k2 : C) * z) key
      simpa using this
    have hs : (s1 : C) = (s2 : C) := by
      have hxy' := hxy
      rw [hk] at hxy'
      exact mul_left_cancel hxy'
    exact Prod.ext (Subtype.ext hk) (Subtype.ext hs)
  have hle : Nat.card (Subgroup.centralizer (U : Set C) × S) ≤ Nat.card C :=
    Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod, h.card_S, h.card_eq] at hle
  -- `120 ≤ 2 * |C_C(U)|` and `|C_C(U)| * 8 ≤ 120` are contradictory.
  omega

end Work.A7REC.Char
