/-
Area `A7REC`: the involution-centralizer leaf of the pass-8 C2+C3 design
(`_design_gw/Core8.lean` §1, `A7InvCentProp`).

Every involution centralizer has order `24` and contains exactly one subgroup of order `3`:
`C_G(z)` has order `24` with `U` the unique subgroup of order `3` (a second one would produce a
subgroup of order `3·3 = 9`, which cannot divide `24`), and `OneInvClass` transports this to every
involution by conjugating the centralizer and its subgroups.
-/
import Submission.Work.A7REC.Excl

namespace Work.A7REC.Char

open Subgroup

/-- **`A7InvCentProp`.**  In a group satisfying `A7RecHyps` with one class of involutions, every
involution centralizer has order `24` and contains exactly one subgroup of order `3`. -/
theorem a7InvCent : A7InvCentProp := by
  intro G _ _ S z U V hyps hone x hx
  have hCz24 : Nat.card (Subgroup.centralizer ({z} : Set G)) = 24 :=
    Basic.card_centralizer_z G (A7RecCtx.ofHyps hyps)
  obtain ⟨_hsimple, _hcard, _hSdih, _hzS, hz2, _hzcen, hCz, hUcard, hUnorm, _hVdef, _hV4,
    _hcross, _hNUV, _hNUcard⟩ := hyps
  -- `U` is the unique subgroup of order `3` of `C_G(z)`
  have hU_le_C : U ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [hCz]; exact le_sup_left
  have hC_le_NU : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (U : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hU_le_C).mp hUnorm
  have huniq : ∀ A : Subgroup G, A ≤ Subgroup.centralizer ({z} : Set G) → Nat.card A = 3 →
      A = U := by
    intro A hA hAcard
    by_contra hne
    have hbot : U ⊓ A = ⊥ := by
      rw [Subgroup.eq_bot_iff_card]
      have hdvd : Nat.card ↥(U ⊓ A) ∣ 3 := by
        rw [← hUcard]
        exact Subgroup.card_dvd_of_le (α := G) inf_le_left
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact h1
      · exfalso
        have hEq : U ⊓ A = U := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hUcard])
        have hUA : U ≤ A := (le_of_eq hEq.symm).trans inf_le_right
        exact hne (Subgroup.eq_of_le_of_card_ge hUA (by rw [hAcard, hUcard])).symm
    have hjoin : Nat.card ↥(U ⊔ A) = 9 := by
      have hmem : A ≤ Subgroup.normalizer (U : Set G) := le_trans hA hC_le_NU
      have hd : Disjoint U A := disjoint_iff.mpr hbot
      rw [Basic.card_sup_mul_card_of_le_normalizer_of_disjoint hmem hd, hUcard, hAcard]
    have hle : U ⊔ A ≤ Subgroup.centralizer ({z} : Set G) := sup_le hU_le_C hA
    have hdvd : Nat.card ↥(U ⊔ A) ∣ 24 := by
      rw [← hCz24]
      exact Subgroup.card_dvd_of_le (α := G) hle
    rw [hjoin] at hdvd
    omega
  -- conjugate `x` to `z`
  obtain ⟨c, hc⟩ := hone x z hx hz2
  have hcx : (↑c : G) * x * (↑c : G)⁻¹ = z := by
    rw [hc.eq]; group
  have hz_eq : (↑c : G)⁻¹ * z * (↑c : G) = x := by rw [← hcx]; group
  -- conjugation by `c` maps `C_G(x)` onto `C_G(z)`
  have hmapC : (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj (↑c : G)).toMonoidHom
      = Subgroup.centralizer ({z} : Set G) := by
    refine le_antisymm ?_ ?_
    · refine (Subgroup.map_centralizer_le_centralizer_image ({x} : Set G)
        (MulAut.conj (↑c : G)).toMonoidHom).trans ?_
      rw [Set.image_singleton]
      have : (MulEquiv.toMonoidHom (MulAut.conj (↑c : G))) x = z := hcx
      rw [this]
    · intro y hy
      refine ⟨(↑c : G)⁻¹ * y * (↑c : G), ?_, ?_⟩
      · show (↑c : G)⁻¹ * y * (↑c : G) ∈ Subgroup.centralizer ({x} : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        rw [hw]
        have hyz : z * y = y * z := Subgroup.mem_centralizer_iff.mp hy z rfl
        calc x * ((↑c : G)⁻¹ * y * (↑c : G))
            = ((↑c : G)⁻¹ * z * (↑c : G)) * ((↑c : G)⁻¹ * y * (↑c : G)) := by rw [hz_eq]
          _ = (↑c : G)⁻¹ * (z * y) * (↑c : G) := by group
          _ = (↑c : G)⁻¹ * (y * z) * (↑c : G) := by rw [hyz]
          _ = ((↑c : G)⁻¹ * y * (↑c : G)) * ((↑c : G)⁻¹ * z * (↑c : G)) := by group
          _ = ((↑c : G)⁻¹ * y * (↑c : G)) * x := by rw [hz_eq]
      · show (↑c : G) * ((↑c : G)⁻¹ * y * (↑c : G)) * (↑c : G)⁻¹ = y
        group
  have hcard_map : ∀ C : Subgroup G,
      Nat.card ↥(C.map (MulAut.conj (↑c : G)).toMonoidHom) = Nat.card ↥C := fun C =>
    (Nat.card_congr (Subgroup.equivMapOfInjective C (MulAut.conj (↑c : G)).toMonoidHom
      (MulAut.conj (↑c : G)).injective).toEquiv).symm
  have hcomap : ∀ C : Subgroup G,
      (C.map (MulAut.conj (↑c : G)).toMonoidHom).comap (MulAut.conj (↑c : G)).toMonoidHom = C :=
    fun C => Subgroup.comap_map_eq_self_of_injective
      (f := (MulAut.conj (↑c : G)).toMonoidHom) (MulAut.conj (↑c : G)).injective C
  constructor
  · -- `|C_G(x)| = 24`
    rw [← hCz24, ← hmapC]
    exact (hcard_map (Subgroup.centralizer ({x} : Set G))).symm
  · -- uniqueness of the subgroup of order `3` in `C_G(x)`
    intro A B hA hB hAc hBc
    have hA' : A.map (MulAut.conj (↑c : G)).toMonoidHom ≤
        Subgroup.centralizer ({z} : Set G) := by
      rw [← hmapC]
      exact Subgroup.map_mono hA
    have hB' : B.map (MulAut.conj (↑c : G)).toMonoidHom ≤
        Subgroup.centralizer ({z} : Set G) := by
      rw [← hmapC]
      exact Subgroup.map_mono hB
    have h1 : A.map (MulAut.conj (↑c : G)).toMonoidHom = U :=
      huniq _ hA' (by rw [hcard_map A, hAc])
    have h2 : B.map (MulAut.conj (↑c : G)).toMonoidHom = U :=
      huniq _ hB' (by rw [hcard_map B, hBc])
    calc A = ((A.map (MulAut.conj (↑c : G)).toMonoidHom).comap
          (MulAut.conj (↑c : G)).toMonoidHom) := (hcomap A).symm
      _ = ((B.map (MulAut.conj (↑c : G)).toMonoidHom).comap
          (MulAut.conj (↑c : G)).toMonoidHom) := by rw [h1, h2]
      _ = B := hcomap B

end Work.A7REC.Char
