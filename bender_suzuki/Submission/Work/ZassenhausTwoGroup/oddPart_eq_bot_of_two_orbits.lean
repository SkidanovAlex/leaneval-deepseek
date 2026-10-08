import Mathlib
import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.ZassenhausTwoGroup.card_dvd_card_sub_one_of_isFpfOn
import Submission.Work.ZassenhausTwoGroup.twoPart_sup_oddPart

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausTwoGroup.oddPart_eq_bot_of_two_orbits`

Let `Q ≤ G` be a finite nilpotent subgroup of even order and `D ≤ N_G(Q)` a subgroup acting
*fixed point freely* on `Q` (`IsFpfOn D Q`: every `1 ≠ d ∈ D` fixes only `1` of `Q`) with at
most two orbits on `Q#` (`FewOrbits D Q 2`, i.e. `|Q| - 1 ≤ 2 |D|`).  Then `Q` is a `2`-group:

  `O_{2'}(Q) = oddPart Q = ⊥`.

This is the "few orbits" rigidity step of Feit's theorem on Zassenhaus groups.  The proof is
purely numerical:

* `Q` nilpotent splits as `Q = O_2(Q) · O_{2'}(Q)` (`twoPart Q ⊔ oddPart Q = Q`,
  `twoPart_sup_oddPart`), the two factors meet trivially (`twoPart_inf_oddPart`, from the
  coprimality of the `2`-core and the `2'`-core) and `|O_{2'}(Q)|` is odd.
* Both factors are *characteristic* in `Q`, so `D ≤ N_G(Q)` normalises them; since
  `D` acts fixed point freely on `Q`, it does so on `O_2(Q) = twoPart Q` as well, and
  Burnside's orbit count (`card_dvd_card_sub_one_of_isFpfOn`) gives
  `|D| ∣ |twoPart Q| - 1`, hence `|D| ≤ |twoPart Q| - 1` whenever `twoPart Q ≠ ⊥`.
* If `oddPart Q ≠ ⊥` then `|oddPart Q| ≥ 3` (odd, `≠ 1`) and `|twoPart Q| ≥ 2` (`|Q|` is even
  and `twoPart Q ⊔ oddPart Q = Q` is a nontrivial decomposition).  From the trivial intersection
  the product map `twoPart Q × oddPart Q → Q` is injective, so
  `|twoPart Q| · |oddPart Q| ≤ |Q|`; combined with `FewOrbits` and the previous bound this gives

    `3 |twoPart Q| ≤ |twoPart Q| · |oddPart Q| ≤ |Q| ≤ 2 |D| + 1 ≤ 2 |twoPart Q| - 1`,

  which is absurd.

Note that *nilpotency* of `Q` is used only through the splitting `Q = O_2(Q) · O_{2'}(Q)`
(`twoPart_sup_oddPart`); the triviality of the intersection, the odd order of `oddPart Q` and the
product bound hold for every finite subgroup.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.ZassenhausTwoGroup

variable {G : Type} [Group G] [Finite G]

section Fitting

/-- `O_2(Q)` is contained in `Q`: it is the image of `O_2(Q)` under the inclusion. -/
private theorem twoPart_le (Q : Subgroup G) : twoPart Q ≤ Q := by
  rintro x ⟨y, -, rfl⟩
  exact y.2

/-- `O_{2'}(Q)` is contained in `Q`: it is the image of `O_{2'}(Q)` under the inclusion. -/
private theorem oddPart_le (Q : Subgroup G) : oddPart Q ≤ Q := by
  rintro x ⟨y, -, rfl⟩
  exact y.2

/-- `oddPart Q = O_{2'}(Q)` has odd order: it is the image, under the injective inclusion
`Q.subtype`, of the `2'`-core of `Q`, whose order is a `2'`-number
(`Work.Fitting.piCore_isPiNat`), and an integer all of whose prime divisors are `≠ 2` is odd. -/
private theorem odd_card_oddPart (Q : Subgroup G) : Odd (Nat.card (oddPart Q)) := by
  have hcard : Nat.card (oddPart Q) = Nat.card (Work.Fitting.pPrimeCore 2 ↥Q) := by
    rw [oddPart]
    exact Subgroup.card_map_of_injective (Subgroup.subtype_injective Q)
  rw [hcard]
  by_contra h
  rw [Nat.not_odd_iff_even] at h
  exact (Work.Fitting.piCore_isPiNat ↥Q (fun q => q ≠ 2)) 2 Nat.prime_two
    (even_iff_two_dvd.mp h) rfl

/-- `O_2(Q)` and `O_{2'}(Q)` meet trivially: passing to the images under the injective
inclusion `Q.subtype` preserves the intersection, and inside `Q` the two cores are disjoint
because their orders are coprime (`Work.Fitting.piCore_inf_eq_bot_of_coprime`). -/
private theorem twoPart_inf_oddPart (Q : Subgroup G) : twoPart Q ⊓ oddPart Q = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  obtain ⟨hyS, hyM⟩ := Subgroup.mem_inf.mp hy
  rw [twoPart, Subgroup.mem_map] at hyS
  obtain ⟨s, hs, hsy⟩ := hyS
  rw [oddPart, Subgroup.mem_map] at hyM
  obtain ⟨m, hm, hmy⟩ := hyM
  -- `s` and `m` have the same image in `G`, hence are equal in `Q`
  have hsm : s = m := Subtype.ext (hsy.trans hmy.symm)
  have hbot : s ∈ (⊥ : Subgroup ↥Q) := by
    rw [← Work.Fitting.piCore_inf_eq_bot_of_coprime (fun q => q = 2) (fun q => q ≠ 2) ↥Q
      (fun _ hp hp' => hp' hp)]
    exact ⟨hs, hsm ▸ hm⟩
  rw [Subgroup.mem_bot] at hbot
  rw [← hsy, hbot]
  rfl

/-- The product `|O_2(Q)| · |O_{2'}(Q)|` is at most `|Q|`: since the two cores meet trivially,
the multiplication map `O_2(Q) × O_{2'}(Q) → Q` is injective (`s₁m₁ = s₂m₂` gives
`s₂⁻¹s₁ = m₂m₁⁻¹ ∈ O_2(Q) ⊓ O_{2'}(Q) = ⊥`). -/
theorem card_twoPart_mul_card_oddPart_le (Q : Subgroup G) :
    Nat.card (twoPart Q) * Nat.card (oddPart Q) ≤ Nat.card Q := by
  have hinf : twoPart Q ⊓ oddPart Q = ⊥ := twoPart_inf_oddPart Q
  have hinj : Function.Injective
      (fun z : ↥(twoPart Q) × ↥(oddPart Q) =>
        (⟨(z.1 : G) * (z.2 : G),
          Q.mul_mem (twoPart_le Q z.1.2) (oddPart_le Q z.2.2)⟩ : ↥Q)) := by
    rintro ⟨s1, m1⟩ ⟨s2, m2⟩ h
    have h'' : (s1 : G) * (m1 : G) = (s2 : G) * (m2 : G) := congrArg Subtype.val h
    have h' : (s2 : G)⁻¹ * (s1 : G) = (m2 : G) * (m1 : G)⁻¹ := by
      calc (s2 : G)⁻¹ * (s1 : G)
          = (s2 : G)⁻¹ * ((s1 : G) * (m1 : G)) * (m1 : G)⁻¹ := by group
        _ = (s2 : G)⁻¹ * ((s2 : G) * (m2 : G)) * (m1 : G)⁻¹ := by rw [h'']
        _ = (m2 : G) * (m1 : G)⁻¹ := by group
    have hmemS : (s2 : G)⁻¹ * (s1 : G) ∈ twoPart Q :=
      (twoPart Q).mul_mem ((twoPart Q).inv_mem s2.2) s1.2
    have hmemM : (s2 : G)⁻¹ * (s1 : G) ∈ oddPart Q := by
      rw [h']
      exact (oddPart Q).mul_mem m2.2 ((oddPart Q).inv_mem m1.2)
    have hone : (s2 : G)⁻¹ * (s1 : G) = 1 := by
      have hb : (s2 : G)⁻¹ * (s1 : G) ∈ (⊥ : Subgroup G) := by
        rw [← hinf]; exact ⟨hmemS, hmemM⟩
      simpa using hb
    have hs : (s1 : G) = (s2 : G) := by
      rw [← mul_inv_cancel_left (s2 : G) (s1 : G), hone, mul_one]
    have hm : (m2 : G) * (m1 : G)⁻¹ = 1 := by rw [← h']; exact hone
    have hm' : (m1 : G) = (m2 : G) := (mul_inv_eq_one.mp hm).symm
    exact Prod.ext (Subtype.ext hs) (Subtype.ext hm')
  have hle := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_prod] at hle

end Fitting

section Normalizer

/-- `D ≤ N_G(Q)` normalises the characteristic subgroup `O_2(Q) ≤ Q`: an element `d ∈ N_G(Q)`
induces the automorphism `x ↦ d x d⁻¹` of `Q` (`Subgroup.normalizerMonoidHom`), and the `2`-core
of `Q` is characteristic in `Q` (`Work.Fitting.pCore_characteristic`), so it is preserved. -/
theorem twoPart_map_conj {Q : Subgroup G} {d : G}
    (hd : d ∈ Subgroup.normalizer (Q : Set G)) :
    (twoPart Q).map (MulAut.conj d).toMonoidHom = twoPart Q := by
  have hcoe : ∀ x : ↥Q, ((Subgroup.normalizerMonoidHom Q ⟨d, hd⟩) x : G) = d * (x : G) * d⁻¹ := by
    intro x
    show (((⟨d, hd⟩ : Subgroup.normalizer (Q : Set G)) • x : ↥Q) : G) = _
    rfl
  have hcomp : (MulAut.conj d).toMonoidHom.comp Q.subtype
      = Q.subtype.comp (Subgroup.normalizerMonoidHom Q ⟨d, hd⟩).toMonoidHom := by
    ext x
    show (MulAut.conj d) (x : G) = ((Subgroup.normalizerMonoidHom Q ⟨d, hd⟩) x : G)
    rw [hcoe, MulAut.conj_apply]
  calc (twoPart Q).map (MulAut.conj d).toMonoidHom
      = ((Work.Fitting.pCore 2 ↥Q).map Q.subtype).map (MulAut.conj d).toMonoidHom := rfl
    _ = (Work.Fitting.pCore 2 ↥Q).map ((MulAut.conj d).toMonoidHom.comp Q.subtype) := by
          rw [Subgroup.map_map]
    _ = (Work.Fitting.pCore 2 ↥Q).map
          (Q.subtype.comp (Subgroup.normalizerMonoidHom Q ⟨d, hd⟩).toMonoidHom) := by rw [hcomp]
    _ = ((Work.Fitting.pCore 2 ↥Q).map
          (Subgroup.normalizerMonoidHom Q ⟨d, hd⟩).toMonoidHom).map Q.subtype := by
          rw [Subgroup.map_map]
    _ = (Work.Fitting.pCore 2 ↥Q).map Q.subtype := by
          rw [Subgroup.characteristic_iff_map_eq.mp
            (inferInstance : (Work.Fitting.pCore 2 ↥Q).Characteristic)
            (Subgroup.normalizerMonoidHom Q ⟨d, hd⟩)]
    _ = twoPart Q := rfl

/-- If `D ≤ N_G(Q)` then also `D ≤ N_G(O_2(Q))`. -/
theorem le_normalizer_twoPart {Q D : Subgroup G} (hD : D ≤ Subgroup.normalizer (Q : Set G)) :
    D ≤ Subgroup.normalizer ((twoPart Q : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro d hd s hs
  have hmap := twoPart_map_conj (Q := Q) (hD hd)
  have hmem : (MulAut.conj d).toMonoidHom s ∈ (twoPart Q).map (MulAut.conj d).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hs
  rw [hmap] at hmem
  have h2 : (MulAut.conj d).toMonoidHom s = d * s * d⁻¹ := MulAut.conj_apply d s
  rwa [h2] at hmem

end Normalizer

section Main

/-- If `Q` is a finite nilpotent subgroup of even order then `O_2(Q) ≠ ⊥`: otherwise, by the
splitting `Q = O_2(Q) · O_{2'}(Q)` of a nilpotent group (`twoPart_sup_oddPart`), `Q` would equal
its odd part, an odd-order group. -/
theorem twoPart_ne_bot_of_even {Q : Subgroup G} (hQ : Group.IsNilpotent Q)
    (heven : Even (Nat.card Q)) : twoPart Q ≠ ⊥ := by
  intro hbot
  have hsup := twoPart_sup_oddPart (Q := Q) hQ
  rw [hbot, bot_sup_eq] at hsup
  have hodd := odd_card_oddPart Q
  rw [hsup] at hodd
  exact Nat.not_even_iff_odd.mpr hodd heven

/-- **`O_{2'}(Q) = ⊥` when `D` acts fixed point freely on `Q` with at most two orbits on `Q#`.**

See the module docstring for the (numerical) proof. -/
theorem oddPart_eq_bot_of_two_orbits {G : Type} [Group G] [Finite G] {Q D : Subgroup G}
    (hQ : Group.IsNilpotent Q) (hD : D ≤ Subgroup.normalizer (Q : Set G))
    (hfpf : Work.ZassenhausTwoGroup.IsFpfOn D Q) (heven : Even (Nat.card Q))
    (hfew : Work.ZassenhausTwoGroup.FewOrbits D Q 2) :
    Work.ZassenhausTwoGroup.oddPart Q = ⊥ := by
  by_contra hodd
  -- `D` normalises `O_2(Q)` and acts fixed point freely on it
  have hDS : D ≤ Subgroup.normalizer ((twoPart Q : Subgroup G) : Set G) :=
    le_normalizer_twoPart hD
  have hfpfS : Work.ZassenhausTwoGroup.IsFpfOn D (twoPart Q) := fun d hd hd1 x hx hconj =>
    hfpf d hd hd1 x (twoPart_le Q hx) hconj
  -- `O_2(Q)` is nontrivial, hence has at least two elements
  have hS2 : 2 ≤ Nat.card (twoPart Q) := by
    have hne : Nat.card (twoPart Q) ≠ 1 := fun h1 =>
      twoPart_ne_bot_of_even hQ heven (Subgroup.card_eq_one.mp h1)
    have hpos : 1 ≤ Nat.card (twoPart Q) := by
      haveI : Nonempty ↥(twoPart Q) := ⟨⟨1, (twoPart Q).one_mem⟩⟩
      exact Nat.card_pos
    omega
  -- Burnside: `|D| ∣ |O_2(Q)| - 1`, so `|D| ≤ |O_2(Q)| - 1`
  have hDle : Nat.card D ≤ Nat.card (twoPart Q) - 1 := by
    have hdvd := card_dvd_card_sub_one_of_isFpfOn hDS hfpfS
    have hpos : 0 < Nat.card (twoPart Q) - 1 := by omega
    exact Nat.le_of_dvd hpos hdvd
  -- at most two orbits on `Q#`: `|Q| - 1 ≤ 2 |D|`
  have hQle : Nat.card Q ≤ 2 * Nat.card D + 1 := by
    have hpos : 1 ≤ Nat.card Q := by
      haveI : Nonempty ↥Q := ⟨⟨1, Q.one_mem⟩⟩
      exact Nat.card_pos
    have h := hfew
    unfold Work.ZassenhausTwoGroup.FewOrbits at h
    omega
  -- the odd part is nontrivial, hence has at least three elements
  have hM3 : 3 ≤ Nat.card (oddPart Q) := by
    obtain ⟨k, hk⟩ := odd_card_oddPart Q
    have hne : Nat.card (oddPart Q) ≠ 1 := fun h1 =>
      hodd (Subgroup.card_eq_one.mp h1)
    omega
  -- the product bound and the contradiction
  have hprod : Nat.card (twoPart Q) * Nat.card (oddPart Q) ≤ Nat.card Q :=
    card_twoPart_mul_card_oddPart_le Q
  have h1 : 3 * Nat.card (twoPart Q) ≤ Nat.card (twoPart Q) * Nat.card (oddPart Q) := by
    have h := Nat.mul_le_mul_left (Nat.card (twoPart Q)) hM3
    rwa [mul_comm (Nat.card (twoPart Q)) 3] at h
  have h2 : 2 * Nat.card D + 1 ≤ 2 * Nat.card (twoPart Q) - 1 := by
    have h3 : 2 * Nat.card D + 1 ≤ 2 * (Nat.card (twoPart Q) - 1) + 1 := by
      have h := Nat.mul_le_mul_left 2 hDle
      omega
    omega
  omega

end Main

end Work.ZassenhausTwoGroup
