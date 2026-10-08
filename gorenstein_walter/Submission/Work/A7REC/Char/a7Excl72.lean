/-
Area `A7REC`, file `Char/a7Excl72.lean`: exclusion of `|H| = 72` (design pass 8 §1.4).

`A7Excl72Prop` states that no subgroup `H` of a finite group `G` with `|H| = 72` can contain the
Suzuki configuration `(U, S', τ')` (`|U| = 3`, `|S'| = 8`, `τ' ∈ Z(S')` an involution normalizing
`U`, and `S' ⊓ C_G(U) = 1`), provided the "no nine" statement `NoNine G U` holds: no subgroup of
order `9` has *all* of its nonidentity elements `G`-conjugate into `U`.

The argument is the design-pass-8 kernel argument, run inside `H`:

* a Sylow `3`-subgroup `P` of `H` containing `U` has order `9` and is abelian, so `P ≤ N_H(U)`
  and `18 ∣ |N_H(U)|`;
* `S' ⊓ N_H(U)` embeds in `Aut(U) ≅ C₂` and contains `τ'`, so it has order `2`; hence the
  `S'`-orbit of `U` has `4` elements, while the number of `H`-conjugates of `U` is
  `[H : N_H(U)] ≤ 4`.  So the `H`-orbit of `U` *is* its `S'`-orbit, and `|N_H(U)| = 18`;
* every `S'`-conjugate of `U` is `τ'`-stable, so `τ'` lies in the core `K` of `N_H(U)`.  As
  `K ⊴ H` and `K ∩ U ⊴ U`, the commutator argument gives `U ≤ K`; being normal, `K` contains
  *all* conjugates of `U`, hence at least four subgroups of order `3`, so `|K| ≠ 6` and `|K| = 18`;
* any conjugate `ω ≠ U` of `U` satisfies `ω ≤ K`; if it met the group `U ⊔ ω` (of order `9`)
  trivially, the product set would have `27 > 18` elements, so all four conjugates of `U` lie in
  `U ⊔ ω`.  That group is `C₃ × C₃`, so its four subgroups of order `3` are exactly the four
  conjugates of `U` and every nonidentity element of it is conjugate into `U` — contradicting
  `NoNine`.

All the counting inputs are the general lemmas proved in the sibling files of this directory.
-/
import Mathlib
import Submission.Work.A7REC.Excl
import Submission.Work.A7REC.Join.card_sup_of_le_normalizer_of_disjoint
import Submission.Work.A7REC.Char.card_mul_card_le_card_of_inf_eq_bot
import Submission.Work.A7REC.Char.noNine_subgroupOf
import Submission.Work.A7REC.Char.exists_card_nine_le_normalizer
import Submission.Work.A7REC.Char.ncard_range_conj_mul_card_inf_normalizer
import Submission.Work.A7REC.Char.card_inf_normalizer_eq_two
import Submission.Work.A7REC.Char.exists_mem_of_ncard_four

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.A7REC.Char

open Subgroup

/-- The application of the monoid homomorphism underlying `MulAut.conj g`. -/
theorem excl72_conj_apply {C : Type*} [Group C] (g x : C) :
    (MulAut.conj g).toMonoidHom x = g * x * g⁻¹ := by
  simp [MulAut.conj_apply]

/-- Conjugation does not change the cardinality of a subgroup. -/
theorem excl72_card_map_conj {C : Type*} [Group C] (U : Subgroup C) (g : C) :
    Nat.card ↥(U.map (MulAut.conj g).toMonoidHom) = Nat.card ↥U :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

/-- In a subgroup of order `3`, every nonidentity element generates the whole subgroup. -/
theorem excl72_zpowers_eq_of_card_three {C : Type*} [Group C] [Finite C] {U : Subgroup C}
    (hU : Nat.card U = 3) {u : C} (hu : u ∈ U) (hu1 : u ≠ 1) : Subgroup.zpowers u = U := by
  have hle : Subgroup.zpowers u ≤ U := Subgroup.zpowers_le.mpr hu
  have h3 : orderOf u = 3 := by
    have hdvd : orderOf u ∣ 3 := by
      rw [← Nat.card_zpowers, ← hU]
      exact Subgroup.card_dvd_of_le hle
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hu1
    · exact h
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hU, Nat.card_zpowers, h3]

/-! ## The main abstract argument -/

/-- **Exclusion of `|C| = 72`** for the Suzuki configuration `(U, S, τ)`. -/
theorem excl72_aux {C : Type*} [Group C] [Finite C] (hC : Nat.card C = 72)
    {U S : Subgroup C} {τ : C} (hU3 : Nat.card U = 3) (hS8 : Nat.card S = 8)
    (hτS : τ ∈ S) (hτ2 : orderOf τ = 2) (hτcen : ∀ x ∈ S, x * τ = τ * x)
    (hτN : τ ∈ Subgroup.normalizer (U : Set C))
    (hdisj : S ⊓ Subgroup.centralizer (U : Set C) = ⊥)
    (hNoNine : ∀ P : Subgroup C, Nat.card P = 9 →
      ∃ p ∈ P, p ≠ 1 ∧ ∀ g : C, ∀ u ∈ U, g * u * g⁻¹ ≠ p) :
    False := by
  classical
  have hτ1 : τ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hτ2
    omega
  have hτC : τ ∉ Subgroup.centralizer (U : Set C) := by
    intro hmem
    have hmem' : τ ∈ S ⊓ Subgroup.centralizer (U : Set C) := ⟨hτS, hmem⟩
    rw [hdisj, Subgroup.mem_bot] at hmem'
    exact hτ1 hmem'
  set N : Subgroup C := Subgroup.normalizer (U : Set C) with hNdef
  have hτN' : τ ∈ N := hτN
  -- `S ⊓ N` has order `2`
  have hSinN : Nat.card ↥(S ⊓ N) = 2 := card_inf_normalizer_eq_two hU3 hτS hτ2 hτN hdisj
  -- the `S`-orbit and the `C`-orbit of `U`
  set ΩS : Set (Subgroup C) :=
    Set.range (fun s : ↥S => U.map (MulAut.conj (s : C)).toMonoidHom) with hΩSdef
  set Ω : Set (Subgroup C) := Set.range (fun c : C => U.map (MulAut.conj c).toMonoidHom)
    with hΩdef
  have hΩS4 : ΩS.ncard = 4 := by
    have hmul := ncard_range_conj_mul_card_inf_normalizer (G := C) U S
    have hSinN' : Nat.card ↥(S ⊓ Subgroup.normalizer (U : Set C)) = 2 := hSinN
    rw [← hΩSdef, hSinN', hS8] at hmul
    omega
  have hΩSsub : ΩS ⊆ Ω := by
    intro W hW
    rw [hΩdef]
    rw [hΩSdef] at hW
    obtain ⟨s, rfl⟩ := hW
    exact ⟨(s : C), rfl⟩
  have hΩSle : ΩS.ncard ≤ Ω.ncard := Set.ncard_le_ncard hΩSsub (Set.finite_range _)
  -- Sylow: a subgroup of order `9` containing `U`, inside `N`
  obtain ⟨P, hP9, hUP, hPN⟩ := exists_card_nine_le_normalizer hC hU3
  have h9dvd : 9 ∣ Nat.card ↥N := by
    rw [← hP9]
    exact Subgroup.card_dvd_of_le hPN
  have h2dvd : 2 ∣ Nat.card ↥N := by
    rw [← hτ2, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hτN')
  have h18dvd : 18 ∣ Nat.card ↥N := by
    have h := Nat.Coprime.mul_dvd_of_dvd_of_dvd (show Nat.Coprime 9 2 by norm_num) h9dvd h2dvd
    simpa using h
  have hNge : 18 ≤ Nat.card ↥N := Nat.le_of_dvd Nat.card_pos h18dvd
  have hΩmul : Ω.ncard * Nat.card ↥N = 72 := by
    have hmul := ncard_range_conj_mul_card_inf_normalizer (G := C) U ⊤
    have hrange : (Set.range (fun t : ↥(⊤ : Subgroup C) =>
        U.map (MulAut.conj (t : C)).toMonoidHom)) = Ω := by
      rw [hΩdef]
      ext W
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨(t : C), rfl⟩
      · rintro ⟨c, rfl⟩
        exact ⟨⟨c, trivial⟩, rfl⟩
    rw [hrange, top_inf_eq, Subgroup.card_top, hC] at hmul
    exact hmul
  have hΩle4 : Ω.ncard ≤ 4 := by
    have h1 : Ω.ncard * 18 ≤ Ω.ncard * Nat.card ↥N := Nat.mul_le_mul_left _ hNge
    rw [hΩmul] at h1
    omega
  have hΩcard : Ω.ncard = 4 := by omega
  have hN18 : Nat.card ↥N = 18 := by
    rw [hΩcard] at hΩmul
    omega
  have hΩeq : ΩS = Ω := Set.eq_of_subset_of_ncard_le hΩSsub (by omega) (Set.finite_range _)
  -- `τ` lies in the core of `N`
  have hτcore : τ ∈ N.normalCore := by
    rw [Subgroup.normalCore_eq_iInf_map_conj, Subgroup.mem_iInf]
    intro c
    rw [Subgroup.mem_map]
    refine ⟨c⁻¹ * τ * c, ?_, ?_⟩
    · have hmemΩ : U.map (MulAut.conj c).toMonoidHom ∈ Ω := by
        rw [hΩdef]
        exact ⟨c, rfl⟩
      rw [← hΩeq] at hmemΩ
      rw [hΩSdef] at hmemΩ
      obtain ⟨s, hs⟩ := hmemΩ
      -- `τ` stabilizes `U^c`
      have hstab : ∀ y ∈ U.map (MulAut.conj c).toMonoidHom,
          τ * y * τ⁻¹ ∈ U.map (MulAut.conj c).toMonoidHom := by
        intro y hy
        rw [← hs] at hy
        have h1 : τ * y * τ⁻¹ ∈ U.map (MulAut.conj (s : C)).toMonoidHom := by
          rw [Subgroup.mem_map] at hy ⊢
          obtain ⟨x, hx, hxy⟩ := hy
          rw [excl72_conj_apply] at hxy
          refine ⟨τ * x * τ⁻¹, (Subgroup.mem_normalizer_iff.mp hτN x).mp hx, ?_⟩
          rw [excl72_conj_apply, ← hxy]
          have hcom : (s : C) * τ = τ * (s : C) := hτcen (s : C) s.2
          have key : τ⁻¹ * (s : C)⁻¹ = (s : C)⁻¹ * τ⁻¹ := by
            have h := congrArg Inv.inv hcom
            rwa [mul_inv_rev, mul_inv_rev] at h
          calc (s : C) * (τ * x * τ⁻¹) * (s : C)⁻¹
              = ((s : C) * τ) * x * (τ⁻¹ * (s : C)⁻¹) := by group
            _ = (τ * (s : C)) * x * (τ⁻¹ * (s : C)⁻¹) := by rw [← hcom]
            _ = (τ * (s : C)) * x * ((s : C)⁻¹ * τ⁻¹) := by rw [key]
            _ = τ * ((s : C) * x * (s : C)⁻¹) * τ⁻¹ := by group
        have hs' : U.map (MulAut.conj (s : C)).toMonoidHom = U.map (MulAut.conj c).toMonoidHom := hs
        rwa [hs'] at h1
      have hmap : U.map (MulAut.conj (c⁻¹ * τ * c)).toMonoidHom = U := by
        refine Subgroup.eq_of_le_of_card_ge ?_ ?_
        · intro z hz
          rw [Subgroup.mem_map] at hz
          obtain ⟨x, hx, hxz⟩ := hz
          rw [excl72_conj_apply] at hxz
          rw [← hxz]
          have hxV : c * x * c⁻¹ ∈ U.map (MulAut.conj c).toMonoidHom := by
            rw [Subgroup.mem_map]
            exact ⟨x, hx, by rw [excl72_conj_apply]⟩
          have hτxV : τ * (c * x * c⁻¹) * τ⁻¹ ∈ U.map (MulAut.conj c).toMonoidHom :=
            hstab _ hxV
          rw [Subgroup.mem_map] at hτxV
          obtain ⟨x', hx', hx'eq⟩ := hτxV
          rw [excl72_conj_apply] at hx'eq
          have hkey : c⁻¹ * τ * c * x * (c⁻¹ * τ * c)⁻¹ = x' := by
            rw [show c⁻¹ * τ * c * x * (c⁻¹ * τ * c)⁻¹ =
              c⁻¹ * (τ * (c * x * c⁻¹) * τ⁻¹) * c by group]
            rw [← hx'eq]
            group
          rw [hkey]
          exact hx'
        · exact le_of_eq (excl72_card_map_conj U (c⁻¹ * τ * c)).symm
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap
    · show c * (c⁻¹ * τ * c) * c⁻¹ = τ
      group
  set K : Subgroup C := N.normalCore with hKdef
  have hKN : K.Normal := Subgroup.normalCore_normal N
  have hKle : K ≤ N := Subgroup.normalCore_le N
  -- `U ≤ K` (commutator argument)
  have hUK : U ≤ K := by
    obtain ⟨u, hu, hu1⟩ : ∃ u ∈ U, u ≠ 1 := by
      by_contra hcon
      have hcon' : ∀ x ∈ U, x = 1 := fun x hx => by
        by_contra hx1
        exact hcon ⟨x, hx, hx1⟩
      have hbot : U = ⊥ := by
        ext x
        constructor
        · intro hx
          exact hcon' x hx
        · intro hx
          rw [Subgroup.mem_bot] at hx
          rw [hx]
          exact U.one_mem
      rw [hbot, Subgroup.card_bot] at hU3
      omega
    have hwU : τ * u * τ⁻¹ * u⁻¹ ∈ U :=
      U.mul_mem ((Subgroup.mem_normalizer_iff.mp hτN u).mp hu) (U.inv_mem hu)
    have hwK : τ * u * τ⁻¹ * u⁻¹ ∈ K := by
      have h1 : u * τ⁻¹ * u⁻¹ ∈ K := hKN.conj_mem τ⁻¹ (K.inv_mem hτcore) u
      have h2 : τ * (u * τ⁻¹ * u⁻¹) ∈ K := K.mul_mem hτcore h1
      rwa [show τ * (u * τ⁻¹ * u⁻¹) = τ * u * τ⁻¹ * u⁻¹ by group] at h2
    have hw1 : τ * u * τ⁻¹ * u⁻¹ ≠ 1 := by
      intro hzero
      have hτu : τ * u * τ⁻¹ = u := by
        have hh := congrArg (fun z : C => z * u) hzero
        simpa [mul_assoc] using hh
      have hcomm : Commute u τ := by
        rw [Commute]
        calc u * τ = (τ * u * τ⁻¹) * τ := by rw [hτu]
          _ = τ * u := by group
      have hcen : τ ∈ Subgroup.centralizer (U : Set C) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hgen : Subgroup.zpowers u = U := excl72_zpowers_eq_of_card_three hU3 hu hu1
        have hy' : y ∈ Subgroup.zpowers u := by
          rw [hgen]
          exact hy
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy'
        rw [← hk]
        exact (hcomm.zpow_left k).eq
      exact hτC hcen
    have hw : τ * u * τ⁻¹ * u⁻¹ ∈ U ⊓ K := ⟨hwU, hwK⟩
    have hcard3 : Nat.card ↥(U ⊓ K) = 3 := by
      have hdvd : Nat.card ↥(U ⊓ K) ∣ 3 := by
        rw [← hU3]
        exact Subgroup.card_dvd_of_le inf_le_left
      have hne1 : Nat.card ↥(U ⊓ K) ≠ 1 := by
        intro hone
        have hbot : U ⊓ K = ⊥ := (Subgroup.eq_bot_iff_card (U ⊓ K)).mpr hone
        rw [hbot, Subgroup.mem_bot] at hw
        exact hw1 hw
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd h hne1
      · exact h
    have hEq : U ⊓ K = U := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard3, hU3])
    rw [← hEq]
    exact inf_le_right
  have hτK : τ ∈ K := hτcore
  have hKdvd : Nat.card ↥K ∣ 18 := by
    rw [← hN18]
    exact Subgroup.card_dvd_of_le hKle
  have h6dvd : 6 ∣ Nat.card ↥K := by
    have h3 : 3 ∣ Nat.card ↥K := by
      rw [← hU3]
      exact Subgroup.card_dvd_of_le hUK
    have h2 : 2 ∣ Nat.card ↥K := by
      rw [← hτ2, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hτK)
    have h := Nat.Coprime.mul_dvd_of_dvd_of_dvd (show Nat.Coprime 2 3 by norm_num) h2 h3
    simpa using h
  -- `U` is not normal in `C`, so there is another conjugate
  have hUnotNormal : ¬ U.Normal := by
    intro hUn
    have hNtop : N = ⊤ := Subgroup.normalizer_eq_top_iff.mpr hUn
    have hle : S ≤ S ⊓ N := fun x hx => ⟨hx, by rw [hNtop]; trivial⟩
    have h8 : 8 ≤ Nat.card ↥(S ⊓ N) := by
      rw [← hS8]
      exact Subgroup.card_le_of_le hle
    omega
  obtain ⟨c, hc⟩ : ∃ c : C, U.map (MulAut.conj c).toMonoidHom ≠ U := by
    by_contra hcon
    push_neg at hcon
    exact hUnotNormal ⟨fun n hn g => by
      rw [← hcon g]
      exact Subgroup.mem_map.mpr ⟨n, hn, excl72_conj_apply g n⟩⟩
  set ω₂ : Subgroup C := U.map (MulAut.conj c).toMonoidHom with hω2def
  have hω2ne : ω₂ ≠ U := hc
  have hω2card : Nat.card ↥ω₂ = 3 := by
    rw [hω2def, excl72_card_map_conj, hU3]
  have hω2leK : ω₂ ≤ K := by
    rw [hω2def]
    intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [excl72_conj_apply]
    exact hKN.conj_mem x (hUK hx) c
  have hUU2 : U ⊓ ω₂ = ⊥ := by
    rw [Subgroup.eq_bot_iff_card]
    have hdvd : Nat.card ↥(U ⊓ ω₂) ∣ 3 := by
      rw [← hU3]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact h
    · exfalso
      have hEq : U ⊓ ω₂ = U := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hU3])
      have hle : U ≤ ω₂ := by
        rw [← hEq]
        exact inf_le_right
      exact hω2ne ((Subgroup.eq_of_le_of_card_ge hle (by rw [hω2card, hU3])).symm)
  have hRcard : Nat.card ↥(U ⊔ ω₂) = 9 := by
    have hn : ω₂ ≤ Subgroup.normalizer (U : Set C) := by
      rw [← hNdef]
      exact le_trans hω2leK hKle
    have hd : Disjoint U ω₂ := disjoint_iff.mpr hUU2
    rw [Work.A7REC.Join.card_sup_of_le_normalizer_of_disjoint hn hd, hU3, hω2card]
  -- `|K| = 18`
  have hKge9 : 9 ≤ Nat.card ↥K := by
    have h := card_mul_card_le_card_of_inf_eq_bot hUK hω2leK hUU2
    rw [hU3, hω2card] at h
    omega
  have hKcard : Nat.card ↥K = 18 := by
    obtain ⟨m, hm⟩ := h6dvd
    have hm3 : m ∣ 3 := by
      obtain ⟨t, ht⟩ := hKdvd
      refine ⟨t, ?_⟩
      have h18 : (18 : ℕ) = 6 * (m * t) := by
        rw [ht, hm]
        ring
      have h' := Nat.eq_of_mul_eq_mul_left (show 0 < 6 by norm_num)
        (show 6 * 3 = 6 * (m * t) by rw [← h18])
      exact h'
    rcases (Nat.dvd_prime Nat.prime_three).mp hm3 with h1 | h3
    · rw [hm, h1, mul_one] at hKge9
      omega
    · rw [hm, h3]
  -- every conjugate of `U` lies in `U ⊔ ω₂`
  have hΩsub : ∀ W ∈ Ω, W ≤ U ⊔ ω₂ ∧ Nat.card W = 3 := by
    intro W hW
    rw [hΩdef] at hW
    obtain ⟨d, rfl⟩ := hW
    constructor
    · by_contra hnot
      have hWleK : U.map (MulAut.conj d).toMonoidHom ≤ K := by
        intro y hy
        rw [Subgroup.mem_map] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        rw [excl72_conj_apply]
        exact hKN.conj_mem x (hUK hx) d
      have hRleK : U ⊔ ω₂ ≤ K := sup_le hUK hω2leK
      have hinf : U.map (MulAut.conj d).toMonoidHom ⊓ (U ⊔ ω₂) = ⊥ := by
        rw [Subgroup.eq_bot_iff_card]
        have hdvd : Nat.card ↥(U.map (MulAut.conj d).toMonoidHom ⊓ (U ⊔ ω₂)) ∣ 3 := by
          rw [← hU3, ← excl72_card_map_conj U d]
          exact Subgroup.card_dvd_of_le inf_le_left
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
        · exact h
        · exfalso
          have hEq : U.map (MulAut.conj d).toMonoidHom ⊓ (U ⊔ ω₂) =
              U.map (MulAut.conj d).toMonoidHom :=
            Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [excl72_card_map_conj U d, hU3, h])
          have hle : U.map (MulAut.conj d).toMonoidHom ≤ U ⊔ ω₂ := by
            rw [← hEq]
            exact inf_le_right
          exact hnot hle
      have h := card_mul_card_le_card_of_inf_eq_bot hWleK hRleK hinf
      rw [excl72_card_map_conj U d, hU3, hRcard, hKcard] at h
      omega
    · rw [excl72_card_map_conj U d, hU3]
  -- final contradiction with `NoNine`
  obtain ⟨p, hpR, hp1, hpfresh⟩ := hNoNine (U ⊔ ω₂) hRcard
  obtain ⟨W, hWΩ, hpW⟩ := exists_mem_of_ncard_four hRcard hΩsub hΩcard p hpR hp1
  rw [hΩdef] at hWΩ
  obtain ⟨d, hd⟩ := hWΩ
  rw [← hd] at hpW
  obtain ⟨u, hu, hueq⟩ := Subgroup.mem_map.mp hpW
  rw [excl72_conj_apply] at hueq
  exact hpfresh d u hu hueq

/-- **`A7Excl72Prop`**: no subgroup `H` of order `72` contains the Suzuki configuration, given
that no subgroup of order `9` has all of its nonidentity elements conjugate into `U`. -/
theorem a7Excl72 : Work.A7REC.A7Excl72Prop := by
  intro G _ _ U S' H τ hconf hNoNine hUH hS'H h72
  obtain ⟨hU3, hS8, hτS, hτ2, hτcen, hτN, hdisj⟩ := hconf
  have hτH : τ ∈ H := hS'H hτS
  set τ₀ : ↥H := ⟨τ, hτH⟩ with hτ0def
  have hC' : Nat.card ↥H = 72 := h72
  have hU3' : Nat.card ↥(U.subgroupOf H) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUH).toEquiv]
    exact hU3
  have hS8' : Nat.card ↥(S'.subgroupOf H) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS'H).toEquiv]
    exact hS8
  have hτS' : τ₀ ∈ S'.subgroupOf H := hτS
  have hτ2' : orderOf τ₀ = 2 := by
    rw [← Subgroup.orderOf_coe τ₀]
    exact hτ2
  have hτcen' : ∀ x ∈ S'.subgroupOf H, x * τ₀ = τ₀ * x := by
    intro x hx
    apply Subtype.ext
    exact hτcen (x : G) hx
  have hτN'' : τ₀ ∈ Subgroup.normalizer (↑(U.subgroupOf H) : Set ↥H) := by
    have hτNG : τ ∈ Subgroup.normalizer (U : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hτN
    have hmem : τ₀ ∈ (Subgroup.normalizer (U : Set G)).subgroupOf H := hτNG
    rwa [Subgroup.subgroupOf_normalizer_eq hUH] at hmem
  have hdisj' : S'.subgroupOf H ⊓ Subgroup.centralizer (↑(U.subgroupOf H) : Set ↥H) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxS, hxC⟩ := hx
    have hxc : ∀ u ∈ U, u * (x : G) = (x : G) * u := by
      intro u hu
      have humem : (⟨u, hUH hu⟩ : ↥H) ∈ U.subgroupOf H := hu
      exact congrArg (fun y : ↥H => (y : G))
        ((Subgroup.mem_centralizer_iff.mp hxC) ⟨u, hUH hu⟩ humem)
    have hmem : (x : G) ∈ S' ⊓ Subgroup.centralizer (U : Set G) :=
      ⟨hxS, Subgroup.mem_centralizer_iff.mpr hxc⟩
    rw [hdisj, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  exact excl72_aux hC' hU3' hS8' hτS' hτ2' hτcen' hτN'' hdisj'
    (noNine_subgroupOf hUH hNoNine)

end Work.A7REC.Char
