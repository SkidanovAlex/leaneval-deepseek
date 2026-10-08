/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# AREA AUTL2 / A5 : elementary group-theoretic tools

* `exists_sq_mem_of_even_index` : a subgroup of even index in a finite group has an element
  outside it whose square lies inside it;
* `exists_involution_outside_of_ne_of_not_cyclic` : in a finite cyclic-or-dihedral group `G`, a
  proper non-cyclic subgroup `T` of a subgroup `S ≤ G` does not contain all involutions of `S`.
-/
import Mathlib
import Submission.Work.AUTL2.Elementary

set_option linter.style.haveILetI false

namespace Work.AUTL2.A5

open Work.AUTL2

/-- In a finite group, a subgroup of even index has an element outside it whose square is in it. -/
theorem exists_sq_mem_of_even_index {G : Type*} [Group G] [Finite G] (K : Subgroup G)
    (h : Even K.index) : ∃ g : G, g ∉ K ∧ g ^ 2 ∈ K := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ K.index := even_iff_two_dvd.mp h
  obtain ⟨P⟩ := IsPGroup.of_bot.exists_le_sylow (p := 2) (G := G)
  have hPidx : ¬ 2 ∣ P.index := Sylow.not_dvd_index P
  have hPnotK : ¬ (P : Subgroup G) ≤ K := by
    intro hle
    exact hPidx (dvd_trans h2 (Subgroup.index_dvd_of_le hle))
  obtain ⟨y, hyP, hyK⟩ := Set.not_subset.mp hPnotK
  have hex : ∃ n : ℕ, y ^ (2 ^ n) ∈ K := by
    obtain ⟨n, hn⟩ := P.isPGroup' ⟨y, hyP⟩
    exact ⟨n, by
      have h := congrArg (Subtype.val) hn
      rw [Subgroup.coe_pow, Subgroup.coe_one] at h
      rw [h]
      exact K.one_mem⟩
  set j := Nat.find hex with hjdef
  have hj : y ^ (2 ^ j) ∈ K := Nat.find_spec hex
  have hjpos : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · rw [h0] at hj
      simp at hj
      exact absurd hj hyK
    · exact h0
  have h2j : 2 ^ (j - 1) * 2 = 2 ^ j := by
    rw [mul_comm, ← pow_succ', show j - 1 + 1 = j from by omega]
  refine ⟨y ^ (2 ^ (j - 1)), ?_, ?_⟩
  · intro hc
    exact Nat.find_min hex (by omega) hc
  · rw [← pow_mul, h2j]
    exact hj

/-- In a finite cyclic-or-dihedral group `G`, if `T ≤ S ≤ G`, `T` is not cyclic and `T ≠ S`,
then `S` contains an involution outside `T`. -/
theorem exists_involution_outside_of_ne_of_not_cyclic {G : Type*} [Group G] [Finite G]
    (T S : Subgroup G)
    (hG : IsCyclic G ∨ ∃ m : ℕ, Nonempty (G ≃* DihedralGroup m))
    (hTS : T ≤ S) (hT : ¬ IsCyclic ↥T) (hne : T ≠ S) :
    ∃ z ∈ S, z ∉ T ∧ z * z = 1 := by
  rcases hG with hcyc | ⟨m, ⟨e⟩⟩
  · haveI := hcyc
    haveI : IsCyclic ↥S := Subgroup.isCyclic_of_le le_top
    exact absurd (Subgroup.isCyclic_of_le hTS) hT
  · have hm : NeZero m := by
      refine ⟨fun h0 => ?_⟩
      haveI : Finite (DihedralGroup m) := Finite.of_equiv G e.toEquiv
      rw [h0] at this
      exact not_finite (DihedralGroup 0)
    have hmemS : ∀ x : G, e x ∈ S.map (e : G →* DihedralGroup m) ↔ x ∈ S := by
      intro x
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, hyx⟩
        rwa [e.injective hyx] at hy
      · intro hx; exact ⟨x, hx, rfl⟩
    have hmemT : ∀ x : G, e x ∈ T.map (e : G →* DihedralGroup m) ↔ x ∈ T := by
      intro x
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, hyx⟩
        rwa [e.injective hyx] at hy
      · intro hx; exact ⟨x, hx, rfl⟩
    have hT'S' : T.map (e : G →* DihedralGroup m) ≤ S.map (e : G →* DihedralGroup m) := by
      rintro y ⟨x, hx, rfl⟩
      exact ⟨x, hTS hx, rfl⟩
    have hT'ne : T.map (e : G →* DihedralGroup m) ≠ S.map (e : G →* DihedralGroup m) := by
      intro hEq
      apply hne
      ext x
      rw [← hmemT x, hEq, hmemS x]
    have hT'ncyc : ¬ IsCyclic ↥(T.map (e : G →* DihedralGroup m)) := by
      intro hc
      haveI := hc
      exact hT (isCyclic_of_surjective (e.subgroupMap T).symm
        (e.subgroupMap T).symm.surjective)
    have hreflT : ∃ i : ZMod m, DihedralGroup.sr i ∈ T.map (e : G →* DihedralGroup m) := by
      by_contra h
      push_neg at h
      have hrot : T.map (e : G →* DihedralGroup m) ≤
          Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup m) := by
        intro x hx
        rcases dihedral_eq_r_or_sr m x with ⟨j, hj⟩ | ⟨i, hi⟩
        · exact hj ▸ dihedral_r_mem_zpowers m j
        · exact absurd (hi ▸ hx) (h i)
      haveI : IsCyclic (Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup m)) :=
        isCyclic_zpowers_r m
      exact hT'ncyc (Subgroup.isCyclic_of_le hrot)
    obtain ⟨i0, hi0⟩ := hreflT
    have hzex : ∃ z ∈ S.map (e : G →* DihedralGroup m),
        z ∉ T.map (e : G →* DihedralGroup m) := by
      by_contra h
      push_neg at h
      exact hT'ne (le_antisymm hT'S' (fun z hz => h z hz))
    obtain ⟨z, hzS, hzT⟩ := hzex
    have key : ∃ z ∈ S.map (e : G →* DihedralGroup m),
        z ∉ T.map (e : G →* DihedralGroup m) ∧ z * z = 1 := by
      by_cases hi0T : DihedralGroup.sr i0 ∈ T.map (e : G →* DihedralGroup m)
      · by_cases hzr : ∃ i : ZMod m, z = DihedralGroup.sr i
        · obtain ⟨i, hi⟩ := hzr
          exact ⟨z, hzS, hzT, by
            rw [hi, DihedralGroup.sr_mul_sr, sub_self, DihedralGroup.r_zero]⟩
        · push_neg at hzr
          have hzrot : z ∈ Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup m) := by
            rcases dihedral_eq_r_or_sr m z with ⟨j, hj⟩ | ⟨i, hi⟩
            · exact hj ▸ dihedral_r_mem_zpowers m j
            · exact absurd hi (hzr i)
          obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzrot
          have hzk : z = DihedralGroup.r (k : ZMod m) := by
            rw [← hk, DihedralGroup.r_zpow]
            simp
          refine ⟨z * DihedralGroup.sr i0, Subgroup.mul_mem _ hzS (hT'S' hi0), ?_, ?_⟩
          · intro hmem
            apply hzT
            have h1 : (z * DihedralGroup.sr i0) * DihedralGroup.sr i0 ∈
                T.map (e : G →* DihedralGroup m) := Subgroup.mul_mem _ hmem hi0T
            rwa [mul_assoc, DihedralGroup.sr_mul_sr, sub_self, DihedralGroup.r_zero,
              mul_one] at h1
          · rw [hzk, DihedralGroup.r_mul_sr]
            rw [DihedralGroup.sr_mul_sr, sub_self, DihedralGroup.r_zero]
      · exact ⟨DihedralGroup.sr i0, hT'S' hi0, hi0T, by
          rw [DihedralGroup.sr_mul_sr, sub_self, DihedralGroup.r_zero]⟩
    obtain ⟨w, hwS, hwT, hw2⟩ := key
    refine ⟨e.symm w, ?_, ?_, ?_⟩
    · obtain ⟨x, hx, hxw⟩ := Subgroup.mem_map.mp hwS
      have hx' : e.symm w = x := by rw [← hxw]; exact e.symm_apply_apply x
      rwa [hx']
    · intro hmem
      apply hwT
      rw [show w = e (e.symm w) from (e.apply_symm_apply w).symm]
      exact Subgroup.mem_map.mpr ⟨e.symm w, hmem, rfl⟩
    · rw [← map_mul, hw2, map_one]

end Work.AUTL2.A5
