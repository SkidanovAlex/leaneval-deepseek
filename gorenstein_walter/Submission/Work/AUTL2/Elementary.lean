/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# AREA AUTL2 : elementary 2-group lemmas

* `Work.AUTL2.card_le_four_of_sq_eq_one_dihedral`: a subgroup of `DihedralGroup n` all of whose
  elements are involutions has at most 4 elements (the 2-rank of a dihedral group is `≤ 2`);
* `Work.AUTL2.not_elementaryAbelian_card_eight_of_dihOrCyc`: a group with cyclic or dihedral
  Sylow 2-subgroups has no elementary abelian subgroup of order 8;
* `Work.AUTL2.involution_outside_index_two`: a cyclic-or-dihedral group `S` with an index-2
  subgroup `T ≅ DihedralGroup n` (`n ≥ 2`) has an involution outside `T`.
-/
import Mathlib

namespace Work.AUTL2

/-- The rotations are exactly the powers of `r 1`. -/
lemma dihedral_r_mem_zpowers (n : ℕ) [NeZero n] (j : ZMod n) :
    DihedralGroup.r j ∈ Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup n) := by
  exact Subgroup.mem_zpowers_iff.mpr ⟨(j.val : ℤ), by rw [DihedralGroup.r_zpow]; simp⟩

/-- Reflexions are not rotations. -/
lemma dihedral_sr_not_mem_zpowers (n : ℕ) (i : ZMod n) :
    DihedralGroup.sr i ∉ Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup n) := by
  intro hi
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hi
  have h1 : DihedralGroup.r (k : ZMod n) = DihedralGroup.sr i := by
    rw [← hk, DihedralGroup.r_zpow]
    simp
  have h2 := congrArg (DihedralGroup.equivSum (n := n)) h1
  exact absurd h2 (by simp [DihedralGroup.equivSum])

/-- Every element of a dihedral group is a rotation or a reflexion. -/
lemma dihedral_eq_r_or_sr (n : ℕ) (x : DihedralGroup n) :
    (∃ j : ZMod n, x = DihedralGroup.r j) ∨ ∃ i : ZMod n, x = DihedralGroup.sr i := by
  cases x with
  | r j => exact Or.inl ⟨j, rfl⟩
  | sr i => exact Or.inr ⟨i, rfl⟩

/-- The rotation subgroup is cyclic. -/
lemma isCyclic_zpowers_r (n : ℕ) :
    IsCyclic (Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup n)) := by
  refine isCyclic_iff_exists_zpowers_eq_top.mpr
    ⟨⟨DihedralGroup.r 1, Subgroup.mem_zpowers _⟩, ?_⟩
  rw [Subgroup.eq_top_iff']
  rintro ⟨y, hy⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

/-- An element of a dihedral group which is not a rotation is a reflexion. -/
lemma dihedral_eq_sr_of_notMem (n : ℕ) [NeZero n] (x : DihedralGroup n)
    (hx : x ∉ Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup n)) :
    ∃ i : ZMod n, x = DihedralGroup.sr i := by
  rcases dihedral_eq_r_or_sr n x with ⟨j, hj⟩ | h
  · exact absurd (hj ▸ dihedral_r_mem_zpowers n j) hx
  · exact h

/-- A subgroup of `DihedralGroup n` consisting of involutions only has at most 4 elements.
(The 2-rank of a dihedral group is at most 2.) -/
lemma card_le_four_of_sq_eq_one_dihedral (n : ℕ) [NeZero n] (E : Subgroup (DihedralGroup n))
    (hE : ∀ x ∈ E, x ^ 2 = 1) : Nat.card E ≤ 4 := by
  classical
  set R : Subgroup (DihedralGroup n) := Subgroup.zpowers (DihedralGroup.r 1) with hRdef
  have hcycR : IsCyclic R := by rw [hRdef]; exact isCyclic_zpowers_r n
  have hI2 : Nat.card ↥(E ⊓ R) ≤ 2 := by
    haveI := hcycR
    haveI : IsCyclic ↥(E ⊓ R) := Subgroup.isCyclic_of_le inf_le_right
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(E ⊓ R))
    have hord : orderOf g = Nat.card ↥(E ⊓ R) := orderOf_eq_card_of_forall_mem_zpowers hg
    have hg2 : g ^ 2 = 1 := Subtype.ext (hE g.1 g.2.1)
    have hdvd : orderOf g ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hg2
    rw [hord] at hdvd
    exact Nat.le_of_dvd (by norm_num) hdvd
  by_cases hrefl : ∃ i : ZMod n, DihedralGroup.sr i ∈ E
  · obtain ⟨i, hi⟩ := hrefl
    have hmem : ∀ x : ↥E, (x : DihedralGroup n) ∉ R → DihedralGroup.sr i * x ∈ R := by
      intro x hx
      obtain ⟨i', hi'⟩ := dihedral_eq_sr_of_notMem n (x : DihedralGroup n) hx
      rw [hi', DihedralGroup.sr_mul_sr]
      exact dihedral_r_mem_zpowers n _
    let f : ↥E → ↥(E ⊓ R) × Fin 2 := fun x =>
      if h : (x : DihedralGroup n) ∈ R then (⟨x.1, ⟨x.2, h⟩⟩, 0)
      else (⟨DihedralGroup.sr i * x, ⟨mul_mem hi x.2, hmem x h⟩⟩, 1)
    have hinj : Function.Injective f := by
      intro x y hxy
      by_cases hx : (x : DihedralGroup n) ∈ R <;> by_cases hy : (y : DihedralGroup n) ∈ R
      · simp only [f, dif_pos hx, dif_pos hy, Prod.mk.injEq] at hxy
        exact Subtype.ext (congrArg (fun z : ↥(E ⊓ R) => (z : DihedralGroup n)) hxy.1)
      · simp only [f, dif_pos hx, dif_neg hy, Prod.mk.injEq] at hxy
        exact absurd hxy.2 (by decide)
      · simp only [f, dif_neg hx, dif_pos hy, Prod.mk.injEq] at hxy
        exact absurd hxy.2 (by decide)
      · simp only [f, dif_neg hx, dif_neg hy, Prod.mk.injEq] at hxy
        exact Subtype.ext (mul_left_cancel
          (congrArg (fun z : ↥(E ⊓ R) => (z : DihedralGroup n)) hxy.1))
    haveI : Fintype ↥(E ⊓ R) := Fintype.ofFinite _
    haveI : Fintype (↥(E ⊓ R) × Fin 2) := inferInstance
    have hcard : Nat.card ↥E ≤ Nat.card (↥(E ⊓ R) × Fin 2) :=
      Nat.card_le_card_of_injective f hinj
    rw [Nat.card_prod, Nat.card_fin] at hcard
    linarith
  · push_neg at hrefl
    have hER : E ≤ R := by
      intro x hx
      rcases dihedral_eq_r_or_sr n x with ⟨j, hj⟩ | ⟨i, hi⟩
      · exact hj ▸ dihedral_r_mem_zpowers n j
      · exact absurd (hi ▸ hx) (hrefl i)
    haveI := hcycR
    haveI : IsCyclic ↥E := Subgroup.isCyclic_of_le hER
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥E)
    have hord : orderOf g = Nat.card ↥E := orderOf_eq_card_of_forall_mem_zpowers hg
    have hg2 : g ^ 2 = 1 := Subtype.ext (hE g.1 g.2)
    have hdvd : orderOf g ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hg2
    rw [hord] at hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega

/-- A group with cyclic or dihedral Sylow 2-subgroups has no elementary abelian subgroup of
order 8: its 2-rank is at most 2. -/
theorem not_elementaryAbelian_card_eight_of_dihOrCyc {P : Type*} [Group P] [Finite P]
    (hP : IsCyclic P ∨ ∃ n : ℕ, Nonempty (P ≃* DihedralGroup n)) :
    ¬ ∃ E : Subgroup P, Nat.card E = 8 ∧ ∀ x ∈ E, x ^ 2 = 1 := by
  rintro ⟨E, hcard, hE⟩
  rcases hP with hcyc | ⟨n, ⟨e⟩⟩
  · haveI := hcyc
    haveI : IsCyclic ↥E := Subgroup.isCyclic E
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥E)
    have hord : orderOf g = Nat.card ↥E := orderOf_eq_card_of_forall_mem_zpowers hg
    have hg2 : g ^ 2 = 1 := Subtype.ext (hE g.1 g.2)
    have hdvd : orderOf g ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hg2
    rw [hord, hcard] at hdvd
    omega
  · haveI : NeZero n := by
      refine ⟨fun h0 => ?_⟩
      haveI : Fintype P := Fintype.ofFinite P
      have h1 : Nat.card P = Nat.card (DihedralGroup n) := Nat.card_congr e.toEquiv
      rw [h0, DihedralGroup.nat_card] at h1
      have h2 : 0 < Nat.card P := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.card_pos_iff.mpr ⟨1⟩
      omega
    have hle : Nat.card (E.map e.toMonoidHom : Subgroup (DihedralGroup n)) ≤ 4 :=
      card_le_four_of_sq_eq_one_dihedral n _ fun x hx => by
        obtain ⟨y, hyE, rfl⟩ := hx
        rw [← map_pow, hE y hyE, map_one]
    rw [Subgroup.card_map_of_injective e.injective] at hle
    omega

/-- A cyclic-or-dihedral group `S` with an index-2 subgroup `T ≅ DihedralGroup n`, `n ≥ 2`,
has an involution outside `T`. -/
theorem involution_outside_index_two {S : Type*} [Group S] [Finite S] (T : Subgroup S) (n : ℕ)
    (hS : IsCyclic S ∨ ∃ m : ℕ, Nonempty (S ≃* DihedralGroup m)) (hn : 2 ≤ n)
    (hT : Nonempty (T ≃* DihedralGroup n)) (hidx : T.index = 2) :
    ∃ z : S, z ∉ T ∧ z * z = 1 := by
  classical
  rcases hS with hcyc | ⟨m, ⟨e⟩⟩
  · -- `S` cyclic: `T` is cyclic, but `T ≅ DihedralGroup n`, `n ≥ 2`, is not
    haveI := hcyc
    obtain ⟨eT⟩ := hT
    haveI : IsCyclic ↥T := Subgroup.isCyclic T
    have : IsCyclic (DihedralGroup n) :=
      isCyclic_of_surjective (eT : ↥T →* DihedralGroup n) eT.surjective
    rw [DihedralGroup.isCyclic_iff] at this
    omega
  · -- Work inside `DihedralGroup m`; `m ≠ 0` because `S` is finite.
    have hm : NeZero m := by
      refine ⟨fun h0 => ?_⟩
      haveI : Fintype S := Fintype.ofFinite S
      have h1 : Nat.card S = Nat.card (DihedralGroup m) := Nat.card_congr e.toEquiv
      rw [h0, DihedralGroup.nat_card] at h1
      have h2 : 0 < Nat.card S := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.card_pos_iff.mpr ⟨1⟩
      omega
    set T' : Subgroup (DihedralGroup m) := T.map e.toMonoidHom with hT'def
    have hidx' : T'.index = 2 := by
      have hrange : e.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr e.surjective
      rw [hT'def, Subgroup.index_map_of_injective (H := T) e.injective, hidx, hrange,
        Subgroup.index_top, mul_one]
    have hne_top : T' ≠ ⊤ := by
      intro h; rw [h, Subgroup.index_top] at hidx'; omega
    obtain ⟨eT⟩ := hT
    have hiso : Nonempty (T' ≃* DihedralGroup n) := by
      rw [hT'def]
      exact ⟨(e.subgroupMap T).symm.trans eT⟩
    have hnotcycT' : ¬ IsCyclic ↥T' := by
      intro hcyc'
      haveI := hcyc'
      obtain ⟨e'⟩ := hiso
      have : IsCyclic (DihedralGroup n) :=
        isCyclic_of_surjective (e' : ↥T' →* DihedralGroup n) e'.surjective
      rw [DihedralGroup.isCyclic_iff] at this
      omega
    -- `T'` contains a reflexion
    obtain ⟨i, hi⟩ : ∃ i : ZMod m, DihedralGroup.sr i ∈ T' := by
      by_contra h
      push_neg at h
      have hrot : T' ≤ Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup m) := by
        intro x hx
        rcases dihedral_eq_r_or_sr m x with ⟨j, hj⟩ | ⟨i', hi'⟩
        · exact hj ▸ dihedral_r_mem_zpowers m j
        · exact absurd (hi' ▸ hx) (h i')
      haveI : IsCyclic (Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup m)) :=
        isCyclic_zpowers_r m
      exact hnotcycT' (Subgroup.isCyclic_of_le hrot)
    -- `r 1 ∉ T'`, so `r 1 * sr i` is an involution outside `T'`
    have hr : DihedralGroup.r 1 ∉ T' := by
      intro hr
      apply hne_top
      refine top_le_iff.mp fun x _ => ?_
      rcases dihedral_eq_r_or_sr m x with ⟨j, hj⟩ | ⟨i', hi'⟩
      · rw [hj]
        have hpow : DihedralGroup.r j = (DihedralGroup.r 1 : DihedralGroup m) ^ j.val := by
          rw [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
        rw [hpow]
        exact Subgroup.pow_mem _ hr _
      · rw [hi', show DihedralGroup.sr i' = DihedralGroup.sr i *
            DihedralGroup.r (i' - i) from by
          rw [DihedralGroup.sr_mul_r]
          congr 1
          abel]
        refine mul_mem hi ?_
        have hpow : DihedralGroup.r (i' - i) =
            (DihedralGroup.r 1 : DihedralGroup m) ^ (i' - i).val := by
          rw [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
        rw [hpow]
        exact Subgroup.pow_mem _ hr _
    refine ⟨e.symm (DihedralGroup.r 1 * DihedralGroup.sr i), ?_, ?_⟩
    · intro hmem
      have h1 : DihedralGroup.r 1 * DihedralGroup.sr i ∈ T' := by
        have h := Subgroup.mem_map_of_mem e.toMonoidHom hmem
        rwa [show e.toMonoidHom (e.symm (DihedralGroup.r 1 * DihedralGroup.sr i)) =
          DihedralGroup.r 1 * DihedralGroup.sr i from e.apply_symm_apply _] at h
      refine hr ?_
      have h2 : DihedralGroup.r 1 = (DihedralGroup.r 1 * DihedralGroup.sr i) *
          (DihedralGroup.sr i)⁻¹ := by group
      rw [h2]
      exact mul_mem h1 (inv_mem hi)
    · rw [← map_mul]
      have hsq : (DihedralGroup.r 1 * DihedralGroup.sr i) *
          (DihedralGroup.r 1 * DihedralGroup.sr i) = 1 := by
        rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_sr]
        simp
      rw [hsq, map_one]

end Work.AUTL2
