import Mathlib

namespace Work.CORE4.A7FGB

/-!
# Centralizer of a Klein four group in `A₇` with a commuting 3-cycle

Auxiliary lemmas leading to `centralizer_le_sup`.
-/

variable {G : Type*}

/-- In a group, `a * b = b * a` once `a ^ 2 = b ^ 2 = (a * b) ^ 2 = 1`. -/
lemma mul_comm_of_sq_eq_one [Group G] {a b : G}
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : (a * b) ^ 2 = 1) : a * b = b * a := by
  have ha' : a * a = 1 := by simpa [pow_two] using ha
  have hb' : b * b = 1 := by simpa [pow_two] using hb
  have hab' : (a * b) * (a * b) = 1 := by simpa [pow_two] using hab
  have h1 : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha'
  have h2 : b⁻¹ = b := inv_eq_of_mul_eq_one_left hb'
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_left hab').symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [h2, h1]

/-- A permutation commuting with `v` maps the support of `v` onto itself. -/
lemma map_support_eq_of_commute {g v : Equiv.Perm (Fin 7)} (h : g * v = v * g) :
    Finset.map g.toEmbedding v.support = v.support := by
  have h1 : g * v * g⁻¹ = v := by rw [h, mul_assoc, mul_inv_cancel, mul_one]
  have h2 := Equiv.Perm.support_conj (σ := g) (τ := v)
  rw [h1] at h2
  exact h2.symm

/-- If `v.support = S` and `g` commutes with `v`, then `g` preserves `S` setwise. -/
lemma mem_support_iff_commute {g v : Equiv.Perm (Fin 7)} (h : g * v = v * g)
    (S : Finset (Fin 7)) (hS : v.support = S) (p : Fin 7) :
    p ∈ S ↔ g p ∈ S := by
  have hmap : Finset.map g.toEmbedding S = S := by
    have := map_support_eq_of_commute h
    rwa [hS] at this
  have key : g p ∈ S ↔ p ∈ S := by
    constructor
    · intro hp
      rw [← hmap] at hp
      rw [Finset.mem_map] at hp
      obtain ⟨a, ha, hap⟩ := hp
      have ha' : a = p := g.injective hap
      rw [ha'] at ha
      exact ha
    · intro hp
      rw [← hmap]
      exact Finset.mem_map.mpr ⟨p, hp, rfl⟩
  exact key.symm

/-- The elements of `V` act transitively on the common support `S`, provided the nonidentity
elements of `V` all have support exactly `S`. -/
lemma exists_apply_eq_of_support_eq (V : Subgroup (alternatingGroup (Fin 7)))
    (S : Finset (Fin 7)) (hVcard : Nat.card V = 4) (hV2 : ∀ v ∈ V, v ^ 2 = 1)
    (hScard : S.card = 4)
    (hsupp : ∀ v ∈ V, v ≠ 1 → (v : Equiv.Perm (Fin 7)).support = S)
    {a b : Fin 7} (ha : a ∈ S) (hb : b ∈ S) :
    ∃ v ∈ V, (v : Equiv.Perm (Fin 7)) a = b := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  have hmem : ∀ v : V, ((v : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) a ∈ S := by
    intro v
    by_cases hv : (v : alternatingGroup (Fin 7)) = 1
    · have hveq : ((v : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) = 1 := by
        rw [hv]; rfl
      rw [hveq]; simpa using ha
    · have hs := hsupp (v : alternatingGroup (Fin 7)) v.2 hv
      rw [← hs]
      exact Equiv.Perm.apply_mem_support.mpr (by rw [hs]; exact ha)
  let f : V → {p // p ∈ S} :=
    fun v => ⟨((v : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) a, hmem v⟩
  have hf_inj : Function.Injective f := by
    intro u v huv
    have huv' : ((u : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) a =
        ((v : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) a := by
      have := congrArg Subtype.val huv
      simpa [f] using this
    have hcoe2 : (((v⁻¹ * u : V) : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
        (((v : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)))⁻¹ *
          ((u : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) := by
      simp
    have hwa : (((v⁻¹ * u : V) : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) a = a := by
      rw [hcoe2, Equiv.Perm.mul_apply, huv']
      simp
    have hw1 : v⁻¹ * u = 1 := by
      by_contra hwne
      have hwne' : ((v⁻¹ * u : V) : alternatingGroup (Fin 7)) ≠ 1 := by
        rintro h
        exact hwne (Subtype.ext (by simpa using h))
      have hsuppw : (((v⁻¹ * u : V) : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).support = S :=
        hsupp ((v⁻¹ * u : V) : alternatingGroup (Fin 7)) (v⁻¹ * u).2 hwne'
      have : (((v⁻¹ * u : V) : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) a ≠ a := by
        have : a ∈ (((v⁻¹ * u : V) : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).support := by
          rw [hsuppw]; exact ha
        rwa [Equiv.Perm.mem_support] at this
      exact this hwa
    have hu : u = v := by
      calc u = v * (v⁻¹ * u) := by group
        _ = v * 1 := by rw [hw1]
        _ = v := mul_one v
    exact hu
  have hcardV : Fintype.card V = 4 := by rw [← Nat.card_eq_fintype_card]; exact hVcard
  have hcardS : Fintype.card {p // p ∈ S} = 4 := by
    rw [Fintype.card_coe, hScard]
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf_inj, by rw [hcardV, hcardS]⟩
  obtain ⟨v, hv⟩ := hbij.2 ⟨b, hb⟩
  refine ⟨v, v.2, ?_⟩
  have := congrArg Subtype.val hv
  simpa [f] using this

/-- An even permutation whose support is contained in the support of a 3-cycle `x` is a power
of `x`. -/
lemma mem_zpowers_of_support_subset (x c : alternatingGroup (Fin 7)) (hx : orderOf x = 3)
    (hxcard : (x : Equiv.Perm (Fin 7)).support.card = 3)
    (hc : (c : Equiv.Perm (Fin 7)).support ⊆ (x : Equiv.Perm (Fin 7)).support) :
    c ∈ Subgroup.zpowers x := by
  set T : Finset (Fin 7) := (x : Equiv.Perm (Fin 7)).support with hT
  have hTcard : T.card = 3 := by rw [hT]; exact hxcard
  haveI : Nontrivial T := by
    rw [← Fintype.one_lt_card_iff_nontrivial, Fintype.card_coe]
    omega
  have hcardAG : Nat.card (alternatingGroup T) = 3 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_coe, hTcard]
    norm_num
  have hxmem : x ∈ (alternatingGroup.ofSubtype T).range :=
    (alternatingGroup.mem_range_ofSubtype_iff T x).mpr (fun a haa => by
      rw [hT]; exact haa)
  have hcmem : c ∈ (alternatingGroup.ofSubtype T).range :=
    (alternatingGroup.mem_range_ofSubtype_iff T c).mpr (fun a haa => by
      rw [hT]; exact hc haa)
  have hcardrange : Nat.card ((alternatingGroup.ofSubtype T).range) = 3 := by
    have h := Subgroup.card_map_of_injective (K := ⊤)
      (f := alternatingGroup.ofSubtype T) alternatingGroup.ofSubtype_injective
    rw [Subgroup.map_top, Subgroup.card_top, hcardAG] at h
    exact h
  have hle : Subgroup.zpowers x ≤ (alternatingGroup.ofSubtype T).range :=
    Subgroup.zpowers_le.mpr hxmem
  have heq : Subgroup.zpowers x = (alternatingGroup.ofSubtype T).range :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcardrange, Nat.card_zpowers, hx])
  rw [heq]
  exact hcmem

theorem centralizer_le_sup (V : Subgroup (alternatingGroup (Fin 7))) (x : alternatingGroup (Fin 7))
    (hVcard : Nat.card V = 4) (hV2 : ∀ v ∈ V, v ^ 2 = 1)
    (hx : orderOf x = 3) (hxcard : (x : Equiv.Perm (Fin 7)).support.card = 3)
    (hcomm : ∀ v ∈ V, v * x = x * v)
    (hsupp : ∀ v ∈ V, v ≠ 1 → (v : Equiv.Perm (Fin 7)).support = Finset.univ \ (x : Equiv.Perm (Fin 7)).support) :
    Subgroup.centralizer (V : Set (alternatingGroup (Fin 7))) ≤ V ⊔ Subgroup.zpowers x := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff] at hg
  set S : Finset (Fin 7) := Finset.univ \ (x : Equiv.Perm (Fin 7)).support with hS
  have hScard : S.card = 4 := by
    rw [hS, Finset.card_sdiff, Finset.inter_univ]
    simp [hxcard]
  have hVne : V ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hVcard
    exact absurd hVcard (by norm_num)
  obtain ⟨v0, hv0ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hVne
  have hv0ne' : (v0 : alternatingGroup (Fin 7)) ≠ 1 := by
    rintro h
    exact hv0ne (Subtype.ext (by simpa using h))
  have hv0V : (v0 : alternatingGroup (Fin 7)) ∈ V := v0.2
  have hv0supp : ((v0 : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).support = S :=
    hsupp (v0 : alternatingGroup (Fin 7)) hv0V hv0ne'
  have hcomm0 : ((g : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) *
        ((v0 : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))
      = ((v0 : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) *
        ((g : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) := by
    have h := congrArg (fun z : alternatingGroup (Fin 7) => (z : Equiv.Perm (Fin 7)))
      (hg (v0 : alternatingGroup (Fin 7)) hv0V)
    simpa using h.symm
  have hpres : ∀ p, p ∈ S ↔ ((g : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) p ∈ S :=
    fun p => mem_support_iff_commute hcomm0 S hv0supp p
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  obtain ⟨w, hwV, hwa⟩ :=
    exists_apply_eq_of_support_eq V S hVcard hV2 hScard hsupp ha ((hpres a).mp ha)
  have hagree : ∀ p ∈ S, ((g : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) p =
      ((w : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) p := by
    intro p hp
    obtain ⟨u, huV, hua⟩ :=
      exists_apply_eq_of_support_eq V S hVcard hV2 hScard hsupp ha hp
    have hgu : ((u : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) *
          ((g : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))
        = ((g : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) *
          ((u : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) := by
      have h := congrArg (fun z : alternatingGroup (Fin 7) => (z : Equiv.Perm (Fin 7)))
        (hg (u : alternatingGroup (Fin 7)) huV)
      simpa using h
    have hu2 : ((u : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) ^ 2 = 1 := by
      have h := congrArg (fun z : alternatingGroup (Fin 7) => (z : Equiv.Perm (Fin 7)))
        (hV2 (u : alternatingGroup (Fin 7)) huV)
      simpa using h
    have hw2 : ((w : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) ^ 2 = 1 := by
      have h := congrArg (fun z : alternatingGroup (Fin 7) => (z : Equiv.Perm (Fin 7)))
        (hV2 (w : alternatingGroup (Fin 7)) hwV)
      simpa using h
    have huwV : (u : alternatingGroup (Fin 7)) * (w : alternatingGroup (Fin 7)) ∈ V :=
      V.mul_mem huV hwV
    have huw2 : ((u : alternatingGroup (Fin 7)) * (w : alternatingGroup (Fin 7))) ^ 2 = 1 :=
      hV2 ((u : alternatingGroup (Fin 7)) * (w : alternatingGroup (Fin 7))) huwV
    have huw2' : (((u : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) *
        ((w : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))) ^ 2 = 1 := by
      have h := congrArg (fun z : alternatingGroup (Fin 7) => (z : Equiv.Perm (Fin 7))) huw2
      simpa using h
    have huw : ((u : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) *
          ((w : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))
        = ((w : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) *
          ((u : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) :=
      mul_comm_of_sq_eq_one hu2 hw2 huw2'
    calc ((g : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) p
        = ((g : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))
            (((u : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) a) := by rw [← hua]
      _ = (((g : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) *
            ((u : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))) a := by
            rw [Equiv.Perm.mul_apply]
      _ = (((u : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) *
            ((g : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))) a := by rw [hgu]
      _ = ((u : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))
            (((g : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) a) := by
            rw [Equiv.Perm.mul_apply]
      _ = ((u : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))
            (((w : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) a) := by rw [hwa]
      _ = (((u : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) *
            ((w : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))) a := by
            rw [Equiv.Perm.mul_apply]
      _ = (((w : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) *
            ((u : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))) a := by rw [huw]
      _ = ((w : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))
            (((u : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) a) := by
            rw [Equiv.Perm.mul_apply]
      _ = ((w : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) p := by rw [hua]
  set hh : alternatingGroup (Fin 7) := g * (w : alternatingGroup (Fin 7))⁻¹ with hhh
  have hfix : ∀ p ∈ S, ((hh : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) p = p := by
    intro p hp
    have hcoeh : ((hh : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
        ((g : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) *
          (((w : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)))⁻¹ := by
      rw [hhh]; simp
    rw [hcoeh, Equiv.Perm.mul_apply]
    have hws : (((w : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))).support ≤ S := by
      by_cases hw1 : (w : alternatingGroup (Fin 7)) = 1
      · rw [hw1]; simp
      · rw [hsupp (w : alternatingGroup (Fin 7)) hwV hw1]
    have hws' : ((((w : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)))⁻¹).support ≤ S := by
      rwa [Equiv.Perm.support_inv]
    have hq : ((((w : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)))⁻¹) p ∈ S :=
      (Equiv.Perm.isInvariant_of_support_le hws' p).2 hp
    rw [hagree _ hq]
    simp
  have hh_supp_le : ((hh : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).support ⊆
      (x : Equiv.Perm (Fin 7)).support := by
    intro p hp
    by_contra hpx
    have hpS : p ∈ S := by
      rw [hS, Finset.mem_sdiff]
      exact ⟨Finset.mem_univ p, hpx⟩
    have hfixp : ((hh : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) p = p := hfix p hpS
    rw [Equiv.Perm.mem_support] at hp
    exact hp hfixp
  have hzpow : hh ∈ Subgroup.zpowers x :=
    mem_zpowers_of_support_subset x hh hx hxcard hh_supp_le
  have hh_mem : hh ∈ V ⊔ Subgroup.zpowers x := Subgroup.mem_sup_right hzpow
  have hw_mem : (w : alternatingGroup (Fin 7)) ∈ V ⊔ Subgroup.zpowers x :=
    Subgroup.mem_sup_left hwV
  have hg_eq : g = hh * (w : alternatingGroup (Fin 7)) := by
    rw [hhh]; group
  rw [hg_eq]
  exact mul_mem hh_mem hw_mem

end Work.CORE4.A7FGB
