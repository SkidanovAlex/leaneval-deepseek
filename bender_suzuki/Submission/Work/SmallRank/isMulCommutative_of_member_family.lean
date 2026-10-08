import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.SmallRank

/-- The conjugation action of a group on its subgroup lattice (a local instance, not
exported, so that it does not interfere with other files). -/
noncomputable local instance subgroupConjAction {A : Type*} [Group A] :
    MulAction A (Subgroup A) where
  smul g H := H.map (MulAut.conj g).toMonoidHom
  one_smul H := by
    change H.map (MulAut.conj (1 : A)).toMonoidHom = H
    rw [map_one]; exact Subgroup.map_id H
  mul_smul g h H := by
    change H.map (MulAut.conj (g * h)).toMonoidHom
        = (H.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom
    rw [Subgroup.map_map]; congr 1; ext x; simp [MulAut.conj_apply, mul_assoc]

/-- Membership in a conjugate subgroup. -/
lemma mem_smul_subgroup {A : Type*} [Group A] (g : A) (H : Subgroup A) (x : A) :
    x ∈ g • H ↔ g⁻¹ * x * g ∈ H := by
  change x ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ H
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
    have : g⁻¹ * x * g = y := by rw [← hyx]; group
    rw [this]; exact hy
  · intro hx
    refine ⟨g⁻¹ * x * g, hx, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group

/-- The stabiliser of a subgroup under conjugation is its normaliser. -/
lemma stabilizer_eq_normalizer {A : Type*} [Group A] (H : Subgroup A) :
    MulAction.stabilizer A H = Subgroup.normalizer (H : Set A) := by
  ext g
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hg h
    constructor
    · intro hh
      have hmem : g * h * g⁻¹ ∈ g • H := by
        change g * h * g⁻¹ ∈ H.map (MulAut.conj g).toMonoidHom
        exact ⟨h, hh, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
      rwa [hg] at hmem
    · intro hh
      have hginv : g⁻¹ • H = H := by
        have : g⁻¹ • (g • H) = H := by
          rw [← mul_smul, inv_mul_cancel, one_smul]
        rwa [hg] at this
      have hmem : h ∈ g⁻¹ • H := by
        change h ∈ H.map (MulAut.conj g⁻¹).toMonoidHom
        refine ⟨g * h * g⁻¹, hh, ?_⟩
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
      rwa [hginv] at hmem
  · intro hg
    apply Subgroup.ext
    intro x
    change x ∈ H.map (MulAut.conj g).toMonoidHom ↔ x ∈ H
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
      rw [← hyx]; exact (hg y).mp hy
    · intro hx
      refine ⟨g⁻¹ * x * g, (hg (g⁻¹ * x * g)).mpr ?_, ?_⟩
      · rw [show g * (g⁻¹ * x * g) * g⁻¹ = x by group]; exact hx
      · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group

/-- Conjugate subgroups have the same cardinality. -/
lemma card_smul_subgroup {A : Type*} [Group A] (g : A) (H : Subgroup A) :
    Nat.card ↥(g • H) = Nat.card ↥H := by
  change Nat.card ↥(H.map (MulAut.conj g).toMonoidHom) = Nat.card ↥H
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

/-- The orbit of a self-normalising subgroup has cardinality its index. -/
lemma card_orbit_eq_index {A : Type*} [Group A] (H : Subgroup A)
    (hH : Subgroup.normalizer (H : Set A) = H) :
    Nat.card ↥(MulAction.orbit A H) = H.index := by
  rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer A H)]
  rw [← Subgroup.index_eq_card]
  congr 1
  exact (stabilizer_eq_normalizer H).trans hH

/-- Orbit-stabiliser for a self-normalising subgroup. -/
lemma card_orbit_mul_card {A : Type*} [Group A] (H : Subgroup A)
    (hH : Subgroup.normalizer (H : Set A) = H) :
    Nat.card ↥(MulAction.orbit A H) * Nat.card ↥H = Nat.card A := by
  rw [card_orbit_eq_index H hH, Nat.mul_comm, Subgroup.card_mul_index]

/-- Elementary arithmetic behind the counting lemma. -/
private lemma arith_le {N r q : ℕ} (h1 : N + q = r * q + 1) (h2 : 3 * N ≤ r * q)
    (hr : 2 ≤ r) (hq : 1 ≤ q) : False := by
  nlinarith [h1, h2, hr, hq]

/-- **Counting lemma.**  Let `A` be a finite group of odd order and `Z ≤ A` a central subgroup.
Suppose that to every `x ∉ Z` there is attached a subgroup `M x` such that

* `Z ≤ M x` and `x ∈ M x`,
* `M x` is abelian,
* any two of the subgroups `M x`, `M y` (`x, y ∉ Z`) are either equal or meet exactly in `Z`,
* each `M x` is its own normaliser in `A`,
* the assignment is compatible with conjugation: `(M x)^g = M (g x g⁻¹)` for `g : A`.

Then `A` is abelian. -/
theorem isMulCommutative_of_member_family {A : Type*} [Group A] [Finite A]
    (hodd : Odd (Nat.card A)) (Z : Subgroup A) (hZ : Z ≤ Subgroup.center A) (M : A → Subgroup A)
    (hZle : ∀ x : A, x ∉ Z → Z ≤ M x)
    (hself : ∀ x : A, x ∉ Z → x ∈ M x)
    (hab : ∀ x : A, x ∉ Z → IsMulCommutative (M x))
    (hint : ∀ x y : A, x ∉ Z → y ∉ Z → M x = M y ∨ M x ⊓ M y = Z)
    (hnorm : ∀ x : A, x ∉ Z → Subgroup.normalizer ((M x : Subgroup A) : Set A) = M x)
    (hconj : ∀ x : A, x ∉ Z → ∀ g : A,
      (M x).map (MulAut.conj g).toMonoidHom = M (g * x * g⁻¹)) :
    IsMulCommutative A := by
  classical
  have hZn : Z.Normal := Subgroup.normal_of_le_center hZ
  by_cases hcase : ∃ x, x ∉ Z ∧ M x = ⊤
  · obtain ⟨x, hx, hMx⟩ := hcase
    rw [isMulCommutative_iff]
    intro a b
    have ha : a ∈ M x := by rw [hMx]; trivial
    have hb : b ∈ M x := by rw [hMx]; trivial
    have hcomm := (isMulCommutative_iff.mp (hab x hx)) ⟨a, ha⟩ ⟨b, hb⟩
    exact Subtype.ext_iff.mp hcomm
  · push_neg at hcase
    by_cases hZtop : Z = ⊤
    · have hcen : Subgroup.center A = ⊤ := le_antisymm le_top (hZtop ▸ hZ)
      exact Subgroup.center_eq_top_iff.mp hcen
    · exfalso
      obtain ⟨x0, hx0⟩ : ∃ x, x ∉ Z := by
        by_contra h; push_neg at h
        exact hZtop ((Subgroup.eq_top_iff' Z).mpr h)
      haveI : Fintype A := Fintype.ofFinite A
      haveI : Fintype (Subgroup A) := Fintype.ofFinite (Subgroup A)
      set dom : Finset A := Finset.univ.filter (fun x => x ∉ Z) with hdom
      set Ωs : Finset (Subgroup A) := dom.image M with hΩs
      set orbQ : Subgroup A → Quotient (MulAction.orbitRel A (Subgroup A)) :=
        fun H => Quotient.mk'' H with horbQ
      set qs : Finset (Quotient (MulAction.orbitRel A (Subgroup A))) := Ωs.image orbQ with hqs
      set q : ℕ := Z.index with hq_def
      have mem_dom : ∀ x, x ∈ dom ↔ x ∉ Z := by
        intro x; rw [hdom]; simp
      have mem_Ωs : ∀ H, H ∈ Ωs ↔ ∃ x, x ∉ Z ∧ M x = H := by
        intro H; rw [hΩs, Finset.mem_image]
        constructor
        · rintro ⟨x, hx, rfl⟩; exact ⟨x, (mem_dom x).mp hx, rfl⟩
        · rintro ⟨x, hx, rfl⟩; exact ⟨x, (mem_dom x).mpr hx, rfl⟩
      have Ωs_Zle : ∀ H ∈ Ωs, Z ≤ H := by
        intro H hH; obtain ⟨x, hx, rfl⟩ := (mem_Ωs H).mp hH; exact hZle x hx
      have Ωs_ne_top : ∀ H ∈ Ωs, H ≠ ⊤ := by
        intro H hH; obtain ⟨x, hx, rfl⟩ := (mem_Ωs H).mp hH; exact hcase x hx
      have Ωs_normalizer : ∀ H ∈ Ωs, Subgroup.normalizer ((H : Subgroup A) : Set A) = H := by
        intro H hH; obtain ⟨x, hx, rfl⟩ := (mem_Ωs H).mp hH; exact hnorm x hx
      have block : ∀ x H, x ∉ Z → H ∈ Ωs → (M x = H ↔ x ∈ H) := by
        intro x H hx hH
        constructor
        · intro h; rw [← h]; exact hself x hx
        · intro hxH
          obtain ⟨y, hy, hyH⟩ := (mem_Ωs H).mp hH
          rcases hint x y hx hy with h | h
          · rw [h, hyH]
          · exfalso
            have hxMx : x ∈ M x := hself x hx
            have hxMy : x ∈ M y := by rw [hyH]; exact hxH
            have : x ∈ M x ⊓ M y := ⟨hxMx, hxMy⟩
            rw [h] at this
            exact hx this
      have invar : ∀ (g : A) H, H ∈ Ωs → g • H ∈ Ωs := by
        intro g H hH
        obtain ⟨y, hy, hyH⟩ := (mem_Ωs H).mp hH
        refine (mem_Ωs _).mpr ⟨g * y * g⁻¹, ?_, ?_⟩
        · intro hconj'
          have hmem : g⁻¹ * (g * y * g⁻¹) * (g⁻¹)⁻¹ ∈ Z := hZn.conj_mem (g * y * g⁻¹) hconj' g⁻¹
          rw [show g⁻¹ * (g * y * g⁻¹) * (g⁻¹)⁻¹ = y by group] at hmem
          exact hy hmem
        · rw [← hyH]
          show M (g * y * g⁻¹) = (M y).map (MulAut.conj g).toMonoidHom
          exact (hconj y hy g).symm
      have orbit_subset : ∀ H ∈ Ωs, MulAction.orbit A H ⊆ Ωs := by
        intro H hH H' hH'
        rw [MulAction.mem_orbit_iff] at hH'
        obtain ⟨g, hg⟩ := hH'
        rw [← hg]; exact invar g H hH
      have qout_mem : ∀ r ∈ qs, r.out ∈ Ωs := by
        intro r hr
        obtain ⟨H, hH, hrH⟩ := Finset.mem_image.mp hr
        have he : (Quotient.mk'' H : Quotient (MulAction.orbitRel A (Subgroup A))) = r := hrH
        have he2 : (Quotient.mk'' r.out : Quotient (MulAction.orbitRel A (Subgroup A))) = r :=
          Quotient.out_eq r
        have hrel : MulAction.orbitRel A (Subgroup A) H r.out := Quotient.exact (he.trans he2.symm)
        have hmem : H ∈ MulAction.orbit A r.out := MulAction.orbitRel_apply.mp hrel
        rw [MulAction.mem_orbit_iff] at hmem
        obtain ⟨g, hg⟩ := hmem
        apply orbit_subset H hH
        rw [MulAction.mem_orbit_iff]
        refine ⟨g⁻¹, ?_⟩
        rw [← hg, ← mul_smul, inv_mul_cancel, one_smul]
      have fiber_eq : ∀ r ∈ qs, Ωs.filter (fun H => orbQ H = r)
          = Finset.univ.filter (fun H : Subgroup A => H ∈ MulAction.orbit A r.out) := by
        intro r hr
        apply Finset.ext
        intro H
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨_, hHr⟩
          have he : (Quotient.mk'' H : Quotient (MulAction.orbitRel A (Subgroup A))) = r := hHr
          have he2 : (Quotient.mk'' r.out : Quotient (MulAction.orbitRel A (Subgroup A))) = r :=
            Quotient.out_eq r
          exact MulAction.orbitRel_apply.mp (Quotient.exact (he.trans he2.symm))
        · intro hHorbit
          refine ⟨orbit_subset r.out (qout_mem r hr) hHorbit, ?_⟩
          exact (Quotient.sound (MulAction.orbitRel_apply.mpr hHorbit)).trans (Quotient.out_eq r)
      have card_orbFinset : ∀ (H : Subgroup A),
          (Finset.univ.filter (fun K : Subgroup A => K ∈ MulAction.orbit A H)).card
            = Nat.card ↥(MulAction.orbit A H) := by
        intro H
        rw [← Fintype.card_subtype (fun K : Subgroup A => K ∈ MulAction.orbit A H)]
        rw [Nat.card_eq_fintype_card]
      have inner_sum : ∀ r ∈ qs, (Ωs.filter (fun H => orbQ H = r)).sum (fun H => Nat.card H)
          = Nat.card A := by
        intro r hr
        rw [fiber_eq r hr]
        have hpt : ∀ H ∈ Finset.univ.filter (fun H : Subgroup A => H ∈ MulAction.orbit A r.out),
            Nat.card H = Nat.card r.out := by
          intro H hH
          rw [Finset.mem_filter] at hH
          obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hH.2
          rw [← hg]; exact card_smul_subgroup g r.out
        rw [Finset.sum_congr rfl hpt, Finset.sum_const, nsmul_eq_mul, card_orbFinset r.out]
        exact card_orbit_mul_card r.out (Ωs_normalizer r.out (qout_mem r hr))
      have hmaps : ∀ H ∈ Ωs, orbQ H ∈ qs := by
        intro H hH; rw [hqs]; exact Finset.mem_image.mpr ⟨H, hH, rfl⟩
      have hsumH : (∑ H ∈ Ωs, Nat.card H) = qs.card * Nat.card A := by
        rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun H => Nat.card H)]
        rw [Finset.sum_congr rfl (fun r hr => inner_sum r hr), Finset.sum_const, nsmul_eq_mul,
          Nat.cast_id]
      have hcardZ : (Finset.univ.filter (fun x : A => x ∈ Z)).card = Nat.card Z := by
        rw [← Fintype.card_subtype (fun x : A => x ∈ Z)]
        rw [Nat.card_eq_fintype_card]
      have hcardH : ∀ H : Subgroup A,
          (Finset.univ.filter (fun x : A => x ∈ H)).card = Nat.card H := by
        intro H
        rw [← Fintype.card_subtype (fun x : A => x ∈ H)]
        rw [Nat.card_eq_fintype_card]
      have hZH : ∀ H ∈ Ωs, Nat.card Z ≤ Nat.card H := by
        intro H hH
        rw [← hcardZ, ← hcardH H]
        apply Finset.card_le_card
        intro x hx
        rw [Finset.mem_filter] at hx ⊢
        exact ⟨hx.1, Ωs_Zle H hH hx.2⟩
      have hZA : Nat.card Z ≤ Nat.card A :=
        Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card Z)
      have fiber_card : ∀ H ∈ Ωs,
          (dom.filter (fun x => M x = H)).card = Nat.card H - Nat.card Z := by
        intro H hH
        have hset : dom.filter (fun x => M x = H)
            = (Finset.univ.filter (fun x : A => x ∈ H))
                \ (Finset.univ.filter (fun x : A => x ∈ Z)) := by
          apply Finset.ext
          intro x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, mem_dom]
          constructor
          · rintro ⟨hxZ, hxM⟩
            exact ⟨(block x H hxZ hH).mp hxM, hxZ⟩
          · rintro ⟨hxH, hxZ⟩
            exact ⟨hxZ, (block x H hxZ hH).mpr hxH⟩
        rw [hset, Finset.card_sdiff_of_subset
          (fun x hx => by rw [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, Ωs_Zle H hH hx.2⟩),
          hcardH, hcardZ]
      have hmaps2 : Set.MapsTo M (↑dom : Set A) (↑Ωs : Set (Subgroup A)) := by
        intro x hx
        exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨x, Finset.mem_coe.mp hx, rfl⟩)
      have hpart1 : dom.card = ∑ H ∈ Ωs, (Nat.card H - Nat.card Z) := by
        rw [Finset.card_eq_sum_card_fiberwise hmaps2]
        apply Finset.sum_congr rfl
        intro H hH
        exact fiber_card H hH
      have hpart2 : dom.card = Nat.card A - Nat.card Z := by
        rw [hdom, Finset.filter_not, Finset.card_sdiff_of_subset (Finset.subset_univ _),
          Finset.card_univ, hcardZ]
        rw [← Nat.card_eq_fintype_card]
      have hsumH3 : (∑ H ∈ Ωs, Nat.card H)
          = (Nat.card A - Nat.card Z) + Ωs.card * Nat.card Z := by
        rw [Finset.sum_congr rfl (fun H hH => (Nat.sub_add_cancel (hZH H hH)).symm),
          Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Nat.cast_id, ← hpart1, hpart2]
      have hpart : Nat.card A + Ωs.card * Nat.card Z
          = (∑ H ∈ Ωs, Nat.card H) + Nat.card Z := by
        calc Nat.card A + Ωs.card * Nat.card Z
            = ((Nat.card A - Nat.card Z) + Nat.card Z) + Ωs.card * Nat.card Z := by
                rw [Nat.sub_add_cancel hZA]
            _ = ((Nat.card A - Nat.card Z) + Ωs.card * Nat.card Z) + Nat.card Z := by ac_rfl
            _ = (∑ H ∈ Ωs, Nat.card H) + Nat.card Z := by rw [hsumH3]
      have hA : Nat.card A = Nat.card Z * q := by
        rw [hq_def]; exact (Subgroup.card_mul_index Z).symm
      have hident : Ωs.card + q = qs.card * q + 1 := by
        have hkey : Nat.card Z * (q + Ωs.card) = Nat.card Z * (qs.card * q + 1) := by
          rw [Nat.mul_add]
          calc Nat.card Z * q + Nat.card Z * Ωs.card
              = Nat.card A + Ωs.card * Nat.card Z := by rw [hA, Nat.mul_comm (Nat.card Z) Ωs.card]
            _ = (∑ H ∈ Ωs, Nat.card H) + Nat.card Z := hpart
            _ = qs.card * Nat.card A + Nat.card Z := by rw [hsumH]
            _ = Nat.card Z * (qs.card * q) + Nat.card Z := by rw [hA]; ring
            _ = Nat.card Z * (qs.card * q + 1) := by ring
        have hZpos : 0 < Nat.card Z := Nat.card_pos
        have := Nat.mul_left_cancel hZpos hkey
        rw [Nat.add_comm] at this
        exact this
      have hqpos : 0 < q := by
        rw [hq_def]; exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      have hq_odd : Odd q := by
        rw [hq_def]
        obtain ⟨m, hm⟩ := Subgroup.index_dvd_card Z
        rw [hm] at hodd
        exact Nat.Odd.of_mul_left hodd
      have relIndex_mul : ∀ H ∈ Ωs, Z.relIndex H * H.index = Z.index :=
        fun H hH => Subgroup.relIndex_mul_index (Ωs_Zle H hH)
      have hrel_dvd : ∀ H ∈ Ωs, Z.relIndex H ∣ q := by
        intro H hH
        refine ⟨H.index, ?_⟩
        rw [hq_def]; exact (relIndex_mul H hH).symm
      have hrel_ge : ∀ H ∈ Ωs, 3 ≤ Z.relIndex H := by
        intro H hH
        have hdvd := hrel_dvd H hH
        have hpos : 0 < Z.relIndex H := Nat.pos_of_dvd_of_pos hdvd hqpos
        have hne1 : Z.relIndex H ≠ 1 := by
          intro h1
          have hHZ : H ≤ Z := Subgroup.relIndex_eq_one.mp h1
          obtain ⟨x, hx, rfl⟩ := (mem_Ωs H).mp hH
          exact hx (hHZ (hself x hx))
        have hodd_rel : Odd (Z.relIndex H) := by
          have h : Odd (Z.relIndex H * H.index) := by rw [relIndex_mul H hH]; exact hq_odd
          exact Nat.Odd.of_mul_left h
        rcases hodd_rel with ⟨k, hk⟩
        omega
      have hcard_relIndex : ∀ H ∈ Ωs, Nat.card Z * Z.relIndex H = Nat.card H := by
        intro H hH
        have h1 : Z.relIndex H * H.index = Z.index := relIndex_mul H hH
        have h2 : Nat.card Z * Z.index = Nat.card A := Subgroup.card_mul_index Z
        have h3 : Nat.card H * H.index = Nat.card A := Subgroup.card_mul_index H
        have hpos : 0 < H.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
        have heq : (Nat.card Z * Z.relIndex H) * H.index = Nat.card H * H.index := by
          rw [mul_assoc, h1, h2, h3]
        exact Nat.mul_right_cancel hpos heq
      have h3N : 3 * Ωs.card ≤ qs.card * q := by
        have hZpos : 0 < Nat.card Z := Nat.card_pos
        have hle : 3 * Ωs.card ≤ ∑ H ∈ Ωs, Z.relIndex H := by
          have hsum3 : (∑ H ∈ Ωs, (3 : ℕ)) = 3 * Ωs.card := by
            rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm]
          rw [← hsum3]
          exact Finset.sum_le_sum (fun H hH => hrel_ge H hH)
        have hZsum : Nat.card Z * (∑ H ∈ Ωs, Z.relIndex H) = qs.card * Nat.card A := by
          rw [Finset.mul_sum]
          rw [Finset.sum_congr rfl (fun H hH => hcard_relIndex H hH)]
          exact hsumH
        have hgoal : Nat.card Z * (3 * Ωs.card) ≤ Nat.card Z * (qs.card * q) := by
          calc Nat.card Z * (3 * Ωs.card) ≤ Nat.card Z * (∑ H ∈ Ωs, Z.relIndex H) :=
                Nat.mul_le_mul_left _ hle
            _ = qs.card * Nat.card A := hZsum
            _ = Nat.card Z * (qs.card * q) := by rw [hA]; ring
        exact Nat.le_of_mul_le_mul_left hgoal hZpos
      have hqs_ge1 : 1 ≤ qs.card := by
        rw [hqs]
        exact Finset.card_pos.mpr
          ⟨orbQ (M x0), Finset.mem_image.mpr ⟨M x0, (mem_Ωs _).mpr ⟨x0, hx0, rfl⟩, rfl⟩⟩
      have hrs : 2 ≤ qs.card := by
        by_contra hcon
        push_neg at hcon
        have hqs1 : qs.card = 1 := by omega
        have hNs1 : Ωs.card = 1 := by
          have := hident
          rw [hqs1, one_mul] at this
          omega
        obtain ⟨H, hHeq⟩ := Finset.card_eq_one.mp hNs1
        have hHmem : H ∈ Ωs := by rw [hHeq]; exact Finset.mem_singleton.mpr rfl
        have hsum1 : (∑ H' ∈ Ωs, Nat.card H') = Nat.card H := by
          rw [hHeq, Finset.sum_singleton]
        have hHA : Nat.card H = Nat.card A := by
          rw [hsum1] at hsumH
          rw [hqs1, one_mul] at hsumH
          exact hsumH
        exact Ωs_ne_top H hHmem (Subgroup.eq_top_of_card_eq H hHA)
      exact arith_le hident h3N hrs (Nat.one_le_iff_ne_zero.mpr (ne_of_gt hqpos))

end Work.SmallRank
