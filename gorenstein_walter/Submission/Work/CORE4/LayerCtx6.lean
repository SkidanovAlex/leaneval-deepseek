import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.DihOrCycSub

open scoped MatrixGroups

namespace Work.CORE4

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-! ## Transport of `IsQuasisimple` and of the shape of `E/Z(E)` -/

/-- `IsSimpleGroup` is transported by a group isomorphism. -/
theorem isSimpleGroup_of_mulEquiv {H₁ H₂ : Type*} [Group H₁] [Group H₂] (e : H₁ ≃* H₂)
    [h : IsSimpleGroup H₁] : IsSimpleGroup H₂ where
  exists_pair_ne := by
    obtain ⟨x, y, hxy⟩ := h.exists_pair_ne
    exact ⟨e x, e y, fun hh => hxy (e.injective hh)⟩
  eq_bot_or_eq_top_of_normal N hN := by
    have hNc : (N.comap (e : H₁ →* H₂)).Normal := hN.comap (e : H₁ →* H₂)
    rcases h.eq_bot_or_eq_top_of_normal (N.comap (e : H₁ →* H₂)) with hbot | htop
    · left
      rw [← Subgroup.map_comap_eq_self_of_surjective (f := (e : H₁ →* H₂)) e.surjective N,
        hbot, Subgroup.map_bot]
    · right
      rw [← Subgroup.map_comap_eq_self_of_surjective (f := (e : H₁ →* H₂)) e.surjective N,
        htop, Subgroup.map_top_of_surjective _ e.surjective]

/-- The image of the center under a group isomorphism is the center. -/
theorem map_center_mulEquiv {H₁ H₂ : Type*} [Group H₁] [Group H₂] (e : H₁ ≃* H₂) :
    (Subgroup.center H₁).map (e : H₁ →* H₂) = Subgroup.center H₂ := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_center_iff] at hy ⊢
    intro g
    calc g * e y = e (e.symm g) * e y := by rw [e.apply_symm_apply]
      _ = e (e.symm g * y) := by rw [map_mul]
      _ = e (y * e.symm g) := by rw [hy (e.symm g)]
      _ = e y * e (e.symm g) := by rw [map_mul]
      _ = e y * g := by rw [e.apply_symm_apply]
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro g
    have h : e (g * e.symm x) = e (e.symm x * g) := by
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact hx (e g)
    exact e.injective h

/-- `IsQuasisimple` is preserved by an injective homomorphism. -/
theorem isQuasisimple_map {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) {E : Subgroup A} (h : Work.GW2.IsQuasisimple E) :
    Work.GW2.IsQuasisimple (E.map f) := by
  obtain ⟨hcomm, hsimple⟩ := h
  have e : ↥E ≃* ↥(E.map f) := Subgroup.equivMapOfInjective E f hf
  have hmap : Subgroup.map (e : ↥E →* ↥(E.map f)) (Subgroup.center ↥E) =
      Subgroup.center ↥(E.map f) := map_center_mulEquiv e
  refine ⟨?_, ?_⟩
  · rw [← Subgroup.map_commutator, hcomm]
  · haveI : IsSimpleGroup (↥E ⧸ Subgroup.center ↥E) := hsimple
    have hcongr := QuotientGroup.congr (Subgroup.center ↥E) (Subgroup.center ↥(E.map f)) e hmap
    exact isSimpleGroup_of_mulEquiv hcongr

/-- **The shape of `E/Z(E)` is transported by an injective homomorphism**:
quasisimplicity, oddness of the centre, and the `A₇`/`PSL(2,q)` description of `E/Z(E)` pass to
the image under an injective homomorphism. -/
theorem quasisimple_shape_map {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) {E : Subgroup A} (hq : Work.GW2.IsQuasisimple E)
    (hodd : Odd (Nat.card (Subgroup.center ↥E)))
    (hshape : Nonempty ((↥E ⧸ Subgroup.center ↥E) ≃* alternatingGroup (Fin 7)) ∨
      ∃ p k : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
        Nonempty ((↥E ⧸ Subgroup.center ↥E) ≃* PSL(2, GaloisField p k))) :
    Work.GW2.IsQuasisimple (E.map f) ∧ Odd (Nat.card (Subgroup.center ↥(E.map f))) ∧
      (Nonempty ((↥(E.map f) ⧸ Subgroup.center ↥(E.map f)) ≃* alternatingGroup (Fin 7)) ∨
        ∃ p k : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
          Nonempty ((↥(E.map f) ⧸ Subgroup.center ↥(E.map f)) ≃* PSL(2, GaloisField p k))) := by
  have e : ↥E ≃* ↥(E.map f) := Subgroup.equivMapOfInjective E f hf
  have hmap : Subgroup.map (e : ↥E →* ↥(E.map f)) (Subgroup.center ↥E) =
      Subgroup.center ↥(E.map f) := map_center_mulEquiv e
  have hq' : Work.GW2.IsQuasisimple (E.map f) := isQuasisimple_map f hf hq
  have hodd' : Odd (Nat.card (Subgroup.center ↥(E.map f))) := by
    rw [← hmap, Subgroup.card_map_of_injective e.injective]
    exact hodd
  have hcongr : (↥E ⧸ Subgroup.center ↥E) ≃* (↥(E.map f) ⧸ Subgroup.center ↥(E.map f)) :=
    QuotientGroup.congr (Subgroup.center ↥E) (Subgroup.center ↥(E.map f)) e hmap
  refine ⟨hq', hodd', ?_⟩
  rcases hshape with hA | hB
  · obtain ⟨hA⟩ := hA
    exact Or.inl ⟨hcongr.symm.trans hA⟩
  · obtain ⟨p, k, hpp, hpodd, h5, hY⟩ := hB
    obtain ⟨hiso⟩ := hY
    exact Or.inr ⟨p, k, hpp, hpodd, h5, ⟨hcongr.symm.trans hiso⟩⟩

/-- A proper subgroup of a finite group is strictly smaller. -/
theorem card_lt_card_of_ne_top {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (h : H ≠ ⊤) : Nat.card ↥H < Nat.card G := by
  haveI : Finite (G ⧸ H) := Quotient.finite _
  have hidx : H.index ≠ 1 := fun h1 => h (Subgroup.index_eq_one.mp h1)
  have hidx0 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hcard := H.index_mul_card
  have hpos : 0 < Nat.card ↥H := Nat.card_pos
  have : 1 < H.index := by omega
  nlinarith [hcard, hpos, this]

/-! ## The layer of `M` -/

/-- **Bender §4, p. 224, first paragraph.**  In the §4 configuration `Case2Ctx6 B` over
`BenderCtx G`, with `E = E(M) = layerIn D.M` the layer of the maximal subgroup `M = D.M`:

* `E` is quasisimple;
* `Z(E)` has odd order;
* `E/Z(E) ≅ A₇` or `E/Z(E) ≅ PSL(2, q)`, `q = p^k ≥ 5`, `p` odd. -/
theorem LayerCtx6 (I : Work.GW2.C4Inputs) {G : Type} [Group G] [Finite G]
    {B : Work.GW2.BenderSetup G} (hbc : Work.GW2.BenderCtx G) (h6 : Work.GW2.Case2Ctx6 B)
    (hD : Work.GW2.DihOrCycSylow ↥h6.D.M) :
    Work.GW2.IsQuasisimple (Work.GW2.layerIn h6.D.M) ∧
      Odd (Nat.card (Subgroup.center ↥(Work.GW2.layerIn h6.D.M))) ∧
      (Nonempty ((↥(Work.GW2.layerIn h6.D.M) ⧸
            Subgroup.center ↥(Work.GW2.layerIn h6.D.M)) ≃* alternatingGroup (Fin 7)) ∨
        ∃ p k : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
          Nonempty ((↥(Work.GW2.layerIn h6.D.M) ⧸
            Subgroup.center ↥(Work.GW2.layerIn h6.D.M)) ≃* PSL(2, GaloisField p k))) := by
  classical
  set M : Subgroup G := h6.D.M with hMdef
  have ht1 : B.t ≠ 1 := by
    intro h1
    have ht := B.t_order
    rw [h1, orderOf_one] at ht
    exact absurd ht (by norm_num)
  -- the layer of `M` is nontrivial
  have hEne : Work.GW2.layerIn M ≠ ⊥ := by
    intro h
    have : B.t ∈ (⊥ : Subgroup G) := h ▸ h6.D.t_mem
    exact ht1 (Subgroup.mem_bot.mp this)
  have hlayer_ne : Work.GW2.layer ↥M ≠ ⊥ := by
    intro h
    apply hEne
    show Work.GW2.layerIn M = ⊥
    rw [Work.GW2.layerIn, h, Subgroup.map_bot]
  -- so `M` has a normal quasisimple subgroup
  obtain ⟨E', hE'norm, hE'q⟩ : ∃ E' : Subgroup ↥M, E'.Normal ∧ Work.GW2.IsQuasisimple E' := by
    by_contra hcon
    apply hlayer_ne
    rw [Work.GW2.layer, sSup_eq_bot]
    intro F hF
    by_contra hFne
    exact hcon ⟨F, hF.1, hF.2⟩
  -- `M` is a D-group, being a proper subgroup of `G`
  have hcard : Nat.card ↥M < Nat.card G := card_lt_card_of_ne_top h6.D.M_coatom.ne_top
  have hIsD : Work.GW2.IsDGroup ↥M := hbc.ih ↥M hcard hD
  -- Bender 1.6 / `LayerProp`
  obtain ⟨hlayer, hodd, hshape⟩ :=
    I.toolkit.lay ↥M I.toolkit.ft hD hIsD E' hE'norm hE'q
  -- `layerIn M = E'.map M.subtype`
  have hEq : Work.GW2.layerIn M = E'.map (M.subtype) := by
    rw [Work.GW2.layerIn, hlayer]
  rw [hEq]
  exact quasisimple_shape_map (M.subtype) (Subgroup.subtype_injective M) hE'q hodd hshape

end Work.CORE4
