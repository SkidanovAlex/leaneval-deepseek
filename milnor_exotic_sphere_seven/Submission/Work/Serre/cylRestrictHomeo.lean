import Mathlib
import Submission.Work.Serre.ThomCylDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The mapping cylinder of a fibre-restriction

For a map `q : C(X, Γ)` and a **closed** subset `S ⊆ Γ`, the mapping cylinder of the restriction
`restrictFibre q S : C(↥(q ⁻¹' S), ↥S)` is canonically homeomorphic to the part
`(cylRetract q) ⁻¹' S` of the mapping cylinder of `q`, and the homeomorphism identifies the bottom
copies `range (cylIncl ·)`.

Writing `Zf := (↥(q ⁻¹' S) × I) ⊕ ↥S` and `Zq := (X × I) ⊕ Γ`, the canonical map is induced by the
inclusion `ι : Zf → Zq` and the quotient map `cylMk q : Zq → cyl q`: its image is exactly
`A := cylRetractFun q ⁻¹' S`, a saturated *closed* subset of `Zq` (here `IsClosed S` is used).  The
key point is the standard fact that the *restriction of a quotient map to a saturated closed subset
is a quotient map* (`isQuotientMap_corestrict` below), which makes the induced bijection a
homeomorphism.

The statement is false without the closedness hypothesis on `S`.
-/

open scoped Topology unitInterval

namespace Work.Serre

/-- **The restriction of a quotient map to a saturated closed subset is a quotient map.**

Let `p : Z → Y` be a quotient map and `ι : Z₀ → Z` an embedding whose range `A` is closed and
saturated for the fibres of `p` (i.e. `p z ∈ p '' A → z ∈ A`).  Then the corestriction of `p ∘ ι`
to the image `p '' A` is a quotient map. -/
private theorem isQuotientMap_corestrict
    {Z Y Z₀ : Type*} [TopologicalSpace Z] [TopologicalSpace Y] [TopologicalSpace Z₀]
    {p : Z → Y} (hp : Topology.IsQuotientMap p) {ι : Z₀ → Z} (hι : Topology.IsEmbedding ι)
    (hA : IsClosed (Set.range ι))
    (hsat : ∀ z, p z ∈ p '' Set.range ι → z ∈ Set.range ι) :
    Topology.IsQuotientMap (fun a : Z₀ =>
      (⟨p (ι a), Set.mem_image_of_mem p (Set.mem_range_self a)⟩ : p '' Set.range ι)) := by
  set A := Set.range ι with hAdef
  set B := p '' A with hBdef
  set Φ : Z₀ → B := fun a => (⟨p (ι a), Set.mem_image_of_mem p (Set.mem_range_self a)⟩ : B)
    with hΦdef
  have hcont : Continuous Φ := by
    refine Continuous.subtype_mk ?_ _
    exact hp.continuous.comp hι.continuous
  refine ⟨Topology.IsCoinducing.of_isOpen_preimage_iff_isOpen ?_, ?_⟩
  · intro U
    refine ⟨fun hU => ?_, fun hU => hU.preimage hcont⟩
    obtain ⟨W, hW, hWU⟩ := hι.isOpen_iff.mp hU
    set U' : Set Y := Subtype.val '' U with hU'def
    have hWA : W ∩ A = {z | z ∈ A ∧ p z ∈ U'} := by
      ext z; constructor
      · intro hz
        obtain ⟨hzW, hzA⟩ := hz
        obtain ⟨a, rfl⟩ := hAdef ▸ hzA
        have h1 : a ∈ ι ⁻¹' W := hzW
        rw [hWU] at h1
        exact ⟨Set.mem_range_self a, ⟨Φ a, h1, rfl⟩⟩
      · intro hz
        obtain ⟨hzA, hzU'⟩ := hz
        obtain ⟨b, hbU, hb1⟩ := hzU'
        obtain ⟨a, rfl⟩ := hAdef ▸ hzA
        have h2 : Φ a ∈ U := by
          have hb : b = Φ a := Subtype.ext hb1
          rwa [hb] at hbU
        have h3 : a ∈ ι ⁻¹' W := hWU ▸ h2
        exact ⟨h3, Set.mem_range_self a⟩
    set S₀ : Set Z := {z | z ∈ A ∧ p z ∈ U'} with hS₀def
    set P : Set Z := S₀ ∪ Aᶜ with hPdef
    have hP_eq : P = W ∪ Aᶜ := by
      rw [hPdef, ← hWA, Set.inter_union_distrib_right, Set.union_compl_self, Set.inter_univ]
    have hPopen : IsOpen P := by
      rw [hP_eq]; exact hW.union hA.isOpen_compl
    have hmemP : ∀ z, z ∈ A → (z ∈ P ↔ p z ∈ U') := by
      intro z hzA
      rw [hPdef, hS₀def]
      constructor
      · rintro (h | h)
        · exact h.2
        · exact absurd hzA h
      · intro h; exact Or.inl ⟨hzA, h⟩
    have hsatP : p ⁻¹' (p '' P) = P := by
      ext z; constructor
      · intro hz
        obtain ⟨z', hz'P, hz'eq⟩ := hz
        by_cases hzA : z ∈ A
        · have hz'A : z' ∈ A := hsat z' (by rw [hz'eq]; exact Set.mem_image_of_mem p hzA)
          have hU' : p z ∈ U' := by
            rw [← hz'eq]
            exact (hmemP z' hz'A).mp hz'P
          exact (hmemP z hzA).mpr hU'
        · exact Or.inr hzA
      · intro hz; exact ⟨z, hz, rfl⟩
    have hΩopen : IsOpen (p '' P) := hp.isOpen_preimage.mp (by
      show IsOpen (p ⁻¹' (p '' P))
      rw [hsatP]
      exact hPopen)
    have hUeq : U = Subtype.val ⁻¹' (p '' P) := by
      ext b; constructor
      · intro hbU
        have hb' : b.1 ∈ U' := ⟨b, hbU, rfl⟩
        obtain ⟨z, hzA, hz⟩ := b.2
        refine ⟨z, (hmemP z hzA).mpr ?_, hz⟩
        rw [hz]; exact hb'
      · rintro ⟨z, hzP, hz⟩
        rw [hPdef, hS₀def] at hzP
        rcases hzP with ⟨hzA, hzU'⟩ | hzA
        · obtain ⟨b', hb'U, hb'1⟩ := hzU'
          have hbb : b' = b := Subtype.ext (hb'1.trans hz)
          rwa [hbb] at hb'U
        · exact absurd (hsat z (by rw [hz]; exact b.2)) hzA
    rw [hUeq]
    exact hΩopen.preimage continuous_subtype_val
  · intro b
    obtain ⟨z, hzA, hz⟩ := b.2
    obtain ⟨a, rfl⟩ := hAdef ▸ hzA
    exact ⟨a, Subtype.ext hz⟩

theorem cylRestrictHomeo {Γ : Type} [TopologicalSpace Γ] {X : Type} [TopologicalSpace X]
    (q : C(X, Γ)) (S : Set Γ) (hS : IsClosed S) :
    ∃ e : Work.Serre.cyl (Work.Serre.restrictFibre q S) ≃ₜ ↥((Work.Serre.cylRetract q) ⁻¹' S),
      ∀ y : Work.Serre.cyl (Work.Serre.restrictFibre q S),
        (y ∈ Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q S)) ↔
          (e y).1 ∈ Set.range (Work.Serre.cylIncl q)) := by
  classical
  set f : C(↥(q ⁻¹' S), ↥S) := restrictFibre q S with hfdef
  set ι : ((↥(q ⁻¹' S) × unitInterval) ⊕ ↥S) → ((X × unitInterval) ⊕ Γ) :=
    Sum.elim (fun z : ↥(q ⁻¹' S) × unitInterval => Sum.inl (z.1.1, z.2))
      (fun s : ↥S => Sum.inr s.1) with hιdef
  have hι_inl : ∀ z : ↥(q ⁻¹' S) × unitInterval, ι (Sum.inl z) = Sum.inl (z.1.1, z.2) :=
    fun z => rfl
  have hι_inr : ∀ s : ↥S, ι (Sum.inr s) = Sum.inr s.1 := fun s => rfl
  have hι : Topology.IsEmbedding ι := by
    rw [hιdef]
    refine Topology.IsEmbedding.sumElim ?_ ?_ ?_ ?_
    · have h₁ : Topology.IsEmbedding (Prod.map (Subtype.val : ↥(q ⁻¹' S) → X)
          (id : unitInterval → unitInterval)) :=
        (Topology.IsEmbedding.subtypeVal (X := X)).prodMap
          (Topology.IsEmbedding.id (X := unitInterval))
      exact Topology.IsEmbedding.inl.comp h₁
    · exact Topology.IsEmbedding.inr.comp Topology.IsEmbedding.subtypeVal
    · rw [Set.disjoint_left]
      rintro x hx ⟨s, rfl⟩
      have hsub : Set.range (fun z : ↥(q ⁻¹' S) × unitInterval => Sum.inl (z.1.1, z.2)) ⊆
          Set.range (Sum.inl : (X × unitInterval) → (X × unitInterval) ⊕ Γ) := by
        rintro _ ⟨z, rfl⟩
        exact ⟨(z.1.1, z.2), rfl⟩
      have hx' : Sum.inr s.1 ∈ Set.range (Sum.inl : (X × unitInterval) →
          (X × unitInterval) ⊕ Γ) :=
        (isClosed_range_inl.closure_subset_iff.mpr hsub) hx
      obtain ⟨y, hy⟩ := hx'
      exact Sum.inl_ne_inr hy
    · rw [Set.disjoint_left]
      rintro x ⟨z, rfl⟩ hx
      have hsub : Set.range (fun s : ↥S => Sum.inr (s.1)) ⊆
          Set.range (Sum.inr : Γ → (X × unitInterval) ⊕ Γ) := by
        rintro _ ⟨s, rfl⟩
        exact ⟨s.1, rfl⟩
      have hx' : Sum.inl (z.1.1, z.2) ∈ Set.range (Sum.inr : Γ →
          (X × unitInterval) ⊕ Γ) :=
        (isClosed_range_inr.closure_subset_iff.mpr hsub) hx
      obtain ⟨y, hy⟩ := hx'
      exact Sum.inr_ne_inl hy
  have hrange : Set.range ι = {z : (X × unitInterval) ⊕ Γ | cylRetractFun q z ∈ S} := by
    ext z; constructor
    · rintro ⟨a, rfl⟩
      cases a with
      | inl zz => exact zz.1.2
      | inr s => exact s.2
    · intro hz
      cases z with
      | inl zz => exact ⟨Sum.inl (⟨zz.1, hz⟩, zz.2), rfl⟩
      | inr γ => exact ⟨Sum.inr ⟨γ, hz⟩, rfl⟩
  have hAclosed : IsClosed (Set.range ι) := by
    have hcont : Continuous (cylRetractFun q) :=
      (q.continuous.comp continuous_fst).sumElim continuous_id
    rw [hrange]
    exact IsClosed.preimage hcont hS
  have hsat : ∀ z, cylMk q z ∈ cylMk q '' Set.range ι → z ∈ Set.range ι := by
    intro z hz
    obtain ⟨z', hz', hzeq⟩ := hz
    rw [hrange] at hz' ⊢
    show cylRetractFun q z ∈ S
    have hrel := cylRetractFun_rel q z' z (Quotient.exact hzeq)
    rw [← hrel]
    exact hz'
  set Φ : ((↥(q ⁻¹' S) × unitInterval) ⊕ ↥S) → ↥(cylMk q '' Set.range ι) :=
    fun a => ⟨cylMk q (ι a), Set.mem_image_of_mem (cylMk q) (Set.mem_range_self a)⟩ with hΦdef
  have hΦ : Topology.IsQuotientMap Φ :=
    isQuotientMap_corestrict
      (isQuotientMap_quotient_mk' (s := Relation.EqvGen.setoid (cylRel q))) hι hAclosed hsat
  have hwell : ∀ a b : ((↥(q ⁻¹' S) × unitInterval) ⊕ ↥S),
      Relation.EqvGen (cylRel f) a b → Φ a = Φ b := by
    intro a b hab
    induction hab with
    | rel x y hxy =>
        obtain ⟨p, rfl, rfl⟩ := hxy
        refine Subtype.ext ?_
        show cylMk q (ι (Sum.inl (p, 1))) = cylMk q (ι (Sum.inr (f p)))
        rw [hι_inl, hι_inr]
        exact cyl_mk_inl_one q p.1
    | refl x => rfl
    | symm x y hxy ih => exact ih.symm
    | trans x y z hxy hyz ih1 ih2 => exact ih1.trans ih2
  set e : cyl f → ↥(cylMk q '' Set.range ι) := Quotient.lift Φ hwell with hedef
  have he_lift : ∀ a : ((↥(q ⁻¹' S) × unitInterval) ⊕ ↥S), e (cylMk f a) = Φ a := by
    intro a
    exact Quotient.lift_mk Φ hwell a
  have he_q : Topology.IsQuotientMap e :=
    Topology.IsQuotientMap.of_comp_isQuotientMap (f := cylMk f) (g := e)
      (isQuotientMap_quotient_mk' (s := Relation.EqvGen.setoid (cylRel f)))
      (by
        have hcomp : e ∘ cylMk f = Φ := funext he_lift
        rw [hcomp]
        exact hΦ)
  have hsatGen : ∀ x y : (X × unitInterval) ⊕ Γ, Relation.EqvGen (cylRel q) x y →
      (x ∈ Set.range ι ↔ y ∈ Set.range ι) := by
    intro x y hab
    induction hab with
    | rel a b hab =>
        obtain ⟨u, rfl, rfl⟩ := hab
        rw [hrange]
        simp [cylRetractFun]
    | refl z => exact Iff.rfl
    | symm x y hxy ih => exact ih.symm
    | trans x y z hxy hyz ih1 ih2 => exact ih1.trans ih2
  have hgen : ∀ x y : (X × unitInterval) ⊕ Γ, Relation.EqvGen (cylRel q) x y →
      ∀ a : ((↥(q ⁻¹' S) × unitInterval) ⊕ ↥S), ι a = x →
        ∃ b : ((↥(q ⁻¹' S) × unitInterval) ⊕ ↥S),
          ι b = y ∧ Relation.EqvGen (cylRel f) a b := by
    intro x y hab
    induction hab with
    | rel x y hxy =>
        intro a ha
        obtain ⟨u, rfl, rfl⟩ := hxy
        cases a with
        | inl z =>
            rw [hι_inl] at ha
            have h1 : z.1.1 = u := congrArg Prod.fst (Sum.inl.inj ha)
            have h2 : z.2 = 1 := congrArg Prod.snd (Sum.inl.inj ha)
            refine ⟨Sum.inr (f z.1), ?_, Relation.EqvGen.rel _ _ ?_⟩
            · rw [hι_inr]
              exact congrArg (fun w => Sum.inr (q w)) h1
            · refine ⟨z.1, congrArg Sum.inl (Prod.ext rfl h2), rfl⟩
        | inr s =>
            rw [hι_inr] at ha
            exact absurd ha Sum.inr_ne_inl
    | refl z => intro a ha; exact ⟨a, ha, Relation.EqvGen.refl a⟩
    | symm x y hxy ih =>
        intro a ha
        obtain ⟨a', ha'⟩ := (hsatGen x y hxy).mpr ⟨a, ha⟩
        obtain ⟨b, hb, hfab⟩ := ih a' ha'
        have hba : b = a := hι.injective (hb.trans ha.symm)
        refine ⟨a', ha', ?_⟩
        rw [hba] at hfab
        exact Relation.EqvGen.symm a' a hfab
    | trans x y z hxy hyz ih1 ih2 =>
        intro a ha
        obtain ⟨b, hb, h1⟩ := ih1 a ha
        obtain ⟨c, hc, h2⟩ := ih2 b hb
        exact ⟨c, hc, Relation.EqvGen.trans a b c h1 h2⟩
  have hinj : Function.Injective e := by
    intro y1 y2 hy
    induction y1 using Quotient.inductionOn with
    | h a =>
      induction y2 using Quotient.inductionOn with
      | h b =>
        have h1 : Φ a = Φ b := by
          rw [← he_lift a, ← he_lift b]
          exact hy
        have h2 : cylMk q (ι a) = cylMk q (ι b) := congrArg Subtype.val h1
        have h3 : Relation.EqvGen (cylRel q) (ι a) (ι b) := Quotient.exact h2
        obtain ⟨c, hc, h4⟩ := hgen (ι a) (ι b) h3 a rfl
        have h5 : c = b := hι.injective hc
        rw [← h5]
        exact Quotient.sound h4
  have hImg : cylMk q '' Set.range ι = (cylRetract q) ⁻¹' S := by
    ext y; constructor
    · rintro ⟨z, hz, rfl⟩
      rw [hrange] at hz
      show cylRetract q (cylMk q z) ∈ S
      exact hz
    · intro hy
      obtain ⟨z, rfl⟩ := Quotient.exists_rep y
      refine ⟨z, ?_, rfl⟩
      rw [hrange]
      show cylRetractFun q z ∈ S
      exact hy
  set e₀ : cyl f ≃ₜ ↥(cylMk q '' Set.range ι) :=
    IsHomeomorph.homeomorph e (isHomeomorph_iff_isQuotientMap_injective.mpr ⟨he_q, hinj⟩)
    with he₀def
  have hval : ∀ y : cyl f, (e₀ y).1 = (e y).1 := fun y => rfl
  have hfinal : ∀ y : cyl f,
      ((e₀.trans (Homeomorph.setCongr hImg)) y).1 = (e y).1 := fun y => rfl
  refine ⟨e₀.trans (Homeomorph.setCongr hImg), ?_⟩
  intro y
  induction y using Quotient.inductionOn with
  | h a =>
    have hvala : ((e₀.trans (Homeomorph.setCongr hImg)) (⟦a⟧ : cyl f)).1 = cylMk q (ι a) := by
      rw [hfinal]
      show (e (cylMk f a)).1 = cylMk q (ι a)
      rw [he_lift]
    constructor
    · intro hy
      obtain ⟨p, hp⟩ := hy
      refine ⟨p.1, ?_⟩
      rw [← hp, hfinal]
      show (e (cylMk f (Sum.inl (p, 0)))).1 = cylMk q (ι (Sum.inl (p, 0)))
      rw [he_lift]
    · intro hy
      rw [hvala] at hy
      obtain ⟨x, hx⟩ := hy
      have hkey : cylMk q (ι a) = cylMk q (Sum.inl (x, 0)) := by
        rw [← hx]
        rfl
      have h3 : Relation.EqvGen (cylRel q) (ι a) (Sum.inl (x, 0)) := Quotient.exact hkey
      obtain ⟨c, hc, h4⟩ := hgen (ι a) (Sum.inl (x, 0)) h3 a rfl
      cases c with
      | inl z =>
          rw [hι_inl] at hc
          have h2 : z.2 = 0 := congrArg Prod.snd (Sum.inl.inj hc)
          have hz : z = (z.1, 0) := Prod.ext rfl h2
          refine ⟨z.1, ?_⟩
          show cylMk f (Sum.inl (z.1, 0)) = (⟦a⟧ : cyl f)
          rw [← congrArg (cylMk f) (congrArg Sum.inl hz)]
          exact Quotient.sound h4.symm
      | inr s =>
          rw [hι_inr] at hc
          exact absurd hc Sum.inr_ne_inl

end Work.Serre
