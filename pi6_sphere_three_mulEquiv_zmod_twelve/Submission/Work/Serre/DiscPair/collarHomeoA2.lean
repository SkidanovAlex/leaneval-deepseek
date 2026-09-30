import Mathlib
import Submission.Work.Serre.DiscPair.collarDefs

/-!
# The collar model of `A₂ ∩ U₀` in the mapping cylinder

This file proves `Work.Serre.DiscPair.collarHomeoA2`: the piece `U₀A₂ = {λ < 1/2} ∩ A₂` of the
mapping cylinder of `q` is homeomorphic to its collar model
`cylSet₁ = (X × {0}) ∪ (A × (0,1/2))` inside `X × I`, the homeomorphism being the (inverse of the)
restriction of the quotient map `X × I → cyl q`, and it carries `(A₂ ∩ U₀) ∩ U₁` onto
`cylSet₂ = A × (0,1/2)`.

The first ingredient is the general topological fact `exists_homeo_of_saturated_open`: if `W` is an
open, saturated subset of a space on which the quotient map `π` is injective (the classes of the
quotient that meet `W` are singletons), then `π` restricts to a homeomorphism `W ≃ₜ π '' W`.
-/

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre.DiscPair

noncomputable section

variable {D : ℕ} {Γ : Type} [TopologicalSpace Γ] {ι : Type}
  {f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)} {X : Type} [TopologicalSpace X]

/-! ## A general fact: quotient maps restrict to saturated open sets with singleton classes -/

/-- **A quotient map restricts to a homeomorphism on an open saturated set with singleton
classes.**  If `W` is open, saturated for the equivalence relation `S`, and every class meeting `W`
is a singleton, then `Quotient.mk''` restricts to a homeomorphism `W ≃ₜ π '' W`, whose value on
`x` is `π x`. -/
theorem exists_homeo_of_saturated_open {Y : Type*} [TopologicalSpace Y] (S : Setoid Y) {W : Set Y}
    (hWo : IsOpen W) (hsat : ∀ ⦃a b⦄, S.r a b → a ∈ W → b ∈ W)
    (htriv : ∀ ⦃a b⦄, a ∈ W → b ∈ W → S.r a b → a = b) :
    ∃ e : ↥W ≃ₜ ↥((Quotient.mk'' : Y → Quotient S) '' W),
      ∀ x : ↥W, ((e x : ↥((Quotient.mk'' : Y → Quotient S) '' W)) : Quotient S)
        = Quotient.mk'' x.1 := by
  classical
  let π : Y → Quotient S := Quotient.mk''
  have hval : ∀ x : ↥W, π x.1 ∈ (π '' W : Set (Quotient S)) := fun x => ⟨x.1, x.2, rfl⟩
  let toFun : ↥W → ↥(π '' W : Set (Quotient S)) := fun x => ⟨π x.1, hval x⟩
  let invFun : ↥(π '' W : Set (Quotient S)) → ↥W :=
    fun y => ⟨Classical.choose y.2, (Classical.choose_spec y.2).1⟩
  have hleft : Function.LeftInverse invFun toFun := by
    intro x
    change (⟨Classical.choose (hval x), (Classical.choose_spec (hval x)).1⟩ : ↥W) = x
    have hr : S.r (Classical.choose (hval x)) x.1 :=
      Quotient.exact (Classical.choose_spec (hval x)).2
    exact Subtype.ext (htriv (Classical.choose_spec (hval x)).1 x.2 hr)
  have hright : Function.RightInverse invFun toFun := by
    intro y
    change (⟨π (Classical.choose y.2),
      hval ⟨Classical.choose y.2, (Classical.choose_spec y.2).1⟩⟩ : ↥(π '' W)) = y
    exact Subtype.ext (Classical.choose_spec y.2).2
  have hcont_to : Continuous toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_quotient_mk'.comp continuous_subtype_val
  have hopen : IsOpenMap toFun := by
    intro U hU
    obtain ⟨O, hO, hUO⟩ := (isOpen_induced_iff (f := (Subtype.val : ↥W → Y))).mp hU
    set A : Set Y := Subtype.val '' U with hAdef
    have hAeq : A = W ∩ O := by
      rw [hAdef, ← hUO, Set.image_preimage_eq_inter_range, Subtype.range_val, Set.inter_comm]
    have hA : IsOpen A := hAeq.symm ▸ hWo.inter hO
    have hAsub : A ⊆ W := by rw [hAeq]; exact Set.inter_subset_left
    have hpre : π ⁻¹' (π '' A) = A := by
      ext y
      constructor
      · rintro ⟨a, ha, haq⟩
        have hsr : S.r a y := Quotient.exact haq
        have haW : a ∈ W := hAsub ha
        have hyW : y ∈ W := hsat hsr haW
        have hya : y = a := (htriv haW hyW hsr).symm
        rw [hya]; exact ha
      · intro hy
        exact ⟨y, hy, rfl⟩
    have himg_open : IsOpen (π '' A) := by
      have h1 : IsOpen (π ⁻¹' (π '' A)) := by rw [hpre]; exact hA
      exact (isQuotientMap_quotient_mk'.isCoinducing.isOpen_preimage).mpr h1
    have hvalimg : (Subtype.val '' (toFun '' U) : Set (Quotient S)) = π '' A := by
      rw [hAdef, ← Set.image_comp, ← Set.image_comp]
      rfl
    have hT : (Subtype.val ⁻¹' (Subtype.val '' (toFun '' U)) : Set ↥(π '' W)) = toFun '' U :=
      Set.preimage_image_eq _ Subtype.val_injective
    exact (isOpen_induced_iff (f := (Subtype.val : ↥(π '' W) → Quotient S))).mpr
      ⟨(Subtype.val '' (toFun '' U)), hvalimg.symm ▸ himg_open, hT⟩
  have hcont_inv : Continuous invFun := by
    rw [continuous_def]
    intro U hU
    have hpre : invFun ⁻¹' U = toFun '' U := by
      ext y
      constructor
      · intro hy
        exact ⟨invFun y, hy, hright y⟩
      · rintro ⟨x, hx, rfl⟩
        show invFun (toFun x) ∈ U
        rw [hleft x]
        exact hx
    rw [hpre]
    exact hopen U hU
  let hhom : ↥W ≃ₜ ↥(π '' W) :=
    { toFun := toFun, invFun := invFun, left_inv := hleft, right_inv := hright,
      continuous_toFun := hcont_to, continuous_invFun := hcont_inv }
  refine ⟨hhom, ?_⟩
  intro x
  rfl

/-! ## Two standard transports of subtypes -/

/-- `{x : ↥s // x ∈ t}` is homeomorphic to `↥(s ∩ t)` (the identity on the underlying points). -/
def subtypeInterHomeo {α : Type*} [TopologicalSpace α] (s t : Set α) :
    {x : ↥s // (x : α) ∈ t} ≃ₜ ↥(s ∩ t) where
  toFun x := ⟨x.1.1, x.1.2, x.2⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv x := rfl
  right_inv x := rfl
  continuous_toFun := Continuous.subtype_mk
    (f := fun x : {x : ↥s // (x : α) ∈ t} => (x.1.1 : α))
    (continuous_subtype_val.comp continuous_subtype_val) (fun x => ⟨x.1.2, x.2⟩)
  continuous_invFun := Continuous.subtype_mk
    (f := fun x : ↥(s ∩ t) => (⟨x.1, x.2.1⟩ : ↥s))
    (Continuous.subtype_mk (f := fun x : ↥(s ∩ t) => (x.1 : α)) continuous_subtype_val
      (fun x => x.2.1))
    (fun x => x.2.2)

/-- For `t ⊆ s`, the subtype `↥t` is homeomorphic to the set of points of `↥s` lying in `t`. -/
def subtypeOfSubsetHomeo {α : Type*} [TopologicalSpace α] {s t : Set α} (h : t ⊆ s) :
    ↥t ≃ₜ {x : ↥s // (x : α) ∈ t} where
  toFun x := ⟨⟨x.1, h x.2⟩, x.2⟩
  invFun x := ⟨x.1.1, x.2⟩
  left_inv x := rfl
  right_inv x := rfl
  continuous_toFun := Continuous.subtype_mk
    (f := fun x : ↥t => (⟨x.1, h x.2⟩ : ↥s))
    (Continuous.subtype_mk (f := fun x : ↥t => (x.1 : α)) continuous_subtype_val
      (fun x => h x.2))
    (fun x => x.2)
  continuous_invFun := Continuous.subtype_mk
    (f := fun x : {x : ↥s // (x : α) ∈ t} => (x.1.1 : α))
    (continuous_subtype_val.comp continuous_subtype_val) (fun x => x.2)

/-! ## The collar `λ < 1/2` inside the presenting disjoint union -/

/-- `W`: the part `X × {λ < 1/2}` of the presenting disjoint union
`(X × I) ⊔ Z` of the mapping cylinder, viewed as a subset of the disjoint union. -/
def cylWi (q : C(X, CylZ D Γ ι f)) : Set ((X × unitInterval) ⊕ CylZ D Γ ι f) :=
  Sum.inl '' {z : X × unitInterval | (z.2 : ℝ) < 1/2}

theorem isOpen_cylWi (q : C(X, CylZ D Γ ι f)) : IsOpen (cylWi q) := by
  rw [cylWi]
  exact isOpenMap_inl _ (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const)

theorem cylLam_cylMk'_inl (q : C(X, CylZ D Γ ι f)) (z : X × unitInterval) :
    cylLam q (Quotient.mk'' (Sum.inl z)) = z.2 := by
  rw [show Quotient.mk'' (Sum.inl z) = cylMk q (Sum.inl (z.1, z.2)) from rfl]
  exact cylLam_cylMk_inl q z.1 z.2

theorem cylLam_cylMk'_inr (q : C(X, CylZ D Γ ι f)) (z : CylZ D Γ ι f) :
    cylLam q (Quotient.mk'' (Sum.inr z)) = (1 : unitInterval) := by
  rw [show Quotient.mk'' (Sum.inr z) = cylMk q (Sum.inr z) from rfl]
  exact cylLam_cylMk_inr q z

/-- Every class of the gluing relation meeting `cylWi` is a singleton. -/
theorem eqvGen_eq_of_mem_cylWi (q : C(X, CylZ D Γ ι f)) {a b}
    (ha : a ∈ cylWi q) (h : Relation.EqvGen (cylRel q) a b) : b = a := by
  obtain ⟨z, hzp, rfl⟩ := ha
  have hz : (z.2 : ℝ) < 1/2 := hzp
  have ht : z.2 ≠ 1 := by
    intro h1; rw [h1] at hz; norm_num at hz
  exact (eqvGen_inl_iff q (p := z.1) (t := z.2) ht h).mp
    (rfl : Sum.inl (z.1, z.2) = Sum.inl (z.1, z.2))

/-- **`U₀` is the image of `cylWi`.** -/
theorem cylU₀_eq_cylMk_image (q : C(X, CylZ D Γ ι f)) :
    cylU₀ q = (Quotient.mk'' : ((X × unitInterval) ⊕ CylZ D Γ ι f) → cyl q) '' cylWi q := by
  ext y
  constructor
  · intro hy
    induction y using Quotient.inductionOn with
    | h a =>
      rcases a with ⟨x, t⟩ | z
      · refine ⟨Sum.inl (x, t), ⟨(x, t), ?_, rfl⟩, rfl⟩
        rw [mem_cylU₀_iff] at hy
        exact (mem_cylU₀_cylMk_inl_iff q x t).mp hy
      · exfalso
        rw [mem_cylU₀_iff, cylLam_cylMk'_inr] at hy
        norm_num at hy
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hw
    have hz' : (z.2 : ℝ) < 1/2 := hz
    rw [mem_cylU₀_iff, cylLam_cylMk'_inl]
    exact hz'

/-- **The collar model of `A₂ ∩ U₀` inside `W`**: the points of `cylWi` whose class lies in `A₂`
are exactly the `Sum.inl`-images of `cylSet₁`. -/
theorem cylSet₁_eq_cylWi_inter (q : C(X, CylZ D Γ ι f)) :
    Sum.inl '' cylSet₁ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q
      = cylWi q ∩ ((Quotient.mk'' : ((X × unitInterval) ⊕ CylZ D Γ ι f) → cyl q) ⁻¹'
          cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q) := by
  ext a
  constructor
  · rintro ⟨z, hzp, rfl⟩
    obtain ⟨hz1, hz2⟩ := hzp
    exact ⟨⟨z, hz1, rfl⟩,
      (mem_cylPairA₂_cylMk_inl_iff q z.1 z.2 hz1).mpr hz2⟩
  · rintro ⟨⟨z, hzp, rfl⟩, ha₂⟩
    have hz1 : (z.2 : ℝ) < 1/2 := hzp
    exact ⟨z, ⟨hz1, (mem_cylPairA₂_cylMk_inl_iff q z.1 z.2 hz1).mp ha₂⟩, rfl⟩

/-! ## The collar homeomorphism -/

/-- **The collar model of `U₀A₂`.**  The set `U₀A₂ = {λ < 1/2} ∩ A₂` of the mapping cylinder of
`q` is homeomorphic to its collar model `cylSet₁ = (X × {0}) ∪ (A × (0,1/2))` inside `X × I`,
and this homeomorphism carries the relative part `(A₂ ∩ U₀) ∩ U₁` onto `cylSet₂ = A × (0,1/2)`. -/
theorem collarHomeoA2 (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    ∃ e : ↥(cylU₀A₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q) ≃ₜ
        ↥(cylSet₁ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q),
      (∀ (x : X) (t : unitInterval) (ht : (t : ℝ) < 1/2)
          (hA₂ : Work.Serre.cylMk q (Sum.inl (x, t)) ∈
            cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q),
        e ⟨⟨Work.Serre.cylMk q (Sum.inl (x, t)), hA₂⟩,
            (mem_cylU₀_cylMk_inl_iff q x t).mpr ht⟩
          = ⟨(x, t), ⟨ht, (mem_cylPairA₂_cylMk_inl_iff q x t ht).mp hA₂⟩⟩) ∧
      (∀ y : ↥(cylU₀A₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q),
        y ∈ cylU₀U₁A₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q ↔
          (e y).1 ∈ cylSet₂ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q) := by
  classical
  have hU : (Quotient.mk'' : ((X × unitInterval) ⊕ CylZ D Γ ι f) → cyl q) '' cylWi q
      = cylU₀ q := (cylU₀_eq_cylMk_image q).symm
  obtain ⟨hh, hh_val⟩ := exists_homeo_of_saturated_open
    (Relation.EqvGen.setoid (cylRel q)) (W := cylWi q) (isOpen_cylWi q)
    (fun a b hab ha => (eqvGen_eq_of_mem_cylWi q ha hab).symm ▸ ha)
    (fun a b ha hb hab => (eqvGen_eq_of_mem_cylWi q ha hab).symm)
  let hhU : ↥(cylWi q) ≃ₜ ↥(cylU₀ q) := hh.trans (Homeomorph.setCongr hU)
  have hhU_val : ∀ w : ↥(cylWi q), ((hhU w).1 : cyl q) = Quotient.mk'' w.1 := by
    intro w
    change (((hh.trans (Homeomorph.setCongr hU)) w : ↥(cylU₀ q)) : cyl q) = Quotient.mk'' w.1
    rw [Homeomorph.trans_apply]
    exact hh_val w
  have hsub : (Sum.inl '' cylSet₁ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q)
      ⊆ cylWi q := by
    rw [cylSet₁_eq_cylWi_inter q]; exact Set.inter_subset_left
  have hiff : ∀ w : ↥(cylWi q),
      (w.1 ∈ Sum.inl '' cylSet₁ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q)
        ↔ ((hhU w).1 ∈ cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q) := by
    intro w
    have hL : (w.1 ∈ Sum.inl '' cylSet₁ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q)
        ↔ (w.1 ∈ cylWi q ∧ Quotient.mk'' w.1
            ∈ cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q) := by
      rw [cylSet₁_eq_cylWi_inter q]
      exact Iff.rfl
    rw [hL, hhU_val w]
    exact ⟨fun h => h.2, fun h => ⟨w.2, h⟩⟩
  let e1 : ↥(cylSet₁ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q) ≃ₜ
      ↥((Sum.inl : X × unitInterval → (X × unitInterval) ⊕ CylZ D Γ ι f) ''
        cylSet₁ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q) :=
    Topology.IsEmbedding.inl.homeomorphImage _
  let e2 : ↥((Sum.inl : X × unitInterval → (X × unitInterval) ⊕ CylZ D Γ ι f) ''
        cylSet₁ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q) ≃ₜ
      {w : ↥(cylWi (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q) //
        (w : (X × unitInterval) ⊕ CylZ D Γ ι f)
          ∈ Sum.inl '' cylSet₁ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q} :=
    subtypeOfSubsetHomeo hsub
  let e3 : {w : ↥(cylWi (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q) //
        (w : (X × unitInterval) ⊕ CylZ D Γ ι f)
          ∈ Sum.inl '' cylSet₁ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q} ≃ₜ
      {y : ↥(cylU₀ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q) //
        (y : cyl q) ∈ cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q} :=
    Homeomorph.subtype hhU hiff
  let e4 : {y : ↥(cylU₀ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q) //
        (y : cyl q) ∈ cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q} ≃ₜ
      ↥(cylU₀ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q
        ∩ cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q) :=
    subtypeInterHomeo _ _
  let e5 : ↥(cylU₀ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q
        ∩ cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q) ≃ₜ
      ↥(cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q
        ∩ cylU₀ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q) :=
    Homeomorph.setCongr (Set.inter_comm _ _)
  let e6 : ↥(cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q
        ∩ cylU₀ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q) ≃ₜ
      ↥(cylU₀A₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q) :=
    (subtypeInterHomeo (cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)
      (cylU₀ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q)).symm
  let htotal : ↥(cylSet₁ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q) ≃ₜ
      ↥(cylU₀A₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q) :=
    ((e1.trans e2).trans e3).trans (e4.trans (e5.trans e6))
  have e1_val : ∀ z : ↥(cylSet₁ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q),
      (e1 z).1 = (Sum.inl z.1 : (X × unitInterval) ⊕ CylZ D Γ ι f) := fun z => rfl
  have e2_val : ∀ x : ↥((Sum.inl : X × unitInterval → (X × unitInterval) ⊕ CylZ D Γ ι f) ''
        cylSet₁ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q),
      ((e2 x).1.1 : (X × unitInterval) ⊕ CylZ D Γ ι f) = x.1 := fun x => rfl
  have e3_val : ∀ w : {w : ↥(cylWi (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q) //
        (w : (X × unitInterval) ⊕ CylZ D Γ ι f)
          ∈ Sum.inl '' cylSet₁ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q},
      ((e3 w).1.1 : cyl q) = ((hhU w.1).1 : cyl q) := fun w => rfl
  have e4_val : ∀ y : {y : ↥(cylU₀ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q) //
        (y : cyl q) ∈ cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q},
      ((e4 y).1 : cyl q) = (y.1.1 : cyl q) := fun y => rfl
  have e5_val : ∀ x : ↥(cylU₀ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q
        ∩ cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q),
      ((e5 x).1 : cyl q) = x.1 := fun x => rfl
  have e6_val : ∀ x : ↥(cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q
        ∩ cylU₀ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q),
      ((e6 x).1.1 : cyl q) = x.1 := fun x => rfl
  have htotal_apply : ∀ z : ↥(cylSet₁ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q),
      ((htotal z).1.1 : cyl q) = Quotient.mk'' (Sum.inl z.1) := by
    intro z
    have hz1 : (e1 z).1 = (Sum.inl z.1 : (X × unitInterval) ⊕ CylZ D Γ ι f) := e1_val z
    have hz2 : ((e2 (e1 z)).1.1 : (X × unitInterval) ⊕ CylZ D Γ ι f) = Sum.inl z.1 := by
      rw [e2_val, hz1]
    have hz3 : ((e3 (e2 (e1 z))).1.1 : cyl q) = Quotient.mk'' (Sum.inl z.1) := by
      rw [e3_val (e2 (e1 z)), hhU_val]
      congr 1
    have hz4 : ((e4 (e3 (e2 (e1 z)))).1 : cyl q) = Quotient.mk'' (Sum.inl z.1) := by
      rw [e4_val, hz3]
    have hz5 : ((e5 (e4 (e3 (e2 (e1 z))))).1 : cyl q) = Quotient.mk'' (Sum.inl z.1) := by
      rw [e5_val, hz4]
    have hz6 : ((e6 (e5 (e4 (e3 (e2 (e1 z)))))).1.1 : cyl q)
        = Quotient.mk'' (Sum.inl z.1) := by
      rw [e6_val, hz5]
    dsimp only [htotal]
    simp only [Homeomorph.trans_apply]
    exact hz6
  refine ⟨htotal.symm, ?_, ?_⟩
  · intro x t ht hA₂
    set z : ↥(cylSet₁ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q) :=
      ⟨(x, t), ⟨ht, (mem_cylPairA₂_cylMk_inl_iff q x t ht).mp hA₂⟩⟩ with hzdef
    have hkey : htotal z = (⟨⟨cylMk q (Sum.inl (x, t)), hA₂⟩,
        (mem_cylU₀_cylMk_inl_iff q x t).mpr ht⟩ :
        ↥(cylU₀A₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)) := by
      apply Subtype.ext
      apply Subtype.ext
      exact htotal_apply z
    change htotal.symm (⟨⟨cylMk q (Sum.inl (x, t)), hA₂⟩,
        (mem_cylU₀_cylMk_inl_iff q x t).mpr ht⟩ :
        ↥(cylU₀A₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)) = z
    rw [← hkey]
    exact Homeomorph.symm_apply_apply htotal z
  · intro y
    set z : ↥(cylSet₁ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q) := htotal.symm y
      with hzdef
    have hyz : htotal z = y := by
      rw [hzdef]; exact Homeomorph.apply_symm_apply htotal y
    have hlam : cylLam q (y.1.1 : cyl q) = z.1.2 := by
      have h1 : (y.1.1 : cyl q) = Quotient.mk'' (Sum.inl z.1) := by
        rw [← hyz]
        exact htotal_apply z
      rw [h1, cylLam_cylMk'_inl]
    constructor
    · intro hmem
      have hmem' : 0 < (cylLam q (y.1.1 : cyl q) : ℝ) := hmem
      obtain ⟨hz1, hz2⟩ := z.2
      refine ⟨?_, hz1, ?_⟩
      · rw [← hlam]; exact hmem'
      · rcases hz2 with h0 | hA
        · exfalso
          have hzero : (cylLam q (y.1.1 : cyl q) : ℝ) = 0 := by rw [hlam, h0]; rfl
          linarith
        · exact hA
    · intro hmem
      obtain ⟨h1, -, -⟩ := hmem
      show 0 < (cylLam q (y.1.1 : cyl q) : ℝ)
      rw [hlam]
      exact h1

end

end Work.Serre.DiscPair
