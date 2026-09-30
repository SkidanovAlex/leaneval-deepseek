/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.Subdivision.LocalIso

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Naturality of the subdivision chain under an isomorphism of local structure

The subdivision chain `subdivCell P n e` of a cell `e` is defined by the cone
recursion from the face lattice `Iic e`, the dimension function, and the incidence
numbers of the facets of `e`.  All of these are preserved by an isomorphism of
local structures `φ : LocalIso P e f`, and the vertexwise map `starLM φ` on the
chains of the order complex intertwines the cones.  The resulting naturality
statement is

`starLM φ n (subdivCell P n e) = subdivCell P n f`  (`starLM_subdivCell`),

proved here by strong induction on `n`.  The ingredients are

* `starLM_coneLM` — the cone `cone_e` is natural in `φ`;
* `LocalIso.restrict` — the restriction of a local isomorphism to a face `x ≤ e`,
  again a local isomorphism (of `x` and `φ x`), so that the induction hypothesis
  applies to the facets of `e`;
* `facetMap` — the induced bijection of the facets of `e` with those of `f`, with
  `starLM_facetsSum` the resulting identity of the subdivided boundaries.
-/

namespace Work.Subdivision

universe u

noncomputable section

namespace PolyCW

variable (P : PolyCW.{u})
variable {e f : P.Cell}

/-! ### The vertexwise map on `snoc` -/

/-- The vertexwise map of an order isomorphism sends the `0`-simplex at `e` to the
`0`-simplex at `φ e`. -/
theorem Simplex.congrIic_vertex {e f : P.Cell} (φ : Set.Iic e ≃o Set.Iic f)
    (h : ∀ i, Simplex.vertex e i ≤ e) :
    Simplex.congrIic P φ (Simplex.vertex e) h =
      Simplex.vertex ((φ ⟨e, le_rfl⟩ : Set.Iic f).1) := by
  apply Simplex.ext
  intro i
  have h1 : (⟨(Simplex.vertex e).toFun i, h i⟩ : Set.Iic e) = ⟨e, le_rfl⟩ := Subtype.ext rfl
  rw [Simplex.congrIic_apply, h1]
  rfl

/-- The vertexwise map of an order isomorphism sends the cone on `σ` with apex `e`
to the cone on the image of `σ` with apex `f`. -/
theorem Simplex.congrIic_snoc {e f : P.Cell} (φ : Set.Iic e ≃o Set.Iic f)
    (he : (φ ⟨e, le_rfl⟩ : Set.Iic f).1 = f) {k : ℕ}
    (σ : Simplex P.Cell k) (hσ : ∀ i, σ i < e)
    (h : ∀ i, Simplex.snoc σ e hσ i ≤ e)
    (h' : ∀ i, Simplex.congrIic P φ σ (fun i => le_of_lt (hσ i)) i < f) :
    Simplex.congrIic P φ (Simplex.snoc σ e hσ) h
      = Simplex.snoc (Simplex.congrIic P φ σ (fun i => le_of_lt (hσ i))) f h' := by
  apply Simplex.ext
  intro i
  induction i using Fin.lastCases with
  | last =>
    have h1 : (⟨(Simplex.snoc σ e hσ).toFun (Fin.last (k+1)), h (Fin.last (k+1))⟩ : Set.Iic e)
        = ⟨e, le_rfl⟩ := Subtype.ext (Simplex.snoc_apply_last σ e hσ)
    rw [Simplex.congrIic_apply, h1, Simplex.snoc_apply_last, he]
  | cast j =>
    have h1 : (⟨(Simplex.snoc σ e hσ).toFun j.castSucc, h j.castSucc⟩ : Set.Iic e)
        = ⟨σ.toFun j, le_of_lt (hσ j)⟩ := Subtype.ext (Simplex.snoc_apply_castSucc σ e hσ j)
    rw [Simplex.congrIic_apply, h1, Simplex.snoc_apply_castSucc, Simplex.congrIic_apply]

/-- **The cone is natural**: for a chain supported strictly below `e`, the
vertexwise map of an order isomorphism interchanges the cone with apex `e` and the
cone with apex `f`. -/
theorem starLM_coneLM {e f : P.Cell} (φ : Set.Iic e ≃o Set.Iic f)
    (he : (φ ⟨e, le_rfl⟩ : Set.Iic f).1 = f) (n : ℕ) :
    ∀ z : chainMod P.Cell n, z ∈ belowSub P e n →
      starLM P φ (n+1) (coneLM P e n z) = coneLM P f n (starLM P φ n z) := by
  have hgen : ∀ (σ : Simplex P.Cell n) (hσ : ∀ i, σ i < e),
      starLM P φ (n+1) (coneLM P e n (Finsupp.single σ 1))
        = coneLM P f n (starLM P φ n (Finsupp.single σ 1)) := by
    intro σ hσ
    have hσle : ∀ i, σ i ≤ e := fun i => le_of_lt (hσ i)
    have hle : ∀ i, Simplex.snoc σ e hσ i ≤ e := by
      intro i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · rw [Simplex.snoc_apply_castSucc]; exact le_of_lt (hσ j)
      · rw [Simplex.snoc_apply_last]
    have hlt : ∀ i, Simplex.congrIic P φ σ hσle i < f := by
      intro i
      have h2 : (φ ⟨σ i, hσle i⟩ : Set.Iic f).1 < (φ ⟨e, le_rfl⟩ : Set.Iic f).1 :=
        φ.strictMono (show (⟨σ i, hσle i⟩ : Set.Iic e) < ⟨e, le_rfl⟩ from hσ i)
      rw [he] at h2
      rw [Simplex.congrIic_apply]
      exact h2
    rw [coneLM_single P e n σ hσ, starLM_single P φ (Simplex.snoc σ e hσ) hle,
      starLM_single P φ σ hσle,
      coneLM_single P f n (Simplex.congrIic P φ σ hσle) hlt,
      Simplex.congrIic_snoc P φ he σ hσ hle hlt]
  have hker : belowSub P e n ≤ LinearMap.ker
      ((starLM P φ (n+1)).comp (coneLM P e n) - (coneLM P f n).comp (starLM P φ n)) := by
    rw [belowSub_le_iff]
    intro σ hσ
    rw [LinearMap.mem_ker]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply]
    rw [hgen σ hσ, sub_self]
  intro z hz
  have h := hker hz
  rw [LinearMap.mem_ker] at h
  simp only [LinearMap.sub_apply, LinearMap.comp_apply] at h
  rw [sub_eq_zero] at h
  exact h

/-! ### Restricting a local isomorphism to a face -/

namespace LocalIso

variable {e f : P.Cell}

/-- The underlying function of the restriction of a local isomorphism to a face. -/
def restrictFun (φ : LocalIso P e f) (x : Set.Iic e) :
    Set.Iic x.1 → Set.Iic (φ.toOrderIso x).1 :=
  fun y => ⟨(φ.toOrderIso ⟨y.1, le_trans y.2 x.2⟩).1,
    Subtype.coe_le_coe.mpr (φ.toOrderIso.monotone (Subtype.mk_le_mk.mpr y.2))⟩

@[simp] theorem restrictFun_apply (φ : LocalIso P e f) (x : Set.Iic e) (y : Set.Iic x.1) :
    (restrictFun P φ x y).1 = (φ.toOrderIso ⟨y.1, le_trans y.2 x.2⟩).1 := rfl

/-- The inverse of `restrictFun`. -/
def restrictInv (φ : LocalIso P e f) (x : Set.Iic e) :
    Set.Iic (φ.toOrderIso x).1 → Set.Iic x.1 :=
  fun z => ⟨(φ.toOrderIso.symm ⟨z.1, le_trans z.2 (φ.toOrderIso x).2⟩).1,
    Subtype.coe_le_coe.mpr (by
      calc φ.toOrderIso.symm ⟨z.1, le_trans z.2 (φ.toOrderIso x).2⟩
            ≤ φ.toOrderIso.symm (φ.toOrderIso x) :=
            φ.toOrderIso.symm.monotone (Subtype.mk_le_mk.mpr z.2)
        _ = x := OrderIso.symm_apply_apply φ.toOrderIso x)⟩

@[simp] theorem restrictInv_apply (φ : LocalIso P e f) (x : Set.Iic e)
    (z : Set.Iic (φ.toOrderIso x).1) :
    (restrictInv P φ x z).1 =
      (φ.toOrderIso.symm ⟨z.1, le_trans z.2 (φ.toOrderIso x).2⟩).1 := rfl

theorem restrictFun_restrictInv (φ : LocalIso P e f) (x : Set.Iic e)
    (z : Set.Iic (φ.toOrderIso x).1) : restrictFun P φ x (restrictInv P φ x z) = z := by
  apply Subtype.ext
  have h1 : (⟨(restrictInv P φ x z).1, le_trans (restrictInv P φ x z).2 x.2⟩ : Set.Iic e)
      = φ.toOrderIso.symm ⟨z.1, le_trans z.2 (φ.toOrderIso x).2⟩ := Subtype.ext rfl
  rw [restrictFun_apply, h1, OrderIso.apply_symm_apply]

theorem restrictInv_restrictFun (φ : LocalIso P e f) (x : Set.Iic e)
    (y : Set.Iic x.1) : restrictInv P φ x (restrictFun P φ x y) = y := by
  apply Subtype.ext
  have h1 : (⟨(restrictFun P φ x y).1, le_trans (restrictFun P φ x y).2 (φ.toOrderIso x).2⟩ :
      Set.Iic f) = φ.toOrderIso ⟨y.1, le_trans y.2 x.2⟩ := Subtype.ext rfl
  rw [restrictInv_apply, h1, OrderIso.symm_apply_apply]

theorem restrictFun_le_iff (φ : LocalIso P e f) (x : Set.Iic e) (a b : Set.Iic x.1) :
    restrictFun P φ x a ≤ restrictFun P φ x b ↔ a ≤ b := by
  have h1 : (restrictFun P φ x a ≤ restrictFun P φ x b) ↔
      (φ.toOrderIso ⟨a.1, le_trans a.2 x.2⟩ ≤ φ.toOrderIso ⟨b.1, le_trans b.2 x.2⟩) :=
    Iff.rfl
  rw [h1]
  exact φ.toOrderIso.le_iff_le

/-- **The restriction of a local isomorphism to a face**: if `x ≤ e` then `φ`
restricts to an isomorphism of the local structures of `x` and `φ x`. -/
def restrict (φ : LocalIso P e f) (x : Set.Iic e) :
    LocalIso P x.1 (φ.toOrderIso x).1 where
  toOrderIso :=
    { toFun := restrictFun P φ x
      invFun := restrictInv P φ x
      left_inv := fun y => restrictInv_restrictFun P φ x y
      right_inv := fun z => restrictFun_restrictInv P φ x z
      map_rel_iff' := by intro a b; exact restrictFun_le_iff P φ x a b }
  map_top := congrArg (fun s : Set.Iic e => (φ.toOrderIso s).1) (Subtype.ext rfl)
  dim_eq := fun y => φ.dim_eq ⟨y.1, le_trans y.2 x.2⟩
  inc_eq := fun y z hz => φ.inc_eq ⟨y.1, le_trans y.2 x.2⟩ hz

end LocalIso

/-- On chains supported below a face `x ≤ e`, the vertexwise map of `φ` agrees with
the vertexwise map of the restriction of `φ` to `x`. -/
theorem starLM_restrict_apply {e f : P.Cell} (φ : LocalIso P e f) (x : Set.Iic e) (k : ℕ)
    {z : chainMod P.Cell k} (hz : z ∈ leSub P x.1 k) :
    starLM P φ.toOrderIso k z = starLM P (LocalIso.restrict P φ x).toOrderIso k z := by
  refine Submodule.span_induction (p := fun z _ => starLM P φ.toOrderIso k z
      = starLM P (LocalIso.restrict P φ x).toOrderIso k z) ?_ ?_ ?_ ?_ hz
  · rintro y ⟨σ, hσ, rfl⟩
    rw [starLM_single P φ.toOrderIso σ (fun i => le_trans (hσ i) x.2),
      starLM_single P (LocalIso.restrict P φ x).toOrderIso σ hσ]
    congr 1
  · simp
  · intro y z hy hz ihy ihz
    rw [map_add, map_add, ihy, ihz]
  · intro a y hy ih
    rw [map_smul, map_smul, ih]

/-! ### The induced bijection of the facets -/

/-- The image of a facet of `e` under a local isomorphism is a facet of `f`. -/
theorem facetMap_mem {e f : P.Cell} (φ : LocalIso P e f)
    (x : {x : P.Cell // x ∈ P.facets e}) :
    (φ.toOrderIso ⟨x.1, le_of_lt (P.facet_lt x.2)⟩).1 ∈ P.facets f := by
  rw [P.mem_facets]
  refine ⟨?_, ?_⟩
  · have h2 : (φ.toOrderIso ⟨x.1, le_of_lt (P.facet_lt x.2)⟩).1 <
        (φ.toOrderIso ⟨e, le_rfl⟩).1 :=
      φ.toOrderIso.strictMono
        (show (⟨x.1, le_of_lt (P.facet_lt x.2)⟩ : Set.Iic e) < ⟨e, le_rfl⟩ from
          P.facet_lt x.2)
    rwa [φ.map_top] at h2
  · have h4 : P.dim (φ.toOrderIso ⟨x.1, le_of_lt (P.facet_lt x.2)⟩).1 = P.dim x.1 :=
      φ.dim_eq ⟨x.1, le_of_lt (P.facet_lt x.2)⟩
    have h5 : P.dim f = P.dim e := by
      have h := φ.dim_eq ⟨e, le_rfl⟩
      rwa [φ.map_top] at h
    have h6 : P.dim e = P.dim x.1 + 1 := ((P.mem_facets e x.1).1 x.2).2
    omega

/-- **The bijection of the facets induced by a local isomorphism.** -/
def facetMap {e f : P.Cell} (φ : LocalIso P e f) (x : {x : P.Cell // x ∈ P.facets e}) :
    {y : P.Cell // y ∈ P.facets f} :=
  ⟨(φ.toOrderIso ⟨x.1, le_of_lt (P.facet_lt x.2)⟩).1, facetMap_mem P φ x⟩

@[simp] theorem facetMap_val {e f : P.Cell} (φ : LocalIso P e f)
    (x : {x : P.Cell // x ∈ P.facets e}) :
    (facetMap P φ x).1 = (φ.toOrderIso ⟨x.1, le_of_lt (P.facet_lt x.2)⟩).1 := rfl

theorem facetMap_injective {e f : P.Cell} (φ : LocalIso P e f) :
    Function.Injective (facetMap P φ) := by
  intro a b hab
  have h1 : (φ.toOrderIso ⟨a.1, le_of_lt (P.facet_lt a.2)⟩).1 =
      (φ.toOrderIso ⟨b.1, le_of_lt (P.facet_lt b.2)⟩).1 :=
    congrArg (fun s : {y : P.Cell // y ∈ P.facets f} => s.1) hab
  have h2 : (⟨a.1, le_of_lt (P.facet_lt a.2)⟩ : Set.Iic e) =
      ⟨b.1, le_of_lt (P.facet_lt b.2)⟩ :=
    φ.toOrderIso.injective (Subtype.ext h1)
  exact Subtype.ext (congrArg (fun s : Set.Iic e => s.1) h2)

theorem facetMap_surjective {e f : P.Cell} (φ : LocalIso P e f) :
    Function.Surjective (facetMap P φ) := by
  intro y
  obtain ⟨ya, hy⟩ := y
  have hmem : (φ.toOrderIso.symm ⟨ya, le_of_lt (P.facet_lt hy)⟩).1 ∈ P.facets e := by
    rw [P.mem_facets]
    refine ⟨?_, ?_⟩
    · have h2 : φ.toOrderIso.symm ⟨ya, le_of_lt (P.facet_lt hy)⟩ <
          φ.toOrderIso.symm (φ.toOrderIso ⟨e, le_rfl⟩) :=
        φ.toOrderIso.symm.strictMono (show (⟨ya, le_of_lt (P.facet_lt hy)⟩ : Set.Iic f) <
          φ.toOrderIso ⟨e, le_rfl⟩ from by
            show ya < (φ.toOrderIso ⟨e, le_rfl⟩).1
            rw [φ.map_top]
            exact P.facet_lt hy)
      rw [OrderIso.symm_apply_apply] at h2
      exact h2
    · have h4 : P.dim (φ.toOrderIso.symm ⟨ya, le_of_lt (P.facet_lt hy)⟩).1 = P.dim ya := by
        have h := φ.dim_eq (φ.toOrderIso.symm ⟨ya, le_of_lt (P.facet_lt hy)⟩)
        rw [OrderIso.apply_symm_apply] at h
        exact h.symm
      have h5 : P.dim f = P.dim e := by
        have h := φ.dim_eq ⟨e, le_rfl⟩
        rwa [φ.map_top] at h
      have h6 : P.dim f = P.dim ya + 1 := ((P.mem_facets f ya).1 hy).2
      omega
  refine ⟨⟨(φ.toOrderIso.symm ⟨ya, le_of_lt (P.facet_lt hy)⟩).1, hmem⟩, ?_⟩
  apply Subtype.ext
  have h1 : (⟨(φ.toOrderIso.symm ⟨ya, le_of_lt (P.facet_lt hy)⟩).1,
      le_of_lt (P.facet_lt hmem)⟩ : Set.Iic e) =
      φ.toOrderIso.symm ⟨ya, le_of_lt (P.facet_lt hy)⟩ := Subtype.ext rfl
  show (φ.toOrderIso ⟨(φ.toOrderIso.symm ⟨ya, le_of_lt (P.facet_lt hy)⟩).1,
    le_of_lt (P.facet_lt hmem)⟩).1 = ya
  rw [h1, OrderIso.apply_symm_apply]

/-- The bijection of facets is compatible with the incidence numbers. -/
theorem facetMap_inc {e f : P.Cell} (φ : LocalIso P e f)
    (x : {x : P.Cell // x ∈ P.facets e}) : P.inc e x.1 = P.inc f (facetMap P φ x).1 := by
  have h := φ.inc_eq ⟨e, le_rfl⟩ x.2
  rw [φ.map_top] at h
  have h1 : (⟨x.1, le_trans (le_of_lt (P.facet_lt x.2)) le_rfl⟩ : Set.Iic e) =
      ⟨x.1, le_of_lt (P.facet_lt x.2)⟩ := Subtype.ext rfl
  rw [h, h1]
  rfl

/-- **The subdivided boundary is natural**: the vertexwise map sends the subdivided
boundary of `e` to the subdivided boundary of `f`. -/
theorem starLM_facetsSum {e f : P.Cell} (φ : LocalIso P e f) (n : ℕ) (he : P.dim e = n + 1)
    (hf : P.dim f = n + 1)
    (ih : ∀ (k : ℕ), k < n + 1 → ∀ (e' : {a : P.Cell // P.dim a = k}) (f' : P.Cell)
      (φ' : LocalIso P e'.1 f') (hf' : P.dim f' = k),
      starLM P φ'.toOrderIso k (subdivCell P k e') = subdivCell P k ⟨f', hf'⟩) :
    starLM P φ.toOrderIso n (∑ x ∈ (P.facets e).attach,
        P.inc e x.1 • subdivCell P n (facetIndex n e he x))
      = ∑ y ∈ (P.facets f).attach, P.inc f y.1 • subdivCell P n (facetIndex n f hf y) := by
  have hpt : ∀ x : {a : P.Cell // a ∈ P.facets e},
      P.inc e x.1 • starLM P φ.toOrderIso n (subdivCell P n (facetIndex n e he x))
        = P.inc f (facetMap P φ x).1 • subdivCell P n (facetIndex n f hf (facetMap P φ x)) := by
    intro x
    obtain ⟨xa, hx⟩ := x
    have hxlt : xa < e := ((P.mem_facets e xa).1 hx).1
    have hxdim : P.dim xa = n := by
      have h1 : P.dim e = P.dim xa + 1 := ((P.mem_facets e xa).1 hx).2
      omega
    have hf' : P.dim (φ.toOrderIso ⟨xa, le_of_lt hxlt⟩).1 = n := by
      rw [φ.dim_eq]; exact hxdim
    have h1 : starLM P φ.toOrderIso n (subdivCell P n (facetIndex n e he ⟨xa, hx⟩))
        = starLM P (LocalIso.restrict P φ ⟨xa, le_of_lt hxlt⟩).toOrderIso n
            (subdivCell P n (facetIndex n e he ⟨xa, hx⟩)) :=
      starLM_restrict_apply P φ ⟨xa, le_of_lt hxlt⟩ n
        (subdivCell_mem_leSub P n (facetIndex n e he ⟨xa, hx⟩))
    have h2 : starLM P (LocalIso.restrict P φ ⟨xa, le_of_lt hxlt⟩).toOrderIso n
        (subdivCell P n (facetIndex n e he ⟨xa, hx⟩))
        = subdivCell P n ⟨(φ.toOrderIso ⟨xa, le_of_lt hxlt⟩).1, hf'⟩ := by
      rw [subdivCell_heq_subtype (P := P) (a := facetIndex n e he ⟨xa, hx⟩)
        (b := ⟨xa, hxdim⟩) rfl]
      exact ih n (by omega) ⟨xa, hxdim⟩ (φ.toOrderIso ⟨xa, le_of_lt hxlt⟩).1
        (LocalIso.restrict P φ ⟨xa, le_of_lt hxlt⟩) hf'
    have h3 : subdivCell P n ⟨(φ.toOrderIso ⟨xa, le_of_lt hxlt⟩).1, hf'⟩
        = subdivCell P n (facetIndex n f hf (facetMap P φ ⟨xa, hx⟩)) :=
      subdivCell_heq_subtype (P := P) rfl
    rw [h1, h2, h3, facetMap_inc P φ ⟨xa, hx⟩]
  rw [map_sum]
  rw [Finset.sum_congr rfl (fun x _ =>
    map_smul (starLM P φ.toOrderIso n) (P.inc e x.1) (subdivCell P n (facetIndex n e he x)))]
  refine Finset.sum_bij (fun x _ => facetMap P φ x) (fun x _ => Finset.mem_attach _ _)
    (fun a₁ _ a₂ _ h => by rw [facetMap_injective P φ h])
    (fun b _ => by
      obtain ⟨a, ha⟩ := facetMap_surjective P φ b
      exact ⟨a, Finset.mem_attach _ _, ha⟩)
    (fun a _ => hpt a)

/-! ### Naturality of the subdivision chain -/

/-- **Naturality of the subdivision chain** under an isomorphism of local
structures, by strong induction on the dimension. -/
theorem starLM_subdivCell_aux :
    ∀ n (e : {e : P.Cell // P.dim e = n}) (f : P.Cell) (φ : LocalIso P e.1 f)
      (hf : P.dim f = n),
      starLM P φ.toOrderIso n (subdivCell P n e) = subdivCell P n ⟨f, hf⟩ := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih e f φ hf
  rcases n with _ | m
  · rw [subdivCell_zero (P := P) e, subdivCell_zero (P := P) ⟨f, hf⟩]
    rw [starLM_single P φ.toOrderIso (Simplex.vertex e.1) (fun i => le_rfl)]
    congr 1
    rw [Simplex.congrIic_vertex P φ.toOrderIso (fun i => le_rfl), φ.map_top]
  · rw [subdivCell_succ_eq (P := P) m e, map_smul]
    have hcone := starLM_coneLM P φ.toOrderIso φ.map_top m
      (∑ x ∈ (P.facets e.1).attach,
        P.inc e.1 x.1 • subdivCell P m (facetIndex m e.1 e.2 x))
      (facetsSum_mem_belowSub P m e.1 e.2)
    rw [hcone, subdivCell_succ_eq (P := P) m ⟨f, hf⟩,
      starLM_facetsSum P φ m e.2 hf (fun k hk => ih k hk)]

end PolyCW

theorem starLM_subdivCell (P : Work.Subdivision.PolyCW) (n : ℕ)
    (e : {e : P.Cell // P.dim e = n}) (f : P.Cell)
    (φ : Work.Subdivision.PolyCW.LocalIso P e.1 f) (hf : P.dim f = n) :
    Work.Subdivision.PolyCW.LocalIso.starLM P φ n (Work.Subdivision.PolyCW.subdivCell P n e) =
      Work.Subdivision.PolyCW.subdivCell P n ⟨f, hf⟩ :=
  PolyCW.starLM_subdivCell_aux P n e f φ hf

end

end Work.Subdivision
