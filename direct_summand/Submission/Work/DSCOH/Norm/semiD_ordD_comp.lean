/-
Area DSCOH (curric-46) — `d² = 0` for the truncated (semi-ordered / ordered) Čech differentials.

The complexes `semiT` (`semiTerm`, `semiD`) and `ordT` (`ordTerm`, `ordD`) of
`Submission/Work/DSCOH/Norm/SemiOrd.lean` are both instances of the following general
construction: fix a family `φ n` of predicates on tuples `Fin (n+1) → ι` which is closed under
deletion of an entry, let

* `gTerm φ n` be the product, over the tuples `y : Fin (n+1) → ι` satisfying `φ n`, of
  `tupleMod P U y = P (⋂_a U (y a))`, and
* `gD φ n : gTerm φ n ⟶ gTerm φ (n+1)` be the alternating sum, over the entries `b` of a tuple
  `x : Fin (n+2) → ι`, of the "delete the `b`-th entry and restrict" map.

Then `gD φ n ≫ gD φ (n+1) = 0`.  The proof is the classical one: expanding the two sums produces
a double sum over pairs `(b, c)`, and the map `(b,c) ↦ (b.succAbove c, c.predAbove b)` — which
swaps the two deleted positions — is a fixed-point-free involution whose terms are opposite
(`Work.DSCOH.Norm.sum_Fin_prod_cancel`).

The two instances are `φ n y := Monotone y` (the semi-ordered complex) and
`φ n y := StrictMono y` (the ordered complex), which is the statement
`Work.DSCOH.Norm.semiD_ordD_comp`.
-/
import Mathlib
import Submission.Work.DSCOH.Norm.SemiOrd
import Submission.Work.DSCOH.Norm.del_del_swap
import Submission.Work.DSCOH.Norm.negOne_pow_succAbove_predAbove
import Submission.Work.DSCOH.Norm.sum_Fin_prod_cancel

namespace Work.DSCOH.Norm

universe u v w

open CategoryTheory Limits Opposite TopologicalSpace
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

variable {X : Type u} [TopologicalSpace X] {A : Type v} [CommRing A] {ι : Type w} [LinearOrder ι]

/-! ## The restriction maps `resDel` -/

/-- `resDel` is the image under the presheaf `P` of the map `opDel` of opens. -/
lemma resDel_eq (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X) {n : ℕ}
    (x : Fin (n + 2) → ι) (b : Fin (n + 2)) :
    resDel P U x b = P.map (opDel U x b).op := by
  rw [resDel]
  congr 1

/-- The composite of two restrictions along successive deletions. -/
lemma resDel_comp (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X) {n : ℕ}
    (z : Fin (n + 3) → ι) (b : Fin (n + 3)) (c : Fin (n + 2)) :
    resDel P U (del z b) c ≫ resDel P U z b = P.map (opDel U z b ≫ opDel U (del z b) c).op := by
  rw [resDel_eq, resDel_eq, ← P.map_comp]
  congr 1

/-! ## The general truncated Čech complex attached to a deletion-closed family of tuples -/

variable [HasProducts (ModuleCat A)]

/-- The `n`-th term: the product over the tuples satisfying `φ n`. -/
noncomputable def gTerm (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X)
    (φ : (n : ℕ) → (Fin (n + 1) → ι) → Prop) (n : ℕ) : ModuleCat A :=
  ∏ᶜ fun x : {y : Fin (n + 1) → ι // φ n y} => tupleMod P U x.val

/-- The projection onto the component of a tuple. -/
noncomputable def gProj (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X)
    (φ : (n : ℕ) → (Fin (n + 1) → ι) → Prop) {n : ℕ} (y : Fin (n + 1) → ι) (hy : φ n y) :
    gTerm P U φ n ⟶ tupleMod P U y :=
  Pi.π (fun x : {y : Fin (n + 1) → ι // φ n y} => tupleMod P U x.val) ⟨y, hy⟩

/-- The `x`-component of the differential: the alternating sum, over the entries `b` of `x`, of
the restriction from the tuple with the `b`-th entry deleted. -/
noncomputable def gS (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X)
    (φ : (n : ℕ) → (Fin (n + 1) → ι) → Prop)
    (hφ : ∀ {n : ℕ} (x : Fin (n + 2) → ι) (b : Fin (n + 2)), φ (n + 1) x → φ n (del x b))
    (n : ℕ) (x : {y : Fin (n + 2) → ι // φ (n + 1) y}) :
    gTerm P U φ n ⟶ tupleMod P U x.val :=
  ∑ b : Fin (n + 2), (-1 : ℤ) ^ (b : ℕ) •
    (gProj P U φ (del x.val b) (hφ x.val b x.property) ≫ resDel P U x.val b)

/-- The differential of the truncated Čech complex: its `x`-component is `gS`. -/
noncomputable def gD (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X)
    (φ : (n : ℕ) → (Fin (n + 1) → ι) → Prop)
    (hφ : ∀ {n : ℕ} (x : Fin (n + 2) → ι) (b : Fin (n + 2)), φ (n + 1) x → φ n (del x b))
    (n : ℕ) : gTerm P U φ n ⟶ gTerm P U φ (n + 1) :=
  Pi.lift fun x => gS P U φ hφ n x

/-- The `p`-component of the double sum: delete the entries `p.1` and `p.2` and restrict. -/
noncomputable def gRest (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X)
    (φ : (n : ℕ) → (Fin (n + 1) → ι) → Prop)
    (hφ : ∀ {n : ℕ} (x : Fin (n + 2) → ι) (b : Fin (n + 2)), φ (n + 1) x → φ n (del x b))
    (n : ℕ) (z : {y : Fin (n + 3) → ι // φ (n + 2) y}) (p : Fin (n + 3) × Fin (n + 2)) :
    gTerm P U φ n ⟶ tupleMod P U z.val :=
  gProj P U φ (del (del z.val p.1) p.2)
      (hφ (del z.val p.1) p.2 (hφ z.val p.1 z.property)) ≫
    (resDel P U (del z.val p.1) p.2 ≫ resDel P U z.val p.1)

/-- The component formula for the differential. -/
lemma gD_comp_gProj (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X)
    (φ : (n : ℕ) → (Fin (n + 1) → ι) → Prop)
    (hφ : ∀ {n : ℕ} (x : Fin (n + 2) → ι) (b : Fin (n + 2)), φ (n + 1) x → φ n (del x b))
    (n : ℕ) (y : Fin (n + 2) → ι) (hy : φ (n + 1) y) :
    gD P U φ hφ n ≫ gProj P U φ y hy = gS P U φ hφ n ⟨y, hy⟩ := by
  rw [gD, gProj]
  exact Pi.lift_comp_π _ _

/-- The projections at two equal tuples are compatible with the restrictions. -/
lemma gProj_map_eq (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X)
    (φ : (n : ℕ) → (Fin (n + 1) → ι) → Prop) {n : ℕ} {y₁ y₂ : Fin (n + 1) → ι} (h : y₁ = y₂)
    (hy₁ : φ n y₁) (hy₂ : φ n y₂) {V : Opens X} (β₁ : V ⟶ tupleOp U y₁)
    (β₂ : V ⟶ tupleOp U y₂) :
    gProj P U φ y₁ hy₁ ≫ P.map β₁.op = gProj P U φ y₂ hy₂ ≫ P.map β₂.op := by
  subst h
  rw [Subsingleton.elim β₁ β₂]

/-- The double restriction does not depend on the order in which the two entries are deleted. -/
lemma gRest_swap (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X)
    (φ : (n : ℕ) → (Fin (n + 1) → ι) → Prop)
    (hφ : ∀ {n : ℕ} (x : Fin (n + 2) → ι) (b : Fin (n + 2)), φ (n + 1) x → φ n (del x b))
    (n : ℕ) (z : {y : Fin (n + 3) → ι // φ (n + 2) y}) (p : Fin (n + 3) × Fin (n + 2)) :
    gRest P U φ hφ n z (p.1.succAbove p.2, p.2.predAbove p.1) = gRest P U φ hφ n z p := by
  simp only [gRest]
  rw [resDel_comp, resDel_comp]
  exact gProj_map_eq P U φ (del_del_swap z.val p.1 p.2) _ _ _ _

/-- One term of the expansion of `gD ≫ gS`: the differential applied to the `b`-th summand of
`gS` is the `b`-th component of `gD n` (which is `gS`) followed by the restriction. -/
lemma gD_comp_gRest_single (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X)
    (φ : (n : ℕ) → (Fin (n + 1) → ι) → Prop)
    (hφ : ∀ {n : ℕ} (x : Fin (n + 2) → ι) (b : Fin (n + 2)), φ (n + 1) x → φ n (del x b))
    (n : ℕ) (z : {y : Fin (n + 3) → ι // φ (n + 2) y}) (b : Fin (n + 3)) :
    gD P U φ hφ n ≫
        (gProj P U φ (del z.val b) (hφ z.val b z.property) ≫ resDel P U z.val b)
      = gS P U φ hφ n ⟨del z.val b, hφ z.val b z.property⟩ ≫ resDel P U z.val b := by
  rw [← Category.assoc, gD_comp_gProj]

/-- **The double sum expansion of the component of `d²`.**  Expanding `(gD n ≫ gD (n+1))` at a
tuple `z : Fin (n+3) → ι` gives the double sum over pairs `p = (p.1, p.2)` of the deletion of
the two entries `p.1` and `p.2` (with the signs kept separate). -/
lemma gD_gD_gProj (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X)
    (φ : (n : ℕ) → (Fin (n + 1) → ι) → Prop)
    (hφ : ∀ {n : ℕ} (x : Fin (n + 2) → ι) (b : Fin (n + 2)), φ (n + 1) x → φ n (del x b))
    (n : ℕ) (z : {y : Fin (n + 3) → ι // φ (n + 2) y}) :
    (gD P U φ hφ n ≫ gD P U φ hφ (n + 1)) ≫ gProj P U φ z.val z.property
      = ∑ p : Fin (n + 3) × Fin (n + 2),
          (-1 : ℤ) ^ (p.1 : ℕ) • ((-1 : ℤ) ^ (p.2 : ℕ) • gRest P U φ hφ n z p) := by
  rw [Category.assoc, gD_comp_gProj]
  simp only [gS, Preadditive.comp_sum, Preadditive.comp_zsmul, gD_comp_gRest_single,
    Preadditive.sum_comp, Preadditive.zsmul_comp, Finset.smul_sum]
  rw [← Finset.sum_product', Finset.univ_product_univ]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [gRest, Category.assoc]

/-- The expansion of `d²` in the form matching the projections `Pi.π` of the product. -/
lemma gD_gD_piπ (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X)
    (φ : (n : ℕ) → (Fin (n + 1) → ι) → Prop)
    (hφ : ∀ {n : ℕ} (x : Fin (n + 2) → ι) (b : Fin (n + 2)), φ (n + 1) x → φ n (del x b))
    (n : ℕ) (z : {y : Fin (n + 3) → ι // φ (n + 2) y}) :
    (gD P U φ hφ n ≫ gD P U φ hφ (n + 1)) ≫
        Pi.π (fun x : {y : Fin (n + 3) → ι // φ (n + 2) y} => tupleMod P U x.val) z
      = ∑ p : Fin (n + 3) × Fin (n + 2),
          (-1 : ℤ) ^ (p.1 : ℕ) • ((-1 : ℤ) ^ (p.2 : ℕ) • gRest P U φ hφ n z p) := by
  rw [show Pi.π (fun x : {y : Fin (n + 3) → ι // φ (n + 2) y} => tupleMod P U x.val) z
      = gProj P U φ z.val z.property from rfl]
  exact gD_gD_gProj P U φ hφ n z

/-- The summand of the expansion is antisymmetric under the involution which swaps the two
deleted positions: this is where the two signs cancel. -/
lemma gRest_antisym (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X)
    (φ : (n : ℕ) → (Fin (n + 1) → ι) → Prop)
    (hφ : ∀ {n : ℕ} (x : Fin (n + 2) → ι) (b : Fin (n + 2)), φ (n + 1) x → φ n (del x b))
    (n : ℕ) (z : {y : Fin (n + 3) → ι // φ (n + 2) y}) (p : Fin (n + 3) × Fin (n + 2)) :
    (-1 : ℤ) ^ (p.1.succAbove p.2).val •
        ((-1 : ℤ) ^ (p.2.predAbove p.1).val •
          gRest P U φ hφ n z (p.1.succAbove p.2, p.2.predAbove p.1))
      = -((-1 : ℤ) ^ p.1.val • ((-1 : ℤ) ^ p.2.val • gRest P U φ hφ n z p)) := by
  rw [gRest_swap]
  simp only [smul_smul]
  rw [negOne_pow_succAbove_predAbove, neg_smul]

/-- **The truncated Čech differential squares to zero.** -/
theorem gD_comp (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X)
    (φ : (n : ℕ) → (Fin (n + 1) → ι) → Prop)
    (hφ : ∀ {n : ℕ} (x : Fin (n + 2) → ι) (b : Fin (n + 2)), φ (n + 1) x → φ n (del x b))
    (n : ℕ) : gD P U φ hφ n ≫ gD P U φ hφ (n + 1) = 0 := by
  apply Pi.hom_ext
  intro z
  rw [zero_comp, gD_gD_piπ]
  exact sum_Fin_prod_cancel _ fun p => gRest_antisym P U φ hφ n z p

/-- The alternating sums of "delete one entry and restrict" defined in `Work.DSCOH.Norm`
square to zero, both on the nondecreasing tuples and on the strictly increasing tuples.
This is the standard `d² = 0` computation of the Čech differential, in the truncated
(sub-index-set) situation; it makes `semiTerm`/`semiD` and `ordTerm`/`ordD` into cochain
complexes. -/
theorem semiD_ordD_comp {X : Type u} [TopologicalSpace X] {A : Type v} [CommRing A]
    {ι : Type w} [Fintype ι] [LinearOrder ι]
    [CategoryTheory.Limits.HasProducts (ModuleCat A)]
    (P : Opposite (TopologicalSpace.Opens X) ⥤ ModuleCat A)
    (U : ι → TopologicalSpace.Opens X) (n : ℕ) :
    (Work.DSCOH.Norm.semiD P U n ≫ Work.DSCOH.Norm.semiD P U (n + 1) = 0) ∧
      (Work.DSCOH.Norm.ordD P U n ≫ Work.DSCOH.Norm.ordD P U (n + 1) = 0) := by
  refine ⟨?_, ?_⟩
  · exact gD_comp P U (fun _ x => Monotone x) (fun x b hx => monotone_del x b hx) n
  · exact gD_comp P U (fun _ x => StrictMono x) (fun x b hx => strictMono_del x b hx) n

end Work.DSCOH.Norm
