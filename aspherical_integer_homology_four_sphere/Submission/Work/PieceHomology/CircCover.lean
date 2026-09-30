/-
# The two-piece cover of the circle, and the contractible-factor product isomorphism

This file collects the point-set facts about the cover of `AddCircle 1 = ℝ/ℤ` by the two open sets

* `cU = ℝ/ℤ ∖ {π(-1/2)}`,
* `cV = ℝ/ℤ ∖ {π(-1/4)}`,

whose intersection is the disjoint union of the two open arcs `cA1 = π '' (-1/4, 1/2)` and
`cA2 = π '' (1/2, 3/4)`.  Each of the four pieces is homeomorphic to an open interval (through the
quotient map as an open partial homeomorphism), hence contractible; this is what makes
`X × (piece) → X` a homotopy equivalence.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

open Set Topology ContinuousMap
open CategoryTheory CategoryTheory.Limits

namespace Work.PieceHomology

noncomputable section

/-- The circle `ℝ/ℤ`. -/
abbrev Circ : Type := AddCircle (1 : ℝ)

/-- The open interval `(-1/2, 1/2)`, written in the form `(a, a+1)`. -/
abbrev J1 : Set ℝ := Set.Ioo (-1/2) (-1/2 + 1)

/-- The open interval `(-1/4, 3/4)`, written in the form `(a, a+1)`. -/
abbrev J2 : Set ℝ := Set.Ioo (-1/4) (-1/4 + 1)

/-- The first arc of the intersection. -/
abbrev K1 : Set ℝ := Set.Ioo (-1/4) (1/2)

/-- The second arc of the intersection. -/
abbrev K2 : Set ℝ := Set.Ioo (1/2) (3/4)

/-- The base point `π 0` of the circle. -/
def cw : Circ := ((0 : ℝ) : Circ)

/-- `U`: the circle minus the point `π(-1/2)`. -/
def cU : Set Circ := {x | x ≠ ((-1/2 : ℝ) : Circ)}

/-- `V`: the circle minus the point `π(-1/4)`. -/
def cV : Set Circ := {x | x ≠ ((-1/4 : ℝ) : Circ)}

/-- The first arc of `U ∩ V`. -/
def cA1 : Set Circ := ((↑) : ℝ → Circ) '' K1

/-- The second arc of `U ∩ V`. -/
def cA2 : Set Circ := ((↑) : ℝ → Circ) '' K2

/-- The quotient map `ℝ → ℝ/ℤ`, as an open partial homeomorphism with source `(a, a+1)`. -/
abbrev phCoe (a : ℝ) : OpenPartialHomeomorph ℝ Circ :=
  AddCircle.openPartialHomeomorphCoe (1 : ℝ) a

/-- The homeomorphism `(-1/2,1/2) ≃ U`. -/
def ΦU : ↥J1 ≃ₜ ↥cU := (phCoe (-1/2)).toHomeomorphSourceTarget

/-- The homeomorphism `(-1/4,3/4) ≃ V`. -/
def ΦV : ↥J2 ≃ₜ ↥cV := (phCoe (-1/4)).toHomeomorphSourceTarget

/-! ## §1  The quotient map and equality of cosets -/

theorem isOpenMap_coe : IsOpenMap ((↑) : ℝ → Circ) :=
  QuotientAddGroup.isOpenMap_coe (G := ℝ) (N := AddSubgroup.zmultiples (1 : ℝ))

/-- `π t = π t'` iff `t - t'` is an integer. -/
theorem coe_eq_iff (t t' : ℝ) : ((t : ℝ) : Circ) = ((t' : ℝ) : Circ) ↔ ∃ k : ℤ, (k : ℝ) = t - t' := by
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by simpa using hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by simpa using hk⟩

/-- If `t - t'` lies strictly between `-1` and `1` and `t ≠ t'`, then `π t ≠ π t'`. -/
theorem coe_ne_of_sub_mem_Ioo (t t' : ℝ) (h : t - t' ∈ Set.Ioo (-1) 1) (hne : t ≠ t') :
    ((t : ℝ) : Circ) ≠ ((t' : ℝ) : Circ) := by
  intro hc
  obtain ⟨k, hk⟩ := (coe_eq_iff t t').mp hc
  have hk1 : (k : ℝ) < 1 := by rw [hk]; exact h.2
  have hk2 : (-1 : ℝ) < (k : ℝ) := by rw [hk]; exact h.1
  have hk0 : k = 0 := by
    have h2 : (-1 : ℤ) < k := by exact_mod_cast hk2
    have h1 : k < (1 : ℤ) := by exact_mod_cast hk1
    omega
  refine hne ?_
  have hz : t - t' = 0 := by rw [← hk, hk0]; norm_num
  linarith

/-- Injectivity of the quotient map on an interval of length `≤ 1`. -/
theorem coe_injOn_Ioo (a b : ℝ) (hba : b - a ≤ 1) :
    Set.InjOn ((↑) : ℝ → Circ) (Set.Ioo a b) := by
  intro x hx y hy hxy
  by_contra hne
  refine coe_ne_of_sub_mem_Ioo x y ?_ hne hxy
  rw [Set.mem_Ioo]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2, hba]

/-! ## §2  The cover -/

theorem isOpen_cU : IsOpen cU := (phCoe (-1/2)).open_target

theorem isOpen_cV : IsOpen cV := (phCoe (-1/4)).open_target

theorem coe_ne_half_quarter : (((-1/2 : ℝ)) : Circ) ≠ (((-1/4 : ℝ)) : Circ) := by
  refine coe_ne_of_sub_mem_Ioo (-1/2) (-1/4) (by norm_num [Set.mem_Ioo]) ?_
  norm_num

theorem cU_union_cV : cU ∪ cV = univ := by
  ext x
  constructor
  · intro _; trivial
  · intro _
    by_cases h : x = (((-1/2 : ℝ)) : Circ)
    · exact Or.inr (fun hc => coe_ne_half_quarter (h.symm.trans hc))
    · exact Or.inl h

theorem cw_mem_cU : cw ∈ cU := by
  show (((0 : ℝ)) : Circ) ≠ (((-1/2 : ℝ)) : Circ)
  exact coe_ne_of_sub_mem_Ioo 0 (-1/2) (by norm_num [Set.mem_Ioo]) (by norm_num)

theorem cw_mem_cV : cw ∈ cV := by
  show (((0 : ℝ)) : Circ) ≠ (((-1/4 : ℝ)) : Circ)
  exact coe_ne_of_sub_mem_Ioo 0 (-1/4) (by norm_num [Set.mem_Ioo]) (by norm_num)

theorem K1_subset_J2 : K1 ⊆ J2 := by
  intro t ht
  rw [K1, mem_Ioo] at ht
  rw [J2, mem_Ioo]
  constructor <;> linarith [ht.1, ht.2]

theorem K2_subset_J2 : K2 ⊆ J2 := by
  intro t ht
  rw [K2, mem_Ioo] at ht
  rw [J2, mem_Ioo]
  constructor <;> linarith [ht.1, ht.2]

theorem cw_mem_cA1 : cw ∈ cA1 := ⟨0, by norm_num [K1, cw], rfl⟩

theorem image_K1_eq : (phCoe (-1/4)) '' K1 = cA1 := by
  rw [cA1]
  rfl

theorem image_K2_eq : (phCoe (-1/4)) '' K2 = cA2 := by
  rw [cA2]
  rfl

/-- `(-1/4, 1/2) ≃ cA1`. -/
def homeo_K1_cA1 : ↥K1 ≃ₜ ↥cA1 :=
  (phCoe (-1/4)).homeomorphOfImageSubsetSource K1_subset_J2 image_K1_eq

/-- `(1/2, 3/4) ≃ cA2`. -/
def homeo_K2_cA2 : ↥K2 ≃ₜ ↥cA2 :=
  (phCoe (-1/4)).homeomorphOfImageSubsetSource K2_subset_J2 image_K2_eq

/-! ## §3  The projection and section of a "cylinder" over a subset of the circle -/

/-- The projection `X × W → X` (as a map from the subtype of `X × Circ`). -/
def projSet (X : Type*) [TopologicalSpace X] (W : Set Circ) :
    (TopCat.of ↥{p : X × Circ | p.2 ∈ W}) ⟶ (TopCat.of X) :=
  TopCat.ofHom (ContinuousMap.fst.comp ⟨Subtype.val, continuous_subtype_val⟩)

@[simp] theorem projSet_apply (X : Type*) [TopologicalSpace X] (W : Set Circ)
    (p : ↥{p : X × Circ | p.2 ∈ W}) : projSet X W p = p.1.1 := rfl

/-- The section `X → X × W` at a point `w ∈ W`. -/
def sectSet (X : Type*) [TopologicalSpace X] (W : Set Circ) (w : W) :
    (TopCat.of X) ⟶ (TopCat.of ↥{p : X × Circ | p.2 ∈ W}) :=
  TopCat.ofHom ⟨fun x => ⟨(x, (w : Circ)), w.2⟩, by fun_prop⟩

@[simp] theorem sectSet_apply (X : Type*) [TopologicalSpace X] (W : Set Circ) (w : W) (x : X) :
    (sectSet X W w x).1 = (x, (w : Circ)) := rfl

theorem projSet_sectSet (X : Type*) [TopologicalSpace X] (W : Set Circ) (w : W) :
    sectSet X W w ≫ projSet X W = 𝟙 (TopCat.of X) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  rfl

/-! ## §4  The ranks of the homology of the circle and of a point -/

/-- The rank of `H_k(S¹)`: `1` in degrees `0` and `1`, `0` otherwise. -/
def rankCirc : ℤ → ℕ := fun k => if k = 0 ∨ k = 1 then 1 else 0

/-- The rank of `H_k(pt)`: `1` in degree `0`, `0` otherwise. -/
def rankPt : ℤ → ℕ := fun k => if k = 0 then 1 else 0

@[simp] theorem rankCirc_zero : rankCirc 0 = 1 := rfl
@[simp] theorem rankCirc_one : rankCirc 1 = 1 := rfl
@[simp] theorem rankPt_zero : rankPt 0 = 1 := rfl

theorem rankCirc_eq_zero (k : ℤ) (h0 : k ≠ 0) (h1 : k ≠ 1) : rankCirc k = 0 := by
  rw [rankCirc]; simp [h0, h1]

theorem rankPt_eq_zero (k : ℤ) (h0 : k ≠ 0) : rankPt k = 0 := by
  rw [rankPt]; simp [h0]

/-! ## §5  The pieces are contractible -/

instance : ContractibleSpace ↥J1 :=
  Convex.contractibleSpace (convex_Ioo _ _) ⟨0, by norm_num [J1]⟩

instance : ContractibleSpace ↥J2 :=
  Convex.contractibleSpace (convex_Ioo _ _) ⟨0, by norm_num [J2]⟩

instance : ContractibleSpace ↥K1 :=
  Convex.contractibleSpace (convex_Ioo _ _) ⟨0, by norm_num [K1]⟩

instance : ContractibleSpace ↥K2 :=
  Convex.contractibleSpace (convex_Ioo _ _) ⟨(1/2 + 3/4)/2, by norm_num [K2]⟩

instance : ContractibleSpace ↥cU := ΦU.symm.contractibleSpace

instance : ContractibleSpace ↥cV := ΦV.symm.contractibleSpace

instance : ContractibleSpace ↥cA1 := homeo_K1_cA1.symm.contractibleSpace

instance : ContractibleSpace ↥cA2 := homeo_K2_cA2.symm.contractibleSpace

end

end Work.PieceHomology
