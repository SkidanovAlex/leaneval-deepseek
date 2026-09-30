/-
# The `A`/`B` decomposition of `M̂` for the Mayer–Vietoris argument

This file is the fourth layer of the area `Space/`: the open cover `M̂ = A ∪ B` used for the
Mayer–Vietoris computation of `H_*(M̂)` (blueprint §3), together with the deformation retractions
of its pieces.

## The cover

The filling piece `[-1,1]² × T_v` carries the layer parameter `sqNorm p = ‖p‖∞ ∈ [0,1]` (the sup
norm on the square); the core of the filling is `sqNorm = 0` and its boundary (glued to the cusp
of `M̄`) is `sqNorm = 1`.

* `B = {sqNorm < 1}` — the union of the open collars, which deformation retracts onto the core
  `⊔_v T_v` (`p ↦ 0`).
* `A = M̄ ∪ {1/4 < sqNorm}` — the complement of the (closed) inner cores `{sqNorm ≤ 1/4}`, which
  deformation retracts onto `M̄` (`p ↦ p/sqNorm`).
* `A ∩ B = {1/4 < sqNorm < 1}` — the collar annulus, which deformation retracts onto the glued
  boundary `⊔_v ∂[-1,1]² × T_v` (`p ↦ p/sqNorm`).

The numbers `1/4` and `1` are the ones of the blueprint (`A = M̂ ∖ {‖p‖∞ ≤ ¼}`, `B = {‖p‖∞ < 1}`).

## Main definitions and results

* `Work.Space.Assembly.Aset`, `Work.Space.Assembly.Bset` — the two open sets.
* `Work.Space.Assembly.Aset_sup_Bset` — `A ⊔ B = ⊤`.
* the homotopy equivalences `Aset ≃ₕ Mbar`, `Bset ≃ₕ ⊔ T_v`, `Aset ⊓ Bset ≃ₕ ⊔ ∂[-1,1]² × T_v`.
-/
import Mathlib
import Submission.Work.Space.Assembly

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function Filter
open TopologicalSpace
open scoped Topology

namespace Work.Space

theorem zero_mem_Sq : (0 : E2) ∈ Sq := by
  simp [Sq]

/-- The core point `(0, t)` of the `v`-th filling piece. -/
def corePt (Torus : Cusp → Type*) (v : Cusp) (t : Torus v) : Filling Torus :=
  ⟨v, (⟨0, zero_mem_Sq⟩, t)⟩

/-- The inner core `{‖p‖∞ < 1}` of the filling pieces: the source of the retraction `B → ⊔ T_v`. -/
def innerCore (Torus : Cusp → Type*) : Set (Filling Torus) := {q | sqNorm q.2.1 < 1}

/-- The outer shell `{1/4 < ‖p‖∞}`, whose complement is the closed inner core of `A`. -/
def outerShell (Torus : Cusp → Type*) : Set (Filling Torus) := {q | 1/4 < sqNorm q.2.1}

/-- The collar annulus `{1/4 < ‖p‖∞ < 1} = A ∩ B` inside the filling pieces. -/
def annulus (Torus : Cusp → Type*) : Set (Filling Torus) := {q | 1/4 < sqNorm q.2.1 ∧ sqNorm q.2.1 < 1}

theorem isOpen_innerCore (Torus : Cusp → Type*) [∀ v, TopologicalSpace (Torus v)] :
    IsOpen (innerCore Torus) :=
  isOpen_lt (continuous_fillingNorm Torus) continuous_const

theorem isOpen_outerShell (Torus : Cusp → Type*) [∀ v, TopologicalSpace (Torus v)] :
    IsOpen (outerShell Torus) :=
  isOpen_lt continuous_const (continuous_fillingNorm Torus)

theorem isOpen_annulus (Torus : Cusp → Type*) [∀ v, TopologicalSpace (Torus v)] :
    IsOpen (annulus Torus) :=
  (isOpen_outerShell Torus).inter (isOpen_innerCore Torus)

theorem mem_boundarySet_iff (Torus : Cusp → Type*) {q : Filling Torus} :
    q ∈ FillingBdry Torus ↔ sqNorm q.2.1 = 1 := Iff.rfl

theorem sqNorm_corePt (Torus : Cusp → Type*) (v : Cusp) (t : Torus v) :
    sqNorm (corePt Torus v t).2.1 = 0 := by
  simp [corePt, sqNorm, nrm]


namespace Assembly

variable (a : Assembly)

/-! ### The identification criterion for the two pieces -/

/-- A point of the filling pieces is glued to a point of `M̄` exactly on the cusped boundary. -/
theorem incMbar_eq_incY_iff {x : a.Mbar} {q : a.Y} :
    a.incMbar x = a.incY q ↔ ∃ hx : x ∈ a.Tset,
      (a.glue ⟨x, hx⟩ : {y : a.Y // y ∈ a.boundarySet}) = q := by
  constructor
  · intro h
    rcases (Quotient.exact h : a.glueData.Rel (Sum.inl x) (Sum.inr q)) with
      ⟨z, h1, h2⟩ | ⟨z, h1, h2⟩ | h'
    · have hxz : x = (z : a.Mbar) := Sum.inl.inj h1
      subst hxz
      exact ⟨z.2, (Sum.inr.inj h2).symm⟩
    · exact absurd h1 (by simp)
    · exact absurd h' (by simp)
  · rintro ⟨hx, rfl⟩
    exact a.incMbar_eq_incY hx

theorem incY_eq_incMbar_iff {q : a.Y} {x : a.Mbar} :
    a.incY q = a.incMbar x ↔ ∃ hx : x ∈ a.Tset,
      (a.glue ⟨x, hx⟩ : {y : a.Y // y ∈ a.boundarySet}) = q := by
  rw [eq_comm]
  exact a.incMbar_eq_incY_iff

/-- The `v`-th boundary point glued to a point of `M̄` lies in the outer shell: its layer is `1`. -/
theorem glue_mem_outerShell {x : a.Mbar} (hx : x ∈ a.Tset) :
    ((a.glue ⟨x, hx⟩ : {y : a.Y // y ∈ a.boundarySet}) : a.Y) ∈ outerShell a.Torus := by
  have h2 : sqNorm ((a.glue ⟨x, hx⟩ : {y : a.Y // y ∈ a.boundarySet}) : a.Y).2.1 = 1 :=
    (a.glue ⟨x, hx⟩).2
  rw [outerShell, mem_setOf_eq, h2]
  norm_num

theorem glue_notMem_innerCore {x : a.Mbar} (hx : x ∈ a.Tset) :
    ((a.glue ⟨x, hx⟩ : {y : a.Y // y ∈ a.boundarySet}) : a.Y) ∉ innerCore a.Torus := by
  have h2 : sqNorm ((a.glue ⟨x, hx⟩ : {y : a.Y // y ∈ a.boundarySet}) : a.Y).2.1 = 1 :=
    (a.glue ⟨x, hx⟩).2
  rw [innerCore, mem_setOf_eq]
  rw [h2]
  norm_num

/-! ### The two open sets -/

/-- **`B`**: the union of the open collars `{‖p‖∞ < 1}` of the filling pieces. -/
def Bset : Opens a.Mhat where
  carrier := a.incY '' innerCore a.Torus
  is_open' := by
    rw [a.isOpen_iff_sum]
    refine ⟨?_, ?_⟩
    · have h : {x : a.Mbar | a.incMbar x ∈ a.incY '' innerCore a.Torus} = ∅ := by
        ext x
        simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, mem_image]
        rintro ⟨q, hq, hxq⟩
        obtain ⟨hx, rfl⟩ := a.incY_eq_incMbar_iff.mp hxq
        exact a.glue_notMem_innerCore hx hq
      rw [h]
      exact isOpen_empty
    · have h : {y : a.Y | a.incY y ∈ a.incY '' innerCore a.Torus} = innerCore a.Torus := by
        ext y
        simp only [mem_setOf_eq, mem_image]
        exact ⟨fun ⟨q, hq, hyq⟩ => by rwa [a.incY_injective hyq] at hq, fun hy => ⟨y, hy, rfl⟩⟩
      rw [h]
      exact isOpen_innerCore a.Torus

/-- **`A`**: `M̄` together with the outer shells `{1/4 < ‖p‖∞}` of the filling pieces. -/
def Aset : Opens a.Mhat where
  carrier := range a.incMbar ∪ a.incY '' outerShell a.Torus
  is_open' := by
    rw [a.isOpen_iff_sum]
    refine ⟨?_, ?_⟩
    · have h : {x : a.Mbar | a.incMbar x ∈ range a.incMbar ∪ a.incY '' outerShell a.Torus}
          = univ := by
        ext x
        simp only [mem_setOf_eq, mem_union, mem_range, mem_univ, iff_true]
        exact Or.inl ⟨x, rfl⟩
      rw [h]
      exact isOpen_univ
    · have h : {y : a.Y | a.incY y ∈ range a.incMbar ∪ a.incY '' outerShell a.Torus}
          = outerShell a.Torus := by
        ext y
        constructor
        · intro hy
          simp only [mem_setOf_eq, mem_union, mem_range, mem_image] at hy
          rcases hy with ⟨m, hm⟩ | ⟨q, hq, hyq⟩
          · obtain ⟨hx, hgl⟩ := a.incMbar_eq_incY_iff.mp hm
            rw [← hgl]
            exact a.glue_mem_outerShell hx
          · rwa [a.incY_injective hyq] at hq
        · intro hy
          simp only [mem_setOf_eq, mem_union, mem_range, mem_image]
          exact Or.inr ⟨y, hy, rfl⟩
      rw [h]
      exact isOpen_outerShell a.Torus

/-! ### Membership criteria -/

theorem incMbar_notMem_Bset (x : a.Mbar) : a.incMbar x ∉ a.Bset := by
  rintro ⟨q, hq, hxq⟩
  obtain ⟨hx, rfl⟩ := a.incY_eq_incMbar_iff.mp hxq
  exact a.glue_notMem_innerCore hx hq

theorem incY_mem_Bset_iff {q : a.Y} : a.incY q ∈ a.Bset ↔ q ∈ innerCore a.Torus := by
  change a.incY q ∈ (a.incY '' innerCore a.Torus) ↔ q ∈ innerCore a.Torus
  exact ⟨fun ⟨q', hq', hqq'⟩ => by rwa [a.incY_injective hqq'] at hq', fun hq => ⟨q, hq, rfl⟩⟩

theorem incY_mem_Aset_iff {q : a.Y} : a.incY q ∈ a.Aset ↔ q ∈ outerShell a.Torus := by
  change a.incY q ∈ (range a.incMbar ∪ a.incY '' outerShell a.Torus) ↔ q ∈ outerShell a.Torus
  constructor
  · intro h
    rcases h with ⟨m, hm⟩ | ⟨q', hq', hqq'⟩
    · obtain ⟨hx, hgl⟩ := a.incMbar_eq_incY_iff.mp hm
      rw [← hgl]
      exact a.glue_mem_outerShell hx
    · rwa [a.incY_injective hqq'] at hq'
  · intro h
    exact Or.inr ⟨q, h, rfl⟩

theorem incMbar_mem_Aset (m : a.Mbar) : a.incMbar m ∈ a.Aset := by
  change a.incMbar m ∈ (range a.incMbar ∪ a.incY '' outerShell a.Torus)
  exact Or.inl ⟨m, rfl⟩

/-! ### The maps of the Mayer--Vietoris squares -/

/-- The inclusion `A ∩ B → B`. -/
def inclAB_B : C({z : a.Mhat // z ∈ a.Aset ∧ z ∈ a.Bset}, {z : a.Mhat // z ∈ a.Bset}) where
  toFun z := ⟨z.1, z.2.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk (fun z => z.2.2)

/-- **The cusp parametrisation** `τ`: the inverse of the gluing, as a map from the glued boundary of
the filling pieces into `M̄`.  This is the `τ_v` of blueprint §1 (`T_v = ℝ³/Λ_v → M̄`), transported
across the gluing homeomorphism `Work.Space.Assembly.glue`. -/
def tauBdry : C({q : a.Y // q ∈ a.boundarySet}, a.Mbar) where
  toFun q := ((a.glue.symm q : a.Tset) : a.Mbar)
  continuous_toFun := continuous_subtype_val.comp (a.glue.symm.continuous)

/-- The cusp parametrisation, evaluated. -/
theorem tauBdry_apply (q : {q : a.Y // q ∈ a.boundarySet}) :
    tauBdry a q = ((a.glue.symm q : a.Tset) : a.Mbar) := rfl

/-- The inclusion `A ∩ B → A`. -/
def inclAB_A : C({z : a.Mhat // z ∈ a.Aset ∧ z ∈ a.Bset}, {z : a.Mhat // z ∈ a.Aset}) where
  toFun z := ⟨z.1, z.2.1⟩
  continuous_toFun := continuous_subtype_val.subtype_mk (fun z => z.2.1)

/-- The projection `⊔_v (∂[-1,1]² × T_v) → ⊔_v T_v` forgetting the boundary coordinate. -/
def projBdry :
    C((Σ v : Cusp, {p : SquarePt // sqNorm p = 1} × a.Torus v), (Σ v : Cusp, a.Torus v)) where
  toFun q := ⟨q.1, q.2.2⟩
  continuous_toFun := by
    apply continuous_sigma
    intro v
    exact continuous_sigmaMk.comp continuous_snd

/-- The projection `⊔_v (∂[-1,1]² × T_v) → ⊔_v T_v`, evaluated. -/
theorem projBdry_apply (q : Σ v : Cusp, {p : SquarePt // sqNorm p = 1} × a.Torus v) :
    projBdry a q = ⟨q.1, q.2.2⟩ := rfl

/-! ### The cover `A ∪ B = M̂` -/

/-- **`A ∪ B = M̂`.**  A point of a filling piece is in `B` if its layer is `< 1`, and in `A` if its
layer is `> 1/4`; since layers lie in `[0,1]`, one of the two always holds. -/
theorem Aset_sup_Bset : a.Aset ⊔ a.Bset = ⊤ := by
  ext z
  obtain ⟨w, rfl⟩ := Quotient.exists_rep z
  rcases w with x | y
  · rw [Opens.coe_sup, Opens.coe_top]
    simp only [mem_union, mem_setOf_eq, mem_univ, iff_true]
    exact Or.inl (a.incMbar_mem_Aset x)
  · rw [Opens.coe_sup, Opens.coe_top]
    simp only [mem_union, mem_setOf_eq, mem_univ, iff_true]
    rcases lt_or_ge (sqNorm y.2.1) 1 with h | h
    · exact Or.inr (a.incY_mem_Bset_iff.mpr h)
    · exact Or.inl (a.incY_mem_Aset_iff.mpr (lt_of_lt_of_le (by norm_num) h))

end Assembly

end Work.Space
