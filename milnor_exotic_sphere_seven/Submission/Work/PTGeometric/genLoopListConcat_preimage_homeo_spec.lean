import Submission.Work.PTGeometric.genLoopListConcat_preimage_homeo

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the *specified* block decomposition of an iterated concatenation

`Work.PTGeometric.genLoopListConcat_preimage_homeo` proves only that the preimage of a set `A` (with
`x ∉ A`) under the iterated concatenation `genLoopListConcat i l` of a list of cube loops is
*homeomorphic* to the disjoint union `Σ k : Fin l.length, (l.get k) ⁻¹' A` of the elements'
preimages.

The last mile needs the homeomorphism **itself**, and it must be the coordinate one: it sends a cube
point `t` to the pair consisting of the index `k` of the dyadic block containing `t` and of the block
reparametrisation of `t`, so that the equation

`(l.get k) u = genLoopListConcat i l t`

holds.  This file builds that homeomorphism explicitly, by redoing the inductive construction of
`genLoopListConcat_preimage_homeo` while keeping all the maps (and their pointwise formulas) under
control.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

open scoped Topology unitInterval
open Function Set

attribute [fun_prop] Work.PTGeometric.continuous_halfMapL Work.PTGeometric.continuous_halfMapLInv
attribute [fun_prop] Work.PTGeometric.continuous_halfMapR Work.PTGeometric.continuous_halfMapRInv

namespace Work.PTGeometric

noncomputable section

variable {N : Type*} [DecidableEq N]

/-! ## Generic homeomorphisms -/

/-- **Reassociation of a nested subtype**: `{x : {x // p x} // q x.1} ≃ₜ {x // p x ∧ q x}`, by the
identity on the underlying points. -/
def subtypeInterHomeo {α : Type*} [TopologicalSpace α] (p q : α → Prop) :
    {x : {x // p x} // q x.1} ≃ₜ {x : α // p x ∧ q x} where
  toFun x := ⟨x.1.1, x.1.2, x.2⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv x := rfl
  right_inv x := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem subtypeInterHomeo_coe {α : Type*} [TopologicalSpace α] (p q : α → Prop)
    (x : {x : {x // p x} // q x.1}) :
    ((subtypeInterHomeo p q x : {x : α // p x ∧ q x}) : α) = x.1.1 := rfl

@[simp] theorem subtypeInterHomeo_symm_coe {α : Type*} [TopologicalSpace α] (p q : α → Prop)
    (x : {x : α // p x ∧ q x}) :
    (((subtypeInterHomeo p q).symm x : {x : {x // p x} // q x.1}) : α) = x.1 := rfl

/-- **Commuting the conjuncts** in a subtype of a conjunction. -/
def subtypeAndCommHomeo {α : Type*} [TopologicalSpace α] (p q : α → Prop) :
    {x : α // p x ∧ q x} ≃ₜ {x : α // q x ∧ p x} where
  toFun x := ⟨x.1, x.2.2, x.2.1⟩
  invFun x := ⟨x.1, x.2.2, x.2.1⟩
  left_inv x := rfl
  right_inv x := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem subtypeAndCommHomeo_coe {α : Type*} [TopologicalSpace α] (p q : α → Prop)
    (x : {x : α // p x ∧ q x}) :
    ((subtypeAndCommHomeo p q x : {x : α // q x ∧ p x}) : α) = x.1 := rfl

@[simp] theorem subtypeAndCommHomeo_symm_coe {α : Type*} [TopologicalSpace α] (p q : α → Prop)
    (x : {x : α // q x ∧ p x}) :
    (((subtypeAndCommHomeo p q).symm x : {x : α // p x ∧ q x}) : α) = x.1 := rfl

/-- **Dropping a redundant conjunct**: `{x // p x ∧ q x} ≃ₜ {x // q x}` when `q x → p x`. -/
def subtypeAndDropHomeo {α : Type*} [TopologicalSpace α] (p q : α → Prop) (h : ∀ x, q x → p x) :
    {x : α // p x ∧ q x} ≃ₜ {x : α // q x} where
  toFun x := ⟨x.1, x.2.2⟩
  invFun x := ⟨x.1, h x.1 x.2, x.2⟩
  left_inv x := rfl
  right_inv x := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem subtypeAndDropHomeo_coe {α : Type*} [TopologicalSpace α] (p q : α → Prop)
    (h : ∀ x, q x → p x) (x : {x : α // p x ∧ q x}) :
    ((subtypeAndDropHomeo p q h x : {x : α // q x}) : α) = x.1 := rfl

@[simp] theorem subtypeAndDropHomeo_symm_coe {α : Type*} [TopologicalSpace α] (p q : α → Prop)
    (h : ∀ x, q x → p x) (x : {x : α // q x}) :
    (((subtypeAndDropHomeo p q h).symm x : {x : α // p x ∧ q x}) : α) = x.1 := rfl

/-- **Changing the predicate of a subtype** along a pointwise iff. -/
def subtypeCongrHomeo {α : Type*} [TopologicalSpace α] {p q : α → Prop} (h : ∀ x, p x ↔ q x) :
    {x : α // p x} ≃ₜ {x : α // q x} where
  toFun x := ⟨x.1, (h x.1).1 x.2⟩
  invFun x := ⟨x.1, (h x.1).2 x.2⟩
  left_inv x := rfl
  right_inv x := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem subtypeCongrHomeo_coe {α : Type*} [TopologicalSpace α] {p q : α → Prop}
    (h : ∀ x, p x ↔ q x) (x : {x : α // p x}) :
    ((subtypeCongrHomeo h x : {x : α // q x}) : α) = x.1 := rfl

@[simp] theorem subtypeCongrHomeo_symm_coe {α : Type*} [TopologicalSpace α] {p q : α → Prop}
    (h : ∀ x, p x ↔ q x) (x : {x : α // q x}) :
    (((subtypeCongrHomeo h).symm x : {x : α // p x}) : α) = x.1 := rfl

/-- **A homeomorphism of ambient spaces induces one on sublevel sets**, when the predicates match
along the homeomorphism. -/
def subtypeHomeoOfIff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (p : X → Prop) (q : Y → Prop) (h : ∀ x, p x ↔ q (e x)) :
    {x : X // p x} ≃ₜ {y : Y // q y} where
  toFun x := ⟨e x.1, (h x.1).1 x.2⟩
  invFun y := ⟨e.symm y.1, (h (e.symm y.1)).2 (by rw [Homeomorph.apply_symm_apply]; exact y.2)⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv y := by apply Subtype.ext; simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem subtypeHomeoOfIff_coe {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (p : X → Prop) (q : Y → Prop) (h : ∀ x, p x ↔ q (e x)) (x : {x : X // p x}) :
    ((subtypeHomeoOfIff e p q h x : {y : Y // q y}) : Y) = e x.1 := rfl

/-- **A space is the topological sum of a clopen set and its complement**, explicitly. -/
def sumComplHomeo {Y : Type*} [TopologicalSpace Y] {s : Set Y} (hs : IsClopen s) :
    Y ≃ₜ (s ⊕ (sᶜ : Set Y)) :=
  letI : DecidablePred (· ∈ s) := Classical.decPred _
  ((Equiv.Set.sumCompl s).toHomeomorphOfContinuousClosed
    (continuous_sum_dom.mpr ⟨continuous_subtype_val, continuous_subtype_val⟩)
    (by
      intro C hC
      obtain ⟨h1, h2⟩ := isClosed_sum_iff.mp hC
      have himg : (Equiv.Set.sumCompl s) '' C =
          (Subtype.val '' (Sum.inl ⁻¹' C)) ∪ (Subtype.val '' (Sum.inr ⁻¹' C)) := by
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          rcases z with x | x
          · exact Or.inl ⟨x, hz, Equiv.Set.sumCompl_apply_inl s x⟩
          · exact Or.inr ⟨x, hz, Equiv.Set.sumCompl_apply_inr s x⟩
        · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
          · exact ⟨Sum.inl x, hx, Equiv.Set.sumCompl_apply_inl s x⟩
          · exact ⟨Sum.inr x, hx, Equiv.Set.sumCompl_apply_inr s x⟩
      rw [himg]
      exact ((hs.1.isClosedMap_subtype_val : IsClosedMap (Subtype.val : s → Y))
        (Sum.inl ⁻¹' C) h1).union
        ((hs.2.isClosed_compl.isClosedMap_subtype_val :
            IsClosedMap (Subtype.val : (sᶜ : Set Y) → Y))
          (Sum.inr ⁻¹' C) h2))).symm

theorem sumComplHomeo_apply_of_mem {Y : Type*} [TopologicalSpace Y] {s : Set Y} (hs : IsClopen s)
    (y : Y) (hy : y ∈ s) : sumComplHomeo hs y = Sum.inl ⟨y, hy⟩ := by
  letI : DecidablePred (· ∈ s) := Classical.decPred _
  change (Equiv.Set.sumCompl s).symm y = Sum.inl ⟨y, hy⟩
  rw [Equiv.symm_apply_eq, Equiv.Set.sumCompl_apply_inl]

theorem sumComplHomeo_apply_of_not_mem {Y : Type*} [TopologicalSpace Y] {s : Set Y}
    (hs : IsClopen s) (y : Y) (hy : y ∉ s) : sumComplHomeo hs y = Sum.inr ⟨y, hy⟩ := by
  letI : DecidablePred (· ∈ s) := Classical.decPred _
  change (Equiv.Set.sumCompl s).symm y = Sum.inr ⟨y, hy⟩
  rw [Equiv.symm_apply_eq, Equiv.Set.sumCompl_apply_inr]

/-! ## The `Fin (n+1)` splitting of a sigma -/

/-- **The `0`-th fibre of a sigma over `Fin (n+1)` splits off.** -/
def sigmaSuccHomeo {n : ℕ} (Y : Fin (n + 1) → Type*) [∀ k, TopologicalSpace (Y k)] :
    ((Σ k : Fin n, Y k.succ) ⊕ Y 0) ≃ₜ (Σ k : Fin (n + 1), Y k) where
  toFun := Sum.elim (fun p : Σ k : Fin n, Y k.succ => ⟨p.1.succ, p.2⟩) (fun y => ⟨0, y⟩)
  invFun := fun p => Fin.cases (motive := fun j => Y j → ((Σ k : Fin n, Y k.succ) ⊕ Y 0))
    Sum.inr (fun k y => Sum.inl ⟨k, y⟩) p.1 p.2
  left_inv := by rintro (⟨k, y⟩ | y) <;> rfl
  right_inv := by
    rintro ⟨j, y⟩
    revert y
    refine Fin.cases ?_ ?_ j
    · intro y; rfl
    · intro k z; rfl
  continuous_toFun := by
    rw [continuous_sum_dom]
    refine ⟨?_, continuous_sigmaMk⟩
    apply continuous_sigma
    intro k
    exact continuous_sigmaMk
  continuous_invFun := by
    apply continuous_sigma
    intro j
    exact continuous_finCases (z := (Sum.inr : Y 0 → ((Σ k : Fin n, Y k.succ) ⊕ Y 0)))
      (s := fun k y => (Sum.inl ⟨k, y⟩ : ((Σ k : Fin n, Y k.succ) ⊕ Y 0)))
      continuous_inr (fun k => continuous_inl.comp continuous_sigmaMk) j

@[simp] theorem sigmaSuccHomeo_apply_inl {n : ℕ} (Y : Fin (n + 1) → Type*)
    [∀ k, TopologicalSpace (Y k)] (p : Σ k : Fin n, Y k.succ) :
    sigmaSuccHomeo Y (Sum.inl p) = ⟨p.1.succ, p.2⟩ := rfl

@[simp] theorem sigmaSuccHomeo_apply_inr {n : ℕ} (Y : Fin (n + 1) → Type*)
    [∀ k, TopologicalSpace (Y k)] (y : Y 0) :
    sigmaSuccHomeo Y (Sum.inr y) = ⟨0, y⟩ := rfl

/-! ## The two halves of the cube, as homeomorphisms of what lies over them -/

/-- The left half of the cube read through the first factor of a concatenation. -/
theorem halfMapLInv_coe_halfMapL {N : Type*} [DecidableEq N] (i : N)
    (t : {t : N → Set.Icc (0 : ℝ) 1 // (((t : N → Set.Icc (0 : ℝ) 1) i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2}) :
    ((halfMapLInv i (halfMapL i t) :
        {t : N → Set.Icc (0 : ℝ) 1 //
          (((t : N → Set.Icc (0 : ℝ) 1) i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2}) :
      N → Set.Icc (0 : ℝ) 1) = (t : N → Set.Icc (0 : ℝ) 1) := by
  rw [halfMapL_left_inv i t]

theorem halfMapRInv_coe_halfMapR {N : Type*} [DecidableEq N] (i : N)
    (t : {t : N → Set.Icc (0 : ℝ) 1 //
      ¬ (((t : N → Set.Icc (0 : ℝ) 1) i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2}) :
    ((halfMapRInv i (halfMapR i t) :
        {t : N → Set.Icc (0 : ℝ) 1 //
          ¬ (((t : N → Set.Icc (0 : ℝ) 1) i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2}) :
      N → Set.Icc (0 : ℝ) 1) = (t : N → Set.Icc (0 : ℝ) 1) := by
  rw [halfMapR_left_inv i t]

/-! ## The induction step -/

theorem block_step {N : Type*} [DecidableEq N] {X : Type} [TopologicalSpace X] {x : X}
    (i : N) (g : GenLoop N X x) (l' : List (GenLoop N X x)) (A : Set X) (hx : x ∉ A)
    (h' : ↥((genLoopListConcat i l') ⁻¹' A) ≃ₜ (Σ k : Fin l'.length, ((l'.get k) ⁻¹' A)))
    (hh' : ∀ t : ↥((genLoopListConcat i l') ⁻¹' A),
      (l'.get (h' t).1) ((h' t).2 : N → Set.Icc (0 : ℝ) 1) = (genLoopListConcat i l') t.1) :
    ∃ h : ↥((genLoopListConcat i (g :: l')) ⁻¹' A) ≃ₜ
        (Σ k : Fin (g :: l').length, (((g :: l').get k) ⁻¹' A)),
      ∀ t : ↥((genLoopListConcat i (g :: l')) ⁻¹' A),
        ((g :: l').get (h t).1) ((h t).2 : N → Set.Icc (0 : ℝ) 1)
          = (genLoopListConcat i (g :: l')) t.1 := by
  classical
  let P : Set (N → Set.Icc (0 : ℝ) 1) := (genLoopListConcat i (g :: l')) ⁻¹' A
  let Q : Set (N → Set.Icc (0 : ℝ) 1) := (genLoopListConcat i l') ⁻¹' A
  let R : Set (N → Set.Icc (0 : ℝ) 1) := g ⁻¹' A
  let s : Set ↥P := {t | (((t : N → Set.Icc (0 : ℝ) 1) i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2}
  have hcoord : Continuous
      (fun t : ↥P => (((t : N → Set.Icc (0 : ℝ) 1) i : Set.Icc (0 : ℝ) 1) : ℝ)) :=
    (continuous_subtype_val : Continuous (Subtype.val : Set.Icc (0:ℝ) 1 → ℝ)).comp
      ((continuous_apply i).comp (continuous_subtype_val :
        Continuous (Subtype.val : ↥P → (N → Set.Icc (0:ℝ) 1))))
  -- the cut locus is not in `P`
  have hne : ∀ t : ↥P,
      (((t : N → Set.Icc (0 : ℝ) 1) i : Set.Icc (0 : ℝ) 1) : ℝ) ≠ 1 / 2 := by
    intro t ht
    have hle : (((t : N → Set.Icc (0 : ℝ) 1) i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2 := le_of_eq ht
    have hp : Set.projIcc (0 : ℝ) 1 (by norm_num) (2 * (1 / 2 : ℝ)) = (1 : Set.Icc (0:ℝ) 1) := by
      rw [show 2 * (1 / 2 : ℝ) = 1 by norm_num, Set.projIcc_right]
      rfl
    have hval : GenLoop.transAt i (genLoopListConcat i l') g (t : N → Set.Icc (0:ℝ) 1)
        = (genLoopListConcat i l') (Function.update (t : N → Set.Icc (0:ℝ) 1) i 1) := by
      rw [genLoop_transAt_apply_of_le i (genLoopListConcat i l') g hle,
        show 2 * (((t : N → Set.Icc (0:ℝ) 1) i : Set.Icc (0:ℝ) 1) : ℝ) = 2 * (1 / 2) by rw [ht]]
      exact congrArg (genLoopListConcat i l')
        (congrArg (Function.update (t : N → Set.Icc (0:ℝ) 1) i) hp)
    have hb : Function.update (t : N → Set.Icc (0:ℝ) 1) i (1 : Set.Icc (0:ℝ) 1)
        ∈ Cube.boundary N :=
      ⟨i, Or.inr (Function.update_self i (1 : Set.Icc (0:ℝ) 1) (t : N → Set.Icc (0:ℝ) 1))⟩
    have hmem : (genLoopListConcat i (g :: l')) (t : N → Set.Icc (0:ℝ) 1) ∈ A := t.2
    rw [genLoopListConcat_cons, hval,
      GenLoop.boundary (genLoopListConcat i l')
        (Function.update (t : N → Set.Icc (0:ℝ) 1) i (1 : Set.Icc (0:ℝ) 1)) hb] at hmem
    exact hx hmem
  have hscl : IsClopen s := by
    have hsplit : s = {t : ↥P |
        (((t : N → Set.Icc (0 : ℝ) 1) i : Set.Icc (0 : ℝ) 1) : ℝ) < 1 / 2} := by
      ext t
      show ((((t : ↥P) : N → Set.Icc (0 : ℝ) 1) i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2 ↔
        (((t : N → Set.Icc (0 : ℝ) 1) i : Set.Icc (0 : ℝ) 1) : ℝ) < 1 / 2
      exact ⟨fun h => lt_of_le_of_ne h (hne t), fun h => le_of_lt h⟩
    refine ⟨IsClosed.preimage hcoord isClosed_Iic, ?_⟩
    rw [hsplit]
    exact IsOpen.preimage hcoord isOpen_Iio
  -- the left block
  have eL_mem : ∀ x : ↥s, (genLoopListConcat i l')
      (halfMapL i ⟨(x.1.1 : N → Set.Icc (0 : ℝ) 1), x.2⟩) ∈ A := by
    intro x
    have h : (genLoopListConcat i (g :: l')) (x.1.1 : N → Set.Icc (0 : ℝ) 1) ∈ A := x.1.2
    rw [genLoopListConcat_cons,
      genLoop_transAt_apply_of_le i (genLoopListConcat i l') g x.2] at h
    exact h
  have eL_inv_mem : ∀ y : ↥Q, (genLoopListConcat i (g :: l'))
      (halfMapLInv i (y : N → Set.Icc (0 : ℝ) 1)) ∈ A := by
    intro y
    have heq : (genLoopListConcat i (g :: l'))
        (halfMapLInv i (y : N → Set.Icc (0 : ℝ) 1))
        = (genLoopListConcat i l') (y : N → Set.Icc (0 : ℝ) 1) := by
      rw [genLoopListConcat_cons,
        genLoop_transAt_apply_of_le i (genLoopListConcat i l') g
          (halfMapLInv i (y : N → Set.Icc (0 : ℝ) 1)).2,
        ← coe_halfMapL, halfMapL_right_inv]
    rw [heq]; exact y.2
  let eL_fun : ↥s → ↥Q := fun x =>
    ⟨halfMapL i ⟨(x.1.1 : N → Set.Icc (0 : ℝ) 1), x.2⟩, eL_mem x⟩
  let eL_inv : ↥Q → ↥s := fun y => by
    refine ⟨(⟨halfMapLInv i (y : N → Set.Icc (0 : ℝ) 1), eL_inv_mem y⟩ : ↥P), ?_⟩
    show ((((halfMapLInv i (y : N → Set.Icc (0 : ℝ) 1)) : N → Set.Icc (0 : ℝ) 1) i :
      Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2
    exact (halfMapLInv i (y : N → Set.Icc (0 : ℝ) 1)).2
  have eL_left : ∀ x : ↥s, eL_inv (eL_fun x) = x := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    exact halfMapLInv_coe_halfMapL i ⟨(x.1.1 : N → Set.Icc (0 : ℝ) 1), x.2⟩
  have eL_right : ∀ y : ↥Q, eL_fun (eL_inv y) = y := by
    intro y
    apply Subtype.ext
    change ((halfMapL i (halfMapLInv i (y : N → Set.Icc (0 : ℝ) 1)) :
        N → Set.Icc (0 : ℝ) 1)) = (y : N → Set.Icc (0 : ℝ) 1)
    rw [halfMapL_right_inv]
  have eL_conts : Continuous eL_fun := by
    show Continuous (fun x : ↥s =>
      (⟨halfMapL i ⟨(x.1.1 : N → Set.Icc (0 : ℝ) 1), x.2⟩, eL_mem x⟩ : ↥Q))
    have h1 : Continuous (fun x : ↥s =>
        halfMapL i ⟨(x.1.1 : N → Set.Icc (0 : ℝ) 1), x.2⟩) := by fun_prop
    exact Continuous.subtype_mk (p := fun z : N → Set.Icc (0 : ℝ) 1 => z ∈ Q) h1 eL_mem
  have eL_conts_inv : Continuous eL_inv := by
    show Continuous (fun y : ↥Q =>
      (⟨⟨halfMapLInv i (y : N → Set.Icc (0 : ℝ) 1), eL_inv_mem y⟩,
        (halfMapLInv i (y : N → Set.Icc (0 : ℝ) 1)).2⟩ : ↥s))
    have h1 : Continuous (fun y : ↥Q => halfMapLInv i (y : N → Set.Icc (0 : ℝ) 1)) := by fun_prop
    have h1' : Continuous (fun y : ↥Q =>
        ((halfMapLInv i (y : N → Set.Icc (0 : ℝ) 1)) : N → Set.Icc (0 : ℝ) 1)) :=
      (continuous_subtype_val : Continuous (Subtype.val :
        {t : N → Set.Icc (0 : ℝ) 1 //
          (((t : N → Set.Icc (0 : ℝ) 1) i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2} →
          N → Set.Icc (0 : ℝ) 1)).comp h1
    exact Continuous.subtype_mk
      (f := fun y : ↥Q => (⟨halfMapLInv i (y : N → Set.Icc (0 : ℝ) 1), eL_inv_mem y⟩ : ↥P))
      (p := fun z : ↥P => z ∈ s)
      (Continuous.subtype_mk
        (f := fun y : ↥Q =>
          ((halfMapLInv i (y : N → Set.Icc (0 : ℝ) 1)) : N → Set.Icc (0 : ℝ) 1))
        (p := fun z : N → Set.Icc (0 : ℝ) 1 => z ∈ P) h1' eL_inv_mem)
      (fun y => (halfMapLInv i (y : N → Set.Icc (0 : ℝ) 1)).2)
  let eL : ↥s ≃ₜ ↥Q :=
    { toFun := eL_fun, invFun := eL_inv, left_inv := eL_left, right_inv := eL_right,
      continuous_toFun := eL_conts, continuous_invFun := eL_conts_inv }
  have eL_coe : ∀ x : ↥s, ((eL x : ↥Q) : N → Set.Icc (0 : ℝ) 1)
      = halfMapL i ⟨(x.1.1 : N → Set.Icc (0 : ℝ) 1), x.2⟩ := fun x => rfl
  -- the right block
  have hneR : ∀ y : ↥R, (((y : N → Set.Icc (0 : ℝ) 1) i : Set.Icc (0 : ℝ) 1) : ℝ) ≠ 0 := by
    intro y h0
    have hb : (y : N → Set.Icc (0 : ℝ) 1) ∈ Cube.boundary N := ⟨i, Or.inl (Subtype.ext h0)⟩
    have hy : g (y : N → Set.Icc (0 : ℝ) 1) = x := GenLoop.boundary g _ hb
    exact hx (by rw [← hy]; exact y.2)
  have eR_mem : ∀ x : ↥sᶜ, g (halfMapR i ⟨(x.1.1 : N → Set.Icc (0 : ℝ) 1), x.2⟩) ∈ A := by
    intro x
    have h : (genLoopListConcat i (g :: l')) (x.1.1 : N → Set.Icc (0 : ℝ) 1) ∈ A := x.1.2
    rw [genLoopListConcat_cons,
      genLoop_transAt_apply_of_gt i (genLoopListConcat i l') g x.2] at h
    exact h
  have eR_inv_mem : ∀ y : ↥R, (genLoopListConcat i (g :: l'))
      (halfMapRInv i ⟨(y : N → Set.Icc (0 : ℝ) 1), hneR y⟩) ∈ A := by
    intro y
    have heq : (genLoopListConcat i (g :: l'))
        (halfMapRInv i ⟨(y : N → Set.Icc (0 : ℝ) 1), hneR y⟩)
        = g (y : N → Set.Icc (0 : ℝ) 1) := by
      rw [genLoopListConcat_cons,
        genLoop_transAt_apply_of_gt i (genLoopListConcat i l') g
          (halfMapRInv i ⟨(y : N → Set.Icc (0 : ℝ) 1), hneR y⟩).2,
        ← coe_halfMapR, halfMapR_right_inv]
    rw [heq]; exact y.2
  let eR_fun : ↥sᶜ → ↥R := fun x =>
    ⟨halfMapR i ⟨(x.1.1 : N → Set.Icc (0 : ℝ) 1), x.2⟩, eR_mem x⟩
  let eR_inv : ↥R → ↥sᶜ := fun y => by
    refine ⟨(⟨halfMapRInv i ⟨(y : N → Set.Icc (0 : ℝ) 1), hneR y⟩, eR_inv_mem y⟩ : ↥P), ?_⟩
    show ¬ ((((halfMapRInv i ⟨(y : N → Set.Icc (0 : ℝ) 1), hneR y⟩) :
      N → Set.Icc (0 : ℝ) 1) i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2
    exact (halfMapRInv i ⟨(y : N → Set.Icc (0 : ℝ) 1), hneR y⟩).2
  have eR_left : ∀ x : ↥sᶜ, eR_inv (eR_fun x) = x := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    exact halfMapRInv_coe_halfMapR i ⟨(x.1.1 : N → Set.Icc (0 : ℝ) 1), x.2⟩
  have eR_right : ∀ y : ↥R, eR_fun (eR_inv y) = y := by
    intro y
    apply Subtype.ext
    change ((halfMapR i (halfMapRInv i ⟨(y : N → Set.Icc (0 : ℝ) 1), hneR y⟩) :
        N → Set.Icc (0 : ℝ) 1)) = (y : N → Set.Icc (0 : ℝ) 1)
    rw [halfMapR_right_inv]
  have eR_conts : Continuous eR_fun := by
    show Continuous (fun x : ↥sᶜ =>
      (⟨halfMapR i ⟨(x.1.1 : N → Set.Icc (0 : ℝ) 1), x.2⟩, eR_mem x⟩ : ↥R))
    have h1 : Continuous (fun x : ↥sᶜ =>
        (halfMapR i ⟨(x.1.1 : N → Set.Icc (0 : ℝ) 1), x.2⟩ :
          {u : N → Set.Icc (0 : ℝ) 1 // ((u i : Set.Icc (0 : ℝ) 1) : ℝ) ≠ 0})) := by fun_prop
    have h1' : Continuous (fun x : ↥sᶜ =>
        ((halfMapR i ⟨(x.1.1 : N → Set.Icc (0 : ℝ) 1), x.2⟩ :
          {u : N → Set.Icc (0 : ℝ) 1 // ((u i : Set.Icc (0 : ℝ) 1) : ℝ) ≠ 0}) :
          N → Set.Icc (0 : ℝ) 1)) :=
      (continuous_subtype_val : Continuous (Subtype.val :
        {u : N → Set.Icc (0 : ℝ) 1 // ((u i : Set.Icc (0 : ℝ) 1) : ℝ) ≠ 0} →
          N → Set.Icc (0 : ℝ) 1)).comp h1
    exact Continuous.subtype_mk
      (f := fun x : ↥sᶜ =>
        ((halfMapR i ⟨(x.1.1 : N → Set.Icc (0 : ℝ) 1), x.2⟩ :
          {u : N → Set.Icc (0 : ℝ) 1 // ((u i : Set.Icc (0 : ℝ) 1) : ℝ) ≠ 0}) :
          N → Set.Icc (0 : ℝ) 1))
      (p := fun z : N → Set.Icc (0 : ℝ) 1 => z ∈ R) h1' eR_mem
  have eR_conts_inv : Continuous eR_inv := by
    show Continuous (fun y : ↥R =>
      (⟨⟨halfMapRInv i ⟨(y : N → Set.Icc (0 : ℝ) 1), hneR y⟩, eR_inv_mem y⟩,
        (halfMapRInv i ⟨(y : N → Set.Icc (0 : ℝ) 1), hneR y⟩).2⟩ : ↥sᶜ))
    have h1 : Continuous (fun y : ↥R =>
        (⟨(y : N → Set.Icc (0 : ℝ) 1), hneR y⟩ :
          {u : N → Set.Icc (0 : ℝ) 1 // ((u i : Set.Icc (0 : ℝ) 1) : ℝ) ≠ 0})) :=
      continuous_subtype_val.subtype_mk (fun y => hneR y)
    have h2 : Continuous (fun y : ↥R =>
        ((halfMapRInv i ⟨(y : N → Set.Icc (0 : ℝ) 1), hneR y⟩ :
          {t : N → Set.Icc (0 : ℝ) 1 //
            ¬ (((t : N → Set.Icc (0 : ℝ) 1) i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2}) :
          N → Set.Icc (0 : ℝ) 1)) :=
      continuous_subtype_val.comp ((continuous_halfMapRInv i).comp h1)
    exact Continuous.subtype_mk
      (f := fun y : ↥R =>
        (⟨halfMapRInv i ⟨(y : N → Set.Icc (0 : ℝ) 1), hneR y⟩, eR_inv_mem y⟩ : ↥P))
      (p := fun z : ↥P => z ∈ sᶜ)
      (Continuous.subtype_mk
        (f := fun y : ↥R =>
          ((halfMapRInv i ⟨(y : N → Set.Icc (0 : ℝ) 1), hneR y⟩ :
            {t : N → Set.Icc (0 : ℝ) 1 //
              ¬ (((t : N → Set.Icc (0 : ℝ) 1) i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2}) :
            N → Set.Icc (0 : ℝ) 1))
        (p := fun z : N → Set.Icc (0 : ℝ) 1 => z ∈ P)
        h2 (fun y => eR_inv_mem y))
      (fun y => (halfMapRInv i ⟨(y : N → Set.Icc (0 : ℝ) 1), hneR y⟩).2)
  let eR : ↥sᶜ ≃ₜ ↥R :=
    { toFun := eR_fun, invFun := eR_inv, left_inv := eR_left, right_inv := eR_right,
      continuous_toFun := eR_conts, continuous_invFun := eR_conts_inv }
  have eR_coe : ∀ x : ↥sᶜ, ((eR x : ↥R) : N → Set.Icc (0 : ℝ) 1)
      = halfMapR i ⟨(x.1.1 : N → Set.Icc (0 : ℝ) 1), x.2⟩ := fun x => rfl
  -- the composite
  let e₁ : ↥P ≃ₜ (↥s ⊕ ↥sᶜ) := sumComplHomeo hscl
  let e₂ : (↥s ⊕ ↥sᶜ) ≃ₜ (↥Q ⊕ ↥R) := Homeomorph.sumCongr eL eR
  let e₃ : (↥Q ⊕ ↥R) ≃ₜ ((Σ k : Fin l'.length, ((l'.get k) ⁻¹' A)) ⊕ ↥R) :=
    Homeomorph.sumCongr h' (Homeomorph.refl ↥R)
  let e₅ : ((Σ k : Fin l'.length, ((l'.get k) ⁻¹' A)) ⊕ ↥R) ≃ₜ
      (Σ k : Fin (g :: l').length, (((g :: l').get k) ⁻¹' A)) :=
    sigmaSuccHomeo (fun k : Fin (l'.length + 1) => ↥(((g :: l').get k) ⁻¹' A))
  refine ⟨e₁.trans (e₂.trans (e₃.trans e₅)), ?_⟩
  intro t
  by_cases ht : (((t : N → Set.Icc (0 : ℝ) 1) i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2
  · have hval : (e₁.trans (e₂.trans (e₃.trans e₅))) t =
        (⟨(h' (eL ⟨t, ht⟩)).1.succ, (h' (eL ⟨t, ht⟩)).2⟩ :
          Σ k : Fin (g :: l').length, (((g :: l').get k) ⁻¹' A)) := by
      rw [Homeomorph.trans_apply, Homeomorph.trans_apply, Homeomorph.trans_apply,
        sumComplHomeo_apply_of_mem hscl t ht]
      rfl
    rw [hval]
    change (l'.get (h' (eL ⟨t, ht⟩)).1) ((h' (eL ⟨t, ht⟩)).2 : N → Set.Icc (0 : ℝ) 1)
      = (genLoopListConcat i (g :: l')) t.1
    have hstep : (genLoopListConcat i (g :: l')) t.1
        = (genLoopListConcat i l')
            (halfMapL i ⟨(t.1 : N → Set.Icc (0 : ℝ) 1), ht⟩) := by
      change GenLoop.transAt i (genLoopListConcat i l') g t.1 = _
      rw [genLoop_transAt_apply_of_le i (genLoopListConcat i l') g ht]
      rfl
    rw [hstep, hh' (eL ⟨t, ht⟩), eL_coe]
  · have hval : (e₁.trans (e₂.trans (e₃.trans e₅))) t =
        (⟨0, eR ⟨t, ht⟩⟩ :
          Σ k : Fin (g :: l').length, (((g :: l').get k) ⁻¹' A)) := by
      rw [Homeomorph.trans_apply, Homeomorph.trans_apply, Homeomorph.trans_apply,
        sumComplHomeo_apply_of_not_mem hscl t ht]
      rfl
    rw [hval]
    change (g ((eR ⟨t, ht⟩ : ↥R) : N → Set.Icc (0 : ℝ) 1))
      = (genLoopListConcat i (g :: l')) t.1
    have hstep : (genLoopListConcat i (g :: l')) t.1
        = g (halfMapR i ⟨(t.1 : N → Set.Icc (0 : ℝ) 1), ht⟩) := by
      change GenLoop.transAt i (genLoopListConcat i l') g t.1 = _
      rw [genLoop_transAt_apply_of_gt i (genLoopListConcat i l') g ht]
      rfl
    rw [hstep, eR_coe]

/-! ## The main induction -/

theorem genLoopListConcat_preimage_homeo_exists {N : Type*} [DecidableEq N] {X : Type}
    [TopologicalSpace X] {x : X} (i : N) (l : List (GenLoop N X x)) (A : Set X) (hx : x ∉ A) :
    ∃ h : ↥((genLoopListConcat i l) ⁻¹' A) ≃ₜ (Σ k : Fin l.length, ((l.get k) ⁻¹' A)),
      ∀ t : ↥((genLoopListConcat i l) ⁻¹' A),
        (l.get (h t).1) ((h t).2 : N → Set.Icc (0 : ℝ) 1) = (genLoopListConcat i l) t.1 := by
  classical
  induction l with
  | nil =>
    haveI : IsEmpty ↥((genLoopListConcat i ([] : List (GenLoop N X x))) ⁻¹' A) :=
      ⟨fun t => hx (by
        simpa only [genLoopListConcat_nil, Set.mem_preimage, GenLoop.const_apply] using t.2)⟩
    haveI : IsEmpty (Σ k : Fin ([] : List (GenLoop N X x)).length,
        ((([] : List (GenLoop N X x)).get k) ⁻¹' A)) :=
      ⟨fun p => Fin.elim0 p.1⟩
    exact ⟨Homeomorph.empty, fun t => isEmptyElim t⟩
  | cons g l' ih =>
    obtain ⟨h', hh'⟩ := ih
    exact block_step i g l' A hx h' hh'

/-- **The specified block decomposition of an iterated concatenation.** -/
theorem genLoopListConcat_preimage_homeo_spec {N : Type*} [DecidableEq N] {X : Type} [TopologicalSpace X]
    {x : X} (i : N) (l : List (GenLoop N X x)) {A : Set X} (hA : IsClosed A) (hx : x ∉ A) :
    ∃ h : ↥((Work.PTGeometric.genLoopListConcat i l) ⁻¹' A) ≃ₜ
        (Σ k : Fin l.length, ((l.get k) ⁻¹' A)),
      ∀ t : ↥((Work.PTGeometric.genLoopListConcat i l) ⁻¹' A),
        (l.get (h t).1) (h t).2 = (Work.PTGeometric.genLoopListConcat i l) t.1 := by
  obtain ⟨h, hh⟩ := genLoopListConcat_preimage_homeo_exists i l A hx
  exact ⟨h, hh⟩

end

end Work.PTGeometric
