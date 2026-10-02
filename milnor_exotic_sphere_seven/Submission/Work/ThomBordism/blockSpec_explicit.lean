import Mathlib
import Submission.Work.PTGeometric.genLoopListConcat_eq_get
import Submission.Work.PTGeometric.genLoopListConcat_preimage_homeo_spec

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

open scoped Topology unitInterval
open Function Set

namespace Work.ThomBordism

noncomputable section

open Work.PTGeometric

/-!
# The block decomposition of an iterated concatenation, with the block index

`Work.PTGeometric.genLoopListConcat i l` is the iterated concatenation of a list of cube loops `l`
along the coordinate `i`, and `Work.PTGeometric.genLoopListConcatStep i l t` computes the *block* of
a cube point `t`: the index `k` of the element of the list which the concatenation consults, and the
reparametrised cube point `u` at which it is read.

`Work.PTGeometric.genLoopListConcat_preimage_homeo_spec` exhibits a homeomorphism from the preimage
of a set `A` (with `x ∉ A`) under `genLoopListConcat i l` onto the disjoint union
`Σ k : Fin l.length, (l.get k) ⁻¹' A` of the elements' preimages, together with the *value* formula
`(l.get k) u = genLoopListConcat i l t`.

This file proves that this homeomorphism can be chosen so that it is *literally* the block map: the
index and the reparametrised point it produces are those computed by
`genLoopListConcatStep i l`.  That is the statement needed to analyse the *pointwise* geometry of the
preimage decomposition.

## Main results

* `Work.ThomBordism.blockSpec_step` — the induction step, with the block-index conclusion;
* `Work.ThomBordism.genLoopListConcatStepHomeo_exists` — the block map is a homeomorphism;
* `Work.ThomBordism.blockSpec_explicit` — the target statement.
-/

/-- **The induction step of the block decomposition, with the block index.**  If the block
decomposition of `genLoopListConcat i l'` is given by the block recursion for `l'`, then the same
holds for `g :: l'`: the homeomorphism built by splitting the cube at `t i = 1/2` sends a cube point
`t` to the pair consisting of the block index and of the reparametrised cube point computed by
`genLoopListConcatStep i (g :: l')`. -/
theorem blockSpec_step {N : Type*} [DecidableEq N] {X : Type} [TopologicalSpace X] {x : X}
    (i : N) (g : GenLoop N X x) (l' : List (GenLoop N X x)) (A : Set X) (hx : x ∉ A)
    (h' : ↥((genLoopListConcat i l') ⁻¹' A) ≃ₜ (Σ k : Fin l'.length, ((l'.get k) ⁻¹' A)))
    (hh' : ∀ t : ↥((genLoopListConcat i l') ⁻¹' A),
      ((h' t).1 : ℕ) = (genLoopListConcatStep i l' (t : N → Set.Icc (0 : ℝ) 1)).1 ∧
      ((h' t).2 : N → Set.Icc (0 : ℝ) 1) =
        (genLoopListConcatStep i l' (t : N → Set.Icc (0 : ℝ) 1)).2) :
    ∃ h : ↥((genLoopListConcat i (g :: l')) ⁻¹' A) ≃ₜ
        (Σ k : Fin (g :: l').length, (((g :: l').get k) ⁻¹' A)),
      ∀ t : ↥((genLoopListConcat i (g :: l')) ⁻¹' A),
        ((h t).1 : ℕ) = (genLoopListConcatStep i (g :: l') (t : N → Set.Icc (0 : ℝ) 1)).1 ∧
        ((h t).2 : N → Set.Icc (0 : ℝ) 1) =
          (genLoopListConcatStep i (g :: l') (t : N → Set.Icc (0 : ℝ) 1)).2 := by
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
    have hU : ((eL ⟨t, ht⟩ : ↥Q) : N → Set.Icc (0 : ℝ) 1) =
        (Function.update (t : N → Set.Icc (0 : ℝ) 1) i
          (Set.projIcc (0 : ℝ) 1 (by norm_num)
            (2 * (((t : N → Set.Icc (0 : ℝ) 1)) i : ℝ)))) := by
      rw [eL_coe]
      rfl
    have hstep := genLoopListConcatStep_cons_le i g l' (t : N → Set.Icc (0 : ℝ) 1) ht
    have h1 : ((h' (eL ⟨t, ht⟩)).1 : ℕ) =
        (genLoopListConcatStep i l'
          (Function.update (t : N → Set.Icc (0 : ℝ) 1) i
            (Set.projIcc (0 : ℝ) 1 (by norm_num)
              (2 * (((t : N → Set.Icc (0 : ℝ) 1)) i : ℝ))))).1 := by
      rw [← hU]
      exact (hh' (eL ⟨t, ht⟩)).1
    have h2 : ((h' (eL ⟨t, ht⟩)).2 : N → Set.Icc (0 : ℝ) 1) =
        (genLoopListConcatStep i l'
          (Function.update (t : N → Set.Icc (0 : ℝ) 1) i
            (Set.projIcc (0 : ℝ) 1 (by norm_num)
              (2 * (((t : N → Set.Icc (0 : ℝ) 1)) i : ℝ))))).2 := by
      rw [← hU]
      exact (hh' (eL ⟨t, ht⟩)).2
    constructor
    · show (((h' (eL ⟨t, ht⟩)).1.succ : Fin (l'.length + 1)) : ℕ)
        = (genLoopListConcatStep i (g :: l') (t : N → Set.Icc (0 : ℝ) 1)).1
      rw [Fin.val_succ, h1, hstep]
    · show ((h' (eL ⟨t, ht⟩)).2 : N → Set.Icc (0 : ℝ) 1)
        = (genLoopListConcatStep i (g :: l') (t : N → Set.Icc (0 : ℝ) 1)).2
      rw [h2, hstep]
  · have hval : (e₁.trans (e₂.trans (e₃.trans e₅))) t =
        (⟨0, eR ⟨t, ht⟩⟩ :
          Σ k : Fin (g :: l').length, (((g :: l').get k) ⁻¹' A)) := by
      rw [Homeomorph.trans_apply, Homeomorph.trans_apply, Homeomorph.trans_apply,
        sumComplHomeo_apply_of_not_mem hscl t ht]
      rfl
    rw [hval]
    have hstep := genLoopListConcatStep_cons_gt i g l' (t : N → Set.Icc (0 : ℝ) 1) ht
    constructor
    · show (((0 : Fin (l'.length + 1)) : ℕ))
        = (genLoopListConcatStep i (g :: l') (t : N → Set.Icc (0 : ℝ) 1)).1
      rw [hstep]
      rfl
    · show ((eR ⟨t, ht⟩ : ↥R) : N → Set.Icc (0 : ℝ) 1)
        = (genLoopListConcatStep i (g :: l') (t : N → Set.Icc (0 : ℝ) 1)).2
      rw [eR_coe, hstep]
      rfl

/-- **The block map is a homeomorphism onto the disjoint union of the blocks.**  For a list `l` of
cube loops and a set `A` not containing the base point, the map sending a cube point of the preimage
of `A` under the iterated concatenation to its block index together with the block reparametrisation
computed by `genLoopListConcatStep` is a homeomorphism onto `Σ k : Fin l.length, (l.get k) ⁻¹' A`. -/
theorem genLoopListConcatStepHomeo_exists {N : Type*} [DecidableEq N] {X : Type}
    [TopologicalSpace X] {x : X} (i : N) (l : List (GenLoop N X x)) (A : Set X) (hx : x ∉ A) :
    ∃ h : ↥((genLoopListConcat i l) ⁻¹' A) ≃ₜ (Σ k : Fin l.length, ((l.get k) ⁻¹' A)),
      ∀ t : ↥((genLoopListConcat i l) ⁻¹' A),
        ((h t).1 : ℕ) = (genLoopListConcatStep i l (t : N → Set.Icc (0 : ℝ) 1)).1 ∧
        ((h t).2 : N → Set.Icc (0 : ℝ) 1) =
          (genLoopListConcatStep i l (t : N → Set.Icc (0 : ℝ) 1)).2 := by
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
    exact blockSpec_step i g l' A hx h' hh'

theorem blockSpec_explicit {N : Type*} [DecidableEq N] {X : Type} [TopologicalSpace X] {x : X}
    (i : N) (l : List (GenLoop N X x)) {A : Set X} (hA : IsClosed A) (hx : x ∉ A) :
    ∃ h : ↥((Work.PTGeometric.genLoopListConcat i l) ⁻¹' A) ≃ₜ
        (Σ k : Fin l.length, ((l.get k) ⁻¹' A)),
      (∀ t : ↥((Work.PTGeometric.genLoopListConcat i l) ⁻¹' A),
        ((h t).1 : ℕ) = (Work.PTGeometric.genLoopListConcatStep i l (t : N → Set.Icc (0 : ℝ) 1)).1
        ∧ ((h t).2 : N → Set.Icc (0 : ℝ) 1) =
            (Work.PTGeometric.genLoopListConcatStep i l (t : N → Set.Icc (0 : ℝ) 1)).2) := by
  have _ := hA
  exact genLoopListConcatStepHomeo_exists i l A hx

end

end Work.ThomBordism
