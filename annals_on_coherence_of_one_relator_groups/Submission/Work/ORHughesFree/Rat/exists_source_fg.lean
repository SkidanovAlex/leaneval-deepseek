/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The source of an element of `Rat(U)` is finitely generated

[JZLA20, Proposition 4.4] attaches to every `α ∈ Rat(U)` a finitely generated subgroup
`source(α) ≤ U` with `α ∈ Rat(source(α)) · U`.  This file proves the *existence* half of that
statement for the term model `RatU U` of `Rat(U)` built in
`Submission/Work/ORHughesFree/Rat/RTerm.lean`:

    for every `α : RatU U` there is `V ≤ U` finitely generated and `β : RatU ↥V`
    with `RatU.ofSubgroup V β = α`.

The proof is the expected one: `α` is the class of a term `t : RTerm U`; the group elements
occurring in `t` are finitely many, so they generate a finitely generated subgroup `V ≤ U`, and
replacing every occurrence of `u : U` in `t` by its image in `V` produces a term `β` over `V`
whose image under the canonical map `Rat(V) → Rat(U)` is `α`.
-/
import Mathlib
import Submission.Work.ORHughesFree.Rat.RTerm
import Submission.Work.ORHughesFree.Rat.Source

set_option autoImplicit false

namespace Work.ORHughesFree

namespace RTerm

/-- The (finite) set of group elements occurring in a term of the free rational `U`-semiring. -/
def supp {U : Type} : RTerm U → Set U
  | .z => ∅
  | .o => ∅
  | .add a b => supp a ∪ supp b
  | .mul a b => supp a ∪ supp b
  | .rat a => supp a
  | .smulL u a => insert u (supp a)
  | .smulR u a => insert u (supp a)

/-- The set of group elements occurring in a term is finite. -/
theorem supp_finite {U : Type} (t : RTerm U) : (supp t).Finite := by
  induction t with
  | z => exact Set.finite_empty
  | o => exact Set.finite_empty
  | add a b iha ihb => exact iha.union ihb
  | mul a b iha ihb => exact iha.union ihb
  | rat a iha => exact iha
  | smulL u a iha => exact iha.insert u
  | smulR u a iha => exact iha.insert u

/-- Reinterpret a term over `U` as a term over `V` along a map `f : U → V`. -/
def map {U V : Type} (f : U → V) : RTerm U → RTerm V
  | .z => .z
  | .o => .o
  | .add a b => .add (map f a) (map f b)
  | .mul a b => .mul (map f a) (map f b)
  | .rat a => .rat (map f a)
  | .smulL u a => .smulL (f u) (map f a)
  | .smulR u a => .smulR (f u) (map f a)

variable {U : Type} [Group U]

/-- Evaluating a term of `Rat(U)` in `Rat(U)` itself (with the rational `U`-semiring structure
`RatU.rational`) returns the class of the term. -/
theorem eval_rational_self (t : RTerm U) :
    RTerm.eval (RatU U) (RatU.rational (U := U)) t = RatU.mk t := by
  induction t with
  | z => rfl
  | o => rfl
  | add a b iha ihb =>
    simp only [RTerm.eval, RatU.mk_add]
    rw [iha, ihb]
  | mul a b iha ihb =>
    simp only [RTerm.eval, RatU.mk_mul]
    rw [iha, ihb]
  | rat a iha =>
    simp only [RTerm.eval, RatU.mk_rat]
    rw [iha]
    rfl
  | smulL u a iha =>
    simp only [RTerm.eval, RatU.mk_smulL]
    rw [iha]
    rfl
  | smulR u a iha =>
    simp only [RTerm.eval, RatU.mk_smulR]
    rw [iha]
    rfl

/-- Reindexing a term along `f : U → ↥V` does not change its value in `Rat(U)` — where the
rational `V`-semiring structure is the restriction of scalars of `Rat(U)` — provided `f` fixes
every group element occurring in the term. -/
theorem eval_map (V : Subgroup U) (f : U → ↥V) (t : RTerm U)
    (h : ∀ u ∈ supp t, (f u : U) = u) :
    RTerm.eval (RatU U) (RatU.restrictScalars V) (RTerm.map f t)
      = RTerm.eval (RatU U) (RatU.rational (U := U)) t := by
  induction t with
  | z => rfl
  | o => rfl
  | add a b iha ihb =>
    simp only [RTerm.map, RTerm.eval]
    rw [iha (fun u hu => h u (Or.inl hu)), ihb (fun u hu => h u (Or.inr hu))]
  | mul a b iha ihb =>
    simp only [RTerm.map, RTerm.eval]
    rw [iha (fun u hu => h u (Or.inl hu)), ihb (fun u hu => h u (Or.inr hu))]
  | rat a iha =>
    simp only [RTerm.map, RTerm.eval]
    rw [iha (fun u hu => h u hu), RatU.restrictScalars_ratOp]
  | smulL u a iha =>
    simp only [RTerm.map, RTerm.eval]
    rw [RatU.restrictScalars_smul, iha (fun v hv => h v (Or.inr hv)), h u (Or.inl rfl)]
  | smulR u a iha =>
    simp only [RTerm.map, RTerm.eval]
    rw [RatU.restrictScalars_smulRight, iha (fun v hv => h v (Or.inr hv)), h u (Or.inl rfl)]

end RTerm

/-- A retraction onto a subgroup: an arbitrary element of `U` is sent to its image in `V` if it
lies in `V` and to `1` otherwise. -/
noncomputable def projSub {U : Type} [Group U] (V : Subgroup U) (u : U) : ↥V := by
  classical
  exact if h : u ∈ V then ⟨u, h⟩ else 1

/-- `projSub` fixes the elements of `V`. -/
theorem coe_projSub {U : Type} [Group U] (V : Subgroup U) {u : U} (hu : u ∈ V) :
    (projSub V u : U) = u := by
  unfold projSub
  rw [dif_pos hu]

namespace Rat

/-- **[JZLA20, Proposition 4.4], existence part.** Every element `α ∈ Rat(U)` lies in the image of
the canonical map `Rat(V) → Rat(U)` for some finitely generated subgroup `V ≤ U`. -/
theorem exists_source_fg {U : Type} [Group U] (α : RatU U) :
    ∃ V : Subgroup U, V.FG ∧ ∃ β : RatU ↥V, RatU.ofSubgroup V β = α := by
  classical
  refine Quotient.inductionOn α ?_
  intro t
  refine ⟨Subgroup.closure (RTerm.supp t), ?_, ?_⟩
  · exact (Subgroup.fg_iff _).mpr ⟨RTerm.supp t, rfl, RTerm.supp_finite t⟩
  · refine ⟨RatU.mk (RTerm.map (projSub (Subgroup.closure (RTerm.supp t))) t), ?_⟩
    dsimp only [RatU.ofSubgroup]
    rw [RatU.lift_apply]
    rw [RTerm.eval_map]
    · exact RTerm.eval_rational_self t
    · intro u hu
      exact coe_projSub _ (Subgroup.subset_closure hu)

end Rat

end Work.ORHughesFree
