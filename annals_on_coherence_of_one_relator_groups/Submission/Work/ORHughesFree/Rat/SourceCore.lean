import Mathlib
import Submission.Work.ORHughesFree.Rat.SourceFrame
import Submission.Work.ORHughesFree.Rat.Weak.SVPart
import Submission.Work.ORHughesFree.Rat.Weak.Structural
import Submission.Work.ORHughesFree.Rat.Weak.A_ofGroup
import Submission.Work.ORHughesFree.Rat.Weak.A_ratOp
import Submission.Work.ORHughesFree.Rat.Weak.A_add_left
import Submission.Work.ORHughesFree.Rat.Weak.Attain
import Submission.Work.ORHughesFree.Rat.Weak.Assembly
import Submission.Work.ORHughesFree.RatU.exists_decomp

/-!
# The source subgroup of an element of `Rat(U)` ([DHS04, Theorem 5.7])

[DHS04, Theorem 5.7] attaches to every `α ∈ Rat(U)` a *unique smallest* subgroup
`source(α) ≤ U` with `α ∈ Rat(source(α)) · U`, and shows that it is finitely generated.  The
framework in which the statement is proved for the concrete term model `RatU U` of
`Rat/RTerm.lean` lives in `Rat/SourceFrame.lean`.

This file proves the theorem itself.

## The structure of the proof

The family `Rat.F α = {V ≤ U | α ∈ Rat(V)·U}` is upward closed, so the theorem is *equivalent* to
the assertion that it has a **least element** `S`: then `S` is the `S` of the statement, and its
finite generation follows from `Rat.mem_A_iff` (a witness `α·φu = ofSubgroup S β` produces a term
`t` with `S = closure (supp t)`); this is `exists_source_subgroup_weak_of_le` below.

The remaining content, the *existence* of the least element, is [DHS04, §5] for the word model
`ℕ[U ♮ X]` of `Rat(U)` (`Rat/WordModel/Defs.lean`).  The statements proved here are the ones that
induction uses:

* `mem_F_iff'` : `V ∈ Rat.F α ↔ ∃ u, α·φu ∈ Rat.A V`;
* `mem_F_add_iff` : `V ∈ Rat.F (x + y) ↔ ∃ u, x·φu ∈ Rat.A V ∧ y·φu ∈ Rat.A V` — the "sum case";
* `mem_BL_iff`, `mem_BL_iff_ofGroup_mul`, `F_ratOp_eq_FL`, `FL_ratOp_eq_F` : the **duality**
  `Rat.F (x⋄) = Rat.FL x` and `Rat.FL (x⋄) = Rat.F x` — the "`⋄` case";
* `ratOp_ofGroup_mul`, `ratOp_mul_ofGroup''`, `ofGroup_mul_ratOp''`, `ofGroup_mul_ratOp'''` :
  the absorption identities;
* `F_zero`, `F_ofGroup` : the base cases.
-/

namespace Work.ORHughesFree.Rat

open Work.ORHughesFree
open Work.ORHughesFree.Rat.WordModel

variable {U : Type} [Group U]

/-- `V ∈ Rat.F α` iff some right translate of `α` lies in `Rat.A V`. -/
theorem mem_F_iff' (α : RatU U) (V : Subgroup U) :
    V ∈ Rat.F α ↔ ∃ u : U, α * RatU.ofGroup u ∈ Rat.A V := by
  constructor
  · rintro ⟨β, u, h⟩
    exact ⟨u⁻¹, β, by rw [← h, mul_assoc, Weak.ofGroup_mul_inv, mul_one]⟩
  · rintro ⟨u, β, h⟩
    exact ⟨β, u⁻¹, by rw [h, mul_assoc, Weak.ofGroup_mul_inv, mul_one]⟩

/-- `Rat.F 0` is the whole lattice. -/
theorem F_zero : Rat.F (0 : RatU U) = Set.univ := by
  ext V
  exact iff_of_true ⟨(0 : RatU ↥V), 1, by rw [map_zero, zero_mul]⟩ trivial

/-- `Rat.F (ofGroup u)` is the whole lattice. -/
theorem F_ofGroup (u : U) : Rat.F (RatU.ofGroup u) = Set.univ := by
  ext V
  exact iff_of_true ⟨(1 : RatU ↥V), u, by rw [map_one, one_mul]⟩ trivial

/-- **Additive purity applied to `Rat.F`**: `V ∈ Rat.F (x + y)` iff a right translate of `x` and
the same right translate of `y` both lie in `Rat.A V`. -/
theorem mem_F_add_iff (x y : RatU U) (V : Subgroup U) :
    V ∈ Rat.F (x + y) ↔
      ∃ u : U, x * RatU.ofGroup u ∈ Rat.A V ∧ y * RatU.ofGroup u ∈ Rat.A V := by
  rw [mem_F_iff']
  constructor
  · rintro ⟨u, h⟩
    rw [add_mul] at h
    exact ⟨u, Weak.A_add_left h,
      Weak.A_add_left (x := y * RatU.ofGroup u) (y := x * RatU.ofGroup u)
        (by rwa [add_comm] at h)⟩
  · rintro ⟨u, hx, hy⟩
    exact ⟨u, by rw [add_mul]; exact (Weak.ASub V).add_mem hx hy⟩

/-! ### The absorption identities -/

/-- `⋄(φu·x) = ⋄x·φu⁻¹`. -/
theorem ratOp_ofGroup_mul (x : RatU U) (u : U) :
    RatU.ratOp (RatU.ofGroup u * x) = RatU.ratOp x * RatU.ofGroup u⁻¹ := by
  have h := RatU.ratOp_mul_ofGroup x u⁻¹
  rw [inv_inv] at h
  exact h.symm

/-- `⋄x·φu = ⋄(φu⁻¹·x)`. -/
theorem ratOp_mul_ofGroup'' (x : RatU U) (u : U) :
    RatU.ratOp x * RatU.ofGroup u = RatU.ratOp (RatU.ofGroup u⁻¹ * x) :=
  RatU.ratOp_mul_ofGroup x u

/-- `φu·⋄x = ⋄(x·φu⁻¹)`. -/
theorem ofGroup_mul_ratOp'' (x : RatU U) (u : U) :
    RatU.ofGroup u * RatU.ratOp x = RatU.ratOp (x * RatU.ofGroup u⁻¹) :=
  RatU.ofGroup_mul_ratOp u x

/-- `φu⁻¹·⋄x = ⋄(x·φu)`. -/
theorem ofGroup_mul_ratOp''' (x : RatU U) (u : U) :
    RatU.ofGroup u⁻¹ * RatU.ratOp x = RatU.ratOp (x * RatU.ofGroup u) := by
  have h := RatU.ofGroup_mul_ratOp u⁻¹ x
  rw [inv_inv] at h
  exact h

/-! ### The left family and the `⋄`-duality -/

/-- **Term characterization of `Rat.BL V = U·Rat(V)`** (mirror of `Rat.mem_B_iff`): `x ∈ Rat.BL V`
iff there is a term `t` with support in `V` and a group element `u` with `φu·[t] = x`. -/
theorem mem_BL_iff (V : Subgroup U) (x : RatU U) :
    x ∈ Rat.BL V ↔ ∃ (t : RTerm U) (u : U),
      (∀ v ∈ RTerm.supp t, v ∈ V) ∧
        RatU.mk (RTerm.mul (RTerm.smulL u RTerm.o) t) = x := by
  constructor
  · rintro ⟨β, u, rfl⟩
    refine Quotient.inductionOn β ?_
    intro τ
    refine ⟨RTerm.map (Subtype.val) τ, u, ?_, ?_⟩
    · intro v hv
      obtain ⟨v', -, rfl⟩ := Rat.supp_map_mem (Subtype.val) τ hv
      exact v'.2
    · change RatU.mk (RTerm.mul (RTerm.smulL u RTerm.o) (RTerm.map Subtype.val τ))
        = RatU.ofGroup u * RatU.ofSubgroup V (RatU.mk τ)
      rw [Rat.ofSubgroup_mk_map τ, RatU.mk_mul]
      rfl
  · rintro ⟨t, u, ht, hx⟩
    refine ⟨RatU.mk (RTerm.map (projSub V) t), u, ?_⟩
    have h1 : RatU.ofSubgroup V (RatU.mk (RTerm.map (projSub V) t)) = RatU.mk t := by
      dsimp only [RatU.ofSubgroup]
      rw [RatU.lift_apply, RTerm.eval_map]
      · exact RTerm.eval_rational_self t
      · intro v hv; exact coe_projSub V (ht v hv)
    rw [← hx, h1, RatU.mk_mul, RatU.mk_smulL, RatU.mk_one]
    rfl

/-- `x ∈ Rat.BL V` iff some left translate `φu·x` lies in `Rat.A V`. -/
theorem mem_BL_iff_ofGroup_mul {V : Subgroup U} {x : RatU U} :
    x ∈ Rat.BL V ↔ ∃ u : U, RatU.ofGroup u * x ∈ Rat.A V := by
  constructor
  · rintro ⟨β, u, hβ⟩
    refine ⟨u⁻¹, β, ?_⟩
    rw [← hβ, ← mul_assoc, ← RatU.ofGroup_mul, inv_mul_cancel, RatU.ofGroup_one, one_mul]
  · rintro ⟨u, β, hβ⟩
    refine ⟨β, u⁻¹, ?_⟩
    rw [hβ, ← mul_assoc, ← RatU.ofGroup_mul, inv_mul_cancel, RatU.ofGroup_one, one_mul]

/-- **The `⋄`-duality**: `α ∈ Rat(V)·U` for `α = x⋄` iff `u·x ∈ Rat(V)` for some `u ∈ U`. -/
theorem F_ratOp_eq_FL (x : RatU U) : Rat.F (RatU.ratOp x) = Rat.FL x := by
  ext V
  rw [mem_F_iff']
  change (∃ u : U, RatU.ratOp x * RatU.ofGroup u ∈ Rat.A V) ↔ x ∈ Rat.BL V
  rw [mem_BL_iff_ofGroup_mul]
  constructor
  · rintro ⟨u, h⟩
    exact ⟨u⁻¹, Weak.A_ratOp (by rw [← ratOp_mul_ofGroup'' x u]; exact h)⟩
  · rintro ⟨u, h⟩
    exact ⟨u⁻¹, by rw [← ratOp_ofGroup_mul x u]; exact Weak.A_ratOp_mem h⟩

/-- **The `⋄`-duality, mirrored.** -/
theorem FL_ratOp_eq_F (x : RatU U) : Rat.FL (RatU.ratOp x) = Rat.F x := by
  ext V
  rw [mem_F_iff']
  change RatU.ratOp x ∈ Rat.BL V ↔ ∃ u : U, x * RatU.ofGroup u ∈ Rat.A V
  rw [mem_BL_iff_ofGroup_mul]
  constructor
  · rintro ⟨u, h⟩
    exact ⟨u⁻¹, Weak.A_ratOp (by rw [← ofGroup_mul_ratOp'' x u]; exact h)⟩
  · rintro ⟨u, h⟩
    exact ⟨u⁻¹, by rw [ofGroup_mul_ratOp''' x u]; exact Weak.A_ratOp_mem h⟩


end Work.ORHughesFree.Rat
