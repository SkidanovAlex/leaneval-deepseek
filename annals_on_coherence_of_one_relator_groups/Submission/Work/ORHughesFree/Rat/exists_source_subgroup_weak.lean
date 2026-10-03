import Mathlib
import Submission.Work.ORHughesFree.Rat.SourceCore
import Submission.Work.ORHughesFree.Rat.OrbitF
import Submission.Work.ORHughesFree.Rat.Ugen_mem_NUV_iff

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

/-! ### The theorem from the least element of `Rat.F` -/

/-- **The target statement follows from the existence of a least element of `Rat.F α`.**

If for every `α` there is `S ∈ Rat.F α` with `S ≤ V` for all `V ∈ Rat.F α`, then `S` is the
`source` of `α`: it is finitely generated (it is the closure of the support of a term witnessing
`α·φu ∈ Rat.A S`), it satisfies `α ∈ Rat(S)·U` by construction, and it satisfies the minimality
clause of the statement. -/
theorem exists_source_subgroup_weak_of_le
    (h : ∀ α : RatU U, ∃ S : Subgroup U, S ∈ Rat.F α ∧
      ∀ V : Subgroup U, V ∈ Rat.F α → S ≤ V)
    (α : RatU U) :
    ∃ (S : Subgroup U), S.FG ∧
      (∃ (u : U) (β : RatU ↥S), RatU.ofSubgroup S β * RatU.ofGroup u = α) ∧
      (∀ (V : Subgroup U) (u : U) (β : RatU ↥V),
        RatU.ofSubgroup V β * RatU.ofGroup u = α → S ≤ V) := by
  obtain ⟨S, hS, hle⟩ := h α
  obtain ⟨u, β, hβu⟩ := (mem_F_iff' α S).mp hS
  -- `hβu : ofSubgroup S β = α * ofGroup u`
  have hmem : α * RatU.ofGroup u ∈ Rat.A S := ⟨β, hβu⟩
  obtain ⟨t, ht, htx⟩ := (Rat.mem_A_iff _ _).mp hmem
  have hclosure : RatU.mk t ∈ Rat.A (Subgroup.closure (RTerm.supp t)) :=
    (Rat.mem_A_iff _ _).mpr ⟨t, fun v hv => Subgroup.subset_closure hv, rfl⟩
  have hclF : Subgroup.closure (RTerm.supp t) ∈ Rat.F α :=
    (mem_F_iff' α _).mpr ⟨u, by rw [← htx]; exact hclosure⟩
  have hcl : Subgroup.closure (RTerm.supp t) = S := by
    refine le_antisymm ?_ (hle _ hclF)
    rw [Subgroup.closure_le]; exact ht
  refine ⟨S, ?_, ⟨u⁻¹, β, ?_⟩, ?_⟩
  · rw [← hcl]
    exact (Subgroup.fg_iff _).mpr ⟨RTerm.supp t, rfl, RTerm.supp_finite t⟩
  · rw [hβu, mul_assoc, ← RatU.ofGroup_mul, mul_inv_cancel, RatU.ofGroup_one, mul_one]
  · intro V u' β' hV
    exact hle V ((mem_F_iff' α V).mpr ⟨u'⁻¹, β',
      by rw [← hV, mul_assoc, ← RatU.ofGroup_mul, mul_inv_cancel, RatU.ofGroup_one, mul_one]⟩)

/-! ### The base cases of the induction of step 4 -/

/-- The case `α = 0` of the principal-filter statement: `Rat.F 0` is everything, so `⊥` is least. -/
theorem F_zero_least : ∃ S : Subgroup U, S ∈ Rat.F (0 : RatU U) ∧
    ∀ V : Subgroup U, V ∈ Rat.F (0 : RatU U) → S ≤ V :=
  ⟨⊥, by rw [F_zero]; trivial, fun _ _ => bot_le⟩

/-- The case `α = ofGroup u`: `Rat.F (ofGroup u)` is everything, so `⊥` is least. -/
theorem F_ofGroup_least (u : U) : ∃ S : Subgroup U, S ∈ Rat.F (RatU.ofGroup u) ∧
    ∀ V : Subgroup U, V ∈ Rat.F (RatU.ofGroup u) → S ≤ V :=
  ⟨⊥, by rw [F_ofGroup]; trivial, fun _ _ => bot_le⟩

/-! ### The invariant of step 4 and the hinge of the induction

The strong induction on `Rat.treeOfRat U` carries two clauses for each `x`: that `S` is the least
element of `Rat.F x`, and the **tail law** relating the tails at any `V ∈ Rat.F x` to those at `S`
(obtained from `Orbit.T_mul_subset` in one direction and `T_subset_mul_of_least` in the other).

The branches of the induction are:

* `x = 0`, `x = ofGroup u` : `F_zero_least`, `F_ofGroup_least`;
* `x = y + z` : `mem_F_add_iff` + `exists_min_pair` (the orbit minimum);
* `x = y⋄` : `F_ratOp_eq_FL` / `FL_ratOp_eq_F` — note that this branch uses the `Rat.FL` statements
  at the *same* `x`, which is why the induction has to be run simultaneously for `Rat.F` and
  `Rat.FL`;
* `x = a * b` (the two *words* of `RatU.exists_decomp`) : the word-level criterion
  `Orbit.Mval_mem_A_iff` together with the recursion `Xgen_mem_closure_iff`.
-/

/-- The two-clause invariant of the induction of step 4: `S` is the least element of `Rat.F x` and
the tail law holds at `S`. -/
def Inv (x : RatU U) (S : Subgroup U) : Prop :=
  S ∈ Rat.F x ∧ (∀ V : Subgroup U, V ∈ Rat.F x → S ≤ V) ∧
    ∀ V : Subgroup U, V ∈ Rat.F x →
      Orbit.T ((FreeProduct.Psi x).coeff.support) V =
        {u : U | ∃ s ∈ Orbit.T ((FreeProduct.Psi x).coeff.support) S, ∃ v ∈ V, u = s * v}

/-- The tail set of the empty support is everything. -/
theorem T_empty_eq_univ (V : Subgroup U) :
    Orbit.T (∅ : Finset (FreeProduct.NU U)) V = Set.univ := by
  ext u; simp [Orbit.T]

/-- `Psi 0 = 0`, so the support of `Psi 0` is empty. -/
theorem support_Psi_zero : (FreeProduct.Psi (0 : RatU U)).coeff.support = ∅ := by
  rw [map_zero]; simp

/-- **The base branch `x = 0` of the induction**: both sides of the tail law are `univ`. -/
theorem exists_inv_zero : ∃ S : Subgroup U, Inv (0 : RatU U) S := by
  refine ⟨⊥, ?_, fun _ _ => bot_le, ?_⟩
  · rw [F_zero]; trivial
  · intro V _
    rw [support_Psi_zero, T_empty_eq_univ, T_empty_eq_univ]
    ext u
    exact ⟨fun _ => ⟨u, trivial, 1, V.one_mem, by simp⟩, fun _ => trivial⟩

/-- The support of a monomial in `ℕ[U ♮ X]` (no `DecidableEq (NU U)` needed). -/
theorem support_single_one_eq (p : FreeProduct.NU U) :
    (MonoidAlgebra.single p (1 : ℕ)).coeff.support = {p} := by
  ext r
  constructor
  · intro hr
    exact Finsupp.support_single_subset hr
  · intro hr
    rw [Finset.mem_singleton] at hr
    subst hr
    rw [Finsupp.mem_support_iff, MonoidAlgebra.coeff_single]
    simp

/-- The tail set of a single `U`-letter. -/
theorem T_single_Ugen (V : Subgroup U) (u : U) :
    Orbit.T {FreeProduct.NU.Ugen u} V = {w : U | u * w ∈ V} := by
  ext w
  simp only [Orbit.T, Finset.mem_singleton, forall_eq, FreeProduct.NU.Ugen_mul,
    Ugen_mem_NUV_iff]

/-- **The base branch `x = ofGroup u` of the induction**: `T {Ugen u} V = u⁻¹V` on both sides. -/
theorem exists_inv_ofGroup (u : U) : ∃ S : Subgroup U, Inv (RatU.ofGroup u) S := by
  refine ⟨⊥, ?_, fun _ _ => bot_le, ?_⟩
  · rw [F_ofGroup]; trivial
  · intro V _
    have hsupp : (FreeProduct.Psi (RatU.ofGroup u)).coeff.support
        = {FreeProduct.NU.Ugen u} := by
      rw [FreeProduct.Psi_ofGroup]
      exact support_single_one_eq _
    rw [hsupp, T_single_Ugen, T_single_Ugen]
    ext w
    constructor
    · intro hw
      refine ⟨u⁻¹, ?_, u * w, hw, ?_⟩
      · simp
      · rw [← mul_assoc, inv_mul_cancel, one_mul]
    · rintro ⟨s, hs, v, hv, rfl⟩
      have h1 : u * s = 1 := by
        have h2 : u * s ∈ (⊥ : Subgroup U) := hs
        simpa using h2
      change u * (s * v) ∈ V
      rw [← mul_assoc, h1, one_mul]
      exact hv

/-! ### The theorem

**[DHS04, Theorem 5.7]** — the existence of the source subgroup — is now **proved** in
`Submission.Work.ORHughesFree.Rat.source_subgroup_exists` (module
`Submission.Work.ORHughesFree.Rat.source_subgroup_exists`, theorem
`Work.ORHughesFree.Rat.source_subgroup_exists`), by the route of `Rat/Source/` (`F`, `FL`, the
induction `exists_least_of_cases`) rather than by the tail-law invariant `Inv` of the present file.
The former legacy statements of this file (`exists_inv`, whose tail-law invariant is not needed for
the theorem, and the wrapper `exists_source_subgroup_weak` that consumed it) have been removed
together with their `sorry`; the reduction `exists_source_subgroup_weak_of_le` below — from a least
element of `Rat.F α` to the theorem — is kept, and is used by `Rat.source_subgroup_exists`. -/

end Work.ORHughesFree.Rat
