import Mathlib
import Submission.Work.Compact.Noncompact.Good
import Submission.Work.Compact.Noncompact.exists_localMap_eq_zero

/-!
# A chain is supported in an open set with compact closure

Let `X` be a topological space in which every point has an open neighbourhood with compact closure
(`hX`).  Then every singular `k`-chain `c` of `X` (with `ℤ` coefficients) is supported in some open
set `U` with compact closure: there is `U` open, `IsCompact (closure U)`, and `c ∈ suppS X U k`.

The proof is the standard one: a chain is a *finite* `ℤ`-linear combination of generators
`ιChainComplex t` (`chain_eq_sum_ιChainComplex`); the image of `t` is compact, so finitely many of
the `hX`-neighbourhoods cover it, and their union is an open set with compact closure.  A generator
whose simplex lands in `U` lies in `C_*(U) → C_*(X)` (`inclChains_f_ι_liftSimplex`), and a
submodule is closed under finite sums.
-/

set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Compact.Noncompact

noncomputable section

open scoped BigOperators

/-- **A singular simplex lands in an open set with compact closure.**

If every point of `X` has an open neighbourhood with compact closure, then for every singular
`n`-simplex `t` of `X` there is an open set `V` with compact closure containing the image of `t`.

The image of `t` is compact; cover it by the `hX`-neighbourhoods of its points and extract a finite
subcover `V = ⋃_{x ∈ s} U x`.  Its closure is `⋃_{x ∈ s} closure (U x)`, a finite union of compact
sets. -/
lemma exists_isOpen_isCompact_closure_forall_mem_simplex {X : TopCat}
    (hX : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsCompact (closure U))
    {n : ℕ} (t : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    ∃ V : Set X, IsOpen V ∧ IsCompact (closure V) ∧
      ∀ z, TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n)) t z ∈ V := by
  classical
  let f := TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n)) t
  have hK : IsCompact (Set.range f) := isCompact_range f.continuous
  choose U hU using hX
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U (fun x => (hU x).1)
    (fun y _ => Set.mem_iUnion.mpr ⟨y, (hU y).2.1⟩)
  refine ⟨⋃ x ∈ s, U x, isOpen_biUnion (fun x _ => (hU x).1), ?_, ?_⟩
  · rw [Finset.closure_biUnion]
    exact s.isCompact_biUnion (fun x _ => (hU x).2.2)
  · intro z
    exact hs ⟨z, rfl⟩

/-- **A singular chain is supported in an open set with compact closure.**

If every point of `X` has an open neighbourhood with compact closure, then every singular `k`-chain
`c` of `X` lies in `suppS X U k` for some open `U` with `IsCompact (closure U)`. -/
theorem exists_suppS_isCompact_closure {X : TopCat}
    (hX : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsCompact (closure U)) (k : ℕ)
    (c : Work.Compact.Noncompact.Ch X k) :
    ∃ U : Set X, IsOpen U ∧ IsCompact (closure U) ∧ c ∈ Work.Compact.Noncompact.suppS X U k := by
  classical
  obtain ⟨S, a, hc⟩ := chain_eq_sum_ιChainComplex (TopCat.toSSet.obj X) k c
  have hper : ∀ t : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk k)),
      ∃ V : Set X, IsOpen V ∧ IsCompact (closure V) ∧
        ∀ z, TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk k)) t z ∈ V :=
    fun t => exists_isOpen_isCompact_closure_forall_mem_simplex hX t
  choose V hVopen hVcomp hVmem using hper
  refine ⟨⋃ t ∈ S, V t, isOpen_biUnion (fun t _ => hVopen t), ?_, ?_⟩
  · rw [Finset.closure_biUnion]
    exact S.isCompact_biUnion (fun t _ => hVcomp t)
  · rw [hc]
    refine Submodule.sum_mem _ (fun t ht => ?_)
    have hsub : ∀ z, TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk k)) t z ∈
        (⋃ t ∈ S, V t) :=
      fun z => Set.mem_biUnion ht (hVmem t z)
    refine ⟨((TopCat.toSSet.obj (TopCat.of (⋃ t ∈ S, V t))).ιChainComplex
      (R := ModuleCat.of ℤ ℤ) (liftSimplex t hsub)).hom (a t), ?_⟩
    exact inclChains_f_ι_liftSimplex t hsub (a t)

end

end Work.Compact.Noncompact
