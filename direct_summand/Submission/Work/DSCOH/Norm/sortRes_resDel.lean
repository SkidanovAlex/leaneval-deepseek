/-
Area DSCOH (curric-46) — the normalization comparison: sorting a tuple commutes with deleting
an entry.

The stable sorting permutation `Tuple.sort` interacts with the deletion `del x b` (delete the
`b`-th entry) as follows: sorting the tuple `del x b` and then deleting nothing is the same as
first sorting `x` and then deleting the entry of the sorted tuple that came from position `b`.
Concretely (`Work.DSCOH.Norm.del_sortIdx_eq_del_comp_sort`)

  `del (sortIdx x).val ((Tuple.sort x).symm b) = (del x b) ∘ Tuple.sort (del x b)`,

which is the tuple-level content of `Work.DSCOH.Norm.sort_comp_succAbove`.

The main theorem of this file, `Work.DSCOH.Norm.sortRes_resDel`, is the corresponding coherence
for the Čech restriction maps: the two ways of going from the semi-ordered term
`semiTerm P U n` to the sections over the open of the tuple `x`,
  * project at `sortIdx (del x b)`, sort, then delete the `b`-th entry, and
  * project at `del (sortIdx x).val ((Tuple.sort x).symm b)`, delete the corresponding entry
    of the sorted tuple, then sort,
agree.  Both routes are `Pi.π` at (propositionally equal) semi-indices followed by `P.map` of
morphisms of the *thin* category `(Opens X)ᵒᵖ`, so the comparison is pure bookkeeping: the two
`(Opens X)ᵒᵖ`-morphisms agree by `Subsingleton.elim`.
-/
import Mathlib
import Submission.Work.DSCOH.Norm.SortSection
import Submission.Work.DSCOH.Norm.projInclChain
import Submission.Work.DSCOH.Norm.sign_sort_succAbove

namespace Work.DSCOH.Norm

open CategoryTheory Limits Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

universe u v w

variable {X : Type u} [TopologicalSpace X] {A : Type v} [CommRing A]
variable {ι : Type w} [Fintype ι] [LinearOrder ι] [HasProducts (ModuleCat A)]

/-! ## Generic bookkeeping for products and `eqToHom` -/

/-- The projection `Pi.π f j` out of a product depends on `j : J` only up to `eqToHom`: for
`h : j = j'` one has `Pi.π f j ≫ eqToHom (congrArg f h) = Pi.π f j'`.

This is `CategoryTheory.Limits.Pi.π_comp_eqToHom` with the `eqToHom` argument displayed in the
form `congrArg f h` (the two proofs are equal by proof irrelevance, but the form matters for
later rewriting). -/
lemma pi_comp_eqToHom_congrArg {C : Type*} [Category C] {J : Type*} (f : J → C) [HasProduct f]
    {j j' : J} (h : j = j') : Pi.π f j ≫ eqToHom (congrArg f h) = Pi.π f j' := by
  cases h
  simp

/-- `eqToHom` of a `congrArg` of a composite `fun t => F (g t)` is `eqToHom` of the `congrArg`
of `F` applied to the `congrArg` of `g`. -/
lemma eqToHom_congrArg_comp {α β : Type*} {C : Type*} [Category C]
    (F : β → C) (g : α → β) {a a' : α} (h : a = a') :
    eqToHom (congrArg (fun t => F (g t)) h) = eqToHom (congrArg F (congrArg g h)) := by
  cases h
  simp

/-! ## Sorting commutes with deleting an entry -/

/-- **Deleting an entry commutes with sorting.**  The tuple obtained by first deleting the
`b`-th entry of `x` and then sorting is the tuple obtained by first sorting `x` and then
deleting the entry of the sorted tuple coming from position `b` (namely the `(sort x)⁻¹ b`-th
entry).

Both sides are nondecreasing reorderings of the same multiset; the proof applies
`Work.DSCOH.Norm.sort_comp_succAbove` entrywise. -/
lemma del_sortIdx_eq_del_comp_sort {n : ℕ} (x : Fin (n + 2) → ι) (b : Fin (n + 2)) :
    del ((sortIdx x).val) ((Tuple.sort x).symm b) = (del x b) ∘ Tuple.sort (del x b) := by
  funext a
  simp only [del_apply, sortIdx_val, Function.comp_apply]
  exact congrArg x (congrFun (sort_comp_succAbove x b) a)

/-- The semi-ordered index obtained by first deleting the `b`-th entry of `x` and then sorting
agrees with the semi-ordered index obtained by first sorting `x` and then deleting the
corresponding entry. -/
lemma sortIdx_del_eq {n : ℕ} (x : Fin (n + 2) → ι) (b : Fin (n + 2)) :
    sortIdx (del x b)
      = ⟨del ((sortIdx x).val) ((Tuple.sort x).symm b),
          monotone_del (sortIdx x).val ((Tuple.sort x).symm b) (sortIdx x).property⟩ := by
  refine Subtype.ext ?_
  exact (del_sortIdx_eq_del_comp_sort x b).symm

/-! ## The coherence of `sortRes` and `resDel` -/

theorem sortRes_resDel {X : Type*} [TopologicalSpace X] {A : Type*} [CommRing A]
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    [CategoryTheory.Limits.HasProducts (ModuleCat A)]
    (P : CategoryTheory.Functor (Opposite (TopologicalSpace.Opens X)) (ModuleCat A))
    (U : ι → TopologicalSpace.Opens X) {n : ℕ} (x : Fin (n + 2) → ι) (b : Fin (n + 2)) :
    CategoryTheory.CategoryStruct.comp
      (CategoryTheory.Limits.Pi.π (fun s : Work.DSCOH.Norm.SemiIdx ι n =>
          Work.DSCOH.Norm.tupleMod P U s.val) (Work.DSCOH.Norm.sortIdx (Work.DSCOH.Norm.del x b)))
      (CategoryTheory.CategoryStruct.comp (Work.DSCOH.Norm.sortRes P U (Work.DSCOH.Norm.del x b))
        (Work.DSCOH.Norm.resDel P U x b)) =
    CategoryTheory.CategoryStruct.comp
      (CategoryTheory.Limits.Pi.π (fun s : Work.DSCOH.Norm.SemiIdx ι n =>
          Work.DSCOH.Norm.tupleMod P U s.val)
        ⟨Work.DSCOH.Norm.del (Work.DSCOH.Norm.sortIdx x).val ((Tuple.sort x).symm b),
          Work.DSCOH.Norm.monotone_del (Work.DSCOH.Norm.sortIdx x).val ((Tuple.sort x).symm b)
            (Work.DSCOH.Norm.sortIdx x).property⟩)
      (CategoryTheory.CategoryStruct.comp
        (Work.DSCOH.Norm.resDel P U (Work.DSCOH.Norm.sortIdx x).val ((Tuple.sort x).symm b))
        (Work.DSCOH.Norm.sortRes P U x)) := by
  let s : SemiIdx ι n := sortIdx (del x b)
  let s' : SemiIdx ι n := ⟨del (sortIdx x).val ((Tuple.sort x).symm b),
      monotone_del (sortIdx x).val ((Tuple.sort x).symm b) (sortIdx x).property⟩
  let g : SemiIdx ι n → (Opens X)ᵒᵖ := fun t => op (tupleOp U t.val)
  let f : SemiIdx ι n → ModuleCat A := fun t => P.obj (op (tupleOp U t.val))
  -- Both sides are the projection at a semi-ordered index followed by the restriction to `x`.
  change Pi.π f s ≫ (sortRes P U (del x b) ≫ resDel P U x b)
      = Pi.π f s' ≫ (resDel P U (sortIdx x).val ((Tuple.sort x).symm b) ≫ sortRes P U x)
  have h : s = s' := sortIdx_del_eq x b
  -- The two inner composites are `P.map` of morphisms of the *thin* category `(Opens X)ᵒᵖ`.
  have hX : sortRes P U (del x b) ≫ resDel P U x b
      = P.map ((sortHom U (del x b)).op ≫ (homOfLE (leOfHom (opDel U x b))).op) := by
    simp only [sortRes, resDel, Functor.map_comp]
  have hX' : resDel P U (sortIdx x).val ((Tuple.sort x).symm b) ≫ sortRes P U x
      = P.map ((homOfLE (leOfHom (opDel U (sortIdx x).val ((Tuple.sort x).symm b)))).op
          ≫ (sortHom U x).op) := by
    simp only [sortRes, resDel, Functor.map_comp]
  rw [hX, hX']
  -- The `eqToHom` comparing the two sources is itself `P.map` of the corresponding `eqToHom`.
  have hge : (eqToHom (congrArg f h) : f s ⟶ f s') = P.map (eqToHom (congrArg g h)) := by
    rw [eqToHom_congrArg_comp P.obj g h, eqToHom_map]
  -- Both `(Opens X)ᵒᵖ`-morphisms have the same source and target, so they are equal.
  have key : P.map ((sortHom U (del x b)).op ≫ (homOfLE (leOfHom (opDel U x b))).op)
      = eqToHom (congrArg f h) ≫
        P.map ((homOfLE (leOfHom (opDel U (sortIdx x).val ((Tuple.sort x).symm b)))).op
          ≫ (sortHom U x).op) := by
    rw [hge, ← P.map_comp]
    exact congrArg P.map (Subsingleton.elim _ _)
  rw [key, ← Category.assoc, pi_comp_eqToHom_congrArg f h]

end Work.DSCOH.Norm
