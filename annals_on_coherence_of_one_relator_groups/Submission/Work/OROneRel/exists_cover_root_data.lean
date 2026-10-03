/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The existence of a gauge whose `Z`-cover root is strictly shorter and tracks `u`

This file proves `Work.OROneRel.exists_cover_root_data`: for a weight `c : α → ℤ` with
`cohom c u = 1`, at least two visited levels and a non-empty decorated word, there is a gauge
`W : ℤ → FreeGroup α` with `W 0 = 1` such that

* `relatorNorm (coverRoot W c u) < relatorNorm u` (the strictly shorter root),
* `coverToClasses W c u (coverRoot W c u) = u` (the root tracks `u`), and
* there is a homomorphism `⟨(coverRoot W c u) ^ l⟩ →* ⟨u ^ l⟩` carrying the class of `coverRoot` to
  the class of `u` (the root survives the exponent `l`).

The three ingredients are

* `Work.OROneRel.exists_coverRoot_norm` (proved in the workspace): a gauge with
  `W 0 = 1` and `relatorNorm (coverRoot W c u) < relatorNorm u`, obtained by gauging away one
  decorated letter of non-zero `c`-weight;
* `Work.OROneRel.gauge_truncation` (proved in the workspace), which computes `u` as the product of
  the loop classes of the decorated letters of non-trivial loop class;
* the identity `coverToClasses_coverRoot_eq` below, which computes the class of `coverRoot` as the
  *same* product, so that the two combine to `coverToClasses (coverRoot) = u` by `gauge_truncation`.

Note on the conventions of `coverRootDefs.lean`: `coverRootList` emits every decorated letter of
non-trivial loop class with the constant exponent `true`, i.e. `coverRoot` is the product of the
*symbols* of the decorated letters, while `coverToClasses` sends the symbol of `p` to the loop class
`coverClass W c p` *of the traversal*.  With these conventions the class of `coverRoot` is exactly
the product computed by `gauge_truncation`.

(The statement below is recorded exactly as requested; the `universe u` declaration, needed for the
`{α : Type u}` of the statement to elaborate, has been added.)
-/
import Mathlib
import Submission.Work.OROneRel.coverRootDefs
import Submission.Work.OROneRel.exists_coverRoot_norm
import Submission.Work.OROneRel.gauge_truncation
import Submission.Work.OROneRel.GaugeDefs
import Submission.Work.OROneRel.MagnusGenDefs

namespace Work.OROneRel

universe u

open Classical

/-! ## 1. Three general lemmas -/

/-- A `filterMap` over an attached list whose function only depends on the *value* is a `filterMap`
over the list itself. -/
theorem filterMap_attach_eq {γ M : Type*} (L : List γ) (N : γ → Option M) :
    L.attach.filterMap (fun p : {x // x ∈ L} => N p.1) = L.filterMap N := by
  conv_rhs => rw [← List.attach_map_subtype_val (l := L)]
  rw [List.filterMap_map]
  rfl

/-- **Filtering is a `filterMap`.**  A `filterMap` that keeps exactly the letters of non-trivial loop
class is the filtered list, mapped by the loop class. -/
theorem filterMap_ite_coverClass_eq_map_filter {α : Type u} (L : List ((α × ℤ) × Bool))
    (W : ℤ → FreeGroup α) (c : α → ℤ) :
    L.filterMap (fun p => if _ : coverClass W c p ≠ 1 then some (coverClass W c p) else none)
      = (L.filter (fun p => decide (coverClass W c p ≠ 1))).map (fun p => coverClass W c p) := by
  induction L with
  | nil => rfl
  | cons a t ih =>
      rw [List.filter_cons]
      by_cases h : coverClass W c a ≠ 1
      · rw [if_pos (decide_eq_true_iff.mpr h), List.map_cons, List.filterMap_cons, dif_pos h, ih]
      · rw [if_neg (by simpa using h), List.filterMap_cons, dif_neg h, ih]

/-- A homomorphism of presented groups is computed on the classes by the underlying homomorphism of
free groups. -/
theorem presentedGroup_map_mk {α β : Type*} (f : FreeGroup α →* FreeGroup β)
    {s : Set (FreeGroup α)} {t : Set (FreeGroup β)} (hst : Set.MapsTo f s t) (x : FreeGroup α) :
    PresentedGroup.map f hst (PresentedGroup.mk s x) = PresentedGroup.mk t (f x) :=
  QuotientGroup.map_mk (Subgroup.normalClosure s) (Subgroup.normalClosure t) f _ x

/-! ## 2. The class of `coverRoot` -/

/-- **The class of the candidate root.**  It is the product of the loop classes of the decorated
letters of `u` of non-trivial loop class -- exactly the product of `gauge_truncation`. -/
theorem coverToClasses_coverRoot_eq {α : Type u} (W : ℤ → FreeGroup α) (c : α → ℤ)
    (u : FreeGroup α) :
    coverToClasses W c u (coverRoot W c u)
      = (((decor c 0 (wordOf u)).filter (fun p => decide (coverClass W c p ≠ 1))).map
          (fun p => coverClass W c p)).prod := by
  classical
  rw [coverRoot, ← map_prod_eq_of_mk (coverToClasses W c u) (coverRootList W c u)]
  congr 1
  unfold coverRootList
  rw [List.map_filterMap]
  have hstep : ((decor c 0 (wordOf u)).attach.filterMap (fun p =>
        Option.map (fun y : coverBeta W c u × Bool => coverToClasses W c u
            (if y.2 = true then FreeGroup.of y.1 else (FreeGroup.of y.1)⁻¹))
          (if h : coverClass W c p.1 ≠ 1 then some (⟨p.1, p.2, h⟩, true) else none)))
      = ((decor c 0 (wordOf u)).attach.filterMap (fun p =>
          if h : coverClass W c p.1 ≠ 1 then some (coverClass W c p.1) else none)) := by
    refine List.filterMap_congr (fun p _ => ?_)
    by_cases h : coverClass W c p.1 ≠ 1
    · rw [dif_pos h, Option.map_some, dif_pos h]
      show some (coverToClasses W c u (FreeGroup.of (⟨p.1, p.2, h⟩ : coverBeta W c u)))
        = some (coverClass W c p.1)
      congr 1
      exact FreeGroup.lift_apply_of
    · rw [dif_neg h, dif_neg h]
      rfl
  rw [hstep]
  exact (filterMap_attach_eq (decor c 0 (wordOf u)) (fun x : (α × ℤ) × Bool =>
      if h : coverClass W c x ≠ 1 then some (coverClass W c x) else none)).trans
    (filterMap_ite_coverClass_eq_map_filter (decor c 0 (wordOf u)) W c)

/-! ## 3. The requested lemma -/

theorem exists_cover_root_data {α : Type u} (c : α → ℤ) (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    (hu : Work.OROneRel.cohom c u = 1)
    (hV : 2 ≤ (Work.OROneRel.coverLevelSet c u).ncard)
    (hN : 0 < (Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u)).length) :
    ∃ W : ℤ → FreeGroup α, W 0 = 1 ∧
      Work.OROneRel.relatorNorm (Work.OROneRel.coverRoot W c u) < Work.OROneRel.relatorNorm u ∧
      Work.OROneRel.coverToClasses W c u (Work.OROneRel.coverRoot W c u) = u ∧
      ∃ (Ψ : PresentedGroup ({(Work.OROneRel.coverRoot W c u) ^ l} :
                Set (FreeGroup (Work.OROneRel.coverBeta W c u))) →*
               PresentedGroup ({u ^ l} : Set (FreeGroup α))),
        Ψ (PresentedGroup.mk ({(Work.OROneRel.coverRoot W c u) ^ l} :
              Set (FreeGroup (Work.OROneRel.coverBeta W c u))) (Work.OROneRel.coverRoot W c u)) =
          PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u := by
  classical
  obtain ⟨W, hW0, hnorm⟩ := exists_coverRoot_norm c u hV hN
  have hclass : coverToClasses W c u (coverRoot W c u) = u := by
    rw [coverToClasses_coverRoot_eq]
    exact gauge_truncation W hW0 hu (fun p => decide (coverClass W c p ≠ 1))
      (fun p => decide_eq_true_iff)
  refine ⟨W, hW0, hnorm, hclass, ?_⟩
  have hst : Set.MapsTo (coverToClasses W c u) ({(coverRoot W c u) ^ l} : Set (FreeGroup (coverBeta W c u)))
      ({u ^ l} : Set (FreeGroup α)) := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx ⊢
    rw [hx, map_pow, hclass]
  exact ⟨PresentedGroup.map (coverToClasses W c u) hst,
    (presentedGroup_map_mk (coverToClasses W c u) hst (coverRoot W c u)).trans (by rw [hclass])⟩

end Work.OROneRel
