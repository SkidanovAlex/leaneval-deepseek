import Mathlib
import Submission.Work.OROneRel.levelChain

/-!
# A finite set of edges of a level graph lies in a window

The windows `Wedge p q a b = winE (tlW p q) a b` of the level graph of the two-letter relator
`a ^ p * b ^ q` (see `Submission/Work/OROneRel/levelChain.lean`) are nested and cover the whole edge
set of the cover.  This file records the (elementary) fact that this covering can be made *uniform
on a finite set*: every finite set `F` of edges of the level graph is contained in a single window
`Wedge p q A B`, and the window can be chosen to contain the basic band `[0, p q]` in its levels,
i.e. with `A ≤ 0` and `(p : ℤ) * (q : ℤ) ≤ B`.

This is the "unbounded window" input used when an argument is localised on a finite piece of the
cover (a finite set of edges, a finite set of relators, …).

## Contents

* `exists_winE_of_finite` -- the general statement for an arbitrary weight `c : α → ℤ`;
* `exists_window_of_finite` -- its two-letter specialisation to `Wedge p q`.
-/

namespace Work.OROneRel

universe u

open Set

/-- **A finite set of edges of a level graph fits into a window.**  For an arbitrary weight
`c : α → ℤ` and a finite set `F` of edges of the `ℤ`-cover there are integers `A ≤ 0` and `B ≥ N`
such that `F` is contained in the window `winE c A B`, i.e. both endpoints `e.2` and `e.2 + c e.1` of
every edge `e ∈ F` lie in `[A, B]`.

(The lower bound is `-(∑_{s ∈ S} |s|)` where `S` collects the endpoint levels of the edges of `F`,
and the upper bound is `max N (∑_{s ∈ S} |s|)`; both are `≤`/`≥` the required quantities because
`s ≤ |s| ≤ ∑_{t ∈ S} |t|`.) -/
theorem exists_winE_of_finite {α : Type u} (c : α → ℤ) (F : Set (α × ℤ)) (hF : F.Finite)
    (N : ℤ) : ∃ A B : ℤ, A ≤ 0 ∧ N ≤ B ∧ ∀ e ∈ F, e ∈ winE c A B := by
  classical
  set S : Finset ℤ := hF.toFinset.image Prod.snd ∪
    hF.toFinset.image (fun e : α × ℤ => e.2 + c e.1) with hS
  have hSnn : 0 ≤ S.sum (fun s => |s|) := Finset.sum_nonneg fun s _ => abs_nonneg s
  refine ⟨-(S.sum fun s => |s|), max N (S.sum fun s => |s|), by omega, le_max_left _ _, ?_⟩
  intro e he
  rw [mem_winE]
  have he1 : e.2 ∈ S := by
    rw [hS]
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, hF.mem_toFinset.mpr he, rfl⟩)
  have he2 : e.2 + c e.1 ∈ S := by
    rw [hS]
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, hF.mem_toFinset.mpr he, rfl⟩)
  have h1 : |e.2| ≤ S.sum (fun s => |s|) :=
    Finset.single_le_sum (fun s _ => abs_nonneg s) he1
  have h2 : |e.2 + c e.1| ≤ S.sum (fun s => |s|) :=
    Finset.single_le_sum (fun s _ => abs_nonneg s) he2
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := neg_abs_le e.2
    linarith
  · exact le_trans (le_abs_self e.2) (le_trans h1 (le_max_right _ _))
  · have := neg_abs_le (e.2 + c e.1)
    linarith
  · exact le_trans (le_abs_self (e.2 + c e.1)) (le_trans h2 (le_max_right _ _))

/-- **A finite set of edges of the two-letter level graph is contained in a window**: there are
`A ≤ 0` and `(p : ℤ) * (q : ℤ) ≤ B` with `F ⊆ Wedge p q A B`. -/
theorem exists_window_of_finite (p q : ℕ) (F : Set (Fin 2 × ℤ)) (hF : F.Finite) :
    ∃ A B : ℤ, A ≤ 0 ∧ (p : ℤ) * (q : ℤ) ≤ B ∧ F ⊆ Work.OROneRel.Wedge p q A B := by
  obtain ⟨A, B, hA, hB, hsub⟩ :=
    exists_winE_of_finite (tlW p q) F hF ((p : ℤ) * (q : ℤ))
  exact ⟨A, B, hA, hB, fun e he => hsub e he⟩

end Work.OROneRel
