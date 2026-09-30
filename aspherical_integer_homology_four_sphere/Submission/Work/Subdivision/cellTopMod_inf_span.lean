/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.Subdivision.Level

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The span of a single top cell meets the refined `n`-skeleton trivially

In degree `n+1` the cellular chain module of a `PolyCW` is free on the
`(n+1)`-cells, and the refined filtration `cellTopMod P hdd n E (n+1)` is, by
definition, the `n`-skeleton (`⊥` in this degree, since `cellSubMod` truncates
at dimension `n`) together with the cells of `E`.  Hence it is exactly the span
of the basis vectors `cellElem e` for the `(n+1)`-cells `e ∈ E`, and a cell
`a ∉ E` therefore spans a line meeting this submodule trivially.

This is the elementary point that lets the `(n+1)`-graded piece of the skeletal
filtration be split into the contributions of the individual cells.
-/

namespace Work.Subdivision

/-- In the free module `ι →₀ ℤ`, the span of the standard basis vectors indexed
by `S` meets the line spanned by a basis vector of an index outside `S`
trivially. -/
lemma span_single_inf_span_single (ι : Type*) (S : Set ι) (a : ι) (ha : a ∉ S) :
    (Submodule.span ℤ {v : ι →₀ ℤ | ∃ i ∈ S, v = Finsupp.single i 1}) ⊓
      (Submodule.span ℤ ({Finsupp.single a 1} : Set (ι →₀ ℤ))) = ⊥ := by
  have hspan : Submodule.span ℤ {v : ι →₀ ℤ | ∃ i ∈ S, v = Finsupp.single i 1}
      = Finsupp.supported ℤ ℤ S := by
    rw [Finsupp.supported_eq_span_single]
    congr 1
    ext v
    exact ⟨fun ⟨i, hi, h⟩ => ⟨i, hi, h.symm⟩, fun ⟨i, hi, h⟩ => ⟨i, hi, h.symm⟩⟩
  rw [hspan, Submodule.eq_bot_iff]
  intro y hy
  rw [Submodule.mem_inf] at hy
  obtain ⟨hy1, hy2⟩ := hy
  rw [Finsupp.mem_supported'] at hy1
  have hy2' : y ∈ Finsupp.supported ℤ ℤ ({a} : Set ι) := by
    rw [Finsupp.supported_eq_span_single]
    rwa [Set.image_singleton]
  rw [Finsupp.mem_supported'] at hy2'
  ext b
  by_cases hb : b = a
  · subst hb; exact hy1 b ha
  · exact hy2' b (by simpa using hb)

namespace PolyCW

universe u

variable {P : PolyCW.{u}}

/-- In degree `n+1` the refined filtration `cellTopMod n E` is the span of the
basis vectors of the `(n+1)`-cells lying in `E`. -/
lemma cellTopMod_succ (hdd : P.HasDdZero) (n : ℕ) (E : Finset P.Cell) :
    cellTopMod P hdd n E (n+1) =
      Submodule.span ℤ {v : {e : P.Cell // P.dim e = n+1} →₀ ℤ |
        ∃ i : {e : P.Cell // P.dim e = n+1}, i.1 ∈ E ∧ v = Finsupp.single i 1} := by
  rw [cellTopMod, cellSubMod_eq_bot P hdd (by omega), bot_sup_eq]
  congr 1
  ext v
  constructor
  · rintro ⟨e, he, hd, rfl⟩
    exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨e, he, e.2, rfl⟩

end PolyCW

theorem cellTopMod_inf_span (P : Work.Subdivision.PolyCW) (hdd : P.HasDdZero) (n : ℕ)
    (E : Finset P.Cell) {a : P.Cell} (ha : P.dim a = n + 1) (hE : a ∉ E) :
    Work.Subdivision.PolyCW.cellTopMod P hdd n E (n + 1) ⊓
      Submodule.span ℤ ({Work.Subdivision.PolyCW.cellElem P hdd (n + 1) ⟨a, ha⟩} :
        Set ((P.cellChain hdd).X (n + 1))) = ⊥ := by
  rw [PolyCW.cellTopMod_succ (P := P) hdd n E]
  exact span_single_inf_span_single _ {i : {e : P.Cell // P.dim e = n+1} | i.1 ∈ E}
    ⟨a, ha⟩ (by simpa using hE)

end Work.Subdivision
