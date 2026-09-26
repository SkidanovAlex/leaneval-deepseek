import Mathlib
import Submission.Work.SG.Defs
import Submission.Work.SG.Data.SellCheck
import Submission.Work.SG.boxVecs_iff
import Submission.Work.SG.abs_le_three_of_sellingGraph

namespace Work.SG

open Work.SG.Data

/-! # `boxVecs` = `sellingVecs` (the `[-3,3]³` path bound)

`Work.SG.Data.boxVecs E` (in `Submission/Work/SG/Data/SellCheck.lean`) enumerates the vectors
`y = (y₀,y₁,y₂)` with all coordinates in `[-3,3]`, `y ≠ 0`, and `|x a - x b| ≤ 1` on every
edge `(a,b) ∈ E`, where `x = (0, y₀, y₁, y₂) : Fin 4 → ℤ`.  `Work.SG.sellingVecs E`
(`Defs.lean`) is the same condition without the coordinate bound.  The claim is that the bound
is automatic for the six Selling support graphs `Work.SG.sellingGraph i` (`i : Fin 6`, defined in
`Defs.lean` as `K₄`, `K₄ - 01`, the 4-cycle `0123`, the paw, the path `0123`, the star at 0):
each graph is connected on the four vertices `0,1,2,3`, so every vertex is joined to `0` by a
walk of at most 3 edges, and each edge changes the height `x` by at most 1 in absolute value;
hence `|x m| ≤ 3` for all `m`, i.e. `|y k| ≤ 3`.

Route: use `List.mem_filterMap`/`List.mem_flatMap` to turn `y ∈ boxVecs E` into the flat
conditions (`y != V3.zero`, `E.all …`, `(x a - x b).natAbs ≤ 1`), `List.all_eq_true`, the
identification `![0, y.x, y.y, y.z] = Fin.cons 0 y.toFun`, and `Int.natAbs` vs `|·|`.  The
converse direction (which needs the bound) is a case analysis on `i : Fin 6` using the explicit
paths in each graph: for `K₄`, the paw and the star `|y k| ≤ 1`; for `K₄ - 01` `|y 0| ≤ 2`;
for the 4-cycle `|y 1| ≤ 2`; for the path `0123` `|y 0| ≤ 1`, `|y 1| ≤ 2`, `|y 2| ≤ 3`. 

The two halves are proven in the sibling modules
`Submission/Work/SG/boxVecs_iff.lean` (the flat characterisation of `boxVecs` membership, with the coordinate bound as a hypothesis) and `Submission/Work/SG/abs_le_three_of_sellingGraph.lean` (for each of the six support graphs every vertex is within 3 edges of 0, whence the bound). This file assembles them: it identifies the two height vectors (`![0, y.x, y.y, y.z] = Fin.cons 0 y.toFun`), transports the edge conditions across that identification, and converts between the two encodings `|u| ≤ 1` and `u.natAbs ≤ 1`. -/

/-- The height vector `x = (0,y₀,y₁,y₂)` of `boxVecs` is `Fin.cons 0 y.toFun`. -/
private lemma cons_eq (y : V3) :
    (![0, y.x, y.y, y.z] : Fin 4 → ℤ) = Fin.cons (0 : ℤ) y.toFun := by
  funext k
  fin_cases k <;> simp [V3.toFun]

/-- `boxVecs` uses `V3.zero`; `sellingVecs` uses the zero function. -/
private lemma toFun_eq_zero_iff (y : V3) : y.toFun = 0 ↔ y = V3.zero := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp [V3.toFun] at h0 h1 h2
    cases y
    simp_all [V3.zero]
  · intro h
    subst h
    funext k
    fin_cases k <;> rfl

/-- `|·| ≤ 1` on `ℤ` is `natAbs ≤ 1` (the two encodings used by `sellingVecs`/`boxVecs`). -/
private lemma abs_le_one_iff_natAbs_le_one (u : ℤ) : |u| ≤ 1 ↔ u.natAbs ≤ 1 := by
  rw [abs_le]
  constructor
  · intro ⟨h1, h2⟩; omega
  · intro h; exact ⟨by omega, by omega⟩

/-- **The `[-3,3]³` bound is automatic on the six Selling support graphs.**  For every `i`, the
vectors of `sellingVecs (sellingGraph i)` are enumerated by `boxVecs (sellingGraph i)`. -/
theorem mem_boxVecs {i : Fin 6} {y : Work.SG.Data.V3} :
    y ∈ Work.SG.Data.boxVecs (Work.SG.sellingGraph i) ↔
      y.toFun ∈ Work.SG.sellingVecs (Work.SG.sellingGraph i) := by
  rw [boxVecs_iff]
  simp only [sellingVecs, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hne, hedge, -⟩
    refine ⟨?_, ?_⟩
    · intro h; exact hne ((toFun_eq_zero_iff y).mp h)
    · intro e he
      have h := hedge e he
      rw [cons_eq] at h
      exact (abs_le_one_iff_natAbs_le_one _).mpr h
  · rintro ⟨hne, hedge⟩
    refine ⟨?_, ?_, ?_⟩
    · intro h; exact hne ((toFun_eq_zero_iff y).mpr h)
    · intro e he
      rw [cons_eq]
      exact (abs_le_one_iff_natAbs_le_one _).mp (hedge e he)
    · intro k
      have h := abs_le_three_of_sellingGraph i (x := Fin.cons 0 y.toFun) (by simp) hedge
        k.succ
      simpa [Fin.cons_succ] using h

end Work.SG
