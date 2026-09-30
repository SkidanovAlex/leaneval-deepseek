import Mathlib
import Submission.Work.ConvexCells.Basic
import Submission.Work.ConvexCells.tightAt_flagPt
import Submission.Work.ConvexCells.Main

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The flag carrier from the basic checks only

`PolytopeData.checksBasic = true` gives `PolytopeData.OkBasic`, a strictly weaker hypothesis than
`P.Ok` (which additionally bundles the emptiness and adding-constraint certificate groups
`OkEmp`/`OkAdd`).  The face-compatibility statement `tightAt s.toE' = tight s.topFace` never uses
those two groups: it only needs the `pos` conditions of `OkBasic`.  This file provides the
`OkBasic`-flavoured versions of the few lemmas involved and proves `sd_carrier_of_basic`.

The lemmas of `ConvexCells/tightAt_flagPt.lean` are stated under `P.Ok`; the proofs below are the
same proofs with the accessors `Ok.D_pos`/`Ok.pos_pos`/`Ok.pos_neg` replaced by the direct
projections out of `OkBasic` (which is the first conjunct of `Ok`).
-/

namespace Work.ConvexCells

open scoped BigOperators
open PolytopeData

variable {d : ℕ}

/-! ### The `OkBasic` accessors -/

theorem okBasic_D_pos {P : PolytopeData d} (h : P.OkBasic) : 0 < P.D := h.1

theorem okBasic_pos_pos {P : PolytopeData d} (h : P.OkBasic) (f : Fin P.K) :
    ∀ i ∈ P.tight f, ∑ j, P.nrm i j * P.pos f j = (P.D : ℤ) * P.rhs i :=
  (h.2.2.2.1 f).1

theorem okBasic_pos_neg {P : PolytopeData d} (h : P.OkBasic) (f : Fin P.K) :
    ∀ i, i ∉ P.tight f → ∑ j, P.nrm i j * P.pos f j < (P.D : ℤ) * P.rhs i :=
  (h.2.2.2.1 f).2

/-! ### The real geometry of the `pos` points from `OkBasic` -/

theorem inner_nR_posR_of_mem_basic {P : PolytopeData d} (h : P.OkBasic) (f : Fin P.K)
    (i : Fin P.m) (hi : i ∈ P.tight f) :
    inner ℝ (P.nR i) (P.posR f) = P.bR i := by
  have hDpos : (0 : ℝ) < (P.D : ℝ) := by exact_mod_cast okBasic_D_pos h
  have hpos : ((∑ j, P.nrm i j * P.pos f j : ℤ) : ℝ) = (P.D : ℝ) * (P.rhs i : ℝ) := by
    have := okBasic_pos_pos h f i hi
    push_cast
    exact_mod_cast this
  refine mul_left_cancel₀ (by positivity : ((P.D : ℝ) ^ 2) ≠ 0) ?_
  rw [D_sq_mul_inner P (okBasic_D_pos h) i f, hpos, bR]
  field_simp

theorem inner_nR_posR_of_not_mem_basic {P : PolytopeData d} (h : P.OkBasic) (f : Fin P.K)
    (i : Fin P.m) (hi : i ∉ P.tight f) :
    inner ℝ (P.nR i) (P.posR f) < P.bR i := by
  have hDpos : (0 : ℝ) < (P.D : ℝ) := by exact_mod_cast okBasic_D_pos h
  have hpos : ((∑ j, P.nrm i j * P.pos f j : ℤ) : ℝ) < (P.D : ℝ) * (P.rhs i : ℝ) := by
    have := okBasic_pos_neg h f i hi
    push_cast
    exact_mod_cast this
  have hkey : ((P.D : ℝ) ^ 2) * inner ℝ (P.nR i) (P.posR f) < ((P.D : ℝ) ^ 2) * P.bR i := by
    rw [D_sq_mul_inner P (okBasic_D_pos h) i f, bR]
    have hDne : (P.D : ℝ) ≠ 0 := ne_of_gt hDpos
    have : ((P.D : ℝ) ^ 2) * ((P.rhs i : ℝ) / (P.D : ℝ)) = (P.D : ℝ) * (P.rhs i : ℝ) := by
      field_simp
    rw [this]
    exact hpos
  exact lt_of_mul_lt_mul_left hkey (by positivity)

theorem tightAt_posR_basic {P : PolytopeData d} (h : P.OkBasic) (f : Fin P.K) :
    P.tightAt (P.posR f) = P.tight f := by
  ext i
  rw [mem_tightAt_iff]
  constructor
  · intro hi
    by_contra hc
    exact absurd hi (not_le.mpr (inner_nR_posR_of_not_mem_basic h f i hc))
  · intro hi; exact le_of_eq (inner_nR_posR_of_mem_basic h f i hi).symm

theorem posR_mem_Pset_basic {P : PolytopeData d} (h : P.OkBasic) (f : Fin P.K) :
    P.posR f ∈ P.Pset := by
  intro i
  by_cases hi : i ∈ P.tight f
  · rw [inner_nR_posR_of_mem_basic h f i hi]
  · exact le_of_lt (inner_nR_posR_of_not_mem_basic h f i hi)

theorem inner_posR_eq_iff_basic {P : PolytopeData d} (h : P.OkBasic) (f : Fin P.K)
    (k : Fin P.m) :
    inner ℝ (P.nR k) (P.posR f) = P.bR k ↔ k ∈ P.tight f := by
  constructor
  · intro heq
    by_contra hk
    exact absurd heq (ne_of_lt (inner_nR_posR_of_not_mem_basic h f k hk))
  · exact inner_nR_posR_of_mem_basic h f k

/-! ### The flag combinatorics -/

/-- A constraint is tight at every face of a flag iff it is tight at the *last* (largest) face.
`IsFlag` orders the faces from the smallest to the largest, so the tight sets decrease along the
list and their common intersection is the tight set of the last entry. -/
theorem flag_forall_tight_iff_basic (P : PolytopeData d) (s : P.FlagPt) (k : Fin P.m) :
    (∀ i : Fin s.flag.length, k ∈ P.tight (s.flag.get i)) ↔ k ∈ P.tight s.topFace := by
  have hpos : 0 < s.flag.length := List.length_pos_of_ne_nil s.flag_ne_nil
  have hlast : s.flag.get ⟨s.flag.length - 1, by omega⟩ = s.flag.getLast s.flag_ne_nil := by
    rw [List.get_eq_getElem, List.getLast_eq_getElem]
  constructor
  · intro hh
    rw [PolytopeData.FlagPt.topFace, ← hlast]
    exact hh _
  · intro hk i
    rw [PolytopeData.FlagPt.topFace, ← hlast] at hk
    by_cases hi : i = (⟨s.flag.length - 1, by omega⟩ : Fin s.flag.length)
    · rw [hi]; exact hk
    · have hlt : i < (⟨s.flag.length - 1, by omega⟩ : Fin s.flag.length) := by
        show (i : ℕ) < s.flag.length - 1
        have hi' := i.isLt
        have hne : (i : ℕ) ≠ s.flag.length - 1 := fun hc => hi (Fin.ext hc)
        omega
      have hsub := List.Pairwise.rel_get_of_lt s.isFlag hlt
      exact hsub.1 hk

/-- The tight set of the affine realization of a flag is the tight set of the top (largest) face of
the flag, using only the basic checks. -/
theorem tightAt_flagPt_basic (P : PolytopeData d) (h : P.OkBasic) (s : P.FlagPt) :
    P.tightAt s.toE' = P.tight s.topFace := by
  ext k
  have hstep : k ∈ P.tightAt s.toE' ↔ (∀ i : Fin s.flag.length, k ∈ P.tight (s.flag.get i)) := by
    unfold PolytopeData.FlagPt.toE'
    have hc := tightAt_combo P (s := Finset.univ) (w := s.wt)
      (z := fun i => P.posR (s.flag.get i))
      (fun i _ => le_of_lt (s.wt_pos i)) s.wt_sum
      (fun i _ => posR_mem_Pset_basic h (s.flag.get i)) k
    rw [hc]
    constructor
    · intro hh i
      rw [← inner_posR_eq_iff_basic h (s.flag.get i) k]
      exact hh i (Finset.mem_univ i) (ne_of_gt (s.wt_pos i))
    · intro hh i _ _
      rw [inner_posR_eq_iff_basic h (s.flag.get i) k]
      exact hh i
  rw [hstep]
  exact flag_forall_tight_iff_basic P s k

end Work.ConvexCells

namespace Work.MbarHomology.ConvexCells

/-- The face compatibility of the flag realization needs only the basic checks: the tight set at the
realization `s.toE'` of a flag point is the tight set of the top face of the flag. -/
theorem sd_carrier_of_basic {d : ℕ} (P : Work.ConvexCells.PolytopeData d)
    (hb : P.checksBasic = true) (s : P.FlagPt) :
    P.tightAt s.toE' = P.tight s.topFace :=
  Work.ConvexCells.tightAt_flagPt_basic P (of_decide_eq_true hb) s

end Work.MbarHomology.ConvexCells
