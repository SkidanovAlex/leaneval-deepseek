/-
  WilG4a : vocabulary for `Work.WilG4a.setOf_lt_graph_mem` (comparison of two `Ω`-graphs).

  Given two functions `f g : ℝ^p → ℝ` whose graphs are `Ω`-definable, we want the set
  `{l : Fin p → ℝ | f l < g l}` to be `Ω`-definable again (with a format depending only on
  the format of the graphs and a degree polynomial in their degree).

  The construction is the standard one for a *comparison* of two definable functions: put the
  two values into two different coordinates of a common ambient space and cut by the
  coordinate half-space `y < t`.  Concretely, in `ℝ^{p+2}` with coordinates

    * `0, …, p-1` — the parameters `l`;
    * `p`         — `y`, the value of `f`;
    * `p+1`       — `t`, the value of `g`,

  the joint set is

    `ltJoint p f g = graphLift f ∩ pullZ2 p (graphOf g) ∩ yLtT p`

  where

  * `graphLift f = {w | Fin.init w ∈ graphOf f}` is the graph of the one-parameter family
    `(l, t) ↦ f l` (the value of `f` sits in coordinate `p`, coordinate `p+1` is free — this is
    `SOMin.prod_right` applied to `graphOf f`);
  * `pullZ2 p Z` (from `WilG4a.fiber_defs`) is the coordinate pullback along `iota1 p`, which
    reads the coordinates `(l, t)` of `ℝ^{p+2}`; applied to `graphOf g` it says `t = g l`;
  * `yLtT p = {w | w (last of the first p+1) < w (last)}` is the half-space `y < t`.

  Two projections (`projLast`, i.e. `SOMin.proj`) eliminate `t` and then `y`, and the result
  is exactly `{l | f l < g l}`: projecting `t` out of `y = f l ∧ t = g l ∧ y < t` leaves
  `y = f l ∧ f l < y`, and projecting `y` out leaves `f l < g l` (this set identity is
  `Work.WilG4a.ltJoint_proj_eq`).

  This file holds the vocabulary and the coordinate-reading lemma; the `Ω`-bookkeeping is in
  `Submission.Work.WilG4a.setOf_lt_graph_mem`.
-/
import Mathlib
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG4a.fiber_defs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4a

open WilkiesDesign WilkiesConjecture

/-- `{w : ℝ^{p+2} | Fin.init w ∈ graphOf f}`: in the coordinates `(l, y, t)` this is the
condition `y = f l`.  It is `SOMin.prod_right` applied to `graphOf f` (with `n = p`). -/
def graphLift {p : ℕ} (f : (Fin p → ℝ) → ℝ) : Set (Fin (p + 2) → ℝ) :=
  {w | Fin.init w ∈ graphOf f}

/-- The joint set of the comparison of the graphs of `f` and `g` inside `ℝ^{p+2}` with
coordinates `(l, y, t)`: `y = f l` (lifted graph of `f`), `t = g l` (pullback of `graphOf g`
along `iota1 p`) and `y < t`. -/
def ltJoint (p : ℕ) (f g : (Fin p → ℝ) → ℝ) : Set (Fin (p + 2) → ℝ) :=
  graphLift f ∩ pullZ2 p (graphOf g) ∩ yLtT p

/-- **Reading the joint set.**  A vector `Fin.snoc (Fin.snoc l z) t` of `ℝ^{p+2}` (coordinates
`(l, z, t)`) lies in `ltJoint p f g` exactly when `z = f l`, `t = g l` and `z < t`. -/
theorem snoc_snoc_mem_ltJoint {p : ℕ} (f g : (Fin p → ℝ) → ℝ) (l : Fin p → ℝ) (z t : ℝ) :
    Fin.snoc (Fin.snoc l z) t ∈ ltJoint p f g ↔ z = f l ∧ t = g l ∧ z < t := by
  have h1 : Fin.snoc (Fin.snoc l z) t ∈ graphLift f ↔ z = f l := by
    rw [graphLift, Set.mem_ofPred_eq, Fin.init_snoc]
    simp [graphOf]
  have h2 : Fin.snoc (Fin.snoc l z) t ∈ pullZ2 p (graphOf g) ↔ t = g l := by
    rw [pullZ2, Set.mem_ofPred_eq, comp_iota1]
    simp only [Fin.init_snoc, Fin.snoc_last]
    simp [graphOf]
  have h3 : Fin.snoc (Fin.snoc l z) t ∈ yLtT p ↔ z < t := by
    simp only [yLtT, Set.mem_ofPred_eq, Fin.snoc_last, Fin.snoc_castSucc]
  rw [ltJoint, Set.mem_inter_iff, Set.mem_inter_iff, h1, h2, h3]
  constructor
  · rintro ⟨⟨ha, hb⟩, hc⟩; exact ⟨ha, hb, hc⟩
  · rintro ⟨ha, hb, hc⟩; exact ⟨⟨ha, hb⟩, hc⟩

end Work.WilG4a
