import Mathlib
import Submission.Work.Drive.Mono.TiltedTraceData
import Submission.Work.Drive.Mono.inter_nonempty_of_closure_inter_nonempty_plus
import Submission.Work.Drive.Mono.frontier_union_of_disjoint_closures
import Submission.Work.Drive.Mono.isEmbeddedSphere_frontier_slabCaps
import Submission.Work.Drive.Mono.isEmbeddedSphere_frontier_union_convex
import Submission.Work.Drive.Final.tls_rest_crux
import Submission.Work.Drive.Mono.frontier_isEmbeddedSphere_of_twoSide

namespace Work.Drive.Mono
/-! ## STATE OF THIS PROOF

The two regimes are

* **the one-sphere window** (`Work.Drive.Final.OneSphereWindow`: the box pokes out of both slab
  faces and, on both sides of the slab, strictly above the wall): the frontier is a *single*
  embedded sphere.  This is `Work.Drive.Mono.frontier_isEmbeddedSphere_of_twoSide`, whose proof is
  the fibre-model computation in `Work/Drive/Mono/WindowCase/` (the frontier is `tlsOuter ∪
  tlsTrough`, two discs glued along their common boundary circle, the seam `tlsSeam`);
* **everything else** (`¬ OneSphereWindow`): `Work.Drive.Final.tls_rest_crux` — the frontier is a
  disjoint union of at most three spheres, given by the "key non-degeneracy fact" that
  `A ∩ C⁺ = ∅ ⟹ Disjoint (closure A) (closure C⁺)` for `A = PBox ∩ {lam < ℓ}` and
  `C⁺ = PBox ∩ {a+h < ⟪v,·⟫}` (and its mirror), i.e. the contrapositive of the *proved*
  `Work.Drive.Mono.inter_nonempty_of_closure_inter_nonempty_plus*`.  That lemma takes only `hseam`'s
  **first** clause (`⟪v,·⟫ = a+h`), NOT the third (the third does not suffice — a referee supplied a
  counterexample).

The remaining case `s ≤ 0` (empty box, empty frontier) is settled directly below with `n = 0`.
-/



/-! ## Reduction notes (for the proof of the main theorem below)

Notation: `B := PBox s c σ` (open convex box), `p y := ⟪v,y⟫`, `q y := ℓ y`, `a := ⟪v,c⟫ + u`,
`U := {y | |p y - a| ≤ h}` (the closed slab, closed convex) and
`K := tiltedSlabClosed a v h ∩ {q ≤ lam} = U ∩ {q ≤ lam}` (the closed convex *chunk*).  Then
`tiltedLevelRemoved = B \ (U ∩ {q < lam})`.

**(1) The interior.**  For `0 < h` one has the *open* identity

`interior (tiltedLevelRemoved) = B ∩ ({|p - a| ≥ h} ∪ {q > lam})`

(note the `≥`, not `>`: a point of `B` with `|p - a| = h` and `q > lam` *is* interior, because a
neighbourhood of it stays inside the removed set).  Consequently (`hv`, `hℓne` enter only to see
that `int R ⊆ R` is sharp, via `inner_pair_surjective`)

`frontier (tiltedLevelRemoved) = frontier (B ∩ ({|p - a| ≥ h} ∪ {q > lam}))`.

That last equality is the delegated brick
`Work.Drive.Mono.frontier_tiltedLevelRemoved_eq_frontier_open`.

**WARNING (twice-refuted spelling).**  The naive frontrier identity
`frontier R = (frontier B \ interior K) ∪ (closure B ∩ frontier K)` is **FALSE** without extra
"poking" hypotheses (`∃ y ∈ B, |p y - a| > h` on both sides, and `∃ y ∈ B, lam < q y`): see
`Submission/Work/Drive/Mono/_cex_ftlrec.lean` and `_ftlrec_hcut_cex.lean`, which refute the
sibling `frontier_tiltedLevelRemoved_eq_caps` for exactly this reason.  In particular the
`cl (B \ K) = cl B ∩ (int K)^c` step fails when the box is swallowed by the slab near a boundary
point.  Work with the `interior` form (1) above instead.

**(2) Structure of the frontier.**  Put `E := B ∩ K` (convex, bounded; its interior is nonempty
whenever it is nonempty) and `M := frontier B ∩ K`, `Σ := frontier B ∩ frontier K`.  Then
`frontier E` is an embedded sphere (`Work.Drive.Mono.isEmbeddedSphere_frontier_of_convex`),
`frontier E = M ∪ (closure B ∩ frontier K)` glued along `Σ`, while the frontier of the removed set
is obtained from that sphere by *replacing* `M` with `frontier B \ interior M`.  Hence

`frontier R` is a disjoint union of embedded spheres as soon as the complement of `M` in the box
sphere is a disjoint union of closed discs, e.g. as soon as `M` is connected (then it is a
`b`-holed sphere and the complement is `b` discs, `b = #`circles of `Σ`).

The connectedness of `M = {y | boxNorm c σ y = s} ∩ {|p y - a| ≤ h} ∩ {q ≤ lam}` is *proved*:
`Work.Drive.Mono.boxSphere_inter_slab_halfspace_connected`.
-/

/-- **The removed set of a level, as the box cut by the two caps and the slab above the wall.**

`tiltedLevelRemoved s c σ u v h ℓ lam = PBox s c σ ∖ (slabClosed (⟪v,c⟫+u) v h ∩ {ℓ < lam})`, so
it is the set of points of the box that lie either strictly outside the (closed) tilted slab or at
or above the wall, i.e. the union of the two caps `{p > a + h}`, `{p < a - h}` (with `p = ⟪v,·⟫`,
`a = ⟪v,c⟫ + u`) and the part `{|p - a| ≤ h} ∩ {lam ≤ ℓ}` of the closed slab above the wall. -/
theorem tiltedLevelRemoved_eq (s : ℝ) (c : LeanEval.KnotTheory.PardonDistortion.R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : LeanEval.KnotTheory.PardonDistortion.R3) (h : ℝ)
    (ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ) (lam : ℝ) :
    tiltedLevelRemoved s c σ u v h ℓ lam
      = Submission.PBox s c σ ∩
        (({y | inner ℝ v c + u + h < inner ℝ v y}
          ∪ {y | inner ℝ v y < inner ℝ v c + u - h})
          ∪ {y | |inner ℝ v y - (inner ℝ v c + u)| ≤ h ∧ lam ≤ ℓ y}) := by
  ext y
  simp only [tiltedLevelRemoved, Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_sdiff,
    Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨hy, hnot⟩
    refine ⟨hy, ?_⟩
    by_cases hc : |inner ℝ v y - (inner ℝ v c + u)| ≤ h
    · by_cases hl : lam ≤ ℓ y
      · exact Or.inr ⟨hc, hl⟩
      · exact absurd ⟨hc, not_le.mp hl⟩ hnot
    · have hc' : h < |inner ℝ v y - (inner ℝ v c + u)| := not_le.mp hc
      rcases lt_abs.mp hc' with hlt | hlt
      · exact Or.inl (Or.inl (by linarith))
      · exact Or.inl (Or.inr (by linarith))
  · rintro ⟨hy, h | h⟩
    · refine ⟨hy, ?_⟩
      rintro ⟨hcl, hl⟩
      rcases h with h' | h'
      · have : h < |inner ℝ v y - (inner ℝ v c + u)| := lt_abs.mpr (Or.inl (by linarith))
        linarith
      · have : h < |inner ℝ v y - (inner ℝ v c + u)| := lt_abs.mpr (Or.inr (by linarith))
        linarith
    · exact ⟨hy, fun hc => absurd h.2 (not_le.mpr hc.2)⟩

/-- **Independence of the sweep height `p = ⟪v,·⟫` and the wall functional `q = ℓ`.**

If `v ≠ 0`, `ℓ v = 0` and `ℓ ≠ 0`, then `(p, q) : ℝ³ → ℝ²` is surjective: the two functionals
have independent gradients (`∇p = v` and the Riesz vector of `ℓ` is a non-zero vector orthogonal
to `v`).  This is what lets one move a point inside the box so as to cross the wall without
leaving the slab (and vice versa), and hence identifies the *interior* of the removed set with the
open union of the two caps and the open slab above the wall. -/
theorem inner_pair_surjective {v : LeanEval.KnotTheory.PardonDistortion.R3}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ} (hv : v ≠ 0) (hℓv : ℓ v = 0)
    (hℓne : ℓ ≠ 0) :
    ∀ r s : ℝ, ∃ w : LeanEval.KnotTheory.PardonDistortion.R3,
      inner ℝ v w = r ∧ ℓ w = s := by
  intro r s
  have hvpos : 0 < inner ℝ v v := real_inner_self_pos.mpr hv
  by_cases h : ∃ w : LeanEval.KnotTheory.PardonDistortion.R3,
      inner ℝ v w = 0 ∧ ℓ w ≠ 0
  · obtain ⟨w₀, hw₀v, hw₀ℓ⟩ := h
    refine ⟨(r / (inner ℝ v v)) • v + (s / (ℓ w₀)) • w₀, ?_, ?_⟩
    · rw [inner_add_right, inner_smul_right, inner_smul_right, hw₀v, mul_zero, add_zero]
      field_simp
    · rw [map_add, map_smul, map_smul, hℓv, smul_zero, zero_add, smul_eq_mul]
      field_simp
  · push Not at h
    exfalso
    refine hℓne (ContinuousLinearMap.ext fun w => ?_)
    have hdec : inner ℝ v (w - (inner ℝ v w / (inner ℝ v v)) • v) = 0 := by
      rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
      ring
    have hz := h _ hdec
    rw [map_sub, map_smul, hℓv, smul_zero, sub_zero] at hz
    exact hz

/-- The box `PBox s c σ` is empty when `s ≤ 0` (its `σ 0`-half-length is `s`). -/
theorem PBox_eq_empty_of_nonpos {s : ℝ} (c : LeanEval.KnotTheory.PardonDistortion.R3)
    (σ : Equiv.Perm (Fin 3)) (hs : s ≤ 0) : Submission.PBox s c σ = ∅ := by
  ext y
  simp only [Set.mem_empty_iff_false, iff_false]
  rw [Submission.mem_PBox]
  intro hh
  have h0 := hh 0
  rw [Submission.boxSide_zero, one_mul] at h0
  have : (0 : ℝ) ≤ |y (σ 0) - c (σ 0)| := abs_nonneg _
  linarith

/-- The removed set of every level is empty when the box is degenerate (`s ≤ 0`). -/
theorem tiltedLevelRemoved_eq_empty_of_nonpos {s : ℝ} (hs : s ≤ 0)
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (v : LeanEval.KnotTheory.PardonDistortion.R3) (h : ℝ)
    (ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ) (lam : ℝ) :
    tiltedLevelRemoved s c σ u v h ℓ lam = ∅ := by
  rw [tiltedLevelRemoved, PBox_eq_empty_of_nonpos c σ hs, Set.empty_sdiff]


open LeanEval.KnotTheory.PardonDistortion
open Set

/-! ## The cap/disjointness bricks of the case analysis

With `A = PBox ∩ {lam < ℓ}`, `C⁺ = PBox ∩ {a+h < ⟪v,·⟫}` (like `C⁻`), the *key fact* is that
`A ∩ C⁺ = ∅` forces the closures of `A` and `C⁺` to be disjoint — the contrapositive of the
colleague's abstract `Work.Drive.Mono.inter_nonempty_aux`.  This is what makes the three open
convex pieces `A, C⁺, C⁻` of the removed set have pairwise disjoint closures (or vanish), so that
the frontier of the removed set is the union of their frontiers. -/

/-- The upper cap meets the above-the-wall part as soon as their closures meet. -/
theorem capPlus_inter_nonempty {s u h lam : ℝ} {c v : R3} {σ : Equiv.Perm (Fin 3)}
    {ℓ : R3 →L[ℝ] ℝ}
    (hseam : (∃ y ∈ closure (Submission.PBox s c σ),
        inner ℝ v y = inner ℝ v c + u + h ∧ ℓ y = lam) →
      (∃ z ∈ Submission.PBox s c σ,
        inner ℝ v z = inner ℝ v c + u + h ∧ lam < ℓ z))
    (hcl : (closure (Submission.PBox s c σ ∩ {y : R3 | lam < ℓ y}) ∩
          closure (Submission.PBox s c σ ∩ {y : R3 |
            inner ℝ v c + u + h < inner ℝ v y})).Nonempty) :
    (Submission.PBox s c σ ∩ {y : R3 | lam < ℓ y} ∩
      {y : R3 | inner ℝ v c + u + h < inner ℝ v y}).Nonempty :=
  inter_nonempty_aux (Work.Topology.SphereSlicing.convex_PBox s c σ) hseam hcl

/-- The lower cap meets the above-the-wall part as soon as their closures meet. -/
theorem capMinus_inter_nonempty {s u h lam : ℝ} {c v : R3} {σ : Equiv.Perm (Fin 3)}
    {ℓ : R3 →L[ℝ] ℝ}
    (hseam : (∃ y ∈ closure (Submission.PBox s c σ),
        inner ℝ v y = inner ℝ v c + u - h ∧ ℓ y = lam) →
      (∃ z ∈ Submission.PBox s c σ,
        inner ℝ v z = inner ℝ v c + u - h ∧ lam < ℓ z))
    (hcl : (closure (Submission.PBox s c σ ∩ {y : R3 | lam < ℓ y}) ∩
          closure (Submission.PBox s c σ ∩ {y : R3 |
            inner ℝ v y < inner ℝ v c + u - h})).Nonempty) :
    (Submission.PBox s c σ ∩ {y : R3 | lam < ℓ y} ∩
      {y : R3 | inner ℝ v y < inner ℝ v c + u - h}).Nonempty := by
  have hk : ∀ y : R3, (inner ℝ (-v) y = -(inner ℝ v c + u - h)) ↔
      (inner ℝ v y = inner ℝ v c + u - h) := by
    intro y
    rw [inner_neg_left]
    constructor <;> intro h <;> linarith
  have hseam' : (∃ y ∈ closure (Submission.PBox s c σ),
        inner ℝ (-v) y = -(inner ℝ v c + u - h) ∧ ℓ y = lam) →
      (∃ z ∈ Submission.PBox s c σ,
        inner ℝ (-v) z = -(inner ℝ v c + u - h) ∧ lam < ℓ z) := by
    rintro ⟨y, hy, hy1, hy2⟩
    obtain ⟨z, hz, hz1, hz2⟩ := hseam ⟨y, hy, (hk y).mp hy1, hy2⟩
    exact ⟨z, hz, (hk z).mpr hz1, hz2⟩
  have hcl' : (closure (Submission.PBox s c σ ∩ {y : R3 | lam < ℓ y}) ∩
      closure (Submission.PBox s c σ ∩ {y : R3 |
        -(inner ℝ v c + u - h) < inner ℝ (-v) y})).Nonempty := by
    have hset : {y : R3 | -(inner ℝ v c + u - h) < inner ℝ (-v) y}
        = {y : R3 | inner ℝ v y < inner ℝ v c + u - h} := by
      ext y
      rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, inner_neg_left]
      constructor <;> intro h <;> linarith
    rw [hset]
    exact hcl
  have hset2 : {y : R3 | h - (inner ℝ v c + u) < -inner ℝ v y}
      = {y : R3 | inner ℝ v y < inner ℝ v c + u - h} := by
    ext y
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq]
    constructor <;> intro h <;> linarith
  simpa [hset2] using inter_nonempty_aux (v := -v) (ℓ := ℓ) (k := -(inner ℝ v c + u - h))
    (Work.Topology.SphereSlicing.convex_PBox s c σ) hseam' hcl'

/-- **Key fact (upper cap).**  If `A = PBox ∩ {lam < ℓ}` does not meet the upper cap, its closure
does not meet the closure of the cap. -/
theorem disjoint_closures_of_not_inter_plus {s u h lam : ℝ} {c v : R3} {σ : Equiv.Perm (Fin 3)}
    {ℓ : R3 →L[ℝ] ℝ}
    (hseam : (∃ y ∈ closure (Submission.PBox s c σ),
        inner ℝ v y = inner ℝ v c + u + h ∧ ℓ y = lam) →
      (∃ z ∈ Submission.PBox s c σ,
        inner ℝ v z = inner ℝ v c + u + h ∧ lam < ℓ z))
    (hdis : (Submission.PBox s c σ ∩ {y : R3 | lam < ℓ y} ∩
        {y : R3 | inner ℝ v c + u + h < inner ℝ v y}) = ∅) :
    Disjoint (closure (Submission.PBox s c σ ∩ {y : R3 | lam < ℓ y}))
      (closure (Submission.PBox s c σ ∩ {y : R3 |
        inner ℝ v c + u + h < inner ℝ v y})) := by
  rw [Set.disjoint_iff_inter_eq_empty]
  by_contra hne
  obtain ⟨x, hx1, hx2⟩ := Set.nonempty_iff_ne_empty.mpr hne
  exact Set.not_nonempty_iff_eq_empty.mpr hdis (capPlus_inter_nonempty hseam ⟨x, hx1, hx2⟩)

/-- **Key fact (lower cap).** -/
theorem disjoint_closures_of_not_inter_minus {s u h lam : ℝ} {c v : R3} {σ : Equiv.Perm (Fin 3)}
    {ℓ : R3 →L[ℝ] ℝ}
    (hseam : (∃ y ∈ closure (Submission.PBox s c σ),
        inner ℝ v y = inner ℝ v c + u - h ∧ ℓ y = lam) →
      (∃ z ∈ Submission.PBox s c σ,
        inner ℝ v z = inner ℝ v c + u - h ∧ lam < ℓ z))
    (hdis : (Submission.PBox s c σ ∩ {y : R3 | lam < ℓ y} ∩
        {y : R3 | inner ℝ v y < inner ℝ v c + u - h}) = ∅) :
    Disjoint (closure (Submission.PBox s c σ ∩ {y : R3 | lam < ℓ y}))
      (closure (Submission.PBox s c σ ∩ {y : R3 |
        inner ℝ v y < inner ℝ v c + u - h})) := by
  rw [Set.disjoint_iff_inter_eq_empty]
  by_contra hne
  obtain ⟨x, hx1, hx2⟩ := Set.nonempty_iff_ne_empty.mpr hne
  exact Set.not_nonempty_iff_eq_empty.mpr hdis (capMinus_inter_nonempty hseam ⟨x, hx1, hx2⟩)

/-- The two caps never have meeting closures. -/
theorem disjoint_closures_caps {s u h : ℝ} {c v : R3} {σ : Equiv.Perm (Fin 3)} (hh : 0 < h) :
    Disjoint (closure (Submission.PBox s c σ ∩ {y : R3 |
        inner ℝ v c + u + h < inner ℝ v y}))
      (closure (Submission.PBox s c σ ∩ {y : R3 |
        inner ℝ v y < inner ℝ v c + u - h})) := by
  rw [Set.disjoint_iff_inter_eq_empty]
  by_contra hne
  obtain ⟨x, hx1, hx2⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have h1 : inner ℝ v c + u + h ≤ inner ℝ v x := by
    have hsub : Submission.PBox s c σ ∩ {y : R3 | inner ℝ v c + u + h < inner ℝ v y} ⊆
        {y : R3 | inner ℝ v c + u + h ≤ inner ℝ v y} := by
      rintro y ⟨-, hy⟩
      exact le_of_lt (show inner ℝ v c + u + h < inner ℝ v y from hy)
    exact closure_minimal hsub (isClosed_le continuous_const (by fun_prop)) hx1
  have h2 : inner ℝ v x ≤ inner ℝ v c + u - h := by
    have hsub : Submission.PBox s c σ ∩ {y : R3 | inner ℝ v y < inner ℝ v c + u - h} ⊆
        {y : R3 | inner ℝ v y ≤ inner ℝ v c + u - h} := by
      rintro y ⟨-, hy⟩
      exact le_of_lt (show inner ℝ v y < inner ℝ v c + u - h from hy)
    exact closure_minimal hsub (isClosed_le (by fun_prop) continuous_const) hx2
  linarith

/-- **The frontier of a level of the tilted sweep is a finite disjoint union of embedded spheres.**

Write `C := PBox s c σ ∩ tiltedSlabClosed (⟪v,c⟫+u) v h ∩ {ℓ < lam}` (convex), so that
`tiltedLevelRemoved = PBox ∖ C` and `frontier (tiltedLevelRemoved) = frontier (PBox ∖ C)`; put
`p y := ⟪v,y⟫`, `q y := ℓ y`, `a := ⟪v,c⟫+u`.  The complement of the chunk inside the closed box is
the union of the three convex caps
`P⁺ = {p > a+h}`, `P⁻ = {p < a-h}`, `R' = {|p-a| ≤ h} ∩ {q ≥ lam}`,
pairwise disjoint as sets, with `P⁺ ∩ P⁻ = ∅` always.  Since `frontier (A ∪ B) ⊆ frontier A ∪
frontier B` and each cap is convex (so its frontier is an embedded sphere), the frontier is always
*covered* by the three cap frontiers; the content of the statement is that it can be written as a
**disjoint** union of spheres.  Whether the closures of the caps meet is controlled by
`Q₊ := max{q : y ∈ closure (PBox), p y = a+h}`, `Q₋` (same with `p = a-h`) and
`β := max{q : y ∈ closure (PBox), |p y - a| ≤ h}`:
* `lam < min(Q₊,Q₋)`: all three closures meet, `PBox ∖ C` is a ball with a convex dimple and the
  frontier is **one** sphere (this is the case of the whole intermediate range when
  `v = shiftVσ σ 1`, where `Q₊ = Q₋ = β = max q` on the box);
* `min < lam < max`: exactly one of the closures of `P⁺, P⁻` meets `cl R'`, giving **two** spheres;
* `max < lam < β`: the three closures are pairwise disjoint, so `frontier = frontier P⁺ ⊔
  frontier P⁻ ⊔ frontier R'`, **three** spheres (this case is a short point-set computation);
* `β < lam`: `R' = ∅` and the frontier is the two caps — **two** spheres.

**Hypotheses** (all hold at all but finitely many levels, hence are part of the choice of the data
`exc`, and all are needed):
* `hedge` — the wall `{q = lam}` contains no edge of the box (if `lam` is the `q`-value of a point
  of an edge in the `σ i` direction, then `q` is non-constant along that direction); without it the
  frontier has a *tripod* along a box edge (e.g. `σ = id`, `s = 1`, `c = u = 0`, `v = (0,0,1)`,
  `ℓ = y₀+y₁`, `h = 0.4`, `lam = 1-2^{1/3}`);
* `hvertex` — the wall does not pass through a vertex of the box;
* `hseam` — the wall is not tangent to the two face seams on the box sphere nor to the top of the
  strip: at `lam = Q₊`, `Q₋` or `β` the seam degenerates and the frontier is a "figure-8" pinch, not
  a `2`-manifold.  Note that the witnesses here **must** range over `closure (PBox)` (the extremal
  values are attained on the box sphere): with `PBox` instead the condition is vacuous, since
  `ℓ v = 0` and `ℓ ≠ 0` let one move inside the box along `v^⊥` to increase `q`.

FALSE without `hℓv` (`ℓ = ⟪v,·⟫`, `u = 0`, `h < s`, `lam = 0` gives a frontier with two components
when the slab does not span the box) — but the *disjoint-union* form survives some of these, so
`hℓv` is kept only because it is part of the tilt data.  The empty case is `n = 0`. -/
theorem tiltedLevel_disjoint_spheres (s : ℝ)
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (v : LeanEval.KnotTheory.PardonDistortion.R3) (h : ℝ)
    (ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ) (lam : ℝ)
    (hv : ‖v‖ = 1) (hh : 0 < h) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    (hedge : ∀ (i : Fin 3) (ε : Fin 3 → Bool),
      lam = ℓ (WithLp.toLp 2 (fun k : Fin 3 => c k +
        (if k = σ i then (0:ℝ) else
          (if ε (σ.symm k) then 1 else -1) * Submission.boxSide (σ.symm k) * s))) →
      ℓ (EuclideanSpace.single (σ i) (1 : ℝ)) ≠ 0)
    (hvertex : ∀ ε : Fin 3 → Bool,
      lam ≠ ℓ (WithLp.toLp 2 (fun j : Fin 3 => c j +
        (if ε (σ.symm j) then 1 else -1) * Submission.boxSide (σ.symm j) * s)))
    (hseam : ((∃ y ∈ closure (Submission.PBox s c σ),
          inner ℝ v y = inner ℝ v c + u + h ∧ ℓ y = lam) →
        (∃ z ∈ Submission.PBox s c σ,
          inner ℝ v z = inner ℝ v c + u + h ∧ lam < ℓ z)) ∧
      ((∃ y ∈ closure (Submission.PBox s c σ),
          inner ℝ v y = inner ℝ v c + u - h ∧ ℓ y = lam) →
        (∃ z ∈ Submission.PBox s c σ,
          inner ℝ v z = inner ℝ v c + u - h ∧ lam < ℓ z)) ∧
      ((∃ y ∈ closure (Submission.PBox s c σ),
          |inner ℝ v y - (inner ℝ v c + u)| ≤ h ∧ ℓ y = lam) →
        (∃ z ∈ Submission.PBox s c σ,
          |inner ℝ v z - (inner ℝ v c + u)| ≤ h ∧ lam < ℓ z))) :
    ∃ (n : ℕ) (S : Fin n → Set LeanEval.KnotTheory.PardonDistortion.R3),
      (∀ i, Work.InnermostDisk.IsEmbeddedSphere (S i)) ∧
      (∀ i j : Fin n, i ≠ j → Disjoint (S i) (S j)) ∧
      frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) = ⋃ i, S i := by
  have hv0 : v ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hv
    exact absurd hv.symm (by norm_num)
  by_cases hs : 0 < s
  · by_cases hwin : Work.Drive.Final.OneSphereWindow s c σ u h lam v ℓ
    · -- the one-sphere window: the frontier is a single embedded sphere (the crux)
      obtain ⟨hwallP, hwallM, hwinP, hwinM⟩ := hwin
      have hsphere : Work.InnermostDisk.IsEmbeddedSphere
          (frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam)) :=
        Work.Drive.Mono.frontier_isEmbeddedSphere_of_twoSide s c σ u v h ℓ lam
          hv hh hℓv hℓne hedge hvertex hseam hwallP hwallM
      refine ⟨1, fun _ => frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam),
        ?_, ?_, ?_⟩
      · intro i; exact hsphere
      · intro i j hij; exact absurd (Subsingleton.elim i j) hij
      · rw [Set.iUnion_const]
    · -- outside the window: the disjoint-closure case analysis
      exact Work.Drive.Final.tls_rest_crux s hs c σ u h lam v ℓ hv0 hh hℓv hℓne
        hedge hvertex hseam hwin
  · -- the box is empty
    have hs' : s ≤ 0 := le_of_not_gt hs
    refine ⟨0, Fin.elim0, ?_, ?_, ?_⟩
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
    · rw [tiltedLevelRemoved_eq_empty_of_nonpos hs' c σ u v h ℓ lam, Set.iUnion_of_empty]
      simp

end Work.Drive.Mono
