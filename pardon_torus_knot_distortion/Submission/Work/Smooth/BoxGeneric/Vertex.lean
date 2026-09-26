import Mathlib
import Submission.Work.Smooth.BoxGeneric.Defs

/-!
# The vertices of Pardon's box

The input `Work.Smooth.BoxGeneric.AeNoVertex` asks that for almost every level `s` the surface
meets no vertex of the box `PBox s c σ`.  This file makes that input concrete: the vertices of the
box of level `s` with sign pattern `ε : Fin 3 → ℝ` (`ε i = ± 1`) form the point

`boxVertex c σ ε s`  (whose `σ i` coordinate is `c (σ i) + ε i * boxSide i * s`),

the map `s ↦ boxVertex c σ ε s` is a *ray*, and every point of the surface at which all three faces
are tight is such a vertex.  Consequently `AeNoVertex` follows from the statement that each of the
eight vertex rays meets the surface in a *finite* set of levels:

`Work.Smooth.BoxGeneric.aeNoVertex_of_finite`.

That finiteness is what holds for a generic `ψ`; for a general diffeomorphism the a.e. statement is
exactly the remaining genericity gap of the chapter (see the README).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.BoxGeneric

noncomputable section

/-- **The vertex of Pardon's box `PBox s c σ` with sign pattern `ε`**: the point whose `σ i`
coordinate is `c (σ i) + ε i * boxSide i * s`, for `i = 0, 1, 2`. -/
def boxVertex (c : R3) (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ℝ) (s : ℝ) : R3 :=
  WithLp.toLp 2 fun j : Fin 3 => c j + ε (σ.symm j) * Submission.boxSide (σ.symm j) * s

theorem boxVertex_apply (c : R3) (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ℝ) (s : ℝ) (i : Fin 3) :
    boxVertex c σ ε s (σ i) = c (σ i) + ε i * Submission.boxSide i * s := by
  simp [boxVertex, Equiv.symm_apply_apply]

theorem boxVertex_ofLp (c : R3) (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ℝ) (s : ℝ) :
    (boxVertex c σ ε s).ofLp = fun j : Fin 3 => c j + ε (σ.symm j) * Submission.boxSide (σ.symm j) * s :=
  rfl

/-- Every vertex of the box is a point of the box sphere at which all three faces are tight. -/
theorem isBoxVertexPoint_boxVertex (c : R3) (σ : Equiv.Perm (Fin 3)) {ε : Fin 3 → ℝ}
    (hε : ∀ i : Fin 3, ε i = 1 ∨ ε i = -1) {s : ℝ} (hs : 0 ≤ s) :
    IsBoxVertexPoint c σ s (boxVertex c σ ε s) := by
  intro i
  have h : boxVertex c σ ε s (σ i) - c (σ i) = ε i * Submission.boxSide i * s := by
    rw [boxVertex_apply]; ring
  rw [faceNorm, h]
  rcases hε i with h1 | h1
  · rw [h1, one_mul, abs_mul, abs_of_pos (Submission.boxSide_pos i), abs_of_nonneg hs,
      mul_comm (Submission.boxSide i) s]
    exact mul_div_cancel_right₀ s (ne_of_gt (Submission.boxSide_pos i))
  · have hneg : (-1 : ℝ) * Submission.boxSide i * s = -(Submission.boxSide i * s) := by ring
    rw [h1, hneg, abs_neg, abs_mul, abs_of_pos (Submission.boxSide_pos i), abs_of_nonneg hs,
      mul_comm (Submission.boxSide i) s]
    exact mul_div_cancel_right₀ s (ne_of_gt (Submission.boxSide_pos i))

/-- **Every point of the box sphere at which all three faces are tight is a vertex of the box.** -/
theorem eq_boxVertex_of_isBoxVertexPoint (c : R3) (σ : Equiv.Perm (Fin 3)) {s : ℝ} (hs : 0 ≤ s)
    {y : R3} (h : IsBoxVertexPoint c σ s y) :
    ∃ ε : Fin 3 → ℝ, (∀ i : Fin 3, ε i = 1 ∨ ε i = -1) ∧ y = boxVertex c σ ε s := by
  have hcoord : ∀ i : Fin 3, |y (σ i) - c (σ i)| = Submission.boxSide i * s := by
    intro i
    have hi := h i
    rw [faceNorm, div_eq_iff (ne_of_gt (Submission.boxSide_pos i))] at hi
    simpa [mul_comm] using hi
  rcases lt_or_eq_of_le hs with hspos | hs0
  · have key : ∀ i : Fin 3, ∃ (a : ℝ), (a = 1 ∨ a = -1) ∧
        y (σ i) - c (σ i) = a * (Submission.boxSide i * s) := by
      intro i
      have hpos : 0 < Submission.boxSide i * s :=
        mul_pos (Submission.boxSide_pos i) hspos
      have h' : |y (σ i) - c (σ i)| = Submission.boxSide i * s := hcoord i
      rcases (abs_eq (le_of_lt hpos)).mp h' with hh | hh
      · exact ⟨1, Or.inl rfl, by rw [hh]; ring⟩
      · exact ⟨-1, Or.inr rfl, by rw [hh]; ring⟩
    choose ε hε hεv using key
    refine ⟨ε, fun i => hε i, ?_⟩
    have hy : y.ofLp = (boxVertex c σ ε s).ofLp := by
      funext j
      obtain ⟨i, rfl⟩ := σ.surjective j
      rw [boxVertex_ofLp]
      have hthis : y.ofLp (σ i) - c.ofLp (σ i) = ε i * (Submission.boxSide i * s) := hεv i
      simp only [Equiv.symm_apply_apply, WithLp.ofLp_toLp]
      linarith
    calc y = WithLp.toLp 2 y.ofLp := (WithLp.toLp_ofLp 2 y).symm
      _ = WithLp.toLp 2 (boxVertex c σ ε s).ofLp := by rw [hy]
      _ = boxVertex c σ ε s := WithLp.toLp_ofLp 2 _
  · refine ⟨fun _ => 1, fun _ => Or.inl rfl, ?_⟩
    have hc : y = c := by
      have hy : y.ofLp = c.ofLp := by
        funext j
        obtain ⟨i, rfl⟩ := σ.surjective j
        have hi := hcoord i
        rw [← hs0, mul_zero] at hi
        have h2 : |y (σ i) - c (σ i)| = 0 := hi
        have h3 : y (σ i) - c (σ i) = 0 := abs_eq_zero.mp h2
        simp only
        linarith
      calc y = WithLp.toLp 2 y.ofLp := (WithLp.toLp_ofLp 2 y).symm
        _ = WithLp.toLp 2 c.ofLp := by rw [hy]
        _ = c := WithLp.toLp_ofLp 2 _
    rw [hc, ← hs0]
    have hbx : (boxVertex c σ (fun _ : Fin 3 => 1) 0).ofLp = c.ofLp := by
      funext j
      obtain ⟨i, rfl⟩ := σ.surjective j
      rw [boxVertex_ofLp]
      simp
    calc c = WithLp.toLp 2 c.ofLp := (WithLp.toLp_ofLp 2 c).symm
      _ = WithLp.toLp 2 (boxVertex c σ (fun _ : Fin 3 => 1) 0).ofLp := by rw [hbx]
      _ = boxVertex c σ (fun _ : Fin 3 => 1) 0 := WithLp.toLp_ofLp 2 _

/-- The sign patterns `Fin 3 → {±1}` form a finite set. -/
theorem finite_signPatterns :
    ({ε : Fin 3 → ℝ | ∀ i : Fin 3, ε i = 1 ∨ ε i = -1}).Finite := by
  have h : ({ε : Fin 3 → ℝ | ∀ i : Fin 3, ε i ∈ ({1, -1} : Set ℝ)}).Finite :=
    Set.Finite.pi' fun _ => (Set.finite_singleton (-1 : ℝ)).insert 1
  refine h.subset fun ε hε i => ?_
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hε i

/-- **`AeNoVertex` from the finiteness of the vertex-ray intersections.**  If each of the eight
vertex rays `s ↦ boxVertex c σ ε s` meets the surface in a finite set of levels, then almost every
box sphere avoids the vertices of the box. -/
theorem aeNoVertex_of_finite (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3))
    (h : ∀ ε : Fin 3 → ℝ, (∀ i : Fin 3, ε i = 1 ∨ ε i = -1) →
      {s : ℝ | boxVertex c σ ε s ∈ (Work.Smooth.Morse.torus ψ).carrier}.Finite) :
    AeNoVertex ψ c σ := by
  rw [AeNoVertex, MeasureTheory.ae_iff]
  have hset : {s : ℝ | ¬ ∀ y ∈ (Work.Smooth.Morse.torus ψ).carrier,
        ¬ IsBoxVertexPoint c σ s y} =
      {s : ℝ | ∃ y ∈ (Work.Smooth.Morse.torus ψ).carrier, IsBoxVertexPoint c σ s y} := by
    ext s
    simp only [not_forall, not_not, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, hx, h⟩; exact ⟨x, hx, h⟩
    · rintro ⟨y, hy, h⟩; exact ⟨y, hy, h⟩
  rw [hset]
  have hbad : {s : ℝ | ∃ y ∈ (Work.Smooth.Morse.torus ψ).carrier, IsBoxVertexPoint c σ s y} ⊆
      ⋃ ε ∈ {ε : Fin 3 → ℝ | ∀ i : Fin 3, ε i = 1 ∨ ε i = -1},
        {s : ℝ | boxVertex c σ ε s ∈ (Work.Smooth.Morse.torus ψ).carrier} := by
    rintro s ⟨y, hy, hvert⟩
    have hs0 : 0 ≤ s := le_trans (faceNorm_nonneg c σ 0 y) (le_of_eq (hvert 0))
    obtain ⟨ε, hε, rfl⟩ := eq_boxVertex_of_isBoxVertexPoint c σ hs0 hvert
    exact Set.mem_biUnion hε hy
  have hfin : (⋃ ε ∈ {ε : Fin 3 → ℝ | ∀ i : Fin 3, ε i = 1 ∨ ε i = -1},
      {s : ℝ | boxVertex c σ ε s ∈ (Work.Smooth.Morse.torus ψ).carrier}).Finite :=
    finite_signPatterns.biUnion (fun ε hε => h ε hε)
  exact MeasureTheory.measure_mono_null hbad (hfin.measure_zero MeasureTheory.volume)

/-- **`AeNoVertex` from the countability of the vertex-ray intersections.**  The same argument as
`aeNoVertex_of_finite`, with finiteness weakened to countability: a countable union of countable
sets of levels is null.

This is the sharpest form of the vertex input which the parametric argument can give: the set of
levels at which a vertex ray meets the surface is the set of parameter values of the intersection of
a *straight line* with the surface `F = ψ(standard torus)`.  For a real-analytic `ψ` this set is
finite (hence countable); for a merely smooth `ψ` it can be an interval — a smooth surface may
contain a segment of a vertex ray, and then the level sets fail to be `1`-manifolds on a
positive-measure set of levels (see the README, §5). -/
theorem aeNoVertex_of_countable (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3))
    (h : ∀ ε : Fin 3 → ℝ, (∀ i : Fin 3, ε i = 1 ∨ ε i = -1) →
      {s : ℝ | boxVertex c σ ε s ∈ (Work.Smooth.Morse.torus ψ).carrier}.Countable) :
    AeNoVertex ψ c σ := by
  rw [AeNoVertex, MeasureTheory.ae_iff]
  have hset : {s : ℝ | ¬ ∀ y ∈ (Work.Smooth.Morse.torus ψ).carrier,
        ¬ IsBoxVertexPoint c σ s y} =
      {s : ℝ | ∃ y ∈ (Work.Smooth.Morse.torus ψ).carrier, IsBoxVertexPoint c σ s y} := by
    ext s
    simp only [not_forall, not_not, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, hx, h⟩; exact ⟨x, hx, h⟩
    · rintro ⟨y, hy, h⟩; exact ⟨y, hy, h⟩
  rw [hset]
  have hbad : {s : ℝ | ∃ y ∈ (Work.Smooth.Morse.torus ψ).carrier, IsBoxVertexPoint c σ s y} ⊆
      ⋃ ε ∈ {ε : Fin 3 → ℝ | ∀ i : Fin 3, ε i = 1 ∨ ε i = -1},
        {s : ℝ | boxVertex c σ ε s ∈ (Work.Smooth.Morse.torus ψ).carrier} := by
    rintro s ⟨y, hy, hvert⟩
    have hs0 : 0 ≤ s := le_trans (faceNorm_nonneg c σ 0 y) (le_of_eq (hvert 0))
    obtain ⟨ε, hε, rfl⟩ := eq_boxVertex_of_isBoxVertexPoint c σ hs0 hvert
    exact Set.mem_biUnion hε hy
  have hcount : (⋃ ε ∈ {ε : Fin 3 → ℝ | ∀ i : Fin 3, ε i = 1 ∨ ε i = -1},
      {s : ℝ | boxVertex c σ ε s ∈ (Work.Smooth.Morse.torus ψ).carrier}).Countable :=
    finite_signPatterns.countable.biUnion (fun ε hε => h ε hε)
  exact MeasureTheory.measure_mono_null hbad (hcount.measure_zero MeasureTheory.volume)

end

end Work.Smooth.BoxGeneric
