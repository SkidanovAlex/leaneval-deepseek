import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.Galerkin.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Galerkin.Compactness

open scoped Real Topology
open Set Metric

set_option autoImplicit false

/-! ## Rational approximation in the two closed intervals

Two elementary one-dimensional approximation lemmas: points of `[0,∞)` and of `[0,π/2]` can be
approximated to any accuracy by *rational* points of the same interval.  Both are proved from
`exists_rat_btwn` (density of `ℚ` in `ℝ`) by exhibiting two explicit strict bounds between which we
interpolate.  The upper endpoint `π/2` is handled by keeping the rational strictly below it. -/

/-- Every point of the half-line `[0,∞)` is approximated, within `ε`, by a rational point of
`[0,∞)`. -/
lemma exists_rat_Ici_near_fts (x : ℝ) (hx : 0 ≤ x) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℚ, 0 ≤ (q : ℝ) ∧ |(q : ℝ) - x| < ε := by
  have hlt : max 0 (x - ε / 2) < x + ε / 2 := max_lt (by linarith) (by linarith)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
  have h0 : (0 : ℝ) ≤ max 0 (x - ε / 2) := le_max_left _ _
  have hL : x - ε / 2 ≤ max 0 (x - ε / 2) := le_max_right _ _
  refine ⟨q, le_of_lt (lt_of_le_of_lt h0 hq1), ?_⟩
  rw [abs_lt]
  exact ⟨by linarith, by linarith⟩

/-- Every point of the interval `[0,π/2]` is approximated, within `ε`, by a rational point of
`[0,π/2]`. -/
lemma exists_rat_Icc_near_fts (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ Real.pi / 2) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ q : ℚ, 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ Real.pi / 2 ∧ |(q : ℝ) - x| < ε := by
  have hπ : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hlt : max 0 (x - ε / 2) < min (x + ε / 2) (Real.pi / 2) :=
    lt_min (max_lt (by linarith) (by linarith)) (max_lt hπ (by linarith))
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
  have h0 : (0 : ℝ) ≤ max 0 (x - ε / 2) := le_max_left _ _
  have hL : x - ε / 2 ≤ max 0 (x - ε / 2) := le_max_right _ _
  have hR : (q : ℝ) < x + ε / 2 := lt_of_lt_of_le hq2 (min_le_left _ _)
  refine ⟨q, le_of_lt (lt_of_le_of_lt h0 hq1),
    le_of_lt (lt_of_lt_of_le hq2 (min_le_right _ _)), ?_⟩
  rw [abs_lt]
  exact ⟨by linarith, by linarith⟩

/-! ## The dense sequence -/

/-- The rational points of the fake-time slab: rational triples all of whose coordinates, read in
`ℝ`, lie in the corresponding closed factor `[0,∞)`, `[0,π/2]`, `[0,∞)`. -/
def slabRat_fts : Set (ℚ × ℚ × ℚ) :=
  {q | 0 ≤ (q.1 : ℝ) ∧ 0 ≤ (q.2.1 : ℝ) ∧ (q.2.1 : ℝ) ≤ Real.pi / 2 ∧ 0 ≤ (q.2.2 : ℝ)}

/-- A rational triple, read as a point of `ℝ³`. -/
def ratTripleToReal_fts (q : ℚ × ℚ × ℚ) : ℝ × ℝ × ℝ :=
  ((q.1 : ℝ), ((q.2.1 : ℚ) : ℝ), ((q.2.2 : ℚ) : ℝ))

/-- **A countable dense sequence in the fake-time slab.**  There is a sequence of points of
`Slab = [0,∞) × [0,π/2] × [0,∞)` whose range is dense in the slab.  (It is used by the compactness
extraction `Work.FTS.Galerkin.exists_subseq_convLocUnif`, which does the diagonal extraction on the
countable dense set and then upgrades it to locally uniform convergence by equicontinuity.)

Intended proof: enumerate the rational points `(q₁, q₂, q₃) ∈ ℚ³` with `q₁ ≥ 0`, `0 ≤ q₂ ≤ π/2`,
`q₃ ≥ 0` (as a sequence via `Encodable`/`Denumerable` of `ℚ × ℚ × ℚ`), and prove density: given
`p ∈ Slab` and `ε > 0`, use `exists_rat_btwn`/`Rat.denseRange_cast` to pick, in each coordinate, a
rational within `ε` of `p` and inside the interval (for the upper endpoint `π/2` use a rational
strictly below it, which exists by density since `π/2` is irrational); for the closed lower
endpoints `0` one may take the rational `0` itself. -/
theorem exists_seq_dense_slab : ∃ e : ℕ → ℝ × ℝ × ℝ,
    (∀ k : ℕ, e k ∈ Work.FTS.Galerkin.Slab) ∧
      ∀ p ∈ Work.FTS.Galerkin.Slab, p ∈ closure (Set.range e) := by
  -- the rational points of the slab form a nonempty countable type, hence can be enumerated
  haveI hne : Nonempty {q : ℚ × ℚ × ℚ // q ∈ slabRat_fts} :=
    ⟨⟨(0, 0, 0), by
      rw [slabRat_fts, Set.mem_setOf_eq]
      refine ⟨?_, ?_, ?_, ?_⟩
      · norm_num
      · norm_num
      · push_cast; positivity
      · norm_num⟩⟩
  obtain ⟨f, hf⟩ := exists_surjective_nat {q : ℚ × ℚ × ℚ // q ∈ slabRat_fts}
  refine ⟨fun k => ratTripleToReal_fts (f k).val, ?_, ?_⟩
  · -- every element of the sequence is a rational point of the slab, hence in the slab
    intro k
    have hk : 0 ≤ ((f k).val.1 : ℝ) ∧ 0 ≤ ((f k).val.2.1 : ℝ) ∧
        ((f k).val.2.1 : ℝ) ≤ Real.pi / 2 ∧ 0 ≤ ((f k).val.2.2 : ℝ) := (f k).2
    exact ⟨hk.1, ⟨⟨hk.2.1, hk.2.2.1⟩, hk.2.2.2⟩⟩
  · -- density: approximate each coordinate of `p` by a rational point of the same interval
    intro p hp
    simp only [mem_Slab, Spaces.Iz, Spaces.Iθ, Set.mem_Ici, Set.mem_Icc,
      Set.mem_setOf_eq] at hp
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨q1, hq1nn, hq1near⟩ := exists_rat_Ici_near_fts p.1 hp.1 hε
    obtain ⟨q2, hq2nn, hq2le, hq2near⟩ := exists_rat_Icc_near_fts p.2.1 hp.2.1.1 hp.2.1.2 hε
    obtain ⟨q3, hq3nn, hq3near⟩ := exists_rat_Ici_near_fts p.2.2 hp.2.2 hε
    obtain ⟨k, hk⟩ := hf ⟨(q1, q2, q3), ⟨hq1nn, hq2nn, hq2le, hq3nn⟩⟩
    have hval : (f k).val = (q1, q2, q3) := congrArg Subtype.val hk
    refine ⟨ratTripleToReal_fts (f k).val, Set.mem_range_self k, ?_⟩
    rw [hval, ratTripleToReal_fts]
    simp only [Prod.dist_eq, Real.dist_eq, max_lt_iff]
    exact ⟨by simpa [abs_sub_comm] using hq1near,
      by simpa [abs_sub_comm] using hq2near,
      by simpa [abs_sub_comm] using hq3near⟩

end Work.FTS.Galerkin.Compactness
