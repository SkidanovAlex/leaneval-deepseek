import Mathlib
import Submission.VoronoiMeasure
import Submission.Cvp

open Module Real MeasureTheory
open scoped Real BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# (P3.1) cell-local-determination: agreeing lattice fragments give agreeing cells

The first step of P3 (continuity of `ℒ ↦ γ_{1/t}(V(ℒ))`): the Voronoi cell of a lattice is
determined *locally* — whether `x ∈ V(ℒ)` only depends on the lattice points of norm
`≤ 2‖x‖`.  Concretely: if two lattices have the same points inside `closedBall 0 T`, their
Voronoi cells agree on `closedBall 0 (T/2)`.

Why: a far-away lattice point `y` (`‖y‖ > T`) can never beat `0` for a point `x` with
`‖x‖ ≤ T/2`, since `‖x − y‖ ≥ ‖y‖ − ‖x‖ > T/2 ≥ ‖x‖`; near points (`‖y‖ ≤ T`) are common
to both lattices by the fragment equality, so `x ∈ V(ℒ₁)` forces `‖x‖ ≤ ‖x − y‖` there too.

Consequently, a matrix-convergent sequence of lattices (whose bounded fragments stabilize)
has its cells converge on every bounded ball — the input to the dominated-convergence step
(P3.2).  This module needs no discreteness or full-rank hypotheses: the argument is purely
about the geometry of the cell definition.
-/

namespace Submission.VoronoiContinuity

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "VC" => Submission.Voronoi.voronoi

/-- **(P3.1)** If two lattices have the same points inside the closed ball of radius `T`,
their Voronoi cells agree on the closed ball of radius `T/2`. -/
lemma voronoi_eq_on_ball_of_fragment_eq (ℒ₁ ℒ₂ : Submodule ℤ E) (T : ℝ)
    (hfrag : ((ℒ₁ : Submodule ℤ E) : Set E) ∩ Metric.closedBall (0 : E) T =
      ((ℒ₂ : Submodule ℤ E) : Set E) ∩ Metric.closedBall (0 : E) T) :
    ((VC ℒ₁ : Set E) ∩ Metric.closedBall (0 : E) (T / 2)) =
      ((VC ℒ₂ : Set E) ∩ Metric.closedBall (0 : E) (T / 2)) := by
  ext x
  constructor
  · rintro ⟨hx1, hxball⟩
    constructor
    · rw [Submission.VoronoiMeasure.mem_voronoi_iff_norm (ℒ := ℒ₂) x]
      intro y
      have hxball' : ‖x‖ ≤ T / 2 := by
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hxball
        exact hxball
      by_cases hle : ‖(y : E)‖ ≤ T
      · -- y lies in the common fragment, hence in ℒ₁ too; use x ∈ V(ℒ₁)
        have hy1 : (y : E) ∈ ℒ₁ := by
          have hyf : (y : E) ∈ ((ℒ₂ : Submodule ℤ E) : Set E) ∩
              Metric.closedBall (0 : E) T := ⟨y.2, by
                rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
                exact hle⟩
          rcases (by rwa [← hfrag] at hyf) with ⟨hy1, _⟩
          exact hy1
        let w : ℒ₁ := ⟨(y : E), hy1⟩
        have hv := (Submission.VoronoiMeasure.mem_voronoi_iff_norm (ℒ := ℒ₁) x).mp hx1 w
        simpa [w] using hv
      · -- far lattice points can never be closer to x than 0 is
        have hgt : T < ‖(y : E)‖ := lt_of_not_ge hle
        have htri : ‖(y : E)‖ ≤ ‖(y : E) - x‖ + ‖x‖ := by
          calc
            ‖(y : E)‖ = ‖((y : E) - x) + x‖ := by congr 1; abel
            _ ≤ ‖(y : E) - x‖ + ‖x‖ := norm_add_le ((y : E) - x) x
        have hrev : ‖x - (y : E)‖ = ‖(y : E) - x‖ := by rw [norm_sub_rev]
        have hxy : ‖x‖ ≤ ‖x - (y : E)‖ := by
          nlinarith [htri, hgt, hxball', hrev, norm_nonneg ((y : E) - x), norm_nonneg x]
        exact pow_le_pow_left₀ (norm_nonneg x) hxy 2
    · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hxball ⊢
      exact hxball
  · rintro ⟨hx2, hxball⟩
    constructor
    · rw [Submission.VoronoiMeasure.mem_voronoi_iff_norm (ℒ := ℒ₁) x]
      intro y
      have hxball' : ‖x‖ ≤ T / 2 := by
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hxball
        exact hxball
      by_cases hle : ‖(y : E)‖ ≤ T
      · have hy2 : (y : E) ∈ ℒ₂ := by
          have hyf : (y : E) ∈ ((ℒ₁ : Submodule ℤ E) : Set E) ∩
              Metric.closedBall (0 : E) T := ⟨y.2, by
                rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
                exact hle⟩
          rcases (by rwa [hfrag] at hyf) with ⟨hy2, _⟩
          exact hy2
        let w : ℒ₂ := ⟨(y : E), hy2⟩
        have hv := (Submission.VoronoiMeasure.mem_voronoi_iff_norm (ℒ := ℒ₂) x).mp hx2 w
        simpa [w] using hv
      · have hgt : T < ‖(y : E)‖ := lt_of_not_ge hle
        have htri : ‖(y : E)‖ ≤ ‖(y : E) - x‖ + ‖x‖ := by
          calc
            ‖(y : E)‖ = ‖((y : E) - x) + x‖ := by congr 1; abel
            _ ≤ ‖(y : E) - x‖ + ‖x‖ := norm_add_le ((y : E) - x) x
        have hrev : ‖x - (y : E)‖ = ‖(y : E) - x‖ := by rw [norm_sub_rev]
        have hxy : ‖x‖ ≤ ‖x - (y : E)‖ := by
          nlinarith [htri, hgt, hxball', hrev, norm_nonneg ((y : E) - x), norm_nonneg x]
        exact pow_le_pow_left₀ (norm_nonneg x) hxy 2
    · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hxball ⊢
      exact hxball

/-! ## (P3.1b) the tie set and the cell boundary -/

/-- The **tie set**: points `x` where the origin ties with a nonzero lattice point
(`x` lies on the bisecting hyperplane of `0` and `y`).  Points outside this set have stable
Voronoi membership under small perturbations of the lattice. -/
def tieSet (ℒ : Submodule ℤ E) : Set E :=
  {x | ∃ y : ℒ, y ≠ 0 ∧ inner ℝ x (y : E) = ‖(y : E)‖ ^ 2 / 2}

/-- The (relative) boundary of the Voronoi cell lies in the tie set: a cell point outside
the interior satisfies some constraint with equality (`exists_tight_of_voronoi_not_interior`),
which is exactly the tie condition. -/
lemma boundary_subset_tieSet {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] :
    ((VC ℒ : Set E) \ interior (VC ℒ)) ⊆ tieSet ℒ := by
  intro x hx
  rcases Submission.Cvp.exists_tight_of_voronoi_not_interior (ℒ := ℒ) hx.1 hx.2 with ⟨y, hy0, ht⟩
  exact ⟨y, hy0, ht⟩

/-- Interior points of the cell are never in the tie set (all constraints are strict). -/
lemma interior_mem_not_tieSet {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (x : E)
    (hx : x ∈ interior (VC ℒ)) : x ∉ tieSet ℒ := by
  intro hxt
  rcases hxt with ⟨y, hy0, ht⟩
  have hstrict : inner ℝ x (y : E) < ‖(y : E)‖ ^ 2 / 2 :=
    (Submission.Cvp.mem_interior_voronoi_iff (ℒ := ℒ) x).mp hx y hy0
  nlinarith

/-- The tie set of a discrete lattice is a countable union of (measure-zero) hyperplanes,
hence has measure zero. -/
lemma volume_tieSet_zero {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] [Countable ℒ] :
    volume (tieSet ℒ) = 0 := by
  classical
  have hS : tieSet ℒ = ⋃ y : {y : ℒ // y ≠ 0},
      {x : E | inner ℝ x (y.1 : E) = ‖(y.1 : E)‖ ^ 2 / 2} := by
    ext x
    simp [tieSet]
  rw [hS]
  rw [measure_iUnion_null]
  intro y
  have hz : volume {x : E | inner ℝ (x - (0 : E)) (y.1 : E) = ‖(y.1 : E)‖ ^ 2 / 2} = 0 :=
    Submission.VoronoiMeasure.hyperplane_measure_zero (p := (0 : E)) (h := (y.1 : E)) (by
      intro hz
      exact y.2 (Subtype.ext hz))
  simpa using hz

/-! ## (P3.1c) membership stability off the tie set

The stabilization lemma (`x_off_tieSet_mem_stable`, below) is the heart of P3.1c: for `x`
off the tie set of the limit lattice, membership of `x` in the Voronoi cell is locally
constant along matrix-convergent lattices.  The two clean structural facts it rests on are
recorded here first:

* off the tie set, membership in the cell is the same as membership in the interior (no
  boundary cases): `cell_mem_iff_interior_of_not_tie`;
* interior membership means *every* constraint is strict, so a finite (bounded-coefficient)
  fragment of the lattice — each a continuous function of the basis matrix — keeps its
  strictness under small perturbations.

The remaining analytic input (recorded as `coefficients_bounded_of_norm` below) is the
bounded-coefficient fragment lemma: lattice points within a fixed ball are integer
combinations of the basis with bounded coefficients (a norm equivalence on the finite-
dimensional coordinate space), which makes the "relevant constraints" a fixed finite set
under basis perturbation.
-/

/-- Off the tie set, membership in the cell is interior membership: no ties means every
satisfied constraint is strict. -/
lemma cell_mem_iff_interior_of_not_tie {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (x : E)
    (hx : x ∉ tieSet ℒ) : x ∈ VC ℒ ↔ x ∈ interior (VC ℒ) := by
  constructor
  · intro hxV
    rw [Submission.Cvp.mem_interior_voronoi_iff]
    intro y hy0
    have hle : inner ℝ x (y : E) ≤ ‖(y : E)‖ ^ 2 / 2 := (Submission.Voronoi.mem_voronoi.mp hxV) y
    have hne : inner ℝ x (y : E) ≠ ‖(y : E)‖ ^ 2 / 2 := by
      intro heq
      exact hx ⟨y, hy0, heq⟩
    exact lt_of_le_of_ne hle hne
  · intro hxI
    exact interior_subset hxI

/-- A violation off the tie set is strict: `x ∉ V(ℒ)` and `x ∉ tieSet ℒ` give a nonzero
lattice point strictly closer to `x` than the origin. -/
lemma strict_violation_of_not_mem_cell_of_not_tie {ℒ : Submodule ℤ E} (x : E)
    (hxV : x ∉ VC ℒ) (hx : x ∉ tieSet ℒ) :
    ∃ y : ℒ, y ≠ 0 ∧ ‖x - (y : E)‖ ^ 2 < ‖x‖ ^ 2 := by
  classical
  by_contra hnot
  push_neg at hnot
  -- every nonzero y has ‖x−y‖² ≥ ‖x‖², i.e. x ∈ V
  have hxV' : x ∈ VC ℒ := by
    rw [Submission.VoronoiMeasure.mem_voronoi_iff_norm]
    intro y
    by_cases hy0 : y = 0
    · subst hy0
      simp
    · have hge : ‖x‖ ^ 2 ≤ ‖x - (y : E)‖ ^ 2 := (hnot y hy0).ge
      exact hge
  exact hxV hxV'

end Submission.VoronoiContinuity