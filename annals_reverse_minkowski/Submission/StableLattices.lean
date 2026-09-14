import Mathlib
import ChallengeDeps
import Submission.LatticeBasics
import Submission.Voronoi
import Submission.VoronoiMeasure
import Submission.TFacts

open Module Real Matrix
open scoped Real BigOperators InnerProductSpace RealInnerProductSpace
set_option autoImplicit false

/-!
# Stable lattices (paper §2.5)

A lattice `ℒ` (a `ℤ`-submodule of `E = EuclideanSpace ℝ (Fin n)`, discrete) is
**stable** when `det ℒ = 1` and every sublattice has determinant at least 1.

In this module we record the definition plus the facts that follow directly from the
already-proven basic theory (λ₁ ≥ 1, the half-ball inside the Voronoi cell, and the
rho_gamma-based reduction of Prop RM_stable to a Voronoi-mass lower bound).
The deeper stable-lattice theory (canonical filtration, uncrossing, direct sums, dual,
Mahler compactness, boundary characterization — paper Prop. 2.7) lives in later modules;
see `Submission/Blueprint.lean` for the full plan.
-/

namespace Submission.StableLattices

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "VC" => Submission.Voronoi.voronoi

/-- A stable lattice: determinant exactly `1`, and all sublattice determinants `≥ 1`. -/
def Stable (ℒ : Submodule ℤ E) [DiscreteTopology ℒ] : Prop :=
  ReverseMinkowski.determinant ℒ = 1 ∧
    ∀ ℒ' (_hle : ℒ' ≤ ℒ) [DiscreteTopology ℒ'], ReverseMinkowski.determinant ℒ' ≥ 1

/-- The second half of the stability definition. -/
lemma all_subdet_ge_one_of_stable {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hSt : Stable ℒ) :
    ∀ ℒ' (_hle : ℒ' ≤ ℒ) [DiscreteTopology ℒ'], ReverseMinkowski.determinant ℒ' ≥ 1 := by
  exact hSt.2

/-- Stable lattices have determinant exactly one. -/
lemma det_eq_one_of_stable {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hSt : Stable ℒ) : ReverseMinkowski.determinant ℒ = 1 := hSt.1

/-- Every nonzero vector of a stable lattice has norm at least one (`λ₁ ≥ 1`). -/
lemma norm_ge_one_of_stable {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hSt : Stable ℒ) (v : ℒ) (hv : v ≠ 0) : 1 ≤ ‖(v : E)‖ := by
  exact Submission.LatticeBasics.norm_ge_one_of_all_subdet (ℒ := ℒ) hSt.2 v hv

/-- The ball of radius `1/2` lies inside the Voronoi cell of a stable lattice
(inradius of the Voronoi cell is `λ₁/2 ≥ 1/2`). -/
lemma half_ball_subset_voronoi_of_stable {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hSt : Stable ℒ) :
    Metric.closedBall (0 : E) (1 / 2) ⊆ VC ℒ := by
  exact Submission.Voronoi.one_half_ball_subset_voronoi_of_min_norm (ℒ := ℒ)
    (fun v hv => norm_ge_one_of_stable hSt v hv)

/-!
## Prop RM_stable (paper §7.2), target statement

For every stable lattice `ℒ ≤ E`, `ρ_{1/t}(ℒ) ≤ 3/2` with `t := 10 (log n + 2)`.

The full proposition requires the whole §7 program (Mahler compactness, gradients,
convex-geometry core); here we record the bridge that the final proof will use:
`rho_gamma` reduces the bound on `ρ` to the lower bound `γ_{1/t}(V(ℒ)) ≥ 2/3`
(already available as `Submission.VoronoiMeasure.rho_le_three_halves_of_gamma_ge`),
and stable lattices satisfy the ball-`1/2`-in-Voronoi fact above.
-/

/-- `ρ_s(ℒ) ≤ 3/2` as soon as the Voronoi cell has Gaussian mass `γ_s(V(ℒ)) ≥ 2/3`
(full-rank lattices; `ρ_s` is the `ReverseMinkowski.ρ` of the challenge). -/
theorem rho_le_three_halves_of_stable_gamma {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) (s : ℝ) (hs : 0 < s)
    (hγ : (2 : ℝ) / 3 ≤
      ∫ x in {x : E | s • x ∈ VC ℒ}, rexp (-Real.pi * ‖x‖ ^ 2)) :
    ReverseMinkowski.ρ s ℒ ≤ 3 / 2 := by
  rw [Submission.VoronoiMeasure.rho_eq_ambient_sum]
  exact Submission.VoronoiMeasure.rho_le_three_halves_of_gamma_ge (ℒ := ℒ) hℒ s hs hγ

/-- The parameter `t = 10 (log n + 2)` of Theorem 1.2 is positive. -/
lemma t_pos_nat (n : ℕ) : 0 < 10 * (log (n : ℝ) + 2) := by
  exact Submission.TFacts.t_pos n

/-- For a full-rank stable lattice, the Voronoi cell is measurable. -/
lemma voronoi_measurable_stable {ℒ : Submodule ℤ E} :
    MeasurableSet (VC ℒ) := by
  exact Submission.Voronoi.voronoi_measurable (ℒ := ℒ)

/-- A det-one sublattice of a stable lattice is stable (every sublattice of it is a
sublattice of the stable host). -/
lemma stable_of_det_one_le {ℒ ℒ' : Submodule ℤ E} [DiscreteTopology ℒ] [DiscreteTopology ℒ']
    (hSt : Submission.StableLattices.Stable ℒ) (hle : ℒ' ≤ ℒ)
    (hdet : ReverseMinkowski.determinant ℒ' = 1) : Submission.StableLattices.Stable ℒ' := by
  constructor
  · exact hdet
  · intro M hMle hDTM
    haveI : DiscreteTopology M := hDTM
    have hMleL : M ≤ ℒ := le_trans hMle hle
    exact Submission.StableLattices.all_subdet_ge_one_of_stable hSt M hMleL

end Submission.StableLattices
