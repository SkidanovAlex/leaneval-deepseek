import Mathlib
import Submission.CoveringRadius
import Submission.StableLattices
import Submission.Poisson
import Submission.MainStable
import Submission.Commons.Lattice.Minkowski.bounded_basis_covolume_one

open Module Real
open scoped Real BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# [B-ii] stable family: uniform boundedness of the Voronoi cells

The precompactness datum the [B-ii] topology layer needs: *the Voronoi cells of the stable
full-rank lattices of a fixed ambient dimension lie in one common closed ball*.

Route (two halves):
1. `Submission/CoveringRadius.lean` gives, for ANY `ℤ`-basis `b` of a full-rank lattice,
   `V(ℒ) ⊆ closedBall 0 (Σᵢ‖(bᵢ : E)‖)`.
2. A **uniform bounded-basis property** — every stable full-rank rank-`m` lattice admits a
   `ℤ`-basis with all vector norms `≤ C(m)` — has been DELEGATED to the commons as
   `Commons.Lattice.Minkowski.bounded_basis_covolume_one` (child L88, in flight).  It is the
   Minkowski-second-type/Mahler-2nd essence: covolume 1 + shortest vector `≥ 1` (which
   stability gives, by `covolume_eq_determinant` + `det_eq_one_of_stable` and
   `norm_ge_one_of_stable`) forces a bounded basis.

`stable_voronoi_uniform_bounded` below is the glue: bounded basis (as an explicit
hypothesis, to be discharged by L88 once it lands) ⇒ uniformly bounded Voronoi cells.
`stable_meets_covolume_one_lambda_ge_one` converts stability into the delegation's two
hypotheses.
-/

namespace Submission.StablePrecompact

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "VC" => Submission.Voronoi.voronoi

/-- Stability gives exactly the two hypotheses of the Minkowski-2nd-type delegation:
covolume `1` (det = 1) and shortest vector `≥ 1`. -/
lemma stable_meets_covolume_one_lambda_ge_one (ℒ : Submodule ℤ E) [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) (hSt : Submission.StableLattices.Stable ℒ) :
    ZLattice.covolume ℒ = 1 ∧ ∀ v : ℒ, v ≠ 0 → 1 ≤ ‖(v : E)‖ := by
  classical
  constructor
  · rw [Submission.Poisson.covolume_eq_determinant (ℒ := ℒ) hℒ]
    exact Submission.StableLattices.det_eq_one_of_stable hSt
  · intro v hv
    exact Submission.StableLattices.norm_ge_one_of_stable hSt v hv

/-- **Glue**: a uniform bounded-basis property for the stable rank-`m` lattices puts all
their Voronoi cells inside the common ball `closedBall 0 ((m : ℝ) · C)`.  (Discharge the
hypothesis `hb` with `Commons.Lattice.Minkowski.bounded_basis_covolume_one` once it lands:
`hb ℒ hSt hfin` = L88 applied via `stable_meets_covolume_one_lambda_ge_one`.) -/
lemma stable_voronoi_uniform_bounded (m : ℕ) (C : ℝ)
    (hb : ∀ (ℒ : Submodule ℤ (EuclideanSpace ℝ (Fin m))) [DiscreteTopology ℒ],
      Submission.StableLattices.Stable ℒ → Module.finrank ℤ ℒ = m →
      ∃ b : Module.Basis (Fin m) ℤ ℒ, ∀ i : Fin m, ‖((b i : ℒ) : (EuclideanSpace ℝ (Fin m)))‖ ≤ C) :
    ∀ (ℒ : Submodule ℤ (EuclideanSpace ℝ (Fin m))) [DiscreteTopology ℒ],
      Submission.StableLattices.Stable ℒ → Module.finrank ℤ ℒ = m →
      Submission.Voronoi.voronoi ℒ ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m))
        ((m : ℝ) * C) := by
  classical
  intro ℒ _hDT hSt hfin
  have hℒ : IsZLattice ℝ ℒ := Submission.MainStable.isZLattice_of_finrank (n := m) ℒ hfin
  rcases hb ℒ hSt hfin with ⟨b, hbnd⟩
  have hsum : (∑ i : Fin m, ‖((b i : ℒ) : (EuclideanSpace ℝ (Fin m)))‖) ≤ (m : ℝ) * C := by
    calc
      (∑ i : Fin m, ‖((b i : ℒ) : (EuclideanSpace ℝ (Fin m)))‖) ≤ ∑ i : Fin m, C :=
        Finset.sum_le_sum (fun i hi => hbnd i)
      _ = (m : ℝ) * C := by
        rw [Finset.sum_const, Finset.card_fin]
        simp [nsmul_eq_mul]
  have hcell := Submission.CoveringRadius.voronoi_subset_closedBall_basis (n := m)
    ℒ hℒ b
  exact fun x hx => (Metric.closedBall_subset_closedBall hsum) (hcell hx)

lemma stable_meets_delegation_hypotheses {m : ℕ} (ℒ : Submodule ℤ (EuclideanSpace ℝ (Fin m)))
    [DiscreteTopology ℒ] (hfin : Module.finrank ℤ ℒ = m)
    (hSt : Submission.StableLattices.Stable ℒ) :
    ZLattice.covolume ℒ = 1 ∧ ∀ v : ℒ, v ≠ 0 → 1 ≤ ‖(v : EuclideanSpace ℝ (Fin m))‖ := by
  have hℒ : IsZLattice ℝ ℒ := Submission.MainStable.isZLattice_of_finrank (n := m) ℒ hfin
  exact stable_meets_covolume_one_lambda_ge_one (n := m) ℒ hℒ hSt

/-- **The [B-ii] precompactness datum**: for every ambient dimension `m` there is a radius
`R` such that the Voronoi cells of ALL stable full-rank rank-`m` lattices lie inside the
common ball `closedBall 0 R`.

(Discharges the bounded-basis hypothesis of `stable_voronoi_uniform_bounded` with
`Commons.Lattice.Minkowski.bounded_basis_covolume_one`, fed by
`stable_meets_delegation_hypotheses`.) -/
theorem stable_voronoi_cells_in_common_ball (m : ℕ) :
    ∃ R : ℝ, ∀ (ℒ : Submodule ℤ (EuclideanSpace ℝ (Fin m))) [DiscreteTopology ℒ],
      Submission.StableLattices.Stable ℒ → Module.finrank ℤ ℒ = m →
      Submission.Voronoi.voronoi ℒ ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) R := by
  classical
  rcases Commons.Lattice.Minkowski.bounded_basis_covolume_one m with ⟨C, hCprop⟩
  refine ⟨(m : ℝ) * C, ?_⟩
  have hb : ∀ (ℒ : Submodule ℤ (EuclideanSpace ℝ (Fin m))) [DiscreteTopology ℒ],
      Submission.StableLattices.Stable ℒ → Module.finrank ℤ ℒ = m →
      ∃ b : Module.Basis (Fin m) ℤ ℒ,
        ∀ i : Fin m, ‖((b i : ℒ) : (EuclideanSpace ℝ (Fin m)))‖ ≤ C := by
    intro ℒ _hDT hSt hfin
    exact hCprop ℒ (Submission.MainStable.isZLattice_of_finrank (n := m) ℒ hfin)
      (stable_meets_delegation_hypotheses (m := m) ℒ hfin hSt).1
      (stable_meets_delegation_hypotheses (m := m) ℒ hfin hSt).2
  exact stable_voronoi_uniform_bounded (m := m) (C := C) hb

end Submission.StablePrecompact