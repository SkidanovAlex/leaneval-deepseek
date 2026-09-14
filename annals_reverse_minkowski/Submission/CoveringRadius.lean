import Mathlib
import Submission.VoronoiMeasure
open Module Real
open scoped Real BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# [B-ii] basis-boundedness hook: covering radius and cell radius from a ℤ-basis

Mahler compactness of the family of stable lattices will be stated in terms of a basis
parametrization: a full-rank lattice `ℒ ≤ E` is identified with (a unimodular class of)
basis matrices.  The first boundedness ingredient is that *every* full-rank lattice has a
covering radius controlled by (the sum of the norms of) **any** of its `ℤ`-bases: using the
`ZSpan.floor`/`ZSpan.fract` decomposition (`x = floor + fract`, `fract` in the fundamental
domain, `‖fract x‖ ≤ Σᵢ‖βᵢ‖` by `ZSpan.norm_fract_le`), every ambient point lies within
`R(b) := Σᵢ ‖(bᵢ : E)‖` of the lattice.  Since the Voronoi cell consists of points closest
to the origin in their translate class, `V(ℒ) ⊆ closedBall 0 R(b)` follows.

Consequences:
* every full-rank lattice admits a *concrete* bounded fundamental body (its Voronoi cell
  inside an explicit ball from *any* basis);
* families of lattices admitting bases with uniformly bounded `R(b)` (e.g. the stable ones,
  via the Minkowski-second-type `Commons.Lattice.Minkowski.bounded_basis_covolume_one`
  delegation — see `Submission/StablePrecompact.lean`) have uniformly bounded Voronoi
  cells — the precompactness datum the [B-ii] topology layer hangs from.
-/

namespace Submission.CoveringRadius

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "VC" => Submission.Voronoi.voronoi

/-- The covering-radius bound from **any** `ℤ`-basis: every ambient point is within
`Σᵢ ‖(bᵢ : E)‖` of the lattice. -/
lemma exists_lattice_point_within_basis {ι : Type*} [Fintype ι]
    (ℒ : Submodule ℤ E) [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    (b : Module.Basis ι ℤ ℒ) (x : E) :
    ∃ v : ℒ, ‖x - (v : E)‖ ≤ ∑ i : ι, ‖((b i : ℒ) : E)‖ := by
  classical
  haveI : IsZLattice ℝ ℒ := hℒ
  let β : Module.Basis ι ℝ E := b.ofZLatticeBasis ℝ ℒ
  let y : E := (ZSpan.floor β x : E)
  have hy : y ∈ ℒ := by
    have h0 : (ZSpan.floor β x : E) ∈ (Submodule.span ℤ (Set.range ⇑β)) :=
      (ZSpan.floor β x).2
    have hspaneq := b.ofZLatticeBasis_span ℝ
    exact (congrArg (fun S : Submodule ℤ E => (ZSpan.floor β x : E) ∈ S) hspaneq).mp
      (by simpa [β] using h0)
  let v : ℒ := ⟨y, hy⟩
  refine ⟨v, ?_⟩
  have hdec : x - (v : E) = ZSpan.fract β x := by
    dsimp [v, y]
    rfl
  rw [hdec]
  have hval : ∀ i : ι, (β i : E) = ((b i : ℒ) : E) := by
    intro i
    dsimp [β]
    simpa using (b.ofZLatticeBasis_apply ℝ i)
  calc
    ‖ZSpan.fract β x‖ ≤ ∑ i : ι, ‖β i‖ := ZSpan.norm_fract_le β x
    _ = ∑ i : ι, ‖((b i : ℒ) : E)‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hval i]

/-- The Voronoi cell of a full-rank lattice lies in the closed ball of radius
`Σᵢ‖(bᵢ : E)‖` for any `ℤ`-basis `b`. -/
lemma voronoi_subset_closedBall_basis {ι : Type*} [Fintype ι]
    (ℒ : Submodule ℤ E) [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    (b : Module.Basis ι ℤ ℒ) :
    VC ℒ ⊆ Metric.closedBall (0 : E) (∑ i : ι, ‖((b i : ℒ) : E)‖) := by
  classical
  haveI : IsZLattice ℝ ℒ := hℒ
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  rcases exists_lattice_point_within_basis ℒ hℒ b x with ⟨v, hv⟩
  have hV := (Submission.VoronoiMeasure.mem_voronoi_iff_norm (ℒ := ℒ) x).mp hx v
  let R : ℝ := ∑ i : ι, ‖((b i : ℒ) : E)‖
  have hR0 : 0 ≤ R := by
    dsimp [R]
    positivity
  have hsq : ‖x‖ ^ 2 ≤ R ^ 2 := by
    have hxv : ‖x - (v : E)‖ ≥ 0 := norm_nonneg _
    have h : ‖x - (v : E)‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hxv hv 2
    nlinarith [hV, h]
  exact le_of_sq_le_sq hsq hR0

end Submission.CoveringRadius
