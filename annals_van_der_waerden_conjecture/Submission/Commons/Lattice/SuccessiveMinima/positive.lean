import Mathlib
import Submission.Commons.Lattice.SuccessiveMinima.Basic

/-!
# Positivity of the successive minima of a full-rank `ℤ`-lattice (shared commons)

Every successive minimum `λᵢ(L)` (`1 ≤ i ≤ finrank ℤ L`) of a discrete full-rank
`ℤ`-lattice `L` in a finite-dimensional real normed space is **strictly positive**.

Proof: discreteness of `L` means `{0}` is open in the subspace topology, so some open ball
around `0` contains no nonzero lattice point; equivalently every nonzero lattice point has
norm `≥ ε` for some `ε > 0`.  The commons lemma
`successiveMinimum_ge_of_forall_ne_zero_norm_ge` then gives `ε ≤ λᵢ(L)`, hence
`0 < λᵢ(L)`.

All declarations are Mathlib-only apart from the Commons successive-minima API.
-/

noncomputable section

open Set Filter Metric
set_option autoImplicit false

namespace Commons.Lattice.SuccessiveMinima

/-- A discrete `ℤ`-submodule of a finite-dimensional real normed space has a uniform
positive lower bound on the norms of its nonzero elements: some ball around `0` contains
no nonzero lattice point. -/
lemma exists_norm_lower_bound {E : Type*} [NormedAddCommGroup E]
    (L : Submodule ℤ E) [DiscreteTopology L] :
    ∃ ε : ℝ, 0 < ε ∧ ∀ v : L, ‖(v : E)‖ < ε → v = 0 := by
  classical
  have h0open : IsOpen ({0} : Set L) := isOpen_discrete ({0} : Set L)
  rw [isOpen_induced_iff (f := fun x : L => (x : E))] at h0open
  rcases h0open with ⟨U, hUopen, hU⟩
  have hU0 : (0 : E) ∈ U := by
    have : (0 : L) ∈ (fun x : L => (x : E)) ⁻¹' U := by
      rw [hU]
      simp
    exact this
  rcases (Metric.isOpen_iff.mp hUopen (0 : E) hU0) with ⟨ε, hε0, hε⟩
  refine ⟨ε, hε0, ?_⟩
  intro v hv
  have hvU : (v : E) ∈ U := hε (by simpa [dist_eq_norm] using hv)
  have hvp : v ∈ (fun x : L => (x : E)) ⁻¹' U := hvU
  have : v ∈ ({0} : Set L) := by simpa [hU] using hvp
  simpa using this

/-- **Positivity of successive minima**: for a discrete full-rank `ℤ`-lattice `L` of a
finite-dimensional real normed space, every successive minimum `λᵢ(L)` with
`1 ≤ i ≤ finrank ℤ L` is strictly positive. -/
theorem positive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (i : ℕ) (hi0 : 0 < i) (hi : i ≤ Module.finrank ℤ L) :
    0 < Commons.Lattice.SuccessiveMinima.successiveMinimum L i := by
  classical
  rcases exists_norm_lower_bound L with ⟨ε, hε0, hsep⟩
  have hge : ∀ v : L, v ≠ 0 → ε ≤ ‖(v : E)‖ := by
    intro v hv
    by_contra hlt
    exact hv (hsep v (lt_of_not_ge hlt))
  have hi1 : 1 ≤ i := by omega
  have hS : (successiveMinimumSet L i).Nonempty := nonempty_successiveMinimumSet L i hi
  have hle : ε ≤ successiveMinimum L i :=
    successiveMinimum_ge_of_forall_ne_zero_norm_ge L ε hi1 hS hge
  exact lt_of_lt_of_le hε0 hle

end Commons.Lattice.SuccessiveMinima
