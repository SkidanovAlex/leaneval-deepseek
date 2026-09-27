import Mathlib

namespace Work.Mostow

/-- **Dimensions add over an orthogonal decomposition.**

If `P : η → Submodule ℝ V` is a finite family of pairwise orthogonal submodules of a
finite-dimensional real inner product space `V` which together span `V`
(`⨆ i, P i = ⊤`), then `∑ i, Module.finrank ℝ ↥(P i) = Module.finrank ℝ V`. -/
theorem finrank_orthogonal_decomp {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {η : Type*} [Fintype η] (P : η → Submodule ℝ V)
    (horth : ∀ i j : η, i ≠ j → ∀ x ∈ P i, ∀ y ∈ P j, inner ℝ x y = 0)
    (hspan : ⨆ i, P i = ⊤) :
    ∑ i, Module.finrank ℝ ↥(P i) = Module.finrank ℝ V := by
  classical
  have hind : iSupIndep P := by
    rw [iSupIndep_def]
    intro i
    refine Submodule.IsOrtho.disjoint ?_
    rw [Submodule.isOrtho_iSup_right]
    intro j
    rw [Submodule.isOrtho_iSup_right]
    intro hij
    exact Submodule.isOrtho_iff_inner_eq.mpr (horth i j hij.symm)
  have e := hind.linearEquiv hspan
  have h2 : Module.finrank ℝ (Π₀ i, ↥(P i)) = ∑ i, Module.finrank ℝ ↥(P i) :=
    Module.finrank_directSum ℝ (fun i => ↥(P i))
  rw [← e.finrank_eq, h2]

end Work.Mostow
