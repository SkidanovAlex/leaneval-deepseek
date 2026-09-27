import Mathlib

namespace Work.Mostow

/-- A finite tuple of pairwise commuting symmetric operators on a finite-dimensional real inner
product space is simultaneously diagonalized by the finitely many joint eigenspaces indexed by the
eigenvalue lists of the operators: these joint eigenspaces are pairwise orthogonal and span.
(Choose each `eig i` surjecting onto the full set of eigenvalues of `T i`.) -/
theorem jointEigenspacesCover {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] {ι : Type*} [Fintype ι] (T : ι → W →ₗ[ℝ] W)
    (hsym : ∀ i, (T i).IsSymmetric) (hcomm : ∀ i i', Commute (T i) (T i')) :
    ∃ (eig : (i : ι) → Fin (Module.finrank ℝ W) → ℝ),
      (∀ i k, Module.End.HasEigenvalue (T i) (eig i k)) ∧
      (⨆ (j : (i : ι) → ↥(Set.range (eig i))), ⨅ i, Module.End.eigenspace (T i) (j i)) = ⊤ ∧
      (∀ (j j' : (i : ι) → ↥(Set.range (eig i))), j ≠ j' →
        ∀ x ∈ (⨅ i, Module.End.eigenspace (T i) (j i)),
          ∀ y ∈ (⨅ i, Module.End.eigenspace (T i) (j' i)), inner ℝ x y = 0) := by
  classical
  -- the eigenvalue list of `T i` (in decreasing order), which enumerates all eigenvalues
  set eig : (i : ι) → Fin (Module.finrank ℝ W) → ℝ :=
    fun i => (hsym i).eigenvalues rfl with heig
  have heig_apply : ∀ i, eig i = (hsym i).eigenvalues rfl := fun i => by rw [heig]
  have hmem : ∀ i (k : Fin (Module.finrank ℝ W)),
      Module.End.HasEigenvalue (T i) (eig i k) := by
    intro i k
    rw [heig_apply i]
    exact (hsym i).hasEigenvalue_eigenvalues rfl k
  have hrange : ∀ i, Set.range (eig i) = {μ : ℝ | Module.End.HasEigenvalue (T i) μ} := by
    intro i
    rw [heig_apply i]
    ext μ
    exact ⟨fun ⟨k, hk⟩ => hk ▸ (hsym i).hasEigenvalue_eigenvalues rfl k,
      fun hμ => (hsym i).exists_eigenvalues_eq rfl hμ⟩
  refine ⟨eig, hmem, ?_, ?_⟩
  · -- the joint eigenspaces span the whole space
    have htop : ⨆ (χ : ι → ℝ), (⨅ i, Module.End.eigenspace (T i) (χ i)) = ⊤ :=
      LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hsym
        (fun i j _ => hcomm i j)
    rw [← htop]
    refine le_antisymm ?_ ?_
    · refine iSup_le fun j => ?_
      exact le_iSup (fun χ : ι → ℝ => ⨅ i, Module.End.eigenspace (T i) (χ i))
        (fun i => (j i : ℝ))
    · refine iSup_le fun χ => ?_
      by_cases hall : ∀ i, χ i ∈ Set.range (eig i)
      · exact le_iSup
          (fun j : (i : ι) → ↥(Set.range (eig i)) => ⨅ i, Module.End.eigenspace (T i) (j i))
          (fun i => ⟨χ i, hall i⟩)
      · rw [not_forall] at hall
        obtain ⟨i₀, hi₀⟩ := hall
        have hbot : Module.End.eigenspace (T i₀) (χ i₀) = ⊥ := by
          by_contra hc
          exact hi₀ (by rw [hrange i₀]; exact Module.End.hasEigenvalue_iff.mpr hc)
        calc (⨅ i, Module.End.eigenspace (T i) (χ i))
            ≤ Module.End.eigenspace (T i₀) (χ i₀) := iInf_le _ _
          _ = ⊥ := hbot
          _ ≤ _ := bot_le
  · -- distinct joint eigenspaces are orthogonal
    intro j j' hjj' x hx y hy
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hjj'
    have hne : (j i₀ : ℝ) ≠ (j' i₀ : ℝ) := fun h => hi₀ (Subtype.ext h)
    refine ((hsym i₀).orthogonalFamily_eigenspaces.isOrtho hne).inner_eq ?_ ?_
    · exact (Submodule.mem_iInf (fun i => Module.End.eigenspace (T i) (j i))).mp hx i₀
    · exact (Submodule.mem_iInf (fun i => Module.End.eigenspace (T i) (j' i))).mp hy i₀

end Work.Mostow
