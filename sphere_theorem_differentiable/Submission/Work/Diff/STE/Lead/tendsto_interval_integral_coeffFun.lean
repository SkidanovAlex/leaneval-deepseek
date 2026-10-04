import Mathlib
import Submission.Work.Diff.STE.Lead.CoeffRepr

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead

/-- If both endpoints of an interval lie in `[0, τ₀)`, then so does every interior point of the
oriented interval `t..s`. -/
private lemma coeffFun_uIoc_subset_Ico {s t τ₀ : ℝ} (hs : s ∈ Set.Ico (0 : ℝ) τ₀)
    (ht : t ∈ Set.Ico (0 : ℝ) τ₀) : Set.uIoc t s ⊆ Set.Ico (0 : ℝ) τ₀ := by
  intro x hx
  rw [Set.mem_uIoc] at hx
  rw [Set.mem_Ico]
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨le_of_lt (lt_of_le_of_lt ht.1 h1), lt_of_le_of_lt h2 hs.2⟩
  · exact ⟨le_of_lt (lt_of_le_of_lt hs.1 h1), lt_of_le_of_lt h2 ht.2⟩

/-- If both endpoints of an interval lie in `[0, τ₀)`, then the oriented interval `t..s` is
contained in the closed interval `[0, τ₀]`. -/
private lemma coeffFun_uIoc_subset_Icc {s t τ₀ : ℝ} (hs : s ∈ Set.Ico (0 : ℝ) τ₀)
    (ht : t ∈ Set.Ico (0 : ℝ) τ₀) : Set.uIoc t s ⊆ Set.Icc (0 : ℝ) τ₀ := by
  intro x hx
  rw [Set.mem_uIoc] at hx
  rw [Set.mem_Icc]
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨le_of_lt (lt_of_le_of_lt ht.1 h1), le_of_lt (lt_of_le_of_lt h2 hs.2)⟩
  · exact ⟨le_of_lt (lt_of_le_of_lt hs.1 h1), le_of_lt (lt_of_le_of_lt h2 ht.2)⟩

theorem tendsto_interval_integral_coeffFun
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (τ₀ : ℝ) (hτ₀ : 0 < τ₀) (φ : ℕ → ℕ)
    (vs : ℕ → ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (W : ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ)
    (K : ℝ) (hK : 0 ≤ K)
    (hmeas : ∀ (m : ℕ), AEMeasurable
      (fun σ : ℝ => Work.Diff.STE.fourierCoeff (D.Rper i (vs m σ) a b) μ)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Icc (0 : ℝ) τ₀)))
    (hbdd : ∀ (m : ℕ) (σ : ℝ), σ ∈ Set.Icc (0 : ℝ) τ₀ →
      ‖Work.Diff.STE.fourierCoeff (D.Rper i (vs m σ) a b) μ‖ ≤ K)
    (hcv : ∀ σ : ℝ, σ ∈ Set.Ico (0 : ℝ) τ₀ →
      Filter.Tendsto (fun m : ℕ => Work.Diff.STE.fourierCoeff (D.Rper i (vs (φ m) σ) a b) μ)
        Filter.atTop (nhds (Work.Diff.STE.fourierCoeff (D.Rper i (W σ) a b) μ)))
    (s t : ℝ) (hs : s ∈ Set.Ico (0 : ℝ) τ₀) (ht : t ∈ Set.Ico (0 : ℝ) τ₀) :
    Filter.Tendsto (fun m : ℕ => ∫ σ in t..s,
        Work.Diff.STE.fourierCoeff (D.Rper i (vs (φ m) σ) a b) μ)
      Filter.atTop
      (nhds (∫ σ in t..s, Work.Diff.STE.fourierCoeff (D.Rper i (W σ) a b) μ)) := by
  -- Dominated convergence for interval integrals: the coefficients are (a.e.) bounded by the
  -- constant `K` on `[0, τ₀] ⊇ t..s` and converge pointwise on `[0, τ₀) ⊇ t..s`.
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (bound := fun _ => K)
  · refine Filter.Eventually.of_forall fun m => ?_
    exact ((hmeas (φ m)).mono_measure (MeasureTheory.Measure.restrict_mono
      (coeffFun_uIoc_subset_Icc hs ht) le_rfl)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun m => Filter.Eventually.of_forall fun σ hσ =>
      hbdd (φ m) σ (coeffFun_uIoc_subset_Icc hs ht hσ)
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun σ hσ =>
      hcv σ (coeffFun_uIoc_subset_Ico hs ht hσ)

end Work.Diff.STE.Lead
