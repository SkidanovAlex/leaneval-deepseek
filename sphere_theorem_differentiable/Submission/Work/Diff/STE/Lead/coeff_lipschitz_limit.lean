import Mathlib
import Submission.Work.Diff.STE.B3.Comp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead

theorem coeff_lipschitz_limit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (τ₀ L : ℝ)
    (u : ℕ → ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (U : ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (hLip : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ)
      (m : ℕ), ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ t' ∈ Set.Ico (0 : ℝ) τ₀,
      ‖Work.Diff.STE.fourierCoeff (D.Rper i (u m t) a b) μ
        - Work.Diff.STE.fourierCoeff (D.Rper i (u m t') a b) μ‖ ≤ L * |t - t'|)
    (hconv : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ),
      TendstoUniformlyOn
        (fun (m : ℕ) (t : ℝ) => Work.Diff.STE.fourierCoeff (D.Rper i (u m t) a b) μ)
        (fun (t : ℝ) => Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ)
        Filter.atTop (Set.Ico (0 : ℝ) τ₀)) :
    ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ),
      ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ t' ∈ Set.Ico (0 : ℝ) τ₀,
      ‖Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ
        - Work.Diff.STE.fourierCoeff (D.Rper i (U t') a b) μ‖ ≤ L * |t - t'| := by
  intro i a b μ t ht t' ht'
  have h1 : Filter.Tendsto
      (fun m : ℕ => Work.Diff.STE.fourierCoeff (D.Rper i (u m t) a b) μ)
      Filter.atTop (nhds (Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ)) :=
    (hconv i a b μ).tendsto_at ht
  have h2 : Filter.Tendsto
      (fun m : ℕ => Work.Diff.STE.fourierCoeff (D.Rper i (u m t') a b) μ)
      Filter.atTop (nhds (Work.Diff.STE.fourierCoeff (D.Rper i (U t') a b) μ)) :=
    (hconv i a b μ).tendsto_at ht'
  have hnorm : Filter.Tendsto
      (fun m : ℕ => ‖Work.Diff.STE.fourierCoeff (D.Rper i (u m t) a b) μ
        - Work.Diff.STE.fourierCoeff (D.Rper i (u m t') a b) μ‖)
      Filter.atTop
      (nhds ‖Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ
        - Work.Diff.STE.fourierCoeff (D.Rper i (U t') a b) μ‖) :=
    (h1.sub h2).norm
  exact le_of_tendsto hnorm
    (Filter.Eventually.of_forall fun m => hLip i a b μ m t ht t' ht')

end Work.Diff.STE.Lead
