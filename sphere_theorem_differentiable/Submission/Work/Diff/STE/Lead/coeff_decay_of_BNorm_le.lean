import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.STE.Lead.coeffFun_bound_and_decay
import Submission.Work.Diff.STE.Lead.Rper_contDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead

open Work.Diff.STE

/-- **Uniform weighted decay of the Fourier coefficients from a uniform `BNorm` bound.**

This is the helper proven here for the localised components of the periodised Galerkin columns: if the
`BNorm` of the (smooth) section `U t` is dominated by `B` uniformly on `[0, τ₀)`, then for each order
`M₀` there is a single constant `C` with `‖û(μ)‖ ⟨μ⟩^{M₀} ≤ C` for every `t ∈ [0, τ₀)`, every
component `(i,a,b)` and every frequency `μ`.

The proof is a one-line application of `coeffFun_bound_and_decay` (which needs the bound on a *closed*
interval `Icc 0 τ`): at a fixed `t ∈ Ico 0 τ₀` we apply it on `Icc 0 t ⊆ Ico 0 τ₀`, with the constant
family `fun _ t' => U t'` and

`C := √(B (2 M₀))` — independent of `t`, `i`, `a`, `b`, `μ`. -/
theorem coeff_decay_of_BNorm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (τ₀ : ℝ) (U : ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (hsm : ∀ t : ℝ, Work.Diff.STE.D.ChartData (I := I) (M := M) (U t))
    (B : ℕ → ℝ) (hB : ∀ k : ℕ, 0 ≤ B k)
    (hUB : ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ k : ℕ, D.BNorm k (U t) ≤ B k) :
    ∀ M₀ : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico (0 : ℝ) τ₀,
      ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ),
      ‖Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ‖ * (Work.Diff.STE.wt μ) ^ M₀ ≤ C := by
  intro M₀
  refine ⟨Real.sqrt (B (2 * M₀)), Real.sqrt_nonneg _, ?_⟩
  intro t ht i a b μ
  obtain ⟨ht0, htτ⟩ := Set.mem_Ico.mp ht
  -- smoothness and periodicity of the (constant) time family, from `hsm`
  have hsm' : ∀ (m : ℕ) (t' : ℝ) (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.Rper i ((fun _ t'' => U t'') m t') a b) := by
    intro m t' i a b
    exact (Rper_contDiff_and_periodic D (U t') (hsm t') i a b).1
  have hper' : ∀ (m : ℕ) (t' : ℝ) (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      Periodic1 (D.Rper i ((fun _ t'' => U t'') m t') a b) := by
    intro m t' i a b
    exact (Rper_contDiff_and_periodic D (U t') (hsm t') i a b).2
  -- the `BNorm` bound, transferred from the half-open to the closed interval `Icc 0 t`
  have hBnd' : ∀ (m : ℕ) (t' : ℝ), t' ∈ Set.Icc (0 : ℝ) t → ∀ k : ℕ,
      D.BNorm k ((fun _ t'' => U t'') m t') ≤ B k := by
    intro m t' ht' k
    obtain ⟨h0, htle⟩ := Set.mem_Icc.mp ht'
    exact hUB t' (Set.mem_Ico.mpr ⟨h0, lt_of_le_of_lt htle htτ⟩) k
  have hmain := coeffFun_bound_and_decay D t B (fun _ t'' => U t'') hsm' hper' hBnd' (hB 0)
  exact hmain.2 M₀ i a b μ 0 t ⟨ht0, le_rfl⟩

end Work.Diff.STE.Lead
