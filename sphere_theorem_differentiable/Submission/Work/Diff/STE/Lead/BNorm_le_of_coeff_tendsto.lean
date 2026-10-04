import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.Data
import Submission.Work.Diff.STE.Lead.CSq_tendsto_of_decay_pointwise

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The composite `Hᵏ` bound passes to a coefficientwise limit

`Work.Diff.STE.Lead.BNorm_le_of_coeff_tendsto`: a sequence of sections `u m` whose composite norms
`D.BNorm k (u m t)` are uniformly bounded by `B k` on `[0,τ₀]`, and whose periodised localised
components have coefficientwise convergent Fourier coefficients (`hconv`) with a uniform decay of
every order (`hdecM`, `hdecU`), has the limit section `U` satisfying the same bound
`D.BNorm k (U t) ≤ B k`.

Route.  `D.BNorm k` is a finite sum (over the charts `i` and the two frame indices `a b`) of the
weighted `ℓ²` masses `CSq k` of the coefficient families of the periodised components.  The uniform
decay hypotheses make all these weighted coefficient families summable in the ordinary sense, so a
junk-`0`-`tsum` cannot occur; Tannery's theorem, packaged for `CSq` as the sibling lemma
`Work.Diff.STE.Lead.CSq_tendsto_of_decay_pointwise` (Tannery for the weighted `ℓ²` mass), then turns
the coefficientwise convergence plus uniform decay into convergence of the weighted `ℓ²` masses.
A finite sum of limits is the limit of the finite sums, hence `D.BNorm k (u m t) → D.BNorm k (U t)`,
and the uniform bound `D.BNorm k (u m t) ≤ B k` passes to the limit.

The only work beyond the sibling lemma is the passage from the per-`(i,a,b)` convergence to the
composite norm: `D.BNorm` is *defined* as the triple finite sum of the component masses, so this is
`tendsto_finsetSum` at the three finite index types, together with the combination `max C₁ C₂` of the
two decay bounds (`hdecM`, `hdecU`) and the evaluation `TendstoUniformlyOn.tendsto_at` of `hconv` at
the fixed time `t`.
-/

namespace Work.Diff.STE.Lead

theorem BNorm_le_of_coeff_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (τ₀ : ℝ)
    (B : ℕ → ℝ) (hB : ∀ k, 0 ≤ B k)
    (u : ℕ → ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (U : ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (hBn : ∀ (m : ℕ) (t : ℝ), t ∈ Set.Ico (0 : ℝ) τ₀ → ∀ k : ℕ, D.BNorm k (u m t) ≤ B k)
    (hdecM : ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (t : ℝ), t ∈ Set.Ico (0 : ℝ) τ₀ →
      ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ),
      ‖Work.Diff.STE.fourierCoeff (D.Rper i (u m t) a b) μ‖ * (Work.Diff.STE.wt μ) ^ M ≤ C)
    (hdecU : ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ), t ∈ Set.Ico (0 : ℝ) τ₀ →
      ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ),
      ‖Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ‖ * (Work.Diff.STE.wt μ) ^ M ≤ C)
    (hconv : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ),
      TendstoUniformlyOn
        (fun (m : ℕ) (t : ℝ) => Work.Diff.STE.fourierCoeff (D.Rper i (u m t) a b) μ)
        (fun (t : ℝ) => Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ)
        Filter.atTop (Set.Ico (0 : ℝ) τ₀)) :
    ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ k : ℕ, D.BNorm k (U t) ≤ B k := by
  intro t ht k
  -- each component family converges in its weighted `ℓ²` mass
  have key : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      Filter.Tendsto (fun m : ℕ => Work.Diff.STE.CSq k
          (fun μ : Fin (Module.finrank ℝ E) → ℤ =>
            Work.Diff.STE.fourierCoeff (D.Rper i (u m t) a b) μ))
        Filter.atTop
        (nhds (Work.Diff.STE.CSq k
          (fun μ : Fin (Module.finrank ℝ E) → ℤ =>
            Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ))) := by
    intro i a b
    refine Work.Diff.STE.Lead.CSq_tendsto_of_decay_pointwise
      (fun (m : ℕ) (μ : Fin (Module.finrank ℝ E) → ℤ) =>
        Work.Diff.STE.fourierCoeff (D.Rper i (u m t) a b) μ)
      (fun μ : Fin (Module.finrank ℝ E) → ℤ =>
        Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ) ?_ ?_ k
    · intro M
      obtain ⟨C₁, hC₁nn, h₁⟩ := hdecM M
      obtain ⟨C₂, hC₂nn, h₂⟩ := hdecU M
      refine ⟨max C₁ C₂, le_max_of_le_left hC₁nn, fun m μ => ⟨?_, ?_⟩⟩
      · exact le_trans (h₁ m t ht i a b μ) (le_max_left C₁ C₂)
      · exact le_trans (h₂ t ht i a b μ) (le_max_right C₁ C₂)
    · intro μ
      exact (hconv i a b μ).tendsto_at ht
  -- the composite norm is the triple finite sum of the component masses
  have hsum : Filter.Tendsto (fun m : ℕ => D.BNorm k (u m t)) Filter.atTop
      (nhds (D.BNorm k (U t))) := by
    simp only [Work.Diff.STE.B3Data.BNorm]
    refine tendsto_finsetSum _ (fun i _ =>
      tendsto_finsetSum _ (fun a _ =>
        tendsto_finsetSum _ (fun b _ => key i a b)))
  exact le_of_tendsto' hsum (fun m => hBn m t ht k)

end Work.Diff.STE.Lead
