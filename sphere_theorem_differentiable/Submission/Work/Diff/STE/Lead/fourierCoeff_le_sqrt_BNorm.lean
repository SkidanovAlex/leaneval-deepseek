import Mathlib
import Submission.Work.Diff.STE.Lead.Rper_contDiff
import Submission.Work.Diff.STE.Man.SectSup
import Submission.Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A single Fourier coefficient of a localised component is controlled by `√(BNorm 0)`

The composite `H⁰` norm `D.BNorm 0 h` is, by definition, the sum of the `ℓ²` norms squared of the
Fourier coefficient families of *all* the localised periodised components `D.Rper i h a b`:

  `D.BNorm 0 h = Σ_i Σ_{ab} CSq 0 (fourierCoeff (D.Rper i h a b))`.

Since every summand is a series of nonnegative terms, each single coefficient of each component is
dominated by the whole: `‖fourierCoeff (D.Rper i h a b) μ‖² ≤ D.BNorm 0 h`, hence

  `‖fourierCoeff (D.Rper i h a b) μ‖ ≤ √(D.BNorm 0 h)`

with the universal constant `C = 1` (independent of the section `h`).

The only non-formal input is the *summability* of the `ℓ²` coefficient family of a component, so
that the bound `f μ ≤ ∑' k, f k` may be applied: the component is `C^∞` and `1`-periodic for
smooth chart data (`Work.Diff.STE.Lead.Rper_contDiff_and_periodic`), hence `L²` on the cube, and
Bessel/Parseval (`Work.Diff.STE.ste_summable_sq_fourierCoeff`) gives the summability.
-/

noncomputable section

open MeasureTheory BigOperators
open scoped Manifold ContDiff Bundle Topology

namespace Work.Diff.STE.Lead

/-- **A single Fourier coefficient of a square summable coefficient family is bounded by the
`H⁰` norm (the plain `ℓ²` norm) of the family.** -/
lemma norm_le_sqrt_CSq_zero {ι : Type*} [Fintype ι] {c : (ι → ℤ) → ℂ}
    (hc : Summable (fun k : ι → ℤ => ‖c k‖ ^ 2)) (μ : ι → ℤ) :
    ‖c μ‖ ≤ Real.sqrt (Work.Diff.STE.CSq 0 c) := by
  refine Real.le_sqrt_of_sq_le ?_
  have hCsq : Work.Diff.STE.CSq 0 c = ∑' k : ι → ℤ, ‖c k‖ ^ 2 := by
    simp only [Work.Diff.STE.CSq, pow_zero, one_mul]
  rw [hCsq]
  exact hc.le_tsum μ (fun j _ => sq_nonneg _)

/-- **The Fourier coefficients of a periodised localised component are square summable.**  The
component is `C^∞` and `1`-periodic (for smooth chart data), hence `L²` on the unit cube, and
Bessel/Parseval applies. -/
lemma summable_sq_fourierCoeff_Rper
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (i : ι₀) (a b : Fin (Module.finrank ℝ E)) :
    Summable (fun μ : Fin (Module.finrank ℝ E) → ℤ =>
      ‖Work.Diff.STE.fourierCoeff (D.Rper i h a b) μ‖ ^ 2) :=
  Work.Diff.STE.ste_summable_sq_fourierCoeff _
    (Work.Diff.STE.ste_memLp_of_continuous
      (Rper_contDiff_and_periodic (I := I) (M := M) D h hh i a b).1.continuous)

theorem fourierCoeff_le_sqrt_BNorm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : Work.Diff.STE.Bil (I := I) (M := M)),
      Work.Diff.STE.D.ChartData (I := I) (M := M) h →
      ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ),
        ‖Work.Diff.STE.fourierCoeff (D.Rper i h a b) μ‖ ≤ C * Real.sqrt (D.BNorm 0 h) := by
  refine ⟨1, zero_le_one, ?_⟩
  intro h hh i a b μ
  have hsumm := summable_sq_fourierCoeff_Rper (I := I) (M := M) D h hh i a b
  -- the single `CSq 0` is dominated by the composite norm `BNorm 0`
  have hBN : Work.Diff.STE.CSq 0 (Work.Diff.STE.fourierCoeff (D.Rper i h a b)) ≤ D.BNorm 0 h := by
    change Work.Diff.STE.CSq 0 (Work.Diff.STE.fourierCoeff (D.Rper i h a b))
      ≤ ∑ i' : ι₀, ∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
        Work.Diff.STE.CSq 0 (Work.Diff.STE.fourierCoeff (D.Rper i' h a' b'))
    exact Work.Diff.STE.sum3_single_le
      (fun i' a' b' => Work.Diff.STE.CSq 0 (Work.Diff.STE.fourierCoeff (D.Rper i' h a' b')))
      (fun i' a' b' => Work.Diff.STE.CSq_nonneg 0 _) i a b
  calc ‖Work.Diff.STE.fourierCoeff (D.Rper i h a b) μ‖
      ≤ Real.sqrt (Work.Diff.STE.CSq 0 (Work.Diff.STE.fourierCoeff (D.Rper i h a b))) :=
        norm_le_sqrt_CSq_zero hsumm μ
    _ ≤ Real.sqrt (D.BNorm 0 h) := Real.sqrt_le_sqrt hBN
    _ = 1 * Real.sqrt (D.BNorm 0 h) := (one_mul _).symm

end Work.Diff.STE.Lead
