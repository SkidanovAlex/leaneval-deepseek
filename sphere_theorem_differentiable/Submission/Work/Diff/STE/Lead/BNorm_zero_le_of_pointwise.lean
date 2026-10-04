import Mathlib
import Submission.Work.Diff.STE.Lead.Rper_contDiff
import Submission.Work.Diff.STE.Lead.ENormSq_zero_Rper_le
import Submission.Work.Diff.STE.CSq_le_ENormSq
import Submission.Work.Diff.STE.Man.SectSup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The composite `H⁰` norm of a pointwise bounded section

For Layer B3 data `D` (`B3Data ι₀ g₀`) and a section `X : Bil` which is *pointwise* bounded by `K`
in the `g₀`-sense,

`|X y u v| ≤ K √(g₀.inner y u u) √(g₀.inner y v v)`,

the composite norm `D.BNorm 0 X = Σ_i Σ_{ab} CSq 0 (fourierCoeff (D.Rper i X a b))` is bounded by
`C K²`, with `C` depending only on `D` (`ChartData X` is required so that the periodised components
are smooth, which is needed to invoke the Sobolev comparison `CSq_le_ENormSq`).

Route: for a section with smooth chart data each periodised component `D.Rper i X a b` is `C^∞`
(`Rper_contDiff_and_periodic`), so the `k = 0` case of the Sobolev comparison `CSq_le_ENormSq` gives

`CSq 0 (fourierCoeff f) ≤ 2 * ENormSq 0 f`,

and the `L²` energy of each component is bounded by `C₂ K²` for a single constant `C₂`
(`ENormSq_zero_Rper_le`).  Summing over the (finitely many) components
`i : ι₀`, `a b : Fin (Module.finrank ℝ E)` turns `K²` into `card ι₀ * n * n * K²`.
-/

namespace Work.Diff.STE.Lead

/-- **The composite norm of a pointwise bounded section is bounded by a multiple of `K²`.** -/
theorem BNorm_zero_le_of_pointwise
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : Work.Diff.STE.Bil (I := I) (M := M)) (K : ℝ), 0 ≤ K →
      (∀ (y : M) (u v : TangentSpace I y),
        |X y u v| ≤ K * Real.sqrt (g₀.inner y u u) * Real.sqrt (g₀.inner y v v)) →
      Work.Diff.STE.D.ChartData (I := I) (M := M) X →
      D.BNorm 0 X ≤ C * K ^ 2 := by
  -- The two ingredients: the `L²` bound for one component, and the Sobolev comparison at `k = 0`.
  obtain ⟨C₂, hC₂nn, hC₂⟩ := ENormSq_zero_Rper_le (I := I) (M := M) D
  obtain ⟨C₁, hC₁nn, hC₁⟩ := CSq_le_ENormSq (ι := Fin (Module.finrank ℝ E)) 0
  refine ⟨C₁ * 2 * C₂ * ((Fintype.card ι₀ : ℝ) * ((Module.finrank ℝ E : ℕ) : ℝ)
    * ((Module.finrank ℝ E : ℕ) : ℝ)), by positivity, ?_⟩
  intro X K hK hbound hchart
  -- `CSq 0 (fourierCoeff (Rper i X a b)) ≤ (C₁ * 2 * C₂) * K ^ 2` for every component.
  have hterm : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      CSq 0 (fourierCoeff (D.Rper i X a b)) ≤ (C₁ * 2 * C₂) * K ^ 2 := by
    intro i a b
    obtain ⟨hcd, hper⟩ := Rper_contDiff_and_periodic (I := I) (M := M) D X hchart i a b
    have hE := hC₂ X K hK hbound i a b
    have h1 := hC₁ (D.Rper i X a b) (hcd.of_le (by simp)) hper
    calc CSq 0 (fourierCoeff (D.Rper i X a b))
        ≤ C₁ * (ENormSq 0 (D.Rper i X a b) + ENormSq 0 (D.Rper i X a b)) := h1
      _ = C₁ * (2 * ENormSq 0 (D.Rper i X a b)) := by ring
      _ ≤ C₁ * (2 * (C₂ * K ^ 2)) :=
          mul_le_mul_of_nonneg_left (by linarith) hC₁nn
      _ = (C₁ * 2 * C₂) * K ^ 2 := by ring
  -- Sum over the finitely many components.
  calc D.BNorm 0 X
      = ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          CSq 0 (fourierCoeff (D.Rper i X a b)) := rfl
    _ ≤ ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          (C₁ * 2 * C₂) * K ^ 2 :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum
          (fun a _ => Finset.sum_le_sum (fun b _ => hterm i a b)))
    _ = ((Fintype.card ι₀ : ℝ) * ((Module.finrank ℝ E : ℕ) : ℝ)
          * ((Module.finrank ℝ E : ℕ) : ℝ)) * ((C₁ * 2 * C₂) * K ^ 2) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [Fintype.card_fin]
        ring
    _ = (C₁ * 2 * C₂ * ((Fintype.card ι₀ : ℝ) * ((Module.finrank ℝ E : ℕ) : ℝ)
          * ((Module.finrank ℝ E : ℕ) : ℝ))) * K ^ 2 := by ring

end Work.Diff.STE.Lead
