import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.sum_mat_csq_le_ENormB
import Submission.Work.Diff.STE.B3.VarCoef.mat_csq_le_components_sigma

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.VarCoef

/-- **The `σ`-ball variant of `sum_mat_csq_le_ENormB`.**  Same conclusion, but the cut-offs `θ l`
are only required to be `1` on the ball of radius `D.σ l` (rather than `2 * D.σ l`).  This is the
form in which the estimates are consumed downstream; the underlying change-of-partition bound
`mat_csq_le_components_sigma` does not use the hypothesis at all. -/
theorem sum_mat_csq_le_ENormB_sigma
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (s : ℕ) (θ : ι₀ → (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hθ : ∀ (l : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ D.σ l → θ l z = 1)
    (hθsm : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (θ l))
    (hθc : ∀ l, HasCompactSupport (θ l))
    (hθt : ∀ (l : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), z ∈ tsupport (θ l) →
      Work.Diff.STE.flatToE (I := I) (D.x₀ l) z ∈ (extChartAt I (D.x₀ l)).target) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (h : Work.Diff.STE.Bil (I := I) (M := M)),
        (∀ (j : ι₀) (a b : Fin (Module.finrank ℝ E)),
          ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R j h a b)) →
        (∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun z =>
              ((∑' m : Fin (Module.finrank ℝ E) → ℤ,
                ((θ l (z + Work.Diff.STE.iVec m) * D.mat l h a b (z + Work.Diff.STE.iVec m) : ℝ)
                  : ℂ))))))
          ≤ C * (D.ENormB s h + D.ENormB 0 h) := by
  classical
  -- ## 1. The bound of a single chart-`l`, single entry `(a,b)` term, with a constant that is
  -- uniform in the section `h` (`mat_csq_le_components_sigma`, proved in the sibling file).
  have hper : ∀ l : ι₀, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (h : Work.Diff.STE.Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E)),
        (∀ (j : ι₀) (a' b' : Fin (Module.finrank ℝ E)),
          ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R j h a' b')) →
        Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun z =>
          ((∑' m : Fin (Module.finrank ℝ E) → ℤ,
            ((θ l (z + Work.Diff.STE.iVec m) * D.mat l h a b (z + Work.Diff.STE.iVec m) : ℝ)
              : ℂ)))))
          ≤ C * ∑ i : ι₀, ∑ a' : Fin (Module.finrank ℝ E),
              ∑ b' : Fin (Module.finrank ℝ E),
                Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (D.Rper i h a' b')) :=
    fun l => mat_csq_le_components_sigma (I := I) (M := M) D s l (θ l) (hθ l) (hθsm l) (hθc l)
      (hθt l)
  choose Cl hClnn hClb using hper
  -- ## 2. The uniform comparison `BNorm ≤ C (ENormB + ENormB 0)`
  -- (`Work.Diff.STE.B3.VarCoef.BNorm_le_ENormB_of_R_contDiff`, proved in the sibling file)
  obtain ⟨C₀, hC₀nn, hC₀b⟩ := BNorm_le_ENormB_of_R_contDiff (I := I) (M := M) D s
  -- ## 3. The assembly
  have hKnn : (0 : ℝ) ≤ ∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E), Cl l :=
    Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun a _ =>
      Finset.sum_nonneg fun b _ => hClnn l
  refine ⟨(∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E), Cl l) * C₀, mul_nonneg hKnn hC₀nn, ?_⟩
  intro h hsmooth
  have hstep : (∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun z =>
        ((∑' m : Fin (Module.finrank ℝ E) → ℤ,
          ((θ l (z + Work.Diff.STE.iVec m) * D.mat l h a b (z + Work.Diff.STE.iVec m) : ℝ)
            : ℂ))))))
      ≤ (∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E), Cl l) * D.BNorm s h := by
    have h1 : (∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun z =>
          ((∑' m : Fin (Module.finrank ℝ E) → ℤ,
            ((θ l (z + Work.Diff.STE.iVec m) * D.mat l h a b (z + Work.Diff.STE.iVec m) : ℝ)
              : ℂ))))))
        ≤ ∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            Cl l * D.BNorm s h :=
      Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun a _ =>
        Finset.sum_le_sum fun b _ => by
          rw [Work.Diff.STE.B3Data.BNorm]
          exact hClb l h a b hsmooth
    calc (∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun z =>
            ((∑' m : Fin (Module.finrank ℝ E) → ℤ,
              ((θ l (z + Work.Diff.STE.iVec m) * D.mat l h a b (z + Work.Diff.STE.iVec m) : ℝ)
                : ℂ))))))
        ≤ ∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            Cl l * D.BNorm s h := h1
      _ = (∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E),
            ∑ b : Fin (Module.finrank ℝ E), Cl l) * D.BNorm s h := by
          simp only [← Finset.sum_mul]
  calc (∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun z =>
          ((∑' m : Fin (Module.finrank ℝ E) → ℤ,
            ((θ l (z + Work.Diff.STE.iVec m) * D.mat l h a b (z + Work.Diff.STE.iVec m) : ℝ)
              : ℂ))))))
      ≤ (∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E), Cl l) * D.BNorm s h := hstep
    _ ≤ (∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), Cl l)
        * (C₀ * (D.ENormB s h + D.ENormB 0 h)) :=
        mul_le_mul_of_nonneg_left (hC₀b h hsmooth) hKnn
    _ = ((∑ l : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), Cl l) * C₀)
        * (D.ENormB s h + D.ENormB 0 h) := by ring

end Work.Diff.STE.B3.VarCoef
