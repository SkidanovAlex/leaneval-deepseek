import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.CSq_trunc_le
import Submission.Work.Diff.STE.norm_seriesFun_le
import Submission.Work.Diff.STE.summable_wt_zpow
import Submission.Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff
import Submission.Work.Diff.STE.periodization_contDiff_periodic
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.JPrelim
import Submission.Work.Diff.STE.B3.ENormSq_le_CSq
import Submission.Work.Diff.STE.B3.R_contDiff_of_chartData

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Sup-norm of the Friedrichs truncation of a localised component against the weighted `ℓ²` mass

`Work.Diff.STE.B3Data.STruncR ρ ε f z` is the value at `z` of the Friedrichs truncation of the
`1`-periodic function obtained by periodising `f`: the Fourier multiplier `ρ (ε ·)` is applied to
the coefficients of the periodisation and the resulting series is evaluated at `z`.

For a localised component `f = D.R i h a b` the periodisation is exactly the Layer B3 object
`D.Rper i h a b` (`Comp.lean`), so the whole estimate is the elementary Sobolev-embedding step of
Layer A:

  `|STruncR ρ ε (D.R i h a b) z| ≤ ‖seriesFun (trunc ρ ε (fourierCoeff (D.Rper i h a b))) z‖`
   (the real part is bounded by the modulus),

then `Work.Diff.STE.norm_seriesFun_le` bounds the sup-norm of a Fourier series by
`C(ι,k) √(CSq k ·)` (Cauchy–Schwarz against the dual weight `⟨k⟩^{-2k}`, summable because
`card ι < 2k`), and finally `Work.Diff.STE.CSq_trunc_le` removes the multiplier using `‖ρ‖ ≤ 1`.

The only regularity input is the smoothness of the localised component `D.R i h a b`, which for a
section given by `Work.Diff.STE.D.ChartData` is
`Work.Diff.STE.B3.R_contDiff_of_chartData`; periodising a cube-supported smooth function preserves
smoothness and `1`-periodicity (`Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff`).
-/

noncomputable section

namespace Work.Diff.STE.Lead.GalTame

/-- The Fourier multiplier `trunc ρ ε` does not increase the weighted `ℓ²` mass: summability of
`Σ_k ⟨k⟩^{2s} ‖c k‖²` is inherited by the truncated family, because `‖ρ‖ ≤ 1`. -/
private lemma summable_trunc_wt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1) (ε : ℝ) (s : ℕ) (c : (ι → ℤ) → ℂ)
    (hc : Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖c k‖ ^ 2)) :
    Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖Work.Diff.STE.trunc ρ ε c k‖ ^ 2) := by
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (Work.Diff.STE.wt_pos k).le s) (sq_nonneg _))
    (fun k => ?_) hc
  have hρk : |ρ (ε • fun i => (k i : ℝ))| ≤ 1 := by
    simpa [Real.norm_eq_abs] using hρ _
  have hk : ‖Work.Diff.STE.trunc ρ ε c k‖ ≤ ‖c k‖ := by
    rw [Work.Diff.STE.trunc, norm_mul, Work.Diff.STE.norm_ofReal_cast]
    calc |ρ (ε • fun i => (k i : ℝ))| * ‖c k‖ ≤ 1 * ‖c k‖ :=
          mul_le_mul_of_nonneg_right hρk (norm_nonneg _)
      _ = ‖c k‖ := one_mul _
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hk 2)
    (pow_nonneg (Work.Diff.STE.wt_pos k).le s)

theorem STruncR_Rper_le_CSq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (k : ℕ) (hk : Fintype.card (Fin (Module.finrank ℝ E)) < 2 * k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ) (h : Work.Diff.STE.Bil (I := I) (M := M)),
      Work.Diff.STE.D.ChartData (I := I) (M := M) h →
      ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E))
        (z : Fin (Module.finrank ℝ E) → ℝ),
        |Work.Diff.STE.B3Data.STruncR ρ ε (D.R i h a b) z|
          ≤ C * Real.sqrt (Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper i h a b))) := by
  classical
  obtain ⟨C, hC, hbound⟩ :=
    Work.Diff.STE.norm_seriesFun_le (ι := Fin (Module.finrank ℝ E)) k hk
  refine ⟨C, hC, ?_⟩
  intro ε h hh i a b z
  -- smoothness of the localised component, hence of its periodisation
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (D.R i h a b) :=
    Work.Diff.STE.B3.R_contDiff_of_chartData D h hh i a b
  obtain ⟨hcd, hper⟩ := Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff D i h a b hsm
  -- weighted `ℓ²` summability of the Fourier coefficients of `Rper i h a b`
  have hc : Summable (fun m : Fin (Module.finrank ℝ E) → ℤ =>
      (Work.Diff.STE.wt m) ^ k * ‖Work.Diff.STE.fourierCoeff (D.Rper i h a b) m‖ ^ 2) :=
    Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff (D.Rper i h a b) hcd hper k
  have hct : Summable (fun m : Fin (Module.finrank ℝ E) → ℤ =>
      (Work.Diff.STE.wt m) ^ k
        * ‖Work.Diff.STE.trunc ρ ε (Work.Diff.STE.fourierCoeff (D.Rper i h a b)) m‖ ^ 2) :=
    summable_trunc_wt ρ hρ ε k _ hc
  -- `STruncR` of the localised component is the real part of the Fourier series of the truncation
  -- of the coefficients of its periodisation
  have hunfold : Work.Diff.STE.B3Data.STruncR ρ ε (D.R i h a b) z
      = (Work.Diff.STE.seriesFun (Work.Diff.STE.trunc ρ ε
          (Work.Diff.STE.fourierCoeff (D.Rper i h a b))) z).re := rfl
  rw [hunfold]
  calc |(Work.Diff.STE.seriesFun (Work.Diff.STE.trunc ρ ε
          (Work.Diff.STE.fourierCoeff (D.Rper i h a b))) z).re|
      ≤ ‖Work.Diff.STE.seriesFun (Work.Diff.STE.trunc ρ ε
          (Work.Diff.STE.fourierCoeff (D.Rper i h a b))) z‖ := Complex.abs_re_le_norm _
    _ ≤ C * Real.sqrt (Work.Diff.STE.CSq k (Work.Diff.STE.trunc ρ ε
          (Work.Diff.STE.fourierCoeff (D.Rper i h a b)))) := hbound _ hct z
    _ ≤ C * Real.sqrt (Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper i h a b))) :=
        mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt (Work.Diff.STE.CSq_trunc_le ρ hρ ε k _ hc)) hC

end Work.Diff.STE.Lead.GalTame
