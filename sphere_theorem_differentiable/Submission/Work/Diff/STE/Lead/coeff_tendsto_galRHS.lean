import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.STE.B3.BPair_J_self
import Submission.Work.Diff.STE.B3.BPair_Rstar
import Submission.Work.Diff.STE.Lead.deTurck_bound
import Submission.Work.Diff.STE.Lead.pPhiJetOf_uniform_v2
import Submission.Work.Diff.STE.B3.fourierCoeff_periodization
import Submission.Work.Diff.STE.B3.transport_Rres_contDiffOn
import Submission.Work.Diff.STE.B3.R_contDiff_of_chartData
import Submission.Work.Diff.STE.Lead.CoeffRepr
import Submission.Work.Diff.STE.Lead.BNorm_tendsto_of_coeff_tendsto
import Submission.Work.Diff.STE.Lead.BNorm_zero_le_of_pointwise
import Submission.Work.Diff.STE.Lead.J_tendsto
import Submission.Work.Diff.STE.Lead.jet2_sub
import Submission.Work.Diff.STE.Lead.clm_norm_le_basis
import Submission.Work.Diff.STE.Lead.Gal.SpanLin
import Submission.Work.Diff.STE.Lead.Gal.SpanBridge
import Submission.Work.Diff.STE.Lead.Gal.Prelude
import Submission.Work.Diff.STE.Lead.galState_J_props
import Submission.Work.Diff.STE.Lead.deTurckSec_BNorm0_tendsto
import Submission.Work.Diff.STE.D.isSymm_deTurckSec
import Submission.Work.Diff.STE.Lead.Rper_contDiff
import Submission.Work.Diff.STE.Lead.fourierCoeff_le_sqrt_BNorm
import Submission.Work.Diff.STE.B3.scoeff_add_of_support
import Submission.Work.Diff.STE.poincare_cube

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace Work.Diff.STE.Lead

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 8000000

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- **Additivity of the Fourier coefficient for continuous functions.** -/
private lemma fourierCoeff_add_cont {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : (ι → ℝ) → ℂ) (hf : Continuous f) (hg : Continuous g) (k : ι → ℤ) :
    Work.Diff.STE.fourierCoeff (fun x => f x + g x) k
      = Work.Diff.STE.fourierCoeff f k + Work.Diff.STE.fourierCoeff g k := by
  have h1 : Integrable (fun x : ι → ℝ => Work.Diff.STE.fourierExp (-k) x * f x)
      (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
    Work.Diff.STE.integrableOn_unitCube_of_continuous
      ((Work.Diff.STE.contDiff_fourierExp (-k)).continuous.mul hf)
  have h2 : Integrable (fun x : ι → ℝ => Work.Diff.STE.fourierExp (-k) x * g x)
      (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
    Work.Diff.STE.integrableOn_unitCube_of_continuous
      ((Work.Diff.STE.contDiff_fourierExp (-k)).continuous.mul hg)
  simp only [Work.Diff.STE.fourierCoeff]
  rw [← MeasureTheory.integral_add h1 h2]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

/-- **Additivity of the localised component in the section.** -/
lemma R_add' (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (X Y : Work.Diff.STE.Bil (I := I) (M := M)) (i : ι₀)
    (a b : Fin (Module.finrank ℝ E)) :
    D.R i (X + Y) a b = D.R i X a b + D.R i Y a b := by
  funext z
  simp only [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat, Pi.add_apply, add_apply]
  ring

/-- **Additivity of the periodised component in the section.** -/
lemma Rper_add' (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (X Y : Work.Diff.STE.Bil (I := I) (M := M)) (i : ι₀)
    (a b : Fin (Module.finrank ℝ E)) :
    D.Rper i (X + Y) a b = D.Rper i X a b + D.Rper i Y a b := by
  have hR : D.R i (X + Y) a b = D.R i X a b + D.R i Y a b := R_add' D X Y i a b
  funext z
  show Work.Diff.STE.B3.perFun (D.R i (X + Y) a b) z
      = Work.Diff.STE.B3.perFun (D.R i X a b) z + Work.Diff.STE.B3.perFun (D.R i Y a b) z
  rw [hR]
  exact Work.Diff.STE.B3.perFun_add _ _
    (Work.Diff.STE.B3Data.R_support_halfOpen D X i a b)
    (Work.Diff.STE.B3Data.R_support_halfOpen D Y i a b) z

/-- **Additivity of the Fourier coefficients of the periodised components.** -/
lemma fourierCoeff_Rper_add' (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (X Y : Work.Diff.STE.Bil (I := I) (M := M)) (i : ι₀)
    (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ)
    (hX : ContDiff ℝ (⊤ : ℕ∞) (D.Rper i X a b))
    (hY : ContDiff ℝ (⊤ : ℕ∞) (D.Rper i Y a b)) :
    Work.Diff.STE.fourierCoeff (D.Rper i (X + Y) a b) μ
      = Work.Diff.STE.fourierCoeff (D.Rper i X a b) μ
        + Work.Diff.STE.fourierCoeff (D.Rper i Y a b) μ := by
  rw [show D.Rper i (X + Y) a b
      = fun z => D.Rper i X a b z + D.Rper i Y a b z from
    funext fun z => congrFun (Rper_add' D X Y i a b) z]
  exact fourierCoeff_add_cont _ _ hX.continuous hY.continuous μ

/-- **`IsSymm` is preserved by subtraction.** -/
lemma IsSymm_sub {h k : Work.Diff.STE.Bil (I := I) (M := M)}
    (hh : Work.Diff.STE.D.IsSymm (I := I) h) (hk : Work.Diff.STE.D.IsSymm (I := I) k) :
    Work.Diff.STE.D.IsSymm (I := I) (h - k) := by
  intro x u v
  simp only [Pi.sub_apply, sub_apply]
  rw [hh x u v, hk x u v]

/-- **`IsSymm` is preserved by addition.** -/
lemma IsSymm_add {h k : Work.Diff.STE.Bil (I := I) (M := M)}
    (hh : Work.Diff.STE.D.IsSymm (I := I) h) (hk : Work.Diff.STE.D.IsSymm (I := I) k) :
    Work.Diff.STE.D.IsSymm (I := I) (h + k) := by
  intro x u v
  simp only [Pi.add_apply, add_apply]
  rw [hh x u v, hk x u v]

/-- **The Friedrichs mollifier is additive in the section** (for symmetric sections with smooth
chart data, and for a profile `ρ` supported in the ball of radius `√2` and `ε > 0`, so that the
truncation is a finite Fourier sum).  This is `J_eq_genMap_galCoeff` combined with the additivity of
`galCoeff` and of `genMap`. -/
lemma J_add' (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (h k : Work.Diff.STE.Bil (I := I) (M := M))
    (hsmh : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (hsmk : Work.Diff.STE.D.ChartData (I := I) (M := M) k)
    (hsymh : Work.Diff.STE.D.IsSymm (I := I) h)
    (hsymk : Work.Diff.STE.D.IsSymm (I := I) k) :
    D.J ρ ε (h + k) = D.J ρ ε h + D.J ρ ε k := by
  have hsym : Work.Diff.STE.D.IsSymm (I := I) (h + k) := IsSymm_add hsymh hsymk
  rw [Work.Diff.STE.Lead.J_eq_genMap_galCoeff D ρ ε hε hρ0 (h + k) hsym,
    Work.Diff.STE.Lead.J_eq_genMap_galCoeff D ρ ε hε hρ0 h hsymh,
    Work.Diff.STE.Lead.J_eq_genMap_galCoeff D ρ ε hε hρ0 k hsymk,
    Work.Diff.STE.Lead.Gal.galCoeff_add D ρ ε h k hsmh hsmk,
    Work.Diff.STE.Lead.Gal.genMap_add]

end Helpers

/-- **Reduction of `coeff_tendsto_galRHS` to the `H⁰`-convergence of the sections under the
DeTurck operator.**

If `X m → Y` in the composite norm `BNorm 0` (which in the application is supplied by the uniform
convergence of the DeTurck operators, cf. `deTurckSec_BNorm0_tendsto`), then the Fourier
coefficients of the components of the Friedrichs mollification `J ρ (ε m) (X m)` converge to those
of `Y`.

Route.  `J ρ (ε m)` is additive in the section (`J_add'`), so
`J ρ (ε m) (X m) = J ρ (ε m) (X m - Y) + J ρ (ε m) Y`, and the coefficient functional is additive
in the section for smooth components; hence

`ĉ_μ (J ρ (ε m) (X m)) - ĉ_μ Y = ĉ_μ (J ρ (ε m) (X m - Y)) + ĉ_μ (J ρ (ε m) Y - Y)`,

whose modulus is bounded by `√(BNorm 0 (J ρ (ε m) (X m - Y))) + √(BNorm 0 (J ρ (ε m) Y - Y))`
(`fourierCoeff_le_sqrt_BNorm`).  The first term is `≤ √C₀ √(BNorm 0 (X m - Y))` by the uniform
`H⁰`-bound `hJN` for `J`, and the second tends to `0` by the limit hypothesis `hJT` at the fixed
section `Y`.  Both bounds vanish, and the squeeze concludes. -/
theorem coeff_tendsto_galRHS_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hJN : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
      ∀ h : Work.Diff.STE.Bil (I := I) (M := M),
      Work.Diff.STE.D.ChartData (I := I) (M := M) h → D.BNorm k (D.J ρ ε h) ≤ C * D.BNorm k h)
    (hJT : ∀ (k : ℕ) (h : Work.Diff.STE.Bil (I := I) (M := M)),
      Work.Diff.STE.D.ChartData (I := I) (M := M) h →
      Filter.Tendsto (fun ε => D.BNorm k (D.J ρ ε h - h))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (ε : ℕ → ℝ) (hε : ∀ m : ℕ, ε m ∈ Set.Ioc (0 : ℝ) 1)
    (hε0 : Filter.Tendsto ε Filter.atTop (nhds 0))
    (X : ℕ → Work.Diff.STE.Bil (I := I) (M := M))
    (Y : Work.Diff.STE.Bil (I := I) (M := M))
    (hCDX : ∀ m : ℕ, Work.Diff.STE.D.ChartData (I := I) (M := M) (X m))
    (hCDY : Work.Diff.STE.D.ChartData (I := I) (M := M) Y)
    (hsymX : ∀ m : ℕ, Work.Diff.STE.D.IsSymm (I := I) (X m))
    (hsymY : Work.Diff.STE.D.IsSymm (I := I) Y)
    (hBN : Filter.Tendsto (fun m : ℕ => D.BNorm 0 (X m - Y)) Filter.atTop (nhds 0))
    (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ) :
    Filter.Tendsto (fun m : ℕ =>
      Work.Diff.STE.fourierCoeff (D.Rper i (D.J ρ (ε m) (X m)) a b) μ)
      Filter.atTop (nhds (Work.Diff.STE.fourierCoeff (D.Rper i Y a b) μ)) := by
  classical
  -- ### the universal constant of `fourierCoeff_le_sqrt_BNorm`, and the `H⁰` bound `hJN 0`
  obtain ⟨C₁, hC₁nn, hC₁⟩ := Work.Diff.STE.Lead.fourierCoeff_le_sqrt_BNorm (I := I) (M := M) D
  obtain ⟨C₀, hC₀nn, hC₀⟩ := hJN 0
  -- ### the limit hypothesis at the fixed section `Y`, composed with `ε m → 0⁺`
  have hJTY : Filter.Tendsto (fun m : ℕ => D.BNorm 0 (D.J ρ (ε m) Y - Y))
      Filter.atTop (nhds 0) :=
    (hJT 0 Y hCDY).comp (by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hε0, Filter.Eventually.of_forall fun m => (hε m).1⟩)
  -- ### smooth chart data of the intermediate sections
  have hCDxy : ∀ m : ℕ, Work.Diff.STE.D.ChartData (I := I) (M := M) (X m - Y) :=
    fun m => Work.Diff.STE.Lead.ChartData_sub (I := I) (M := M) (X m) Y (hCDX m) hCDY
  have hCDJx : ∀ m : ℕ, Work.Diff.STE.D.ChartData (I := I) (M := M) (D.J ρ (ε m) (X m)) :=
    fun m => Work.Diff.STE.Lead.chartData_J_props (I := I) (M := M) D ρ hρ (ε m) (X m) (hCDX m)
  have hCDJy : ∀ m : ℕ, Work.Diff.STE.D.ChartData (I := I) (M := M) (D.J ρ (ε m) Y) :=
    fun m => Work.Diff.STE.Lead.chartData_J_props (I := I) (M := M) D ρ hρ (ε m) Y hCDY
  have hCDJxy : ∀ m : ℕ,
      Work.Diff.STE.D.ChartData (I := I) (M := M) (D.J ρ (ε m) (X m - Y)) :=
    fun m => Work.Diff.STE.Lead.chartData_J_props (I := I) (M := M) D ρ hρ (ε m)
      (X m - Y) (hCDxy m)
  have hCDJyy : ∀ m : ℕ,
      Work.Diff.STE.D.ChartData (I := I) (M := M) (D.J ρ (ε m) Y - Y) :=
    fun m => Work.Diff.STE.Lead.ChartData_sub (I := I) (M := M) (D.J ρ (ε m) Y) Y
      (hCDJy m) hCDY
  -- ### the periodised components of the intermediate sections are smooth
  have hper_sm : ∀ (Z : Work.Diff.STE.Bil (I := I) (M := M)),
      Work.Diff.STE.D.ChartData (I := I) (M := M) Z →
      ContDiff ℝ (⊤ : ℕ∞) (D.Rper i Z a b) :=
    fun Z hZ => (Work.Diff.STE.Lead.Rper_contDiff_and_periodic (I := I) (M := M) D Z hZ i a b).1
  -- ### the pointwise coefficient bound
  have hbound : ∀ m : ℕ,
      ‖Work.Diff.STE.fourierCoeff (D.Rper i (D.J ρ (ε m) (X m)) a b) μ
        - Work.Diff.STE.fourierCoeff (D.Rper i Y a b) μ‖
      ≤ C₁ * (Real.sqrt C₀ * Real.sqrt (D.BNorm 0 (X m - Y)))
        + C₁ * Real.sqrt (D.BNorm 0 (D.J ρ (ε m) Y - Y)) := by
    intro m
    -- additivity of the mollifier in the section
    have hsymxy : Work.Diff.STE.D.IsSymm (I := I) (X m - Y) := IsSymm_sub (hsymX m) hsymY
    have hJadd : D.J ρ (ε m) (X m) = D.J ρ (ε m) (X m - Y) + D.J ρ (ε m) Y := by
      have hab : (X m - Y) + Y = X m := sub_add_cancel (X m) Y
      have h := J_add' D ρ (ε m) (hε m).1 hρ0 (X m - Y) Y (hCDxy m) hCDY hsymxy hsymY
      exact (congrArg (fun Z => D.J ρ (ε m) Z) hab).symm.trans h
    -- additivity of the coefficient functional in the section
    have h1 : Work.Diff.STE.fourierCoeff (D.Rper i (D.J ρ (ε m) (X m)) a b) μ
        = Work.Diff.STE.fourierCoeff (D.Rper i (D.J ρ (ε m) (X m - Y)) a b) μ
          + Work.Diff.STE.fourierCoeff (D.Rper i (D.J ρ (ε m) Y) a b) μ := by
      rw [hJadd]
      exact fourierCoeff_Rper_add' D (D.J ρ (ε m) (X m - Y)) (D.J ρ (ε m) Y) i a b μ
        (hper_sm _ (hCDJxy m)) (hper_sm _ (hCDJy m))
    have h2 : Work.Diff.STE.fourierCoeff (D.Rper i (D.J ρ (ε m) Y) a b) μ
        - Work.Diff.STE.fourierCoeff (D.Rper i Y a b) μ
        = Work.Diff.STE.fourierCoeff (D.Rper i (D.J ρ (ε m) Y - Y) a b) μ :=
      (Work.Diff.STE.B3Data.fourierCoeff_Rper_sub D (D.J ρ (ε m) Y) Y i a b μ
        (hper_sm _ (hCDJy m)) (hper_sm _ hCDY)).symm
    -- the two summands are bounded by the `H⁰` norms
    have hb1 : ‖Work.Diff.STE.fourierCoeff (D.Rper i (D.J ρ (ε m) (X m - Y)) a b) μ‖
        ≤ C₁ * (Real.sqrt C₀ * Real.sqrt (D.BNorm 0 (X m - Y))) := by
      have h := hC₁ (D.J ρ (ε m) (X m - Y)) (hCDJxy m) i a b μ
      have hJN0 := hC₀ (ε m) (hε m) (X m - Y) (hCDxy m)
      have hs : Real.sqrt (D.BNorm 0 (D.J ρ (ε m) (X m - Y)))
          ≤ Real.sqrt C₀ * Real.sqrt (D.BNorm 0 (X m - Y)) := by
        rw [← Real.sqrt_mul hC₀nn]
        exact Real.sqrt_le_sqrt hJN0
      calc ‖Work.Diff.STE.fourierCoeff (D.Rper i (D.J ρ (ε m) (X m - Y)) a b) μ‖
          ≤ C₁ * Real.sqrt (D.BNorm 0 (D.J ρ (ε m) (X m - Y))) := h
        _ ≤ C₁ * (Real.sqrt C₀ * Real.sqrt (D.BNorm 0 (X m - Y))) :=
            mul_le_mul_of_nonneg_left hs hC₁nn
    have hb2 : ‖Work.Diff.STE.fourierCoeff (D.Rper i (D.J ρ (ε m) Y - Y) a b) μ‖
        ≤ C₁ * Real.sqrt (D.BNorm 0 (D.J ρ (ε m) Y - Y)) :=
      hC₁ (D.J ρ (ε m) Y - Y) (hCDJyy m) i a b μ
    have hkey : Work.Diff.STE.fourierCoeff (D.Rper i (D.J ρ (ε m) (X m)) a b) μ
        - Work.Diff.STE.fourierCoeff (D.Rper i Y a b) μ
        = Work.Diff.STE.fourierCoeff (D.Rper i (D.J ρ (ε m) (X m - Y)) a b) μ
          + Work.Diff.STE.fourierCoeff (D.Rper i (D.J ρ (ε m) Y - Y) a b) μ := by
      rw [h1, ← h2]
      ring
    rw [hkey]
    exact (norm_add_le _ _).trans (add_le_add hb1 hb2)
  -- ### the majorant tends to `0`
  have hlimY : Filter.Tendsto (fun m : ℕ => Real.sqrt (D.BNorm 0 (X m - Y)))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun m : ℕ => Real.sqrt (D.BNorm 0 (X m - Y)))
        Filter.atTop (nhds (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto 0).comp hBN
    simpa using h1
  have hlim1 : Filter.Tendsto (fun m : ℕ =>
      C₁ * (Real.sqrt C₀ * Real.sqrt (D.BNorm 0 (X m - Y)))) Filter.atTop (nhds 0) := by
    have h2 : Filter.Tendsto (fun m : ℕ => Real.sqrt C₀ * Real.sqrt (D.BNorm 0 (X m - Y)))
        Filter.atTop (nhds 0) := by
      simpa using hlimY.const_mul (Real.sqrt C₀)
    simpa using h2.const_mul C₁
  have hlim2 : Filter.Tendsto (fun m : ℕ =>
      C₁ * Real.sqrt (D.BNorm 0 (D.J ρ (ε m) Y - Y))) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun m : ℕ => Real.sqrt (D.BNorm 0 (D.J ρ (ε m) Y - Y)))
        Filter.atTop (nhds 0) := by
      have h2 : Filter.Tendsto (fun m : ℕ => Real.sqrt (D.BNorm 0 (D.J ρ (ε m) Y - Y)))
          Filter.atTop (nhds (Real.sqrt 0)) :=
        (Real.continuous_sqrt.tendsto 0).comp hJTY
      simpa using h2
    simpa using h1.const_mul C₁
  have hlim : Filter.Tendsto (fun m : ℕ =>
      C₁ * (Real.sqrt C₀ * Real.sqrt (D.BNorm 0 (X m - Y)))
        + C₁ * Real.sqrt (D.BNorm 0 (D.J ρ (ε m) Y - Y))) Filter.atTop (nhds 0) := by
    simpa using hlim1.add hlim2
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero (fun m => norm_nonneg _) (fun m => hbound m) hlim)


theorem coeff_tendsto_galRHS
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless] [CompactSpace M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hLC : Submission.Diff.LCSmooth I M)
    (hJN : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
      ∀ h : Work.Diff.STE.Bil (I := I) (M := M),
      Work.Diff.STE.D.ChartData (I := I) (M := M) h → D.BNorm k (D.J ρ ε h) ≤ C * D.BNorm k h)
    (hJT : ∀ (k : ℕ) (h : Work.Diff.STE.Bil (I := I) (M := M)),
      Work.Diff.STE.D.ChartData (I := I) (M := M) h →
      Filter.Tendsto (fun ε => D.BNorm k (D.J ρ ε h - h))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (τ₀ : ℝ) (hτ₀ : 0 < τ₀) (B : ℕ → ℝ) (hB : ∀ k : ℕ, 0 ≤ B k)
    (lam K : ℝ) (hlam : 0 < lam) (hK : 0 < K)
    (ε : ℕ → ℝ) (hε : ∀ m : ℕ, ε m ∈ Set.Ioc (0 : ℝ) 1)
    (hε0 : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hs : ℕ → Work.Diff.STE.Bil (I := I) (M := M))
    (U : Work.Diff.STE.Bil (I := I) (M := M))
    (hsm : ∀ m : ℕ, Work.Diff.STE.D.ChartData (I := I) (M := M) (hs m))
    (hsmU : Work.Diff.STE.D.ChartData (I := I) (M := M) U)
    (hconv : ∀ k : ℕ, Filter.Tendsto (fun m : ℕ => D.BNorm k (hs m - U)) Filter.atTop (nhds 0))
    (hell : ∀ (m : ℕ) (x : M) (v : TangentSpace I x),
      lam * g₀.inner x v v ≤ (hs m) x v v)
    (hellU : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ U x v v)
    (hub : ∀ (m : ℕ) (x : M) (v : TangentSpace I x),
      (hs m) x v v ≤ K * g₀.inner x v v)
    (hubU : ∀ (x : M) (v : TangentSpace I x), U x v v ≤ K * g₀.inner x v v)
    (hsym : ∀ (m : ℕ) (x : M) (u v : TangentSpace I x), (hs m) x u v = (hs m) x v u)
    (hpos : ∀ (m : ℕ) (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < (hs m) x v v)
    (hsymU : ∀ (x : M) (u v : TangentSpace I x), U x u v = U x v u)
    (hposU : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < U x v v)
    (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ) :
    Filter.Tendsto (fun m : ℕ => Work.Diff.STE.fourierCoeff (D.Rper i (D.J ρ (ε m)
        (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ (hs m) (hsym m) (hpos m) (hsm m))) a b) μ)
      Filter.atTop (nhds (Work.Diff.STE.fourierCoeff (D.Rper i
        (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ U hsymU hposU hsmU) a b) μ)) := by
  classical
  -- the parameter `c` of the jet-level uniform convergence
  have hcard : 0 < Fintype.card ι₀ := Fintype.card_pos_iff.mpr ⟨i⟩
  have hsqrt : 0 < Real.sqrt (Fintype.card ι₀) := Real.sqrt_pos.mpr (by exact_mod_cast hcard)
  have hinv : 0 < (Real.sqrt (Fintype.card ι₀))⁻¹ := inv_pos.mpr hsqrt
  have hc1 : (Real.sqrt (Fintype.card ι₀))⁻¹ / 2 ≤ (Real.sqrt (Fintype.card ι₀))⁻¹ := by
    rw [div_le_iff₀ (by norm_num)]
    nlinarith [hinv]
  -- the jet-level uniform convergence of the DeTurck operator
  have hA := Work.Diff.STE.Lead.pPhiJetOf_uniform_v2 (I := I) (M := M) D hs U hsm hsmU hsymU hposU
    ((Real.sqrt (Fintype.card ι₀))⁻¹ / 2) (by positivity) hconv
  -- its consequence: `H⁰`-convergence of the DeTurck sections
  have hBN := Work.Diff.STE.Lead.deTurckSec_BNorm0_tendsto (I := I) (M := M) D hLC hs U
    hsym hpos hsm hsymU hposU hsmU ((Real.sqrt (Fintype.card ι₀))⁻¹ / 2)
    (by positivity) hc1 hA
  exact Work.Diff.STE.Lead.coeff_tendsto_galRHS_aux (I := I) (M := M) D ρ hρ hρ0 hJN hJT
    ε hε hε0
    (fun m => Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ (hs m) (hsym m) (hpos m) (hsm m))
    (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ U hsymU hposU hsmU)
    (fun m => Work.Diff.STE.B3.chartData_deTurckSec (I := I) (M := M) (g₀ := g₀) hLC
      (hs m) (hsym m) (hpos m) (hsm m))
    (Work.Diff.STE.B3.chartData_deTurckSec (I := I) (M := M) (g₀ := g₀) hLC
      U hsymU hposU hsmU)
    (fun m => Work.Diff.STE.D.isSymm_deTurckSec (I := I) (M := M) (ι₀ := ι₀) hLC
      (hs m) (hsym m) (hpos m) (hsm m))
    (Work.Diff.STE.D.isSymm_deTurckSec (I := I) (M := M) (ι₀ := ι₀) hLC U hsymU hposU hsmU)
    hBN i a b μ

end Work.Diff.STE.Lead
