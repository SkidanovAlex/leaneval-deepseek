import Mathlib
import Submission.Work.Diff.STE.Lead.aemeasurable_uncurry_R_vs
import Submission.Work.Diff.STE.B3.fourierCoeff_periodization
import Submission.Work.Diff.STE.Lead.CoeffRepr

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Almost-everywhere measurability of the Fourier coefficients of the velocity components

`Work.Diff.STE.Lead.fourierCoeff_vs_aemeasurable` is the measurability input of the final
`ε → 0`-argument of Layer B3: the coefficient functional

  `σ ↦ fourierCoeff (D.Rper i (vs σ) a b) μ`

is `AEMeasurable` for the Lebesgue measure restricted to `[0, τ]`, as soon as `vs σ` is the
one-sided `σ`-derivative of the section family `u` on `[0, τ]` (hypothesis `hode`).

## Route

Two facts are combined, and neither of them needs any integrability or bound on `vs`:

* `Work.Diff.STE.Lead.fourierCoeff_Rper_eq_sum_integral` (`CoeffRepr.lean`) writes the coefficient
  **for an arbitrary section** `h` as an integral over the unit cube of the *explicit finite* sum
  `∑_{m ∈ cubeIdx} R i h a b (· + m)` — the periodisation collapses on the unit cube because the
  localised component is supported in the open centred cube.
* `Work.Diff.STE.Lead.aemeasurable_uncurry_R_vs`-style joint measurability: for each fixed shift
  `m` the function `(σ, z) ↦ D.R i (vs σ) a b (z + m)` is `AEMeasurable` for the product of the
  restricted Lebesgue measure on `[0, τ]` with the restricted Lebesgue measure on the unit cube.
  This is `aemeasurable_uncurry_of_hasDerivWithinAt_aux` applied to the *clamped* family
  `σ ↦ D.R i (u (min (max σ 0) τ)) a b (· + m)`, whose joint measurability is Carathéodory's
  lemma (`caratheodory_measurable_aux`: continuity in `σ` from `hode`, measurability in `z` from
  the chart smoothness `hCDu`), and whose `σ`-derivative on `[0, τ]` is the corresponding
  component of `vs` (`hode`, plus linearity of `R` in the section).

Fubini for the parameter integral (`MeasureTheory.AEStronglyMeasurable.integral_prod_right'`)
then makes the integral in `z` — hence, by the first point, the coefficient itself —
a.e. measurable.

Crucially, the two integrals are compared **pointwise** in `σ` (`integral_congr` inside
`fourierCoeff_Rper_eq_sum_integral`), so no `Integrable` hypothesis on the sections `vs σ` is
needed anywhere.
-/

noncomputable section

open MeasureTheory BigOperators

namespace Work.Diff.STE.Lead

theorem fourierCoeff_vs_aemeasurable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) {τ : ℝ} (hτ : 0 < τ)
    (u vs : ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (hCDu : ∀ t : ℝ, Work.Diff.STE.D.ChartData (I := I) (M := M) (u t))
    (hode : ∀ t ∈ Set.Icc (0 : ℝ) τ, ∀ (x : M) (u₀ v : TangentSpace I x),
      HasDerivWithinAt (fun s : ℝ => u s x u₀ v) (vs t x u₀ v) (Set.Icc (0 : ℝ) τ) t)
    (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ) :
    AEMeasurable (fun σ : ℝ => Work.Diff.STE.fourierCoeff (D.Rper i (vs σ) a b) μ)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Icc (0 : ℝ) τ)) := by
  -- notation
  let Z : Type := Fin (Module.finrank ℝ E) → ℝ
  let ν : MeasureTheory.Measure Z :=
    (MeasureTheory.volume : MeasureTheory.Measure Z).restrict
      (Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)))
  let μσ : MeasureTheory.Measure ℝ :=
    (MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Icc (0 : ℝ) τ)
  -- ## Step 1: joint measurability of the clamped family `σ ↦ D.R i (u (clamp σ)) a b z`
  have hG0 : Measurable (fun p : ℝ × Z =>
      D.R i (u (min (max p.1 0) τ)) a b p.2) := by
    refine caratheodory_measurable_aux
      (f := fun σ z => D.R i (u (min (max σ 0) τ)) a b z) ?_ ?_
    · intro z
      have hwu : ContinuousOn
          (fun t : ℝ => u t (D.pt i z) (D.e i a (D.pt i z)) (D.e i b (D.pt i z)))
          (Set.Icc (0 : ℝ) τ) :=
        fun t ht => (hode t ht (D.pt i z) (D.e i a (D.pt i z))
          (D.e i b (D.pt i z))).continuousWithinAt
      have hcm : Continuous (fun σ : ℝ => min (max σ 0) τ) :=
        (continuous_id.max continuous_const).min continuous_const
      have hmap : ∀ σ : ℝ, min (max σ 0) τ ∈ Set.Icc (0 : ℝ) τ :=
        fun σ => ⟨le_min (le_max_right _ _) hτ.le, min_le_right _ _⟩
      have hcomp := hwu.comp_continuous hcm hmap
      have h2 := hcomp.const_mul (D.psi i z * Real.sqrt (D.dens i z))
      simpa only [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat,
        Function.comp_apply, mul_assoc] using h2
    · intro σ
      exact (Work.Diff.STE.B3.R_contDiff_of_chartData D (u (min (max σ 0) τ))
        (hCDu (min (max σ 0) τ)) i a b).continuous.measurable
  -- ## Step 2: joint measurability of `(σ, z) ↦ D.R i (vs σ) a b (z + m)` for every shift `m`
  have hshift : ∀ m : Fin (Module.finrank ℝ E) → ℤ,
      AEMeasurable (fun p : ℝ × Z =>
        ((D.R i (vs p.1) a b (p.2 + Work.Diff.STE.iVec m) : ℝ) : ℂ)) (μσ.prod ν) := by
    intro m
    have hT : Measurable (fun p : ℝ × Z => (p.1, p.2 + Work.Diff.STE.iVec m)) :=
      Measurable.prod (f := fun p : ℝ × Z => (p.1, p.2 + Work.Diff.STE.iVec m))
        measurable_fst (measurable_snd.add_const (Work.Diff.STE.iVec m))
    have hGm : Measurable (fun p : ℝ × Z =>
        D.R i (u (min (max p.1 0) τ)) a b (p.2 + Work.Diff.STE.iVec m)) :=
      hG0.comp hT
    have hdm : ∀ s ∈ Set.Ioo (0 : ℝ) τ, ∀ z : Z,
        HasDerivWithinAt
          (fun σ : ℝ => D.R i (u (min (max σ 0) τ)) a b (z + Work.Diff.STE.iVec m))
          (D.R i (vs s) a b (z + Work.Diff.STE.iVec m)) (Set.Icc (0 : ℝ) τ) s := by
      intro s hs z
      have hs' : s ∈ Set.Icc (0 : ℝ) τ := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
      have h1 : HasDerivWithinAt (fun σ : ℝ => D.R i (u σ) a b (z + Work.Diff.STE.iVec m))
          (D.R i (vs s) a b (z + Work.Diff.STE.iVec m)) (Set.Icc (0 : ℝ) τ) s := by
        have h0 := hode s hs' (D.pt i (z + Work.Diff.STE.iVec m))
          (D.e i a (D.pt i (z + Work.Diff.STE.iVec m)))
          (D.e i b (D.pt i (z + Work.Diff.STE.iVec m)))
        have h2 := h0.const_mul
          (D.psi i (z + Work.Diff.STE.iVec m) * Real.sqrt (D.dens i (z + Work.Diff.STE.iVec m)))
        simpa only [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat] using h2
      -- on `Icc 0 τ` the clamp is the identity
      refine h1.congr ?_ ?_
      · intro σ hσ
        simp only [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat]
        rw [max_eq_left hσ.1, min_eq_left hσ.2]
      · simp only [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat]
        rw [max_eq_left hs'.1, min_eq_left hs'.2]
    obtain ⟨g, hg, hfg⟩ := aemeasurable_uncurry_of_hasDerivWithinAt_aux
      (Z := Z) (μ := ν) (a := 0) (b := τ)
      (G := fun p : ℝ × Z => D.R i (u (min (max p.1 0) τ)) a b (p.2 + Work.Diff.STE.iVec m))
      (F := fun s z => D.R i (vs s) a b (z + Work.Diff.STE.iVec m)) hGm hdm
    refine ⟨fun p => ((g p : ℝ) : ℂ), Complex.measurable_ofReal.comp hg, ?_⟩
    filter_upwards [hfg] with p hp
    show ((D.R i (vs p.1) a b (p.2 + Work.Diff.STE.iVec m) : ℝ) : ℂ) = _
    rw [hp]
  -- ## Step 3: joint measurability of the integrand of the finite-sum representation
  have hΦ : AEMeasurable (fun p : ℝ × Z =>
      Work.Diff.STE.fourierExp (-μ) p.2 *
        ∑ m ∈ cubeIdx E, ((D.R i (vs p.1) a b (p.2 + Work.Diff.STE.iVec m) : ℝ) : ℂ))
      (μσ.prod ν) := by
    refine AEMeasurable.mul ?_ ?_
    · exact ((Work.Diff.STE.continuous_fourierExp (-μ)).measurable.comp measurable_snd).aemeasurable
    · have hsumEq : (∑ m ∈ cubeIdx E, fun p : ℝ × Z =>
          ((D.R i (vs p.1) a b (p.2 + Work.Diff.STE.iVec m) : ℝ) : ℂ))
          = fun p : ℝ × Z => ∑ m ∈ cubeIdx E,
              ((D.R i (vs p.1) a b (p.2 + Work.Diff.STE.iVec m) : ℝ) : ℂ) := by
        funext p
        rw [Finset.sum_apply]
      have hsum : AEMeasurable (∑ m ∈ cubeIdx E, fun p : ℝ × Z =>
          ((D.R i (vs p.1) a b (p.2 + Work.Diff.STE.iVec m) : ℝ) : ℂ)) (μσ.prod ν) :=
        Finset.aemeasurable_sum (cubeIdx E) (fun m _ => hshift m)
      rwa [hsumEq] at hsum
  -- ## Step 4: Fubini — the parameter integral is a.e. measurable
  have hB : AEMeasurable (fun σ : ℝ => ∫ z, Work.Diff.STE.fourierExp (-μ) z *
      ∑ m ∈ cubeIdx E, ((D.R i (vs σ) a b (z + Work.Diff.STE.iVec m) : ℝ) : ℂ)
        ∂((MeasureTheory.volume : MeasureTheory.Measure Z).restrict
          (Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E))))) μσ :=
    (hΦ.aestronglyMeasurable.integral_prod_right').aemeasurable
  -- ## Step 5: identify the parameter integral with the coefficient, pointwise in `σ`
  refine hB.congr ?_
  filter_upwards with σ
  have h := fourierCoeff_Rper_eq_sum_integral (I := I) (M := M) D (vs σ) i a b μ
  simpa only [Work.Diff.STE.fourierCoeff] using h.symm

end Work.Diff.STE.Lead
