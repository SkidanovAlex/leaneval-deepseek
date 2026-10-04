import Mathlib
import Submission.Work.Diff.STE.B3.BPairDefs
import Submission.Work.Diff.STE.B3.Rstar_apply
import Submission.Work.Diff.STE.B3.dens_bound_sigma

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3: continuity of the chart matrix of the reconstruction `Rstar i u`

The reconstruction `D.Rstar i u` of a family of component functions `u` is the section

`p ↦ ζ i p · Σ_{ab} u a b (coord i p) · eᵢa♭ ⊗ eᵢb♭`,

whose chart matrix in the chart `j` is `z ↦ D.mat j (Rstar i u) a b z`.  This file proves that it
is continuous at every point of the *genuine* set `‖z‖ < σ j ∧ ζ i (pt j z) ≠ 0`; this is the
continuity input used by `Work.Diff.STE.B3.integrableOn_Rpair_term`.

**The reduction.**  Write `p₀ := D.pt j z`.  Since `D.ζ i p₀ ≠ 0`, the point `p₀` lies in the chart
source of `x₀ i` and its flat coordinate there has norm `< σ i` (`D.hζsupp`).  Hence, near `p₀`,
* all the maps `p ↦ coord i p`, `p ↦ χ i (coord i p)`, `p ↦ dens i (coord i p)` and
  `p ↦ u a b (coord i p)` are continuous (the flat coordinate is continuous on the chart source,
  the cut-off is smooth everywhere, the density is continuous at every point of the chart *target*
  and the flat coordinate of `p₀` lies in that target, and `u a b` is continuous by hypothesis);
* the metric pairings `p ↦ g₀.inner p (e j a p) (e i c p)` are continuous because both fields are
  smooth sections and the metric is smooth (`ContMDiffAt.inner_bundle`).

Evaluating `Rstar` with `Rstar_apply` turns `p ↦ Rstar i u p (e j a p) (e j b p)` into a product of
those continuous functions (the coefficient `ζ i p · χ i (coord i p) · (√(dens i (coord i p)))⁻¹`
times the double sum over `c, d`), hence it is continuous at `p₀`; composing with the continuous
parametrisation `z ↦ pt j z` (the chart inverse, continuous on the chart target, which contains
the `2σ j`-ball) gives the claim.

The proof avoids the junk values of the partial charts exactly as `B3/BPairDefs.lean` does: the
`ζ i` factor localises everything to the chart-`i` source.
-/

noncomputable section

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.B3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-! ### Two elementary generalities -/

/-- **The affine flat coordinates are inverse to `flatToE`.**  For every point `p`, the `flatToE`
image of the flat coordinate of `p` in the chart at `x₀` is the chart image of `p` — no hypothesis
on `p` is needed, this is a pure computation in the affine identification. -/
lemma flatToE_coord_cm (x₀ p : M) :
    flatToE (I := I) x₀ (coord (I := I) x₀ p) = (extChartAt I x₀) p := by
  have hcancel : (Module.finBasis ℝ E).equivFun ((extChartAt I x₀) x₀)
      + ((Module.finBasis ℝ E).equivFun ((extChartAt I x₀) p)
          - (Module.finBasis ℝ E).equivFun ((extChartAt I x₀) x₀))
      = (Module.finBasis ℝ E).equivFun ((extChartAt I x₀) p) := by abel
  simp only [flatToE_apply, coord_apply]
  rw [hcancel, LinearEquiv.symm_apply_apply]

/-- **The flat coordinate is continuous at every point of the chart source.**  On the (open) chart
source the extended chart is smooth by `contMDiffOn_extChartAt`, and `coord` is the composition of
the chart, the linear identification `E ≃ ℝⁿ` and a translation. -/
lemma continuousAt_coord_of_mem_source {x₀ : M} {p : M}
    (hp : p ∈ (extChartAt I x₀).source) :
    ContinuousAt (fun q : M => coord (I := I) x₀ q) p := by
  have hsrc : (chartAt H x₀).source ∈ 𝓝 p := by
    rw [← extChartAt_source (I := I) x₀]
    exact (isOpen_extChartAt_source (I := I) x₀).mem_nhds hp
  have h1 : ContinuousAt (fun q : M => (extChartAt I x₀) q) p :=
    ((contMDiffOn_extChartAt (I := I) (x := x₀)
      (n := ((⊤ : ENat) : WithTop ENat))).contMDiffAt hsrc).continuousAt
  have h2 : ContinuousAt (fun q : M =>
      (Module.finBasis ℝ E).equivFun ((extChartAt I x₀) q)) p :=
    (((Module.finBasis ℝ E).equivFun : E →ₗ[ℝ] (Fin (Module.finrank ℝ E) → ℝ))
      |>.toContinuousLinearMap).continuous.continuousAt.comp h1
  have h3 : ContinuousAt (fun q : M => (Module.finBasis ℝ E).equivFun ((extChartAt I x₀) q)
      - (Module.finBasis ℝ E).equivFun ((extChartAt I x₀) x₀)) p :=
    h2.sub continuousAt_const
  simpa only [coord_apply] using h3

/-- **The metric pairing of two smooth fields is continuous.**  The metric is a smooth section of
the bundle of bilinear forms, so evaluating it against the two smooth fields is smooth by the
bundle bilinear-application lemma — the same argument as in
`Work.Diff.STE.contMDiffOn_metricComp`. -/
lemma continuousAt_inner_of_cmdiff {g : SMet I M} {p : M}
    {X Y : Π q : M, TangentSpace I q}
    (hX : CMDiffAt ∞ (T% X) p) (hY : CMDiffAt ∞ (T% Y) p) :
    ContinuousAt (fun q : M => g.inner q (X q) (Y q)) p := by
  have hψ : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun m : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) m
        (g.inner m)) p :=
    g.contMDiff p
  have hmain : ContMDiffWithinAt I (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun m : M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) m
        (g.inner m (X m) (Y m))) univ p :=
    ContMDiffWithinAt.clm_bundle_apply₂ (𝕜 := ℝ) (B := M) (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (E₁ := fun x : M => TangentSpace I x) (E₂ := fun x : M => TangentSpace I x)
      (E₃ := Bundle.Trivial M ℝ) (b := fun m : M => m)
      (v := X) (w := Y) (ψ := fun m : M => g.inner m)
      (s := univ) (x := p) hψ hX hY
  have hsec : ContMDiffWithinAt I 𝓘(ℝ, ℝ) ∞
      (fun m : M => g.inner m (X m) (Y m)) univ p := by
    have := (contMDiffWithinAt_section (IB := I) (F := ℝ) (E := Bundle.Trivial M ℝ)
      (s := fun m : M => g.inner m (X m) (Y m)) (a := univ) (x₀ := p) (n := ∞)).mp hmain
    simpa using this
  exact (continuousWithinAt_univ _ _).1 hsec.continuousWithinAt

/-! ### The target -/

theorem continuousAt_mat_Rstar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hu : ∀ a b : Fin (Module.finrank ℝ E), Continuous (u a b))
    (a b : Fin (Module.finrank ℝ E))
    {z : Fin (Module.finrank ℝ E) → ℝ} (hz : ‖z‖ < D.σ j)
    (hζ : D.ζ i (D.pt j z) ≠ 0) :
    ContinuousAt (fun z => D.mat j (D.Rstar i u) a b z) z := by
  classical
  -- the base point of `M` and the genuine chart-`i` information it carries
  set p₀ : M := D.pt j z with hp₀
  have hζ₀ : D.ζ i p₀ ≠ 0 := by rw [hp₀]; exact hζ
  have hsrc_i : p₀ ∈ (extChartAt I (D.x₀ i)).source := (D.hζsupp i p₀ hζ₀).1
  -- `pt j` is continuous at `z` (the chart `j` is genuine on the `2σ j`-ball)
  have hz2 : ‖z‖ ≤ 2 * D.σ j := by have := D.hσ j; linarith
  have hflat : ContinuousAt (fun w : Fin (Module.finrank ℝ E) → ℝ =>
      flatToE (I := I) (D.x₀ j) w) z :=
    (flatToE_contDiff (I := I) (M := M) (D.x₀ j)).continuous.continuousAt
  have hpt : ContinuousAt (fun w : Fin (Module.finrank ℝ E) → ℝ => D.pt j w) z := by
    have h := (continuousAt_extChartAt_symm'' (I := I) (D.htarget j z hz2)).comp hflat
    simpa only [B3Data.pt, Function.comp_def] using h
  -- the flat coordinate of `p₀` and the continuity of the coefficient functions there
  have hcoord : ContinuousAt (fun p : M => coord (I := I) (D.x₀ i) p) p₀ :=
    continuousAt_coord_of_mem_source hsrc_i
  have htgt : flatToE (I := I) (D.x₀ i) (coord (I := I) (D.x₀ i) p₀)
      ∈ (extChartAt I (D.x₀ i)).target := by
    rw [flatToE_coord_cm]
    exact PartialEquiv.map_source (extChartAt I (D.x₀ i)) hsrc_i
  have hdens : ContinuousAt (fun p : M => D.dens i (coord (I := I) (D.x₀ i) p)) p₀ :=
    (dens_continuousAt_of_mem_target D i htgt).comp hcoord
  have hsqrt : ContinuousAt
      (fun p : M => Real.sqrt (D.dens i (coord (I := I) (D.x₀ i) p))) p₀ :=
    Real.continuous_sqrt.continuousAt.comp hdens
  have hsqrtne : Real.sqrt (D.dens i (coord (I := I) (D.x₀ i) p₀)) ≠ 0 :=
    (Real.sqrt_pos.mpr (dens_pos_of_mem_target D i htgt)).ne'
  have hinv : ContinuousAt
      (fun p : M => (Real.sqrt (D.dens i (coord (I := I) (D.x₀ i) p)))⁻¹) p₀ :=
    ContinuousAt.inv₀ hsqrt hsqrtne
  have hzeta : ContinuousAt (fun p : M => D.ζ i p) p₀ :=
    (D.hζsm i).continuous.continuousAt
  have hchi : ContinuousAt (fun p : M => D.χ i (coord (I := I) (D.x₀ i) p)) p₀ :=
    ((D.hχsm i).continuous.continuousAt).comp hcoord
  have hcoeff : ContinuousAt (fun p : M => D.ζ i p * D.χ i (coord (I := I) (D.x₀ i) p)
      * (Real.sqrt (D.dens i (coord (I := I) (D.x₀ i) p)))⁻¹) p₀ :=
    (hzeta.mul hchi).mul hinv
  -- the coefficient family and the metric pairings inside the double sum
  have hucd : ∀ c d : Fin (Module.finrank ℝ E),
      ContinuousAt (fun p : M => u c d (coord (I := I) (D.x₀ i) p)) p₀ :=
    fun c d => (hu c d).continuousAt.comp hcoord
  have hinc₁ : ∀ c d : Fin (Module.finrank ℝ E),
      ContinuousAt (fun p : M => g₀.inner p (D.e j a p) (D.e i c p)) p₀ :=
    fun c d => continuousAt_inner_of_cmdiff ((D.hesm j a).contMDiffAt)
      ((D.hesm i c).contMDiffAt)
  have hinc₂ : ∀ c d : Fin (Module.finrank ℝ E),
      ContinuousAt (fun p : M => g₀.inner p (D.e j b p) (D.e i d p)) p₀ :=
    fun c d => continuousAt_inner_of_cmdiff ((D.hesm j b).contMDiffAt)
      ((D.hesm i d).contMDiffAt)
  -- the double sum is continuous at `p₀`
  have hterm : ContinuousAt (fun p : M => fun c d : Fin (Module.finrank ℝ E) =>
      u c d (coord (I := I) (D.x₀ i) p) * g₀.inner p (D.e j a p) (D.e i c p)
        * g₀.inner p (D.e j b p) (D.e i d p)) p₀ := by
    rw [continuousAt_pi]
    intro c
    rw [continuousAt_pi]
    intro d
    exact ((hucd c d).mul (hinc₁ c d)).mul (hinc₂ c d)
  have hsumlin : Continuous (fun v : Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ => ∑ c, ∑ d, v c d) := by
    refine continuous_finsetSum Finset.univ (fun c _ => ?_)
    refine continuous_finsetSum Finset.univ (fun d _ => ?_)
    exact (continuous_apply d).comp (continuous_apply c)
  have hsum : ContinuousAt (fun p : M => ∑ c : Fin (Module.finrank ℝ E),
        ∑ d : Fin (Module.finrank ℝ E),
          u c d (coord (I := I) (D.x₀ i) p) * g₀.inner p (D.e j a p) (D.e i c p)
            * g₀.inner p (D.e j b p) (D.e i d p)) p₀ := by
    simpa only [Function.comp_def] using hsumlin.continuousAt.comp hterm
  -- hence the chart matrix of the reconstruction, read as a function on `M`, is continuous at `p₀`
  have hG : ContinuousAt (fun p : M => D.Rstar i u p (D.e j a p) (D.e j b p)) p₀ := by
    have heq : (fun p : M => D.Rstar i u p (D.e j a p) (D.e j b p))
        = fun p : M => D.ζ i p * D.χ i (coord (I := I) (D.x₀ i) p)
            * (Real.sqrt (D.dens i (coord (I := I) (D.x₀ i) p)))⁻¹
            * (∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
                u c d (coord (I := I) (D.x₀ i) p)
                  * g₀.inner p (D.e j a p) (D.e i c p)
                  * g₀.inner p (D.e j b p) (D.e i d p)) := by
      funext p
      exact Rstar_apply D i u p (D.e j a p) (D.e j b p)
    rw [heq]
    exact hcoeff.mul hsum
  -- compose with the parametrisation `z ↦ pt j z`
  have hcomp : ContinuousAt ((fun p : M => D.Rstar i u p (D.e j a p) (D.e j b p))
      ∘ fun w : Fin (Module.finrank ℝ E) → ℝ => D.pt j w) z :=
    ContinuousAt.comp (x := z) (f := fun w : Fin (Module.finrank ℝ E) → ℝ => D.pt j w)
      hG hpt
  refine hcomp.congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [Function.comp_def, B3Data.mat]

end Work.Diff.STE.B3
