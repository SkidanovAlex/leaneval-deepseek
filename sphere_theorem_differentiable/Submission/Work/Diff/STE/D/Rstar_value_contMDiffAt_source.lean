import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.Rstar_apply
import Submission.Work.Diff.STE.B3.densGood
import Submission.Work.Diff.STE.B3.dens_bound_sigma
import Submission.Work.Diff.EXT.ricCore
import Submission.Work.Diff.STE.contDiffOn_chartComp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer D: smoothness of the evaluation of a reconstruction `Rstar i u` on smooth fields

The reconstruction `D.Rstar i u` of a family of component functions is the section

`p ↦ ζ i p · Σ_{ab} u a b (coord i p) · eᵢa♭ ⊗ eᵢb♭`

(`Work.Diff.STE.B3Data.Rstar`, see `B3/Comp.lean`).  This file proves that its *evaluation* on two
smooth fields is smooth:

`Work.Diff.STE.D.Rstar_value_contMDiffAt_source`
  `ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (fun q ↦ D.Rstar i u q (X q) (Y q)) p₀`

for `p₀` in the chart source of `x₀ i` (the two remaining hypotheses of the statement, `hlt` and the
smoothness of `X`, `Y`, are not needed for this *smoothness* statement other than through `X`, `Y`;
in particular the conclusion is local).

**The reduction.**  `Work.Diff.STE.B3.Rstar_apply` evaluates the section at a point `q` as the
product of the scalar coefficient

`ζ i q · χ i (coord i q) · (√(dens i (coord i q)))⁻¹`

with the finite double sum

`Σ_{ab} u a b (coord i q) · ⟪X q, eᵢa q⟫ · ⟪Y q, eᵢb q⟫`.

Every factor is smooth at `p₀`:

* `coord i` is the composition of the chart `extChartAt I (x₀ i)` (smooth on its source, which
  contains `p₀`) with the affine identification `E ≃ ℝⁿ` (`contMDiffAt_coord_of_mem_source`);
* `ζ i` is globally smooth (`B3Data.hζsm`), `χ i` and `u a b` are `C^∞` on the model space
  (`B3Data.hχsm`, `hu`) and are composed with `coord i`;
* the density `dens i = √det (chartMatFun g₀ (x₀ i) (flatToE (x₀ i) ·))` is `C^∞` and positive at
  the flat coordinate of `p₀` because that flat coordinate lies in the chart target
  (`flatToE_coord` + `PartialEquiv.map_source`) and `Work.Diff.STE.B3.densGood` is proved;
  `√` and `(·)⁻¹` are smooth there (`Real.contDiffAt_sqrt`, `ContMDiffAt.inv₀`);
* the metric pairings `⟪X, eᵢa⟫` are smooth by `ContMDiffAt.inner_bundle`
  (`inner_contMDiffAt` below), from the smoothness of `X`, `Y`, of the fields `e i a`
  (`B3Data.hesm`) and of the metric.

The double sum is a finite sum of products, hence smooth (`ContMDiffAt.sum`), and so is the
product with the coefficient; the identification of this product with `D.Rstar i u q (X q) (Y q)`
is `Work.Diff.STE.B3.Rstar_apply`.
-/

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.Diff.STE.D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [I.Boundaryless] [T2Space M]

/-- **The flat coordinate is `C^∞` at every point of the chart source.**  `coord x₀` is the
composition of the extended chart at `x₀` (smooth on its source, which is open) with the affine
identification `E ≃ ℝⁿ` followed by the translation by the flat coordinate of the chart centre. -/
lemma contMDiffAt_coord_of_mem_source {x₀ : M} {p : M}
    (hp : p ∈ (extChartAt I x₀).source) :
    ContMDiffAt I 𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ) ∞
      (fun q : M => Work.Diff.STE.coord (I := I) x₀ q) p := by
  have hchart : ContMDiffAt I 𝓘(ℝ, E) ∞ (fun q : M => (extChartAt I x₀) q) p :=
    (contMDiffOn_extChartAt (I := I) (x := x₀) (n := ∞)).contMDiffAt
      (by
        rw [← extChartAt_source (I := I) x₀]
        exact (isOpen_extChartAt_source (I := I) x₀).mem_nhds hp)
  have haff : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ) ∞
      (fun w : E => (Module.finBasis ℝ E).equivFun w
        - (Module.finBasis ℝ E).equivFun ((extChartAt I x₀) x₀)) ((extChartAt I x₀) p) :=
    contMDiffAt_iff_contDiffAt.mpr
      ((((Module.finBasis ℝ E).equivFun.toContinuousLinearMap).contDiff).sub
        contDiff_const).contDiffAt
  refine (haff.comp p hchart).congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => ?_)
  simp only [Function.comp_def, Work.Diff.STE.coord_apply]

/-- **The metric pairing of two smooth fields is smooth at a point.**  The metric is a smooth
section of the bundle of bilinear forms, so evaluating it against two smooth fields is smooth by
`ContMDiffAt.inner_bundle` (the same argument as in
`Work.Diff.STE.B3.continuousAt_inner_of_cmdiff`, at level `∞`). -/
lemma inner_contMDiffAt {g : Submission.Diff.SMet I M} {p : M}
    {X Y : Π q : M, TangentSpace I q}
    (hX : Work.Diff.EXT.SmoothFieldAt I M X p)
    (hY : Work.Diff.EXT.SmoothFieldAt I M Y p) :
    ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ENat) : WithTop ENat)
      (fun q : M => g.inner q (X q) (Y q)) p := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  exact ContMDiffAt.inner_bundle (F := E) (E := fun x : M ↦ TangentSpace I x) (b := id) hX hY

theorem Rstar_value_contMDiffAt_source
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [I.Boundaryless] [T2Space M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hu : ∀ (a b : Fin (Module.finrank ℝ E)), ContDiff ℝ (⊤ : ℕ∞) (u a b))
    {p₀ : M} (hsrc : p₀ ∈ (extChartAt I (D.x₀ i)).source)
    (hlt : ‖Work.Diff.STE.coord (I := I) (D.x₀ i) p₀‖ < 2 * D.σ i)
    {X Y : Π q : M, TangentSpace I q}
    (hX : Work.Diff.EXT.SmoothFieldAt I M X p₀)
    (hY : Work.Diff.EXT.SmoothFieldAt I M Y p₀) :
    ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ENat) : WithTop ENat)
      (fun q : M => D.Rstar i u q (X q) (Y q)) p₀ := by
  -- Step 1: the flat coordinate of the chart `i` is smooth at `p₀`.
  have hcoord : ContMDiffAt I 𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ) ∞
      (fun q : M => Work.Diff.STE.coord (I := I) (D.x₀ i) q) p₀ :=
    contMDiffAt_coord_of_mem_source hsrc
  -- Step 2: the flat coordinate of `p₀` lies in the chart target of `x₀ i`, so the volume density
  -- is smooth (and positive) there.
  have htgt : Work.Diff.STE.flatToE (I := I) (D.x₀ i)
      (Work.Diff.STE.coord (I := I) (D.x₀ i) p₀)
      ∈ (extChartAt I (D.x₀ i)).target := by
    -- `flatToE (coord p₀) = extChartAt (x₀ i) p₀`, which lies in the chart target.
    have hcancel : (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) (D.x₀ i))
        + ((Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) p₀)
            - (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) (D.x₀ i)))
        = (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) p₀) := by abel
    have hfe : Work.Diff.STE.flatToE (I := I) (D.x₀ i)
        (Work.Diff.STE.coord (I := I) (D.x₀ i) p₀) = (extChartAt I (D.x₀ i)) p₀ := by
      simp only [Work.Diff.STE.flatToE_apply, Work.Diff.STE.coord_apply]
      rw [hcancel, LinearEquiv.symm_apply_apply]
    rw [hfe]
    exact PartialEquiv.map_source (extChartAt I (D.x₀ i)) hsrc
  have hdat := Work.Diff.STE.B3.densGood D i
    (Work.Diff.STE.coord (I := I) (D.x₀ i) p₀) htgt
  have hdens : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun q : M => D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) q)) p₀ :=
    (contMDiffAt_iff_contDiffAt.mpr hdat.2).comp p₀ hcoord
  -- Step 3: the square root of the density and its inverse are smooth at `p₀`.
  have hsqrt : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun q : M => Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) q))) p₀ :=
    (contMDiffAt_iff_contDiffAt.mpr (Real.contDiffAt_sqrt (ne_of_gt hdat.1))).comp p₀ hdens
  have hinv : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun q : M =>
        (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) q)))⁻¹) p₀ :=
    hsqrt.inv₀ (Real.sqrt_pos.mpr hdat.1).ne'
  -- Step 4: the cut-off `χ i ∘ coord i`, the weight `ζ i` and the coefficient are smooth.
  have hζ : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun q : M => D.ζ i q) p₀ := (D.hζsm i).contMDiffAt
  have hχ : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun q : M => D.χ i (Work.Diff.STE.coord (I := I) (D.x₀ i) q)) p₀ :=
    (contMDiffAt_iff_contDiffAt.mpr ((D.hχsm i).contDiffAt)).comp p₀ hcoord
  have hcoeff : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun q : M => D.ζ i q * D.χ i (Work.Diff.STE.coord (I := I) (D.x₀ i) q)
        * (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) q)))⁻¹) p₀ :=
    (hζ.mul hχ).mul hinv
  -- Step 5: the entries of the double sum: the component functions `u a b ∘ coord i` and the two
  -- metric pairings with the frame fields `e i a`, `e i b`.
  have hu' : ∀ a b : Fin (Module.finrank ℝ E), ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun q : M => u a b (Work.Diff.STE.coord (I := I) (D.x₀ i) q)) p₀ := fun a b =>
    (contMDiffAt_iff_contDiffAt.mpr ((hu a b).contDiffAt)).comp p₀ hcoord
  have hXe : ∀ a : Fin (Module.finrank ℝ E), ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun q : M => g₀.inner q (X q) (D.e i a q)) p₀ := fun a =>
    inner_contMDiffAt (g := g₀) hX ((D.hesm i a).contMDiffAt)
  have hYe : ∀ b : Fin (Module.finrank ℝ E), ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun q : M => g₀.inner q (Y q) (D.e i b q)) p₀ := fun b =>
    inner_contMDiffAt (g := g₀) hY ((D.hesm i b).contMDiffAt)
  have hterm : ∀ a b : Fin (Module.finrank ℝ E), ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun q : M => u a b (Work.Diff.STE.coord (I := I) (D.x₀ i) q)
        * g₀.inner q (X q) (D.e i a q) * g₀.inner q (Y q) (D.e i b q)) p₀ := fun a b =>
    ((hu' a b).mul (hXe a)).mul (hYe b)
  have hsum : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun q : M => ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        u a b (Work.Diff.STE.coord (I := I) (D.x₀ i) q)
          * g₀.inner q (X q) (D.e i a q) * g₀.inner q (Y q) (D.e i b q)) p₀ := by
    refine ContMDiffAt.sum (t := Finset.univ)
      (f := fun a q => ∑ b : Fin (Module.finrank ℝ E),
        u a b (Work.Diff.STE.coord (I := I) (D.x₀ i) q)
          * g₀.inner q (X q) (D.e i a q) * g₀.inner q (Y q) (D.e i b q)) (fun a _ => ?_)
    exact ContMDiffAt.sum (t := Finset.univ) (fun b _ => hterm a b)
  -- Step 6: the coefficient times the double sum is smooth, and it *is* the evaluation of the
  -- reconstruction (`Rstar_apply`).
  have hmain : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun q : M => D.ζ i q * D.χ i (Work.Diff.STE.coord (I := I) (D.x₀ i) q)
          * (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) q)))⁻¹
          * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              u a b (Work.Diff.STE.coord (I := I) (D.x₀ i) q)
                * g₀.inner q (X q) (D.e i a q) * g₀.inner q (Y q) (D.e i b q))) p₀ :=
    hcoeff.mul hsum
  refine hmain.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => ?_)
  exact Work.Diff.STE.B3.Rstar_apply D i u q (X q) (Y q)

end Work.Diff.STE.D
