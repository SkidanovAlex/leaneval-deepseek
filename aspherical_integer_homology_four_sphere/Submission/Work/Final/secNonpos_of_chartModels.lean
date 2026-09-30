/-
# `sec ≤ 0` at a point, from the chart models of the metric

The curvature bridge of the project: the *pointwise* form of the bridge that turns the model
computations of `Work.Curvature` (the three coordinate models of the metric on `M̂`, each with
non-positive sectional curvature) into the intrinsic statement

`⟪R(u,v)v, u⟫ ≤ 0` for an orthonormal pair `u`, `v` at a point `x₀`,

for the (smooth, torsion-free, metric-compatible) connection `C.cov` of the framework.

The input is exactly the hypothesis produced by the `Space` area
(`Work.Space.ModelAtlas.chartGram_is_model`): a model metric field `G` which agrees with the chart
metric `chartGram x₀` near the chart image of `x₀`, and which has non-positive sectional curvature
at that point (`Work.Curvature.SecNonposAt`).

## The proof

Write `q₀ = extChartAt I4 x₀ x₀` and `σ` for the coordinate frame of the chart at `x₀`.

1. Given `u`, `v` in the tangent space at `x₀`, write them as frame vectors, `u = σ α`,
   `v = σ β` (`frameVector_coordFun_eq`).
2. `Submission.ChartCurv.curvVec_eq_chart` computes the curvature in chart coordinates:
   `R(σ α, σ β) σ β = σ (dB α β β − dB β β α + B(B(β,β),α) − B(B(β,α),β))`.
3. The Koszul identity in charts (`Work.LeviCivita.chartGram_chrB_eq_koszul`) together with the
   change of variables `Work.Curvature.chartDg_eq_dG` identifies the chart Christoffel symbol with
   the model one: `chartBridge_chrB_eq_koszulChr_of_model`, `B(q;a,b) = koszulChr G (extChartAt I4 x₀ q) a b`
   for every `q` of the chart.  The positivity and linearity needed by
   `Work.Curvature.koszulChr_eq_of_forall` are transported from the chart metric (which is
   positive definite) along `chartGram = G`.
4. Upgrading step 3 to derivatives gives `chartBridge_dB_eq_dBmodel`:
   `dB q d a b = dBmodel G q d a b`.  The content is the *eventual* equality
   `chartBridge_chrRep_eventuallyEq_koszulChr` (the chart representative of `B` is the model Christoffel
   symbol near `q₀`) together with the chart formula for `mvfderiv`
   (`Submission.ChartCurvCont.mvfderiv_frameVector_eq_fderiv`).
5. Evaluating the inner product with `chartGram_apply` and replacing `chartGram x₀ x₀` by `G q₀`
   turns the curvature numerator into `G q₀ (modelCurv G q₀ α β β) α`, which is `≤ 0` by
   `hsec`.
-/
import Mathlib
import Submission.Work.Final.Framework
import Submission.Work.RiemLib.ChartCurvCont

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Final

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace Work.Space.E4 M]
  [ChartedRiem M] [C : ChartedRiemConn M]

/-- The chart metric is linear in its first slot (difference form). -/
lemma chartBridge_chartGram_sub_fst (x₀ p : M) (a b c : Work.Space.E4) :
    Submission.ChartConnection.chartGram (I := Work.Space.I4) x₀ p (a - b) c
      = Submission.ChartConnection.chartGram (I := Work.Space.I4) x₀ p a c
        - Submission.ChartConnection.chartGram (I := Work.Space.I4) x₀ p b c := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ b,
    Submission.ChartConnection.chartGram_add_fst,
    Submission.ChartConnection.chartGram_smul_fst]
  ring

/-- The chart Christoffel symbol `q ↦ B q a b` is differentiable at every point of the chart
(it is a finite linear combination of the smooth Christoffel entries `gammaEntry`). -/
theorem chartBridge_mdifferentiableAt_chrB (x₀ : M) {p : M}
    (hp : p ∈ (chartAt Work.Space.E4 x₀).source) (a b : Work.Space.E4) :
    MDifferentiableAt Work.Space.I4 𝓘(ℝ, Work.Space.E4)
      (fun q : M => Submission.ChartCurv.chrB C.cov x₀ q a b) p := by
  classical
  have hsrc : ∀ᶠ q in nhds p, q ∈ (chartAt Work.Space.E4 x₀).source :=
    (chartAt Work.Space.E4 x₀).open_source.mem_nhds hp
  have hev : (fun q : M => Submission.ChartCurv.chrB C.cov x₀ q a b)
      =ᶠ[nhds p] (fun q : M =>
        ∑ i : Fin (Module.finrank ℝ Work.Space.E4),
          ∑ j : Fin (Module.finrank ℝ Work.Space.E4),
            (((Module.finBasis ℝ Work.Space.E4).coord i) a
                * ((Module.finBasis ℝ Work.Space.E4).coord j) b) •
              Submission.ChartCurv.gammaEntry C.cov x₀ i j q) :=
    hsrc.mono (fun q hq =>
      Submission.ChartCurv.chrB_eq_sum_gammaEntry (cov := C.cov) x₀ q a b hq)
  refine MDifferentiableAt.congr_of_eventuallyEq ?_ hev
  refine Submission.ChartCurv.mdifferentiableAt_sum_fun (I := Work.Space.I4) Finset.univ
    (fun i q => ∑ j : Fin (Module.finrank ℝ Work.Space.E4),
      (((Module.finBasis ℝ Work.Space.E4).coord i) a
          * ((Module.finBasis ℝ Work.Space.E4).coord j) b) •
        Submission.ChartCurv.gammaEntry C.cov x₀ i j q) ?_
  intro i _
  refine Submission.ChartCurv.mdifferentiableAt_sum_fun (I := Work.Space.I4) Finset.univ
    (fun j q => (((Module.finBasis ℝ Work.Space.E4).coord i) a
          * ((Module.finBasis ℝ Work.Space.E4).coord j) b) •
        Submission.ChartCurv.gammaEntry C.cov x₀ i j q) ?_
  intro j _
  exact (Submission.ChartCurv.mdifferentiableAt_gammaEntry (cov := C.cov) x₀ i j hp).const_smul _

/-- **The chart Christoffel symbol solves the model Koszul formula.**  If the chart metric at `x₀`
agrees with the model metric field `G` near the chart image of `p`, then `chrB` at `p` is the
Koszul solution of `G` at the chart image of `p`. -/
theorem chartBridge_chrB_eq_koszulChr_of_model (x₀ p : M)
    (hp : p ∈ (chartAt Work.Space.E4 x₀).source) {G : Work.Curvature.MetricField}
    (hmodel : ∀ᶠ q in nhds ((extChartAt Work.Space.I4 x₀) p), ∀ a b : Work.Space.E4,
      Submission.ChartConnection.chartGram (I := Work.Space.I4) x₀
        ((extChartAt Work.Space.I4 x₀).symm q) a b = G q a b)
    (a b : Work.Space.E4) :
    Submission.ChartCurv.chrB C.cov x₀ p a b
      = Work.Curvature.koszulChr G ((extChartAt Work.Space.I4 x₀) p) a b := by
  classical
  set q : Work.Space.E4 := (extChartAt Work.Space.I4 x₀) p with hq
  have hp' : p ∈ (extChartAt Work.Space.I4 x₀).source := by
    rw [extChartAt_source]; exact hp
  have hsymm : (extChartAt Work.Space.I4 x₀).symm q = p := by
    rw [hq]; exact (extChartAt Work.Space.I4 x₀).left_inv hp'
  -- the model metric at `q` is the chart metric at `p`
  have hpt : ∀ a b : Work.Space.E4,
      Submission.ChartConnection.chartGram (I := Work.Space.I4) x₀ p a b = G q a b := by
    intro a b
    have h := Filter.Eventually.self_of_nhds hmodel a b
    rwa [hsymm] at h
  have hlin : ∀ x y c : Work.Space.E4, G q (x - y) c = G q x c - G q y c := by
    intro x y c
    rw [← hpt (x - y) c, ← hpt x c, ← hpt y c, chartBridge_chartGram_sub_fst]
  have hpos : ∀ x : Work.Space.E4, x ≠ 0 → 0 < G q x x := by
    intro x hx
    rw [← hpt x x]
    simpa using Work.LeviCivita.chartGram_posDef (I := Work.Space.I4) x₀ p hp hx
  have hk : ∀ c : Work.Space.E4,
      G q (Submission.ChartCurv.chrB C.cov x₀ p a b) c
        = Work.Curvature.koszulRHS G q a b c := by
    intro c
    rw [← hpt (Submission.ChartCurv.chrB C.cov x₀ p a b) c]
    have h1 : Submission.ChartConnection.chartGram (I := Work.Space.I4) x₀ p
          (Submission.ChartCurv.chrB C.cov x₀ p a b) c
        = (1/2) * (Work.Curvature.dG G q b a c + Work.Curvature.dG G q a b c
            - Work.Curvature.dG G q c a b) := by
      rw [Work.LeviCivita.chartGram_chrB_eq_koszul (I := Work.Space.I4) C.compat C.torsion
          x₀ p hp a b c,
        Work.Curvature.chartDg_eq_dG (I := Work.Space.I4) x₀ p b a c
          (hmodel.mono (fun r hr => hr a c)),
        Work.Curvature.chartDg_eq_dG (I := Work.Space.I4) x₀ p a b c
          (hmodel.mono (fun r hr => hr b c)),
        Work.Curvature.chartDg_eq_dG (I := Work.Space.I4) x₀ p c a b
          (hmodel.mono (fun r hr => hr a b))]
    rw [h1, Work.Curvature.koszulRHS, one_div]
  exact (Work.Curvature.koszulChr_eq_of_forall hlin hpos hk).symm

/-- The pointwise form of `chartBridge_chrB_eq_koszulChr_of_model` at the centre `x₀` of the chart. -/
theorem chartBridge_chrB_at_center_eq_koszulChr (x₀ : M) {G : Work.Curvature.MetricField}
    (hmodel : ∀ᶠ q in nhds ((extChartAt Work.Space.I4 x₀) x₀), ∀ a b : Work.Space.E4,
      Submission.ChartConnection.chartGram (I := Work.Space.I4) x₀
        ((extChartAt Work.Space.I4 x₀).symm q) a b = G q a b)
    (a b : Work.Space.E4) :
    Submission.ChartCurv.chrB C.cov x₀ x₀ a b
      = Work.Curvature.koszulChr G ((extChartAt Work.Space.I4 x₀) x₀) a b :=
  chartBridge_chrB_eq_koszulChr_of_model (C := C) x₀ x₀ (mem_chart_source Work.Space.E4 x₀) hmodel a b

/-- **The chart representative of `chrB` is the model Christoffel symbol** near the chart image of
`x₀`: `x ↦ B(σ(x); a, b) = koszulChr G x a b` for all `x` near `q₀ = extChartAt I4 x₀ x₀`. -/
theorem chartBridge_chrRep_eventuallyEq_koszulChr (x₀ : M) {G : Work.Curvature.MetricField}
    (hmodel : ∀ᶠ q in nhds ((extChartAt Work.Space.I4 x₀) x₀), ∀ a b : Work.Space.E4,
      Submission.ChartConnection.chartGram (I := Work.Space.I4) x₀
        ((extChartAt Work.Space.I4 x₀).symm q) a b = G q a b)
    (a b : Work.Space.E4) :
    (fun x : Work.Space.E4 =>
        Submission.ChartCurv.chrB C.cov x₀ ((extChartAt Work.Space.I4 x₀).symm x) a b)
      =ᶠ[nhds ((extChartAt Work.Space.I4 x₀) x₀)]
        (fun x : Work.Space.E4 => Work.Curvature.koszulChr G x a b) := by
  classical
  have hS : {q : Work.Space.E4 | ∀ a b : Work.Space.E4,
      Submission.ChartConnection.chartGram (I := Work.Space.I4) x₀
        ((extChartAt Work.Space.I4 x₀).symm q) a b = G q a b}
      ∈ nhds ((extChartAt Work.Space.I4 x₀) x₀) := hmodel
  have hx₀ : (extChartAt Work.Space.I4 x₀) x₀ ∈ (extChartAt Work.Space.I4 x₀).target :=
    (extChartAt Work.Space.I4 x₀).map_source (by
      rw [extChartAt_source]; exact mem_chart_source Work.Space.E4 x₀)
  have hint : interior {q : Work.Space.E4 | ∀ a b : Work.Space.E4,
      Submission.ChartConnection.chartGram (I := Work.Space.I4) x₀
        ((extChartAt Work.Space.I4 x₀).symm q) a b = G q a b}
      ∈ nhds ((extChartAt Work.Space.I4 x₀) x₀) :=
    isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hS)
  have htg : (extChartAt Work.Space.I4 x₀).target ∈ nhds ((extChartAt Work.Space.I4 x₀) x₀) :=
    (isOpen_extChartAt_target (I := Work.Space.I4) x₀).mem_nhds hx₀
  change ∀ᶠ x in nhds ((extChartAt Work.Space.I4 x₀) x₀),
    Submission.ChartCurv.chrB C.cov x₀ ((extChartAt Work.Space.I4 x₀).symm x) a b
      = Work.Curvature.koszulChr G x a b
  filter_upwards [hint, htg] with x hx hxt
  have hsrc : (extChartAt Work.Space.I4 x₀).symm x ∈ (chartAt Work.Space.E4 x₀).source := by
    have h := (extChartAt Work.Space.I4 x₀).map_target hxt
    rwa [extChartAt_source] at h
  have hright : (extChartAt Work.Space.I4 x₀) ((extChartAt Work.Space.I4 x₀).symm x) = x :=
    (extChartAt Work.Space.I4 x₀).right_inv hxt
  have hmodel' : ∀ᶠ r in nhds
        ((extChartAt Work.Space.I4 x₀) ((extChartAt Work.Space.I4 x₀).symm x)),
      ∀ a b : Work.Space.E4,
        Submission.ChartConnection.chartGram (I := Work.Space.I4) x₀
          ((extChartAt Work.Space.I4 x₀).symm r) a b = G r a b := by
    rw [hright]
    exact Filter.mem_of_superset (isOpen_interior.mem_nhds hx) interior_subset
  have h := chartBridge_chrB_eq_koszulChr_of_model (C := C) x₀
    ((extChartAt Work.Space.I4 x₀).symm x) hsrc hmodel' a b
  rwa [hright] at h

/-- **The derivative of the chart Christoffel symbol is the model one.** -/
theorem chartBridge_dB_eq_dBmodel (x₀ : M) {G : Work.Curvature.MetricField}
    (hmodel : ∀ᶠ q in nhds ((extChartAt Work.Space.I4 x₀) x₀), ∀ a b : Work.Space.E4,
      Submission.ChartConnection.chartGram (I := Work.Space.I4) x₀
        ((extChartAt Work.Space.I4 x₀).symm q) a b = G q a b)
    (d a b : Work.Space.E4) :
    Submission.ChartCurv.dB C.cov x₀ x₀ d a b
      = Work.Curvature.dBmodel G ((extChartAt Work.Space.I4 x₀) x₀) d a b := by
  have hsrc : x₀ ∈ (chartAt Work.Space.E4 x₀).source := mem_chart_source Work.Space.E4 x₀
  have hmd : MDifferentiableAt Work.Space.I4 𝓘(ℝ, Work.Space.E4)
      (fun q : M => Submission.ChartCurv.chrB C.cov x₀ q a b) x₀ :=
    chartBridge_mdifferentiableAt_chrB (C := C) x₀ hsrc a b
  have hev := chartBridge_chrRep_eventuallyEq_koszulChr (C := C) x₀ hmodel a b
  calc Submission.ChartCurv.dB C.cov x₀ x₀ d a b
      = mvfderiv Work.Space.I4 (fun q : M => Submission.ChartCurv.chrB C.cov x₀ q a b) x₀
          (Submission.Geodesic.frameVector (I := Work.Space.I4) x₀ x₀ d) := rfl
    _ = fderiv ℝ (fun x : Work.Space.E4 =>
          Submission.ChartCurv.chrB C.cov x₀ ((extChartAt Work.Space.I4 x₀).symm x) a b)
          ((extChartAt Work.Space.I4 x₀) x₀) d :=
        Submission.ChartCurvCont.mvfderiv_frameVector_eq_fderiv (I := Work.Space.I4)
          x₀ hsrc hmd d
    _ = fderiv ℝ (fun x : Work.Space.E4 => Work.Curvature.koszulChr G x a b)
          ((extChartAt Work.Space.I4 x₀) x₀) d := by
        rw [Filter.EventuallyEq.fderiv_eq hev]
    _ = Work.Curvature.dBmodel G ((extChartAt Work.Space.I4 x₀) x₀) d a b := rfl

/-- **The pointwise curvature bridge.**  If the chart metric at `x₀` coincides with a model metric
field `G` near the chart image of `x₀`, and `G` has non-positive sectional curvature there, then the
sectional curvature of `M` at `x₀` (for the framework connection `C.cov`) is non-positive: the
numerator `⟪R(u,v)v, u⟫` is `≤ 0` for every orthonormal pair `u`, `v` of tangent vectors. -/
theorem secNonpos_of_chartModels
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace Work.Space.E4 M]
    [Work.Final.ChartedRiem M] [C : Work.Final.ChartedRiemConn M]
    (x₀ : M) {G : Work.Curvature.MetricField}
    (hsec : Work.Curvature.SecNonposAt G ((extChartAt Work.Space.I4 x₀) x₀))
    (hmodel : Filter.Eventually (fun q => ∀ a b : Work.Curvature.E4,
        Submission.ChartConnection.chartGram (I := Work.Space.I4) x₀
          ((extChartAt Work.Space.I4 x₀).symm q) a b = G q a b)
      (nhds ((extChartAt Work.Space.I4 x₀) x₀))) :
    ∀ u v : TangentSpace Work.Space.I4 x₀, Work.Final.riemNorm x₀ u = 1 →
      Work.Final.riemNorm x₀ v = 1 → Work.Final.riemInner x₀ u v = 0 →
      Work.Final.riemInner x₀ (Submission.CurvatureVec.curvVec C.cov x₀ u v v) u ≤ 0 := by
  intro u v _hu _hv _huv
  classical
  have hsrc : x₀ ∈ (chartAt Work.Space.E4 x₀).source := mem_chart_source Work.Space.E4 x₀
  have hmem : x₀ ∈ (extChartAt Work.Space.I4 x₀).source := by
    rw [extChartAt_source]; exact hsrc
  -- write `u` and `v` as frame vectors of the chart at `x₀`
  set α : Work.Curvature.E4 :=
    Submission.ChartCurv.coordFun (I := Work.Space.I4) x₀ (fun _ : M => u) x₀ with hα
  set β : Work.Curvature.E4 :=
    Submission.ChartCurv.coordFun (I := Work.Space.I4) x₀ (fun _ : M => v) x₀ with hβ
  have hαfr : Submission.Geodesic.frameVector (I := Work.Space.I4) x₀ x₀ α = u := by
    rw [hα]
    exact Submission.ChartCurv.frameVector_coordFun_eq (I := Work.Space.I4) x₀ hsrc
  have hβfr : Submission.Geodesic.frameVector (I := Work.Space.I4) x₀ x₀ β = v := by
    rw [hβ]
    exact Submission.ChartCurv.frameVector_coordFun_eq (I := Work.Space.I4) x₀ hsrc
  rw [← hαfr, ← hβfr]
  -- the curvature tensor in the coordinates of the chart at `x₀`
  rw [Submission.ChartCurv.curvVec_eq_chart (cov := C.cov) (htor := C.torsion) x₀ x₀ β β α hsrc]
  set A : Work.Curvature.E4 := Submission.ChartCurv.dB C.cov x₀ x₀ α β β
      - Submission.ChartCurv.dB C.cov x₀ x₀ β β α
      + Submission.ChartCurv.chrB C.cov x₀ x₀ (Submission.ChartCurv.chrB C.cov x₀ x₀ β β) α
      - Submission.ChartCurv.chrB C.cov x₀ x₀ (Submission.ChartCurv.chrB C.cov x₀ x₀ β α) β with hAdef
  change Submission.ChartConnection.chartGram (I := Work.Space.I4) x₀ x₀ A α ≤ 0
  -- the model hypothesis, specialised to the point `x₀` itself
  have hmodelE : ∀ᶠ q in nhds ((extChartAt Work.Space.I4 x₀) x₀), ∀ a b : Work.Space.E4,
      Submission.ChartConnection.chartGram (I := Work.Space.I4) x₀
        ((extChartAt Work.Space.I4 x₀).symm q) a b = G q a b := hmodel
  have hmodel' : ∀ a b : Work.Curvature.E4,
      Submission.ChartConnection.chartGram (I := Work.Space.I4) x₀ x₀ a b
        = G ((extChartAt Work.Space.I4 x₀) x₀) a b := by
    intro a b
    have h := Filter.Eventually.self_of_nhds hmodel a b
    rwa [show (extChartAt Work.Space.I4 x₀).symm ((extChartAt Work.Space.I4 x₀) x₀) = x₀ from
      (extChartAt Work.Space.I4 x₀).left_inv hmem] at h
  -- the chart expression is the model curvature
  have hA : A = Work.Curvature.modelCurv G ((extChartAt Work.Space.I4 x₀) x₀) α β β := by
    simp only [hAdef, Work.Curvature.modelCurv, chartBridge_dB_eq_dBmodel x₀ hmodelE,
      chartBridge_chrB_at_center_eq_koszulChr x₀ hmodelE]
  rw [hA, hmodel']
  exact hsec α β

end

end Work.Final
