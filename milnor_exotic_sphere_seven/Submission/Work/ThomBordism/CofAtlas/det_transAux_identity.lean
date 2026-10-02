import Submission.Work.ThomBordism.CofAtlas.Signs
import Submission.Work.ThomBordism.CofAtlas.Structure
import Submission.Work.ThomBordism.CofAtlas.det_section_prod
import Submission.Work.ThomBordism.CofAtlas.Tdom_comp_Delta
import Submission.Work.ThomBordism.CofAtlas.Delta_comp_DeltaInv
import Submission.Work.ThomBordism.CofAtlas.Omega_comp_Tdom
import Submission.Work.ThomBordism.CofAtlas.range_chartIota_eq_ker_Omega
import Submission.Work.ThomBordism.CofAtlas.fderiv_transAux_int

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The determinant identity for the transition of two `Lvl` charts

`Work.ThomBordism.CofAtlas.det_transAux_identity`: the determinant of the differential of the
transition `transAux x y` of the `Lvl` charts at two points `x`, `y` of the coframed level set,
in terms of the chart signs `sgn`, the chart-change signs `tau` and the coframing transition
`gLin`.

The content is the abstract determinant identity `det_section_prod_gen`, applied to
`β = chartBeta x`, `J = chartIota x`, `Ω = Omega x q`, `β' = chartBeta y ∘ Tdom`,
`q' = Omega y q ∘ Tdom`, `g = gLin x y q`, together with

* `range (chartIota x) = ker (Omega x q)` (`range_chartIota_eq_ker_Omega`),
* `chartBeta x ∘ chartIota x = id` (`chartBeta_iota`),
* `Omega y q ∘ Tdom = gLin x y q ∘ Omega x q` (`Omega_comp_Tdom`),
* the chain rule `fderiv transAux = chartBeta y ∘ Tdom ∘ chartIota x` (`fderiv_transAux_int`),
* `(chartBeta y ∘ Tdom).prod (Omega y q ∘ Tdom) = phiD y q ∘ Tdom`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter ModelWithCorners
open Work.PTGeometric
open Work.PTGeometric.Lvl

namespace Work.ThomBordism.CofAtlas

noncomputable section

variable {k n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (NN k)) M]
  [IsManifold (𝓡∂ (NN k)) ((⊤ : ENat) : WithTop ENat) M]

theorem det_transAux_identity (D : Cof k n M) (x y : D.S.Pre) {q : D.S.Pre}
    (hx : q ∈ D.src x) (hy : q ∈ D.src y)
    (hxi : (x : M) ∉ (𝓡∂ (NN k)).boundary M) :
    LinearMap.det (fderiv ℝ (D.S.transAux x y) (D.lvlExt x q)).toLinearMap *
      LinearMap.det ((sigma k).toLinearMap.comp (D.phiD x (q : M)).toLinearMap) *
      LinearMap.det (D.gLin x y (q : M)).toLinearMap
    = LinearMap.det ((sigma k).toLinearMap.comp (D.phiD y (q : M)).toLinearMap) *
      LinearMap.det (D.Tdom x y (q : M)).toLinearMap := by
  have hqcx : q ∈ D.S.chartSource x := D.src_subset_chartSource x hx
  have hqcy : q ∈ D.S.chartSource y := D.src_subset_chartSource y hy
  have hqint : (q : M) ∈ (𝓡∂ (NN k)).interior M := by
    rw [← ModelWithCorners.compl_boundary]
    exact D.src_interior x hxi hx
  -- `g` is invertible
  have hgpos : 0 < LinearMap.det (D.gLin x y (q : M)).toLinearMap := by
    have h := D.hpos (D.jx x) (D.jx y) (q : M) (D.src_subset_U x hx) (D.src_subset_U y hy)
    simpa only [Cof.gLin] using h
  have hgne : LinearMap.det (D.gLin x y (q : M)).toLinearMap ≠ 0 := ne_of_gt hgpos
  have hker : LinearMap.ker (D.gLin x y (q : M)).toLinearMap = ⊥ := by
    by_contra h
    exact hgne ((LinearMap.det_eq_zero_iff_ker_ne_bot).mpr h)
  let g : EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin k) :=
    LinearEquiv.ofBijective (D.gLin x y (q : M)).toLinearMap
      ⟨LinearMap.ker_eq_bot.mp hker,
       (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp
        (LinearMap.ker_eq_bot.mp hker)⟩
  have hgto : g.toLinearMap = (D.gLin x y (q : M)).toLinearMap := rfl
  -- the hypotheses of the abstract identity
  have hJ : ((D.S.chartBeta x).toLinearMap).comp ((D.S.chartIota x).toLinearMap) = 1 := by
    refine LinearMap.ext fun v => ?_
    simpa using D.S.chartBeta_iota x v
  have himJ : LinearMap.range ((D.S.chartIota x).toLinearMap)
      = LinearMap.ker ((D.Omega x (q : M)).toLinearMap) :=
    range_chartIota_eq_ker_Omega D x hx hqint
  have hq' : ((D.Omega y (q : M)).comp (D.Tdom x y (q : M))).toLinearMap
      = g.toLinearMap.comp ((D.Omega x (q : M)).toLinearMap) := by
    rw [hgto]
    exact congrArg ContinuousLinearMap.toLinearMap (Omega_comp_Tdom D x y hx hy hqint)
  -- the abstract identity
  have key := det_section_prod_gen (K := ℝ) (V := EuclideanSpace ℝ (Fin 9))
    (W := EuclideanSpace ℝ (Fin k)) (X := ModN k) (sigma k)
    ((D.S.chartBeta x).toLinearMap)
    (((D.S.chartBeta y).comp (D.Tdom x y (q : M))).toLinearMap)
    ((D.Omega x (q : M)).toLinearMap)
    (((D.Omega y (q : M)).comp (D.Tdom x y (q : M))).toLinearMap)
    g ((D.S.chartIota x).toLinearMap) hJ himJ hq'
  -- the chain rule identifies the first factor
  have e1 : LinearMap.det (fderiv ℝ (D.S.transAux x y) (D.lvlExt x q)).toLinearMap
      = LinearMap.det (((D.S.chartBeta y).comp (D.Tdom x y (q : M))).toLinearMap.comp
          (D.S.chartIota x).toLinearMap) := by
    rw [fderiv_transAux_int D x y hqcx hqcy hxi]
    exact congrArg (fun f => LinearMap.det f) (LinearMap.comp_assoc _ _ _).symm
  -- and `det_comp` the last one
  have eR : LinearMap.det ((sigma k).toLinearMap.comp (D.phiD y (q : M)).toLinearMap) *
      LinearMap.det (D.Tdom x y (q : M)).toLinearMap
      = LinearMap.det ((sigma k).toLinearMap.comp
          (((D.S.chartBeta y).comp (D.Tdom x y (q : M))).toLinearMap.prod
            ((D.Omega y (q : M)).comp (D.Tdom x y (q : M))).toLinearMap)) := by
    rw [← LinearMap.det_comp]
    congr 1
  rw [e1, ← hgto, eR]
  exact key

end

end Work.ThomBordism.CofAtlas
