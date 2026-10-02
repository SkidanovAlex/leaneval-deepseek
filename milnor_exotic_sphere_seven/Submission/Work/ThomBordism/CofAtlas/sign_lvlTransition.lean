import Submission.Work.ThomBordism.CofAtlas.Signs
import Submission.Work.ThomBordism.CofAtlas.Structure
import Submission.Work.ThomBordism.CofAtlas.det_section_prod
import Submission.Work.ThomBordism.CofAtlas.Tdom_comp_Delta
import Submission.Work.ThomBordism.CofAtlas.Delta_comp_DeltaInv
import Submission.Work.ThomBordism.CofAtlas.Omega_comp_Tdom
import Submission.Work.ThomBordism.CofAtlas.range_chartIota_eq_ker_Omega
import Submission.Work.ThomBordism.CofAtlas.fderiv_transAux_int
import Submission.Work.ThomBordism.CofAtlas.det_transAux_identity

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The sign of the transition of two `Lvl` charts (the crux)

`Work.ThomBordism.CofAtlas.sign_lvlTransition`: for the coframed level-set data `D`, two interior
points `x`, `y` of the level set and a point `q` of the overlap of their (connected) chart sources,

`sign (det (d transAux)) = sgn x q · sgn y q · tau x q · tau y q`.

The proof combines the determinant identity `det_transAux_identity` with the corresponding
identity for the chart change (`Tdom_comp_Delta`), the positivity of `det (gLin)` (`hpos`) and of
`det (Tex)` (`hMdet`), and the non-vanishing of `det (Delta x q)` and of `det (σ ∘ phiD x q)`.
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

/-! ## Elementary sign arithmetic -/

theorem mul_self_eq_one_of_ne_zero (s : SignType) (hs : s ≠ 0) : s * s = 1 := by
  cases s <;> simp_all

/-- **The sign computation.**  If `A * B * C = D * E` and `E * Fx = Fy * G` with
`sign C = sign G = 1` and `sign B ≠ 0`, `sign Fx ≠ 0`, then
`sign A = sign B · sign D · sign Fx · sign Fy`. -/
theorem sign_prod_eq {A B C D E Fx Fy G : ℝ}
    (hI : A * B * C = D * E) (hII : E * Fx = Fy * G)
    (hC : SignType.sign C = 1) (hG : SignType.sign G = 1)
    (hB : SignType.sign B ≠ 0) (hFx : SignType.sign Fx ≠ 0) :
    SignType.sign A = SignType.sign B * SignType.sign D * SignType.sign Fx * SignType.sign Fy := by
  have hsB : SignType.sign B * SignType.sign B = 1 := mul_self_eq_one_of_ne_zero _ hB
  have hsFx : SignType.sign Fx * SignType.sign Fx = 1 := mul_self_eq_one_of_ne_zero _ hFx
  have h1 : SignType.sign A * SignType.sign B = SignType.sign D * SignType.sign E := by
    have h := congrArg SignType.sign hI
    simp only [sign_mul] at h
    rw [hC, mul_one] at h
    exact h
  have h2 : SignType.sign E = SignType.sign Fy * SignType.sign Fx := by
    have h := congrArg SignType.sign hII
    simp only [sign_mul] at h
    rw [hG, mul_one] at h
    calc SignType.sign E
        = SignType.sign E * (SignType.sign Fx * SignType.sign Fx) := by rw [hsFx, mul_one]
      _ = SignType.sign E * SignType.sign Fx * SignType.sign Fx := by rw [mul_assoc]
      _ = SignType.sign Fy * SignType.sign Fx := by rw [h]
  calc SignType.sign A
      = SignType.sign A * (SignType.sign B * SignType.sign B) := by rw [hsB, mul_one]
    _ = SignType.sign A * SignType.sign B * SignType.sign B := by rw [mul_assoc]
    _ = SignType.sign D * SignType.sign E * SignType.sign B := by rw [h1]
    _ = SignType.sign D * (SignType.sign Fy * SignType.sign Fx) * SignType.sign B := by rw [h2]
    _ = SignType.sign B * SignType.sign D * SignType.sign Fx * SignType.sign Fy := by ac_rfl

/-! ## Non-vanishing of the chart sign and the chart-change sign -/

/-- **The chart sign at a point of the source is nonzero**: `(β_x, Ω_x(q))` is injective. -/
theorem sgn_det_ne_zero (D : Cof k n M) (x : D.S.Pre) {q : D.S.Pre} (hq : q ∈ D.src x)
    (hint : (q : M) ∈ (𝓡∂ (NN k)).interior M) :
    LinearMap.det ((sigma k).toLinearMap.comp (D.phiD x (q : M)).toLinearMap) ≠ 0 := by
  intro h0
  have hker : LinearMap.ker ((sigma k).toLinearMap.comp (D.phiD x (q : M)).toLinearMap) ≠ ⊥ :=
    (LinearMap.det_eq_zero_iff_ker_ne_bot).mp h0
  apply hker
  rw [Submodule.eq_bot_iff]
  intro v hv
  have hphi : (D.phiD x (q : M)).toLinearMap v = 0 := by
    have hcomp : (sigma k).toLinearMap ((D.phiD x (q : M)).toLinearMap v) = 0 := by
      simpa only [LinearMap.comp_apply, LinearMap.mem_ker] using hv
    exact (sigma k).injective (by
      simpa only [LinearEquiv.coe_toLinearMap, LinearMap.comp_apply, map_zero] using hcomp)
  have hβ : (D.S.chartBeta x) v = 0 := by
    have h := congrArg Prod.fst hphi
    simpa [Cof.phiD] using h
  have hΩ : (D.Omega x (q : M)) v = 0 := by
    have h := congrArg Prod.snd hphi
    simpa [Cof.phiD] using h
  have hkerΩ : LinearMap.ker ((D.Omega x (q : M)).toLinearMap)
      = LinearMap.range ((D.S.chartIota x).toLinearMap) :=
    (range_chartIota_eq_ker_Omega D x hq hint).symm
  have hvΩ : v ∈ LinearMap.range ((D.S.chartIota x).toLinearMap) := by
    rw [← hkerΩ, LinearMap.mem_ker]
    exact hΩ
  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hvΩ
  have hw0 : w = 0 := by
    have h := hβ
    rw [← hw] at h
    change (D.S.chartBeta x) ((D.S.chartIota x) w) = 0 at h
    rwa [D.S.chartBeta_iota x w] at h
  rw [← hw, hw0, map_zero]

/-- **The chart-change sign at a point of the source is nonzero**: `Delta x q` is invertible. -/
theorem tau_det_ne_zero (D : Cof k n M) (x : D.S.Pre) {q : D.S.Pre} (hq : q ∈ D.src x)
    (hint : (q : M) ∈ (𝓡∂ (NN k)).interior M) :
    LinearMap.det (D.Delta x (q : M)).toLinearMap ≠ 0 := by
  have hD := Delta_comp_DeltaInv D x (D.src_subset_chartSource x hq) (D.src_subset_ambSrc x hq) hint
  have h2 : (D.Delta x (q : M)).toLinearMap.comp (D.DeltaInv x (q : M)).toLinearMap = 1 := by
    have h := congrArg (fun f : ModN k →L[ℝ] ModN k => (f : ModN k →ₗ[ℝ] ModN k)) hD
    simpa using h
  have hmul : LinearMap.det (D.Delta x (q : M)).toLinearMap
      * LinearMap.det (D.DeltaInv x (q : M)).toLinearMap = 1 := by
    rw [← LinearMap.det_comp, h2]
    simp
  intro hzero
  rw [hzero, zero_mul] at hmul
  exact one_ne_zero hmul.symm

/-! ## Positivity of the coframing transition and of the ambient chart change -/

theorem gLin_det_pos (D : Cof k n M) (x y : D.S.Pre) {q : D.S.Pre} (hx : q ∈ D.src x)
    (hy : q ∈ D.src y) :
    0 < LinearMap.det (D.gLin x y (q : M)).toLinearMap := by
  have h := D.hpos (D.jx x) (D.jx y) (q : M) (D.src_subset_U x hx) (D.src_subset_U y hy)
  simpa only [Cof.gLin] using h

/-- **The derivative of the ambient chart change has positive determinant** (this is `hMdet`). -/
theorem tex_det_pos (D : Cof k n M) (x y : D.S.Pre) {q : D.S.Pre}
    (hxi : (x : M) ∉ (𝓡∂ (NN k)).boundary M) (hyi : (y : M) ∉ (𝓡∂ (NN k)).boundary M)
    (hqx : q ∈ D.ambSrc x) (hqy : q ∈ D.ambSrc y)
    (hint : (q : M) ∈ (𝓡∂ (NN k)).interior M) :
    0 < LinearMap.det (D.Tex x y (q : M)).toLinearMap := by
  have hsrc : (q : M) ∈ (D.ambChart x).source := hqx
  have hsrc' : (q : M) ∈ (extChartAt (𝓡∂ (NN k)) (x : M)).source := by
    simpa [OpenPartialHomeomorph.extend_source] using hsrc
  have hnb : (q : M) ∉ (𝓡∂ (NN k)).boundary M := by
    rw [← ModelWithCorners.compl_interior]
    simpa using hint
  refine D.hMdet (x : M) (y : M) hxi hyi (D.ambExt x (q : M)) ⟨?_, ?_⟩ ?_
  · -- the point lies in the target of the ambient chart at `x`
    exact PartialEquiv.map_source _ hsrc'
  · -- and its preimage lies in the source of the chart at `y`
    show (extChartAt (𝓡∂ (NN k)) (x : M)).symm (D.ambExt x (q : M))
      ∈ (extChartAt (𝓡∂ (NN k)) (y : M)).source
    have hleft : (extChartAt (𝓡∂ (NN k)) (x : M)).symm (D.ambExt x (q : M)) = (q : M) :=
      PartialEquiv.left_inv _ hsrc'
    rw [hleft]
    simpa [OpenPartialHomeomorph.extend_source] using (hqy : (q : M) ∈ (D.ambChart y).source)
  · -- the zeroth coordinate is positive
    refine lt_of_le_of_ne ?_ (Ne.symm fun hzero => hnb ?_)
    · exact Work.ThomBordism.Transversality.Preimage.zero_le_extend_apply_coord (D.ambChart x) hsrc
    · exact (Work.ThomBordism.Transversality.Preimage.mem_boundary_iff_extend_apply_coord_eq_zero
        (m := NN k) (IsManifold.chart_mem_maximalAtlas (x : M)) hsrc).mpr hzero

/-! ## The two determinant identities -/

theorem tex_delta_identity (D : Cof k n M) (x y : D.S.Pre) {q : D.S.Pre}
    (hx : q ∈ D.src x) (hy : q ∈ D.src y)
    (hint : (q : M) ∈ (𝓡∂ (NN k)).interior M) :
    LinearMap.det (D.Tdom x y (q : M)).toLinearMap * LinearMap.det (D.Delta x (q : M)).toLinearMap
      = LinearMap.det (D.Delta y (q : M)).toLinearMap
        * LinearMap.det (D.Tex x y (q : M)).toLinearMap := by
  have h := Tdom_comp_Delta D x y (D.src_subset_chartSource x hx) (D.src_subset_chartSource y hy)
    (D.src_subset_ambSrc x hx) (D.src_subset_ambSrc y hy) hint
  rw [← LinearMap.det_comp, ← LinearMap.det_comp]
  congr 1
  exact congrArg ContinuousLinearMap.toLinearMap h

/-! ## The crux -/

theorem sign_lvlTransition (D : Cof k n M) (x y : D.S.Pre) {q : D.S.Pre}
    (hx : q ∈ D.src x) (hy : q ∈ D.src y)
    (hxi : (x : M) ∉ (𝓡∂ (NN k)).boundary M) (hyi : (y : M) ∉ (𝓡∂ (NN k)).boundary M) :
    SignType.sign (LinearMap.det (fderiv ℝ (D.S.transAux x y) (D.lvlExt x q)).toLinearMap)
      = D.sgn x (q : M) * D.sgn y (q : M) * D.tau x (q : M) * D.tau y (q : M) := by
  have hqint : (q : M) ∈ (𝓡∂ (NN k)).interior M := by
    rw [← ModelWithCorners.compl_boundary]
    exact D.src_interior x hxi hx
  refine sign_prod_eq (A := LinearMap.det (fderiv ℝ (D.S.transAux x y) (D.lvlExt x q)).toLinearMap)
    (B := LinearMap.det ((sigma k).toLinearMap.comp (D.phiD x (q : M)).toLinearMap))
    (C := LinearMap.det (D.gLin x y (q : M)).toLinearMap)
    (D := LinearMap.det ((sigma k).toLinearMap.comp (D.phiD y (q : M)).toLinearMap))
    (E := LinearMap.det (D.Tdom x y (q : M)).toLinearMap)
    (Fx := LinearMap.det (D.Delta x (q : M)).toLinearMap)
    (Fy := LinearMap.det (D.Delta y (q : M)).toLinearMap)
    (G := LinearMap.det (D.Tex x y (q : M)).toLinearMap)
    (det_transAux_identity D x y hx hy hxi) (tex_delta_identity D x y hx hy hqint)
    (sign_pos (gLin_det_pos D x y hx hy))
    (sign_pos (tex_det_pos D x y hxi hyi (D.src_subset_ambSrc x hx)
      (D.src_subset_ambSrc y hy) hqint))
    (sign_ne_zero.mpr (sgn_det_ne_zero D x hx hqint))
    (sign_ne_zero.mpr (tau_det_ne_zero D x hx hqint))

end

end Work.ThomBordism.CofAtlas
