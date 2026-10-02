import Mathlib
import Submission.Work.ThomBordism.CofAtlas.Signs
import Submission.Work.ThomBordism.CofAtlas.Tdom_comp_Delta
import Submission.Work.PTGeometric.GrRank

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The coframing transforms by the coframing cocycle under a change of chart

`Work.ThomBordism.CofAtlas.Omega_comp_Tdom`: for `x y` in the level set and `q` a point of the
overlap (lying over an interior point of `M`),

`Ω_y(q) ∘ Tdom x y q = gLin x y q ∘ Ω_x(q)`.

Here `Ω_x(p) = ℓ (jx x) ∘ mfderiv v p ∘ Cx x p` is the coframing of the level set read in the
normal-form coordinates of the chart at `x` (`Cx x p` being the derivative of the chart change from
the normal-form chart at `x` to the ambient chart *at `p`*, in which `mfderiv v p` is written), and
`Tdom x y q` is the derivative of the change of normal-form coordinates from `x` to `y`.  The
identity is therefore a chain rule (`Cx y q ∘ Tdom x y q = Cx x q`, proved here as
`Cx_comp_Tdom`) together with the algebraic fact that the coframing inverse `e (jx x) q` of
`ℓ (jx x)` is a right inverse of `ℓ (jx x)` on the plane `im (P q)`:

* `range (mfderiv v q) = {w | P q w = w}` is the hypothesis `Cof.hlink` of the data;
* `e j q : ℝᵏ → ℝⁿ` is injective (`Cof.heinj`) with left inverse `ℓ j` (`Cof.hℓe`) and maps into
  the fixed space of `P q`, which has dimension `k` because `P q ∈ Gr n k`
  (`Work.PTGeometric.finrank_range_mem_Gr`, the rank of an orthogonal projection is its trace);
* hence `range (e j q) = {w | P q w = w}`, so `e j q (ℓ j w) = w` for every fixed point `w`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter ModelWithCorners
open Work.PTGeometric
open Work.PTGeometric.Lvl

namespace Work.ThomBordism.CofAtlas

noncomputable section

variable {k n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (NN k)) M]
  [IsManifold (𝓡∂ (NN k)) ((⊤ : ENat) : WithTop ENat) M]

/-- **Chain rule for the coframing transport.**  The derivative of the change of normal-form
coordinates from `x` to `y`, followed by the transport from the normal-form chart at `y` to the
ambient chart at `q`, is the transport from the normal-form chart at `x` to the ambient chart at
`q`.  Both composites are the derivative at the point corresponding to `q` of the chart change
`domChart x → ambChart q`. -/
private theorem Cx_comp_Tdom (D : Cof k n M) (x y : D.S.Pre) {q : D.S.Pre}
    (hx : q ∈ D.src x) (hy : q ∈ D.src y)
    (hint : (q : M) ∈ (𝓡∂ (NN k)).interior M) :
    (D.Cx y (q : M)).comp (D.Tdom x y (q : M)) = D.Cx x (q : M) := by
  set p : M := (q : M) with hp
  have hn : (((⊤ : ENat) : WithTop ENat) : ℕ∞ω) ≠ 0 := by simp
  have hxcs : q ∈ D.S.chartSource x := D.src_subset_chartSource x hx
  have hycs : q ∈ D.S.chartSource y := D.src_subset_chartSource y hy
  have hxsrc : p ∈ (D.domChart x).source := hxcs.1
  have hysrc : p ∈ (D.domChart y).source := hycs.1
  have haqsrc : p ∈ (D.ambChart q).source := by
    simp [Cof.ambChart, hp]
  have hdomxmax : D.domChart x ∈ IsManifold.maximalAtlas (𝓡∂ (NN k))
      ((⊤ : ENat) : WithTop ENat) M :=
    Work.PTGeometric.Lvl.Setup.domChartAt_mem_maximalAtlas D.S x
  have hdomymax : D.domChart y ∈ IsManifold.maximalAtlas (𝓡∂ (NN k))
      ((⊤ : ENat) : WithTop ENat) M :=
    Work.PTGeometric.Lvl.Setup.domChartAt_mem_maximalAtlas D.S y
  have haqmax : D.ambChart q ∈ IsManifold.maximalAtlas (𝓡∂ (NN k))
      ((⊤ : ENat) : WithTop ENat) M :=
    IsManifold.chart_mem_maximalAtlas (q : M)
  have hintDomx : (D.domChart x).extend (𝓡∂ (NN k)) p ∈ interior (range (𝓡∂ (NN k))) :=
    tcD_mem_interior_range (𝓡∂ (NN k)) hn hdomxmax hxsrc hint
  have hintDomy : (D.domChart y).extend (𝓡∂ (NN k)) p ∈ interior (range (𝓡∂ (NN k))) :=
    tcD_mem_interior_range (𝓡∂ (NN k)) hn hdomymax hysrc hint
  have hdF : DifferentiableAt ℝ (D.domChange x y) ((D.domChart x).extend (𝓡∂ (NN k)) p) :=
    tcD_differentiableAt (𝓡∂ (NN k)) hn hdomxmax hdomymax hxsrc hysrc hintDomx
  have hdG : DifferentiableAt ℝ
      ((𝓡∂ (NN k)).extendCoordChange (D.domChart y) (D.ambChart q))
      ((D.domChart y).extend (𝓡∂ (NN k)) p) :=
    tcD_differentiableAt (𝓡∂ (NN k)) hn hdomymax haqmax hysrc haqsrc hintDomy
  have hv1 : (D.domChange x y) ((D.domChart x).extend (𝓡∂ (NN k)) p)
      = (D.domChart y).extend (𝓡∂ (NN k)) p :=
    tcD_apply_extend (𝓡∂ (NN k)) (D.domChart x) (D.domChart y) hxsrc
  have hev : (((𝓡∂ (NN k)).extendCoordChange (D.domChart y) (D.ambChart q)) ∘
        ((𝓡∂ (NN k)).extendCoordChange (D.domChart x) (D.domChart y)))
      =ᶠ[𝓝 ((D.domChart x).extend (𝓡∂ (NN k)) p)]
        ((𝓡∂ (NN k)).extendCoordChange (D.domChart x) (D.ambChart q)) :=
    tcD_comp_eventuallyEq (𝓡∂ (NN k)) (D.domChart x) (D.domChart y) (D.ambChart q) hxsrc hysrc
  have hchainL : fderiv ℝ (((𝓡∂ (NN k)).extendCoordChange (D.domChart y) (D.ambChart q)) ∘
        ((𝓡∂ (NN k)).extendCoordChange (D.domChart x) (D.domChart y)))
        ((D.domChart x).extend (𝓡∂ (NN k)) p)
      = (D.Cx y p).comp (D.Tdom x y p) := by
    rw [fderiv_comp (x := (D.domChart x).extend (𝓡∂ (NN k)) p)
      (f := (𝓡∂ (NN k)).extendCoordChange (D.domChart x) (D.domChart y))
      (g := (𝓡∂ (NN k)).extendCoordChange (D.domChart y) (D.ambChart q))
      (by rw [hv1]; exact hdG) hdF]
    rw [hv1]
    rfl
  have hchainR : fderiv ℝ (((𝓡∂ (NN k)).extendCoordChange (D.domChart y) (D.ambChart q)) ∘
        ((𝓡∂ (NN k)).extendCoordChange (D.domChart x) (D.domChart y)))
        ((D.domChart x).extend (𝓡∂ (NN k)) p) = D.Cx x p := by
    rw [hev.fderiv_eq]
    rfl
  rw [← hchainL, hchainR]

/-- **The coframing frame is a two-sided inverse of `ℓ` on the plane of `P`.**  If `w` is a fixed
vector of the projection `P z`, then `e (jx x) z` (the frame of the chart `x`, read at `z`) applied
to `ℓ (jx x) w` returns `w`. -/
private theorem e_ell_apply_of_fixed (D : Cof k n M) (x z : D.S.Pre)
    (hzU : (z : M) ∈ D.U (D.jx x)) {w : EuclideanSpace ℝ (Fin n)}
    (hw : D.P (z : M) w = w) :
    D.e (D.jx x) (z : M) (D.ℓ (D.jx x) w) = w := by
  have hle : LinearMap.range ((D.e (D.jx x) (z : M)).toLinearMap)
      ≤ LinearMap.range ((D.P (z : M)).toLinearMap) := by
    intro u hu
    obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hu
    rw [← hc]
    exact LinearMap.mem_range.mpr ⟨D.e (D.jx x) (z : M) c, (D.hℓe (D.jx x) (z : M) hzU c).2⟩
  have hfinE : Module.finrank ℝ (LinearMap.range ((D.e (D.jx x) (z : M)).toLinearMap)) = k := by
    rw [LinearMap.finrank_range_of_inj (D.heinj (D.jx x) (z : M) hzU)]
    simp [finrank_euclideanSpace]
  have hfinP : Module.finrank ℝ (LinearMap.range ((D.P (z : M)).toLinearMap)) = k :=
    Work.PTGeometric.finrank_range_mem_Gr (D.hPgr (z : M))
  have heq : LinearMap.range ((D.e (D.jx x) (z : M)).toLinearMap)
      = LinearMap.range ((D.P (z : M)).toLinearMap) :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hfinE, hfinP])
  have hwmem : w ∈ LinearMap.range ((D.P (z : M)).toLinearMap) :=
    LinearMap.mem_range.mpr ⟨w, hw⟩
  rw [← heq] at hwmem
  obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hwmem
  rw [← hc]
  change (D.e (D.jx x) (z : M)) ((D.ℓ (D.jx x)) ((D.e (D.jx x) (z : M)) c))
    = (D.e (D.jx x) (z : M)) c
  rw [(D.hℓe (D.jx x) (z : M) hzU c).1]

end

end Work.ThomBordism.CofAtlas

namespace Work.ThomBordism.CofAtlas

theorem Omega_comp_Tdom
    {k n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) ((⊤ : ENat) : WithTop ENat) M]
    (D : Work.ThomBordism.CofAtlas.Cof k n M) (x y : D.S.Pre) {q : D.S.Pre}
    (hx : q ∈ D.src x) (hy : q ∈ D.src y)
    (hint : (q : M) ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).interior M) :
    (D.Omega y (q : M)).comp (D.Tdom x y (q : M))
      = (D.gLin x y (q : M)).comp (D.Omega x (q : M)) := by
  have hCxT : (D.Cx y (q : M)).comp (D.Tdom x y (q : M)) = D.Cx x (q : M) :=
    Cx_comp_Tdom D x y hx hy hint
  have hfun : ∀ u : ModN k, D.Cx y (q : M) (D.Tdom x y (q : M) u) = D.Cx x (q : M) u := by
    intro u
    exact congrArg (fun f : ModN k →L[ℝ] ModN k => f u) hCxT
  have hU : (q : M) ∈ D.U (D.jx x) := D.src_subset_U x hx
  have hlinkq : Set.range (mfderiv (𝓡∂ (NN k))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) D.v (q : M))
      = {w | D.P (q : M) w = w} := D.hlink (q : M) q.2
  refine ContinuousLinearMap.ext (fun z => ?_)
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  have hOy : D.Omega y (q : M) ((D.Tdom x y (q : M)) z)
      = D.ℓ (D.jx y) ((mfderiv (𝓡∂ (NN k))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) D.v (q : M))
            (D.Cx y (q : M) ((D.Tdom x y (q : M)) z))) := rfl
  have hOx : D.Omega x (q : M) z
      = D.ℓ (D.jx x) ((mfderiv (𝓡∂ (NN k))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) D.v (q : M))
            (D.Cx x (q : M) z)) := rfl
  have hG : D.gLin x y (q : M) (D.Omega x (q : M) z)
      = D.ℓ (D.jx y) (D.e (D.jx x) (q : M) (D.Omega x (q : M) z)) := rfl
  rw [hOy, hG, hOx]
  have hfix : D.P (q : M) ((mfderiv (𝓡∂ (NN k))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) D.v (q : M))
          ((D.Cx x (q : M)) z)) = (mfderiv (𝓡∂ (NN k))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) D.v (q : M))
          ((D.Cx x (q : M)) z) := by
    have hm : (mfderiv (𝓡∂ (NN k))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) D.v (q : M))
          ((D.Cx x (q : M)) z) ∈ Set.range (mfderiv (𝓡∂ (NN k))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) D.v (q : M)) := ⟨_, rfl⟩
    rwa [hlinkq] at hm
  rw [hfun z, e_ell_apply_of_fixed D x q hU hfix]

end Work.ThomBordism.CofAtlas
