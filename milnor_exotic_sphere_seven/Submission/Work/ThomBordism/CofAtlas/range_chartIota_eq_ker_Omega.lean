import Mathlib
import Submission.Work.ThomBordism.CofAtlas.Signs
import Submission.Work.ThomBordism.CofAtlas.Tdom_comp_Delta
import Submission.Work.PTGeometric.FDerivInChart
import Submission.Work.PTGeometric.GrRank

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter ModelWithCorners
open Work.PTGeometric

namespace Work.ThomBordism.CofAtlas

noncomputable section

variable {k n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) ((⊤ : ENat) : WithTop ENat) M]

/-! ## The ambient derivatives -/

/-- `mfderiv v q`, with the target tangent space identified with the model space. -/
private noncomputable def vLin (D : Cof k n M) (q : D.S.Pre) :
    ModN k →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  mfderiv (𝓡∂ (NN k)) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) D.v (q : M)

/-! ## Elementary linear algebra of the coframing -/

private theorem e_ell_apply_of_fixed_aux (D : Cof k n M) (x z : D.S.Pre)
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

/-- `range (mfderiv v q) = range (P q)`. -/
private theorem range_vLin_eq_range_P_aux (D : Cof k n M) {q : D.S.Pre} :
    (vLin D q).toLinearMap.range = (D.P (q : M)).toLinearMap.range := by
  have hlinkq : Set.range (vLin D q) = {z | D.P (q : M) z = z} := D.hlink (q : M) q.2
  refine le_antisymm ?_ ?_
  · intro z hz
    rw [LinearMap.mem_range] at hz ⊢
    obtain ⟨y, rfl⟩ := hz
    have hm : (vLin D q) y ∈ Set.range (vLin D q) := ⟨y, rfl⟩
    rw [hlinkq] at hm
    exact ⟨_, hm⟩
  · intro z hz
    rw [LinearMap.mem_range] at hz ⊢
    obtain ⟨y, hy⟩ := hz
    have hfix : D.P (q : M) z = z := by
      rw [← hy]
      exact Work.PTGeometric.mem_Gr_apply_apply (D.hPgr (q : M)) y
    have : z ∈ Set.range (vLin D q) := by rw [hlinkq]; exact hfix
    obtain ⟨u, hu⟩ := this
    exact ⟨u, hu⟩

/-- `ker (ℓ j ∘ mfderiv v q) = ker (mfderiv v q)`. -/
private theorem ker_ell_comp_eq_aux (D : Cof k n M) (x : D.S.Pre) {q : D.S.Pre}
    (hq : q ∈ D.src x) :
    LinearMap.ker ((D.ℓ (D.jx x)).comp (vLin D q)).toLinearMap
      = LinearMap.ker (vLin D q).toLinearMap := by
  have hU : (q : M) ∈ D.U (D.jx x) := D.src_subset_U x hq
  refine le_antisymm ?_ ?_
  · intro w hw
    have hw' : (D.ℓ (D.jx x)) ((vLin D q) w) = 0 := hw
    have hfix : D.P (q : M) ((vLin D q) w) = (vLin D q) w := by
      have hlinkq : Set.range (vLin D q) = {z | D.P (q : M) z = z} := D.hlink (q : M) q.2
      have hm : (vLin D q) w ∈ Set.range (vLin D q) := ⟨w, rfl⟩
      rwa [hlinkq] at hm
    have h1 := e_ell_apply_of_fixed_aux D x q hU hfix
    rw [hw', map_zero] at h1
    exact h1.symm
  · intro w hw
    have hw' : (vLin D q) w = 0 := hw
    refine LinearMap.mem_ker.mpr ?_
    change (D.ℓ (D.jx x)) ((vLin D q) w) = 0
    rw [hw', map_zero]

/-- `finrank (ker (mfderiv v q)) = 9`. -/
private theorem finrank_ker_vLin_aux (D : Cof k n M) (q : D.S.Pre) :
    Module.finrank ℝ (LinearMap.ker (vLin D q).toLinearMap) = 9 := by
  have hrange := range_vLin_eq_range_P_aux D (q := q)
  have hk : Module.finrank ℝ (LinearMap.range (vLin D q).toLinearMap) = k := by
    rw [hrange]
    exact Work.PTGeometric.finrank_range_mem_Gr (D.hPgr (q : M))
  have hrn := LinearMap.finrank_range_add_finrank_ker (vLin D q).toLinearMap
  have hmod : Module.finrank ℝ (ModN k) = 9 + k := by
    show Module.finrank ℝ (EuclideanSpace ℝ (Fin ((8 + k) + 1))) = 9 + k
    rw [finrank_euclideanSpace]
    simp only [Fintype.card_fin]
    omega
  rw [hk, hmod] at hrn
  omega

/-- `range (chartIota x) = ker (aLin x)`. -/
private theorem range_chartIota_eq_ker_aLin_aux (D : Cof k n M) (x : D.S.Pre) :
    LinearMap.range (D.S.chartIota x).toLinearMap = LinearMap.ker (D.S.aLin x).toLinearMap := by
  refine le_antisymm ?_ ?_
  · rintro v ⟨y, rfl⟩
    exact Work.PTGeometric.Lvl.Setup.chartIota_mem_ker D.S x y
  · intro v hv
    exact ⟨D.S.chartBeta x v, Work.PTGeometric.Lvl.Setup.chartIota_beta D.S x hv⟩

private theorem chartIota_injective_aux (D : Cof k n M) (x : D.S.Pre) :
    Function.Injective (D.S.chartIota x) := by
  intro a b hab
  have h : (D.S.chartBeta x) ((D.S.chartIota x) a) = (D.S.chartBeta x) ((D.S.chartIota x) b) := by
    rw [hab]
  rwa [Work.PTGeometric.Lvl.Setup.chartBeta_iota, Work.PTGeometric.Lvl.Setup.chartBeta_iota]
    at h

/-- The transition `e → e` of an extended chart is locally the identity. -/
private theorem tcD_self_eventuallyEq_aux {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {M' : Type*} [TopologicalSpace M']
    (I : ModelWithCorners 𝕜 E H) (e : OpenPartialHomeomorph M' H)
    {x : M'} (hx : x ∈ e.source) (hint : (e.extend I) x ∈ interior (range (I : H → E))) :
    I.extendCoordChange e e =ᶠ[𝓝 ((e.extend I) x)] id := by
  have htarget : (e.extend I).target ∈ 𝓝 ((e.extend I) x) := by
    rw [OpenPartialHomeomorph.extend_target]
    refine Filter.inter_mem ?_ ?_
    · refine I.continuous_symm.continuousAt.preimage_mem_nhds ?_
      have h1 : I.symm ((e.extend I) x) = e x := by
        rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply, ModelWithCorners.left_inv]
      rw [h1]
      exact e.open_target.mem_nhds (e.map_source hx)
    · exact mem_of_superset (isOpen_interior.mem_nhds hint) interior_subset
  filter_upwards [htarget] with z hz
  show (e.extend I) ((e.extend I).symm z) = z
  exact (e.extend I).right_inv hz

/-- **`Cx x q` is injective.** -/
private theorem ker_Cx_eq_bot_aux (D : Cof k n M) (x : D.S.Pre) {q : D.S.Pre} (hq : q ∈ D.src x)
    (hint : (q : M) ∈ (𝓡∂ (NN k)).interior M) :
    LinearMap.ker (D.Cx x (q : M)).toLinearMap = ⊥ := by
  set p : M := (q : M) with hp
  have hn : (((⊤ : ENat) : WithTop ENat) : ℕ∞ω) ≠ 0 := by simp
  have hxcs : q ∈ D.S.chartSource x := D.src_subset_chartSource x hq
  have hxsrc : p ∈ (D.domChart x).source := hxcs.1
  have haqsrc : p ∈ (D.ambChart q).source := by simp [Cof.ambChart, hp]
  have hdomxmax : D.domChart x ∈ IsManifold.maximalAtlas (𝓡∂ (NN k))
      ((⊤ : ENat) : WithTop ENat) M :=
    Work.PTGeometric.Lvl.Setup.domChartAt_mem_maximalAtlas D.S x
  have haqmax : D.ambChart q ∈ IsManifold.maximalAtlas (𝓡∂ (NN k))
      ((⊤ : ENat) : WithTop ENat) M :=
    IsManifold.chart_mem_maximalAtlas (q : M)
  have hintDomx : (D.domChart x).extend (𝓡∂ (NN k)) p ∈ interior (range (𝓡∂ (NN k))) :=
    tcD_mem_interior_range (𝓡∂ (NN k)) hn hdomxmax hxsrc hint
  have hintAmb : (D.ambChart q).extend (𝓡∂ (NN k)) p ∈ interior (range (𝓡∂ (NN k))) :=
    tcD_mem_interior_range (𝓡∂ (NN k)) hn haqmax haqsrc hint
  have hdF : DifferentiableAt ℝ
      (⇑((𝓡∂ (NN k)).extendCoordChange (D.domChart x) (D.ambChart q))) (D.domExt x p) :=
    tcD_differentiableAt (𝓡∂ (NN k)) hn hdomxmax haqmax hxsrc haqsrc hintDomx
  have hdL : DifferentiableAt ℝ
      (⇑((𝓡∂ (NN k)).extendCoordChange (D.ambChart q) (D.domChart x))) (D.ambExt q p) :=
    tcD_differentiableAt (𝓡∂ (NN k)) hn haqmax hdomxmax haqsrc hxsrc hintAmb
  have hv : ((𝓡∂ (NN k)).extendCoordChange (D.domChart x) (D.ambChart q)) (D.domExt x p)
      = D.ambExt q p :=
    tcD_apply_extend (𝓡∂ (NN k)) (D.domChart x) (D.ambChart q) hxsrc
  have hev1 : (((𝓡∂ (NN k)).extendCoordChange (D.ambChart q) (D.domChart x)) ∘
        ((𝓡∂ (NN k)).extendCoordChange (D.domChart x) (D.ambChart q)))
      =ᶠ[𝓝 (D.domExt x p)]
        ((𝓡∂ (NN k)).extendCoordChange (D.domChart x) (D.domChart x)) :=
    tcD_comp_eventuallyEq (𝓡∂ (NN k)) (D.domChart x) (D.ambChart q) (D.domChart x) hxsrc haqsrc
  have hev2 : ((𝓡∂ (NN k)).extendCoordChange (D.domChart x) (D.domChart x))
      =ᶠ[𝓝 (D.domExt x p)] id :=
    tcD_self_eventuallyEq_aux (𝓡∂ (NN k)) (D.domChart x) hxsrc hintDomx
  have hev : (((𝓡∂ (NN k)).extendCoordChange (D.ambChart q) (D.domChart x)) ∘
        ((𝓡∂ (NN k)).extendCoordChange (D.domChart x) (D.ambChart q)))
      =ᶠ[𝓝 (D.domExt x p)] id := hev1.trans hev2
  have hL : HasFDerivAt (⇑((𝓡∂ (NN k)).extendCoordChange (D.ambChart q) (D.domChart x)))
      (fderiv ℝ (⇑((𝓡∂ (NN k)).extendCoordChange (D.ambChart q) (D.domChart x)))
        (D.ambExt q p))
      (((𝓡∂ (NN k)).extendCoordChange (D.domChart x) (D.ambChart q)) (D.domExt x p)) := by
    rw [hv]
    exact hdL.hasFDerivAt
  have hF : HasFDerivAt (⇑((𝓡∂ (NN k)).extendCoordChange (D.domChart x) (D.ambChart q)))
      (D.Cx x p) (D.domExt x p) := hdF.hasFDerivAt
  have hcomp := hL.comp (D.domExt x p) hF
  have h1 : HasFDerivAt id
      ((fderiv ℝ (⇑((𝓡∂ (NN k)).extendCoordChange (D.ambChart q) (D.domChart x)))
        (D.ambExt q p)).comp (D.Cx x p)) (D.domExt x p) :=
    hcomp.congr_of_eventuallyEq hev.symm
  have huniq : ContinuousLinearMap.id ℝ (ModN k)
      = (fderiv ℝ (⇑((𝓡∂ (NN k)).extendCoordChange (D.ambChart q) (D.domChart x)))
        (D.ambExt q p)).comp (D.Cx x p) :=
    (hasFDerivAt_id (D.domExt x p)).unique h1
  rw [LinearMap.ker_eq_bot]
  intro a b hab
  have h2 : (D.Cx x p) a = (D.Cx x p) b := hab
  have h3 : a = ((fderiv ℝ (⇑((𝓡∂ (NN k)).extendCoordChange (D.ambChart q) (D.domChart x)))
        (D.ambExt q p)).comp (D.Cx x p)) a := by
    rw [← huniq]; rfl
  have h4 : ((fderiv ℝ (⇑((𝓡∂ (NN k)).extendCoordChange (D.ambChart q) (D.domChart x)))
        (D.ambExt q p)).comp (D.Cx x p)) b = b := by
    rw [← huniq]; rfl
  rw [h3, ContinuousLinearMap.comp_apply, h2, ← ContinuousLinearMap.comp_apply, h4]


/-- **The level-set tangent directions are killed by `dv`.**  This is the geometric input of
`range_chartIota_eq_ker_Omega`: the direction `Cx x q (chartIota x w)` is the velocity at `0` of a
curve through `q` that lies in `W`, so `mfderiv v q` kills it.  The curve is
`t ↦ (domChartAt x).extend.symm (domExt x q + t • chartIota x w)`: its points are in `W` near `0`
because in the normal-form chart at `x` the level set `W ∩ U x` is the zero set of
`aLin x ∘ domExt x`, and `aLin x (domExt x q + t • chartIota x w) = aLin x (chartZ x)` for every
`t` (`chartIota` lands in `ker (aLin x)` and `aLin x (domExt x q) = aLin x (chartZ x)`). -/
private theorem mfderiv_Cx_chartIota_aux (D : Cof k n M) (x : D.S.Pre) {q : D.S.Pre} (hq : q ∈ D.src x)
    (hint : (q : M) ∈ (𝓡∂ (NN k)).interior M) (w : EuclideanSpace ℝ (Fin 9)) :
    (vLin D q) (D.Cx x (q : M) (D.S.chartIota x w)) = 0 := by
  have hn : (((⊤ : ENat) : WithTop ENat) : ℕ∞ω) ≠ 0 := by simp
  have hxcs : q ∈ D.S.chartSource x := D.src_subset_chartSource x hq
  have hxsrc : (q : M) ∈ (D.domChart x).source := hxcs.1
  have haqsrc : (q : M) ∈ (D.ambChart q).source := mem_chart_source _ _
  have hdomxmax : D.domChart x ∈ IsManifold.maximalAtlas (𝓡∂ (NN k))
      ((⊤ : ENat) : WithTop ENat) M :=
    Work.PTGeometric.Lvl.Setup.domChartAt_mem_maximalAtlas D.S x
  have haqmax : D.ambChart q ∈ IsManifold.maximalAtlas (𝓡∂ (NN k))
      ((⊤ : ENat) : WithTop ENat) M :=
    IsManifold.chart_mem_maximalAtlas (q : M)
  have hintDomx : (D.domChart x).extend (𝓡∂ (NN k)) (q : M) ∈ interior (range (𝓡∂ (NN k))) :=
    tcD_mem_interior_range (𝓡∂ (NN k)) hn hdomxmax hxsrc hint
  have hintAmb : (D.ambChart q).extend (𝓡∂ (NN k)) (q : M) ∈ interior (range (𝓡∂ (NN k))) :=
    tcD_mem_interior_range (𝓡∂ (NN k)) hn haqmax haqsrc hint
  -- the derivative of the chart transition
  have hdF : DifferentiableAt ℝ
      (⇑((𝓡∂ (NN k)).extendCoordChange (D.domChart x) (D.ambChart q))) (D.domExt x (q : M)) :=
    tcD_differentiableAt (𝓡∂ (NN k)) hn hdomxmax haqmax hxsrc haqsrc hintDomx
  -- `dv` read in the ambient chart at `q`
  have hdv : MDifferentiableAt (𝓡∂ (NN k))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) D.v (q : M) :=
    D.hvsm.contMDiffAt.mdifferentiableAt (by simp)
  have hW' := Work.PTGeometric.hasFDerivWithinAt_comp_extChartAt_symm
    (I := 𝓡∂ (NN k)) (f := D.v) (x := (q : M)) hdv
  have hmem : Set.range (𝓡∂ (NN k)) ∈ 𝓝 (D.ambExt q (q : M)) :=
    mem_of_superset (isOpen_interior.mem_nhds hintAmb) interior_subset
  have hgAt : HasFDerivAt (fun z : ModN k => D.v ((D.ambExt q).symm z)) (vLin D q)
      (D.ambExt q (q : M)) :=
    hW'.hasFDerivAt hmem
  have hv : (⇑((𝓡∂ (NN k)).extendCoordChange (D.domChart x) (D.ambChart q))) (D.domExt x (q : M))
      = D.ambExt q (q : M) :=
    tcD_apply_extend (𝓡∂ (NN k)) (D.domChart x) (D.ambChart q) hxsrc
  have hgAt' : HasFDerivAt (fun z : ModN k => D.v ((D.ambExt q).symm z)) (vLin D q)
      ((⇑((𝓡∂ (NN k)).extendCoordChange (D.domChart x) (D.ambChart q))) (D.domExt x (q : M))) := by
    rw [hv]; exact hgAt
  have hF' : HasFDerivAt (⇑((𝓡∂ (NN k)).extendCoordChange (D.domChart x) (D.ambChart q)))
      (D.Cx x (q : M)) (D.domExt x (q : M)) := hdF.hasFDerivAt
  have hcomp := hgAt'.comp (D.domExt x (q : M)) hF'
  -- the composite agrees with `z ↦ v (domInv x z)` near the base point
  have hsrcEq : (D.ambExt q).source = (D.ambChart q).source :=
    OpenPartialHomeomorph.extend_source (D.ambChart q)
  have hcont : ContinuousAt (fun z : ModN k => (D.domExt x).symm z) (D.domExt x (q : M)) :=
    OpenPartialHomeomorph.continuousAt_extend_symm (D.domChart x) hxsrc
  have hleft : (D.domExt x).symm (D.domExt x (q : M)) = (q : M) :=
    OpenPartialHomeomorph.extend_left_inv (D.domChart x) hxsrc
  have hev_mem : ∀ᶠ z in 𝓝 (D.domExt x (q : M)), (D.domExt x).symm z ∈ (D.ambChart q).source := by
    have h1 : (D.domExt x).symm (D.domExt x (q : M)) ∈ (D.ambChart q).source := by
      rw [hleft]; exact haqsrc
    exact hcont.preimage_mem_nhds ((D.ambChart q).open_source.mem_nhds h1)
  have hev : (fun z : ModN k => D.v ((D.domExt x).symm z))
      =ᶠ[𝓝 (D.domExt x (q : M))]
        (fun z : ModN k => D.v ((D.ambExt q).symm
          ((⇑((𝓡∂ (NN k)).extendCoordChange (D.domChart x) (D.ambChart q))) z))) := by
    filter_upwards [hev_mem] with z hz
    have hz' : (D.domExt x).symm z ∈ (D.ambExt q).source := by
      rw [hsrcEq]; exact hz
    rw [show (⇑((𝓡∂ (NN k)).extendCoordChange (D.domChart x) (D.ambChart q))) z
        = D.ambExt q ((D.domExt x).symm z) from by
      simp only [ModelWithCorners.extendCoordChange, PartialEquiv.trans_apply]]
    rw [show (D.ambExt q).symm (D.ambExt q ((D.domExt x).symm z)) = (D.domExt x).symm z from
      PartialEquiv.left_inv (D.ambExt q) hz']
  have hE : HasFDerivAt (fun z : ModN k => D.v ((D.domExt x).symm z))
      ((vLin D q).comp (D.Cx x (q : M))) (D.domExt x (q : M)) :=
    hcomp.congr_of_eventuallyEq hev
  -- the affine line and its derivative
  have hline : HasDerivAt (fun t : ℝ => D.domExt x (q : M) + t • (D.S.chartIota x w))
      (D.S.chartIota x w) (0 : ℝ) := by
    have h1 : HasDerivAt (fun t : ℝ => t • (D.S.chartIota x w)) (D.S.chartIota x w) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const (D.S.chartIota x w)
    simpa using h1.const_add (D.domExt x (q : M))
  have hE' : HasFDerivAt (fun z : ModN k => D.v ((D.domExt x).symm z))
      ((vLin D q).comp (D.Cx x (q : M)))
      (D.domExt x (q : M) + (0 : ℝ) • (D.S.chartIota x w)) := by
    simpa using hE
  have hderiv := hE'.comp_hasDerivAt (0 : ℝ) hline
  -- the curve stays in `W` near `0`, so the function is eventually zero
  have htarget_nhds : (D.domExt x).target ∈ 𝓝 (D.domExt x (q : M)) := by
    have hV : IsOpen ((𝓡∂ (NN k)).symm ⁻¹' (D.S.domChartAt x).target
        ∩ interior (range (𝓡∂ (NN k)))) :=
      ((D.S.domChartAt x).open_target.preimage (𝓡∂ (NN k)).continuous_symm).inter isOpen_interior
    have hmemV : D.domExt x (q : M) ∈ (𝓡∂ (NN k)).symm ⁻¹' (D.S.domChartAt x).target
        ∩ interior (range (𝓡∂ (NN k))) := by
      refine ⟨?_, hintDomx⟩
      show (𝓡∂ (NN k)).symm (D.domExt x (q : M)) ∈ (D.S.domChartAt x).target
      rw [show D.domExt x (q : M) = (𝓡∂ (NN k)) ((D.S.domChartAt x) (q : M)) from rfl,
        (𝓡∂ (NN k)).left_inv]
      exact (D.S.domChartAt x).map_source hxsrc
    refine mem_of_superset (hV.mem_nhds hmemV) ?_
    intro z hz
    rw [OpenPartialHomeomorph.extend_target]
    exact ⟨hz.1, interior_subset hz.2⟩
  have hcurve_cont : ContinuousAt (fun t : ℝ => D.domExt x (q : M) + t • (D.S.chartIota x w)) 0 :=
    (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
  have htarget_ev : ∀ᶠ t in 𝓝 (0 : ℝ),
      D.domExt x (q : M) + t • (D.S.chartIota x w) ∈ (D.domExt x).target := by
    have htn : (D.domExt x).target ∈
        𝓝 (D.domExt x (q : M) + (0 : ℝ) • (D.S.chartIota x w)) := by simpa using htarget_nhds
    have := hcurve_cont.eventually_mem htn
    simpa using this
  have hUsev : ∀ᶠ t in 𝓝 (0 : ℝ),
      (D.domExt x).symm (D.domExt x (q : M) + t • (D.S.chartIota x w)) ∈ D.L.U x := by
    have hcont1 : ContinuousAt (fun z : ModN k => (D.domExt x).symm z)
        (D.domExt x (q : M) + (0 : ℝ) • (D.S.chartIota x w)) := by simpa using hcont
    have hcont2 : ContinuousAt (fun t : ℝ =>
        (D.domExt x).symm (D.domExt x (q : M) + t • (D.S.chartIota x w))) 0 :=
      ContinuousAt.comp hcont1 hcurve_cont
    have h0 : (D.domExt x).symm (D.domExt x (q : M) + (0 : ℝ) • (D.S.chartIota x w)) = (q : M) := by
      rw [zero_smul, add_zero]; exact hleft
    have hmemq : (D.domExt x).symm (D.domExt x (q : M) + (0 : ℝ) • (D.S.chartIota x w)) ∈ D.L.U x := by
      rw [h0]
      exact hxcs.2.2
    exact hcont2.eventually_mem ((D.L.isOpen_U x).mem_nhds hmemq)
  have hchartZ : (D.S.codChartAt x) 0 = (D.S.aLin x) (D.S.chartZ x) := by
    rw [← D.S.localMap_self x, D.S.codChartAt_localMap x (D.S.mem_domChartAt_source x)]
    rfl
  have hev0 : (fun t : ℝ => D.v ((D.domExt x).symm (D.domExt x (q : M) + t • (D.S.chartIota x w))))
      =ᶠ[𝓝 (0 : ℝ)] (fun _ => 0) := by
    filter_upwards [hUsev, htarget_ev] with t htU htT
    have hy_src : (D.domExt x).symm (D.domExt x (q : M) + t • (D.S.chartIota x w))
        ∈ (D.S.domChartAt x).source := by
      rw [← OpenPartialHomeomorph.extend_source (I := 𝓡∂ (NN k)) (D.S.domChartAt x)]
      exact PartialEquiv.map_target (D.domExt x) htT
    have hlin : (D.S.aLin x) (D.domExt x (q : M) + t • (D.S.chartIota x w))
        = (D.S.aLin x) (D.S.chartZ x) := by
      rw [map_add, map_smul, Work.PTGeometric.Lvl.Setup.chartIota_mem_ker, smul_zero, add_zero]
      exact Work.PTGeometric.Lvl.Setup.aLin_extend_eq D.S x hxcs
    have hcod : (D.S.codChartAt x) (D.S.localMap x
          ((D.domExt x).symm (D.domExt x (q : M) + t • (D.S.chartIota x w))))
        = (D.S.codChartAt x) 0 := by
      rw [D.S.codChartAt_localMap x hy_src, PartialEquiv.right_inv (D.domExt x) htT]
      show (D.S.aLin x) (D.domExt x (q : M) + t • (D.S.chartIota x w)) = (D.S.codChartAt x) 0
      rw [hlin, hchartZ]
    have hmem1 : D.S.localMap x ((D.domExt x).symm
        (D.domExt x (q : M) + t • (D.S.chartIota x w))) ∈ (D.S.codChartAt x).source :=
      D.S.domChartAt_source_subset x hy_src
    have hmem2 : (0 : EuclideanSpace ℝ (Fin k)) ∈ (D.S.codChartAt x).source := by
      rw [← D.S.localMap_self x]
      exact D.S.domChartAt_source_subset x (D.S.mem_domChartAt_source x)
    have hg0 : D.S.localMap x ((D.domExt x).symm
        (D.domExt x (q : M) + t • (D.S.chartIota x w))) = 0 := by
      calc D.S.localMap x ((D.domExt x).symm (D.domExt x (q : M) + t • (D.S.chartIota x w)))
          = (D.S.codChartAt x).symm ((D.S.codChartAt x) (D.S.localMap x
              ((D.domExt x).symm (D.domExt x (q : M) + t • (D.S.chartIota x w))))) :=
            (PartialEquiv.left_inv _ hmem1).symm
        _ = (D.S.codChartAt x).symm ((D.S.codChartAt x) 0) := by rw [hcod]
        _ = 0 := PartialEquiv.left_inv _ hmem2
    have hWmem : (D.domExt x).symm (D.domExt x (q : M) + t • (D.S.chartIota x w)) ∈ D.W :=
      (D.L.zero_iff x _ htU).mp hg0
    simpa [D.hW] using hWmem
  have h2 : HasDerivAt (fun t : ℝ =>
      D.v ((D.domExt x).symm (D.domExt x (q : M) + t • (D.S.chartIota x w)))) 0 0 :=
    (hev0.hasDerivAt_iff).mpr (hasDerivAt_const (0 : ℝ) (0 : EuclideanSpace ℝ (Fin n)))
  have hzero : ((vLin D q).comp (D.Cx x (q : M))) (D.S.chartIota x w) = 0 := hderiv.unique h2
  simpa [ContinuousLinearMap.comp_apply] using hzero

/-! ## The target -/

theorem range_chartIota_eq_ker_Omega
    {k n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) ((⊤ : ENat) : WithTop ENat) M]
    (D : Work.ThomBordism.CofAtlas.Cof k n M) (x : D.S.Pre) {q : D.S.Pre} (hq : q ∈ D.src x)
    (hint : (q : M) ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).interior M) :
    LinearMap.range (D.S.chartIota x).toLinearMap
      = LinearMap.ker (D.Omega x (q : M)).toLinearMap := by
  set p : M := (q : M) with hp
  have hker : LinearMap.ker (D.Omega x p).toLinearMap
      = (LinearMap.ker (vLin D q).toLinearMap).comap (D.Cx x p).toLinearMap := by
    have h1 : (D.Omega x p).toLinearMap
        = ((D.ℓ (D.jx x)).comp (vLin D q)).toLinearMap.comp (D.Cx x p).toLinearMap := rfl
    rw [h1, LinearMap.ker_comp, ker_ell_comp_eq_aux D x hq]
  rw [hker]
  have hCxker : LinearMap.ker (D.Cx x p).toLinearMap = ⊥ := by
    rw [hp]
    exact ker_Cx_eq_bot_aux D x hq (by rw [← hp]; exact hint)
  have hle : (LinearMap.range (D.S.chartIota x).toLinearMap).map (D.Cx x p).toLinearMap
      ≤ LinearMap.ker (vLin D q).toLinearMap := by
    intro u hu
    rw [Submodule.mem_map] at hu
    obtain ⟨w, hw, rfl⟩ := hu
    obtain ⟨y, hy⟩ := hw
    rw [← hy]
    exact mfderiv_Cx_chartIota_aux D x hq (by rw [← hp]; exact hint) y
  have hfin1 : Module.finrank ℝ
      ↥((LinearMap.range (D.S.chartIota x).toLinearMap).map (D.Cx x p).toLinearMap) = 9 := by
    have hinj : Function.Injective
        (fun w : ↥(LinearMap.range (D.S.chartIota x).toLinearMap) => (D.Cx x p) w) := by
      intro a b hab
      exact Subtype.ext (LinearMap.ker_eq_bot.mp hCxker hab)
    have hrange : LinearMap.range (((D.Cx x p).toLinearMap).comp
        (LinearMap.range (D.S.chartIota x).toLinearMap).subtype)
        = (LinearMap.range (D.S.chartIota x).toLinearMap).map (D.Cx x p).toLinearMap := by
      ext z
      simp only [LinearMap.mem_range, Submodule.mem_map]
      constructor
      · rintro ⟨w, hw⟩
        exact ⟨w, w.2, hw⟩
      · rintro ⟨w, hw, hwz⟩
        exact ⟨⟨w, hw⟩, hwz⟩
    rw [← hrange, LinearMap.finrank_range_of_inj hinj,
      LinearMap.finrank_range_of_inj (chartIota_injective_aux D x)]
    simp [finrank_euclideanSpace]
  have hfin2 : Module.finrank ℝ ↥(LinearMap.ker (vLin D q).toLinearMap) = 9 :=
    finrank_ker_vLin_aux D q
  have heq : (LinearMap.range (D.S.chartIota x).toLinearMap).map (D.Cx x p).toLinearMap
      = LinearMap.ker (vLin D q).toLinearMap :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hfin1, hfin2])
  rw [← heq, Submodule.comap_map_eq, hCxker, sup_bot_eq]

end

end Work.ThomBordism.CofAtlas
