import Mathlib
import Submission.Work.ThomBordism.levelSet_positiveAtlas_of_coframing
import Submission.Work.ThomBordism.isHalfOrientationFamily_relChainsInclPunct
import Submission.Work.ThomBordism.explicitOrientationFamily
import Submission.Work.ThomBordism.CollarInstanceCongr
import Submission.Work.ThomBordism.CofAtlas.Structure
import Submission.Work.ThomBordism.CofAtlas.newBoundary
import Submission.Work.ThomBordism.CofAtlas.newIsManifold
import Submission.Work.ThomBordism.CofAtlas.newTransition_det_pos
import Submission.Work.ThomBordism.CofAtlas.det_newTransition
import Submission.Work.ThomBordism.CofAtlas.sgnConst
import Submission.Work.ThomBordism.CofAtlas.tauConst
import Submission.Work.ThomBordism.PosAtlas.chartTrChangeSigned

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The value of an orientation family of a coframed level set

`Work.ThomBordism.orientationFamily_valued_of_coframing`: for the coframed level set `D.S.Pre` of a
`Cof` datum `D`, carrying a collar, there is a half-orientation family `γ` whose value at every
interior point is *explicitly* `flipSign x` times the chart transfer of the Euclidean local generator
along the `Lvl` chart at `x`.

The family is the family of local classes of one global relative fundamental class `w`.  The class is
produced in the *corrected* charted space `CofAtlas.newChartedSpace D` (which is positively oriented,
`CofAtlas.newTransition_det_pos`), where the family of chart transfers of the Euclidean generator is
known to be a half-orientation family (`Work.PTGeometric.exists_halfOrientationFamily_of_det_pos`, in
the explicit form `Work.ThomBordism.explicitOrientationFamily`), so that
`Work.ThomBordism.exists_relFundClass_of_explicitFamily` gives `w` with that local class at every
interior point.  The corrected chart at `x` is the `Lvl` chart at `x` post-composed with the
reflection `reflectMap x` (whose determinant sign is `flipSign x`, `CofAtlas.reflectLin_det`), so the
signed change of charts for the local generator (`Work.ThomBordism.PosAtlas.chartTrChangeSigned`,
applied to the derivative `reflectLin D x`) converts the value to `flipSign x • (Lvl chart transfer)`.
The class is then transported to the relative chain complex of `D.S.Pre` with the *same* boundary, and
`Work.ThomBordism.isHalfOrientationFamily_relChainsInclPunct` upgrades its local classes to a
half-orientation family.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Manifold ContDiff Topology
open Function Set Topology ModelWithCorners Filter
open Work.PTGeometric

namespace Work.ThomBordism

namespace CofAtlas

noncomputable section

variable {k n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
  [IsManifold (𝓡∂ ((8 + k) + 1)) ((⊤ : ENat) : WithTop ENat) M]

theorem newManifold_one (D : Cof k n M) :
    @IsManifold ℝ _ (EuclideanSpace ℝ (Fin 9)) _ _ (EuclideanHalfSpace 9) _ (𝓡∂ 9) 1 D.S.Pre _
      (CofAtlas.newChartedSpace D) :=
  @IsManifold.of_le ℝ _ (EuclideanSpace ℝ (Fin 9)) _ _ (EuclideanHalfSpace 9) _ (𝓡∂ 9) D.S.Pre _
    (CofAtlas.newChartedSpace D) 1 ((⊤:ENat):WithTop ENat) (by simp) (CofAtlas.newIsManifold D)

/-- The `IsManifold`-at-`1` structure of the `Lvl` charted space. -/
theorem lvlManifold_one (D : Cof k n M) :
    @IsManifold ℝ _ (EuclideanSpace ℝ (Fin 9)) _ _ (EuclideanHalfSpace 9) _ (𝓡∂ 9) 1 D.S.Pre _
      (Work.PTGeometric.Lvl.Setup.instChartedSpace D.S) :=
  @IsManifold.of_le ℝ _ (EuclideanSpace ℝ (Fin 9)) _ _ (EuclideanHalfSpace 9) _ (𝓡∂ 9) D.S.Pre _
    (Work.PTGeometric.Lvl.Setup.instChartedSpace D.S) 1 ((⊤:ENat):WithTop ENat) (by simp)
    (Work.PTGeometric.Lvl.Setup.instIsManifold D.S)

/-- The interior chart at `x` of the corrected charted space. -/
noncomputable abbrev icN (D : Cof k n M) (x : D.S.Pre) :
    OpenPartialHomeomorph D.S.Pre (EuclideanSpace ℝ (Fin 9)) :=
  @Work.PTGeometric.icChart 8 (TopCat.of D.S.Pre) _ (CofAtlas.newChartedSpace D) (newManifold_one D) x

/-- The interior chart at `x` of the `Lvl` charted space. -/
noncomputable abbrev icL (D : Cof k n M) (x : D.S.Pre) :
    OpenPartialHomeomorph D.S.Pre (EuclideanSpace ℝ (Fin 9)) :=
  @Work.PTGeometric.icChart 8 (TopCat.of D.S.Pre) _ (Work.PTGeometric.Lvl.Setup.instChartedSpace D.S)
    (lvlManifold_one D) x

/-- The boundary of the `Lvl` charted space. -/
abbrev BL (D : Cof k n M) : Set D.S.Pre :=
  @ModelWithCorners.boundary ℝ _ (EuclideanSpace ℝ (Fin 9)) _ _ (EuclideanHalfSpace 9) _
    (𝓡∂ 9) D.S.Pre _ (Work.PTGeometric.Lvl.Setup.instChartedSpace D.S)

theorem icN_coe (D : Cof k n M) (x : D.S.Pre) :
    ⇑(icN D x) = ⇑((D.newChart x).extend (𝓡∂ 9)) := by
  letI : ChartedSpace (EuclideanHalfSpace 9) D.S.Pre := CofAtlas.newChartedSpace D
  letI : IsManifold (𝓡∂ 9) 1 D.S.Pre := newManifold_one D
  rw [icN, Work.PTGeometric.icChart_coe]
  show ⇑(extChartAt (𝓡∂ 9) x) = _
  rw [extChartAt_coe, CofAtlas.newChartedSpace_chartAt]
  rfl

theorem icN_coe_symm (D : Cof k n M) (x : D.S.Pre) :
    ⇑(icN D x).symm = ⇑((D.newChart x).extend (𝓡∂ 9)).symm := by
  letI : ChartedSpace (EuclideanHalfSpace 9) D.S.Pre := CofAtlas.newChartedSpace D
  letI : IsManifold (𝓡∂ 9) 1 D.S.Pre := newManifold_one D
  rw [icN, Work.PTGeometric.icChart_coe_symm]
  show ⇑(extChartAt (𝓡∂ 9) x).symm = _
  rw [extChartAt_coe_symm, CofAtlas.newChartedSpace_chartAt]
  rfl

theorem icN_target (D : Cof k n M) (x : D.S.Pre) :
    (icN D x).target = interior ((D.newChart x).extend (𝓡∂ 9)).target := by
  letI : ChartedSpace (EuclideanHalfSpace 9) D.S.Pre := CofAtlas.newChartedSpace D
  letI : IsManifold (𝓡∂ 9) 1 D.S.Pre := newManifold_one D
  rw [icN, Work.PTGeometric.icChart_target]
  show interior (extChartAt (𝓡∂ 9) x).target = _
  congr 1

theorem icL_coe (D : Cof k n M) (x : D.S.Pre) :
    ⇑(icL D x) = ⇑(D.lvlExt x) := by
  letI : ChartedSpace (EuclideanHalfSpace 9) D.S.Pre :=
    Work.PTGeometric.Lvl.Setup.instChartedSpace D.S
  letI : IsManifold (𝓡∂ 9) 1 D.S.Pre := lvlManifold_one D
  rw [icL, Work.PTGeometric.icChart_coe]
  rfl

theorem icL_coe_symm (D : Cof k n M) (x : D.S.Pre) :
    ⇑(icL D x).symm = ⇑(D.lvlExt x).symm := by
  letI : ChartedSpace (EuclideanHalfSpace 9) D.S.Pre :=
    Work.PTGeometric.Lvl.Setup.instChartedSpace D.S
  letI : IsManifold (𝓡∂ 9) 1 D.S.Pre := lvlManifold_one D
  rw [icL, Work.PTGeometric.icChart_coe_symm]
  rfl

theorem icL_target (D : Cof k n M) (x : D.S.Pre) :
    (icL D x).target = interior (D.lvlExt x).target := by
  letI : ChartedSpace (EuclideanHalfSpace 9) D.S.Pre :=
    Work.PTGeometric.Lvl.Setup.instChartedSpace D.S
  letI : IsManifold (𝓡∂ 9) 1 D.S.Pre := lvlManifold_one D
  rw [icL, Work.PTGeometric.icChart_target]
  rfl

theorem hasFDerivAt_icN_icL (D : Cof k n M) (x : D.S.Pre)
    (hxM : (x : M) ∉ (𝓡∂ ((8 + k) + 1)).boundary M) :
    HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 9) => ⇑(icL D x) (⇑(icN D x).symm z))
      (reflectLin D x) (⇑(icN D x) x) := by
  -- the `Lvl` instances, for the lemmas about `icL`
  letI : ChartedSpace (EuclideanHalfSpace 9) D.S.Pre :=
    Work.PTGeometric.Lvl.Setup.instChartedSpace D.S
  letI : IsManifold (𝓡∂ 9) ((⊤:ENat):WithTop ENat) D.S.Pre :=
    Work.PTGeometric.Lvl.Setup.instIsManifold D.S
  letI : IsManifold (𝓡∂ 9) 1 D.S.Pre := lvlManifold_one D
  have hx : x ∉ (𝓡∂ 9).boundary D.S.Pre :=
    fun h => hxM ((Work.PTGeometric.Lvl.Setup.mem_boundary_iff D.S x).mp h)
  -- `x` lies in the source of `icL`
  have hxsrc : x ∈ (icL D x).source := by
    rw [icL]
    refine Work.PTGeometric.icChart_mem_source 8 (TopCat.of D.S.Pre) x x hx ?_
    rw [extChartAt_source]
    exact mem_chart_source (EuclideanHalfSpace 9) x
  -- the `Lvl` extended chart at `x` sends `x` into the interior of its target
  have hintL : ⇑(D.lvlExt x) x ∈ interior (D.lvlExt x).target := by
    have h1 : ⇑(icL D x) x ∈ (icL D x).target := (icL D x).map_source hxsrc
    rw [icL_coe, icL_target] at h1
    exact h1
  -- the centre
  set z₀ : EuclideanSpace ℝ (Fin 9) := ⇑((D.newChart x).extend (𝓡∂ 9)) x with hz₀def
  have hz₀_mem : z₀ ∈ ((D.newChart x).extend (𝓡∂ 9)).target := by
    rw [hz₀def]
    exact PartialEquiv.map_source _ (by
      rw [OpenPartialHomeomorph.extend_source, CofAtlas.newChart_source]
      exact D.mem_src_self x)
  have hreflz₀ : reflectLin D x z₀ = ⇑(D.lvlExt x) x := by
    rw [hz₀def, CofAtlas.newChart_extend_apply, CofAtlas.reflectLin_self]
  -- the eventual equality
  have hU2 : {z : EuclideanSpace ℝ (Fin 9) | reflectLin D x z ∈ interior (D.lvlExt x).target}
      ∈ 𝓝 z₀ := by
    refine (reflectLin D x).continuous.continuousAt.preimage_mem_nhds ?_
    rw [hreflz₀]
    exact IsOpen.mem_nhds isOpen_interior hintL
  -- the model half-space is a neighbourhood of `z₀` (its zeroth coordinate is positive)
  have hz₀pos : 0 < z₀.ofLp 0 := by
    have hz₀val : z₀ = reflectLin D x (⇑(D.lvlExt x) x) := by
      rw [hz₀def, CofAtlas.newChart_extend_apply]
    have h1 : z₀.ofLp 0 = (⇑(D.lvlExt x) x).ofLp 0 := by
      rw [hz₀val, reflectLin_coord_zero]
    have h2 : (⇑(D.lvlExt x) x).ofLp 0 = D.S.chartEps x := by
      rw [show ⇑(D.lvlExt x) x = ⇑((D.S.chartAt x).extend (𝓡∂ 9)) x from rfl,
        Work.PTGeometric.Lvl.Setup.chartAt_self_extend D.S x,
        Work.PTGeometric.Lvl.Setup.chartFun_self D.S x]
      simp [PiLp.smul_apply, Work.Surgery.e₀_apply_zero]
    rw [h1, h2]
    exact Work.PTGeometric.Lvl.Setup.chartEps_pos D.S x hxM
  have hU1 : {z : EuclideanSpace ℝ (Fin 9) | 0 ≤ z.ofLp 0} ∈ 𝓝 z₀ := by
    have hopen : IsOpen {z : EuclideanSpace ℝ (Fin 9) | 0 < z.ofLp 0} := by
      rw [← interior_halfSpace 2 (0 : ℝ) (0 : Fin 9)]
      exact isOpen_interior
    exact Filter.mem_of_superset (IsOpen.mem_nhds hopen hz₀pos)
      (fun w (hw : 0 < w.ofLp 0) => show 0 ≤ w.ofLp 0 from le_of_lt hw)
  have hev : (fun z => ⇑(D.lvlExt x) (⇑((D.newChart x).extend (𝓡∂ 9)).symm z))
      =ᶠ[𝓝 z₀] (fun z => reflectLin D x z) := by
    refine Filter.eventually_of_mem
      (U := {z : EuclideanSpace ℝ (Fin 9) | 0 ≤ z.ofLp 0} ∩
        {z : EuclideanSpace ℝ (Fin 9) | reflectLin D x z ∈ interior (D.lvlExt x).target})
      (Filter.inter_mem hU1 hU2) ?_
    intro z hz
    show ⇑(D.lvlExt x) (⇑((D.newChart x).extend (𝓡∂ 9)).symm z) = reflectLin D x z
    rw [CofAtlas.newChart_extend_symm_apply D x hz.1]
    exact PartialEquiv.right_inv (D.lvlExt x) (interior_subset hz.2)
  have hbase : HasFDerivAt (fun z => ⇑(D.lvlExt x) (⇑((D.newChart x).extend (𝓡∂ 9)).symm z))
      (reflectLin D x) z₀ :=
    (ContinuousLinearMap.hasFDerivAt (reflectLin D x)).congr_of_eventuallyEq hev
  -- transfer to the interior charts
  have hfun : (fun z => ⇑(D.lvlExt x) (⇑((D.newChart x).extend (𝓡∂ 9)).symm z))
      = (fun z => ⇑(icL D x) (⇑(icN D x).symm z)) := by
    funext z
    rw [icL_coe, icN_coe_symm]
  rw [← hfun, icN_coe]
  exact hbase

theorem signType_if (s : SignType) :
    (if 0 < (s : ℝ) then (1:ℤ) else -1) = (if s = 1 then 1 else -1) := by
  cases s <;> simp

theorem flipSign_ne_zero (D : Cof k n M) (x : D.S.Pre)
    (hx : (x : M) ∉ (𝓡∂ ((8 + k) + 1)).boundary M) : D.flipSign x ≠ 0 := by
  have hsgn : D.sgn x (x : M) ≠ 0 := (sgnConst D x hx).2 x (D.mem_src_self x)
  have htau : D.tau x (x : M) ≠ 0 := (tauConst D x hx).2 x (D.mem_src_self x)
  rw [Cof.flipSign]
  exact mul_ne_zero hsgn htau

/-- **The chart transfer of the corrected chart is `flipSign` times that of the `Lvl` chart.** -/
theorem chartTr_icN_eq (D : Cof k n M) (x : D.S.Pre)
    (hxM : (x : M) ∉ (𝓡∂ ((8 + k) + 1)).boundary M)
    (hxN : x ∈ (icN D x).source) (hxL : x ∈ (icL D x).source) :
    (Work.PTGeometric.HOF.chartTr (W := TopCat.of D.S.Pre) (icN D x) x hxN)
        (Work.PTGeometric.HOF.eucFam 9 (by norm_num) ((icN D x) x))
      = (if D.flipSign x = 1 then (1:ℤ) else -1) •
        (Work.PTGeometric.HOF.chartTr (W := TopCat.of D.S.Pre) (icL D x) x hxL)
          (Work.PTGeometric.HOF.eucFam 9 (by norm_num) ((icL D x) x)) := by
  have hne : D.flipSign x ≠ 0 := flipSign_ne_zero D x hxM
  have hdet : LinearMap.det (reflectLin D x).toLinearMap = (D.flipSign x : ℝ) :=
    reflectLin_det D x hne
  have hA : Function.Bijective (reflectLin D x) :=
    ⟨Function.LeftInverse.injective (g := reflectLin D x) (fun v => CofAtlas.reflectLin_self D x v),
     Function.RightInverse.surjective (g := reflectLin D x) (fun v => CofAtlas.reflectLin_self D x v)⟩
  have hd := hasFDerivAt_icN_icL D x hxM
  have h := Work.ThomBordism.PosAtlas.chartTrChangeSigned (W := TopCat.of D.S.Pre)
    (icN D x) (icL D x) x hxN hxL (reflectLin D x) hA hd
  rw [h, hdet, signType_if (D.flipSign x)]

/-- The boundary of the corrected charted space. -/
abbrev BN (D : Cof k n M) : Set D.S.Pre :=
  @ModelWithCorners.boundary ℝ _ (EuclideanSpace ℝ (Fin 9)) _ _ (EuclideanHalfSpace 9) _
    (𝓡∂ 9) D.S.Pre _ (CofAtlas.newChartedSpace D)

theorem icN_mem_source (D : Cof k n M) (x : D.S.Pre) (hx : x ∉ BN D) :
    x ∈ (icN D x).source := by
  letI : ChartedSpace (EuclideanHalfSpace 9) D.S.Pre := CofAtlas.newChartedSpace D
  letI : IsManifold (𝓡∂ 9) 1 D.S.Pre := newManifold_one D
  rw [icN]
  refine Work.PTGeometric.icChart_mem_source 8 (TopCat.of D.S.Pre) x x hx ?_
  rw [extChartAt_source]
  exact mem_chart_source (EuclideanHalfSpace 9) x

theorem icL_mem_source (D : Cof k n M) (x : D.S.Pre) (hx : x ∉ BL D) :
    x ∈ (icL D x).source := by
  letI : ChartedSpace (EuclideanHalfSpace 9) D.S.Pre :=
    Work.PTGeometric.Lvl.Setup.instChartedSpace D.S
  letI : IsManifold (𝓡∂ 9) 1 D.S.Pre := lvlManifold_one D
  rw [icL]
  refine Work.PTGeometric.icChart_mem_source 8 (TopCat.of D.S.Pre) x x hx ?_
  rw [extChartAt_source]
  exact mem_chart_source (EuclideanHalfSpace 9) x

/-- The local class of the corrected chart transfer. -/
noncomputable abbrev newValue (D : Cof k n M) (x : D.S.Pre) (hx : x ∉ BN D) :
    Work.Orient.LocH (TopCat.of D.S.Pre) 9 x :=
  (Work.PTGeometric.HOF.chartTr (W := TopCat.of D.S.Pre) (icN D x) x (icN_mem_source D x hx))
    (Work.PTGeometric.HOF.eucFam 9 (by norm_num) ((icN D x) x))

/-- The local class of the `Lvl` chart transfer. -/
noncomputable abbrev lvlValue (D : Cof k n M) (x : D.S.Pre) (hx : x ∉ BL D) :
    Work.Orient.LocH (TopCat.of D.S.Pre) 9 x :=
  (Work.PTGeometric.HOF.chartTr (W := TopCat.of D.S.Pre) (icL D x) x (icL_mem_source D x hx))
    (Work.PTGeometric.HOF.eucFam 9 (by norm_num) ((icL D x) x))

theorem newValue_eq (D : Cof k n M) (x : D.S.Pre)
    (hxM : (x : M) ∉ (𝓡∂ ((8 + k) + 1)).boundary M)
    (hxN : x ∉ BN D) (hxL : x ∉ BL D) :
    newValue D x hxN = (if D.flipSign x = 1 then (1:ℤ) else -1) • lvlValue D x hxL :=
  chartTr_icN_eq D x hxM (icN_mem_source D x hxN) (icL_mem_source D x hxL)

theorem notMem_ambient_of_notMem_BN (D : Cof k n M) {x : D.S.Pre} (hx : x ∉ BN D) :
    (x : M) ∉ (𝓡∂ ((8 + k) + 1)).boundary M := by
  have hset : {y : D.S.Pre | (y : M) ∈ (𝓡∂ ((8 + k) + 1)).boundary M} = BN D :=
    (CofAtlas.newBoundary D).symm
  intro hh
  exact hx (hset ▸ hh)

/-- **Transport of a relative class across an equality of the excluded sets.** -/
theorem relPunct_transport {n : ℕ} {W : TopCat} {E F : Set W} (h : E = F)
    (ΓF : ∀ x : W, x ∉ F → Work.Orient.LocH W (n + 1) x)
    (hv : ∃ w : (Work.Cohomology.relChains W E).homology (n + 1),
      (∀ x hx, (HomologicalComplex.homologyMap (Work.Orient.relPunct W E x hx) (n + 1)).hom w
        = ΓF x (h ▸ hx)) ∧
      (∀ x hx, Submodule.span ℤ
        {((HomologicalComplex.homologyMap (Work.Orient.relPunct W E x hx) (n + 1)).hom w)} = ⊤)) :
    ∃ w : (Work.Cohomology.relChains W F).homology (n + 1),
      (∀ x hx, (HomologicalComplex.homologyMap (Work.Orient.relPunct W F x hx) (n + 1)).hom w
        = ΓF x hx) ∧
      (∀ x hx, Submodule.span ℤ
        {((HomologicalComplex.homologyMap (Work.Orient.relPunct W F x hx) (n + 1)).hom w)} = ⊤) := by
  subst h
  obtain ⟨w, h1, h2⟩ := hv
  exact ⟨w, h1, h2⟩


end

end CofAtlas


theorem orientationFamily_valued_of_coframing
    {k n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
      ((⊤ : ENat) : WithTop ENat) M]
    (D : CofAtlas.Cof k n M) (hWne : D.W.Nonempty)
    (hcol : Nonempty (@Work.Surgery.Collar 8 D.S.Pre inferInstance
      (Work.PTGeometric.Lvl.Setup.instChartedSpace D.S))) :
    letI : ChartedSpace (EuclideanHalfSpace 9) D.S.Pre :=
      Work.PTGeometric.Lvl.Setup.instChartedSpace D.S
    letI : IsManifold (modelWithCornersEuclideanHalfSpace 9)
        ((⊤ : ENat) : WithTop ENat) D.S.Pre :=
      Work.PTGeometric.Lvl.Setup.instIsManifold D.S
    letI : IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 D.S.Pre :=
      IsManifold.of_le (n := ((⊤ : ENat) : WithTop ENat)) (by simp)
    ∃ γ : ∀ x : D.S.Pre,
        x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary D.S.Pre →
        Work.Orient.LocH (TopCat.of D.S.Pre) 9 x,
      Work.Orient.IsHalfOrientationFamily 8 (TopCat.of D.S.Pre) γ ∧
      (∀ (x : D.S.Pre) (hx : x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary D.S.Pre),
        γ x hx = (if D.flipSign x = 1 then (1 : ℤ) else -1) •
          Work.PTGeometric.HOF.chartTr (Work.PTGeometric.icChart 8 (TopCat.of D.S.Pre) x) x
            (Work.PTGeometric.icChart_mem_source 8 (TopCat.of D.S.Pre) x x hx
              (by rw [extChartAt_source]
                  exact mem_chart_source (EuclideanHalfSpace 9) x))
            (Work.PTGeometric.HOF.eucFam 9 (by norm_num)
              (Work.PTGeometric.icChart 8 (TopCat.of D.S.Pre) x x))) := by
  classical
  -- the `Lvl` charted-space structure of the statement, re-installed for the proof
  letI : ChartedSpace (EuclideanHalfSpace 9) D.S.Pre :=
    Work.PTGeometric.Lvl.Setup.instChartedSpace D.S
  letI : IsManifold (𝓡∂ 9) ((⊤ : ENat) : WithTop ENat) D.S.Pre :=
    Work.PTGeometric.Lvl.Setup.instIsManifold D.S
  letI : IsManifold (𝓡∂ 9) 1 D.S.Pre :=
    IsManifold.of_le (n := ((⊤ : ENat) : WithTop ENat)) (by simp)
  haveI : Nonempty D.S.Pre := by
    obtain ⟨y, hy⟩ := hWne
    exact ⟨⟨y, hy⟩⟩
  -- the boundary of the level set inside `M`
  let Sbd : Set D.S.Pre := {x | (x : M) ∈ (𝓡∂ ((8 + k) + 1)).boundary M}
  have hbdL : CofAtlas.BL D = Sbd := by
    ext x
    exact Work.PTGeometric.Lvl.Setup.mem_boundary_iff D.S x
  have hbdN : CofAtlas.BN D = Sbd := CofAtlas.newBoundary D
  have h : CofAtlas.BN D = CofAtlas.BL D := hbdN.trans hbdL.symm
  -- the relative class, in the corrected charted space
  have hwN : ∃ w : (Work.Cohomology.relChains (TopCat.of D.S.Pre) (CofAtlas.BN D)).homology 9,
      (∀ (x : D.S.Pre) (hx : x ∉ CofAtlas.BN D),
        (HomologicalComplex.homologyMap
          (Work.Orient.relPunct (TopCat.of D.S.Pre) (CofAtlas.BN D) x hx) 9).hom w
            = CofAtlas.newValue D x hx) ∧
      (∀ (x : D.S.Pre) (hx : x ∉ CofAtlas.BN D),
        Submodule.span ℤ {((HomologicalComplex.homologyMap
          (Work.Orient.relPunct (TopCat.of D.S.Pre) (CofAtlas.BN D) x hx) 9).hom w)} = ⊤) := by
    letI : ChartedSpace (EuclideanHalfSpace 9) D.S.Pre := CofAtlas.newChartedSpace D
    haveI : IsManifold (𝓡∂ 9) ((⊤ : ENat) : WithTop ENat) D.S.Pre := CofAtlas.newIsManifold D
    haveI : IsManifold (𝓡∂ 9) 1 D.S.Pre := CofAtlas.newManifold_one D
    haveI : CompactSpace D.S.Pre := Work.PTGeometric.Lvl.Setup.instCompactSpace D.S
    obtain ⟨cL⟩ := hcol
    have hbdN' : (𝓡∂ 9).boundary D.S.Pre
        = {x : D.S.Pre | (x : M) ∈ (𝓡∂ ((8 + k) + 1)).boundary M} := CofAtlas.newBoundary D
    have hcouple : CofAtlas.BL D = (𝓡∂ 9).boundary D.S.Pre :=
      hbdL.trans (hbdN'.symm : Sbd = (𝓡∂ 9).boundary D.S.Pre)
    have cN : Work.Surgery.Collar 8 D.S.Pre :=
      Work.ThomBordism.Collar.of_instance_congr hcouple cL
    obtain ⟨w, hfund, hw⟩ := Work.ThomBordism.exists_relFundClass_of_explicitFamily (n := 8) cN
      (CofAtlas.newTransition_det_pos D)
    refine ⟨w, ?_, ?_⟩
    · intro x hx
      rw [hw x hx]
      rfl
    · intro x hx
      exact hfund x hx
  obtain ⟨wN, hwNval, hwNgen⟩ := hwN
  -- transport the class to the `Lvl` relative chain complex
  obtain ⟨w, hwval, hwgen⟩ :
      ∃ w : (Work.Cohomology.relChains (TopCat.of D.S.Pre) (CofAtlas.BL D)).homology 9,
        (∀ (x : D.S.Pre) (hx : x ∉ CofAtlas.BL D),
          (HomologicalComplex.homologyMap
            (Work.Orient.relPunct (TopCat.of D.S.Pre) (CofAtlas.BL D) x hx) 9).hom w
              = (if D.flipSign x = 1 then (1 : ℤ) else -1) • CofAtlas.lvlValue D x hx) ∧
        (∀ (x : D.S.Pre) (hx : x ∉ CofAtlas.BL D),
          Submodule.span ℤ {((HomologicalComplex.homologyMap
            (Work.Orient.relPunct (TopCat.of D.S.Pre) (CofAtlas.BL D) x hx) 9).hom w)} = ⊤) :=
    CofAtlas.relPunct_transport (n := 8) (W := TopCat.of D.S.Pre)
      (E := CofAtlas.BN D) (F := CofAtlas.BL D) h
      (fun x hx => (if D.flipSign x = 1 then (1 : ℤ) else -1) • CofAtlas.lvlValue D x hx)
      ⟨wN, (fun x hx => (hwNval x hx).trans (CofAtlas.newValue_eq D x
        (CofAtlas.notMem_ambient_of_notMem_BN D hx) hx (h ▸ hx))), hwNgen⟩
  refine ⟨fun x hx => (HomologicalComplex.homologyMap (relChainsInclPunct (TopCat.of D.S.Pre)
      ((𝓡∂ 9).boundary D.S.Pre) x hx) 9).hom w, ?_, ?_⟩
  · refine Work.ThomBordism.isHalfOrientationFamily_relChainsInclPunct
      (W := TopCat.of D.S.Pre) w ?_
    intro x hx
    rw [← Work.Orient.relPunct_eq_relChainsInclPunct]
    exact hwgen x hx
  · intro x hx
    dsimp only
    rw [← Work.Orient.relPunct_eq_relChainsInclPunct, hwval x hx]

end Work.ThomBordism
