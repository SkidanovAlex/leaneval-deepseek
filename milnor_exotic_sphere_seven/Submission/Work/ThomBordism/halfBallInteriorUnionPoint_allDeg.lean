import Mathlib
import Submission.Work.Orient.Boundary.halfBallInteriorUnionPoint
import Submission.Work.Orient.Boundary.halfBallInteriorUnionPoint_model
import Submission.Work.Orient.Boundary.halfBallInteriorUnionPoint_transfer
import Submission.Work.Orient.Boundary.HalfVanishing
import Submission.Work.Orient.Boundary.localHomology_corner

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The boundary-point half-ball vanishing in **every** degree

`Work.Orient.Boundary.isZero_halfBallInteriorUnionPoint` proves

`H_n(W, W∖(K ∩ W° ∪ {y})) = 0`

for the coordinate half-ball `K = halfBallPiece (n+1) W y r` at a boundary point `y` of a space `W`
charted in the half-space model — in the single degree `n` (one below the top, the degree needed
for the local fundamental class).

This file proves the same vanishing in **every** degree `k`, which is what the collar/orientation
machinery downstream asks for.  Every ingredient of the original proof is already degree-general
(`Work.Orient.Boundary.homeoRelChainsIso`, `Work.Cohomology.excision`,
`Work.Orient.Boundary.isZero_relChains_of_homotopyEquiv_incl`,
`Work.Orient.Boundary.isZero_locH_of_mem_boundary_all`,
`Work.Cohomology.relSubPunctured_homology_iso` and the long exact sequence of the triple all carry
an arbitrary degree), so the three steps of the original proof are simply re-run with the degree
left arbitrary:

* `isZero_relChains_punctured_boundary_halfBall_allDeg` — the flat model: the push away from the
  boundary point realises the complement of the half-ball as a deformation retract;
* `isZero_model_halfspaceForm_allDeg` — the same in the chart form;
* `isZero_halfBallInteriorUnionPoint_of_model_allDeg` — the chart transfer;
* the long exact sequence of the triple `(K ∩ W° ∪ {y})ᶜ ⊆ W∖{y} ⊆ W`, whose third term vanishes
  because `y` is a boundary point.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold Topology

namespace Work.Orient.Boundary

noncomputable section

/-- **The flat model at the boundary point, in every degree.**  The push away from the boundary
point `c` realises the complement of the half-ball `{dist · c ≤ ρ ∧ 0 < · 0}` inside the punctured
half-space as a homotopy equivalence, so the relative homology vanishes in every degree. -/
theorem isZero_relChains_punctured_boundary_halfBall_allDeg (n : ℕ)
    (c : EuclideanSpace ℝ (Fin (n + 1))) (hc : c 0 = 0) (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) :
    IsZero ((Work.Cohomology.relChains (TopCat.of (pSpace n c)) (pSet n c ρ)).homology k) := by
  classical
  -- the retraction, at the endpoint of the homotopy
  have hpathY : Continuous fun y : pSpace n c => pPath n ρ 1 c hc y := by
    have hb : Continuous fun y : pSpace n c => pPathA n ρ 1 c y :=
      (continuous_pPathA n ρ c).comp (continuous_const.prodMk continuous_id)
    unfold pPath
    exact Continuous.subtype_mk hb (fun y => ⟨by
        unfold pPathA
        rw [coord_add_smul n hc]
        exact mul_nonneg (le_of_lt pScaleT_pos) y.2.1,
      pPathA_ne (pSpace_dist_pos y)⟩)
  let g : TopCat.of (pSpace n c) ⟶ TopCat.of (pSet n c ρ) := TopCat.ofHom
    ⟨fun y => ⟨pPath n ρ 1 c hc y, pPath_one_mem n hc hρ y⟩,
      Continuous.subtype_mk hpathY (fun y => pPath_one_mem n hc hρ y)⟩
  let Hmap : C(↑unitInterval × pSpace n c, pSpace n c) :=
    ⟨fun q => pPath n ρ (q.1 : ℝ) c hc q.2, by
      have h2 : Continuous fun q : ↑unitInterval × pSpace n c => ((q.1 : ℝ), q.2) := by fun_prop
      have h1 : Continuous fun q : ↑unitInterval × pSpace n c => pPathA n ρ (q.1 : ℝ) c q.2 :=
        (continuous_pPathA n ρ c).comp h2
      unfold pPath
      exact Continuous.subtype_mk h1 (fun q => ⟨by
          unfold pPathA
          rw [coord_add_smul n hc]
          exact mul_nonneg (le_of_lt pScaleT_pos) q.2.2.1,
        pPathA_ne (pSpace_dist_pos q.2)⟩)⟩
  have hY : TopCat.Homotopy (𝟙 (TopCat.of (pSpace n c)))
      (g ≫ Work.Cohomology.subtypeIncl (TopCat.of (pSpace n c)) (pSet n c ρ)) :=
    ContinuousMap.Homotopy.mk Hmap
      (fun y => by
        apply Subtype.ext
        show pPathA n ρ 0 c y = y.1
        unfold pPathA
        rw [pScaleT_zero, one_smul]
        abel)
      (fun y => rfl)
  have hpathZm : Continuous fun q : ↑unitInterval × (TopCat.of (pSet n c ρ)) =>
      pPath n ρ (q.1 : ℝ) c hc q.2.1 := by
    have h3 : Continuous fun q : ↑unitInterval × (TopCat.of (pSet n c ρ)) =>
        ((q.1 : ℝ), q.2.1) := by fun_prop
    have h2 : Continuous fun q : ↑unitInterval × (TopCat.of (pSet n c ρ)) =>
        pPathA n ρ (q.1 : ℝ) c q.2.1 := (continuous_pPathA n ρ c).comp h3
    unfold pPath
    exact Continuous.subtype_mk h2 (fun q => ⟨by
        unfold pPathA
        rw [coord_add_smul n hc]
        exact mul_nonneg (le_of_lt pScaleT_pos) q.2.1.2.1,
      pPathA_ne (pSpace_dist_pos q.2.1)⟩)
  let hZm : C(↑unitInterval × (TopCat.of (pSet n c ρ)), TopCat.of (pSet n c ρ)) :=
    ⟨fun q => ⟨pPath n ρ (q.1 : ℝ) c hc q.2.1, pPath_mem n hc q.1.2.1 q.2⟩,
      Continuous.subtype_mk hpathZm (fun q => pPath_mem n hc q.1.2.1 q.2)⟩
  have hZhom : TopCat.Homotopy (𝟙 (TopCat.of (pSet n c ρ)))
      (Work.Cohomology.subtypeIncl (TopCat.of (pSpace n c)) (pSet n c ρ) ≫ g) :=
    ContinuousMap.Homotopy.mk hZm
      (fun z => by
        unfold hZm
        apply Subtype.ext
        apply Subtype.ext
        show pPathA n ρ 0 c z.1 = z.1.1
        unfold pPathA
        rw [pScaleT_zero, one_smul]
        abel)
      (fun z => rfl)
  exact isZero_relChains_of_homotopyEquiv_incl g hZhom.symm hY.symm k

/-- **The flat model in the chart form, in every degree.**  The canonical homeomorphism between the
punctured half-space in ambient coordinates and the punctured half-space as a subtype of
`EuclideanHalfSpace`. -/
theorem isZero_model_halfspaceForm_allDeg (n : ℕ) (c : EuclideanHalfSpace (n + 1)) (hc : c.1 0 = 0)
    (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) :
    IsZero ((Work.Cohomology.relChains (TopCat.of {v : EuclideanHalfSpace (n + 1) | v ≠ c})
      {v : {v : EuclideanHalfSpace (n + 1) | v ≠ c} | (v : EuclideanHalfSpace (n + 1)) ∉
        (Work.Orient.halfIncl (n + 1) ⁻¹' Metric.closedBall (Work.Orient.halfIncl (n + 1) c) ρ
          ∩ {v : EuclideanHalfSpace (n + 1) | 0 < v.1 0})}).homology k) := by
  classical
  obtain ⟨e⟩ := homeoRelChainsIso (puncturedHalfSpaceHomeo n c) (pSet n c.1 ρ)
    {v : ↥{v : EuclideanHalfSpace (n + 1) | v ≠ c} | (v : EuclideanHalfSpace (n + 1)) ∉
      (Work.Orient.halfIncl (n + 1) ⁻¹' Metric.closedBall (Work.Orient.halfIncl (n + 1) c) ρ
        ∩ {v : EuclideanHalfSpace (n + 1) | 0 < v.1 0})}
    (fun y => by
      exact Iff.rfl) k
  exact IsZero.of_iso
    (isZero_relChains_punctured_boundary_halfBall_allDeg n c.1 hc ρ hρ k) e.symm

/-- **The chart transfer, in every degree.**  For a coordinate half-ball `K = halfBallPiece (n+1) W y r`
at the boundary point `y`, the vanishing of the flat model (with the puncture at the image of `y`
and the excluded set the complement of the half-ball) implies the vanishing of
`H_k(W∖{y}, (W∖{y})∖(K ∩ W°))` in every degree. -/
theorem isZero_halfBallInteriorUnionPoint_of_model_allDeg (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (hy : y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (r : ℝ) (hr : 0 < r) (hgood : Work.Orient.halfBallGood (n + 1) W y r) (k : ℕ)
    (hmodel : CategoryTheory.Limits.IsZero ((Work.Cohomology.relChains
      (TopCat.of {v : EuclideanHalfSpace (n + 1) | v ≠ (chartAt (EuclideanHalfSpace (n + 1)) y) y})
      {v : {v : EuclideanHalfSpace (n + 1) | v ≠ (chartAt (EuclideanHalfSpace (n + 1)) y) y} |
        (v : EuclideanHalfSpace (n + 1)) ∉
          (Work.Orient.halfIncl (n + 1) ⁻¹' Metric.closedBall
              (Work.Orient.halfIncl (n + 1) ((chartAt (EuclideanHalfSpace (n + 1)) y) y)) (r / 2)
            ∩ {v : EuclideanHalfSpace (n + 1) | 0 < v.1 0})}).homology k)) :
    CategoryTheory.Limits.IsZero ((Work.Cohomology.relChains (TopCat.of {z : W | z ≠ y})
      {z : {z : W | z ≠ y} | (z : W) ∉ (Work.Orient.halfBallPiece (n + 1) W y r ∩
        {z : W | z ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W})}).homology k) := by
  classical
  let e := chartAt (EuclideanHalfSpace (n + 1)) y
  have hysrc : y ∈ e.source := mem_chart_source (EuclideanHalfSpace (n + 1)) y
  have hKclosed : IsClosed (Work.Orient.halfBallPiece (n + 1) W y r) :=
    (Work.Orient.IsCoordHalfBall.isCompact (n := n + 1) ⟨y, r, hr, hgood, rfl⟩).isClosed
  have hKsrc : Work.Orient.halfBallPiece (n + 1) W y r ⊆ e.source := fun w hw => hw.2
  let K0 : Set (EuclideanHalfSpace (n + 1)) :=
    Work.Orient.halfIncl (n + 1) ⁻¹'
      Metric.closedBall (Work.Orient.halfIncl (n + 1) (e y)) (r / 2)
  let D : Set (EuclideanHalfSpace (n + 1)) :=
    K0 ∩ {v : EuclideanHalfSpace (n + 1) | 0 < v.1 0}
  have hK0target : K0 ⊆ e.target :=
    fun v hv => hgood (Metric.closedBall_subset_ball (by linarith) hv)
  have hDK0 : D ⊆ K0 := fun v hv => hv.1
  have hK0closed : IsClosed K0 :=
    (Metric.isClosed_closedBall (x := Work.Orient.halfIncl (n + 1) (e y)) (ε := r / 2)).preimage
      continuous_subtype_val
  have hcorr : ∀ w : W, w ∈ e.source →
      ((w ∈ Work.Orient.halfBallPiece (n + 1) W y r ∩
        {z : W | z ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W}) ↔
      e w ∈ D) := by
    refine fun w hw => ?_
    have h1 : w ∈ Work.Orient.halfBallPiece (n + 1) W y r ↔ e w ∈ K0 :=
      ⟨fun h => h.1, fun h => ⟨h, hw⟩⟩
    have h2 : w ∈ ({z : W | z ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W}) ↔
        0 < (e w).1 0 :=
      ⟨fun h => chartAt_interior_pos hw h, fun h => not_mem_boundary_of_chartAt_pos hw h⟩
    exact h1.and h2
  -- ### Step 1: excise `W∖{y}` down to the chart source
  let X : TopCat := TopCat.of {z : W | z ≠ y}
  let A : Set X := {z : X | (z : W) ∉ (Work.Orient.halfBallPiece (n + 1) W y r ∩
        {z : W | z ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W})}
  let Z : Set X := {z : X | (z : W) ∉ e.source}
  have hZclosed : IsClosed Z := by
    have heq : Z = (fun z : X => (z : W)) ⁻¹' (e.source)ᶜ := by ext z; exact Iff.rfl
    rw [heq]
    exact e.open_source.isClosed_compl.preimage continuous_subtype_val
  have hsub : closure Z ⊆ interior A := by
    intro z hz
    rw [hZclosed.closure_eq] at hz
    have hzW : (z : W) ∉ e.source := hz
    have hzK : (z : W) ∉ Work.Orient.halfBallPiece (n + 1) W y r := fun h => hzW (hKsrc h)
    have hnbhd : ({z' : X | (z' : W) ∉ Work.Orient.halfBallPiece (n + 1) W y r} ∈ 𝓝 z) :=
      (hKclosed.isOpen_compl.preimage continuous_subtype_val).mem_nhds hzK
    exact mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset hnbhd (fun z' hz' h => hz' h.1))
  obtain ⟨e0⟩ := Work.Cohomology.excision X A Z hsub k
  -- ### The model side
  let XH : TopCat := TopCat.of {v : EuclideanHalfSpace (n + 1) | v ≠ e y}
  let AH : Set XH := {v : XH | (v : EuclideanHalfSpace (n + 1)) ∉ D}
  let ZH : Set XH := {v : XH | (v : EuclideanHalfSpace (n + 1)) ∉ e.target}
  have hmod : IsZero ((Work.Cohomology.relChains XH AH).homology k) := hmodel
  have hZHclosed : IsClosed ZH := by
    have heq : ZH = (fun v : XH => (v : EuclideanHalfSpace (n + 1))) ⁻¹' (e.target)ᶜ := by
      ext v; exact Iff.rfl
    rw [heq]
    exact e.open_target.isClosed_compl.preimage continuous_subtype_val
  have hsubH : closure ZH ⊆ interior AH := by
    intro v hv
    rw [hZHclosed.closure_eq] at hv
    have hvK0 : (v : EuclideanHalfSpace (n + 1)) ∉ K0 := fun h => hv (hK0target h)
    have hnbhd : ({v' : XH | (v' : EuclideanHalfSpace (n + 1)) ∉ K0} ∈ 𝓝 v) :=
      (hK0closed.preimage continuous_subtype_val).isOpen_compl.mem_nhds hvK0
    exact mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset hnbhd (fun v' hv' h => hv' (hDK0 h)))
  obtain ⟨e2⟩ := Work.Cohomology.excision XH AH ZH hsubH k
  -- ### The chart homeomorphism between the two chart sources
  let U1 : Type := {z : X | z ∉ Z}
  let A1 : Set U1 := {z : U1 | (z : X) ∈ A}
  let U2 : Type := {v : XH | v ∉ ZH}
  let A2 : Set U2 := {v : U2 | (v : XH) ∈ AH}
  have hnn : ∀ {p : Prop}, ¬¬p → p := fun h => Classical.byContradiction h
  let φ : U1 ≃ₜ U2 :=
    { toFun := fun z =>
        ⟨⟨e (((z : U1) : X) : W), fun heq =>
            ((z : U1) : X).2 (e.injOn (hnn z.2) hysrc heq)⟩,
          fun h => h (e.map_source (hnn z.2))⟩
      invFun := fun v =>
        ⟨⟨e.symm (((v : U2) : XH) : EuclideanHalfSpace (n + 1)), fun heq =>
            ((v : U2) : XH).2 (by
              have hv : (((v : U2) : XH) : EuclideanHalfSpace (n + 1)) ∈ e.target := hnn v.2
              rw [← e.right_inv hv, heq])⟩,
          fun h => h (e.map_target (hnn v.2))⟩
      left_inv := fun z => by
        apply Subtype.ext
        apply Subtype.ext
        exact e.left_inv (hnn z.2)
      right_inv := fun v => by
        apply Subtype.ext
        apply Subtype.ext
        exact e.right_inv (hnn v.2)
      continuous_toFun := Continuous.subtype_mk (Continuous.subtype_mk
        (e.continuousOn.comp_continuous (continuous_subtype_val.comp continuous_subtype_val)
          (fun z => hnn z.2)) _) _
      continuous_invFun := Continuous.subtype_mk (Continuous.subtype_mk
        (e.symm.continuousOn.comp_continuous (continuous_subtype_val.comp continuous_subtype_val)
          (fun v => hnn v.2)) _) _ }
  have hA1 : ∀ z : U1, z ∈ A1 ↔ φ z ∈ A2 := by
    intro z
    have hw : (((z : U1) : X) : W) ∈ e.source := hnn z.2
    show (((z : U1) : X) : W) ∉ (Work.Orient.halfBallPiece (n + 1) W y r ∩
        {z : W | z ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W}) ↔
      e (((z : U1) : X) : W) ∈ D → False
    exact not_congr (hcorr (((z : U1) : X) : W) hw)
  obtain ⟨e1⟩ := homeoRelChainsIso φ A1 A2 hA1 k
  exact IsZero.of_iso (IsZero.of_iso (IsZero.of_iso hmod e2.symm) e1) e0

end

end Work.Orient.Boundary

namespace Work.ThomBordism

open Work.Orient.Boundary

/-- **The vanishing input, in every degree.**  For the coordinate half-ball `K` around the boundary
point `y`, the relative group `H_k(W, W∖(K ∩ W° ∪ {y}))` vanishes for every `k`. -/
theorem halfBallInteriorUnionPoint_allDeg
    (n : ℕ) (W : TopCat) [CompactSpace W] [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (hy : y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (r : ℝ) (hr : 0 < r) (hgood : Work.Orient.halfBallGood (n + 1) W y r)
    (k : ℕ) :
    CategoryTheory.Limits.IsZero ((Work.Cohomology.relChains W
      ((((Work.Orient.halfBallPiece (n + 1) W y r) ∩
        {x : W | x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W}) ∪ {y})ᶜ)).homology k) := by
  classical
  -- the flat model and its transfer
  have hmod := isZero_model_halfspaceForm_allDeg n ((chartAt (EuclideanHalfSpace (n + 1)) y) y)
    (chartAt_boundary_coord_zero n W hy) (r / 2) (by linarith) k
  have htr := isZero_halfBallInteriorUnionPoint_of_model_allDeg n W y hy r hr hgood k hmod
  -- the triple `A ⊆ B ⊆ W`
  set B : Set W := {z : W | z ≠ y} with hBdef
  set P : Set W := (Work.Orient.halfBallPiece (n + 1) W y r) ∩
    {x : W | x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W} with hPdef
  have hAB : (P ∪ {y})ᶜ ⊆ B := fun z hz hyz => hz (Or.inr hyz)
  -- the vanishing of the third term: `y` is a boundary point
  have h3 : IsZero ((Work.Cohomology.relChains W B).homology k) := by
    have hB : B = {z : W | z ≠ y} := rfl
    rw [hB]
    exact isZero_locH_of_mem_boundary_all n W hy k
  -- the vanishing of the first term, via the subspace model of the transfer
  have hset : {z : ↥{z : W | z ≠ y} | (z : W) ∈ (P ∪ {y})ᶜ}
      = {z : ↥{z : W | z ≠ y} | (z : W) ∉ P} := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · intro h hP; exact h (Or.inl hP)
    · rintro h (hP | hyz)
      · exact h hP
      · exact z.2 hyz
  have hspace : IsZero ((Work.Cohomology.relChains (TopCat.of {z : W | z ≠ y})
      {z : ↥{z : W | z ≠ y} | (z : W) ∉ P}).homology k) := htr
  have h1 : IsZero (((Work.Cohomology.tripleShort W (P ∪ {y})ᶜ B hAB).X₁).homology k) := by
    obtain ⟨e⟩ := Work.Cohomology.relSubPunctured_homology_iso W y (P ∪ {y})
      (Set.mem_union_right _ rfl) k
    have hsp : IsZero ((Work.Cohomology.relChains (TopCat.of {z : W | z ≠ y})
        {z : ↥{z : W | z ≠ y} | (z : W) ∈ (P ∪ {y})ᶜ}).homology k) := by
      rw [hset]; exact hspace
    exact IsZero.of_iso hsp e
  -- the long exact sequence of the triple gives the middle
  have hS : (Work.Cohomology.tripleShort W (P ∪ {y})ᶜ B hAB).ShortExact :=
    Work.Cohomology.relChains_triple_shortExact W (P ∪ {y})ᶜ B hAB
  have hker : LinearMap.ker (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.tripleShort W (P ∪ {y})ᶜ B hAB).g k)) = ⊥ := by
    have hf0 : HomologicalComplex.homologyMap
        (Work.Cohomology.tripleShort W (P ∪ {y})ᶜ B hAB).f k = 0 :=
      IsZero.eq_zero_of_src h1 _
    have hr := ShortComplex.Exact.moduleCat_range_eq_ker (hS.homology_exact₂ k)
    have hrange : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.tripleShort W (P ∪ {y})ᶜ B hAB).f k)).range = ⊥ := by
      rw [hf0, ModuleCat.hom_zero, LinearMap.range_zero]
    exact hr.symm.trans hrange
  have hinj : Function.Injective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.tripleShort W (P ∪ {y})ᶜ B hAB).g k)) :=
    LinearMap.ker_eq_bot.mp hker
  haveI : Subsingleton (((Work.Cohomology.tripleShort W (P ∪ {y})ᶜ B hAB).X₃).homology k) :=
    ModuleCat.isZero_iff_subsingleton.mp h3
  exact ModuleCat.isZero_iff_subsingleton.mpr
    ⟨fun a b => hinj (Subsingleton.elim _ _)⟩

end Work.ThomBordism
