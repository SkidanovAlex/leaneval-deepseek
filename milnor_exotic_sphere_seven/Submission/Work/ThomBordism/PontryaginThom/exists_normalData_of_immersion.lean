import Mathlib
import Submission.Work.ThomBordism.PontryaginThom.NormalData
import Submission.Work.ThomBordism.PontryaginThom.Orthogonal
import Submission.Work.ThomBordism.PontryaginThom.continuousOn_orthProjCLM
import Submission.Work.ThomBordism.PontryaginThom.orthInj_planeProj_complInj
import Submission.Work.ThomBordism.PontryaginThom.planeProj_orthInj_complInj
import Submission.Work.ThomBordism.PontryaginThom.Frames

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-!
# The normal bundle of an immersion exists

This file proves `exists_normalData_of_immersion`: for a closed smooth `8`-manifold `V`, an
immersion `f : V → ℝ^{8+k}` (`C¹`, injective derivative) produces the data

`NormalData V k f`  =  the complement bundle `ComplementData V.pt k (CoverIdx V k)` of the image
of the derivative, over the finite chart cover `Work.Thom.chartCover` crossed with the chart indices
`S : ChartIdx 8 k` of the oriented Grassmannian,

together with the two facts that tie it to the geometry: the base set of `(i,S)` lies in the source
of the chart `i` and the `S`-th coordinate projection of the frame `frame f i` is invertible there,
and the kernel of the projection is the plane `im (d f_x)` of the frame.

## The construction

For the index `(i,S) : Fin (chartCoverSize) × ChartIdx 8 k` the plane is
`im (coeffMap (frame f (chartCover i) x)) ⊆ ℝ^{8+k}` (`FramesRange.lean`), where `frame f i x` is
the matrix of the derivative of the chart representative (`Frames.lean`).  The base set of `(i,S)` is

`coverBaseSet f (i,S) = (chartCover i).source ∩ {x | det (frameMatrix S (frame f i x)) ≠ 0}`

— open, because the determinant is continuous on the source and `{y | y ≠ 0}` is open — and it covers
`V`, because every point lies in some chart (`chartCover_spec`) and in that chart some `S` projects
the plane invertibly (`exists_chartIdx_frame`, from the injectivity of `mfderiv`).

On the base set of `(i,S)` we take

* the projection `P i x = planeProj (frame f i x) S h` onto the complement of the plane along it,
  whose kernel is `im (coeffMap (frame f i x))` by `ker_planeProj`;
* the insertion `I i x = orthInj (frame f i x) ∘ complInj S` of the *orthogonal* complement of the
  plane, followed by the coordinate insertion of the `S`-complement.  The orthogonal insertion is
  chart-independent on the plane (`orthInj_planeProj_complInj`), and the complement projection
  inverts it (`planeProj_orthInj_complInj_of_det`), so `P ∘ I = id` and
  `ker P = im (coeffMap (frame f i x))`.

Both `P` and `I` are extended to all of `V` by junk values off the base set (`coverP`/`coverI` are
`if h : det … ≠ 0 then … else …`, the `else` branch being the *coordinate* complement
`complProj S ∘ complInj S = id`), so that `P ∘ I = id` holds *everywhere*, as `ComplementData`
requires; on the base set the `if` reduces to the geometric branch.  Continuity of `P` on the base
set is `continuous_planeProj_family`, and continuity of `I` is that of the orthogonal projection
onto the plane (`continuousOn_orthProjCLM`), with the frame of an immersion independent at every
point of a chart (`frame_linearIndependent`).

The chart-independence `ker_agree` of the gluing data is `range_coeffMap_frame_agree`: the plane of
an immersion does not depend on the chart.
-/

open scoped Manifold ContDiff Topology

namespace Work.ThomBordism.PontryaginThom

open Work.ThomBordism.Grassmann

noncomputable section

variable {V : Man8} {k : ℕ}

/-! ## The finite cover of the construction -/

/-- The chart of the finite cover `Work.Thom.chartCover` at the first coordinate of an index. -/
abbrev coverChart (i : CoverIdx V k) : atlas (Euc 8) V.pt :=
  Work.Thom.chartCover (H := Euc 8) (M := V.pt) i.1

/-- The frame of the immersion `f` in the chart of the cover, at `x`. -/
abbrev coverFrame (f : V.pt → Euc (8 + k)) (i : CoverIdx V k) (x : V.pt) : Fin 8 → Euc (8 + k) :=
  frame f (coverChart i) x

/-- The determinant of the chart index `S` of the frame of the immersion in the chart `i`. -/
abbrev coverDet (f : V.pt → Euc (8 + k)) (i : CoverIdx V k) (x : V.pt) : ℝ :=
  (frameMatrix i.2 (coverFrame f i x)).det

/-- **The base set of the index `(i,S)`**: the points of the chart `i` where the `S`-th coordinate
projection of the frame of the immersion is invertible. -/
def coverBaseSet (f : V.pt → Euc (8 + k)) (i : CoverIdx V k) : Set V.pt :=
  (coverChart i).1.source ∩ {x | coverDet f i x ≠ 0}

/-- The matrix of a frame depends continuously on the frame. -/
theorem continuous_frameMatrix_id {k : ℕ} (S : ChartIdx 8 k) :
    Continuous fun A : Fin 8 → Euc (8 + k) => frameMatrix S A :=
  continuous_frameMatrix_family (fun A => A) continuous_id S

/-- The condition `det (frameMatrix S A) ≠ 0` is open in the frame `A`: the determinant is a
continuous function of the matrix and `{y | y ≠ 0}` is open. -/
theorem isOpen_det_frameMatrix {k : ℕ} (S : ChartIdx 8 k) :
    IsOpen {A : Fin 8 → Euc (8 + k) | (frameMatrix S A).det ≠ 0} :=
  (isOpen_compl_singleton (x := (0 : ℝ))).preimage
    (Continuous.matrix_det (continuous_frameMatrix_id S))

/-- **The base set is open**: it is the intersection of the (open) source of the chart with the
preimage of the open set `{det ≠ 0}` under the continuous chart representative of the frame. -/
theorem isOpen_coverBaseSet (f : V.pt → Euc (8 + k))
    (hf : ContMDiff (𝓡 8) (𝓡 (8 + k)) 1 f) (i : CoverIdx V k) :
    IsOpen (coverBaseSet f i) :=
  (continuousOn_frame f hf (coverChart i)).isOpen_inter_preimage
    (coverChart i).1.open_source (isOpen_det_frameMatrix i.2)

/-! ## The projection and the insertion, and their junk extension -/

/-- **The projection of the complement data at the index `(i,S)`**: the projection onto the
complement of the plane along it (`planeProj`) where the coordinate projection of the frame is
invertible, and the coordinate complement projection `complProj S` elsewhere (a junk value, chosen
so that it is a left inverse of the corresponding junk value of `coverI`). -/
def coverP (f : V.pt → Euc (8 + k)) (i : CoverIdx V k) (x : V.pt) :
    (Fin (8 + k) → ℝ) →L[ℝ] (Fin k → ℝ) :=
  if h : coverDet f i x ≠ 0 then
    LinearMap.toContinuousLinearMap (planeProj (coverFrame f i x) i.2 h)
  else LinearMap.toContinuousLinearMap (complProj i.2)

/-- **The insertion of the complement data at the index `(i,S)`**: the orthogonal complement of the
plane, transported into the `S`-complement coordinates of the frame, where the coordinate projection
of the frame is invertible, and the coordinate insertion `complInj S` elsewhere (a junk value). -/
def coverI (f : V.pt → Euc (8 + k)) (i : CoverIdx V k) (x : V.pt) :
    (Fin k → ℝ) →L[ℝ] (Fin (8 + k) → ℝ) :=
  if h : coverDet f i x ≠ 0 then
    (LinearMap.toContinuousLinearMap (orthInj (coverFrame f i x))).comp
      (LinearMap.toContinuousLinearMap (complInj i.2))
  else LinearMap.toContinuousLinearMap (complInj i.2)

/-- **The complement projection inverts the orthogonal insertion**, with no independence hypothesis
on the frame: `u - complInj S (planeProj A S hS u)` is the component of `u` in the plane of `A`,
which `orthInj A` kills — the orthogonal projection onto the plane lands in the plane
(`range_orthProj_le`) and the plane is the kernel of the complement projection (`ker_planeProj`).
(This is `planeProj_orthInj_complInj` with the unused hypothesis `LinearIndependent ℝ A` removed,
which is what the junk extension needs.) -/
theorem planeProj_orthInj_complInj_of_det {k : ℕ} (A : Fin 8 → Euc (8 + k))
    (S : ChartIdx 8 k) (hS : (frameMatrix S A).det ≠ 0) (w : Fin k → ℝ) :
    planeProj A S hS (orthInj A (complInj S w)) = w := by
  have hproj : planeProj A S hS (complInj S w) = w := by
    have h1 := congrArg (fun g => g w) (planeProj_planeInj A S hS)
    simpa [planeInj] using h1
  rw [orthInj, LinearMap.sub_apply, LinearMap.id_apply, map_sub, hproj,
    planeProj_orthProj A S hS (complInj S w), sub_zero]

/-- **`coverP` and `coverI` are mutually inverse at every index and every point**: on the base set
of the index this is `planeProj_orthInj_complInj_of_det`, and off it both are the junk values
`complProj S`, `complInj S`, which are mutually inverse. -/
theorem coverP_comp_coverI (f : V.pt → Euc (8 + k)) (i : CoverIdx V k) (x : V.pt) :
    (coverP f i x).comp (coverI f i x) = ContinuousLinearMap.id ℝ (Fin k → ℝ) := by
  by_cases h : coverDet f i x ≠ 0
  · rw [coverP, dif_pos h, coverI, dif_pos h]
    refine ContinuousLinearMap.ext fun w => ?_
    show planeProj (coverFrame f i x) i.2 h
      ((orthInj (coverFrame f i x)) ((complInj i.2) w)) = w
    exact planeProj_orthInj_complInj_of_det (coverFrame f i x) i.2 h w
  · rw [coverP, dif_neg h, coverI, dif_neg h]
    refine ContinuousLinearMap.ext fun w => ?_
    show complProj i.2 (complInj i.2 w) = w
    have h1 := congrArg (fun g => g w) (complProj_complInj i.2)
    simpa using h1

/-! ## The linear algebra of the construction -/

/-- **The kernel of the projection of the index `(i,S)` is the plane of the frame**, on the base
set, where the projection is `planeProj` (`ker_planeProj`). -/
theorem ker_coverP (f : V.pt → Euc (8 + k)) (i : CoverIdx V k) (x : V.pt)
    (hx : x ∈ coverBaseSet f i) :
    LinearMap.ker ((coverP f i x : (Fin (8 + k) → ℝ) →L[ℝ] (Fin k → ℝ)) :
        (Fin (8 + k) → ℝ) →ₗ[ℝ] (Fin k → ℝ))
      = LinearMap.range (coeffMap (coverFrame f i x)) := by
  have h : coverDet f i x ≠ 0 := hx.2
  rw [show ((coverP f i x : (Fin (8 + k) → ℝ) →L[ℝ] (Fin k → ℝ)) :
        (Fin (8 + k) → ℝ) →ₗ[ℝ] (Fin k → ℝ))
      = planeProj (coverFrame f i x) i.2 h from by
    rw [coverP, dif_pos h]; rfl]
  exact ker_planeProj (coverFrame f i x) i.2 h

/-- **The kernels of the projections of two indices agree on the overlap**: the plane of an
immersion does not depend on the chart (`range_coeffMap_frame_agree`). -/
theorem ker_coverP_agree (f : V.pt → Euc (8 + k))
    (hf : ContMDiff (𝓡 8) (𝓡 (8 + k)) 1 f)
    (i j : CoverIdx V k) (x : V.pt)
    (hi : x ∈ coverBaseSet f i) (hj : x ∈ coverBaseSet f j) :
    LinearMap.ker ((coverP f i x : (Fin (8 + k) → ℝ) →L[ℝ] (Fin k → ℝ)) :
        (Fin (8 + k) → ℝ) →ₗ[ℝ] (Fin k → ℝ))
      = LinearMap.ker ((coverP f j x : (Fin (8 + k) → ℝ) →L[ℝ] (Fin k → ℝ)) :
        (Fin (8 + k) → ℝ) →ₗ[ℝ] (Fin k → ℝ)) := by
  rw [ker_coverP f i x hi, ker_coverP f j x hj]
  exact range_coeffMap_frame_agree f hf (coverChart i) (coverChart j) hi.1 hj.1

/-! ## The cover is a cover -/

/-- **A chosen index over each point**: a chart of the finite cover containing `x`
(`chartCover_spec`) together with an admissible chart index of the Grassmannian for the frame of the
immersion in that chart (`exists_chartIdx_frame`, from the injectivity of `mfderiv`). -/
noncomputable def coverIndexAt (f : V.pt → Euc (8 + k))
    (hf : ContMDiff (𝓡 8) (𝓡 (8 + k)) 1 f)
    (hinj : ∀ x : V.pt, Function.Injective (mfderiv (𝓡 8) (𝓡 (8 + k)) f x))
    (x : V.pt) : CoverIdx V k :=
  (Classical.choose (Work.Thom.chartCover_spec (H := Euc 8) (M := V.pt) x),
   Classical.choose (exists_chartIdx_frame f hf hinj
     (Work.Thom.chartCover (H := Euc 8) (M := V.pt)
       (Classical.choose (Work.Thom.chartCover_spec (H := Euc 8) (M := V.pt) x)))
     (Classical.choose_spec (Work.Thom.chartCover_spec (H := Euc 8) (M := V.pt) x))))

/-- The chosen index over `x` lies over `x`. -/
theorem mem_coverBaseSet_indexAt (f : V.pt → Euc (8 + k))
    (hf : ContMDiff (𝓡 8) (𝓡 (8 + k)) 1 f)
    (hinj : ∀ x : V.pt, Function.Injective (mfderiv (𝓡 8) (𝓡 (8 + k)) f x))
    (x : V.pt) : x ∈ coverBaseSet f (coverIndexAt f hf hinj x) := by
  refine ⟨Classical.choose_spec (Work.Thom.chartCover_spec (H := Euc 8) (M := V.pt) x),
    Classical.choose_spec (exists_chartIdx_frame f hf hinj
      (Work.Thom.chartCover (H := Euc 8) (M := V.pt)
        (Classical.choose (Work.Thom.chartCover_spec (H := Euc 8) (M := V.pt) x)))
      (Classical.choose_spec (Work.Thom.chartCover_spec (H := Euc 8) (M := V.pt) x)))⟩

/-! ## Continuity of the projection and the insertion -/

/-- **The projection depends continuously on the point on the base set**: it is `planeProj` of the
continuous frame, which is continuous in the frame (`continuous_planeProj_family`); the frame of the
chart representative of a `C¹` map is continuous on the chart's source (`continuousOn_frame`). -/
theorem continuousOn_coverP (f : V.pt → Euc (8 + k))
    (hf : ContMDiff (𝓡 8) (𝓡 (8 + k)) 1 f) (i : CoverIdx V k) :
    ContinuousOn (fun x => coverP f i x) (coverBaseSet f i) := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous fun p : ↥(coverBaseSet f i) => coverP f i p.1
  have hF : Continuous fun p : ↥(coverBaseSet f i) => coverFrame f i p.1 :=
    continuousOn_iff_continuous_domRestrict.mp
      ((continuousOn_frame f hf (coverChart i)).mono Set.inter_subset_left)
  have hd : ∀ p : ↥(coverBaseSet f i), (frameMatrix i.2 (coverFrame f i p.1)).det ≠ 0 :=
    fun p => p.2.2
  refine (continuous_planeProj_family (fun p : ↥(coverBaseSet f i) => coverFrame f i p.1) hF
    i.2 hd).congr fun p => ?_
  rw [coverP, dif_pos (hd p)]

/-- **The insertion depends continuously on the point on the base set**: it is the orthogonal
insertion of the plane followed by the coordinate insertion, and the orthogonal projection onto the
plane is continuous in the frame (`continuousOn_orthProjCLM`), the frame of the immersion being
linearly independent at every point of a chart (`frame_linearIndependent`). -/
theorem continuousOn_coverI (f : V.pt → Euc (8 + k))
    (hf : ContMDiff (𝓡 8) (𝓡 (8 + k)) 1 f)
    (hinj : ∀ x : V.pt, Function.Injective (mfderiv (𝓡 8) (𝓡 (8 + k)) f x))
    (i : CoverIdx V k) :
    ContinuousOn (fun x => coverI f i x) (coverBaseSet f i) := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous fun p : ↥(coverBaseSet f i) => coverI f i p.1
  have hF : Continuous fun p : ↥(coverBaseSet f i) => coverFrame f i p.1 :=
    continuousOn_iff_continuous_domRestrict.mp
      ((continuousOn_frame f hf (coverChart i)).mono Set.inter_subset_left)
  have hLI : ∀ p : ↥(coverBaseSet f i), LinearIndependent ℝ (coverFrame f i p.1) :=
    fun p => frame_linearIndependent f hf hinj (coverChart i) p.2.1
  have hprojC : Continuous fun p : ↥(coverBaseSet f i) =>
      LinearMap.toContinuousLinearMap (orthProj (coverFrame f i p.1)) :=
    continuousOn_univ.mp (continuousOn_orthProjCLM
      (fun p : ↥(coverBaseSet f i) => coverFrame f i p.1) Set.univ hF.continuousOn
      (fun p _ => hLI p))
  have hone : Continuous fun _ : ↥(coverBaseSet f i) =>
      (1 : (Fin (8 + k) → ℝ) →L[ℝ] (Fin (8 + k) → ℝ)) := continuous_const
  have hJ : Continuous fun p : ↥(coverBaseSet f i) =>
      LinearMap.toContinuousLinearMap (orthInj (coverFrame f i p.1)) := by
    refine (hone.sub hprojC).congr fun p => ?_
    refine ContinuousLinearMap.ext fun w => ?_
    simp [orthInj]
  have hconst : Continuous fun _ : ↥(coverBaseSet f i) =>
      LinearMap.toContinuousLinearMap (complInj i.2) := continuous_const
  refine (hJ.clm_comp hconst).congr fun p => ?_
  rw [coverI, dif_pos (show coverDet f i p.1 ≠ 0 from p.2.2)]

/-! ## The normal bundle of an immersion -/

/-- **The complement data of the normal bundle of an immersion**: the projection `coverP` and the
insertion `coverI` over the finite cover `CoverIdx V k`, with the geometric hypotheses verified
above. -/
noncomputable def coverData (f : V.pt → Euc (8 + k))
    (hf : ContMDiff (𝓡 8) (𝓡 (8 + k)) 1 f)
    (hinj : ∀ x : V.pt, Function.Injective (mfderiv (𝓡 8) (𝓡 (8 + k)) f x)) :
    ComplementData V.pt k (CoverIdx V k) where
  baseSet := coverBaseSet f
  isOpen_baseSet := isOpen_coverBaseSet f hf
  indexAt := coverIndexAt f hf hinj
  mem_baseSet_at := mem_coverBaseSet_indexAt f hf hinj
  P := coverP f
  I := coverI f
  continuousOn_P := continuousOn_coverP f hf
  continuousOn_I := continuousOn_coverI f hf hinj
  P_comp_I := coverP_comp_coverI f
  ker_agree := fun i j x hi hj => ker_coverP_agree f hf i j x hi hj

theorem exists_normalData_of_immersion {V : Work.ThomBordism.Man8} {k : ℕ}
    (f : V.pt → Work.ThomBordism.PontryaginThom.Euc (8 + k))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 8)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (8 + k)))) 1 f)
    (hinj : ∀ x : V.pt, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 8)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (8 + k)))) f x)) :
    Nonempty (Work.ThomBordism.PontryaginThom.NormalData V k f) := by
  have hf' : ContMDiff (𝓡 8) (𝓡 (8 + k)) 1 f := hf
  have hinj' : ∀ x : V.pt, Function.Injective (mfderiv (𝓡 8) (𝓡 (8 + k)) f x) := hinj
  exact ⟨{ D := coverData f hf' hinj'
           baseSet_sub := fun i S x hx => hx.1
           baseSet_det := fun i S x hx => hx.2
           ker_eq_range := fun i S x hx => ker_coverP f (i, S) x hx }⟩

end

end Work.ThomBordism.PontryaginThom
