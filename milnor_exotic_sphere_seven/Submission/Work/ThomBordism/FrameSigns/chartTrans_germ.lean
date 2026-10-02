import Mathlib
import Submission.Work.ThomBordism.FrameSigns.Charts
import Submission.Work.ThomBordism.PontryaginThom.TangentCompat
import Submission.Work.TangentClasses.Tangent

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.ThomBordism.FrameSigns

noncomputable section

open scoped Manifold ContDiff Topology

/-- The model space `ℝ⁸`, as a **file-local** notation.  The abbreviation `E8` is deliberately not
declared globally in this directory any more (`FrameSigns/Defs.lean` uses the explicit type), since
`germFDeriv.lean` declares its own `E8` and the two modules must be importable together
(e.g. in `chartCoh_compare.lean`).  The statement of `chartTrans_germ` below is spelled with `E8`
exactly as requested; this local notation is its definition. -/
local notation "E8" => EuclideanSpace ℝ (Fin 8)

/-!
## The transition germ between two charts of the finite cover

The pieces of `chartTrans_germ`, proved below:

* `chartTrans_germ_set_eq_image` — the germ set is the translate by `−eᵢ x` of the image of the
  overlap under the chart `eᵢ`;
* `chartTrans_germ_isOpen` — hence open, since an open partial homeomorphism is an open map on its
  source and translations are homeomorphisms;
* `chartTrans_germ_zero_mem` — `0 = eᵢ x − eᵢ x` lies in it;
* `chartTrans_germ_mapsTo` / `chartTrans_germ_continuousOn` — the map
  `w ↦ eᵢ⁻¹ (w + eᵢ x)` carries the germ set into the overlap, where `w ↦ eⱼ w − eⱼ x` is
  continuous; composing gives the continuity of the germ;
* `chartTrans_germ_ne_zero` — injectivity of `eᵢ` and `eⱼ` on their sources;
* `chartTrans_germ_hasFDerivAt` — the chain rule with the translation;
* `chartTrans_germ_fderiv_inverse` / `chartTrans_germ_bijective` — the derivative of the chart
  change is invertible: the transition `eᵢ ∘ eⱼ⁻¹` is a local inverse of `eⱼ ∘ eᵢ⁻¹`, and the chain
  rule applied to both composites gives the two one-sided inverse identities for the derivatives. -/

/-- The germ set is the translate by `−eᵢ x` of the image of the overlap of the two chart sources
under the chart `eᵢ`. -/
theorem chartTrans_germ_set_eq_image (V : Man8) (i j : ChartIdx V) (x : V.pt) :
    germSet V i j x
      = (fun v : E8 => v - (chartOf V i).1 x)
          '' ((chartOf V i).1 '' (src V i ∩ src V j)) := by
  rw [germSet]
  rw [show (fun z : V.pt => (chartOf V i).1 z - (chartOf V i).1 x)
      = (fun v : E8 => v - (chartOf V i).1 x) ∘ (chartOf V i).1 from rfl,
    Set.image_comp]

/-- **The germ set is open**: it is the image of the open set `src V i ∩ src V j` under the chart
`eᵢ` (an open map on its source), translated. -/
theorem chartTrans_germ_isOpen (V : Man8) (i j : ChartIdx V) (x : V.pt) :
    IsOpen (germSet V i j x) := by
  rw [chartTrans_germ_set_eq_image]
  have hbase : IsOpen ((chartOf V i).1 '' (src V i ∩ src V j)) :=
    (chartOf V i).1.isOpen_image_of_subset_source
      ((chartOf V i).1.open_source.inter (chartOf V j).1.open_source)
      Set.inter_subset_left
  rw [show (fun v : E8 => v - (chartOf V i).1 x)
      = (fun v : E8 => -(chartOf V i).1 x + v) from by
    funext v
    simp [sub_eq_add_neg, add_comm]]
  exact isOpenMap_add_left (-(chartOf V i).1 x) _ hbase

/-- **`0` lies in the germ set** (at the image of `x`, which is in both sources). -/
theorem chartTrans_germ_zero_mem (V : Man8) (i j : ChartIdx V) {x : V.pt}
    (hi : x ∈ src V i) (hj : x ∈ src V j) :
    (0 : E8) ∈ germSet V i j x := by
  refine ⟨x, ⟨hi, hj⟩, ?_⟩
  simp

/-- **The translated chart of `i` inverted carries the germ set into the overlap**: for
`w = eᵢ z − eᵢ x` with `z` in the overlap, `eᵢ⁻¹ (w + eᵢ x) = z`. -/
theorem chartTrans_germ_mapsTo (V : Man8) (i j : ChartIdx V) (x : V.pt) :
    Set.MapsTo (fun w : E8 => (chartOf V i).1.symm (w + (chartOf V i).1 x))
      (germSet V i j x) (src V i ∩ src V j) := by
  intro w hw
  obtain ⟨z, hz, hwz⟩ := hw
  rw [← hwz]
  simp only [sub_add_cancel, (chartOf V i).1.left_inv hz.1]
  exact hz

/-- **The transition germ is continuous on the germ set**: it is the composite of the (continuous on
the overlap) map `z ↦ eⱼ z − eⱼ x` with the inverse of the translated chart `i`. -/
theorem chartTrans_germ_continuousOn (V : Man8) (i j : ChartIdx V) (x : V.pt) :
    ContinuousOn (germFun V i j x) (germSet V i j x) := by
  have hψ : ContinuousOn (fun w : E8 => (chartOf V i).1.symm (w + (chartOf V i).1 x))
      (germSet V i j x) :=
    (chartOf V i).1.continuousOn_symm.comp
      ((continuous_id.add (continuous_const : Continuous fun _ : E8 => (chartOf V i).1 x)).continuousOn.mono
        (Set.subset_univ _))
      (fun w hw => by
        obtain ⟨z, hz, hwz⟩ := hw
        rw [← hwz]
        simp only [sub_add_cancel]
        exact (chartOf V i).1.map_source hz.1)
  have hζ : ContinuousOn (fun z : V.pt => (chartOf V j).1 z - (chartOf V j).1 x)
      (src V i ∩ src V j) :=
    (((chartOf V j).1.continuousOn.mono Set.inter_subset_right)).sub continuousOn_const
  have h := hζ.comp hψ (chartTrans_germ_mapsTo V i j x)
  refine ContinuousOn.congr h ?_
  intro w hw
  rfl

/-- **The transition germ does not vanish off `0`**: the two charts are injective on their
sources. -/
theorem chartTrans_germ_ne_zero (V : Man8) (i j : ChartIdx V) {x : V.pt}
    (hj : x ∈ src V j) :
    ∀ w ∈ germSet V i j x, w ≠ 0 → germFun V i j x w ≠ 0 := by
  intro w hw hw0 hzero
  obtain ⟨z, hz, hwz⟩ := hw
  have hwz' : w = (chartOf V i).1 z - (chartOf V i).1 x := by
    rw [← hwz]
  rw [hwz'] at hzero hw0
  simp only [germFun, sub_add_cancel, (chartOf V i).1.left_inv hz.1] at hzero
  have hzx : (chartOf V j).1 z = (chartOf V j).1 x := sub_eq_zero.mp hzero
  have hzjeq : z = x := by
    have h1 : z = (chartOf V j).1.symm ((chartOf V j).1 z) :=
      ((chartOf V j).1.left_inv hz.2).symm
    rw [h1, hzx, (chartOf V j).1.left_inv hj]
  refine hw0 ?_
  rw [hzjeq, sub_self]

/-- **The derivative of the germ at `0`**: the chain rule applied to
`germFun = (eⱼ ∘ eᵢ⁻¹) ∘ (translation by eᵢ x)`. -/
theorem chartTrans_germ_hasFDerivAt (V : Man8) (i j : ChartIdx V) {x : V.pt}
    (hi : x ∈ src V i) (hj : x ∈ src V j) :
    HasFDerivAt (germFun V i j x)
      (fderiv ℝ (fun y => chartMap V j ((chartOf V i).1.symm y)) ((chartOf V i).1 x)) 0 := by
  have hd : HasFDerivAt (fun y => chartMap V j ((chartOf V i).1.symm y))
      (fderiv ℝ (fun y => chartMap V j ((chartOf V i).1.symm y)) ((chartOf V i).1 x))
      ((chartOf V i).1 x) :=
    (Work.ThomBordism.PontryaginThom.differentiableAt_chartChange (chartOf V i) (chartOf V j)
      hi hj).hasFDerivAt
  have hT : HasFDerivAt (fun w : E8 => w + (chartOf V i).1 x)
      (ContinuousLinearMap.id ℝ E8) 0 :=
    (hasFDerivAt_id (0 : E8)).add_const _
  have hd' : HasFDerivAt (fun y => chartMap V j ((chartOf V i).1.symm y))
      (fderiv ℝ (fun y => chartMap V j ((chartOf V i).1.symm y)) ((chartOf V i).1 x))
      ((fun w : E8 => w + (chartOf V i).1 x) 0) := by
    show HasFDerivAt (fun y => chartMap V j ((chartOf V i).1.symm y))
      (fderiv ℝ (fun y => chartMap V j ((chartOf V i).1.symm y)) ((chartOf V i).1 x))
      (0 + (chartOf V i).1 x)
    rw [zero_add]
    exact hd
  have hcomp := hd'.comp (0 : E8) hT
  have h0 : HasFDerivAt
      (fun w : E8 => chartMap V j ((chartOf V i).1.symm (w + (chartOf V i).1 x)))
      (fderiv ℝ (fun y => chartMap V j ((chartOf V i).1.symm y)) ((chartOf V i).1 x)) 0 := hcomp
  exact h0.sub_const ((chartOf V j).1 x)

/-- **The transition `eᵢ ∘ eⱼ⁻¹` is an inverse of `eⱼ ∘ eᵢ⁻¹` near `eᵢ x`** (both are identities on
the overlap of the two charts, which is a neighbourhood of the relevant points). -/
theorem chartTrans_germ_comp_eventuallyEq (V : Man8) (i j : ChartIdx V) {x : V.pt}
    (hi : x ∈ src V i) (hj : x ∈ src V j) :
    ((fun y : E8 => chartMap V i ((chartOf V j).1.symm y)) ∘
      (fun y : E8 => chartMap V j ((chartOf V i).1.symm y)))
      =ᶠ[𝓝 ((chartOf V i).1 x)] id := by
  have hy₀ : (chartOf V i).1 x ∈ (chartOf V i).1.target := (chartOf V i).1.map_source hi
  have hjx : (chartOf V i).1.symm ((chartOf V i).1 x) ∈ (chartOf V j).1.source := by
    rw [(chartOf V i).1.left_inv hi]
    exact hj
  have hcont : ContinuousAt (chartOf V i).1.symm ((chartOf V i).1 x) :=
    ((chartOf V i).1.continuousOn_symm.continuousWithinAt hy₀).continuousAt
      ((chartOf V i).1.open_target.mem_nhds hy₀)
  filter_upwards [(chartOf V i).1.open_target.mem_nhds hy₀,
    hcont.preimage_mem_nhds ((chartOf V j).1.open_source.mem_nhds hjx)] with y hy hys
  show chartMap V i ((chartOf V j).1.symm (chartMap V j ((chartOf V i).1.symm y))) = y
  simp only [chartMap_apply, (chartOf V j).1.left_inv hys, (chartOf V i).1.right_inv hy]

/-- **The derivative of the chart change is injective with left inverse the derivative of the
inverse chart change**, by the chain rule applied to `(eᵢ ∘ eⱼ⁻¹) ∘ (eⱼ ∘ eᵢ⁻¹) = id`. -/
theorem chartTrans_germ_fderiv_inverse (V : Man8) (i j : ChartIdx V) {x : V.pt}
    (hi : x ∈ src V i) (hj : x ∈ src V j) :
    (fderiv ℝ (fun y => chartMap V i ((chartOf V j).1.symm y)) ((chartOf V j).1 x)).comp
      (fderiv ℝ (fun y => chartMap V j ((chartOf V i).1.symm y)) ((chartOf V i).1 x))
      = ContinuousLinearMap.id ℝ E8 := by
  have hdφ : DifferentiableAt ℝ (fun y => chartMap V j ((chartOf V i).1.symm y))
      ((chartOf V i).1 x) :=
    Work.ThomBordism.PontryaginThom.differentiableAt_chartChange (chartOf V i) (chartOf V j) hi hj
  have hdψ : DifferentiableAt ℝ (fun y => chartMap V i ((chartOf V j).1.symm y))
      ((chartOf V j).1 x) :=
    Work.ThomBordism.PontryaginThom.differentiableAt_chartChange (chartOf V j) (chartOf V i) hj hi
  have hφ0 : (fun y => chartMap V j ((chartOf V i).1.symm y)) ((chartOf V i).1 x)
      = (chartOf V j).1 x := by
    change chartMap V j ((chartOf V i).1.symm ((chartOf V i).1 x)) = (chartOf V j).1 x
    rw [chartMap_apply, (chartOf V i).1.left_inv hi]
  have hψφ : HasFDerivAt (fun y => chartMap V i ((chartOf V j).1.symm y))
      (fderiv ℝ (fun y => chartMap V i ((chartOf V j).1.symm y)) ((chartOf V j).1 x))
      ((fun y => chartMap V j ((chartOf V i).1.symm y)) ((chartOf V i).1 x)) := by
    rw [hφ0]
    exact hdψ.hasFDerivAt
  have hcomp : HasFDerivAt
      ((fun y => chartMap V i ((chartOf V j).1.symm y)) ∘
        (fun y => chartMap V j ((chartOf V i).1.symm y)))
      ((fderiv ℝ (fun y => chartMap V i ((chartOf V j).1.symm y)) ((chartOf V j).1 x)).comp
        (fderiv ℝ (fun y => chartMap V j ((chartOf V i).1.symm y)) ((chartOf V i).1 x)))
      ((chartOf V i).1 x) :=
    hψφ.comp ((chartOf V i).1 x) hdφ.hasFDerivAt
  have heq := chartTrans_germ_comp_eventuallyEq V i j hi hj
  have h1 : HasFDerivAt ((fun y => chartMap V i ((chartOf V j).1.symm y)) ∘
        (fun y => chartMap V j ((chartOf V i).1.symm y))) (ContinuousLinearMap.id ℝ E8)
      ((chartOf V i).1 x) :=
    (Filter.EventuallyEq.hasFDerivAt_iff heq).mpr (hasFDerivAt_id _)
  exact hcomp.unique h1

/-- **The derivative of the chart change is invertible**: the derivative of the transition is a
bijection, with inverse the derivative of the inverse transition. -/
theorem chartTrans_germ_bijective (V : Man8) (i j : ChartIdx V) {x : V.pt}
    (hi : x ∈ src V i) (hj : x ∈ src V j) :
    Function.Bijective
      (fderiv ℝ (fun y => chartMap V j ((chartOf V i).1.symm y)) ((chartOf V i).1 x)) := by
  have h1 := chartTrans_germ_fderiv_inverse V i j hi hj
  have h2 := chartTrans_germ_fderiv_inverse V j i hj hi
  have h1' : ∀ y : E8,
      (fderiv ℝ (fun y => chartMap V i ((chartOf V j).1.symm y)) ((chartOf V j).1 x))
        ((fderiv ℝ (fun y => chartMap V j ((chartOf V i).1.symm y)) ((chartOf V i).1 x)) y)
      = y := by
    intro y
    have hh := congrArg (fun (T : E8 →L[ℝ] E8) => T y) h1
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using hh
  have h2' : ∀ y : E8,
      (fderiv ℝ (fun y => chartMap V j ((chartOf V i).1.symm y)) ((chartOf V i).1 x))
        ((fderiv ℝ (fun y => chartMap V i ((chartOf V j).1.symm y)) ((chartOf V j).1 x)) y)
      = y := by
    intro y
    have hh := congrArg (fun (T : E8 →L[ℝ] E8) => T y) h2
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using hh
  refine ⟨fun a b hab => ?_, fun b => ⟨_, h2' b⟩⟩
  · have hh := congrArg (fun z => (fderiv ℝ (fun y => chartMap V i ((chartOf V j).1.symm y))
        ((chartOf V j).1 x)) z) hab
    simpa only [h1'] using hh

/-- **The transition germ between two charts of the finite cover is a germ diffeomorphism at `0`,
with the derivative of the chart change, which is invertible.**

`germSet V i j x` is the image of the overlap `src V i ∩ src V j` under the translated chart `i`;
`germFun V i j x w = eⱼ (eᵢ⁻¹ (w + eᵢ x)) − eⱼ x` is the transition function, transported to the
origin.

Suggested route: `germSet` is the image of the open set `src V i ∩ src V j` under the partial
homeomorphism `eᵢ` composed with a translation, hence open and containing `0` (since `x` is in the
overlap).  `germFun = (eⱼ ∘ eᵢ⁻¹) ∘ (translation by eᵢ x)` on `germSet`, and `eⱼ ∘ eᵢ⁻¹` is the
transition between two charts of the atlas of a `C^∞` manifold, hence smooth on the open set
`eᵢ (src V i ∩ src V j)` (`StructureGroupoid.compatible_of_mem_maximalAtlas` with the
`contDiffGroupoid`, or `contDiffWithinAt_ext_coord_change`); this gives continuity; non-vanishing off
`0` is injectivity of `eᵢ⁻¹` and `eⱼ` on their sources.  The derivative at `0` is
`L := fderiv ℝ (fun y => eⱼ (eᵢ⁻¹ y)) (eᵢ x)` by the chain rule with the translation.  For the
invertibility of `L`, the route available in the workspace is via the preferred chart
`c := achart (Euc 8) x`:
`L = B ∘ A` with `A := fderiv ℝ (fun y => c (eᵢ⁻¹ y)) (eᵢ x)` and
`B := fderiv ℝ (fun y => eⱼ (c⁻¹ y)) (c x)` (chain rule, since `eⱼ ∘ eᵢ⁻¹ = (eⱼ ∘ c⁻¹) ∘ (c ∘ eᵢ⁻¹)`
near `eᵢ x`); and each of `A`, `B` is invertible because the composite with its counterpart in the
other direction is the identity, e.g. `B' ∘ A = id` where `B' := fderiv ℝ (fun y => eᵢ (c⁻¹ y)) (c x)`
(chain rule applied to `y ↦ eᵢ (c⁻¹ (c (eᵢ⁻¹ y))) = eᵢ (eᵢ⁻¹ y)`).  Concretely,
`Work.ThomBordism.PontryaginThom.tCoord_tangentBundle_eq`
(`Submission/Work/ThomBordism/PontryaginThom/TangentCompat.lean`) identifies `A` (transported by
`funToEuc`/`eucToFun`) with `tCoord (tangentBundle (𝓡 8) V.pt) i x`, and
`Work.TangentClasses.tangentBundle_prod_coordChange` / `coordChange_comp` /
`coordChange_self` give the inverse identities. -/
theorem chartTrans_germ (V : Man8) (i j : ChartIdx V) {x : V.pt}
    (hi : x ∈ src V i) (hj : x ∈ src V j) :
    IsOpen (germSet V i j x) ∧ (0 : E8) ∈ germSet V i j x ∧
      ContinuousOn (germFun V i j x) (germSet V i j x) ∧
      (∀ w ∈ germSet V i j x, w ≠ 0 → germFun V i j x w ≠ 0) ∧
      HasFDerivAt (germFun V i j x)
        (fderiv ℝ (fun y => chartMap V j ((chartOf V i).1.symm y)) ((chartOf V i).1 x)) 0 ∧
      Function.Bijective (fderiv ℝ (fun y => chartMap V j ((chartOf V i).1.symm y))
        ((chartOf V i).1 x)) :=
  ⟨chartTrans_germ_isOpen V i j x, chartTrans_germ_zero_mem V i j hi hj,
   chartTrans_germ_continuousOn V i j x, chartTrans_germ_ne_zero V i j hj,
   chartTrans_germ_hasFDerivAt V i j hi hj, chartTrans_germ_bijective V i j hi hj⟩

end

end Work.ThomBordism.FrameSigns
