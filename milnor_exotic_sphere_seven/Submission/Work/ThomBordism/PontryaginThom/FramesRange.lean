import Submission.Work.ThomBordism.PontryaginThom.Frames
import Submission.Work.ThomBordism.PontryaginThom.Splitting

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# The plane of an immersion is chart-independent

`Frames.lean` defines the frame `frame f i x` of the immersion `f` in the chart `i`, and proves its
continuity (`continuousOn_frame`).  This file proves the second fact the construction of the normal
bundle needs: on the overlap of two charts, the two frames span the **same** subspace of `ℝ^{k+8}`
(`range_coeffMap_frame_agree`), i.e. the plane `im (d f_x)` does not depend on the chart.  This is
the chain rule: the chart representatives differ by the (invertible) derivative of the chart change.
-/

open scoped Manifold ContDiff Topology

namespace Work.ThomBordism.PontryaginThom

open Work.ThomBordism.Grassmann

noncomputable section

variable {V : Man8} {k : ℕ}

/-- The chart representative of an immersion is `C¹` on the chart's target. -/
theorem contDiffOn_chartRep (f : V.pt → Euc (8 + k))
    (hf : ContMDiff (𝓡 8) (𝓡 (8 + k)) 1 f) (i : atlas (Euc 8) V.pt) :
    ContDiffOn ℝ 1 (chartRep f i) i.1.target := by
  have hmem : i.1 ∈ IsManifold.maximalAtlas (𝓡 8) 1 V.pt :=
    IsManifold.subset_maximalAtlas (I := 𝓡 8) (n := 1) i.2
  have hsymm : ContMDiffOn 𝓘(ℝ, Euc 8) (𝓡 8) 1 (fun y => i.1.symm y) i.1.target :=
    contMDiffOn_symm_of_mem_maximalAtlas hmem
  have hcomp : ContMDiffOn 𝓘(ℝ, Euc 8) (𝓘(ℝ, Euc (8 + k))) 1
      (fun y => f (i.1.symm y)) i.1.target :=
    (hf.contMDiffOn).comp hsymm (t := Set.univ) (fun y _ => Set.mem_univ (i.1.symm y))
  exact hcomp.contDiffOn

/-- The chart change `y ↦ j (i.symm y)` is differentiable at `i x` on the overlap. -/
theorem differentiableAt_chartChange (i j : atlas (Euc 8) V.pt) {x : V.pt}
    (hi : x ∈ i.1.source) (hj : x ∈ j.1.source) :
    DifferentiableAt ℝ (fun y => j.1 (i.1.symm y)) (i.1 x) := by
  have hmem_i : i.1 ∈ IsManifold.maximalAtlas (𝓡 8) 1 V.pt :=
    IsManifold.subset_maximalAtlas (I := 𝓡 8) (n := 1) i.2
  have hmem_j : j.1 ∈ IsManifold.maximalAtlas (𝓡 8) 1 V.pt :=
    IsManifold.subset_maximalAtlas (I := 𝓡 8) (n := 1) j.2
  have hy₀ : i.1 x ∈ i.1.target := i.1.map_source hi
  have hjx : i.1.symm (i.1 x) ∈ j.1.source := by rw [i.1.left_inv hi]; exact hj
  have hsymm := (contMDiffOn_symm_of_mem_maximalAtlas hmem_i (i.1 x) hy₀).mono
    (Set.inter_subset_left : i.1.target ∩ i.1.symm ⁻¹' j.1.source ⊆ i.1.target)
  have hj' := contMDiffOn_of_mem_maximalAtlas hmem_j (i.1.symm (i.1 x)) hjx
  have hcomp := hj'.comp (i.1 x) hsymm (fun y hy => hy.2)
  have hdiff : DifferentiableWithinAt ℝ (fun y => j.1 (i.1.symm y))
      (i.1.target ∩ i.1.symm ⁻¹' j.1.source) (i.1 x) :=
    (hcomp.contDiffWithinAt).differentiableWithinAt one_ne_zero
  have hcont : ContinuousAt i.1.symm (i.1 x) :=
    (i.1.continuousOn_symm.continuousWithinAt hy₀).continuousAt (i.1.open_target.mem_nhds hy₀)
  exact hdiff.differentiableAt (Filter.inter_mem (i.1.open_target.mem_nhds hy₀)
    (hcont.preimage_mem_nhds (j.1.open_source.mem_nhds hjx)))

/-! ## The plane does not depend on the chart -/

/-- The chart representatives of two charts agree near an overlap point after the chart change. -/
theorem chartRep_eventuallyEq (f : V.pt → Euc (8 + k)) (i j : atlas (Euc 8) V.pt) {x : V.pt}
    (hi : x ∈ i.1.source) (hj : x ∈ j.1.source) :
    chartRep f i =ᶠ[𝓝 (i.1 x)] chartRep f j ∘ (fun y => j.1 (i.1.symm y)) := by
  have hy₀ : i.1 x ∈ i.1.target := i.1.map_source hi
  have hjx : i.1.symm (i.1 x) ∈ j.1.source := by rw [i.1.left_inv hi]; exact hj
  have hcont : ContinuousAt i.1.symm (i.1 x) :=
    (i.1.continuousOn_symm.continuousWithinAt hy₀).continuousAt (i.1.open_target.mem_nhds hy₀)
  filter_upwards [i.1.open_target.mem_nhds hy₀,
    hcont.preimage_mem_nhds (j.1.open_source.mem_nhds hjx)] with y hy hyj
  show f (i.1.symm y) = f (j.1.symm (j.1 (i.1.symm y)))
  rw [j.1.left_inv hyj]

/-- **The chain rule for the chart representatives**: the derivatives of the two chart
representatives differ by the derivative of the chart change. -/
theorem fderiv_chartRep_eq (f : V.pt → Euc (8 + k))
    (hf : ContMDiff (𝓡 8) (𝓡 (8 + k)) 1 f) (i j : atlas (Euc 8) V.pt) {x : V.pt}
    (hi : x ∈ i.1.source) (hj : x ∈ j.1.source) :
    fderiv ℝ (chartRep f i) (i.1 x)
      = (fderiv ℝ (chartRep f j) (j.1 x)).comp
          (fderiv ℝ (fun y => j.1 (i.1.symm y)) (i.1 x)) := by
  let φ : Euc 8 → Euc 8 := fun y => j.1 (i.1.symm y)
  have hφ0 : φ (i.1 x) = j.1 x := by simp only [φ, i.1.left_inv hi]
  have hdj : DifferentiableAt ℝ (chartRep f j) (j.1 x) :=
    (((contDiffOn_chartRep f hf j).differentiableOn one_ne_zero) (j.1 x) (j.1.map_source hj))
      |>.differentiableAt (j.1.open_target.mem_nhds (j.1.map_source hj))
  have hdφ : DifferentiableAt ℝ φ (i.1 x) := differentiableAt_chartChange i j hi hj
  have heq : chartRep f i =ᶠ[𝓝 (i.1 x)] chartRep f j ∘ φ := chartRep_eventuallyEq f i j hi hj
  rw [heq.fderiv_eq]
  rw [fderiv_comp (𝕜 := ℝ) (i.1 x) (by rw [hφ0]; exact hdj) hdφ]
  rw [hφ0]

/-- The standard-basis expansion in `Fin 8 → ℝ`. -/
theorem sum_single_smul (v : Fin 8 → ℝ) : ∑ l, v l • Pi.single l 1 = v := by
  funext r
  rw [Finset.sum_apply, Finset.sum_eq_single r]
  · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  · intro b _ hb
    rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb), smul_eq_mul, mul_zero]
  · intro h; exact absurd (Finset.mem_univ r) h

/-- `coeffMap f v` is the image under `eucToFun` of the linear combination `∑ j, v j • f j`. -/
theorem coeffMap_eq_sum (f : Fin 8 → Euc (8 + k)) (v : Fin 8 → ℝ) :
    coeffMap f v = eucToFun (8 + k) (∑ j, v j • f j) := by
  funext r
  rw [coeffMap_apply]
  rw [show eucToFun (8 + k) (∑ j, v j • f j) = ∑ j, v j • eucToFun (8 + k) (f j) from by
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => (map_smul _ _ _).trans rfl]
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl fun j _ => by
    rw [Pi.smul_apply, smul_eq_mul, eucToFun_apply]
    rfl

/-- The standard-basis expansion in `ℝⁿ`, in the euclidean space. -/
theorem sum_smul_single_eq_funToEuc (v : Fin 8 → ℝ) :
    ∑ l, v l • EuclideanSpace.single l 1 = funToEuc 8 v := by
  rw [show (∑ l, v l • EuclideanSpace.single l 1)
      = ∑ l, funToEuc 8 (v l • Pi.single l 1) from
    Finset.sum_congr rfl fun l _ => by
      rw [map_smul]
      rfl]
  rw [← map_sum, sum_single_smul]

/-- **The plane of the frame does not depend on the chart** (one inclusion), by the chain rule. -/
theorem range_coeffMap_frame_le (f : V.pt → Euc (8 + k))
    (hf : ContMDiff (𝓡 8) (𝓡 (8 + k)) 1 f) (i j : atlas (Euc 8) V.pt) {x : V.pt}
    (hi : x ∈ i.1.source) (hj : x ∈ j.1.source) :
    LinearMap.range (coeffMap (frame f i x)) ≤ LinearMap.range (coeffMap (frame f j x)) := by
  rintro w ⟨v, rfl⟩
  set Z : Euc 8 := (fderiv ℝ (fun y => j.1 (i.1.symm y)) (i.1 x)) (funToEuc 8 v) with hZ
  have hY : (fderiv ℝ (chartRep f j) (j.1 x)) Z
      = ∑ m, (eucToFun 8 Z) m • frame f j x m := by
    conv_lhs => rw [show Z = ∑ m, (eucToFun 8 Z) m • EuclideanSpace.single m 1 from by
      rw [sum_smul_single_eq_funToEuc, funToEuc_eucToFun]]
    rw [map_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [map_smul]; rfl
  have hL : (∑ l, v l • frame f i x l)
      = (fderiv ℝ (chartRep f i) (i.1 x)) (funToEuc 8 v) := by
    rw [show (∑ l, v l • frame f i x l)
        = ∑ l, (fderiv ℝ (chartRep f i) (i.1 x)) (v l • EuclideanSpace.single l 1) from
      Finset.sum_congr rfl fun l _ => by rw [map_smul]; rfl,
      ← map_sum, sum_smul_single_eq_funToEuc]
  have hkey : (∑ l, v l • frame f i x l) = ∑ m, (eucToFun 8 Z) m • frame f j x m := by
    rw [hL, fderiv_chartRep_eq f hf i j hi hj, ContinuousLinearMap.comp_apply]
    exact hY
  refine LinearMap.mem_range.mpr ⟨eucToFun 8 Z, ?_⟩
  rw [coeffMap_eq_sum, coeffMap_eq_sum, hkey]

/-- **The plane of an immersion does not depend on the chart**: on the overlap of two charts, the
frames of `im (d f_x)` span the same subspace of `ℝ^{k+8}`.  This is the chain rule
(`fderiv_chartRep_eq`) in both directions. -/
theorem range_coeffMap_frame_agree (f : V.pt → Euc (8 + k))
    (hf : ContMDiff (𝓡 8) (𝓡 (8 + k)) 1 f) (i j : atlas (Euc 8) V.pt) {x : V.pt}
    (hi : x ∈ i.1.source) (hj : x ∈ j.1.source) :
    LinearMap.range (coeffMap (frame f i x)) = LinearMap.range (coeffMap (frame f j x)) :=
  le_antisymm (range_coeffMap_frame_le f hf i j hi hj) (range_coeffMap_frame_le f hf j i hj hi)

/-- The preferred chart at `x`, as an element of the atlas. -/
def chartAtIdx (x : V.pt) : atlas (Euc 8) V.pt :=
  ⟨chartAt (Euc 8) x, ChartedSpace.chart_mem_atlas x⟩

@[simp] theorem chartAtIdx_val (x : V.pt) : (chartAtIdx x).1 = chartAt (Euc 8) x := rfl

/-- **`mfderiv` in the preferred chart**: for the self models, `mfderiv f x` is the derivative of
the preferred chart representative `f ∘ (chartAt x).symm` at `(chartAt x) x`. -/
theorem mfderiv_eq_fderiv_chartAt (f : V.pt → Euc (8 + k))
    (hf : ContMDiff (𝓡 8) (𝓡 (8 + k)) 1 f) (x : V.pt) :
    mfderiv (𝓡 8) (𝓡 (8 + k)) f x
      = fderiv ℝ (fun y => f ((chartAt (Euc 8) x).symm y)) ((chartAt (Euc 8) x) x) := by
  have hx₀ : x ∈ (chartAtIdx x).1.source := mem_chart_source (Euc 8) x
  have hy₀ : (chartAtIdx x).1 x ∈ (chartAtIdx x).1.target := (chartAtIdx x).1.map_source hx₀
  have hdiff : DifferentiableAt ℝ (fun y => f ((chartAt (Euc 8) x).symm y))
      ((chartAt (Euc 8) x) x) :=
    ((contDiffOn_chartRep f hf (chartAtIdx x)).differentiableOn one_ne_zero _ hy₀).differentiableAt
      ((chartAtIdx x).1.open_target.mem_nhds hy₀)
  refine HasMFDerivAt.mfderiv ?_
  refine ⟨hf.continuous.continuousAt, ?_⟩
  rw [show writtenInExtChartAt (𝓡 8) (𝓡 (8 + k)) x f
      = (fun y => f ((chartAt (Euc 8) x).symm y)) from by
    funext y
    simp only [writtenInExtChartAt, Function.comp_apply, extChartAt_self_eq,
      modelWithCornersSelf_coe, Function.id_comp]
    rfl,
    show Set.range (𝓡 8) = Set.univ from ModelWithCorners.range_eq_univ (𝓡 8),
    show (extChartAt (𝓡 8) x) x = (chartAt (Euc 8) x) x from rfl]
  exact hdiff.hasFDerivAt.hasFDerivWithinAt

/-- **The plane of the frame is the image of `mfderiv`**: the range of the frame's coordinate map is
the image of the derivative of `f` at `x`, transported to the coordinates of `ℝ^{k+8}`. -/
theorem range_coeffMap_frame_eq_mfderiv (f : V.pt → Euc (8 + k))
    (hf : ContMDiff (𝓡 8) (𝓡 (8 + k)) 1 f) (i : atlas (Euc 8) V.pt) {x : V.pt}
    (hx : x ∈ i.1.source) :
    LinearMap.range (coeffMap (frame f i x))
      = Submodule.map (eucToFun (8 + k)).toLinearMap
          (LinearMap.range ((mfderiv (𝓡 8) (𝓡 (8 + k)) f x).toLinearMap)) := by
  have hmem : x ∈ (chartAtIdx x).1.source := mem_chart_source (Euc 8) x
  have hcr : fderiv ℝ (chartRep f (chartAtIdx x)) ((chartAtIdx x).1 x)
      = mfderiv (𝓡 8) (𝓡 (8 + k)) f x := (mfderiv_eq_fderiv_chartAt f hf x).symm
  refine le_antisymm ?_ ?_
  · rintro w ⟨v, rfl⟩
    rw [coeffMap_eq_sum]
    have hL : (∑ l, v l • frame f i x l)
        = (fderiv ℝ (chartRep f i) (i.1 x)) (funToEuc 8 v) := by
      rw [show (∑ l, v l • frame f i x l)
          = ∑ l, (fderiv ℝ (chartRep f i) (i.1 x)) (v l • EuclideanSpace.single l 1) from
        Finset.sum_congr rfl fun l _ => by rw [map_smul]; rfl,
        ← map_sum, sum_smul_single_eq_funToEuc]
    rw [hL, fderiv_chartRep_eq f hf i (chartAtIdx x) hx hmem,
      ContinuousLinearMap.comp_apply, hcr]
    refine Submodule.mem_map_of_mem ?_
    exact ⟨(fderiv ℝ (fun y => (chartAtIdx x).1 (i.1.symm y)) (i.1 x)) (funToEuc 8 v), rfl⟩
  · intro z hz
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hz
    obtain ⟨u₀, rfl⟩ := hu
    rw [show mfderiv (𝓡 8) (𝓡 (8 + k)) f x
        = fderiv ℝ (chartRep f (chartAtIdx x)) ((chartAtIdx x).1 x) from hcr.symm,
      fderiv_chartRep_eq f hf (chartAtIdx x) i hmem hx]
    change eucToFun (8 + k) ((fderiv ℝ (chartRep f i) (i.1 x))
        ((fderiv ℝ (fun y => i.1 ((chartAtIdx x).1.symm y)) ((chartAtIdx x).1 x)) u₀))
      ∈ LinearMap.range (coeffMap (frame f i x))
    set Z : Euc 8 := (fderiv ℝ (fun y => i.1 ((chartAtIdx x).1.symm y)) ((chartAtIdx x).1 x)) u₀
      with hZ
    have hY : (fderiv ℝ (chartRep f i) (i.1 x)) Z
        = ∑ m, (eucToFun 8 Z) m • frame f i x m := by
      conv_lhs => rw [show Z = ∑ m, (eucToFun 8 Z) m • EuclideanSpace.single m 1 from by
        rw [sum_smul_single_eq_funToEuc, funToEuc_eucToFun]]
      rw [map_sum]
      exact Finset.sum_congr rfl fun m _ => by rw [map_smul]; rfl
    rw [hY]
    refine LinearMap.mem_range.mpr ⟨eucToFun 8 Z, ?_⟩
    rw [coeffMap_eq_sum]

/-- **The frame of an immersion is linearly independent in every chart** (the derivative of an
immersion is injective, and the range of the frame is the image of that derivative). -/
theorem frame_linearIndependent (f : V.pt → Euc (8 + k))
    (hf : ContMDiff (𝓡 8) (𝓡 (8 + k)) 1 f)
    (hinj : ∀ x : V.pt, Function.Injective (mfderiv (𝓡 8) (𝓡 (8 + k)) f x))
    (i : atlas (Euc 8) V.pt) {x : V.pt} (hx : x ∈ i.1.source) :
    LinearIndependent ℝ (frame f i x) := by
  have h2 : Module.finrank ℝ ↥(LinearMap.range
      ((mfderiv (𝓡 8) (𝓡 (8 + k)) f x).toLinearMap)) = 8 := by
    haveI : FiniteDimensional ℝ (TangentSpace (𝓡 8) x) :=
      inferInstanceAs (FiniteDimensional ℝ (Euc 8))
    have hrn := LinearMap.finrank_range_add_finrank_ker
      ((mfderiv (𝓡 8) (𝓡 (8 + k)) f x).toLinearMap)
    rw [LinearMap.ker_eq_bot.mpr (hinj x)] at hrn
    simp only [finrank_bot, add_zero] at hrn
    rw [hrn]
    exact finrank_euclideanSpace_fin
  have hker : LinearMap.ker (coeffMap (frame f i x)) = ⊥ := by
    have hdim : Module.finrank ℝ ↥(LinearMap.range (coeffMap (frame f i x))) = 8 := by
      rw [range_coeffMap_frame_eq_mfderiv f hf i hx]
      have hinj_e : Function.Injective (eucToFun (8 + k)) := fun a b h => by
        have := congrArg (funToEuc (8 + k)) h
        simpa only [funToEuc_eucToFun] using this
      rw [← (Submodule.equivMapOfInjective ((eucToFun (8 + k)).toLinearMap) hinj_e
        (LinearMap.range ((mfderiv (𝓡 8) (𝓡 (8 + k)) f x).toLinearMap))).finrank_eq]
      exact h2
    have hrn := LinearMap.finrank_range_add_finrank_ker (coeffMap (frame f i x))
    rw [hdim, Module.finrank_fin_fun] at hrn
    refine Submodule.finrank_eq_zero.mp ?_
    omega
  rw [Fintype.linearIndependent_iff]
  intro v hv m
  have h0 : coeffMap (frame f i x) v = 0 := by rw [coeffMap_eq_sum, hv, map_zero]
  have hv0 : v = 0 := LinearMap.ker_eq_bot.mp hker (by rw [h0, map_zero])
  rw [hv0]
  rfl

/-- **An admissible chart index of the Grassmannian exists for the frame of an immersion**: some
`S : ChartIdx 8 k` projects the plane isomorphically (`det (frameMatrix S (frame f i x)) ≠ 0`). -/
theorem exists_chartIdx_frame (f : V.pt → Euc (8 + k))
    (hf : ContMDiff (𝓡 8) (𝓡 (8 + k)) 1 f)
    (hinj : ∀ x : V.pt, Function.Injective (mfderiv (𝓡 8) (𝓡 (8 + k)) f x))
    (i : atlas (Euc 8) V.pt) {x : V.pt} (hx : x ∈ i.1.source) :
    ∃ S : ChartIdx 8 k, (frameMatrix S (frame f i x)).det ≠ 0 :=
  exists_chartIdx_det_ne_zero (frame f i x) (frame_linearIndependent f hf hinj i hx)

end

end Work.ThomBordism.PontryaginThom