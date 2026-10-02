import Mathlib
import Submission.Work.Projective.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The smooth atlas of `ℂPⁿ`

This module turns the affine charts of `Work.Projective.Basic` into a smooth structure on `ℂPⁿ`:

* `Work.Projective.chart i : OpenPartialHomeomorph (CP n) (Fin n → ℂ)` — the chart at `i`, with
  source `chartSet i` and target all of `Fin n → ℂ`;
* `Work.Projective.atlas n` and the instance `ChartedSpace (Fin n → ℂ) (CP n)`;
* the instance `IsManifold (𝓘(ℝ, Fin n → ℂ)) ∞ (CP n)`, from the smoothness of the transition maps
  `chartFun j ∘ chartInv i` (`Work.Projective.contDiffOn_chartFun_chartInv`);
* `Work.Projective.compactSpace_CP`, `Work.Projective.connectedSpace_CP` — `ℂPⁿ` is compact and
  connected (it is a continuous image of the unit sphere of `ℂ^{n+1}`).

The re-charting of everything over the model `EuclideanSpace ℝ (Fin (2*n))` is in
`Work.Projective.Model`.

## Conventions

The model space is `Fin n → ℂ` with its `ℝ`-vector space structure; `𝓘(ℝ, Fin n → ℂ)` is the
identity model with corners.
-/

open scoped LinearAlgebra.Projectivization Manifold ContDiff Topology

namespace Work.Projective

noncomputable section

/-! ## Continuity of the chart maps -/

/-- The inverse chart map is continuous (it is the quotient map applied to the continuous map
`w ↦ Fin.insertNth i 1 w`). -/
theorem continuous_chartInv {n : ℕ} (i : Fin (n + 1)) : Continuous (chartInv i) :=
  (continuous_cpMk n).comp
    (Continuous.subtype_mk (continuous_insertNth_one i) (insertNth_one_ne_zero i))

/-- The preimage of the chart at `i` under the quotient map. -/
theorem preimage_chartSet_eq {n : ℕ} (i : Fin (n + 1)) :
    cpMk n ⁻¹' chartSet i = {v : {v : CPV n // v ≠ 0} | v.1 i ≠ 0} := by
  ext v
  rw [chartSet_eq_image]
  constructor
  · rintro ⟨w, hw, hweq⟩
    exact (cpMk_eq_iff_coord n w v hweq i).mp hw
  · intro hv
    exact ⟨v, hv, rfl⟩

/-- **The chart at `i` is open in `ℂPⁿ`** (the topology being the quotient topology). -/
theorem isOpen_chartSet {n : ℕ} (i : Fin (n + 1)) : IsOpen (chartSet i) := by
  rw [isOpen_coinduced, preimage_chartSet_eq]
  exact (isOpen_ne_fun (continuous_apply i) continuous_const).preimage continuous_subtype_val

/-- The chart map `chartFun i` is continuous on its chart. -/
theorem continuousOn_chartFun {n : ℕ} (i : Fin (n + 1)) :
    ContinuousOn (chartFun i) (chartSet i) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hq := (isQuotientMap_cpMk n).restrictPreimage_isOpen (isOpen_chartSet i)
  rw [hq.continuous_iff]
  change Continuous ((cpMk n ⁻¹' chartSet i).domRestrict (chartFunAux i))
  rw [← continuousOn_iff_continuous_domRestrict]
  rw [preimage_chartSet_eq]
  refine (continuousOn_iff_continuous_domRestrict).mpr ?_
  apply continuous_pi
  intro k
  exact (continuous_apply (i.succAbove k)).comp
      (continuous_subtype_val.comp continuous_subtype_val) |>.div
    ((continuous_apply i).comp (continuous_subtype_val.comp continuous_subtype_val))
    (fun v => v.2)

/-! ## Smoothness of the transition maps -/

/-- The `m`-th coordinate of `Fin.insertNth i x w` is smooth in `w`. -/
theorem contDiffOn_insertNth_apply {n : ℕ} (i m : Fin (n + 1)) (x : ℂ) (s : Set (Fin n → ℂ)) :
    ContDiffOn ℝ ∞ (fun w : Fin n → ℂ =>
      (Fin.insertNth (α := fun _ => ℂ) i x w) m) s := by
  by_cases hm : m = i
  · subst hm
    refine (contDiffOn_const (c := x) (s := s)).congr ?_
    intro w _
    rw [Fin.insertNth_apply_same]
  · refine ((contDiff_apply ℝ ℂ (removeAbove i m hm)).contDiffOn (s := s)).congr ?_
    intro w _
    exact insertNth_apply_of_ne i m hm x w

/-- `A/B` is smooth on `s` when `A`, `B` are and `B` does not vanish on `s` (`ℂ`-valued version of
`ContDiffOn.div`, which Mathlib states only for `𝕜`-valued functions). -/
theorem contDiffOn_div {n : ℕ} (A B : (Fin n → ℂ) → ℂ) (s : Set (Fin n → ℂ))
    (hA : ContDiffOn ℝ ∞ A s) (hB : ContDiffOn ℝ ∞ B s) (h0 : ∀ w ∈ s, B w ≠ 0) :
    ContDiffOn ℝ ∞ (fun w => A w / B w) s :=
  (ContDiffOn.mul hA (ContDiffOn.inv hB h0)).congr fun w _ => div_eq_mul_inv (A w) (B w)

/-- The transition function `w ↦ ((Fin.insertNth i 1 w) (j.succAbove k) / (Fin.insertNth i 1 w) j)_k`
is smooth on the set where the denominator does not vanish. -/
theorem contDiffOn_transFun {n : ℕ} (i j : Fin (n + 1)) :
    ContDiffOn ℝ ∞ (fun w : Fin n → ℂ => fun k : Fin n =>
      (Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) w) (j.succAbove k) /
      (Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) w) j)
      {w | chartInv i w ∈ chartSet j} := by
  set S : Set (Fin n → ℂ) := {w | chartInv i w ∈ chartSet j} with hS
  rw [contDiffOn_pi]
  intro k
  refine contDiffOn_div _ _ S (contDiffOn_insertNth_apply (s := S) i (j.succAbove k) 1)
    (contDiffOn_insertNth_apply (s := S) i j 1) ?_
  intro w hw
  have hmem : cpMk n ⟨Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) w,
      insertNth_one_ne_zero i w⟩ ∈ chartSet j := by rw [← chartInv_apply i w]; exact hw
  exact (mem_chartSet_iff j _).mp hmem

/-- **The transition map of the affine charts `i` and `j` of `ℂPⁿ` is smooth**, in the form
`w ↦ chartFun j (chartInv i w)` on the set where it is defined. -/
theorem contDiffOn_chartFun_chartInv {n : ℕ} (i j : Fin (n + 1)) :
    ContDiffOn ℝ ∞ (fun w : Fin n → ℂ => chartFun j (chartInv i w))
      {w | chartInv i w ∈ chartSet j} := by
  refine (contDiffOn_transFun i j).congr ?_
  intro w _
  rw [chartInv_apply, chartFun_cpMk]
  rfl

/-! ## The charts and the atlas -/

/-- **The affine chart of `ℂPⁿ` at `i`**, as an open partial homeomorphism onto `Fin n → ℂ`. -/
def chart {n : ℕ} (i : Fin (n + 1)) : OpenPartialHomeomorph (CP n) (Fin n → ℂ) where
  toFun := chartFun i
  invFun := chartInv i
  source := chartSet i
  target := Set.univ
  map_source' := fun _ _ => Set.mem_univ _
  map_target' := fun w _ => chartInv_mem_chartSet i w
  left_inv' := fun p hp => chartInv_chartFun i p hp
  right_inv' := fun w _ => chartFun_chartInv i w
  continuousOn_toFun := continuousOn_chartFun i
  continuousOn_invFun := (continuous_chartInv i).continuousOn
  open_source := isOpen_chartSet i
  open_target := isOpen_univ

@[simp] theorem chart_toFun {n : ℕ} (i : Fin (n + 1)) : ⇑(chart i) = chartFun i := rfl

@[simp] theorem chart_symm_toFun {n : ℕ} (i : Fin (n + 1)) :
    ⇑(chart i).symm = chartInv i := rfl

@[simp] theorem chart_source {n : ℕ} (i : Fin (n + 1)) : (chart i).source = chartSet i := rfl

@[simp] theorem chart_target {n : ℕ} (i : Fin (n + 1)) : (chart i).target = Set.univ := rfl

/-- **The atlas of `ℂPⁿ`**: the affine charts. -/
def atlas (n : ℕ) : Set (OpenPartialHomeomorph (CP n) (Fin n → ℂ)) := Set.range (chart (n := n))

theorem chart_mem_atlas {n : ℕ} (i : Fin (n + 1)) : chart i ∈ atlas n := ⟨i, rfl⟩

instance instChartedSpaceCP (n : ℕ) : ChartedSpace (Fin n → ℂ) (CP n) where
  atlas := atlas n
  chartAt p := chart (Classical.choose (exists_mem_chartSet p))
  mem_chart_source p := (Classical.choose_spec (exists_mem_chartSet p))
  chart_mem_atlas p := ⟨Classical.choose (exists_mem_chartSet p), rfl⟩

/-! ## Smoothness of the structure -/

/-- Membership in the `C^n` groupoid attached to the identity model with corners `𝓘(ℝ, E)` is
exactly smoothness of the map and of its inverse on their sources and targets. -/
theorem mem_contDiffGroupoid_self_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {e : OpenPartialHomeomorph E E} :
    e ∈ contDiffGroupoid ∞ (𝓘(ℝ, E)) ↔
      ContDiffOn ℝ ∞ ⇑e e.source ∧ ContDiffOn ℝ ∞ ⇑e.symm e.target := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid]
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.preimage_id,
    Set.range_id, Set.inter_univ, Function.comp_id, Function.id_comp]

/-- The transition map of two charts is a `C^∞` element of the groupoid of the identity model. -/
theorem chart_symm_trans_chart_mem {n : ℕ} (i j : Fin (n + 1)) :
    (chart i).symm ≫ₕ (chart j) ∈ contDiffGroupoid ∞ (𝓘(ℝ, Fin n → ℂ)) := by
  rw [mem_contDiffGroupoid_self_iff]
  constructor
  · refine (contDiffOn_chartFun_chartInv i j).congr_mono ?_ ?_
    · intro w _
      rfl
    · intro w hw
      rw [OpenPartialHomeomorph.trans_source] at hw
      exact hw.2
  · refine (contDiffOn_chartFun_chartInv j i).congr_mono ?_ ?_
    · intro w _
      rfl
    · intro w hw
      rw [OpenPartialHomeomorph.trans_target] at hw
      exact hw.2

/-- **`ℂPⁿ` is a smooth manifold**, modelled on `Fin n → ℂ` (`= ℝ^{2n}`). -/
instance instIsManifoldCP (n : ℕ) : IsManifold (𝓘(ℝ, Fin n → ℂ)) ∞ (CP n) where
  compatible := by
    intro e e' he he'
    obtain ⟨i, rfl⟩ := he
    obtain ⟨j, rfl⟩ := he'
    exact chart_symm_trans_chart_mem i j

/-! ## Compactness and connectedness -/

/-- The point `[1 : 1 : ⋯ : 1]` of `ℂPⁿ`, which lies in every affine chart. -/
def allOnesCP (n : ℕ) : CP n :=
  cpMk n ⟨fun _ => (1 : ℂ), fun h => one_ne_zero (congrFun h 0)⟩

/-- `ℂPⁿ` is nonempty (it contains `[1 : ⋯ : 1]`). -/
theorem nonempty_CP (n : ℕ) : Nonempty (CP n) := ⟨allOnesCP n⟩

theorem allOnesCP_mem_chartSet {n : ℕ} (i : Fin (n + 1)) : allOnesCP n ∈ chartSet i := by
  rw [chartSet_eq_image]
  exact ⟨⟨fun _ => (1 : ℂ), fun h => one_ne_zero (congrFun h 0)⟩, by simp, rfl⟩

/-- A vector of norm `1` is nonzero. -/
theorem sphere_ne_zero {n : ℕ} {v : CPV n} (hv : v ∈ Metric.sphere (0 : CPV n) 1) : v ≠ 0 := by
  intro h
  have h1 : ‖v‖ = 1 := by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hv
    exact hv
  rw [h, norm_zero] at h1
  norm_num at h1

/-- The quotient map from the unit sphere of `ℂ^{n+1}` onto `ℂPⁿ`. -/
def unitSphereMap (n : ℕ) : ↥(Metric.sphere (0 : CPV n) 1) → CP n :=
  fun v => cpMk n ⟨v.1, sphere_ne_zero v.2⟩

theorem continuous_unitSphereMap (n : ℕ) : Continuous (unitSphereMap n) :=
  (continuous_cpMk n).comp (Continuous.subtype_mk continuous_subtype_val _)

theorem unitSphereMap_surjective (n : ℕ) : Function.Surjective (unitSphereMap n) := by
  intro p
  obtain ⟨v, rfl⟩ := cpMk_surjective n p
  have hv : (v : CPV n) ≠ 0 := v.2
  have hne : ‖(v : CPV n)‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  set x : CPV n := (‖(v : CPV n)‖)⁻¹ • (v : CPV n) with hx
  have hnorm : ‖x‖ = 1 := by
    rw [hx, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ hne]
  have hmem : x ∈ Metric.sphere (0 : CPV n) 1 := by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact hnorm
  refine ⟨⟨x, hmem⟩, ?_⟩
  change cpMk n ⟨x, sphere_ne_zero hmem⟩ = cpMk n v
  refine (cpMk_eq_iff n ⟨x, sphere_ne_zero hmem⟩ v).mpr
    ⟨((‖(v : CPV n)‖ : ℂ))⁻¹, ?_⟩
  change ((‖(v : CPV n)‖ : ℂ))⁻¹ • (v : CPV n) = x
  rw [hx]
  ext k
  simp

/-- **`ℂPⁿ` is compact**: it is the continuous image of the unit sphere of `ℂ^{n+1}`. -/
theorem compactSpace_CP (n : ℕ) : CompactSpace (CP n) := by
  have : CompactSpace ↥(Metric.sphere (0 : CPV n) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : CPV n) 1)
  rw [← isCompact_univ_iff]
  have h := isCompact_univ.image (continuous_unitSphereMap n)
  rwa [Set.image_univ, Set.range_eq_univ.mpr (unitSphereMap_surjective n)] at h

/-- Each affine chart of `ℂPⁿ` is preconnected (it is the continuous image of `Fin n → ℂ`). -/
theorem isPreconnected_chartSet {n : ℕ} (i : Fin (n + 1)) : IsPreconnected (chartSet i) :=
  isPreconnected_range (continuous_chartInv i)

/-- **`ℂPⁿ` is connected**: it is the union of its affine charts, all of which contain the point
`[1 : ⋯ : 1]`. -/
theorem connectedSpace_CP (n : ℕ) : ConnectedSpace (CP n) := by
  rw [connectedSpace_iff_univ]
  have hunion : (Set.univ : Set (CP n)) = ⋃ i, chartSet i := by
    ext p
    simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
    exact exists_mem_chartSet p
  rw [hunion]
  exact ⟨⟨allOnesCP n, by
      simp only [Set.mem_iUnion]
      exact ⟨0, allOnesCP_mem_chartSet 0⟩⟩,
    isPreconnected_iUnion ⟨allOnesCP n, by
      simp only [Set.mem_iInter]
      exact fun i => allOnesCP_mem_chartSet i⟩ (fun i => isPreconnected_chartSet i)⟩

end

end Work.Projective
