import Mathlib
import Submission.Work.Stems.CollapseDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Continuity of the collapse map `Iⁿ → Iⁿ/∂Iⁿ ≅ Sⁿ`

This file proves that the explicit collapse map `cubeToOnePoint n : Iⁿ → OnePoint ℝⁿ`
of `Submission.Work.Stems.exists_collapsingMap` is continuous.

The map is
`cubeToOnePoint n q = if q ∈ ∂Iⁿ then ∞ else ↑(cubeCoords n q)`,
where `cubeCoords` is given by the coordinate formula `q ↦ (y_i/√(1-y_i²))_i`, `y_i = 2q_i - 1`.

* On the open complement of the boundary, `cubeCoords` is continuous (each coordinate is a
  quotient of continuous functions whose denominator does not vanish), hence so is the map.
* Near a boundary point, one coordinate of `cubeCoords` blows up like `y/√(1-y²)` as
  `y → ±1`, so `cubeToOnePoint` tends to `∞`; the gluing lemma
  `tendsto_of_tendsto_ite` then gives continuity there.
-/

open scoped Topology unitInterval OnePoint
open Filter

namespace Work.Stems

noncomputable section

variable {n : ℕ}

/-! ## A gluing lemma for maps into a one-point compactification -/

/-- If `f` agrees with the constant `∞` on `S` and with the coercion of a map `g` off `S`, and
if `g` tends to `∞` along the filter of points approaching `q₀` from outside `S`, then `f` is
continuous at `q₀` in the sense that it tends to `∞`. -/
theorem tendsto_of_tendsto_ite {X V : Type*} [TopologicalSpace X] [TopologicalSpace V]
    (S : Set X) (q₀ : X) (g : X → V) (f : X → OnePoint V)
    (hS : ∀ x ∈ S, f x = ∞) (hSc : ∀ x ∉ S, f x = (g x : OnePoint V))
    (h : Tendsto (fun x => (g x : OnePoint V)) (𝓝[Sᶜ] q₀) (𝓝 ∞)) :
    Tendsto f (𝓝 q₀) (𝓝 ∞) := by
  rw [Tendsto]
  intro U hU
  rw [mem_map]
  have h1 : (fun x => (g x : OnePoint V)) ⁻¹' U ∈ 𝓝[Sᶜ] q₀ := h hU
  rw [nhdsWithin, Filter.mem_inf_iff_superset] at h1
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := h1
  refine mem_of_superset ht₁ ?_
  intro x hx
  simp only [Set.mem_preimage]
  by_cases hxS : x ∈ S
  · rw [hS x hxS]; exact mem_of_mem_nhds hU
  · rw [hSc x hxS]
    exact hsub ⟨hx, ht₂ hxS⟩

/-! ## The boundary of the cube is closed -/

theorem isClosed_cubeBoundary (n : ℕ) : IsClosed (Cube.boundary (Fin n)) := by
  have h : Cube.boundary (Fin n) =
      ⋃ i : Fin n, ({y : CubeI n | y i = 0} ∪ {y : CubeI n | y i = 1}) := by
    ext y
    simp only [Cube.boundary, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_union]
  rw [h]
  exact isClosed_iUnion_of_finite fun i =>
    (isClosed_eq (continuous_apply i) continuous_const).union
      (isClosed_eq (continuous_apply i) continuous_const)

/-! ## `cubeCoords` is continuous off the boundary -/

/-- On the complement of the boundary `∂Iⁿ` the denominator `√(1 - y_i²)` never vanishes, so
`cubeCoords` is continuous there. -/
theorem continuousAt_cubeCoords_of_not_mem_boundary (n : ℕ) {q : CubeI n}
    (hq : q ∉ Cube.boundary (Fin n)) : ContinuousAt (cubeCoords n) q := by
  have hcoord : ∀ i : Fin n, ContinuousAt (fun x : CubeI n =>
      (2 * (x i : ℝ) - 1) / Real.sqrt (1 - (2 * (x i : ℝ) - 1)^2)) q := by
    intro i
    have hnum : Continuous (fun x : CubeI n => 2 * (x i : ℝ) - 1) := by fun_prop
    have hden : Continuous (fun x : CubeI n => 1 - (2 * (x i : ℝ) - 1)^2) := by fun_prop
    refine ContinuousAt.div hnum.continuousAt (ContinuousAt.sqrt hden.continuousAt) ?_
    have hne0 : (q i : ℝ) ≠ 0 := by
      intro h
      exact hq ⟨i, Or.inl (Subtype.ext (by simpa using h))⟩
    have hne1 : (q i : ℝ) ≠ 1 := by
      intro h
      exact hq ⟨i, Or.inr (Subtype.ext (by simpa using h))⟩
    have hlt1 : (q i : ℝ) < 1 := lt_of_le_of_ne (q i).2.2 hne1
    have hgt0 : (0 : ℝ) < (q i : ℝ) := lt_of_le_of_ne (q i).2.1 (Ne.symm hne0)
    have hy1 : 2 * (q i : ℝ) - 1 < 1 := by linarith
    have hym1 : -1 < 2 * (q i : ℝ) - 1 := by linarith
    have hpos : 0 < 1 - (2 * (q i : ℝ) - 1)^2 := by nlinarith
    exact ne_of_gt (Real.sqrt_pos.mpr hpos)
  have hpi := continuousAt_pi.mpr hcoord
  exact (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous.continuousAt.comp hpi

/-! ## Coordinate bounds for the Euclidean norm

(These only need the fact that the Euclidean norm dominates each coordinate.) -/

theorem cubeCoord_le_norm (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) : x i ≤ ‖x‖ :=
  le_trans (le_abs_self _) (PiLp.norm_apply_le (p := 2) (β := fun _ : Fin n => ℝ) x i)

theorem neg_norm_le_cubeCoord (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    -‖x‖ ≤ x i :=
  le_trans (neg_le_neg (PiLp.norm_apply_le (p := 2) (β := fun _ : Fin n => ℝ) x i))
    (neg_abs_le _)

/-! ## The one-dimensional blow-up `y/√(1-y²)` at `y = ±1` -/

/-- `y / √(1-y²) → +∞` as `y → 1` from below.  (Substitute `y = sin θ`, so that
`y / √(1-y²) = tan θ` and `θ → π/2⁻`.) -/
theorem tendsto_div_sqrt_one_sub_sq_atTop :
    Tendsto (fun y : ℝ => y / Real.sqrt (1 - y ^ 2)) (𝓝[<] (1 : ℝ)) atTop := by
  have h1 : Tendsto Real.arcsin (𝓝[<] (1 : ℝ)) (𝓝[<] (Real.pi / 2)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h : Tendsto Real.arcsin (𝓝 (1 : ℝ)) (𝓝 (Real.arcsin 1)) :=
        Real.continuous_arcsin.continuousAt
      rw [Real.arcsin_one] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact Real.arcsin_lt_pi_div_two.mpr hy
  have hf : Tendsto (fun y : ℝ => Real.tan (Real.arcsin y)) (𝓝[<] (1 : ℝ)) atTop :=
    Real.tendsto_tan_pi_div_two.comp h1
  refine hf.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (-1 : ℝ) < 1)] with y hy
  rw [Real.tan_eq_sin_div_cos, Real.sin_arcsin hy.1.le hy.2.le, Real.cos_arcsin]

/-- `y / √(1-y²) → -∞` as `y → -1` from above. -/
theorem tendsto_div_sqrt_one_sub_sq_atBot :
    Tendsto (fun y : ℝ => y / Real.sqrt (1 - y ^ 2)) (𝓝[>] (-1 : ℝ)) atBot := by
  have h1 : Tendsto Real.arcsin (𝓝[>] (-1 : ℝ)) (𝓝[>] (-(Real.pi / 2))) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h : Tendsto Real.arcsin (𝓝 (-1 : ℝ)) (𝓝 (Real.arcsin (-1))) :=
        Real.continuous_arcsin.continuousAt
      rw [Real.arcsin_neg_one] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact Real.neg_pi_div_two_lt_arcsin.mpr hy
  have hf : Tendsto (fun y : ℝ => Real.tan (Real.arcsin y)) (𝓝[>] (-1 : ℝ)) atBot :=
    Real.tendsto_tan_neg_pi_div_two.comp h1
  refine hf.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (-1 : ℝ) < 1)] with y hy
  rw [Real.tan_eq_sin_div_cos, Real.sin_arcsin hy.1.le hy.2.le, Real.cos_arcsin]

/-! ## One coordinate of `cubeCoords` blows up at a face of the cube -/

/-- If `q` lies on the face `q i = 1`, the `i`-th coordinate of `cubeCoords` tends to `+∞` as
one approaches `q` from inside the cube. -/
theorem tendsto_cubeCoord_atTop (n : ℕ) (i : Fin n) {q : CubeI n} (hq : (q i : ℝ) = 1) :
    Tendsto (fun x : CubeI n => (2 * (x i : ℝ) - 1) / Real.sqrt (1 - (2 * (x i : ℝ) - 1)^2))
      (𝓝[(Cube.boundary (Fin n))ᶜ] q) atTop := by
  have hφ : Tendsto (fun x : CubeI n => 2 * (x i : ℝ) - 1)
      (𝓝[(Cube.boundary (Fin n))ᶜ] q) (𝓝[<] (1 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : ContinuousAt (fun x : CubeI n => 2 * (x i : ℝ) - 1) q :=
        (by fun_prop : Continuous (fun x : CubeI n => 2 * (x i : ℝ) - 1)).continuousAt
      have hval : 2 * (q i : ℝ) - 1 = 1 := by rw [hq]; norm_num
      have h' : Tendsto (fun x : CubeI n => 2 * (x i : ℝ) - 1) (𝓝 q) (𝓝 (2 * (q i : ℝ) - 1)) :=
        hc
      rw [hval] at h'
      exact h'.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have hne : (x i : ℝ) ≠ 1 := fun h => hx ⟨i, Or.inr (Subtype.ext (by simpa using h))⟩
      have hlt : (x i : ℝ) < 1 := lt_of_le_of_ne (x i).2.2 hne
      show 2 * (x i : ℝ) - 1 < 1
      linarith
  simpa only [Function.comp_def] using (tendsto_div_sqrt_one_sub_sq_atTop.comp hφ)

/-- If `q` lies on the face `q i = 0`, the `i`-th coordinate of `cubeCoords` tends to `-∞` as
one approaches `q` from inside the cube. -/
theorem tendsto_cubeCoord_atBot (n : ℕ) (i : Fin n) {q : CubeI n} (hq : (q i : ℝ) = 0) :
    Tendsto (fun x : CubeI n => (2 * (x i : ℝ) - 1) / Real.sqrt (1 - (2 * (x i : ℝ) - 1)^2))
      (𝓝[(Cube.boundary (Fin n))ᶜ] q) atBot := by
  have hφ : Tendsto (fun x : CubeI n => 2 * (x i : ℝ) - 1)
      (𝓝[(Cube.boundary (Fin n))ᶜ] q) (𝓝[>] (-1 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : ContinuousAt (fun x : CubeI n => 2 * (x i : ℝ) - 1) q :=
        (by fun_prop : Continuous (fun x : CubeI n => 2 * (x i : ℝ) - 1)).continuousAt
      have hval : 2 * (q i : ℝ) - 1 = -1 := by rw [hq]; norm_num
      have h' : Tendsto (fun x : CubeI n => 2 * (x i : ℝ) - 1) (𝓝 q) (𝓝 (2 * (q i : ℝ) - 1)) :=
        hc
      rw [hval] at h'
      exact h'.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have hne : (x i : ℝ) ≠ 0 := fun h => hx ⟨i, Or.inl (Subtype.ext (by simpa using h))⟩
      have hgt : (0 : ℝ) < (x i : ℝ) := lt_of_le_of_ne (x i).2.1 (Ne.symm hne)
      show -1 < 2 * (x i : ℝ) - 1
      linarith
  simpa only [Function.comp_def] using (tendsto_div_sqrt_one_sub_sq_atBot.comp hφ)

/-! ## `cubeCoords` tends to infinity at the boundary -/

/-- Every compact set in `ℝⁿ` is eventually avoided by `cubeCoords` when approaching the
boundary of the cube. -/
theorem tendsto_cubeCoords_cocompact (n : ℕ) {q : CubeI n} (hq : q ∈ Cube.boundary (Fin n)) :
    Tendsto (cubeCoords n) (𝓝[(Cube.boundary (Fin n))ᶜ] q)
      (cocompact (EuclideanSpace ℝ (Fin n))) := by
  rw [← Metric.cobounded_eq_cocompact]
  rw [(Metric.hasBasis_cobounded_compl_closedBall (0 : EuclideanSpace ℝ (Fin n))).tendsto_right_iff]
  intro r _
  obtain ⟨i, hi⟩ : ∃ i, q i = 0 ∨ q i = 1 := hq
  have hqi : (q i : ℝ) = 0 ∨ (q i : ℝ) = 1 := by
    rcases hi with h | h
    · exact Or.inl (by simpa using congrArg Subtype.val h)
    · exact Or.inr (by simpa using congrArg Subtype.val h)
  rcases hqi with h0 | h1
  · have hc := tendsto_cubeCoord_atBot n i h0
    filter_upwards [hc.eventually (Filter.eventually_lt_atBot (- max r 0))] with x hx
    intro hmem
    have hbound : -max r 0 ≤ (cubeCoords n x) i := by
      have hb : -‖cubeCoords n x‖ ≤ (cubeCoords n x) i := neg_norm_le_cubeCoord n _ i
      have hb2 : ‖cubeCoords n x‖ = dist (cubeCoords n x) 0 := (dist_zero_right _).symm
      have hb3 : dist (cubeCoords n x) 0 ≤ r := hmem
      have hb4 : r ≤ max r 0 := le_max_left r 0
      linarith
    rw [show (cubeCoords n x) i =
        (2 * (x i : ℝ) - 1) / Real.sqrt (1 - (2 * (x i : ℝ) - 1)^2) from rfl] at hbound
    linarith
  · have hc := tendsto_cubeCoord_atTop n i h1
    filter_upwards [hc.eventually (Filter.eventually_gt_atTop (max r 0))] with x hx
    intro hmem
    have hbound : (cubeCoords n x) i ≤ max r 0 := by
      have hb : (cubeCoords n x) i ≤ ‖cubeCoords n x‖ := cubeCoord_le_norm n _ i
      have hb2 : ‖cubeCoords n x‖ = dist (cubeCoords n x) 0 := (dist_zero_right _).symm
      have hb3 : dist (cubeCoords n x) 0 ≤ r := hmem
      have hb4 : r ≤ max r 0 := le_max_left r 0
      linarith
    rw [show (cubeCoords n x) i =
        (2 * (x i : ℝ) - 1) / Real.sqrt (1 - (2 * (x i : ℝ) - 1)^2) from rfl] at hbound
    linarith

/-! ## The main result -/

theorem cubeToOnePoint_continuous (n : ℕ) : Continuous (cubeToOnePoint n) := by
  rw [continuous_iff_continuousAt]
  intro q
  by_cases hq : q ∈ Cube.boundary (Fin n)
  · have hfq : cubeToOnePoint n q = ∞ := by
      simp only [cubeToOnePoint]
      rw [if_pos hq]
    rw [ContinuousAt, hfq]
    refine tendsto_of_tendsto_ite (Cube.boundary (Fin n)) q (cubeCoords n) (cubeToOnePoint n)
      ?_ ?_ ?_
    · intro x hx
      simp only [cubeToOnePoint]; rw [if_pos hx]
    · intro x hx
      simp only [cubeToOnePoint]; rw [if_neg hx]
    · have hblow := tendsto_cubeCoords_cocompact n hq
      have h2 : Tendsto (cubeCoords n) (𝓝[(Cube.boundary (Fin n))ᶜ] q)
          (comap OnePoint.some (𝓝 (∞ : OnePoint (EuclideanSpace ℝ (Fin n))))) := by
        rwa [OnePoint.comap_coe_nhds_infty, Filter.coclosedCompact_eq_cocompact]
      simpa only [Function.comp_def] using (tendsto_comap_iff.mp h2)
  · have hc := continuousAt_cubeCoords_of_not_mem_boundary n hq
    have hcoe : ContinuousAt (fun x => (cubeCoords n x : OnePoint (EuclideanSpace ℝ (Fin n)))) q :=
      OnePoint.continuous_coe.continuousAt.comp hc
    refine hcoe.congr ?_
    filter_upwards [(isClosed_cubeBoundary n).isOpen_compl.mem_nhds hq] with x hx
    simp only [cubeToOnePoint]
    rw [if_neg hx]

end

end Work.Stems
