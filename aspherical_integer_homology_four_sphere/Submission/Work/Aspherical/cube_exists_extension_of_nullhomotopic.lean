import Mathlib
import Submission.Work.Aspherical.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology unitInterval

namespace Work.Aspherical

noncomputable section

/-!
# The disc extension property for cubes

A continuous map on the boundary `∂I^n` of the cube `I^n` (`n ≥ 1`) that is
null-homotopic extends to the whole cube.

The cube `I^n` is the cone on its boundary with apex the centre `c`; if
`G : ∂I^n × I → Y` is a null-homotopy of `b` (`G(·,0) = b`, `G(·,1) = y₀`) then
the extension is `x ↦ G(t x, r x)`, where `r x` is the radial projection of `x`
to `∂I^n` and `t x = 1 - max_i |2 x_i - 1|` is the cone parameter (`t = 0` on
`∂I^n`, `t = 1` at `c`).  The radial projection is discontinuous at `c`, but
there `t = 1` and `G(·,1)` is constant; the tube lemma turns this into
continuity.
-/

/-- The "radial radius" of a point of the cube, `max_i |2 x_i - 1| ∈ [0,1]`.
It equals `0` at the centre and `1` exactly on the boundary. -/
def cubeRad {n : ℕ} [NeZero n] (x : Fin n → ↥(Set.Icc (0:ℝ) 1)) : ℝ :=
  (Finset.univ : Finset (Fin n)).sup' Finset.univ_nonempty (fun i => |2 * (x i : ℝ) - 1|)

/-- The centre of the cube. -/
def cubeCenter (n : ℕ) : Fin n → ↥(Set.Icc (0:ℝ) 1) := fun _ => ⟨1/2, by norm_num⟩

/-- The boundary of the cube `I^n` is compact (it is closed in the compact cube). -/
instance instCompactSpaceBoundary (n : ℕ) : CompactSpace ↥(Cube.boundary (Fin n)) :=
  (isCompact_iff_compactSpace).mp (isClosed_boundary n).isCompact

theorem cubeRad_nonneg {n : ℕ} [NeZero n] (x : Fin n → ↥(Set.Icc (0:ℝ) 1)) :
    0 ≤ cubeRad x := by
  unfold cubeRad
  obtain ⟨i⟩ := (inferInstance : Nonempty (Fin n))
  exact le_trans (abs_nonneg _)
    (Finset.le_sup' (fun i => |2 * (x i : ℝ) - 1|) (Finset.mem_univ i))

theorem cubeRad_le_one {n : ℕ} [NeZero n] (x : Fin n → ↥(Set.Icc (0:ℝ) 1)) :
    cubeRad x ≤ 1 := by
  unfold cubeRad
  apply Finset.sup'_le
  intro i _
  have h1 : (0:ℝ) ≤ (x i : ℝ) := (x i).2.1
  have h2 : (x i : ℝ) ≤ 1 := (x i).2.2
  rw [abs_le]; constructor <;> linarith

theorem cubeRad_coord_le {n : ℕ} [NeZero n] (x : Fin n → ↥(Set.Icc (0:ℝ) 1)) (i : Fin n) :
    |(x i : ℝ) - 1/2| ≤ cubeRad x / 2 := by
  have h : |2 * (x i : ℝ) - 1| ≤ cubeRad x :=
    Finset.le_sup' (fun i => |2 * (x i : ℝ) - 1|) (Finset.mem_univ i)
  have h2 : |2 * (x i : ℝ) - 1| = 2 * |(x i : ℝ) - 1/2| := by
    rw [show 2 * (x i : ℝ) - 1 = 2 * ((x i : ℝ) - 1/2) by ring]
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  rw [h2] at h
  linarith

theorem cubeRad_continuous {n : ℕ} [NeZero n] :
    Continuous (fun x : Fin n → ↥(Set.Icc (0:ℝ) 1) => cubeRad x) := by
  rw [continuous_iff_continuousAt]
  intro x
  unfold cubeRad
  apply Filter.Tendsto.finset_sup'_nhds_apply
  intro i _
  have h1 : ContinuousAt (fun y : Fin n → ↥(Set.Icc (0:ℝ) 1) => (y i : ℝ)) x :=
    (continuous_subtype_val.comp (continuous_apply i)).continuousAt
  have h2 : ContinuousAt (fun y : Fin n → ↥(Set.Icc (0:ℝ) 1) => 2 * (y i : ℝ) - 1) x :=
    (h1.const_mul 2).sub_const 1
  exact h2.abs

theorem cubeRad_eq_zero {n : ℕ} [NeZero n] (x : Fin n → ↥(Set.Icc (0:ℝ) 1)) :
    cubeRad x = 0 ↔ x = cubeCenter n := by
  constructor
  · intro h
    funext i
    apply Subtype.ext
    have hle : |2 * (x i : ℝ) - 1| ≤ cubeRad x :=
      Finset.le_sup' (fun i => |2 * (x i : ℝ) - 1|) (Finset.mem_univ i)
    rw [h] at hle
    have habs : |2 * (x i : ℝ) - 1| = 0 := le_antisymm hle (abs_nonneg _)
    have : 2 * (x i : ℝ) - 1 = 0 := abs_eq_zero.mp habs
    simp only [cubeCenter]
    linarith
  · rintro rfl
    apply le_antisymm
    · unfold cubeRad
      apply Finset.sup'_le
      intro i _
      simp only [cubeCenter]
      norm_num
    · exact cubeRad_nonneg _

theorem cubeRad_boundary {n : ℕ} [NeZero n] {u : Fin n → ↥(Set.Icc (0:ℝ) 1)}
    (hu : u ∈ Cube.boundary (Fin n)) : cubeRad u = 1 := by
  obtain ⟨i, hi | hi⟩ := hu
  · have h : |2 * (u i : ℝ) - 1| ≤ cubeRad u :=
      Finset.le_sup' (fun i => |2 * (u i : ℝ) - 1|) (Finset.mem_univ i)
    have hval : ((u i : ↥(Set.Icc (0:ℝ) 1)) : ℝ) = 0 := by rw [hi]; rfl
    rw [hval] at h; norm_num at h
    linarith [cubeRad_le_one u]
  · have h : |2 * (u i : ℝ) - 1| ≤ cubeRad u :=
      Finset.le_sup' (fun i => |2 * (u i : ℝ) - 1|) (Finset.mem_univ i)
    have hval : ((u i : ↥(Set.Icc (0:ℝ) 1)) : ℝ) = 1 := by rw [hi]; rfl
    rw [hval] at h; norm_num at h
    linarith [cubeRad_le_one u]

/-- A coordinate of the radial projection of `x` to the boundary. -/
def radCoord {n : ℕ} [NeZero n] (x : Fin n → ↥(Set.Icc (0:ℝ) 1)) (i : Fin n) : ℝ :=
  1/2 + ((x i : ℝ) - 1/2)/cubeRad x

theorem radCoord_mem_I {n : ℕ} [NeZero n] (x : Fin n → ↥(Set.Icc (0:ℝ) 1))
    (h : cubeRad x ≠ 0) (i : Fin n) : radCoord x i ∈ Set.Icc (0:ℝ) 1 := by
  have hM : 0 < cubeRad x := lt_of_le_of_ne (cubeRad_nonneg x) (Ne.symm h)
  have hc := cubeRad_coord_le x i
  have hdiv : |((x i : ℝ) - 1/2)/cubeRad x| ≤ 1/2 := by
    rw [abs_div, abs_of_pos hM, div_le_iff₀ hM]
    linarith
  have ht := abs_le.mp hdiv
  rw [Set.mem_Icc, radCoord]
  constructor <;> linarith [ht.1, ht.2]

/-- The radial projection of `x` to the boundary, as a map `Fin n → I`. -/
def radF {n : ℕ} [NeZero n] (x : Fin n → ↥(Set.Icc (0:ℝ) 1)) (h : cubeRad x ≠ 0) :
    Fin n → ↥(Set.Icc (0:ℝ) 1) :=
  fun i => ⟨radCoord x i, radCoord_mem_I x h i⟩

theorem radF_mem_boundary {n : ℕ} [NeZero n] (x : Fin n → ↥(Set.Icc (0:ℝ) 1))
    (h : cubeRad x ≠ 0) : radF x h ∈ Cube.boundary (Fin n) := by
  have hM : 0 < cubeRad x := lt_of_le_of_ne (cubeRad_nonneg x) (Ne.symm h)
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup'
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin n)).Nonempty)
    (fun i => |2 * (x i : ℝ) - 1|)
  have hj' : cubeRad x = |2 * (x j : ℝ) - 1| := hj
  refine ⟨j, ?_⟩
  have hkey : |2 * (radCoord x j) - 1| = 1 := by
    have heq : 2 * (radCoord x j) - 1 = (2 * (x j : ℝ) - 1)/cubeRad x := by
      simp only [radCoord]; ring
    rw [heq, abs_div, abs_of_pos hM, hj',
      div_self (ne_of_gt (by rw [← hj']; exact hM))]
  rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hkey with hh | hh
  · right
    exact Subtype.ext (by linarith : radCoord x j = 1)
  · left
    exact Subtype.ext (by linarith : radCoord x j = 0)

/-- The radial projection of a non-central point of the cube to its boundary. -/
def radPt {n : ℕ} [NeZero n] (x : Fin n → ↥(Set.Icc (0:ℝ) 1)) (h : cubeRad x ≠ 0) :
    ↥(Cube.boundary (Fin n)) :=
  ⟨radF x h, radF_mem_boundary x h⟩

/-- The radial projection on non-central points, as a map on the subtype. -/
def radPtS {n : ℕ} [NeZero n]
    (y : {x : Fin n → ↥(Set.Icc (0:ℝ) 1) // cubeRad x ≠ 0}) : ↥(Cube.boundary (Fin n)) :=
  radPt y.1 y.2

/-- The radial projection, extended by an arbitrary value at the centre. -/
def radPtAll {n : ℕ} [NeZero n] (x : Fin n → ↥(Set.Icc (0:ℝ) 1)) :
    ↥(Cube.boundary (Fin n)) :=
  if h : cubeRad x = 0 then ⟨Cube.zeroPoint n, Cube.zeroPoint_mem_boundary n⟩ else radPt x h

theorem radPtAll_of_ne {n : ℕ} [NeZero n] (x : Fin n → ↥(Set.Icc (0:ℝ) 1))
    (h : cubeRad x ≠ 0) : radPtAll x = radPt x h := dite_eq_right h

/-- The "cone parameter" on the cube: `0` on the boundary, `1` at the centre. -/
def cubeTime {n : ℕ} [NeZero n] (x : Fin n → ↥(Set.Icc (0:ℝ) 1)) : I :=
  ⟨1 - cubeRad x, by
    constructor
    · linarith [cubeRad_le_one x]
    · linarith [cubeRad_nonneg x]⟩

theorem cubeTime_continuous {n : ℕ} [NeZero n] :
    Continuous (fun x : Fin n → ↥(Set.Icc (0:ℝ) 1) => cubeTime x) := by
  apply Continuous.subtype_mk
  have h : Continuous (fun x : Fin n → ↥(Set.Icc (0:ℝ) 1) => (1:ℝ) - cubeRad x) :=
    continuous_const.sub cubeRad_continuous
  simpa only [Pi.sub_apply] using h

theorem cubeTime_center {n : ℕ} [NeZero n] : cubeTime (cubeCenter n) = 1 := by
  apply Subtype.ext
  show 1 - cubeRad (cubeCenter n) = ((1 : I) : ℝ)
  rw [(cubeRad_eq_zero (cubeCenter n)).mpr rfl]
  norm_num

theorem radPt_boundary_id {n : ℕ} [NeZero n] (u : Fin n → ↥(Set.Icc (0:ℝ) 1))
    (hu : u ∈ Cube.boundary (Fin n)) :
    radPt u (by rw [cubeRad_boundary hu]; norm_num) = ⟨u, hu⟩ := by
  apply Subtype.ext
  funext i
  apply Subtype.ext
  show radCoord u i = (u i : ℝ)
  rw [radCoord, cubeRad_boundary hu]
  ring

theorem radPtS_continuous {n : ℕ} [NeZero n] :
    Continuous (radPtS (n := n)) := by
  unfold radPtS radPt
  apply Continuous.subtype_mk
  unfold radF
  apply continuous_pi
  intro i
  apply Continuous.subtype_mk
  unfold radCoord
  have hbase : Continuous
      (fun y : {x : Fin n → ↥(Set.Icc (0:ℝ) 1) // cubeRad x ≠ 0} => (y.1 i : ℝ)) := by
    have h1 : Continuous
        (fun p : Fin n → ↥(Set.Icc (0:ℝ) 1) => (p i : ℝ)) :=
      continuous_subtype_val.comp (continuous_apply i)
    exact h1.comp continuous_subtype_val
  have hden : Continuous
      (fun y : {x : Fin n → ↥(Set.Icc (0:ℝ) 1) // cubeRad x ≠ 0} => cubeRad y.1) :=
    cubeRad_continuous.comp continuous_subtype_val
  have hcn : Continuous
      (fun _ : {x : Fin n → ↥(Set.Icc (0:ℝ) 1) // cubeRad x ≠ 0} => (1/2 : ℝ)) :=
    continuous_const
  exact ((hbase.sub hcn).div hden (fun y => y.2)).const_add (1/2)

/-- Continuity of `x ↦ G (t x, r x)` where `t → 1` along a filter and `G(·,1)` is constant,
using the tube lemma. -/
theorem tendsto_comp_eq_of_tendsto_fst {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {Y : Type*} [TopologicalSpace Y] {G : C(I × K, Y)} {y0 : Y} (hG : ∀ k, G (1, k) = y0)
    {α : Type*} [TopologicalSpace α] {f : α → K} {g : α → I} {x : α}
    (hg : Filter.Tendsto g (𝓝 x) (𝓝 1)) :
    Filter.Tendsto (fun a => G (g a, f a)) (𝓝 x) (𝓝 y0) := by
  intro V hV
  rcases mem_nhds_iff.mp hV with ⟨O, hOV, hO, hy0O⟩
  have hn : IsOpen (G ⁻¹' O) := hO.preimage G.continuous
  have hsub : ({1} : Set I) ×ˢ (Set.univ : Set K) ⊆ G ⁻¹' O := by
    rintro ⟨t, k⟩ ⟨ht, -⟩
    simp only [Set.mem_singleton_iff] at ht
    subst ht
    show G (1, k) ∈ O
    rw [hG k]
    exact hy0O
  obtain ⟨u, v, hu, hv, h1u, htv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_univ hn hsub
  have hgu : g ⁻¹' u ∈ 𝓝 x := hg (hu.mem_nhds (h1u (Set.mem_singleton 1)))
  refine Filter.mem_map.mpr (Filter.mem_of_superset hgu ?_)
  intro a ha
  exact hOV (huv ⟨ha, htv (Set.mem_univ _)⟩)

/-- The disc extension property for cubes: a continuous map on the boundary `∂I^n` of the cube
`I^n` (`n ≥ 1`) that is null-homotopic extends to the whole cube. -/
theorem cube_exists_extension_of_nullhomotopic {n : ℕ} [NeZero n] {Y : Type*} [TopologicalSpace Y]
    (b : C(↥(Cube.boundary (Fin n)), Y)) (hb : ContinuousMap.Nullhomotopic b) :
    ∃ H : C(Fin n → ↥(Set.Icc (0:ℝ) 1), Y),
      ∀ u : ↥(Cube.boundary (Fin n)), H u = b u := by
  obtain ⟨y0, ⟨G⟩⟩ := hb
  refine ⟨⟨fun x => G (cubeTime x, radPtAll x), ?_⟩, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : cubeRad x = 0
    · have hxc : x = cubeCenter n := (cubeRad_eq_zero x).mp hx
      subst hxc
      have hval : G (cubeTime (cubeCenter n), radPtAll (cubeCenter n)) = y0 := by
        rw [cubeTime_center]; exact G.map_one_left _
      have htend : Filter.Tendsto (fun a => G (cubeTime a, radPtAll a)) (𝓝 (cubeCenter n))
          (𝓝 (G (cubeTime (cubeCenter n), radPtAll (cubeCenter n)))) := by
        rw [hval]
        exact tendsto_comp_eq_of_tendsto_fst (G := G.toContinuousMap) (y0 := y0)
          (fun k => G.map_one_left k) (f := radPtAll) (g := fun a => cubeTime a)
          (by simpa only [ContinuousAt, cubeTime_center] using
            cubeTime_continuous.continuousAt (x := cubeCenter n))
      exact htend
    · have hrad : ContinuousAt (fun a : Fin n → ↥(Set.Icc (0:ℝ) 1) => radPtAll a) x := by
        have hrestrict : Continuous
            ({a : Fin n → ↥(Set.Icc (0:ℝ) 1) | cubeRad a ≠ 0}.domRestrict
              (fun a => radPtAll a)) := by
          have heq : ({a : Fin n → ↥(Set.Icc (0:ℝ) 1) | cubeRad a ≠ 0}.domRestrict
              (fun a => radPtAll a)) = radPtS := by
            funext y
            show radPtAll y.1 = radPtS y
            rw [radPtAll_of_ne y.1 y.2]
            rfl
          rw [heq]; exact radPtS_continuous
        have hon : ContinuousOn (fun a : Fin n → ↥(Set.Icc (0:ℝ) 1) => radPtAll a)
            {a | cubeRad a ≠ 0} :=
          continuousOn_iff_continuous_domRestrict.mpr hrestrict
        have hopen : IsOpen {a : Fin n → ↥(Set.Icc (0:ℝ) 1) | cubeRad a ≠ 0} :=
          (isOpen_ne (x := (0:ℝ))).preimage cubeRad_continuous
        exact hon.continuousAt (hopen.mem_nhds hx)
      have hpair : ContinuousAt (fun a : Fin n → ↥(Set.Icc (0:ℝ) 1) =>
          (cubeTime a, radPtAll a)) x := by
        rw [ContinuousAt, nhds_prod_eq]
        exact (show Filter.Tendsto (fun a : Fin n → ↥(Set.Icc (0:ℝ) 1) => cubeTime a)
            (𝓝 x) (𝓝 (cubeTime x)) from cubeTime_continuous.continuousAt).prodMk hrad
      exact G.continuous.continuousAt.comp hpair
  · intro u
    show G (cubeTime (u : Fin n → ↥(Set.Icc (0:ℝ) 1)),
        radPtAll (u : Fin n → ↥(Set.Icc (0:ℝ) 1))) = b u
    have ht : cubeTime (u : Fin n → ↥(Set.Icc (0:ℝ) 1)) = 0 := by
      apply Subtype.ext
      show 1 - cubeRad (u : Fin n → ↥(Set.Icc (0:ℝ) 1)) = ((0 : I) : ℝ)
      rw [cubeRad_boundary u.2]
      norm_num
    have hr : radPtAll (u : Fin n → ↥(Set.Icc (0:ℝ) 1)) = u := by
      rw [radPtAll_of_ne _ (by rw [cubeRad_boundary u.2]; norm_num)]
      exact radPt_boundary_id (u : Fin n → ↥(Set.Icc (0:ℝ) 1)) u.2
    rw [ht, hr]
    exact G.map_zero_left u

end

end Work.Aspherical
