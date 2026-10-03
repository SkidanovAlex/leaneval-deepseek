import Mathlib

namespace Work.HornSeq

open Set Metric Filter
open scoped Topology

/-- The unit disc as a subset of `ℂ` is open. -/
lemma isOpen_unitDisc_ball : IsOpen (Metric.ball (0 : ℂ) 1) := Metric.isOpen_ball

theorem exists_homeomorph_unitDisc_of_injOn_analytic {B : Set ℂ} {φ : ℂ → ℂ}
    (hBopen : IsOpen B)
    (hφmaps : ∀ z ∈ B, ‖φ z‖ < 1)
    (hφsurj : ∀ w : ℂ, ‖w‖ < 1 → ∃ z ∈ B, φ z = w)
    (hφana : ∀ z ∈ B, AnalyticAt ℂ φ z)
    (hφinj : Set.InjOn φ B) :
    ∃ H : ↥B ≃ₜ ↥(Metric.ball (0 : ℂ) 1), ∀ z : ↥B, (H z : ℂ) = φ z := by
  have hmem : ∀ w : ℂ, w ∈ Metric.ball (0 : ℂ) 1 ↔ ‖w‖ < 1 := by
    intro w; rw [Metric.mem_ball, dist_eq_norm, sub_zero]
  have hball : ∀ z ∈ B, φ z ∈ Metric.ball (0 : ℂ) 1 := fun z hz => (hmem _).mpr (hφmaps z hz)
  have hball_open : IsOpen (Metric.ball (0 : ℂ) 1) := Metric.isOpen_ball
  have hcontOn : ContinuousOn φ B := fun z hz => (hφana z hz).continuousAt.continuousWithinAt
  -- ## `φ` is an open map on `B`
  have hlocOpen : ∀ S : Set ↥B, IsOpen S → IsOpen (φ '' (Subtype.val '' S)) := by
    intro S hS
    have hSopen : IsOpen (Subtype.val '' S) :=
      (hBopen.isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen).mp hS
    rw [isOpen_iff_mem_nhds]
    rintro w ⟨z, hz, rfl⟩
    rcases hz with ⟨y, hyS, rfl⟩
    have hana : AnalyticAt ℂ φ (y : ℂ) := hφana y y.2
    rcases hana.eventually_constant_or_nhds_le_map_nhds with hconst | hmap
    · -- impossible: `φ` would be locally constant, contradicting injectivity
      exfalso
      have hnhds : B ∩ {z' : ℂ | φ z' = φ (y : ℂ)} ∈ 𝓝 (y : ℂ) :=
        Filter.inter_mem (hBopen.mem_nhds y.2) hconst
      obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp hnhds
      set r : ℝ := ε / 2 with hr
      have hrpos : 0 < r := by rw [hr]; linarith
      set z' : ℂ := (y : ℂ) + ((r : ℝ) : ℂ) with hz'
      have hdiff : z' - (y : ℂ) = ((r : ℝ) : ℂ) := by rw [hz']; ring
      have hz'mem : z' ∈ B ∩ {z' : ℂ | φ z' = φ (y : ℂ)} := by
        apply hε
        rw [Metric.mem_ball, dist_eq_norm, hdiff, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hrpos, hr]
        linarith
      have hz'ne : z' ≠ (y : ℂ) := by
        intro h
        have h1 : z' - (y : ℂ) = 0 := by rw [h, sub_self]
        rw [hdiff] at h1
        exact (Complex.ofReal_ne_zero.mpr (ne_of_gt hrpos)) h1
      exact hz'ne (hφinj hz'mem.1 y.2 hz'mem.2)
    · -- openness: `φ '' (val '' S)` is a neighbourhood of `φ y`
      have hT : Subtype.val '' S ∈ 𝓝 (y : ℂ) := hSopen.mem_nhds ⟨y, hyS, rfl⟩
      have hpre : φ ⁻¹' (φ '' (Subtype.val '' S)) ∈ 𝓝 (y : ℂ) :=
        Filter.mem_of_superset hT (fun x hx => ⟨x, hx, rfl⟩)
      exact hmap (Filter.mem_map.mpr hpre)
  -- ## the bijection `↥B ≃ ↥(unit disc)`
  let e : ↥B ≃ ↥(Metric.ball (0 : ℂ) 1) :=
    { toFun := fun z => ⟨φ (z : ℂ), hball z z.2⟩
      invFun := fun w => ⟨(hφsurj (w : ℂ) ((hmem w).mp w.2)).choose,
        (hφsurj (w : ℂ) ((hmem w).mp w.2)).choose_spec.1⟩
      left_inv := by
        intro z
        apply Subtype.ext
        exact hφinj (hφsurj (φ (z : ℂ)) ((hmem _).mp (hball z z.2))).choose_spec.1 z.2
          (hφsurj (φ (z : ℂ)) ((hmem _).mp (hball z z.2))).choose_spec.2
      right_inv := by
        intro w
        apply Subtype.ext
        exact (hφsurj (w : ℂ) ((hmem w).mp w.2)).choose_spec.2 }
  -- ## `e` is continuous
  have hcont_e : Continuous (e : ↥B → ↥(Metric.ball (0 : ℂ) 1)) := by
    change Continuous (fun z : ↥B => (⟨φ (z : ℂ), hball z z.2⟩ : ↥(Metric.ball (0 : ℂ) 1)))
    exact hcontOn.domRestrict.subtype_mk (fun z => hball z z.2)
  -- ## `e` is an open map
  have hIsOpenMap_e : IsOpenMap (e : ↥B → ↥(Metric.ball (0 : ℂ) 1)) := by
    intro S hS
    have h_eq : Subtype.val '' (e '' S) = φ '' (Subtype.val '' S) := by
      ext a
      constructor
      · rintro ⟨y, ⟨z, hzS, rfl⟩, rfl⟩
        exact ⟨(z : ℂ), ⟨z, hzS, rfl⟩, rfl⟩
      · rintro ⟨a, ⟨z, hzS, rfl⟩, rfl⟩
        exact ⟨e z, ⟨z, hzS, rfl⟩, rfl⟩
    rw [hball_open.isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen, h_eq]
    exact hlocOpen S hS
  refine ⟨e.toHomeomorphOfContinuousOpen hcont_e hIsOpenMap_e, ?_⟩
  intro z
  rw [Equiv.toHomeomorphOfContinuousOpen_apply]
  rfl

end Work.HornSeq
