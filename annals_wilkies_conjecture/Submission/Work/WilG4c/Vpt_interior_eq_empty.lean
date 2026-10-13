import Mathlib
import Submission.Work.WilG4c.BadRayDefs

set_option autoImplicit false
noncomputable section
open Classical
open scoped Topology

namespace Work.WilG4c

/-- The cone map `w ↦ u + w_last • (init w - u)`; `Vpt u T` is its preimage of `T`. -/
def coneMap {N : ℕ} (u : Fin N → ℝ) : (Fin (N + 1) → ℝ) → (Fin N → ℝ) :=
  fun w => u + w (Fin.last N) • (Fin.init w - u)

theorem mem_coneMap {N : ℕ} {u : Fin N → ℝ} {T : Set (Fin N → ℝ)} {w : Fin (N + 1) → ℝ} :
    coneMap u w ∈ T ↔ w ∈ Vpt u T := Iff.rfl

/-- The section of `coneMap u` at height `t`: the inverse of `coneMap u` on the slice
`w_last = t`, valid when `t ≠ 0`. -/
def coneSection {N : ℕ} (u : Fin N → ℝ) (t : ℝ) : (Fin N → ℝ) → (Fin (N + 1) → ℝ) :=
  fun z => Fin.snoc (u + t⁻¹ • (z - u)) t

theorem continuous_coneSection {N : ℕ} (u : Fin N → ℝ) (t : ℝ) :
    Continuous (coneSection u t) := by
  unfold coneSection
  fun_prop

theorem coneMap_coneSection {N : ℕ} (u : Fin N → ℝ) {t : ℝ} (ht : t ≠ 0) (z : Fin N → ℝ) :
    coneMap u (coneSection u t z) = z := by
  unfold coneSection coneMap
  simp only [Fin.init_snoc, Fin.snoc_last]
  rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ ht, one_smul, add_sub_cancel]

theorem coneSection_coneMap {N : ℕ} (u : Fin N → ℝ) {t : ℝ} (ht : t ≠ 0) (v : Fin N → ℝ) :
    coneSection u t (coneMap u (Fin.snoc v t)) = Fin.snoc v t := by
  unfold coneSection
  have h : coneMap u (Fin.snoc v t) - u = t • (v - u) := by
    simp only [coneMap, Fin.init_snoc, Fin.snoc_last, add_sub_cancel_left]
  rw [h, smul_smul, inv_mul_cancel₀ ht, one_smul, add_sub_cancel]

/-- The cone `Vpt u T` over a set `T` of empty interior again has empty interior. -/
theorem Vpt_interior_eq_empty {N : ℕ} (u : Fin N → ℝ) (T : Set (Fin N → ℝ))
    (hint : interior T = ∅) : interior (Work.WilG4c.Vpt u T) = ∅ := by
  rw [← Set.not_nonempty_iff_eq_empty]
  rintro ⟨w0, hw0⟩
  -- Step 1: move to a point of `interior (Vpt u T)` whose last coordinate is nonzero.
  have hstep1 : ∃ w1 ∈ interior (Vpt u T), w1 (Fin.last N) ≠ 0 := by
    by_cases h : w0 (Fin.last N) ≠ 0
    · exact ⟨w0, hw0, h⟩
    · have h0 : w0 (Fin.last N) = 0 := not_not.mp h
      have hcont : ContinuousAt
          (fun c : ℝ => (Fin.snoc (Fin.init w0) c : Fin (N + 1) → ℝ)) (w0 (Fin.last N)) := by
        fun_prop
      have hnhds : interior (Vpt u T) ∈
          𝓝 ((fun c : ℝ => (Fin.snoc (Fin.init w0) c : Fin (N + 1) → ℝ)) (w0 (Fin.last N))) := by
        simp only [Fin.snoc_init_self]
        exact isOpen_interior.mem_nhds hw0
      have hmem : (fun c : ℝ => (Fin.snoc (Fin.init w0) c : Fin (N + 1) → ℝ)) ⁻¹'
          (interior (Vpt u T)) ∈ 𝓝 (w0 (Fin.last N)) :=
        hcont.preimage_mem_nhds hnhds
      rw [h0, Metric.mem_nhds_iff] at hmem
      obtain ⟨ε, hε, hball⟩ := hmem
      have hmem_ball : (ε / 2 : ℝ) ∈ Metric.ball (0 : ℝ) ε := by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
        linarith
      refine ⟨Fin.snoc (Fin.init w0) (ε / 2), hball hmem_ball, ?_⟩
      rw [Fin.snoc_last]
      exact ne_of_gt (half_pos hε)
  obtain ⟨w1, hw1, ht1⟩ := hstep1
  -- Step 2: `coneMap u w1` lies in `interior T`.
  have hsec : coneSection u (w1 (Fin.last N)) (coneMap u w1) = w1 := by
    have h := coneSection_coneMap u (t := w1 (Fin.last N)) ht1 (Fin.init w1)
    rwa [Fin.snoc_init_self] at h
  have hpre : (coneSection u (w1 (Fin.last N))) ⁻¹' (interior (Vpt u T)) ∈ 𝓝 (coneMap u w1) := by
    have hc : ContinuousAt (coneSection u (w1 (Fin.last N))) (coneMap u w1) :=
      (continuous_coneSection u _).continuousAt
    have hmem : interior (Vpt u T) ∈ 𝓝 (coneSection u (w1 (Fin.last N)) (coneMap u w1)) := by
      rw [hsec]
      exact isOpen_interior.mem_nhds hw1
    exact hc.preimage_mem_nhds hmem
  have hsub : (coneSection u (w1 (Fin.last N))) ⁻¹' (interior (Vpt u T)) ⊆ T := by
    intro z hz
    have hzv : coneSection u (w1 (Fin.last N)) z ∈ Vpt u T := interior_subset hz
    have hzT : coneMap u (coneSection u (w1 (Fin.last N)) z) ∈ T := mem_coneMap.mpr hzv
    rwa [coneMap_coneSection u ht1 z] at hzT
  have hT : T ∈ 𝓝 (coneMap u w1) := Filter.mem_of_superset hpre hsub
  have hmem3 : coneMap u w1 ∈ interior T := mem_interior_iff_mem_nhds.mpr hT
  rw [hint] at hmem3
  exact hmem3

end Work.WilG4c
