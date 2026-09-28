import Mathlib

namespace Work.EMFG

open Set Metric

/-- The normalization `x ↦ ‖x‖⁻¹ • x` of a nonzero vector has norm one. -/
lemma norm_inv_smul_eq_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
    (hx : x ≠ 0) : ‖(‖x‖)⁻¹ • x‖ = 1 := by
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)

/-- A convex cone (closed under multiplication by positive scalars) which does not contain the
origin intersects the unit sphere in a contractible space.  Indeed the intersection is
"spherically convex": the straight segment between two of its points stays in the cone and misses
the origin, so it can be normalized to the sphere, and straight-line homotopy towards any fixed
point of the intersection followed by normalization contracts it. -/
theorem contractible_convexCone_sphere {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} (hconv : Convex ℝ C) (hcone : ∀ x ∈ C, ∀ r : ℝ, 0 < r → r • x ∈ C)
    (h0 : (0 : E) ∉ C) (hne : C.Nonempty) :
    ContractibleSpace ↥(C ∩ Metric.sphere (0 : E) 1) := by
  obtain ⟨p₀, hp₀⟩ := hne
  have hp₀_ne : p₀ ≠ 0 := fun h => h0 (h ▸ hp₀)
  have hp₀_pos : 0 < ‖p₀‖ := norm_pos_iff.mpr hp₀_ne
  set p : E := (‖p₀‖)⁻¹ • p₀ with hp_def
  have hpC : p ∈ C := hcone p₀ hp₀ (‖p₀‖)⁻¹ (inv_pos.mpr hp₀_pos)
  have hpn : ‖p‖ = 1 := by
    rw [hp_def, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hp₀_pos.le)]
    exact inv_mul_cancel₀ (ne_of_gt hp₀_pos)
  have hpS : p ∈ Metric.sphere (0 : E) 1 := by
    rw [Metric.mem_sphere, dist_zero_right]; exact hpn
  have hpY : p ∈ C ∩ Metric.sphere (0 : E) 1 := ⟨hpC, hpS⟩
  rw [contractible_iff_id_nullhomotopic]
  have hxn : ∀ x : ↥(C ∩ Metric.sphere (0 : E) 1), ‖(x : E)‖ = 1 := fun x => by
    have h := Metric.mem_sphere.mp x.property.2
    rwa [dist_zero_right] at h
  have hxc : ∀ x : ↥(C ∩ Metric.sphere (0 : E) 1), (x : E) ∈ C := fun x => x.property.1
  have hAc : Continuous (fun q : unitInterval × ↥(C ∩ Metric.sphere (0 : E) 1) =>
      (1 - (q.1 : ℝ)) • (q.2 : E) + (q.1 : ℝ) • p) := by
    fun_prop
  have hAmem : ∀ q : unitInterval × ↥(C ∩ Metric.sphere (0 : E) 1),
      (1 - (q.1 : ℝ)) • (q.2 : E) + (q.1 : ℝ) • p ∈ C := by
    intro q
    refine (convex_iff_add_mem.mp hconv) (hxc q.2) hpC ?_ ?_ ?_
    · exact sub_nonneg.mpr q.1.property.2
    · exact q.1.property.1
    · ring
  have hAne : ∀ q : unitInterval × ↥(C ∩ Metric.sphere (0 : E) 1),
      (1 - (q.1 : ℝ)) • (q.2 : E) + (q.1 : ℝ) • p ≠ 0 :=
    fun q hq => h0 (hq ▸ hAmem q)
  have hΨc : Continuous (fun q : unitInterval × ↥(C ∩ Metric.sphere (0 : E) 1) =>
      (‖(1 - (q.1 : ℝ)) • (q.2 : E) + (q.1 : ℝ) • p‖)⁻¹ •
        ((1 - (q.1 : ℝ)) • (q.2 : E) + (q.1 : ℝ) • p)) := by
    refine (hAc.norm.inv₀ ?_).smul hAc
    intro q
    exact norm_ne_zero_iff.mpr (hAne q)
  have hΨmem : ∀ q : unitInterval × ↥(C ∩ Metric.sphere (0 : E) 1),
      (‖(1 - (q.1 : ℝ)) • (q.2 : E) + (q.1 : ℝ) • p‖)⁻¹ •
        ((1 - (q.1 : ℝ)) • (q.2 : E) + (q.1 : ℝ) • p) ∈ C ∩ Metric.sphere (0 : E) 1 := by
    intro q
    have hz : (1 - (q.1 : ℝ)) • (q.2 : E) + (q.1 : ℝ) • p ≠ 0 := hAne q
    refine ⟨?_, ?_⟩
    · exact hcone _ (hAmem q) _ (inv_pos.mpr (norm_pos_iff.mpr hz))
    · rw [Metric.mem_sphere, dist_zero_right]
      exact norm_inv_smul_eq_one hz
  let Φ : C(unitInterval × ↥(C ∩ Metric.sphere (0 : E) 1),
      ↥(C ∩ Metric.sphere (0 : E) 1)) :=
    ⟨fun q => ⟨_, hΨmem q⟩, hΨc.subtype_mk hΨmem⟩
  refine ⟨⟨p, hpY⟩, ⟨ContinuousMap.Homotopy.mk Φ ?_ ?_⟩⟩
  · intro x
    apply Subtype.ext
    show (‖(1 - ((0 : unitInterval) : ℝ)) • (x : E) + ((0 : unitInterval) : ℝ) • p‖)⁻¹ •
      ((1 - ((0 : unitInterval) : ℝ)) • (x : E) + ((0 : unitInterval) : ℝ) • p) = (x : E)
    simp [hxn x]
  · intro x
    apply Subtype.ext
    show (‖(1 - ((1 : unitInterval) : ℝ)) • (x : E) + ((1 : unitInterval) : ℝ) • p‖)⁻¹ •
      ((1 - ((1 : unitInterval) : ℝ)) • (x : E) + ((1 : unitInterval) : ℝ) • p) = p
    simp [hpn]

end Work.EMFG
