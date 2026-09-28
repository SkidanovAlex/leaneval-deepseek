import Mathlib
import Submission.Work.RatHurewicz.SphereThomDefs

set_option synthInstance.maxHeartbeats 400000

namespace Work.RatHurewicz

open scoped unitInterval

/-- A nonempty convex cone `C` in `ℝ^{n+1}` not containing the origin meets the unit sphere in a
contractible set: the radial normalisation of the segment `(1-t)·x + t·x₀` is a nullhomotopy of the
identity, because the segment stays in `C` (convexity) and never hits the origin (`0 ∉ C`). -/
theorem coneSphereContractible (n : ℕ) (C : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hconv : Convex ℝ C) (hcone : ∀ x ∈ C, ∀ t : ℝ, 0 < t → t • x ∈ C)
    (h0 : (0 : EuclideanSpace ℝ (Fin (n + 1))) ∉ C)
    (hne : (C ∩ Metric.sphere 0 1).Nonempty) :
    ContractibleSpace ↥(C ∩ Metric.sphere 0 1) := by
  classical
  rw [contractible_iff_id_nullhomotopic]
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨hx₀C, hx₀S⟩ := hx₀
  have hx₀n : ‖x₀‖ = 1 := by
    rw [Metric.mem_sphere, dist_zero_right] at hx₀S; exact hx₀S
  refine ⟨⟨x₀, hx₀C, hx₀S⟩, ?_⟩
  -- the underlying straight-line map `(t,x) ↦ (1-t)·x + t·x₀`
  let φ : unitInterval × ↥(C ∩ Metric.sphere 0 1) → EuclideanSpace ℝ (Fin (n+1)) :=
    fun p => (1 - (p.1 : ℝ)) • (p.2 : EuclideanSpace ℝ (Fin (n+1))) + (p.1 : ℝ) • x₀
  have hφ_def : ∀ p, φ p
      = (1 - (p.1 : ℝ)) • (p.2 : EuclideanSpace ℝ (Fin (n+1))) + (p.1 : ℝ) • x₀ := fun p => rfl
  have hφ_cont : Continuous φ := by fun_prop
  have hφ_mem : ∀ p, φ p ∈ C := by
    intro p
    rw [hφ_def p]
    exact hconv p.2.2.1 hx₀C (by linarith [unitInterval.le_one p.1]) (unitInterval.nonneg p.1)
      (by ring)
  have hφ_ne : ∀ p, φ p ≠ 0 := by
    intro p hp
    exact h0 (hp ▸ hφ_mem p)
  have hφ_norm : ∀ p, ‖φ p‖⁻¹ • φ p ∈ Metric.sphere 0 1 := by
    intro p
    have hn : 0 < ‖φ p‖ := norm_pos_iff.mpr (hφ_ne p)
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg hn.le]
    exact inv_mul_cancel₀ hn.ne'
  have hmem : ∀ p, ‖φ p‖⁻¹ • φ p ∈ C ∩ Metric.sphere 0 1 := by
    intro p
    exact ⟨hcone (φ p) (hφ_mem p) ‖φ p‖⁻¹ (inv_pos.mpr (norm_pos_iff.mpr (hφ_ne p))),
      hφ_norm p⟩
  have hinner : Continuous (fun p : unitInterval × ↥(C ∩ Metric.sphere 0 1) =>
      ‖φ p‖⁻¹ • φ p) :=
    (hφ_cont.norm).inv₀ (fun p => (norm_pos_iff.mpr (hφ_ne p)).ne') |>.smul hφ_cont
  let F : C(unitInterval × ↥(C ∩ Metric.sphere 0 1), ↥(C ∩ Metric.sphere 0 1)) :=
    ⟨fun p => ⟨‖φ p‖⁻¹ • φ p, hmem p⟩, Continuous.subtype_mk hinner hmem⟩
  refine ⟨ContinuousMap.Homotopy.mk F ?_ ?_⟩
  · intro x
    apply Subtype.ext
    show ‖φ (0, x)‖⁻¹ • φ (0, x) = (x : EuclideanSpace ℝ (Fin (n+1)))
    have h0' : φ (0, x) = (x : EuclideanSpace ℝ (Fin (n+1))) := by
      rw [hφ_def]; simp
    rw [h0']
    have hxn : ‖(x : EuclideanSpace ℝ (Fin (n+1)))‖ = 1 := by
      have := x.2.2
      rw [Metric.mem_sphere, dist_zero_right] at this
      exact this
    rw [hxn, inv_one, one_smul]
  · intro x
    apply Subtype.ext
    show ‖φ (1, x)‖⁻¹ • φ (1, x) = x₀
    have h1' : φ (1, x) = x₀ := by
      rw [hφ_def]; simp
    rw [h1', hx₀n, inv_one, one_smul]

end Work.RatHurewicz
