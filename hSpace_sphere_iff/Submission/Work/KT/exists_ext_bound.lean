import Mathlib

namespace Work.KT

/-- Tietze extension with a pointwise bound: a continuous complex-valued function on a closed
subset `s` of a compact Hausdorff space extends to the whole space with the same pointwise bound. -/
theorem exists_ext_bound {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (s : Set X) (hs : IsClosed s) (c : ℝ) (hc : 0 ≤ c) (F : C(s, ℂ)) (hF : ∀ x, ‖F x‖ ≤ c) :
    ∃ G : C(X, ℂ), (∀ x, ‖G x‖ ≤ c) ∧ ∀ x : s, G x = F x := by
  -- A compact Hausdorff space is normal, so Tietze extension applies.
  obtain rfl | hcpos := eq_or_lt_of_le hc
  · -- If `c = 0`, the bound forces `F` to vanish identically and we take the zero extension.
    refine ⟨0, fun x => by simp, fun x => ?_⟩
    have hx : F x = 0 := norm_le_zero_iff.mp (hF x)
    simp [hx]
  · -- Otherwise the closed ball of radius `c > 0` in `ℂ` satisfies the Tietze extension property.
    have : TietzeExtension (Metric.closedBall (0 : ℂ) c) :=
      Metric.instTietzeExtensionClosedBall ℂ 0 hcpos
    have hFt : ∀ x : s, F x ∈ Metric.closedBall (0 : ℂ) c := by
      intro x
      simpa [Metric.mem_closedBall, dist_zero_right] using hF x
    obtain ⟨g, hgmem, hgrest⟩ := ContinuousMap.exists_forall_mem_restrict_eq hs F hFt
    refine ⟨g, ?_, ?_⟩
    · intro x
      simpa [Metric.mem_closedBall, dist_zero_right] using hgmem x
    · intro x
      exact DFunLike.congr_fun hgrest x

end Work.KT
