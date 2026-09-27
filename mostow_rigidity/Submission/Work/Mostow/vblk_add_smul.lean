import Mathlib
import Submission.Work.Mostow.euclidBlockDefs

namespace Work.Mostow

/-- `vblk k hk R` is additive. -/
theorem vblk_add (k : ℕ) {n : ℕ} (hk : k ≤ n)
    (R : Submission.Mostow.E (n - k) ≃ₗᵢ[ℝ] Submission.Mostow.E (n - k))
    (u v : Submission.Mostow.E n) :
    vblk k hk R (u + v) = vblk k hk R u + vblk k hk R v := by
  apply WithLp.ofLp_injective
  funext i
  rw [WithLp.ofLp_add, Pi.add_apply]
  by_cases h : (i : ℕ) < k
  · rw [vblk_ofLp_of_lt k hk R (u + v) i h, vblk_ofLp_of_lt k hk R u i h,
      vblk_ofLp_of_lt k hk R v i h, WithLp.ofLp_add, Pi.add_apply]
  · rw [vblk_ofLp_of_ge k hk R (u + v) i h, vblk_ofLp_of_ge k hk R u i h,
      vblk_ofLp_of_ge k hk R v i h, tailOf_add, map_add, WithLp.ofLp_add, Pi.add_apply]

/-- `vblk k hk R` is `ℝ`-homogeneous. -/
theorem vblk_smul (k : ℕ) {n : ℕ} (hk : k ≤ n)
    (R : Submission.Mostow.E (n - k) ≃ₗᵢ[ℝ] Submission.Mostow.E (n - k))
    (c : ℝ) (u : Submission.Mostow.E n) :
    vblk k hk R (c • u) = c • vblk k hk R u := by
  apply WithLp.ofLp_injective
  funext i
  rw [WithLp.ofLp_smul, Pi.smul_apply]
  by_cases h : (i : ℕ) < k
  · rw [vblk_ofLp_of_lt k hk R (c • u) i h, vblk_ofLp_of_lt k hk R u i h,
      WithLp.ofLp_smul, Pi.smul_apply]
  · rw [vblk_ofLp_of_ge k hk R (c • u) i h, vblk_ofLp_of_ge k hk R u i h, tailOf_smul, map_smul,
      WithLp.ofLp_smul, Pi.smul_apply]

theorem vblk_add_smul (k : ℕ) {n : ℕ} (hk : k ≤ n)
    (R : Submission.Mostow.E (n - k) ≃ₗᵢ[ℝ] Submission.Mostow.E (n - k)) :
    (∀ u v : Submission.Mostow.E n, Work.Mostow.vblk k hk R (u + v)
        = Work.Mostow.vblk k hk R u + Work.Mostow.vblk k hk R v) ∧
      (∀ (c : ℝ) (u : Submission.Mostow.E n), Work.Mostow.vblk k hk R (c • u)
        = c • Work.Mostow.vblk k hk R u) :=
  ⟨fun u v => vblk_add k hk R u v, fun c u => vblk_smul k hk R c u⟩

end Work.Mostow
