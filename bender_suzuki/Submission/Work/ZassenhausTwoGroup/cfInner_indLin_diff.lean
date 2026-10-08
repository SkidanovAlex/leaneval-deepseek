import Mathlib
import Submission.Work.ZassenhausTwoGroup.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausTwoGroup

theorem cfInner_indLin_diff {H : Type} [Group H] [Fintype H] {G : Type} [Group G] [Fintype G]
    {S : Finset (H → ℂ)} {τ : (H → ℂ) →ₗ[ℤ] (G → ℂ)}
    (hiso : Work.Coherence.IsometryOn S τ) (horth : Work.Coherence.Orthonormal S)
    {χ χ₀ : H → ℂ} (hχ : χ ∈ S) (hχ₀ : χ₀ ∈ S) (hne : χ ≠ χ₀) {a : ℤ}
    (hdeg : χ 1 = (a : ℂ) * χ₀ 1) :
    Work.Coherence.cfInner (τ (χ - (a : ℂ) • χ₀)) (τ (χ - (a : ℂ) • χ₀))
      = 1 + (a : ℂ) ^ 2 := by
  -- `χ - a • χ₀` has degree `χ 1 - a * χ₀ 1 = 0`, so it lies in the degree-zero lattice
  -- `ℤ[S]^0`, where `τ` is an isometry.
  have hmem : χ - (a : ℂ) • χ₀ ∈ Work.Coherence.ZSpan0 S := by
    rw [Work.Coherence.mem_zSpan0]
    constructor
    · have h1 : χ ∈ Work.Coherence.ZSpan S := Work.Coherence.self_mem_zSpan hχ
      have h2 : χ₀ ∈ Work.Coherence.ZSpan S := Work.Coherence.self_mem_zSpan hχ₀
      have h3 : (a : ℂ) • χ₀ = a • χ₀ := Int.cast_smul_eq_zsmul ℂ a χ₀
      rw [h3]
      exact AddSubgroup.sub_mem _ h1 (AddSubgroup.zsmul_mem _ h2 a)
    · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hdeg]
      ring
  -- The isometry preserves the inner product of this element.
  have hinner := hiso.inner_eq (χ - (a : ℂ) • χ₀) hmem (χ - (a : ℂ) • χ₀) hmem
  rw [hinner]
  -- Orthonormality of `S` computes the inner product with `χ`, `χ₀`.
  have hχχ : Work.Coherence.cfInner χ χ = 1 := by simpa using horth χ hχ χ hχ
  have hχ₀χ₀ : Work.Coherence.cfInner χ₀ χ₀ = 1 := by simpa using horth χ₀ hχ₀ χ₀ hχ₀
  have hχχ₀ : Work.Coherence.cfInner χ χ₀ = 0 := by simpa [hne] using horth χ hχ χ₀ hχ₀
  have hχ₀χ : Work.Coherence.cfInner χ₀ χ = 0 := by
    simpa [Ne.symm hne] using horth χ₀ hχ₀ χ hχ
  rw [Work.Coherence.cfInner_sub_right, Work.Coherence.cfInner_sub_left,
      Work.Coherence.cfInner_sub_left]
  rw [Work.Coherence.cfInner_smul_left, Work.Coherence.cfInner_smul_right,
      Work.Coherence.cfInner_smul_left, Work.Coherence.cfInner_smul_right]
  rw [hχχ, hχ₀χ₀, hχχ₀, hχ₀χ]
  have hstar : (starRingEnd ℂ) (a : ℂ) = (a : ℂ) := by simp
  rw [hstar]
  ring

end Work.ZassenhausTwoGroup
