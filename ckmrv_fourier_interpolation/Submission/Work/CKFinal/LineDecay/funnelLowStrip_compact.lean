import Mathlib

namespace Work.CKFinal.LineDecay

open Set UpperHalfPlane

/-- The closed horizontal strip `{|Re τ| ≤ 1, 2 ≤ Im τ ≤ H}` in the upper half plane is
compact.  It is the image, under the continuous embedding `ℍ → ℂ`, of the intersection of
`ℂ`'s preimage of the compact box `[-1,1] × [2,H]` with the upper half plane. -/
theorem funnelLowStrip_compact {H : ℝ} :
    IsCompact {τ : UpperHalfPlane | |τ.re| ≤ 1 ∧ 2 ≤ τ.im ∧ τ.im ≤ H} := by
  rw [isEmbedding_coe.isCompact_iff]
  have hset : ((↑) : UpperHalfPlane → ℂ) ''
        {τ : UpperHalfPlane | |τ.re| ≤ 1 ∧ 2 ≤ τ.im ∧ τ.im ≤ H}
      = {z : ℂ | |z.re| ≤ 1 ∧ 2 ≤ z.im ∧ z.im ≤ H} := by
    ext z
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      exact hτ
    · intro hz
      exact ⟨⟨z, by linarith [hz.2.1]⟩, hz, rfl⟩
  rw [hset]
  have himg : {z : ℂ | |z.re| ≤ 1 ∧ 2 ≤ z.im ∧ z.im ≤ H}
      = (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ''
          (Icc (-1) 1 ×ˢ Icc 2 H) := by
    ext z
    constructor
    · intro hz
      refine ⟨(z.re, z.im), ⟨abs_le.mp hz.1, hz.2⟩, ?_⟩
      apply Complex.ext <;> simp
    · rintro ⟨p, hp, rfl⟩
      show |((p.1 : ℂ) + (p.2 : ℂ) * Complex.I).re| ≤ 1 ∧
        2 ≤ ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I).im ∧
        ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I).im ≤ H
      rw [show ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I).re = p.1 by simp,
        show ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I).im = p.2 by simp, abs_le]
      exact ⟨⟨hp.1.1, hp.1.2⟩, hp.2.1, hp.2.2⟩
  rw [himg]
  exact (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)

end Work.CKFinal.LineDecay
