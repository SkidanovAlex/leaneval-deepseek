import Mathlib
import Submission.Work.NumberTheory.Linnik.scratch_l71cond

namespace Work.LinnikAreas.DhRepel

/-- If `2γ < |v|`, where `γ = θ/(λ tan θ)` is the half-width of the support of Heath-Brown's `g`,
then `g * g` vanishes at `v`: for if `g s ≠ 0` and `g (v - s) ≠ 0` then `|s| < γ` and
`|v - s| < γ`, whence `|v| ≤ |s| + |v - s| < 2γ`, a contradiction. -/
theorem convCosF_supp {θ lam : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) {v : ℝ}
    (hv : 2 * (θ / (lam * Real.tan θ)) < |v|) :
    (∫ s : ℝ, Commons.NumberTheory.Linnik.extCosG θ lam s * Commons.NumberTheory.Linnik.extCosG θ lam (v - s)) = 0 := by
  have hzero : ∀ s : ℝ,
      Commons.NumberTheory.Linnik.extCosG θ lam s * Commons.NumberTheory.Linnik.extCosG θ lam (v - s) = 0 := by
    intro s
    by_contra h
    rw [mul_eq_zero] at h
    push_neg at h
    obtain ⟨h1, h2⟩ := h
    have h1' : ¬ (θ / (lam * Real.tan θ) ≤ |s|) :=
      fun hc => h1 (Commons.NumberTheory.Linnik.extCosG_supp hθ0 hθ1 hlam s hc)
    have h2' : ¬ (θ / (lam * Real.tan θ) ≤ |v - s|) :=
      fun hc => h2 (Commons.NumberTheory.Linnik.extCosG_supp hθ0 hθ1 hlam (v - s) hc)
    rw [not_le] at h1' h2'
    have htri : |v| ≤ |s| + |v - s| := by
      calc |v| = |s + (v - s)| := by ring_nf
        _ ≤ |s| + |v - s| := abs_add_le s (v - s)
    linarith
  simp [hzero]

end Work.LinnikAreas.DhRepel
