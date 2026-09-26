import Submission.Work.Smooth.JordanSeparation.offset_injective

/-!
# The offsets of an immersed curve are simple closed curves

The offset curves `θ ↦ c.γ θ + s · v θ` of an immersed `C¹` simple closed curve `c` along a
Lipschitz field `v` uniformly transverse to `c` are again injective on one period, for `s ≠ 0`
small enough: `innerCurve_isSimple`.  This is the step that lets one iterate the collar
construction of `SCHOENFLIES.md` — the inner boundary curve of the collar is itself a simple closed
curve, so the whole Jordan–Schoenflies problem can be transferred to it.

It is a direct corollary of `offset_injective` (the injectivity of the offset map on a strip modulo
the period): two parameters of the offset curve with the same image are the same parameter modulo
`2π`, and on `Ico 0 (2π)` that forces equality.
-/

open Work.Smooth.Jordan Work.Smooth.JordanSeparation

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- **The offset curve at height `s ≠ 0` is injective on one period.** -/
theorem innerCurve_isSimple (c : SmoothPlaneCurve)
    (himm : SmoothPlaneCurve.IsImmersion c) (hsimple : c.toPlaneCurve.IsSimple)
    {v : ℝ → ℂ} {κ L : ℝ} (hκ : 0 < κ) (hL : 0 < L)
    (hper : Function.Periodic v (2 * Real.pi))
    (htrans : IsTransverseUnitField c κ v) (hlip : IsLipschitzField L v) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, |s| < δ → s ≠ 0 →
      Set.InjOn (fun θ : ℝ => c.γ θ + (s : ℂ) * v θ) (Set.Ico 0 (2 * Real.pi)) := by
  obtain ⟨δ, hδpos, hinj⟩ := offset_injective c himm hsimple hκ hL hper htrans hlip
  refine ⟨δ, hδpos, fun s hs _ θ hθ θ' hθ' heq => ?_⟩
  have hoff : offset c v (θ, s) = offset c v (θ', s) := by
    simpa [offset] using heq
  obtain ⟨-, k, hk⟩ := hinj θ θ' s s hs hs hoff
  have hk' : θ' - θ = (k : ℝ) * (2 * Real.pi) := by linarith
  have h2 : |θ' - θ| < 2 * Real.pi := by
    rw [abs_lt]; constructor <;> linarith [hθ.1, hθ.2, hθ'.1, hθ'.2]
  have h4 : |((k : ℝ))| * (2 * Real.pi) < 2 * Real.pi := by
    have h4' : |((k : ℝ)) * (2 * Real.pi)| < 2 * Real.pi := by rw [← hk']; exact h2
    rwa [abs_mul, abs_of_pos two_pi_pos] at h4'
  have h5 : |((k : ℝ))| < 1 := by nlinarith [Real.pi_pos]
  have h6 : |k| < (1 : ℤ) := by exact_mod_cast h5
  have hk0 : k = 0 := Int.abs_lt_one_iff.mp h6
  rw [hk0, Int.cast_zero, zero_mul] at hk'
  linarith

end

end Work.Smooth.JordanSeparation
