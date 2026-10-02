import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology Filter

namespace Work.ELRig.DerivSign

theorem deriv_sign {f : ℝ → ℝ} {s₀ : ℝ} (hd : deriv f s₀ ≠ 0) :
    ∃ η > 0, ∀ s : ℝ, 0 < |s - s₀| → |s - s₀| < η →
      0 < (f s - f s₀) * (s - s₀) * deriv f s₀ := by
  -- `deriv f s₀ ≠ 0` forces differentiability at `s₀`.
  have hdiff : DifferentiableAt ℝ f s₀ := by
    by_contra h
    exact hd (deriv_zero_of_not_differentiableAt h)
  have hf : HasDerivAt f (deriv f s₀) s₀ := hdiff.hasDerivAt
  -- Little-o form of the derivative: the error is `o(s - s₀)`.
  have hlo := hf.isLittleO
  have hc : 0 < |deriv f s₀| / 2 := by positivity
  have hbound : ∀ᶠ x in 𝓝 s₀,
      |f x - f s₀ - (x - s₀) * deriv f s₀| ≤ |deriv f s₀| / 2 * |x - s₀| := by
    have hb := (Asymptotics.IsLittleO_def (𝓝 s₀)
        (fun x => f x - f s₀ - (x - s₀) • deriv f s₀) (fun x => x - s₀)).mp hlo hc
    rw [Asymptotics.isBigOWith_iff] at hb
    simpa [Real.norm_eq_abs, smul_eq_mul] using hb
  obtain ⟨η, hη, hηP⟩ := Metric.eventually_nhds_iff.mp hbound
  refine ⟨η, hη, fun s hs hs' => ?_⟩
  have hsp := hηP hs'
  set d := deriv f s₀
  set a := s - s₀
  have hdne : d ≠ 0 := hd
  have hane : a ≠ 0 := by
    intro h; rw [h, abs_zero] at hs; exact lt_irrefl 0 hs
  set e := f s - f s₀ - a * d
  have h1 : |e| ≤ |d| / 2 * |a| := by simpa [a, e, d] using hsp
  -- The error is strictly smaller than `|(s - s₀)·d|`, so it cannot change the sign.
  have h2 : |e| < |a * d| := by
    rw [abs_mul]
    have hd2 : 0 < |d| := abs_pos.mpr hdne
    have ha2 : 0 < |a| := abs_pos.mpr hane
    nlinarith [abs_nonneg e]
  have hkey : 0 < (a * d) * (a * d + e) := by
    have hy : a * d ≠ 0 := mul_ne_zero hane hdne
    rcases lt_or_gt_of_ne hy with hneg | hpos
    · rw [abs_of_neg hneg] at h2
      exact mul_pos_of_neg_of_neg hneg (by linarith [(abs_lt.mp h2).2])
    · rw [abs_of_pos hpos] at h2
      exact mul_pos hpos (by linarith [(abs_lt.mp h2).1])
  have hthis : (f s - f s₀) * (s - s₀) * deriv f s₀ = (a * d) * (a * d + e) := by
    simp only [a, d, e]
    ring
  rw [hthis]; exact hkey

end Work.ELRig.DerivSign
