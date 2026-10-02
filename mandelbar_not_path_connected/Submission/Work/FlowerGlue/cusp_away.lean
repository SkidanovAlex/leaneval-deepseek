import Mathlib
import Submission.Work.FlowerGlue.cyl_prelim

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FlowerGlue

open Complex Filter Function
open scoped Real Topology

noncomputable section

/-- **C1 with the base point pinned to `T 0`** (variant of `cyl_omit`): if `T` is entire, injective
and `1`-equivariant, then at the upper end of the cylinder `T` omits a whole `ℤ`-tube around `T 0`.
The delivered `cyl_omit` returns the centre as an existential (its proof uses `T 0` internally); the
present statement exposes that centre, which is what the cusp estimate needs. -/
theorem cyl_omit_at_T0 {T : ℂ → ℂ} (hT : Differentiable ℂ T) (hinj : Function.Injective T)
    (hper : ∀ ζ : ℂ, T (ζ + 1) = T ζ + 1) :
    ∃ ε > 0, ∀ ζ : ℂ, 1 < ζ.im → ∀ n : ℤ, ε ≤ ‖T ζ - T 0 - (n : ℂ)‖ := by
  have hnc : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), T z = T 0 := by
    intro h
    obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp h
    have hmem : ((r / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) r := by
      rw [Metric.mem_ball, dist_zero_right]
      have : ‖((r / 2 : ℝ) : ℂ)‖ = r / 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < r / 2)]
      rw [this]; linarith
    have hne : ((r / 2 : ℝ) : ℂ) ≠ 0 := by
      simp only [ofReal_ne_zero]
      linarith
    exact hne (hinj (hsub hmem))
  have hopen : 𝓝 (T 0) ≤ Filter.map T (𝓝 0) := by
    rcases (hT.analyticAt 0).eventually_constant_or_nhds_le_map_nhds with h' | h'
    · exact absurd h' hnc
    · exact h'
  have hTimg : T '' Metric.ball (0 : ℂ) (1 / 2) ∈ 𝓝 (T 0) := by
    apply hopen
    rw [Filter.mem_map]
    exact Filter.mem_of_superset (Metric.ball_mem_nhds (0 : ℂ) (by norm_num))
      (fun z hz => ⟨z, hz, rfl⟩)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hTimg
  refine ⟨ε, hε, ?_⟩
  intro ζ hζ n
  by_contra hcon
  rw [not_le] at hcon
  have hperZ : ∀ (w : ℂ) (m : ℤ), T (w + (m : ℂ)) = T w + (m : ℂ) := by
    intro w m
    have hp : Function.Periodic (fun w => T w - w) 1 := by
      intro w
      show T (w + 1) - (w + 1) = T w - w
      rw [hper w]
      ring
    have hthis := hp.int_mul m w
    rw [mul_one] at hthis
    calc T (w + (m : ℂ)) = (T (w + (m : ℂ)) - (w + (m : ℂ))) + (w + (m : ℂ)) := by ring
      _ = (T w - w) + (w + (m : ℂ)) := by rw [hthis]
      _ = T w + (m : ℂ) := by ring
  have hmem2 : T ζ - (n : ℂ) ∈ T '' Metric.ball (0 : ℂ) (1 / 2) := by
    apply hεsub
    rw [Metric.mem_ball, dist_eq_norm]
    rw [show T ζ - (n : ℂ) - T 0 = T ζ - T 0 - (n : ℂ) from by ring]
    exact hcon
  obtain ⟨v, hv, hveq⟩ := hmem2
  have hζv : ζ = v + (n : ℂ) := by
    apply hinj
    rw [hperZ v n, hveq]
    ring
  have hvlt : ‖v‖ < 1 / 2 := by
    rw [Metric.mem_ball, dist_zero_right] at hv
    exact hv
  have him : ζ.im = v.im := by
    rw [hζv, Complex.add_im, ← Complex.ofReal_intCast n, Complex.ofReal_im, add_zero]
  have hvim : v.im ≤ ‖v‖ := Complex.im_le_norm v
  linarith

/-- **The cusp function of `e ∘ T` is bounded away from `e (T 0)` near `q = 0`.**

This is step (b) of the proof of `cyl_end_bdd` (see `NOTES_LEAD_mandelbar_gaps2.md` §1.1): for
`‖q‖ < exp (-2π)` the point `invQParam 1 q` has imaginary part `> 1`, so `T` applied to it avoids
the `ε`-tube around `T 0` (`cyl_omit_at_T0`), and the exponential separates the `ℤ`-tubes
(`exp_sep`) — hence a uniform positive lower bound on `‖cuspFunction 1 (e ∘ T) q - e (T 0)‖`. -/
theorem cusp_away {T : ℂ → ℂ} (hT : Differentiable ℂ T) (hinj : Function.Injective T)
    (hper : ∀ ζ : ℂ, T (ζ + 1) = T ζ + 1) :
    ∃ δ > 0, ∃ ρ > 0, ∀ q : ℂ, q ≠ 0 → ‖q‖ < ρ →
      δ ≤ ‖Function.Periodic.cuspFunction 1 (fun ζ => e (T ζ)) q - e (T 0)‖ := by
  obtain ⟨ε, hεpos, hε⟩ := cyl_omit_at_T0 hT hinj hper
  obtain ⟨δ, hδpos, hδ⟩ := exp_sep (T 0) hεpos
  refine ⟨δ, hδpos, Real.exp (-2 * Real.pi), Real.exp_pos _, ?_⟩
  intro q hq hqρ
  rw [Function.Periodic.cuspFunction_eq_of_nonzero (1 : ℝ) (fun ζ => e (T ζ)) hq]
  -- the preimage of `q` under `qParam 1` lies in the upper half-plane `{im > 1}`
  have him : 1 < (Function.Periodic.invQParam 1 q).im := by
    rw [Function.Periodic.im_invQParam]
    have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
    have hlog : Real.log ‖q‖ < -2 * Real.pi := by
      have h := (Real.log_lt_log_iff (norm_pos_iff.mpr hq)
        (Real.exp_pos (-2 * Real.pi))).mpr hqρ
      rwa [Real.log_exp] at h
    have h2 : 2 * Real.pi < -(Real.log ‖q‖) := by linarith
    have heq : -1 / (2 * Real.pi) * Real.log ‖q‖ = -(Real.log ‖q‖) / (2 * Real.pi) := by ring
    rw [heq, lt_div_iff₀ h2pi, one_mul]
    exact h2
  exact hδ (T (Function.Periodic.invQParam 1 q))
    (fun n => hε (Function.Periodic.invQParam 1 q) him n)

end

end Work.FlowerGlue
