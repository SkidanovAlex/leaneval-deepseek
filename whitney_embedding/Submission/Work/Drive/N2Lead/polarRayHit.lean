import Mathlib
import Submission.Work.Drive.N2Lead.twistDefs

/-!
# The `hhit` row of the saddle window's certificates, for the polar (bridge) picture

`Work.Drive.N2Lead.isCertifiedAt_of_starRegions` asks, for each region `Ω k` with centre `o k`, for a
direction `e k ≠ 0` such that the ray `{o k + s • e k : s > 0}` meets the level's picture at most
once.  For the two regions `Ω_R` (centre `1`) and `Ω_L` (centre `-1`) of the upper certificate
(`NOTES_LEAD_saddlePacket.md` §4.3) the *bridge* part of the level is drawn by the polar curve
`t ↦ r (Θ t) · exp (i Θ t)`, and the ray `(1, ∞)` (direction `e = 1`) is met exactly when the angle
is in `2πℤ`.  This file proves that this happens at most once per period of the parametrisation:

* `polarRay_angle`: a point of the polar curve on the ray `(1, ∞)` has its angle in `2πℤ`
  (from `‖exp (i θ)‖ = 1` and `Complex.exp_eq_one_iff`);
* `thetaAddInt`: the integer-shift form of the periodicity `Θ (t + 1) = Θ t + 2π`;
* `polarRay_hit_unique`: two parameters of the polar picture on that ray differ by an integer —
  which, together with the `modOne` row of `Work.Drive.N2C.LevelCurves`, shows that the ray meets the
  level's picture at most once.

The companion row (the model and remnant parts of the upper level never meet those rays) is
`Work.Drive.N2Lead.modelArc_not_mem_ray` in `N2Lead/modelArcRayFree.lean`.
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology

/-- The integer-shift form of the periodicity `Θ (t+1) = Θ t + 2π`. -/
lemma thetaAddInt {Θ : ℝ → ℝ} (hΘper : ∀ t : ℝ, Θ (t + 1) = Θ t + 2 * Real.pi)
    (x : ℝ) (k : ℤ) : Θ (x + k) = Θ x + 2 * Real.pi * k := by
  have hnat : ∀ (n : ℕ) (y : ℝ), Θ (y + n) = Θ y + 2 * Real.pi * n := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ m ih =>
      intro y
      have h1 : y + (m + 1 : ℕ) = (y + m) + 1 := by push_cast; ring
      rw [h1, hΘper, ih]
      push_cast; ring
  obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg k
  · subst hn; simpa using hnat n x
  · subst hn
    have h1 := hnat n (x + -(n : ℤ))
    have h2 : x + -(n : ℤ) + (n : ℝ) = x := by push_cast; ring
    rw [h2] at h1
    have h3 : Θ x = Θ (x + -(n : ℤ)) + 2 * Real.pi * n := h1
    rw [h3]; push_cast; ring

/-- **A point of the polar curve on the ray `(1, ∞)` has its angle in `2πℤ`.** -/
lemma polarRay_angle {r Θ : ℝ → ℝ} {t σ : ℝ} (hσ : 0 < σ) (hrpos : ∀ φ : ℝ, 0 < r φ)
    (h : (r (Θ t) : ℂ) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I) = ((1 + σ : ℝ) : ℂ)) :
    ∃ m : ℤ, Θ t = 2 * Real.pi * m := by
  have hr : ((r (Θ t) : ℝ) : ℂ) ≠ 0 := by simpa using ne_of_gt (hrpos (Θ t))
  have hexp : Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I)
      = ((1 + σ : ℝ) : ℂ) / ((r (Θ t) : ℝ) : ℂ) := by
    rw [eq_div_iff hr, mul_comm]; exact h
  have hnorm : ‖Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]; simp
  have hsqrt : ∀ z : ℂ, Real.sqrt (Complex.normSq z) = ‖z‖ := fun z => by
    rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg z)]
  have ha : (1 + σ) / r (Θ t) = 1 := by
    have h1 := congrArg norm hexp
    have h2 : ‖(((1 + σ : ℝ)) : ℂ)‖ = |1 + σ| := by
      rw [← hsqrt, Complex.normSq_ofReal, ← pow_two, Real.sqrt_sq_eq_abs]
    have h3 : ‖(((r (Θ t) : ℝ)) : ℂ)‖ = |r (Θ t)| := by
      rw [← hsqrt, Complex.normSq_ofReal, ← pow_two, Real.sqrt_sq_eq_abs]
    rw [hnorm, Complex.norm_div, h2, h3, abs_of_pos (by linarith : (0:ℝ) < 1 + σ),
      abs_of_pos (hrpos (Θ t))] at h1
    exact h1.symm
  have hexp1 : Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [hexp, ← Complex.ofReal_div, ha, Complex.ofReal_one]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp1
  refine ⟨n, ?_⟩
  have h2 := congrArg Complex.im hn
  simp at h2
  linarith [h2]

/-- **`hhit` for the polar curve: the ray `(1, ∞)` meets the bridge picture at most once per period.**
If two parameters of the `1`-periodic polar picture lie on that ray, they differ by an integer. -/
theorem polarRay_hit_unique {r Θ : ℝ → ℝ} (hrpos : ∀ φ : ℝ, 0 < r φ)
    (hΘmono : StrictMono Θ) (hΘper : ∀ t : ℝ, Θ (t + 1) = Θ t + 2 * Real.pi)
    {t t' σ σ' : ℝ} (hσ : 0 < σ) (hσ' : 0 < σ')
    (ht : (r (Θ t) : ℂ) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I) = ((1 + σ : ℝ) : ℂ))
    (ht' : (r (Θ t') : ℂ) * Complex.exp (((Θ t' : ℝ) : ℂ) * Complex.I) = ((1 + σ' : ℝ) : ℂ)) :
    ∃ k : ℤ, t = t' + k := by
  obtain ⟨m, hm⟩ := polarRay_angle hσ hrpos ht
  obtain ⟨m', hm'⟩ := polarRay_angle hσ' hrpos ht'
  have hcoe : (((m - m' : ℤ)) : ℝ) = (m : ℝ) - (m' : ℝ) := by push_cast; ring
  refine ⟨m - m', ?_⟩
  have hkey : t = t' + ((m : ℝ) - (m' : ℝ)) := by
    have hdiff : Θ (t' + ((m : ℝ) - (m' : ℝ))) = Θ t := by
      have hper' : Θ (t' + ((m : ℝ) - (m' : ℝ)))
          = Θ t' + 2 * Real.pi * ((m : ℝ) - (m' : ℝ)) := by
        have hh := thetaAddInt hΘper t' (m - m')
        rwa [hcoe] at hh
      rw [hper', hm, hm']
      ring
    exact (hΘmono.injective hdiff).symm
  rw [hkey, hcoe]

end Work.Drive.N2Lead
