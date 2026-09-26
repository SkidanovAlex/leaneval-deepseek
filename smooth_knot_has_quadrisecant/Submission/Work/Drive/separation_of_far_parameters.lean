import Mathlib
import Submission.Work.Drive.Prelude
import Submission.Work.Drive.uniformBoundsC1
import Submission.Work.Drive.cInfKnot
import Submission.KnotMap

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-!
# Separation of far parameters

For a smooth knot `r` there is a `C¹`-radius `ε > 0` such that every knot `r'` that is
`ε`-close to `r` in `C⁰` *and* in `C¹` is still uniformly separated at parameter scale `η`:
whenever two parameters `a b` of the knot circle are at distance at least `η`, the images
`r' a`, `r' b` are at distance at least some `δ = δ(η) > 0`.

The mathematics is entirely elementary.  For the *reference* knot `r`,

* its speed is bounded below by some `m > 0` (compactness of the period, regularity);
* nearby parameters satisfy a chord estimate `(m/2) |t - t'| ≤ ‖r t - r t'‖` for
  `|t - t'| ≤ δ₀` (mean value theorem, uniform continuity of the velocity);
* far parameters satisfy `σ ≤ ‖r t - r t'‖` for `δ₀ ≤ |t - t'| ≤ period - δ₀`
  (compactness of the period together with injectivity).

The first two are exactly the content of `Work.Drive.uniformBoundsC1` applied to the
constant family `(t, s) ↦ r t`.  Given these, the perturbation estimate
`‖r' t - r' s‖ ≥ ‖r t - r s‖ - ε |t - s|` (the mean value theorem applied to `r' - r`,
whose velocity is `< ε` by hypothesis) finishes the proof.

We prove the two estimates with real parameters and transport them to the parameter
circle `AddCircle period` using representatives chosen at the exact circle distance.
-/

/-! ### Representatives on the parameter circle -/

/-- `knotMap r` agrees with `r` on *every* real representative of a point of the
parameter circle, not only on the fundamental half-open period. -/
lemma knotMap_eq_of_periodic {r : ℝ → Space} (hper : Function.Periodic r period) (t : ℝ) :
    knotMap r (t : AddCircle period) = r t := by
  obtain ⟨y, hy, hyt⟩ := AddCircle.eq_coe_Ico (t : AddCircle period)
  have h1 : knotMap r (y : AddCircle period) = r y := AddCircle.liftIco_zero_coe_apply hy
  have h2 : r y = r t := by
    have hzero : ((y - t : ℝ) : AddCircle period) = 0 := by
      rw [AddCircle.coe_sub, hyt, sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff period).mp hzero
    have h' : (n : ℝ) * period = y - t := by simpa [zsmul_eq_mul] using hn
    have hyn : y = t + (n : ℝ) * period := by linarith
    rw [hyn]
    exact hper.int_mul n t
  rw [← hyt, h1, h2]

/-- Any two points of the parameter circle have real representatives at distance exactly
their circle distance. -/
lemma exists_representatives_dist (a b : AddCircle period) :
    ∃ t s : ℝ, (t : AddCircle period) = a ∧ (s : AddCircle period) = b ∧
      |t - s| = dist a b := by
  obtain ⟨s₀, -, hs₀⟩ := AddCircle.eq_coe_Ico b
  obtain ⟨x, -, hx⟩ := AddCircle.eq_coe_Ico (a - b)
  refine ⟨s₀ + (x - (round (period⁻¹ * x) : ℝ) * period), s₀, ?_, hs₀, ?_⟩
  · have hks : (((round (period⁻¹ * x) : ℝ) * period : ℝ) : AddCircle period) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]
      exact ⟨round (period⁻¹ * x), by simp⟩
    rw [AddCircle.coe_add, AddCircle.coe_sub, hks, hx, hs₀]
    abel
  · simp only [add_sub_cancel_left]
    rw [dist_eq_norm, ← hx, AddCircle.norm_eq]

/-! ### Calculus helpers -/

/-- The velocity of a difference of curves. -/
lemma velocity_sub_curve {f g : ℝ → Space} {t : ℝ} (hf : DifferentiableAt ℝ f t)
    (hg : DifferentiableAt ℝ g t) :
    velocity (fun u : ℝ => f u - g u) t = velocity f t - velocity g t := by
  have h : (fun u : ℝ => f u - g u) = f - g := rfl
  unfold velocity
  rw [h, deriv_sub hf hg]

/-- Mean-value bound: an analytic curve whose speed is at most `b` moves at most `b` per unit
time. -/
lemma norm_sub_le_of_velocity_bound {z : ℝ → Space} (hz : ContDiff ℝ ⊤ z) {b : ℝ}
    (hb : ∀ t : ℝ, ‖velocity z t‖ ≤ b) : ∀ s t : ℝ, ‖z t - z s‖ ≤ b * |t - s| := by
  intro s t
  have hzdiff : Differentiable ℝ z := hz.differentiable (by decide)
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := z) (s := Set.univ) (C := b)
    (fun x _ => hzdiff x) (fun x _ => hb x) convex_univ (Set.mem_univ s) (Set.mem_univ t)
  simpa [norm_sub_rev, abs_sub_comm] using h

/-! ### The main statement -/

theorem separation_of_far_parameters {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ r' : ℝ → LeanEval.KnotTheory.Quadrisecant.Space,
        LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r' →
        (∀ t : ℝ, ‖r' t - r t‖ < ε ∧
          ‖LeanEval.KnotTheory.Quadrisecant.velocity r' t -
            LeanEval.KnotTheory.Quadrisecant.velocity r t‖ < ε) →
        ∀ a b : AddCircle LeanEval.KnotTheory.Quadrisecant.period,
          η ≤ dist a b → δ ≤ ‖LeanEval.KnotTheory.Quadrisecant.knotMap r' a -
            LeanEval.KnotTheory.Quadrisecant.knotMap r' b‖ := by
  have hp : 0 < period := period_pos
  -- geometric bounds for the reference knot, from the constant family `(t, s) ↦ r t`
  obtain ⟨m, δ₀, σ, hm, hδ₀pos, hδ₀half, hσ, hb⟩ :=
    uniformBoundsC1 (F := fun t (_s : ℝ) => r t)
      ((hr.smooth.comp contDiff_fst).of_le le_top)
      (fun s _ => isCInfKnot_of_isSmoothKnot hr)
  have hvel : ∀ t : ℝ, m ≤ ‖velocity r t‖ := fun t => (hb 0 ⟨le_rfl, zero_le_one⟩).1 t
  have hnear : ∀ t t' : ℝ, |t' - t| ≤ δ₀ → (m / 2) * |t' - t| ≤ ‖r t - r t'‖ :=
    fun t t' h => (hb 0 ⟨le_rfl, zero_le_one⟩).2.1 t t' h
  have hfar : ∀ t t' : ℝ, δ₀ ≤ |t' - t| → |t' - t| ≤ period - δ₀ →
      σ ≤ ‖r t - r t'‖ :=
    fun t t' h1 h2 => (hb 0 ⟨le_rfl, zero_le_one⟩).2.2 t t' h1 h2
  -- the perturbation radius
  set ε : ℝ := min (m / 4) (σ / period) with hεdef
  have hεm : ε ≤ m / 4 := by rw [hεdef]; exact min_le_left _ _
  have hεσ : ε ≤ σ / period := by rw [hεdef]; exact min_le_right _ _
  have hεpos : 0 < ε := by
    rw [hεdef]; exact lt_min (by linarith) (div_pos hσ hp)
  have hmε : 0 < m / 2 - ε := by linarith
  have hσε : 0 < σ - ε * (period / 2) := by
    have h1 : ε * (period / 2) ≤ (σ / period) * (period / 2) :=
      mul_le_mul_of_nonneg_right hεσ (by linarith)
    have h2 : (σ / period) * (period / 2) = σ / 2 := by
      field_simp
    linarith
  refine ⟨ε, hεpos, ?_⟩
  intro η hη
  set D : ℝ := min ((m / 2 - ε) * η) (σ - ε * (period / 2)) with hDdef
  have hDpos : 0 < D := by
    rw [hDdef]; exact lt_min (mul_pos hmε hη) hσε
  have hD1 : D ≤ (m / 2 - ε) * η := by rw [hDdef]; exact min_le_left _ _
  have hD2 : D ≤ σ - ε * (period / 2) := by rw [hDdef]; exact min_le_right _ _
  refine ⟨D, hDpos, ?_⟩
  intro r' hr' hclose a b hab
  -- representatives at exact circle distance
  obtain ⟨t, s, ht, hs, hts⟩ := exists_representatives_dist a b
  have hka : knotMap r' a = r' t := by rw [← ht]; exact knotMap_eq_of_periodic hr'.periodic t
  have hkb : knotMap r' b = r' s := by rw [← hs]; exact knotMap_eq_of_periodic hr'.periodic s
  have hΔη : η ≤ |t - s| := by rw [hts]; exact hab
  have hΔle : |t - s| ≤ period / 2 := by
    rw [hts, dist_eq_norm]
    have h := AddCircle.norm_le_half_period period (x := a - b) period_ne_zero
    rwa [abs_of_pos hp] at h
  -- the perturbation estimate
  have hvelz : ∀ u : ℝ, ‖velocity (fun u : ℝ => r' u - r u) u‖ ≤ ε := by
    intro u
    rw [velocity_sub_curve ((hr'.smooth.differentiable (by decide)) u)
      ((hr.smooth.differentiable (by decide)) u)]
    exact le_of_lt (hclose u).2
  have hmvt : ‖(r' t - r t) - (r' s - r s)‖ ≤ ε * |t - s| :=
    norm_sub_le_of_velocity_bound (hr'.smooth.sub hr.smooth) hvelz s t
  have hkey : ‖r t - r s‖ - ε * |t - s| ≤ ‖r' t - r' s‖ := by
    have hsplit : r' t - r' s = (r t - r s) + ((r' t - r t) - (r' s - r s)) := by abel
    have hstep : ‖r t - r s‖ - ‖(r' t - r t) - (r' s - r s)‖ ≤
        ‖(r t - r s) + ((r' t - r t) - (r' s - r s))‖ := by
      have h := norm_sub_le ((r t - r s) + ((r' t - r t) - (r' s - r s)))
        ((r' t - r t) - (r' s - r s))
      rw [add_sub_cancel_right] at h
      linarith
    calc ‖r t - r s‖ - ε * |t - s|
        ≤ ‖(r t - r s) + ((r' t - r t) - (r' s - r s))‖ := by linarith [hstep, hmvt]
      _ = ‖r' t - r' s‖ := by rw [← hsplit]
  by_cases hlocal : |t - s| ≤ δ₀
  · -- nearby parameters: the reference knot moves at least at speed `m/2`
    have hloc : (m / 2) * |t - s| ≤ ‖r t - r s‖ := by
      have := hnear t s (by rwa [abs_sub_comm])
      simpa [abs_sub_comm] using this
    calc D ≤ (m / 2 - ε) * η := hD1
      _ ≤ (m / 2 - ε) * |t - s| := mul_le_mul_of_nonneg_left hΔη (le_of_lt hmε)
      _ = (m / 2) * |t - s| - ε * |t - s| := by ring
      _ ≤ ‖r t - r s‖ - ε * |t - s| := by linarith
      _ ≤ ‖r' t - r' s‖ := hkey
      _ = ‖knotMap r' a - knotMap r' b‖ := by rw [← hka, ← hkb]
  · -- far parameters: the reference knot is separated by `σ`
    have hδ₀le : δ₀ ≤ |t - s| := le_of_not_ge hlocal
    have hfar' : σ ≤ ‖r t - r s‖ := by
      refine hfar t s (by rwa [abs_sub_comm]) ?_
      rw [abs_sub_comm]
      linarith [hΔle, hδ₀half]
    calc D ≤ σ - ε * (period / 2) := hD2
      _ ≤ σ - ε * |t - s| := by
            have h1 : ε * |t - s| ≤ ε * (period / 2) :=
              mul_le_mul_of_nonneg_left hΔle (le_of_lt hεpos)
            linarith
      _ ≤ ‖r t - r s‖ - ε * |t - s| := by linarith
      _ ≤ ‖r' t - r' s‖ := hkey
      _ = ‖knotMap r' a - knotMap r' b‖ := by rw [← hka, ← hkb]

end Work.Drive
