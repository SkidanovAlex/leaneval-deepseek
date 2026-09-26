import Mathlib
import Submission.Work.Drive.cInfKnot
import Submission.Work.Drive.uniformBoundsC1

set_option linter.unusedVariables false

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-!
# The three knot clauses for a *uniformly* small `C¹` correction

`Work.Drive.smallCorrection_clauses_cInf` shows that for a single `C^∞` knot `r` there is a
radius `ε > 0` such that every `period`-periodic `C¹` correction `w` which is smaller than `ε`
in `C⁰` and `C¹` again has the three structural knot clauses (periodicity, simplicity on one
period, nonvanishing velocity).

This file isolates the part of that argument that is *uniform in a parameter*: given any
`period`-periodic curve `r` together with

* a positive lower bound `m` for its speed,
* a parameter scale `δ` on which the chord is at least `(m/2)` times the parameter difference,
* a positive separation `σ` for parameters that differ by between `δ` and `period - δ`,

the three clauses hold for `r + w` for every `C¹` correction `w` with `‖w‖_∞ < ε` and
`‖w'‖_∞ < ε`, where `0 < ε ≤ min (m/4) (σ/4)`.  The constants `m, δ, σ` are supplied uniformly
by `Work.Drive.uniformBoundsC1` (the `C¹` version of `Work.Drive.uniformCurveBounds`).
-/

/-- The triangle-difference estimate: `(m/2 - ε)|s - u| ≤ ‖(r s + w s) - (r u + w u)‖` as soon
as the chord of `r` dominates `(m/2)|s - u|` and the chord of `w` is at most `ε|s - u|`. -/
private lemma norm_diff_sum_lower {r w : ℝ → Space} {m ε : ℝ}
    {s u : ℝ} (h1 : (m / 2) * |s - u| ≤ ‖r s - r u‖)
    (h2 : ‖w s - w u‖ ≤ ε * |s - u|) :
    (m / 2 - ε) * |s - u| ≤ ‖(r s + w s) - (r u + w u)‖ := by
  have htri : ‖r s - r u‖ - ‖w s - w u‖ ≤ ‖(r s + w s) - (r u + w u)‖ := by
    have h := norm_sub_le ((r s - r u) + (w s - w u)) (w s - w u)
    rw [add_sub_cancel_right] at h
    have he : (r s - r u) + (w s - w u) = (r s + w s) - (r u + w u) := by abel
    rw [he] at h
    linarith
  have hsub : (m / 2 - ε) * |s - u| ≤ ‖r s - r u‖ - ‖w s - w u‖ := by
    have hrw : (m / 2 - ε) * |s - u| = (m / 2) * |s - u| - ε * |s - u| := by ring
    rw [hrw]; linarith
  linarith

/-- **The three knot clauses from explicit uniform geometric bounds.**

Let `r` be a `period`-periodic differentiable curve whose speed is bounded below by `m > 0`,
whose chords on parameter windows of length `≤ δ` dominate `(m/2)` times the parameter
difference, and which separates parameters at distance between `δ` and `period - δ` by at
least `σ > 0`.  Then for every `C¹`, `period`-periodic correction `w` with `‖w‖ < ε` and
`‖w'‖ < ε`, where `0 < ε ≤ min (m/4) (σ/4)`, the sum `r + w` is again periodic, injective on
one period, and has nonvanishing velocity. -/
theorem correction_clauses_of_bounds {r : ℝ → Space}
    (hrdiff : Differentiable ℝ r) (hrper : Function.Periodic r period)
    {m δ σ ε : ℝ} (hm : 0 < m) (hσ : 0 < σ) (hε : 0 < ε)
    (hεm : ε ≤ m / 4) (hεσ : ε ≤ σ / 4)
    (hb1 : ∀ t : ℝ, m ≤ ‖velocity r t‖)
    (hb2 : ∀ t t' : ℝ, |t' - t| ≤ δ → (m / 2) * |t' - t| ≤ ‖r t - r t'‖)
    (hb3 : ∀ t t' : ℝ, δ ≤ |t' - t| → |t' - t| ≤ period - δ → σ ≤ ‖r t - r t'‖) :
    ∀ w : ℝ → Space, ContDiff ℝ 1 w → Function.Periodic w period →
      (∀ t : ℝ, ‖w t‖ < ε) → (∀ t : ℝ, ‖velocity w t‖ < ε) →
      Function.Periodic (fun t : ℝ => r t + w t) period ∧
        Set.InjOn (fun t : ℝ => r t + w t) (Set.Ico 0 period) ∧
          ∀ t : ℝ, velocity (fun t : ℝ => r t + w t) t ≠ 0 := by
  intro w hwsm hwper hwn hwv
  have hwdiff : Differentiable ℝ w := hwsm.differentiable (by decide)
  have hwlip : ∀ a b : ℝ, ‖w b - w a‖ ≤ ε * |b - a| := by
    intro a b
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := w) (s := Set.univ)
      (fun x _ => hwdiff x) (fun x _ => le_of_lt (hwv x)) convex_univ
      (Set.mem_univ a) (Set.mem_univ b)
    rwa [Real.norm_eq_abs] at h
  have hmm : 0 < m / 2 - ε := by linarith
  have hsσ : 0 < σ - 2 * ε := by linarith
  have key : ∀ s t : ℝ, s ∈ Set.Ico (0 : ℝ) period → t ∈ Set.Ico (0 : ℝ) period → t < s →
      (fun t : ℝ => r t + w t) s = (fun t : ℝ => r t + w t) t → False := by
    intro s t hs ht hts heq
    have heq' : r s + w s = r t + w t := heq
    have hhpos : 0 < s - t := sub_pos.mpr hts
    have hhper : s - t < period := by have h1 := hs.2; have h2 := ht.1; linarith
    by_cases hle : s - t ≤ δ
    · have habs : |s - t| ≤ δ := by rw [abs_of_pos hhpos]; exact hle
      have hloc : (m / 2) * |s - t| ≤ ‖r s - r t‖ := by
        have h := hb2 t s habs
        rwa [norm_sub_rev] at h
      have hcomb := norm_diff_sum_lower (u := t) hloc (hwlip t s)
      have hzero : ‖(r s + w s) - (r t + w t)‖ = 0 := by rw [heq', sub_self, norm_zero]
      have hpp : 0 < (m / 2 - ε) * |s - t| := mul_pos hmm (abs_pos.mpr (ne_of_gt hhpos))
      linarith
    · have hgt : δ < s - t := not_le.mp hle
      by_cases hle2 : s - t ≤ period - δ
      · have hd : σ ≤ ‖r s - r t‖ :=
          hb3 s t (by rw [abs_sub_comm, abs_of_pos hhpos]; exact hgt.le)
            (by rw [abs_sub_comm, abs_of_pos hhpos]; exact hle2)
        have hw' : ‖w s - w t‖ ≤ 2 * ε := by
          have h2 := norm_sub_le (w s) (w t)
          linarith [hwn s, hwn t]
        have htri : ‖r s - r t‖ - ‖w s - w t‖ ≤ ‖(r s + w s) - (r t + w t)‖ := by
          have h := norm_sub_le ((r s - r t) + (w s - w t)) (w s - w t)
          rw [add_sub_cancel_right] at h
          have he : (r s - r t) + (w s - w t) = (r s + w s) - (r t + w t) := by abel
          rw [he] at h
          linarith
        have hzero : ‖(r s + w s) - (r t + w t)‖ = 0 := by rw [heq', sub_self, norm_zero]
        linarith
      · have hgt2 : period - δ < s - t := not_le.mp hle2
        set t' : ℝ := t + period with ht'def
        have hrs : r t' = r t := hrper t
        have hws : w t' = w t := hwper t
        have hne : s - t' ≠ 0 := by
          intro hc
          rw [ht'def] at hc
          linarith
        have habs : |s - t'| ≤ δ := by
          have hneg : s - t' ≤ 0 := by rw [ht'def]; linarith
          rw [abs_of_nonpos hneg]
          rw [ht'def]
          linarith
        have hloc : (m / 2) * |s - t'| ≤ ‖r s - r t'‖ := by
          have h := hb2 t' s habs
          rwa [norm_sub_rev] at h
        have hcomb := norm_diff_sum_lower (u := t') hloc (hwlip t' s)
        rw [hrs, hws] at hcomb
        have hzero : ‖(r s + w s) - (r t + w t)‖ = 0 := by rw [heq', sub_self, norm_zero]
        have hpp : 0 < (m / 2 - ε) * |s - t'| :=
          mul_pos hmm (abs_pos.mpr hne)
        linarith
  refine ⟨?_, ?_, ?_⟩
  · exact hrper.add hwper
  · intro s hs t ht heq
    rcases lt_trichotomy t s with h | h | h
    · exact absurd heq (key s t hs ht h)
    · exact h.symm
    · exact absurd heq.symm (key t s ht hs h)
  · intro t
    have hsum : velocity (fun t : ℝ => r t + w t) t = velocity r t + velocity w t := by
      simp only [velocity]
      change deriv (r + w) t = deriv r t + deriv w t
      rw [deriv_add (hrdiff t) (hwdiff t)]
    rw [hsum]
    have h1 : ‖velocity r t‖ - ‖velocity w t‖ ≤ ‖velocity r t + velocity w t‖ := by
      have h := norm_sub_le (velocity r t + velocity w t) (velocity w t)
      rw [add_sub_cancel_right] at h
      linarith
    have : 0 < ‖velocity r t + velocity w t‖ := by
      linarith [hb1 t, hwv t, h1, hεm, hm]
    exact norm_pos_iff.mp this

/-- **Uniform correction clauses (the requested lemma).**

For a jointly `C¹` family `F` whose slices `F · s`, `s ∈ [0,1]`, are `C^∞` knots, there is a
single radius `ε > 0` such that *every* jointly `C¹`, `period`-periodic correction `W` whose
slices together with their velocities are bounded by `ε` on the slab `s ∈ [0,1]` again has, for
every slice `s ∈ [0,1]`, the three structural knot clauses: `F · s + W · s` is `period`-periodic,
injective on one period, and has nonvanishing velocity.

This is the uniform-in-`s` refinement of `Work.Drive.smallCorrection_clauses_cInf`: the
constants `m, δ, σ` of `Work.Drive.uniformBoundsC1` replace the compactness argument at a
single slice, and `Work.Drive.correction_clauses_of_bounds` converts them into the clauses with
`ε = min (m/4) (σ/4)`. -/
theorem uniformCorrection_clauses {F : ℝ → ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hF : ContDiff ℝ 1 (fun p : ℝ × ℝ => F p.1 p.2))
    (hper : ∀ s t : ℝ, F (t + LeanEval.KnotTheory.Quadrisecant.period) s = F t s)
    (hslice : ∀ s ∈ Set.Icc (0 : ℝ) 1, Work.Drive.IsCInfKnot (fun t : ℝ => F t s)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ W : ℝ → ℝ → LeanEval.KnotTheory.Quadrisecant.Space,
      ContDiff ℝ 1 (fun p : ℝ × ℝ => W p.1 p.2) →
      (∀ s t : ℝ, W (t + LeanEval.KnotTheory.Quadrisecant.period) s = W t s) →
      (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ‖W t s‖ < ε ∧
        ‖deriv (fun u : ℝ => W u s) t‖ < ε) →
      ∀ s ∈ Set.Icc (0 : ℝ) 1,
        Function.Periodic (fun t : ℝ => F t s + W t s)
            LeanEval.KnotTheory.Quadrisecant.period ∧
          Set.InjOn (fun t : ℝ => F t s + W t s)
            (Set.Ico 0 LeanEval.KnotTheory.Quadrisecant.period) ∧
            ∀ t : ℝ, LeanEval.KnotTheory.Quadrisecant.velocity
              (fun t : ℝ => F t s + W t s) t ≠ 0 := by
  obtain ⟨m, δ, σ, hm, _hδ, _hδ2, hσ, hb⟩ := uniformBoundsC1 hF hslice
  refine ⟨min (m / 4) (σ / 4), lt_min (by linarith) (by linarith), ?_⟩
  intro W hWsm hWper hWsmall s hs
  have hrper : Function.Periodic (fun t : ℝ => F t s)
      LeanEval.KnotTheory.Quadrisecant.period := fun t => hper s t
  have hrdiff : Differentiable ℝ (fun t : ℝ => F t s) :=
    (hslice s hs).1.differentiable (by decide)
  have hwsm : ContDiff ℝ 1 (fun t : ℝ => W t s) := by
    have h : ContDiff ℝ 1 (fun t : ℝ => (t, s)) := by fun_prop
    exact hWsm.comp h
  have hwper : Function.Periodic (fun t : ℝ => W t s)
      LeanEval.KnotTheory.Quadrisecant.period := fun t => hWper s t
  exact correction_clauses_of_bounds (r := fun t : ℝ => F t s) hrdiff hrper hm hσ
    (lt_min (by linarith) (by linarith)) (min_le_left _ _) (min_le_right _ _)
    (hb s hs).1 (hb s hs).2.1 (hb s hs).2.2 (fun t => W t s) hwsm hwper
    (fun t => (hWsmall s hs t).1)
    (fun t => by simpa only [velocity] using (hWsmall s hs t).2)

end Work.Drive
