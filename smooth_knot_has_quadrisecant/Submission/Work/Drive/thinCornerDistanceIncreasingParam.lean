import Mathlib
import Submission.Work.Drive.thinCorner_distance_increasing
import Submission.Work.Drive.thinLocalRadial

namespace Work.Drive

set_option maxHeartbeats 4000000

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-!
## The backward local-gap estimate

The mirror of `Work.Drive.thinCorner_local_gap`: the chord of parameter length `ρ` taken *backwards*
from `a` is bounded above by the chord of length `τ ≥ 2 ρ` taken from `b`, provided `a` and `b` are
within `δ` of each other and `ρ, τ ≤ δ`.
-/
lemma thinCorner_local_gap_bwd {r : ℝ → Space} (hrd : Differentiable ℝ r)
    {m C δ : ℝ} (hm : 0 < m) (hC : 0 ≤ C) (hδC : C * δ ≤ m / 8)
    (hspeed : ∀ t : ℝ, m ≤ ‖deriv r t‖)
    (hlip : ∀ t t' : ℝ, ‖deriv r t - deriv r t'‖ ≤ C * |t' - t|)
    {a b ρ τ : ℝ} (hab : |a - b| ≤ δ) (hρ : 0 < ρ) (hρδ : ρ ≤ δ) (hτρ : 2 * ρ ≤ τ)
    (hτδ : τ ≤ δ) :
    ‖r (a - ρ) - r a‖ + ρ * (m - 5 * (C * δ)) ≤ ‖r (b + τ) - r b‖ := by
  have hτ0 : 0 < τ := by linarith
  obtain ⟨-, -, hlow⟩ := thinCorner_shift_sub_le hrd hC hlip (b := b) (σ := τ) hτ0.le
  obtain ⟨-, hub, -⟩ := thinCorner_shift_sub_le hrd hC hlip (b := a - ρ) (σ := ρ) hρ.le
  -- upper bound for the backward chord
  have hub' : ‖r (a - ρ) - r a‖ ≤ ρ * (‖deriv r (a - ρ)‖ + C * ρ) := by
    have h1 : (a - ρ) + ρ = a := by ring
    rw [h1] at hub
    rw [norm_sub_rev] at hub
    exact hub
  -- the speed at `a - ρ` is controlled by the speed at `b`
  have hv_bound : ‖deriv r (a - ρ)‖ ≤ ‖deriv r b‖ + 2 * (C * δ) := by
    have h1 : ‖deriv r (a - ρ) - deriv r b‖ ≤ C * |a - ρ - b| := by
      have h := hlip (a - ρ) b
      rw [abs_sub_comm b (a - ρ)] at h
      exact h
    have h2 : |a - ρ - b| ≤ 2 * δ := by
      have h3 : a - ρ - b = (a - b) - ρ := by ring
      rw [h3]
      have h4 : |(a - b) - ρ| ≤ |a - b| + |ρ| := by
        have h := abs_sub_le (a - b) 0 ρ
        simpa using h
      rw [abs_of_pos hρ] at h4
      linarith [hab, hρδ]
    have h5 : C * |a - ρ - b| ≤ C * (2 * δ) := mul_le_mul_of_nonneg_left h2 hC
    have h6 : ‖deriv r (a - ρ)‖ ≤ ‖deriv r b‖ + ‖deriv r (a - ρ) - deriv r b‖ := by
      have h := norm_add_le (deriv r b) (deriv r (a - ρ) - deriv r b)
      have he : deriv r b + (deriv r (a - ρ) - deriv r b) = deriv r (a - ρ) := by abel
      rw [he] at h
      exact h
    linarith
  have hupper : ‖r (a - ρ) - r a‖ ≤ ρ * (‖deriv r b‖ + 3 * (C * δ)) := by
    calc ‖r (a - ρ) - r a‖ ≤ ρ * (‖deriv r (a - ρ)‖ + C * ρ) := hub'
      _ ≤ ρ * (‖deriv r b‖ + 2 * (C * δ) + C * ρ) := by
          apply mul_le_mul_of_nonneg_left _ hρ.le
          linarith [hv_bound]
      _ ≤ ρ * (‖deriv r b‖ + 3 * (C * δ)) := by
          apply mul_le_mul_of_nonneg_left _ hρ.le
          have h : C * ρ ≤ C * δ := mul_le_mul_of_nonneg_left hρδ hC
          linarith
  have hlower : 2 * ρ * (‖deriv r b‖ - C * δ) ≤ ‖r (b + τ) - r b‖ := by
    have h3 : ‖deriv r b‖ - C * δ ≤ ‖deriv r b‖ - C * τ := by
      have h := mul_le_mul_of_nonneg_left hτδ hC
      linarith
    have h4 : 0 ≤ ‖deriv r b‖ - C * δ := by
      have h := hspeed b
      linarith
    have h2 := mul_le_mul hτρ h3 h4 (by linarith [hρ.le])
    linarith
  have hkey : ρ * (‖deriv r b‖ + 3 * (C * δ)) + ρ * (m - 5 * (C * δ))
      ≤ 2 * ρ * (‖deriv r b‖ - C * δ) := by
    have hA : m ≤ ‖deriv r b‖ := hspeed b
    have hkey0 : ‖deriv r b‖ + 3 * (C * δ) + (m - 5 * (C * δ)) ≤ 2 * (‖deriv r b‖ - C * δ) := by
      linarith
    have hk := mul_le_mul_of_nonneg_left hkey0 hρ.le
    nlinarith [hk]
  linarith [hupper, hlower, hkey]

open LeanEval.KnotTheory.Quadrisecant in
/-- The parameterised form of `Work.Drive.thinCorner_distance_increasing`: the radial distance at a
parameter shift `±ρ` (`ρ ≤ ρmax`) is beaten by the distance to every point at circular parameter
distance at least `2 ρ`.  (The second clause is the mirror of the first; it is what the *head* of the
thin loop needs, cf. `Drive/radialGapOfTools`.) -/
theorem thinCornerDistanceIncreasingParam {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t]) :
    ∃ ε₂ ρmax : ℝ, 0 < ε₂ ∧ 0 < ρmax ∧ 4 * ρmax < period ∧
      ∀ r' : ℝ → Space, IsSmoothKnot r' →
        (∀ t : ℝ, ‖r' t - r t‖ < ε₂ ∧ ‖velocity r' t - velocity r t‖ < ε₂ ∧
          ‖deriv (deriv r') t - deriv (deriv r) t‖ < ε₂) →
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρmax → ∀ x s : ℝ, 2 * ρ ≤ circSep s x →
          ‖r' (x + ρ) - r' x‖ < ‖r' s - r' x‖ ∧
          ‖r' (x - ρ) - r' x‖ < ‖r' s - r' x‖ := by
  obtain ⟨m, M, C, hm, hM, hC, hspd, hspdM, hlip⟩ := thinCorner_speed_bounds hr
  have hC0 : 0 ≤ C := hC.le
  have hp : 0 < period := period_pos
  -- the local scale
  set δ : ℝ := min 1 (m / (64 * C)) with hδdef
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδC : C * δ ≤ m / 64 := by
    have h := min_le_right (1 : ℝ) (m / (64 * C))
    have h8 : C * (m / (64 * C)) = m / 64 := by field_simp
    calc C * δ = C * min 1 (m / (64 * C)) := by rw [hδdef]
      _ ≤ C * (m / (64 * C)) := mul_le_mul_of_nonneg_left h hC0
      _ = m / 64 := h8
  have h2δ : 2 * δ < period := by
    have hpi : (2 : ℝ) < period := by unfold period; have := Real.pi_gt_three; linarith
    linarith
  obtain ⟨μ, hμpos, hμ⟩ := thinCorner_separation hr hδpos h2δ
  -- the perturbation radius
  set ε₂ : ℝ := min (m / 16) (min (μ / 4) (1 / 2)) with hεdef
  have hεpos : 0 < ε₂ := by
    rw [hεdef]
    exact lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hεm : ε₂ ≤ m / 16 := by rw [hεdef]; exact min_le_left _ _
  have hεμ : ε₂ ≤ μ / 4 := by
    rw [hεdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hmε : 0 < m - ε₂ := by linarith [hεm, hm]
  have hμ2ε : 0 < μ - 2 * ε₂ := by linarith [hεμ, hμpos]
  have hM'pos : 0 < M + ε₂ := by linarith
  have hCε : 0 ≤ C + ε₂ := by linarith
  have hδC' : (C + ε₂) * δ ≤ (m - ε₂) / 8 := by
    have h2 : ε₂ * δ ≤ ε₂ := by
      calc ε₂ * δ ≤ ε₂ * 1 := mul_le_mul_of_nonneg_left hδ1 hεpos.le
        _ = ε₂ := mul_one _
    have h4 : (C + ε₂) * δ = C * δ + ε₂ * δ := by ring
    rw [h4]
    linarith [hδC, h2, hεm, hm]
  have hmargf : 0 < (m - ε₂) - 4 * ((C + ε₂) * δ) := by
    linarith [hδC', hmε]
  have hmargb : 0 < (m - ε₂) - 5 * ((C + ε₂) * δ) := by
    linarith [hδC', hmε]
  -- the parameter window
  set ρmax : ℝ := min (δ / 2) (min (period / 8) ((μ - 2 * ε₂) / (2 * (M + ε₂)))) with hρdef
  have hρmaxpos : 0 < ρmax := by
    rw [hρdef]
    refine lt_min (by linarith) (lt_min (by linarith) (div_pos hμ2ε (by linarith)))
  have hρmax_δ : ρmax ≤ δ := by
    have h1 : ρmax ≤ δ / 2 := min_le_left _ _
    linarith
  have h4ρmax : 4 * ρmax < period := by
    have h1 : ρmax ≤ period / 8 := le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hρmax_far : (M + ε₂) * ρmax < μ - 2 * ε₂ := by
    have h1 : ρmax ≤ (μ - 2 * ε₂) / (2 * (M + ε₂)) :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    calc (M + ε₂) * ρmax ≤ (M + ε₂) * ((μ - 2 * ε₂) / (2 * (M + ε₂))) :=
          mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = (μ - 2 * ε₂) / 2 := by field_simp
      _ < μ - 2 * ε₂ := by linarith
  refine ⟨ε₂, ρmax, hεpos, hρmaxpos, h4ρmax, ?_⟩
  intro r' hr' hclose ρ hρ hρmax x s hsep
  have hcse : circSep s x = ‖((s - x : ℝ) : AddCircle period)‖ := by
    rw [circSep, dist_eq_norm, ← AddCircle.coe_sub]
  have h4ρ : 4 * ρ < period := by linarith [hρmax, h4ρmax]
  set h : ℝ := thinCorner_red (s - x) with hhdef
  have hbnd := thinCorner_red_bounds hρ h4ρ (u := s - x) (by rw [← hcse]; exact hsep)
  have hh2ρ : 2 * ρ ≤ h := hbnd.1
  have hh2ρ' : 2 * ρ ≤ period - h := hbnd.2
  have hhIco : h ∈ Set.Ico (0 : ℝ) period := thinCorner_red_mem (s - x)
  have hhlt : h < period := hhIco.2
  have hρδ : ρ ≤ δ := le_trans hρmax hρmax_δ
  -- the transferred data of `r'`
  have hpos : ∀ t : ℝ, ‖r' t - r t‖ < ε₂ := fun t => (hclose t).1
  have hvel : ∀ t : ℝ, ‖velocity r' t - velocity r t‖ < ε₂ := fun t => (hclose t).2.1
  have hacc : ∀ t : ℝ, ‖deriv (deriv r') t - deriv (deriv r) t‖ < ε₂ := fun t => (hclose t).2.2
  have hdiff' : Differentiable ℝ r' := hr'.smooth.differentiable (by simp)
  have hspd' : ∀ t : ℝ, m - ε₂ ≤ ‖deriv r' t‖ := by
    intro t
    have h1 : m ≤ ‖deriv r t‖ := hspd t
    have h2 : ‖deriv r' t - deriv r t‖ < ε₂ := hvel t
    have h4 : ‖deriv r t‖ ≤ ‖deriv r' t‖ + ‖deriv r' t - deriv r t‖ := by
      have h5 := norm_add_le (deriv r' t) (deriv r t - deriv r' t)
      have h6 : deriv r' t + (deriv r t - deriv r' t) = deriv r t := by abel
      rw [h6, norm_sub_rev] at h5
      exact h5
    linarith
  have hspdM' : ∀ t : ℝ, ‖deriv r' t‖ ≤ M + ε₂ := by
    intro t
    have h1 : ‖deriv r t‖ ≤ M := hspdM t
    have h2 : ‖deriv r' t - deriv r t‖ < ε₂ := hvel t
    have h3 : ‖deriv r' t‖ ≤ ‖deriv r t‖ + ‖deriv r' t - deriv r t‖ := by
      have h5 := norm_add_le (deriv r t) (deriv r' t - deriv r t)
      have h6 : deriv r t + (deriv r' t - deriv r t) = deriv r' t := by abel
      rw [h6] at h5
      exact h5
    linarith
  have hlip' : ∀ t t' : ℝ, ‖deriv r' t - deriv r' t'‖ ≤ (C + ε₂) * |t' - t| :=
    deriv_lipschitz_of_c2close hr hr' hεpos.le hlip hacc
  have hrs : r' (x + h) = r' s := thinCorner_r_eq_of_coe_eq hr' (by
    rw [AddCircle.coe_add, thinCorner_red_coe, AddCircle.coe_sub]; abel)
  rcases le_or_gt h δ with hcase | hcase
  · -- forward-local regime
    have hfw := thinCorner_local_gap hdiff' hmε hCε hδC' hspd' hlip'
      (a := x) (b := x) (ρ := ρ) (τ := h)
      (by rw [sub_self, abs_zero]; exact hδpos.le) hρ hρδ hh2ρ hcase
    have hbw := thinCorner_local_gap_bwd hdiff' hmε hCε hδC' hspd' hlip'
      (a := x) (b := x) (ρ := ρ) (τ := h)
      (by rw [sub_self, abs_zero]; exact hδpos.le) hρ hρδ hh2ρ hcase
    rw [hrs] at hfw hbw
    exact ⟨by linarith [mul_pos hρ hmargf], by linarith [mul_pos hρ hmargb]⟩
  · rcases lt_or_ge h (period - δ) with hcase2 | hcase2
    · -- the far regime: use the reference separation
      have hxr : thinCorner_red x ∈ Set.Icc (0 : ℝ) period :=
        Set.Ico_subset_Icc_self (thinCorner_red_mem x)
      have hμ' : μ ≤ ‖r (thinCorner_red x + h) - r (thinCorner_red x)‖ :=
        hμ (thinCorner_red x) hxr h ⟨hcase.le, hcase2.le⟩
      have hsep'' : μ - 2 * ε₂
          ≤ ‖r' (thinCorner_red x + h) - r' (thinCorner_red x)‖ := by
        have hp1 : ‖r (thinCorner_red x + h) - r' (thinCorner_red x + h)‖ < ε₂ := by
          rw [norm_sub_rev]
          exact hpos (thinCorner_red x + h)
        have hp2 : ‖r' (thinCorner_red x) - r (thinCorner_red x)‖ < ε₂ :=
          hpos (thinCorner_red x)
        have htri : ‖r (thinCorner_red x + h) - r (thinCorner_red x)‖
            ≤ ‖r' (thinCorner_red x + h) - r' (thinCorner_red x)‖ + 2 * ε₂ := by
          have hsplit : r (thinCorner_red x + h) - r (thinCorner_red x)
              = (r (thinCorner_red x + h) - r' (thinCorner_red x + h))
                + (r' (thinCorner_red x + h) - r' (thinCorner_red x))
                + (r' (thinCorner_red x) - r (thinCorner_red x)) := by abel
          rw [hsplit]
          calc ‖(r (thinCorner_red x + h) - r' (thinCorner_red x + h))
                + (r' (thinCorner_red x + h) - r' (thinCorner_red x))
                + (r' (thinCorner_red x) - r (thinCorner_red x))‖
              ≤ ‖(r (thinCorner_red x + h) - r' (thinCorner_red x + h))
                + (r' (thinCorner_red x + h) - r' (thinCorner_red x))‖
                + ‖r' (thinCorner_red x) - r (thinCorner_red x)‖ := norm_add_le _ _
            _ ≤ (‖r (thinCorner_red x + h) - r' (thinCorner_red x + h)‖
                + ‖r' (thinCorner_red x + h) - r' (thinCorner_red x)‖)
                + ‖r' (thinCorner_red x) - r (thinCorner_red x)‖ := by
                linarith [norm_add_le (r (thinCorner_red x + h) - r' (thinCorner_red x + h))
                  (r' (thinCorner_red x + h) - r' (thinCorner_red x))]
            _ ≤ ε₂ + ‖r' (thinCorner_red x + h) - r' (thinCorner_red x)‖ + ε₂ := by linarith
            _ = ‖r' (thinCorner_red x + h) - r' (thinCorner_red x)‖ + 2 * ε₂ := by ring
        linarith
      have heq' : ‖r' (thinCorner_red x + h) - r' (thinCorner_red x)‖ = ‖r' s - r' x‖ := by
        rw [thinCorner_r_red_add hr' x h, thinCorner_r_red hr' x, hrs]
      have hub1 : ‖r' (x + ρ) - r' x‖ ≤ (M + ε₂) * ρ :=
        thinCorner_sub_le_speed hdiff' hM'pos.le hspdM' (b := x) (σ := ρ) hρ.le
      have hub2 : ‖r' (x - ρ) - r' x‖ ≤ (M + ε₂) * ρ := by
        have h1 : ((x - ρ) + ρ) = x := by ring
        have h := thinCorner_sub_le_speed hdiff' hM'pos.le hspdM' (b := x - ρ) (σ := ρ) hρ.le
        rw [h1, norm_sub_rev] at h
        exact h
      have hfar : (M + ε₂) * ρ < μ - 2 * ε₂ :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_left hρmax hM'pos.le) hρmax_far
      rw [heq'] at hsep''
      exact ⟨by linarith [hub1, hfar], by linarith [hub2, hfar]⟩
    · -- the backward-local regime (the wrap-around)
      have hτle : period - h ≤ δ := by linarith
      have hτpos : 0 < period - h := by linarith [hhlt]
      have hxsub : r' (x - (period - h)) = r' (x + h) := thinCorner_r_eq_of_coe_eq hr' (by
        rw [AddCircle.coe_sub, AddCircle.coe_sub, AddCircle.coe_add, AddCircle.coe_period]; abel)
      have hsimp : x - (period - h) + (period - h) = x := by ring
      have habs : |x - (x - (period - h))| ≤ δ := by
        have h1 : x - (x - (period - h)) = period - h := by ring
        rw [h1, abs_of_nonneg hτpos.le]
        exact hτle
      have hfw := thinCorner_local_gap hdiff' hmε hCε hδC' hspd' hlip'
        (a := x) (b := x - (period - h)) (ρ := ρ) (τ := period - h) habs hρ hρδ hh2ρ' hτle
      rw [hsimp, hxsub] at hfw
      have hbw := thinCorner_local_gap_bwd hdiff' hmε hCε hδC' hspd' hlip'
        (a := x) (b := x - (period - h)) (ρ := ρ) (τ := period - h) habs hρ hρδ hh2ρ' hτle
      rw [hsimp, hxsub] at hbw
      have hR : ‖r' x - r' (x + h)‖ = ‖r' s - r' x‖ := by rw [hrs, norm_sub_rev]
      rw [hR] at hfw hbw
      exact ⟨by linarith [mul_pos hρ hmargf], by linarith [mul_pos hρ hmargb]⟩

end

end Work.Drive
