import Mathlib
import Submission.Work.Drive.EpsForm.WaypointDesign2

namespace Work.Drive.EpsForm

open Set

noncomputable section

/-! ## Plane algebra for chords of the unit circle -/

/-- A point of the chord joining two points of the unit circle: if `P` and `Q` have squared
norm `1`, then the point of the segment `[P,Q]` at parameter `s ∈ [a,b]` has squared norm
`1 - λ(1-λ)·|P - Q|²` with `λ = (s-a)/(b-a)`.  In particular the open chord runs strictly
inside the circle as soon as `P ≠ Q`. -/
lemma seg_unit_norm {P Q : ℝ × ℝ} (hP : P.1 ^ 2 + P.2 ^ 2 = 1) (hQ : Q.1 ^ 2 + Q.2 ^ 2 = 1)
    (a b s : ℝ) :
    (seg P Q a b s).1 ^ 2 + (seg P Q a b s).2 ^ 2
      = 1 - ((s - a) / (b - a)) * (1 - (s - a) / (b - a))
          * ((P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2) := by
  simp only [seg]
  linear_combination (1 - (s - a) / (b - a)) * hP + ((s - a) / (b - a)) * hQ

/-- A nonzero vector of the plane has positive squared norm. -/
lemma sq_sum_pos_of_ne {u : ℝ × ℝ} (h : u ≠ 0) : 0 < u.1 ^ 2 + u.2 ^ 2 := by
  rcases eq_or_ne u.1 0 with h1 | h1
  · have h2 : u.2 ≠ 0 := fun h2 => h (Prod.ext h1 h2)
    nlinarith [sq_pos_of_ne_zero h2]
  · nlinarith [sq_pos_of_ne_zero h1]

/-! ## The waypoints lie on the unit circle -/

lemma nrm_W5c (t : ℝ) : (W5c t).1 ^ 2 + (W5c t).2 ^ 2 = 1 := by
  simp only [W5c]
  rw [Real.cos_sq_add_sin_sq]

lemma nrm_W3c (t : ℝ) : (W3c t).1 ^ 2 + (W3c t).2 ^ 2 = 1 := by
  by_cases h : inRange t
  · rw [W3c, if_pos h]
    simp only
    rw [Real.cos_sq_add_sin_sq]
  · rw [W3c, if_neg h]
    exact nrm_W5c t

/-- On the open chord range the waypoints `W3c t` and `W5c t` are distinct, so that the
chord `[W3c t, W5c t]` is a genuine chord of the unit circle.  (Equality would force
`phLift t + dlt t ≡ t (mod 2π)`, i.e. `dlt t = 3t/2 + π`, and `dlt t = cos (3t/4)/2 ≤ 1/2`
makes the right hand side nonpositive while `dlt t = sin (3t/4 + π/2)/2 < 3t/4 + π/2` makes
it positive.) -/
lemma W3c_ne_W5c_of_open {t : ℝ} (hu : u0 < t) (hv : t < v0) : W3c t ≠ W5c t := by
  intro h
  have hin : inRange t := ⟨le_of_lt hu, le_of_lt hv⟩
  have hfst := congrArg Prod.fst h
  have hsnd := congrArg Prod.snd h
  simp only [W3c, if_pos hin, W5c] at hfst hsnd
  have hdlt_pos : 0 < dlt t := by
    have hb := bump_pos hu hv
    unfold dlt
    linarith
  have hdlt_le : dlt t ≤ 1 / 2 := by
    have hb : bump t ≤ 1 := Real.sin_le_one _
    unfold dlt
    linarith
  have hangle : t - (phLift t + dlt t) = 3 * t / 2 + Real.pi - dlt t := by
    rw [phLift_eq]; ring
  have hcos1 : Real.cos (3 * t / 2 + Real.pi - dlt t) = 1 := by
    have := Real.cos_sub t (phLift t + dlt t)
    rw [hangle] at this
    rw [this, hfst, hsnd]
    have h2 : Real.cos t * Real.cos t + Real.sin t * Real.sin t = 1 := by
      nlinarith [Real.cos_sq_add_sin_sq t]
    linarith [h2]
  have hA0 : 3 * t / 2 + Real.pi - dlt t = 0 := by
    have hlt1 : -(2 * Real.pi) < 3 * t / 2 + Real.pi - dlt t := by
      have h1 : -Real.pi < 3 * t / 2 := by
        unfold u0 at hu; linarith [Real.pi_pos]
      linarith [hdlt_le, Real.pi_gt_three]
    have hlt2 : 3 * t / 2 + Real.pi - dlt t < 2 * Real.pi := by
      have h1 : 3 * t / 2 < Real.pi := by
        unfold v0 at hv; linarith [Real.pi_pos]
      linarith
    exact (Real.cos_eq_one_iff_of_lt_of_lt hlt1 hlt2).mp hcos1
  have hy : dlt t = 3 * t / 2 + Real.pi := by linarith
  have hZpos : 0 < 3 * t / 4 + Real.pi / 2 := by linarith
  have hdlt : dlt t = Real.sin (3 * t / 4 + Real.pi / 2) / 2 := by
    have h3 : 3 * t / 4 = (3 * t / 4 + Real.pi / 2) - Real.pi / 2 := by ring
    unfold dlt
    rw [bump_eq_cos, h3, Real.cos_sub_pi_div_two]
    ring_nf
  have hslt := Real.sin_lt hZpos
  linarith [hdlt, hy, hslt]

/-! ## The main statement -/

/-- **The interior intersection of the corrected profile with the unit circle.**
For `t ∈ (-π,π]`, the corrected profile `profX t` (the polyline
`W1 → W2c t → W3c t → W5c t` at levels `0 ≤ sig1c t ≤ sig2c t ≤ 1`) meets the unit
circle, at parameters `0 < s < 1`, exactly at the two chord levels `sig1 t`, `sig2 t`,
and this only for `t` in the chord range `[u0,v0]`; also `profX t 1 = W5c t`.

Route: `W2c t`, `W3c t`, `W5c t` all lie on the unit circle (`n2_W2c`, `n2_W3c`,
`n2_W5c` in `profW_injOn.lean`), the chord `[W2c t, W3c t]` and the chord
`[W3c t, W5c t]` run strictly inside the unit circle except at their endpoints (strict
convexity of the disc, via `n2` of a convex combination), the segment from `W1 = (-2,0)`
meets the circle only at `W2c t` (because `(W2c t).1 = cos (phLift t) ≤ -1/2` inside the
chord range and `(W2c t).1 = cos t ≤ -1/2` outside it), and the levels are ordered by
`waypoint_levels`. -/
theorem profX_levels {t s : ℝ} (ht : -Real.pi < t) (ht' : t ≤ Real.pi) :
    profX t 1 = W5c t ∧ (0 < s → s < 1 →
      (((profX t s).1 ^ 2 + (profX t s).2 ^ 2 = 1) ↔
        (inRange t ∧ (s = sig1 t ∨ s = sig2 t)))) := by
  refine ⟨profX_one t, fun hs0 hs1 => ⟨?_, ?_⟩⟩
  · intro hnorm
    by_cases hin : inRange t
    · have hs1c : sig1c t = sig1 t := by simp only [sig1c, if_pos hin]
      have hs2c : sig2c t = sig2 t := by simp only [sig2c, if_pos hin]
      by_cases hb1 : s ≤ sig1c t
      · -- the first piece `[W1, W2c t]` meets the circle only at its upper end
        rw [profX_br1 hb1, norm_br1 hin] at hnorm
        have hfac : (s / sig1c t - 1) * ((5 + 4 * Real.cos (phLift t)) * (s / sig1c t) - 3)
            = 0 := by linarith
        have hcos : Real.cos (phLift t) ≤ -(1 / 2) := cos_phLift_le_of_inRange hin
        have hcpos : 0 < 5 + 4 * Real.cos (phLift t) := by
          have := Real.neg_one_le_cos (phLift t); linarith
        have hcle : 5 + 4 * Real.cos (phLift t) ≤ 3 := by linarith
        have hratio_ge : 1 ≤ 3 / (5 + 4 * Real.cos (phLift t)) :=
          (one_le_div₀ hcpos).2 hcle
        have hsigpos : 0 < sig1c t := sig1c_pos t
        have hlam_le : s / sig1c t ≤ 1 := (div_le_one hsigpos).2 hb1
        have hratio : s / sig1c t = 1 := by
          rcases mul_eq_zero.mp hfac with h | h
          · linarith
          · have h2 : s / sig1c t = 3 / (5 + 4 * Real.cos (phLift t)) := by
              rw [eq_div_iff (ne_of_gt hcpos)]; linarith
            exact le_antisymm hlam_le (le_trans hratio_ge (le_of_eq h2.symm))
        have hse : s = sig1 t := by
          have := (div_eq_one_iff_eq (ne_of_gt hsigpos)).mp hratio
          rw [this, hs1c]
        exact ⟨hin, Or.inl hse⟩
      · by_cases hb2 : s ≤ sig2c t
        · -- the chord `[W2c t, W3c t]` meets the circle only at its two ends
          rw [profX_br2 hb1 hb2, norm_br2 hin] at hnorm
          have hlt : sig1c t < s := lt_of_not_ge hb1
          have hbump : 0 < bump t := by
            have : sig1 t < 1 := by rw [← hs1c]; linarith
            unfold sig1 at this; linarith
          have hopen := (bump_pos_iff hin).1 hbump
          have hss : sig1 t < sig2 t := sig1_lt_sig2 hopen.1 hopen.2
          have hdiff : 0 < sig2c t - sig1c t := by rw [hs1c, hs2c]; linarith
          have hlam_pos : 0 < (s - sig1c t) / (sig2c t - sig1c t) :=
            div_pos (by rw [hs1c]; linarith) hdiff
          have hcosd : Real.cos (dlt t) ≠ 1 := by
            have hd0 : 0 < dlt t := by unfold dlt; linarith
            have hd2 : dlt t < 2 * Real.pi := by
              have hb1' : bump t ≤ 1 := Real.sin_le_one _
              have hπ : (1 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
              unfold dlt; linarith
            have := Real.cos_eq_one_iff_of_lt_of_lt (by linarith) hd2
            intro hh; exact hd0.ne' (this.mp hh)
          have hfac : 2 * ((s - sig1c t) / (sig2c t - sig1c t))
              * (1 - (s - sig1c t) / (sig2c t - sig1c t)) * (1 - Real.cos (dlt t)) = 0 := by
            linarith
          have hlam : (s - sig1c t) / (sig2c t - sig1c t) = 1 := by
            rcases mul_eq_zero.mp hfac with h | h
            · rcases mul_eq_zero.mp h with h' | h'
              · exact absurd h' (by intro hh; linarith [hlam_pos])
              · linarith
            · exact absurd h (by intro hh; exact hcosd (by linarith))
          have hse : s = sig2 t := by
            have := (div_eq_one_iff_eq (ne_of_gt hdiff)).mp hlam
            rw [hs1c, hs2c] at this; linarith
          exact ⟨hin, Or.inr hse⟩
        · -- the chord `[W3c t, W5c t]` runs strictly inside the circle
          exfalso
          have hslt : sig2c t < s := lt_of_not_ge hb2
          have hbump : 0 < bump t := by
            have : sig2 t < 1 := by rw [← hs2c]; linarith
            unfold sig2 at this; linarith
          have hopen := (bump_pos_iff hin).1 hbump
          have hW : W3c t ≠ W5c t := W3c_ne_W5c_of_open hopen.1 hopen.2
          rw [profX_br3 hb1 hb2, seg_unit_norm (nrm_W3c t) (nrm_W5c t)] at hnorm
          have hden : 0 < 1 - sig2c t := by linarith
          have hlpos : 0 < (s - sig2c t) / (1 - sig2c t) := div_pos (by linarith) hden
          have hllt : (s - sig2c t) / (1 - sig2c t) < 1 := (div_lt_one hden).2 (by linarith)
          have hprod : 0 < ((s - sig2c t) / (1 - sig2c t))
              * (1 - (s - sig2c t) / (1 - sig2c t)) := mul_pos hlpos (by linarith)
          have hwn : 0 < ((W3c t).1 - (W5c t).1) ^ 2 + ((W3c t).2 - (W5c t).2) ^ 2 := by
            have := sq_sum_pos_of_ne (u := W3c t - W5c t) (sub_ne_zero.mpr hW)
            simpa only [Prod.fst_sub, Prod.snd_sub] using this
          have hpos := mul_pos hprod hwn
          linarith
    · -- outside the chord range the profile is the straight segment `[W1, W5c t]`
      have hs1c : sig1c t = 1 := by simp only [sig1c, if_neg hin]
      have hW : W2c t = W5c t := W2c_eq_of_not_inRange hin
      have hb1 : s ≤ sig1c t := by rw [hs1c]; exact le_of_lt hs1
      rw [profX_br1 hb1, hs1c, hW, norm_out] at hnorm
      exfalso
      have hfac : (s - 1) * ((5 + 4 * Real.cos t) * s - 3) = 0 := by linarith
      have hcos : Real.cos t ≤ -(1 / 2) := by
        rcases lt_or_ge t u0 with h | h
        · have h' : t ≤ -2 * Real.pi / 3 := by unfold u0 at h; linarith
          exact cos_le_neg_half_of_le (le_of_lt ht) h'
        · have hv : v0 < t := by
            by_contra hc
            exact hin ⟨h, le_of_not_gt hc⟩
          have h' : 2 * Real.pi / 3 ≤ t := by unfold v0 at hv; linarith
          exact cos_le_neg_half_of_ge h' ht'
      have hcpos : 0 < 5 + 4 * Real.cos t := by
        have := Real.neg_one_le_cos t; linarith
      have hcle : 5 + 4 * Real.cos t ≤ 3 := by linarith
      have hsge : 1 ≤ 3 / (5 + 4 * Real.cos t) := (one_le_div₀ hcpos).2 hcle
      have h3 : (5 + 4 * Real.cos t) * s - 3 = 0 := by
        rcases mul_eq_zero.mp hfac with h | h
        · exact absurd h (by intro hh; linarith [hs1])
        · exact h
      have hse : s = 3 / (5 + 4 * Real.cos t) := by
        rw [eq_div_iff (ne_of_gt hcpos)]; linarith
      linarith [hse, hsge, hs1]
  · -- conversely, the two chord levels do lie on the unit circle
    rintro ⟨hin, hsig | hsig⟩
    · have hs1c : sig1c t = sig1 t := by simp only [sig1c, if_pos hin]
      have hb1 : s ≤ sig1c t := by rw [hs1c, hsig]
      rw [profX_br1 hb1, norm_br1 hin, hsig, hs1c, div_self (ne_of_gt (sig1_pos t))]
      ring
    · have hs1c : sig1c t = sig1 t := by simp only [sig1c, if_pos hin]
      have hs2c : sig2c t = sig2 t := by simp only [sig2c, if_pos hin]
      have hs2lt : sig2 t < 1 := by rw [← hsig]; exact hs1
      have hbump : 0 < bump t := by unfold sig2 at hs2lt; linarith
      have hopen := (bump_pos_iff hin).1 hbump
      have hss : sig1 t < sig2 t := sig1_lt_sig2 hopen.1 hopen.2
      have hb1 : ¬ s ≤ sig1c t := by rw [hs1c, hsig]; exact not_le.mpr hss
      have hb2 : s ≤ sig2c t := by rw [hs2c, hsig]
      have hne : sig2 t - sig1 t ≠ 0 := ne_of_gt (sub_pos.mpr hss)
      rw [profX_br2 hb1 hb2, norm_br2 hin, hsig, hs1c, hs2c, div_self hne]
      ring

end

end Work.Drive.EpsForm
