import Submission.Work.OddEnvelope.ChordCurve

/-!
# The two branches of the envelope profile

`envelopeRight p c t = σ t + p σ`, where `σ` is the unique slope with `c σ = t`.  The left branch
of the profile is the same construction with `c = x` and `p = -h` (see
`envelopeLeft_eq`), so all the analytic work is done once, in this file, for a *branch*
`(p, c)`: a chord curve `c` (see `IsChordCurve`) together with a perturbation `p` vanishing
near `0` (`IsEnvelopeBranch`).

Main results:

* `IsEnvelopeBranch.strictMonoOn_curve` : `σ ↦ σ c σ + p σ` is strictly increasing;
* `IsEnvelopeBranch.envelopeRight_pos` : the branch is positive on `(0,1)`;
* `IsEnvelopeBranch.envelopeRight_eq_semicircle` : on the unperturbed part `(0, tStar)` the
  branch equals the semicircle `√(1-t²)`;
* `IsEnvelopeBranch.kSlope_neg` : the logarithmic derivative `kSlope p c` is negative.
-/

namespace Work.OddEnvelope

noncomputable section

open Set Filter
open scoped Topology ContDiff

/-- A branch of the envelope profile: a chord curve `c` with a perturbation `p` vanishing on
`(0, 1 - 2τ)` (so that the branch is positive there) and outside `(1 - τ, ∞)` (the perturbed
window).  The conditions `mono` and `shape` are the first and second order shape conditions. -/
structure IsEnvelopeBranch (p c : ℝ → ℝ) extends IsChordCurve c : Prop where
  /-- `p` is smooth on `(0,∞)`. -/
  smooth_p : ContDiffOn ℝ ∞ p (Set.Ioi 0)
  /-- the curve is positive on `(0,∞)`. -/
  pos_c : ∀ s, 0 < s → 0 < c s
  /-- `p` vanishes for small slopes. -/
  vanish_p : ∀ s, 0 < s → s < 1 - 2 * tau → p s = 0
  /-- `p` vanishes for large slopes. -/
  vanish_p_tail : ∀ s, 1 - tau < s → p s = 0
  /-- `σ ↦ σ c σ + p σ` is strictly increasing. -/
  mono : ∀ s, 0 < s → 0 < c s + s * deriv c s + deriv p s
  /-- second order shape condition (strict concavity of the branch). -/
  shape : ∀ s, 0 < s →
    0 < 2 * (deriv c s) ^ 2 - c s * deriv (deriv c) s +
      deriv (deriv p) s * deriv c s - deriv p s * deriv (deriv c) s

variable {p c : ℝ → ℝ}

lemma IsEnvelopeBranch.strictAntiOn (hb : IsEnvelopeBranch p c) : StrictAntiOn c (Set.Ioi 0) :=
  hb.toIsChordCurve.strictAntiOn

/-- The curve `σ ↦ σ c σ + p σ` of the branch is strictly increasing. -/
lemma IsEnvelopeBranch.strictMonoOn_curve (hb : IsEnvelopeBranch p c) :
    StrictMonoOn (fun σ => σ * c σ + p σ) (Set.Ioi 0) := by
  have hderiv : ∀ s, 0 < s →
      deriv (fun σ => σ * c σ + p σ) s = c s + s * deriv c s + deriv p s := by
    intro s hs
    have hcs : ContDiffAt ℝ ∞ c s := hb.smooth.contDiffAt (isOpen_Ioi.mem_nhds hs)
    have hps : ContDiffAt ℝ ∞ p s := hb.smooth_p.contDiffAt (isOpen_Ioi.mem_nhds hs)
    have hd : HasDerivAt (fun σ => σ * c σ + p σ) (1 * c s + s * deriv c s + deriv p s) s :=
      ((hasDerivAt_id s).mul (hcs.differentiableAt (by simp)).hasDerivAt).add
        (hps.differentiableAt (by simp)).hasDerivAt
    simpa [one_mul] using hd.deriv
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) ?_ ?_
  · exact (continuousOn_id.mul hb.smooth.continuousOn).add hb.smooth_p.continuousOn
  · intro s hs
    rw [interior_Ioi] at hs
    rw [hderiv s hs]
    exact hb.mono s hs

lemma IsEnvelopeBranch.kSlope_neg (hb : IsEnvelopeBranch p c) {σ : ℝ} (hσ : 0 < σ) :
    kSlope p c σ < 0 := by
  rw [kSlope, div_neg_iff]
  exact Or.inl ⟨hb.mono σ hσ, hb.deriv_neg σ hσ⟩

/-- The right branch of the envelope is positive on `(0,1)`. -/
lemma IsEnvelopeBranch.envelopeRight_pos (hb : IsEnvelopeBranch p c) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) : 0 < envelopeRight p c t := by
  set σ := slopeRight c t with hσdef
  have hσpos : 0 < σ := by rw [hσdef]; exact hb.toIsChordCurve.slopeRight_pos ht
  have hcσ : c σ = t := by rw [hσdef]; exact hb.toIsChordCurve.slopeRight_eq ht
  have hminpos : 0 < min σ (1 - 2 * tau) := lt_min hσpos one_sub_two_tau_pos
  obtain ⟨σ', hσ'pos, hσ'lt⟩ : ∃ σ' : ℝ, 0 < σ' ∧ σ' < min σ (1 - 2 * tau) :=
    ⟨min σ (1 - 2 * tau) / 2, by linarith, by linarith⟩
  have hle : σ' < σ := lt_of_lt_of_le hσ'lt (min_le_left _ _)
  have hle2 : σ' < 1 - 2 * tau := lt_of_lt_of_le hσ'lt (min_le_right _ _)
  have hmono := hb.strictMonoOn_curve hσ'pos hσpos hle
  have hval : (fun u => u * c u + p u) σ' = σ' * c σ' := by
    simp [hb.vanish_p σ' hσ'pos hle2]
  have hgoal : envelopeRight p c t = (fun u => u * c u + p u) σ := by
    rw [envelopeRight, ← hσdef, ← hcσ]
  have hpos' : 0 < σ' * c σ' := mul_pos hσ'pos (hb.pos_c σ' hσ'pos)
  rw [hgoal]
  have hpos'' : (0 : ℝ) < (fun u => u * c u + p u) σ' := by rw [hval]; exact hpos'
  linarith [hmono, hpos'']

/-- On the unperturbed part `(0, tStar)` the right branch is the semicircle. -/
lemma IsEnvelopeBranch.envelopeRight_eq_semicircle (hb : IsEnvelopeBranch p c) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) tStar) : envelopeRight p c t = semicircle t := by
  set σ := slopeRight c t with hσdef
  have ht' : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨ht.1, lt_trans ht.2 tStar_lt_one⟩
  have hσpos : 0 < σ := by rw [hσdef]; exact hb.toIsChordCurve.slopeRight_pos ht'
  have hcσ : c σ = t := by rw [hσdef]; exact hb.toIsChordCurve.slopeRight_eq ht'
  have hσgt : 1 - tau < σ := by
    rcases lt_trichotomy σ (1 - tau) with h | h | h
    · have h2 : c (1 - tau) < c σ :=
        hb.toIsChordCurve.strictAntiOn hσpos one_sub_tau_pos h
      rw [hb.toIsChordCurve.tail (1 - tau) le_rfl, hcσ] at h2
      exact absurd h2 (not_lt.mpr ht.2.le)
    · have h2 : c σ = tStar := by
        rw [h]; exact hb.toIsChordCurve.tail (1 - tau) le_rfl
      rw [hcσ] at h2
      exact absurd h2 (ne_of_lt ht.2)
    · exact h
  have hp0 : p σ = 0 := hb.vanish_p_tail σ hσgt
  have hpx : c σ = profileX σ := hb.toIsChordCurve.tail σ hσgt.le
  have ht_eq : t = profileX σ := by rw [← hcσ, hpx]
  calc envelopeRight p c t = slopeRight c t * t + p (slopeRight c t) := rfl
    _ = σ * profileX σ + p σ := by rw [show slopeRight c t = σ from hσdef.symm, ht_eq]
    _ = σ * profileX σ := by rw [hp0, add_zero]
    _ = semicircle (profileX σ) := mul_profileX_eq_semicircle hσpos
    _ = semicircle t := by rw [ht_eq]

end

end Work.OddEnvelope
