import Mathlib
import Submission.Work.Smooth.JordanSeparation.Defs
import Submission.Work.Smooth.JordanSeparation.local_chord_estimate
import Submission.Work.Smooth.JordanSeparation.far_chord_bound

/-!
# Injectivity of the offset map of a transverse Lipschitz field

For a simple `C¹` immersed closed plane curve `c` and a field `v` which is a unit field uniformly
transverse to `c` and globally Lipschitz, the **offset map**
`offset c v (t, u) = c.γ t + u · v t` is injective on the strip `ℝ × (-δ, δ)` modulo the period
`2π`: if `offset c v (t,u) = offset c v (t',u')` with `|u|, |u'| < δ`, then `u = u'` and
`t' = t + 2πk`.  This is the tubular neighbourhood statement in the form needed for
`atMostTwo_connectedComponentIn_of_offset`.

The proof has three ingredients, all quantitative:

* a **local chord estimate** (`local_chord_estimate`): for small `|t' - t|` the chord
  `c.γ t' - c.γ t` is not tangent to `v t`,
  `μ |t' - t| ≤ |detV (c.γ t' - c.γ t) (v t)|`;
* a **global separation estimate** (`far_chord_bound`): parameters which are far apart on the
  circle parametrise points at distance at least `η > 0`;
* the Lipschitz property of `v`, which turns the first estimate into a lower bound on the
  coefficient `u'`.

Everything is then assembled: on the fundamental domain `[0, 2π)` a coincidence either happens at
equal parameters (trivial), at a small parameter difference (excluded by the local estimate), at a
far parameter difference (excluded by the global separation), or at a parameter difference close to
the full period (excluded by the local estimate applied after shifting one parameter by `2π`).
-/

open Set

namespace Work.Smooth.JordanSeparation

noncomputable section

/-! ## Helper lemmas -/

/-- `detV` is additive in its first argument. -/
private theorem detV_sub_left (u w x : ℂ) : detV (u - w) x = detV u x - detV w x := by
  rw [detV_eq, detV_eq, detV_eq]; simp only [Complex.sub_re, Complex.sub_im]; ring

/-- `detV` is additive in its second argument. -/
private theorem detV_sub_right (u x y : ℂ) : detV u (x - y) = detV u x - detV u y := by
  rw [detV_eq, detV_eq, detV_eq]; simp only [Complex.sub_re, Complex.sub_im]; ring

/-- **The Lipschitz step.**  If the chord of the curve over a small parameter interval is not
tangent to `v` at the base parameter, then the coefficient `u'` of a coincidence
`offset c v (t,u) = offset c v (t',u')` is bounded below by `μ / L`. -/
private theorem offset_det_bound (c : Work.Smooth.Jordan.SmoothPlaneCurve) {v : ℝ → ℂ} {L μ ε : ℝ}
    (hL : 0 < L) (hv : ∀ t, ‖v t‖ = 1) (hlip : IsLipschitzField L v)
    (hloc : ∀ t t' : ℝ, 0 < |t' - t| → |t' - t| ≤ ε →
      μ * |t' - t| ≤ |detV (c.γ t' - c.γ t) (v t)|)
    {t t' u u' : ℝ} (hd : 0 < |t' - t|) (hle : |t' - t| ≤ ε)
    (heq : offset c v (t, u) = offset c v (t', u')) : μ / L ≤ |u'| := by
  have h1 := hloc t t' hd hle
  have hchord : c.γ t' - c.γ t = u * v t - u' * v t' := by
    have h : c.γ t' + u' * v t' = c.γ t + u * v t := by
      have hh := heq; simp only [offset] at hh; exact hh.symm
    calc c.γ t' - c.γ t = (c.γ t' + u' * v t') - u' * v t' - c.γ t := by ring
      _ = (c.γ t + u * v t) - u' * v t' - c.γ t := by rw [h]
      _ = u * v t - u' * v t' := by ring
  have hdet : detV (c.γ t' - c.γ t) (v t) = -(u' * detV (v t') (v t)) := by
    rw [hchord, detV_sub_left, detV_smul_left, detV_smul_left, detV_self, mul_zero]
    ring
  have hbd : |detV (v t') (v t)| ≤ L * |t' - t| := by
    have h := abs_detV_le (v t') (v t - v t')
    have h' : detV (v t') (v t - v t') = detV (v t') (v t) := by
      rw [detV_sub_right, detV_self, sub_zero]
    rw [h'] at h
    calc |detV (v t') (v t)| ≤ ‖v t'‖ * ‖v t - v t'‖ := h
      _ = ‖v t - v t'‖ := by rw [hv t', one_mul]
      _ ≤ L * |t - t'| := hlip t t'
      _ = L * |t' - t| := by rw [abs_sub_comm]
  have h2 : |detV (c.γ t' - c.γ t) (v t)| = |u'| * |detV (v t') (v t)| := by
    rw [hdet, abs_neg, abs_mul]
  rw [h2] at h1
  have h3 : μ ≤ |u'| * L := by
    have h4 : μ * |t' - t| ≤ (|u'| * L) * |t' - t| := by
      calc μ * |t' - t| ≤ |u'| * |detV (v t') (v t)| := h1
        _ ≤ |u'| * (L * |t' - t|) := mul_le_mul_of_nonneg_left hbd (abs_nonneg _)
        _ = (|u'| * L) * |t' - t| := by ring
    exact le_of_mul_le_mul_right h4 hd
  rwa [div_le_iff₀ hL]

/-- Every real number is congruent modulo `2π` to a point of `[0, 2π)`. -/
theorem exists_int_sub_mem_Ico (t : ℝ) :
    ∃ k : ℤ, t - (k : ℝ) * (2 * Real.pi) ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := by
  refine ⟨⌊t / (2 * Real.pi)⌋, ?_⟩
  have hT : (0 : ℝ) < 2 * Real.pi := by positivity
  have h : t - (⌊t / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi)
      = Int.fract (t / (2 * Real.pi)) * (2 * Real.pi) := by
    rw [Int.fract]; field_simp
  rw [Set.mem_Ico, h]
  constructor
  · exact mul_nonneg (Int.fract_nonneg _) hT.le
  · simpa using mul_lt_mul_of_pos_right (Int.fract_lt_one _) hT

/-! ## The main theorem -/

theorem offset_injective (c : Work.Smooth.Jordan.SmoothPlaneCurve)
    (himm : Work.Smooth.Jordan.SmoothPlaneCurve.IsImmersion c) (hsimple : c.toPlaneCurve.IsSimple)
    {v : ℝ → ℂ} {κ L : ℝ} (hκ : 0 < κ) (hL : 0 < L)
    (hper : Function.Periodic v (2 * Real.pi))
    (htrans : Work.Smooth.JordanSeparation.IsTransverseUnitField c κ v)
    (hlip : Work.Smooth.JordanSeparation.IsLipschitzField L v) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t t' u u' : ℝ, |u| < δ → |u'| < δ →
      Work.Smooth.JordanSeparation.offset c v (t, u)
        = Work.Smooth.JordanSeparation.offset c v (t', u') →
        u = u' ∧ ∃ k : ℤ, t' = t + k * (2 * Real.pi) := by
  obtain ⟨ε₀, hε₀pos, μ, hμpos, hloc₀⟩ := local_chord_estimate c himm hκ hL htrans hlip
  set ε := min ε₀ Real.pi with hεdef
  have hεpos : 0 < ε := lt_min hε₀pos Real.pi_pos
  have hloc : ∀ t t' : ℝ, 0 < |t' - t| → |t' - t| ≤ ε →
      μ * |t' - t| ≤ |detV (c.γ t' - c.γ t) (v t)| :=
    fun t t' h1 h2 => hloc₀ t t' h1 (le_trans h2 (min_le_left _ _))
  obtain ⟨η, hηpos, hfar⟩ := far_chord_bound c hsimple hεpos (min_le_right _ _)
  set δ := min (μ / L) (η / 2) with hδdef
  have hδpos : 0 < δ := lt_min (div_pos hμpos hL) (by linarith)
  refine ⟨δ, hδpos, ?_⟩
  intro t t' u u' hu hu' heq
  -- injectivity on the fundamental domain `[0, 2π)`
  have key : ∀ t t' u u' : ℝ, t ∈ Set.Ico 0 (2 * Real.pi) → t' ∈ Set.Ico 0 (2 * Real.pi) →
      |u| < δ → |u'| < δ → offset c v (t, u) = offset c v (t', u') →
      t = t' ∧ u = u' := by
    intro t t' u u' ht ht' hu hu' heq
    have hs_lt : |t' - t| < 2 * Real.pi := by
      rw [abs_lt]; constructor <;> linarith [ht.1, ht.2, ht'.1, ht'.2]
    by_cases hs0 : t' - t = 0
    · -- equal parameters: the coefficients agree because `v t ≠ 0`
      have htt' : t' = t := by linarith
      refine ⟨htt'.symm, ?_⟩
      have hmul : (u : ℂ) * v t = (u' : ℂ) * v t := by
        have h := heq
        rw [htt'] at h
        simp only [offset] at h
        exact add_left_cancel h
      have hvt0 : v t ≠ 0 := by
        intro h0
        have h1 := htrans.1 t
        rw [h0, norm_zero] at h1
        norm_num at h1
      exact Complex.ofReal_injective (mul_right_cancel₀ hvt0 hmul)
    · have hd : 0 < |t' - t| := abs_pos.mpr hs0
      by_cases hε' : |t' - t| ≤ ε
      · -- small parameter difference: the local chord estimate gives `|u'| ≥ μ / L`
        rcases lt_or_gt_of_ne hs0 with hlt | hgt
        · have hd' : 0 < |t - t'| := by rw [abs_sub_comm]; exact hd
          have hle' : |t - t'| ≤ ε := by rw [abs_sub_comm]; exact hε'
          have hh := offset_det_bound c hL htrans.1 hlip hloc hd' hle' heq.symm
          exact (not_lt_of_ge hh (lt_of_lt_of_le hu (min_le_left _ _))).elim
        · have hh := offset_det_bound c hL htrans.1 hlip hloc hd hε' heq
          exact (not_lt_of_ge hh (lt_of_lt_of_le hu' (min_le_left _ _))).elim
      · by_cases hfar' : |t' - t| ≤ 2 * Real.pi - ε
        · -- far parameters: the two points of the curve are at distance at least `η > 2δ`
          have hη := hfar t t' ht ht' (le_of_lt (lt_of_not_ge hε')) hfar'
          have hchord : c.γ t - c.γ t' = u' * v t' - u * v t := by
            have h : c.γ t + u * v t = c.γ t' + u' * v t' := by
              have hh := heq; simpa only [offset] using hh
            calc c.γ t - c.γ t' = (c.γ t + u * v t) - u * v t - c.γ t' := by ring
              _ = (c.γ t' + u' * v t') - u * v t - c.γ t' := by rw [h]
              _ = u' * v t' - u * v t := by ring
          have hslack : ‖c.γ t - c.γ t'‖ ≤ |u| + |u'| := by
            rw [hchord]
            calc ‖u' * v t' - u * v t‖ ≤ ‖u' * v t'‖ + ‖u * v t‖ := norm_sub_le _ _
              _ = |u'| + |u| := by simp [htrans.1, Complex.norm_real, Real.norm_eq_abs]
              _ = |u| + |u'| := by ring
          have hlt : ‖c.γ t - c.γ t'‖ < η := by
            have h2 : |u| + |u'| < η := by
              have h1 : δ ≤ η / 2 := min_le_right _ _
              linarith
            linarith
          exact (not_lt_of_ge hη hlt).elim
        · -- parameter difference close to a full period: shift one parameter by `2π`
          rcases lt_or_gt_of_ne hs0 with hlt | hgt
          · have hbnd : 2 * Real.pi - (t - t') < ε := by
              have h := lt_of_not_ge hfar'
              rw [abs_of_neg hlt] at h
              linarith
            have hpos : 0 < 2 * Real.pi - (t - t') := by
              have h := hs_lt; rw [abs_of_neg hlt] at h; linarith
            have hdiff : |t - (t' + 2 * Real.pi)| = 2 * Real.pi - (t - t') := by
              rw [show t - (t' + 2 * Real.pi) = -(2 * Real.pi - (t - t')) by ring, abs_neg,
                abs_of_pos hpos]
            have hd' : 0 < |t - (t' + 2 * Real.pi)| := by rw [hdiff]; exact hpos
            have hle' : |t - (t' + 2 * Real.pi)| ≤ ε := by rw [hdiff]; linarith
            have heq' : offset c v (t' + 2 * Real.pi, u') = offset c v (t, u) := by
              rw [offset_periodic c hper t' u']; exact heq.symm
            have hh := offset_det_bound c hL htrans.1 hlip hloc hd' hle' heq'
            exact (not_lt_of_ge hh (lt_of_lt_of_le hu (min_le_left _ _))).elim
          · have hbnd : 2 * Real.pi - (t' - t) < ε := by
              have h := lt_of_not_ge hfar'
              rw [abs_of_pos hgt] at h
              linarith
            have hpos : 0 < 2 * Real.pi - (t' - t) := by
              have h := hs_lt; rw [abs_of_pos hgt] at h; linarith
            have hdiff : |t' - (t + 2 * Real.pi)| = 2 * Real.pi - (t' - t) := by
              rw [show t' - (t + 2 * Real.pi) = -(2 * Real.pi - (t' - t)) by ring, abs_neg,
                abs_of_pos hpos]
            have hd' : 0 < |t' - (t + 2 * Real.pi)| := by rw [hdiff]; exact hpos
            have hle' : |t' - (t + 2 * Real.pi)| ≤ ε := by rw [hdiff]; linarith
            have heq' : offset c v (t + 2 * Real.pi, u) = offset c v (t', u') := by
              rw [offset_periodic c hper t u]; exact heq
            have hh := offset_det_bound c hL htrans.1 hlip hloc hd' hle' heq'
            exact (not_lt_of_ge hh (lt_of_lt_of_le hu' (min_le_left _ _))).elim
  -- reduce the parameters modulo `2π` into the fundamental domain
  obtain ⟨n, hn⟩ := exists_int_sub_mem_Ico t
  obtain ⟨m, hm⟩ := exists_int_sub_mem_Ico t'
  set t₀ := t - (n : ℝ) * (2 * Real.pi) with ht₀
  set t₁ := t' - (m : ℝ) * (2 * Real.pi) with ht₁
  have ht₀mem : t₀ ∈ Set.Ico 0 (2 * Real.pi) := by rw [ht₀]; exact hn
  have ht₁mem : t₁ ∈ Set.Ico 0 (2 * Real.pi) := by rw [ht₁]; exact hm
  have ht_eq : t = t₀ + (n : ℝ) * (2 * Real.pi) := by rw [ht₀]; ring
  have ht'_eq : t' = t₁ + (m : ℝ) * (2 * Real.pi) := by rw [ht₁]; ring
  have hct : c.γ t = c.γ t₀ := by rw [ht_eq]; exact c.periodic.int_mul n t₀
  have hvt : v t = v t₀ := by rw [ht_eq]; exact hper.int_mul n t₀
  have hct' : c.γ t' = c.γ t₁ := by rw [ht'_eq]; exact c.periodic.int_mul m t₁
  have hvt' : v t' = v t₁ := by rw [ht'_eq]; exact hper.int_mul m t₁
  have heq₀ : offset c v (t₀, u) = offset c v (t₁, u') := by
    have h := heq
    simp only [offset] at h ⊢
    rw [← hct, ← hvt, ← hct', ← hvt']
    exact h
  obtain ⟨ht01, hu01⟩ := key t₀ t₁ u u' ht₀mem ht₁mem hu hu' heq₀
  refine ⟨hu01, m - n, ?_⟩
  have hk : t' = t + ((m : ℝ) - (n : ℝ)) * (2 * Real.pi) := by
    rw [ht'_eq, ht_eq, ← ht01]
    ring
  rw [hk, Int.cast_sub]

end

end Work.Smooth.JordanSeparation
