import Mathlib
import Submission.Work.OddVolterra.Free.free_slope_api

/-!
# Continuity of the untruncated (free-tip) envelope profile

This file proves `continuousOn_envProfileFree`: for a free-tip envelope curve and a slope `c > 0`,
the untruncated profile `Work.OddVolterra.Free.envProfileFree h x y` is continuous on the closed
interval `[-(x c), y c]`.

There is no `tendsto_one` field to lean on, so `Work.OddEnvelope.slopeRight` is no longer
automatically the inverse of the chord curve on `(0,1)`.  Everything is rebuilt from the three
facts that *are* available: strict antitonicity (`x_deriv_neg`/`y_deriv_neg`), positivity on
`(0,∞)` (from the semicircle tail) and the semicircle tail itself, which produces an explicit
realiser of any value below `c s` (via the intermediate value property) and shows that the
realiser tends to `∞` as the value tends to the tip.
-/

namespace Work.OddVolterra.Free

noncomputable section

open Set Filter
open scoped Topology ContDiff

variable {p c : ℝ → ℝ}

/-! ## The realising slope of a value of the curve -/

/-- A strictly antitone curve with the semicircle tail realises every value of `(0, c s]`. -/
theorem exists_slope_le_of_lt {c : ℝ → ℝ} (hcont : ContinuousOn c (Set.Ioi 0))
    (hanti : StrictAntiOn c (Set.Ioi 0))
    (htail : ∀ s : ℝ, 1 - Work.OddCurve.tau ≤ s → c s = Work.OddEnvelope.profileX s)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hts : t ≤ c s) :
    ∃ σ : ℝ, s ≤ σ ∧ 0 < σ ∧ c σ = t := by
  set ρ : ℝ := max s (1 - Work.OddCurve.tau) + 1 / t + 1 with hρdef
  have hρgt : max s (1 - Work.OddCurve.tau) < ρ := by
    have h2 : (0 : ℝ) < 1 / t := by positivity
    rw [hρdef]; linarith
  have hρs : s < ρ := lt_of_le_of_lt (le_max_left _ _) hρgt
  have hρτ : 1 - Work.OddCurve.tau ≤ ρ :=
    le_of_lt (lt_of_le_of_lt (le_max_right _ _) hρgt)
  have hrec : 1 / t < ρ := by
    rw [hρdef]
    have h2 : (0 : ℝ) < 1 / t := by positivity
    have h3 : (0 : ℝ) ≤ max s (1 - Work.OddCurve.tau) := le_trans hs.le (le_max_left _ _)
    linarith
  have hρpos : 0 < ρ := lt_trans hs hρs
  have hcρ : c ρ = Work.OddEnvelope.profileX ρ := htail ρ hρτ
  have hpxρ : Work.OddEnvelope.profileX ρ < t :=
    Work.OddCurve.Free.IsEnvelopeCurveFree.lt_profileX_of_lt_div ht hrec
  have hcρlt : c ρ < t := by rw [hcρ]; exact hpxρ
  have hcont' : ContinuousOn (fun σ : ℝ => -c σ) (Set.Icc s ρ) :=
    (hcont.mono (fun u hu => lt_of_lt_of_le hs hu.1)).neg
  have hmem : -t ∈ Set.Icc ((fun σ : ℝ => -c σ) s) ((fun σ : ℝ => -c σ) ρ) :=
    ⟨by simpa using neg_le_neg hts, by simpa using neg_le_neg hcρlt.le⟩
  obtain ⟨σ, hσ, hσeq⟩ := intermediate_value_Icc hρs.le hcont' hmem
  exact ⟨σ, hσ.1, lt_of_lt_of_le hs hσ.1, by simpa using hσeq⟩

/-- If `σ > 0` realises `t` then it *is* the inverse slope at `t`. -/
theorem slopeRight_eq_of_lt {c : ℝ → ℝ} (hanti : StrictAntiOn c (Set.Ioi 0)) {σ t : ℝ}
    (hσ : 0 < σ) (h : c σ = t) : Work.OddEnvelope.slopeRight c t = σ := by
  have hmem := Function.invFunOn_pos (s := Set.Ioi (0 : ℝ)) ⟨σ, hσ, h⟩
  exact hanti.injOn hmem.1 hσ (by rw [hmem.2, h])

/-- Eventually around a value of the curve, the inverse slope really is a realiser of that
value. -/
theorem eventually_slopeRight_realises {c : ℝ → ℝ} (hcont : ContinuousOn c (Set.Ioi 0))
    (hanti : StrictAntiOn c (Set.Ioi 0)) (hpos : ∀ s : ℝ, 0 < s → 0 < c s)
    (htail : ∀ s : ℝ, 1 - Work.OddCurve.tau ≤ s → c s = Work.OddEnvelope.profileX s)
    {t₀ σ₀ : ℝ} (hσ₀ : 0 < σ₀) (hcσ₀ : c σ₀ = t₀) :
    ∀ᶠ t in 𝓝 t₀, c (Work.OddEnvelope.slopeRight c t) = t := by
  have hσ₀2 : 0 < σ₀ / 2 := by linarith
  have hlt2 : σ₀ / 2 < σ₀ := by linarith
  have h1 : (0:ℝ) < σ₀ + σ₀ / 2 := by linarith
  have h2 : σ₀ < σ₀ + σ₀ / 2 := by linarith
  have hlo : c (σ₀ + σ₀ / 2) < t₀ := by
    rw [← hcσ₀]
    exact hanti hσ₀ h1 h2
  have hhi : t₀ < c (σ₀ / 2) := by
    rw [← hcσ₀]
    exact hanti hσ₀2 hσ₀ hlt2
  have hlopos : 0 < c (σ₀ + σ₀ / 2) := hpos _ h1
  filter_upwards [isOpen_Ioo.mem_nhds ⟨hlo, hhi⟩] with t ht
  have htpos : 0 < t := lt_trans hlopos ht.1
  obtain ⟨σ, hσs, hσpos, hcσ⟩ := exists_slope_le_of_lt hcont hanti htail hσ₀2 htpos ht.2.le
  rw [slopeRight_eq_of_lt hanti hσpos hcσ]
  exact hcσ

/-- **The inverse slope is continuous at every value of the curve.** -/
theorem tendsto_slopeRight_of_eq {c : ℝ → ℝ} (hcont : ContinuousOn c (Set.Ioi 0))
    (hanti : StrictAntiOn c (Set.Ioi 0)) (hpos : ∀ s : ℝ, 0 < s → 0 < c s)
    (htail : ∀ s : ℝ, 1 - Work.OddCurve.tau ≤ s → c s = Work.OddEnvelope.profileX s)
    {t₀ σ₀ : ℝ} (hσ₀ : 0 < σ₀) (hcσ₀ : c σ₀ = t₀) :
    Tendsto (fun t : ℝ => Work.OddEnvelope.slopeRight c t) (𝓝 t₀) (𝓝 σ₀) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set ε' : ℝ := min (ε / 2) (σ₀ / 2) with hε'def
  have hε'pos : 0 < ε' := lt_min (by linarith) (by linarith)
  have hε'lt : ε' < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hσ₀' : 0 < σ₀ - ε' := by
    have := min_le_right (ε / 2) (σ₀ / 2)
    linarith
  have h1 : (0:ℝ) < σ₀ + ε' := by linarith
  have h2 : σ₀ < σ₀ + ε' := by linarith
  have h3 : σ₀ - ε' < σ₀ := by linarith
  have hlo : c (σ₀ + ε') < t₀ := by
    rw [← hcσ₀]
    exact hanti hσ₀ h1 h2
  have hhi : t₀ < c (σ₀ - ε') := by
    rw [← hcσ₀]
    exact hanti hσ₀' hσ₀ h3
  have hlopos : 0 < c (σ₀ + ε') := hpos _ h1
  filter_upwards [isOpen_Ioo.mem_nhds ⟨hlo, hhi⟩] with t ht
  have htpos : 0 < t := lt_trans hlopos ht.1
  obtain ⟨σ, hσs, hσpos, hcσ⟩ := exists_slope_le_of_lt hcont hanti htail hσ₀' htpos ht.2.le
  have hsl : Work.OddEnvelope.slopeRight c t = σ := slopeRight_eq_of_lt hanti hσpos hcσ
  have hlt1 : σ < σ₀ + ε' := by
    rcases lt_trichotomy σ (σ₀ + ε') with h | h | h
    · exact h
    · exfalso
      rw [h] at hcσ
      linarith [hcσ, ht.1]
    · exfalso
      have h' := hanti h1 hσpos h
      rw [hcσ] at h'
      linarith [ht.1]
  rw [Real.dist_eq, hsl, abs_lt]
  exact ⟨by linarith, by linarith⟩

/-- **Continuity of the right branch at a value of the curve.** -/
theorem continuousAt_envelopeRight_of_eq {c p : ℝ → ℝ} (hcont : ContinuousOn c (Set.Ioi 0))
    (hanti : StrictAntiOn c (Set.Ioi 0)) (hpos : ∀ s : ℝ, 0 < s → 0 < c s)
    (htail : ∀ s : ℝ, 1 - Work.OddCurve.tau ≤ s → c s = Work.OddEnvelope.profileX s)
    (hp : ContinuousOn p (Set.Ioi 0)) {t₀ σ₀ : ℝ} (hσ₀ : 0 < σ₀) (hcσ₀ : c σ₀ = t₀) :
    ContinuousAt (Work.OddEnvelope.envelopeRight p c) t₀ := by
  have hslope := tendsto_slopeRight_of_eq hcont hanti hpos htail hσ₀ hcσ₀
  have hG : ContinuousAt (fun σ : ℝ => σ * c σ + p σ) σ₀ :=
    ((continuousAt_id.mul (hcont.continuousAt (isOpen_Ioi.mem_nhds hσ₀))).add
      (hp.continuousAt (isOpen_Ioi.mem_nhds hσ₀)))
  have hsl₀ : Work.OddEnvelope.slopeRight c t₀ = σ₀ := slopeRight_eq_of_lt hanti hσ₀ hcσ₀
  have hslope' : ContinuousAt (Work.OddEnvelope.slopeRight c) t₀ := by
    show Tendsto (Work.OddEnvelope.slopeRight c) (𝓝 t₀) (𝓝 (Work.OddEnvelope.slopeRight c t₀))
    rw [hsl₀]
    exact hslope
  have hcomp : ContinuousAt (fun t : ℝ =>
      (fun σ : ℝ => σ * c σ + p σ) (Work.OddEnvelope.slopeRight c t)) t₀ :=
    hG.comp_of_eq hslope' hsl₀
  refine ContinuousAt.congr_of_eventuallyEq (g := Work.OddEnvelope.envelopeRight p c) hcomp ?_
  filter_upwards [eventually_slopeRight_realises hcont hanti hpos htail hσ₀ hcσ₀] with t ht
  rw [Work.OddEnvelope.envelopeRight, ht]

/-! ## The limits of the two branches at `0` -/

theorem tendsto_profileX_atTop : Tendsto Work.OddEnvelope.profileX atTop (𝓝 0) := by
  have hs : Tendsto (fun σ : ℝ => Real.sqrt (1 + σ ^ 2)) atTop atTop := by
    rw [tendsto_atTop]
    intro M
    filter_upwards [eventually_ge_atTop (max M 0)] with σ hσ
    rcases le_or_gt M 0 with h | h
    · exact le_trans h (Real.sqrt_nonneg _)
    · rw [Real.le_sqrt (by positivity) (by nlinarith [le_trans (le_max_right M 0) hσ, h])]
      nlinarith [le_trans (le_max_left M 0) hσ, h]
  have h := hs.inv_tendsto_atTop
  have hfun : Work.OddEnvelope.profileX = fun σ : ℝ => (Real.sqrt (1 + σ ^ 2))⁻¹ := by
    funext σ
    rw [Work.OddEnvelope.profileX, one_div]
  rw [hfun]
  exact h

/-- The left end of the perturbation window is below `1`. -/
theorem one_sub_tau_lt_one : (1 : ℝ) - Work.OddCurve.tau < 1 := by
  norm_num [Work.OddCurve.tau]

/-- A set of the form `(0, d)` belongs eventually to the filter `𝓝[>] 0`. -/
theorem eventually_lt_of_pos {d : ℝ} (hd : 0 < d) :
    ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < d := by
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Iio_mem_nhds hd] with t ht _
  exact ht

/-! ## The limits of the two branches at `0` -/

/-- **The right branch tends to `1` at the tip `t = 0⁺`.** -/
theorem tendsto_envelopeRight_zero {c p : ℝ → ℝ} (hcont : ContinuousOn c (Set.Ioi 0))
    (hanti : StrictAntiOn c (Set.Ioi 0)) (hpos : ∀ s : ℝ, 0 < s → 0 < c s)
    (htail : ∀ s : ℝ, 1 - Work.OddCurve.tau ≤ s → c s = Work.OddEnvelope.profileX s)
    (hzero : ∀ s : ℝ, 1 - Work.OddCurve.tau < s → p s = 0) :
    Tendsto (Work.OddEnvelope.envelopeRight p c) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  -- the inverse slope tends to `∞`
  have htop : Tendsto (fun t : ℝ => Work.OddEnvelope.slopeRight c t) (𝓝[>] (0 : ℝ)) atTop := by
    rw [tendsto_atTop]
    intro M
    rcases le_or_gt M 1 with hM | hM
    · filter_upwards [self_mem_nhdsWithin, eventually_lt_of_pos (hpos 1 one_pos)] with t ht0 ht1
      obtain ⟨σ, hσ1, hσpos, hcσ⟩ :=
        exists_slope_le_of_lt hcont hanti htail one_pos ht0 ht1.le
      rw [slopeRight_eq_of_lt hanti hσpos hcσ]
      linarith
    · filter_upwards [self_mem_nhdsWithin,
        eventually_lt_of_pos (hpos M (by linarith : 0 < M))] with t ht0 ht1
      obtain ⟨σ, hσ1, hσpos, hcσ⟩ :=
        exists_slope_le_of_lt hcont hanti htail (by linarith : 0 < M) ht0 ht1.le
      rw [slopeRight_eq_of_lt hanti hσpos hcσ]
      exact hσ1
  -- eventually the branch is the semicircle of the inverse slope
  have hev : (Work.OddEnvelope.envelopeRight p c) =ᶠ[𝓝[>] (0 : ℝ)]
      fun t => Work.OddEnvelope.semicircle (Work.OddEnvelope.profileX
        (Work.OddEnvelope.slopeRight c t)) := by
    filter_upwards [self_mem_nhdsWithin, eventually_lt_of_pos (hpos 1 one_pos)] with t ht0 ht1
    obtain ⟨σ, hσ1, hσpos, hcσ⟩ := exists_slope_le_of_lt hcont hanti htail one_pos ht0 ht1.le
    have hsl : Work.OddEnvelope.slopeRight c t = σ := slopeRight_eq_of_lt hanti hσpos hcσ
    have hge : 1 - Work.OddCurve.tau < σ := by linarith [one_sub_tau_lt_one, hσ1]
    rw [Work.OddEnvelope.envelopeRight, hsl, ← hcσ, hzero σ hge, add_zero, htail σ hge.le,
      Work.OddEnvelope.mul_profileX_eq_semicircle hσpos]
  refine Filter.Tendsto.congr' hev.symm ?_
  have hsemi : ContinuousAt Work.OddEnvelope.semicircle (0 : ℝ) := by
    have h : Work.OddEnvelope.semicircle = fun t : ℝ => Real.sqrt (1 - t ^ 2) := rfl
    rw [h]
    exact (Real.continuous_sqrt.comp (by fun_prop)).continuousAt
  have hlim : Tendsto (fun t : ℝ => Work.OddEnvelope.profileX (Work.OddEnvelope.slopeRight c t))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_profileX_atTop.comp htop
  have hsemi0 : Work.OddEnvelope.semicircle 0 = 1 := by
    simp [Work.OddEnvelope.semicircle]
  have hcomp := hsemi.tendsto.comp hlim
  rw [hsemi0] at hcomp
  simpa only [Function.comp_def] using hcomp

/-! ## The profile is continuous on a section of a smaller slope -/

/-- The untruncated profile on the right half-line is the right branch. -/
theorem envProfileFree_of_pos {h x y : ℝ → ℝ} {t : ℝ} (ht : 0 < t) :
    envProfileFree h x y t = Work.OddEnvelope.envelopeRight h y t := by
  rw [envProfileFree, if_pos ht]

/-- The untruncated profile on the left half-line is the left branch. -/
theorem envProfileFree_of_neg {h x y : ℝ → ℝ} {t : ℝ} (ht : t < 0) :
    envProfileFree h x y t = Work.OddEnvelope.envelopeLeft h x t := by
  rw [envProfileFree, if_neg (not_lt.mpr ht.le), if_pos ht]

/-- The untruncated profile at `0` is `1`. -/
theorem envProfileFree_zero {h x y : ℝ → ℝ} : envProfileFree h x y 0 = 1 := by
  rw [envProfileFree, if_neg (lt_irrefl 0), if_neg (lt_irrefl 0)]

/-- **Continuity of the untruncated envelope profile on `[-(x c), y c]`.** -/
theorem continuousOn_envProfileFree {h x y : ℝ → ℝ}
    (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) {c : ℝ} (hc : 0 < c) :
    ContinuousOn (envProfileFree h x y) (Set.Icc (-(x c)) (y c)) := by
  -- the right limit at `0`
  have hlim0 : Tendsto (envProfileFree h x y) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hbase := tendsto_envelopeRight_zero (c := y) (p := h) H.smooth_y.continuousOn
      H.strictAntiOn_y (fun s hs => H.pos_y hs) H.y_tail (fun s hs => H.h_eq_zero_of_gt hs)
    refine Filter.Tendsto.congr' ?_ hbase
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (envProfileFree_of_pos ht).symm
  -- the left limit at `0`
  have hlim0' : Tendsto (envProfileFree h x y) (𝓝[<] (0 : ℝ)) (𝓝 1) := by
    have hbase := tendsto_envelopeRight_zero (c := x) (p := Work.OddEnvelope.negH h)
      H.smooth_x.continuousOn H.strictAntiOn_x (fun s hs => H.pos_x hs) H.x_tail
      (fun s hs => by
        simp only [Work.OddEnvelope.negH]
        rw [H.h_eq_zero_of_gt hs, neg_zero])
    have hneg : Tendsto (fun t : ℝ => -t) (𝓝[<] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · simpa using ((continuous_neg : Continuous (fun t : ℝ => -t)).tendsto 0).mono_left
          nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact neg_pos.mpr (show t < 0 from ht)
    have hcomp := hbase.comp hneg
    refine Filter.Tendsto.congr' ?_ hcomp
    filter_upwards [self_mem_nhdsWithin] with t ht
    show Work.OddEnvelope.envelopeRight (Work.OddEnvelope.negH h) x (-t) = envProfileFree h x y t
    rw [envProfileFree_of_neg (show t < 0 from ht),
      ← Work.OddEnvelope.envelopeLeft_eq_negH h x t]
  rw [ContinuousOn]
  intro t ht
  rcases lt_trichotomy t 0 with hneg | heq | hpos
  · -- the left branch
    have htpos : 0 < -t := by linarith
    have hlec : -t ≤ x c := by linarith [ht.1]
    obtain ⟨σ, hsσ, hσpos, hxσ⟩ := H.exists_slope_x hc htpos hlec
    have hca : ContinuousAt (Work.OddEnvelope.envelopeLeft h x) t := by
      have hca' : ContinuousAt (Work.OddEnvelope.envelopeRight (Work.OddEnvelope.negH h) x) (-t) :=
        continuousAt_envelopeRight_of_eq (c := x) (p := Work.OddEnvelope.negH h)
          H.smooth_x.continuousOn H.strictAntiOn_x (fun s hs => H.pos_x hs) H.x_tail
          H.smooth_h.neg.continuousOn hσpos hxσ
      have hcomp : ContinuousAt
          (fun s : ℝ => Work.OddEnvelope.envelopeRight (Work.OddEnvelope.negH h) x (-s)) t :=
        hca'.comp (continuous_neg.continuousAt)
      refine ContinuousAt.congr_of_eventuallyEq (g := Work.OddEnvelope.envelopeLeft h x) hcomp ?_
      exact Eventually.of_forall fun s => Work.OddEnvelope.envelopeLeft_eq_negH h x s
    have hev : envProfileFree h x y =ᶠ[𝓝 t] Work.OddEnvelope.envelopeLeft h x := by
      filter_upwards [isOpen_Iio.mem_nhds hneg] with u hu
      exact envProfileFree_of_neg hu
    exact (ContinuousAt.congr_of_eventuallyEq (g := envProfileFree h x y) hca hev).continuousWithinAt
  · -- `t = 0`: both one-sided limits are `1`
    subst heq
    rw [Metric.continuousWithinAt_iff, envProfileFree_zero]
    have hR : ∀ ε > 0, ∃ δ > 0, ∀ u : ℝ, 0 < u → dist u 0 < δ →
        dist (envProfileFree h x y u) 1 < ε := by
      intro ε hε
      have h1 : Tendsto (envProfileFree h x y) (𝓝[>] (0 : ℝ))
          (𝓝 (envProfileFree h x y 0)) := by
        rw [envProfileFree_zero]; exact hlim0
      have h2 : ∀ᶠ u in 𝓝[>] (0 : ℝ), dist (envProfileFree h x y u) 1 < ε := by
        have := (Metric.tendsto_nhds.mp h1) ε hε
        rwa [envProfileFree_zero] at this
      rw [eventually_nhdsWithin_iff] at h2
      obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp h2
      exact ⟨δ, hδ, fun u hu0 huδ => hδ' huδ hu0⟩
    have hL : ∀ ε > 0, ∃ δ > 0, ∀ u : ℝ, u < 0 → dist u 0 < δ →
        dist (envProfileFree h x y u) 1 < ε := by
      intro ε hε
      have h1 : Tendsto (envProfileFree h x y) (𝓝[<] (0 : ℝ))
          (𝓝 (envProfileFree h x y 0)) := by
        rw [envProfileFree_zero]; exact hlim0'
      have h2 : ∀ᶠ u in 𝓝[<] (0 : ℝ), dist (envProfileFree h x y u) 1 < ε := by
        have := (Metric.tendsto_nhds.mp h1) ε hε
        rwa [envProfileFree_zero] at this
      rw [eventually_nhdsWithin_iff] at h2
      obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp h2
      exact ⟨δ, hδ, fun u hu0 huδ => hδ' huδ hu0⟩
    intro ε hε
    obtain ⟨δ₁, hδ₁, hδ₁'⟩ := hR ε hε
    obtain ⟨δ₂, hδ₂, hδ₂'⟩ := hL ε hε
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun u _ huδ => ?_⟩
    rcases lt_trichotomy u 0 with h | h | h
    · exact hδ₂' u h (lt_of_lt_of_le huδ (min_le_right _ _))
    · subst h
      rw [envProfileFree_zero, Real.dist_eq]
      simpa using hε
    · exact hδ₁' u h (lt_of_lt_of_le huδ (min_le_left _ _))
  · -- the right branch
    obtain ⟨σ, hsσ, hσpos, hyσ⟩ := H.exists_slope_y hc hpos ht.2
    have hca : ContinuousAt (Work.OddEnvelope.envelopeRight h y) t :=
      continuousAt_envelopeRight_of_eq H.smooth_y.continuousOn H.strictAntiOn_y
        (fun s hs => H.pos_y hs) H.y_tail H.smooth_h.continuousOn hσpos hyσ
    have hev : envProfileFree h x y =ᶠ[𝓝 t] Work.OddEnvelope.envelopeRight h y := by
      filter_upwards [isOpen_Ioi.mem_nhds hpos] with u hu
      exact envProfileFree_of_pos hu
    exact (ContinuousAt.congr_of_eventuallyEq (g := envProfileFree h x y) hca hev).continuousWithinAt

end

end Work.OddVolterra.Free
