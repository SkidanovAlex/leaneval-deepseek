import Mathlib
import Submission.Work.OddCurve.Free
import Submission.Work.OddEnvelope.ChordCurve

/-!
# Free chord curves: the inverse-slope API without the tip normalisation

`Work.OddEnvelope.IsChordCurve` is a smooth strictly decreasing `c : (0,∞) → (0,1)` with
`c σ → 1` as `σ → 0⁺` and `c = profileX` for `σ ≥ 1 - τ`.  The limit `1` is what makes `c` a
bijection onto `(0,1)` and `slopeRight c` its inverse on all of `(0,1)`.

For the free-tip envelope structure `Work.OddCurve.Free.IsEnvelopeCurveFree` the tip is only known
to be *some* positive number `b`, so the range of `c` is `(0,b)` and all the inverse-slope
statements must be phrased with `b` in place of `1`.  This file provides that API:

* `IsChordCurveFree c` — the structure (smooth, strictly decreasing, `c → b > 0` at `0⁺`, and
  `c = profileX` on `[1-τ, ∞)`), with `IsEnvelopeCurveFree.toChordCurveFree_x/_y`;
* strict antitonicity and injectivity on `(0,∞)`, positivity, and `c s < b`
  (`lt_of_tendsto_of_strictAntiOn_Ioi`);
* **surjectivity onto `(0, c s]`** (`exists_slope_of_mem_Ioc`) and onto `(0,b)`
  (`exists_slope_of_mem_Ioo`), both by the intermediate value theorem;
* the identification of `slopeRight c` with any positive preimage (`slopeRight_eq_of`);
* **continuity of `slopeRight c`** at every point of its range (`continuousAt_slopeRight`,
  by the monotone two-sided bracket) and hence on `(0,b)` (`continuousOn_slopeRight`), together
  with the left-branch version (`continuousOn_slopeLeft`).

Everything the free-tip re-plumbing of the odd case needs about the inverse slopes, with the tip
left free, is here.
-/

namespace Work.OddCurve.Free

noncomputable section

open Set Filter
open scoped Topology ContDiff

variable {c : ℝ → ℝ}

/-- **A free chord curve.**  A smooth function, strictly decreasing on `(0,∞)`, with a *positive
limit* `b` at `0⁺` (the tip, not required to be `1`) and equal to the semicircle's chord function
`profileX` for `σ ≥ 1 - τ`. -/
structure IsChordCurveFree (c : ℝ → ℝ) : Prop where
  /-- `c` is smooth on `(0,∞)`. -/
  smooth : ContDiffOn ℝ ∞ c (Set.Ioi 0)
  /-- `c` is strictly decreasing on `(0,∞)`. -/
  deriv_neg : ∀ s : ℝ, 0 < s → deriv c s < 0
  /-- `c` has a positive limit at `0⁺` (the tip). -/
  tendsto_free : ∃ b : ℝ, 0 < b ∧ Filter.Tendsto c (𝓝[>] (0 : ℝ)) (𝓝 b)
  /-- Beyond the perturbation window `c` is the semicircle's chord function. -/
  tail : ∀ s : ℝ, 1 - Work.OddEnvelope.tau ≤ s → c s = Work.OddEnvelope.profileX s

/-- The `x`-branch of a free envelope curve is a free chord curve. -/
theorem IsEnvelopeCurveFree.toChordCurveFree_x {h x y : ℝ → ℝ} (H : IsEnvelopeCurveFree h x y) :
    IsChordCurveFree x where
  smooth := H.smooth_x
  deriv_neg := H.x_deriv_neg
  tendsto_free := H.x_tendsto_free
  tail := H.x_tail

/-- The `y`-branch of a free envelope curve is a free chord curve. -/
theorem IsEnvelopeCurveFree.toChordCurveFree_y {h x y : ℝ → ℝ} (H : IsEnvelopeCurveFree h x y) :
    IsChordCurveFree y where
  smooth := H.smooth_y
  deriv_neg := H.y_deriv_neg
  tendsto_free := H.y_tendsto_free
  tail := H.y_tail

/-! ## Basic order facts -/

lemma IsChordCurveFree.strictAntiOn (hc : IsChordCurveFree c) : StrictAntiOn c (Set.Ioi 0) :=
  strictAntiOn_of_deriv_neg (convex_Ioi 0) hc.smooth.continuousOn (by
    intro s hs
    rw [interior_Ioi] at hs
    exact hc.deriv_neg s hs)

lemma IsChordCurveFree.injOn (hc : IsChordCurveFree c) : Set.InjOn c (Set.Ioi 0) :=
  hc.strictAntiOn.injOn

/-- A free chord curve is positive: it is `profileX` on the tail and strictly above `profileX` on
the transition, and `profileX > 0`. -/
lemma IsChordCurveFree.pos (hc : IsChordCurveFree c) {s : ℝ} (hs : 0 < s) : 0 < c s := by
  rcases lt_trichotomy s (1 - Work.OddEnvelope.tau) with hlt | heq | hgt
  · have h₁ : c (1 - Work.OddEnvelope.tau) < c s :=
      hc.strictAntiOn hs Work.OddEnvelope.one_sub_tau_pos hlt
    rw [hc.tail (1 - Work.OddEnvelope.tau) le_rfl] at h₁
    exact lt_trans (Work.OddEnvelope.profileX_pos _) h₁
  · rw [heq, hc.tail (1 - Work.OddEnvelope.tau) le_rfl]
    exact Work.OddEnvelope.profileX_pos _
  · rw [hc.tail s hgt.le]
    exact Work.OddEnvelope.profileX_pos s

/-- The tip is a strict upper bound for the curve. -/
lemma IsChordCurveFree.lt_tip (hc : IsChordCurveFree c) {b : ℝ}
    (hb : Filter.Tendsto c (𝓝[>] (0 : ℝ)) (𝓝 b)) {s : ℝ} (hs : 0 < s) : c s < b :=
  Work.OddEnvelope.lt_of_tendsto_of_strictAntiOn_Ioi hc.strictAntiOn hb s hs

/-- `profileX σ < 1/σ` for `σ > 0`. -/
lemma profileX_lt_inv {σ : ℝ} (hσ : 0 < σ) : Work.OddEnvelope.profileX σ < 1 / σ := by
  have hsqrt : σ < Real.sqrt (1 + σ ^ 2) := by
    rw [Real.lt_sqrt (by positivity)]
    nlinarith
  have h := one_div_lt_one_div_of_lt hσ hsqrt
  simpa [Work.OddEnvelope.profileX] using h

/-! ## Surjectivity of a free chord curve -/

/-- **A slope past any given one at which `c` is already below `t`.**  This is the tail fact the
free-tip surjectivity arguments rest on: `c = profileX` beyond `1 - τ` and `profileX σ < 1/σ`. -/
lemma IsChordCurveFree.exists_le_slope_lt (hc : IsChordCurveFree c) {s t : ℝ} (hs : 0 < s)
    (ht : 0 < t) : ∃ S : ℝ, s ≤ S ∧ 1 - Work.OddEnvelope.tau ≤ S ∧ c S < t := by
  set M : ℝ := max (max s (1 - Work.OddEnvelope.tau)) (1 / t) with hM
  have hsM : s ≤ M := le_trans (le_max_left s _) (le_max_left _ _)
  have hτM : 1 - Work.OddEnvelope.tau ≤ M := le_trans (le_max_right s _) (le_max_left _ _)
  have hinvM : 1 / t < M + 1 := by
    have h : 1 / t ≤ M := le_max_right _ _
    linarith
  refine ⟨M + 1, by linarith, by linarith, ?_⟩
  have hpos : 0 < M + 1 := by linarith [one_div_pos.mpr ht]
  have h1 : Work.OddEnvelope.profileX (M + 1) < 1 / (M + 1) := profileX_lt_inv hpos
  have h2 : 1 / (M + 1) < t := by
    have h3 := one_div_lt_one_div_of_lt (one_div_pos.mpr ht) hinvM
    simpa [one_div] using h3
  rw [hc.tail (M + 1) (by linarith)]
  linarith

/-- **Surjectivity onto `(0, c s]`.**  Every `t` with `0 < t ≤ c s` is the value of `c` at some
slope `σ ≥ s`.  This is the free-tip replacement for `IsChordCurve.surj`. -/
lemma IsChordCurveFree.exists_slope_of_mem_Ioc (hc : IsChordCurveFree c) {s t : ℝ}
    (hs : 0 < s) (ht0 : 0 < t) (hts : t ≤ c s) : ∃ σ : ℝ, s ≤ σ ∧ 0 < σ ∧ c σ = t := by
  rcases lt_or_eq_of_le hts with hlt | heq
  · obtain ⟨S, hsS, hSτ, hcS⟩ := hc.exists_le_slope_lt hs ht0
    have hcont : ContinuousOn c (Set.Icc s S) :=
      hc.smooth.continuousOn.mono (fun x hx => lt_of_lt_of_le hs hx.1)
    have hsub := intermediate_value_Icc' hsS hcont
    have htmem : t ∈ Set.Icc (c S) (c s) := ⟨hcS.le, hlt.le⟩
    obtain ⟨σ, hσmem, hσeq⟩ := hsub htmem
    exact ⟨σ, hσmem.1, lt_of_lt_of_le hs hσmem.1, hσeq⟩
  · exact ⟨s, le_rfl, hs, heq.symm⟩

/-- **Surjectivity onto the whole range `(0, b)`.** -/
lemma IsChordCurveFree.exists_slope_of_mem_Ioo (hc : IsChordCurveFree c) {b : ℝ}
    (hb : Filter.Tendsto c (𝓝[>] (0 : ℝ)) (𝓝 b)) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) b) :
    ∃ σ : ℝ, 0 < σ ∧ c σ = t := by
  obtain ⟨σ₁, hσ₁pos, hσ₁⟩ : ∃ σ₁ : ℝ, 0 < σ₁ ∧ t < c σ₁ := by
    have hsmall : ∀ᶠ σ in 𝓝[>] (0 : ℝ), t < c σ :=
      hb.eventually (Ioi_mem_nhds ht.2)
    obtain ⟨σ₁, h₁, h₂⟩ := (hsmall.and self_mem_nhdsWithin).exists
    exact ⟨σ₁, h₂, h₁⟩
  obtain ⟨σ₂, hσ₁σ₂, hσ₂⟩ : ∃ σ₂ : ℝ, σ₁ ≤ σ₂ ∧ c σ₂ < t := by
    obtain ⟨S, hσ₁S, _, hcS⟩ := hc.exists_le_slope_lt hσ₁pos ht.1
    exact ⟨S, hσ₁S, hcS⟩
  have hcont : ContinuousOn c (Set.Icc σ₁ σ₂) :=
    hc.smooth.continuousOn.mono (fun x hx => lt_of_lt_of_le hσ₁pos hx.1)
  have hsub := intermediate_value_Icc' hσ₁σ₂ hcont
  have htmem : t ∈ Set.Icc (c σ₂) (c σ₁) := ⟨hσ₂.le, hσ₁.le⟩
  obtain ⟨σ, hσmem, hσeq⟩ := hsub htmem
  exact ⟨σ, lt_of_lt_of_le hσ₁pos hσmem.1, hσeq⟩

/-! ## `slopeRight` of a free chord curve -/

/-- Any positive preimage of `t` under `c` *is* `slopeRight c t`. -/
lemma IsChordCurveFree.slopeRight_eq_of (hc : IsChordCurveFree c) {σ t : ℝ} (hσ : 0 < σ)
    (h : c σ = t) : Work.OddEnvelope.slopeRight c t = σ := by
  have h' : Work.OddEnvelope.slopeRight c (c σ) = σ := by
    simpa [Work.OddEnvelope.slopeRight] using hc.injOn.leftInvOn_invFunOn hσ
  rwa [h] at h'

/-! ## The inverse slope at a point of the range -/

/-- The inverse slope of `t ∈ (0,b)` is a genuine preimage of `t`. -/
lemma IsChordCurveFree.slopeRight_mem (hc : IsChordCurveFree c) {b t : ℝ}
    (hb : Filter.Tendsto c (𝓝[>] (0 : ℝ)) (𝓝 b)) (ht : t ∈ Set.Ioo (0 : ℝ) b) :
    Work.OddEnvelope.slopeRight c t ∈ Set.Ioi 0 ∧ c (Work.OddEnvelope.slopeRight c t) = t := by
  obtain ⟨σ, hσ, hσt⟩ := hc.exists_slope_of_mem_Ioo hb ht
  have h1 : Work.OddEnvelope.slopeRight c t = σ := hc.slopeRight_eq_of hσ hσt
  rw [h1]
  exact ⟨hσ, hσt⟩

lemma IsChordCurveFree.slopeRight_pos (hc : IsChordCurveFree c) {b t : ℝ}
    (hb : Filter.Tendsto c (𝓝[>] (0 : ℝ)) (𝓝 b)) (ht : t ∈ Set.Ioo (0 : ℝ) b) :
    0 < Work.OddEnvelope.slopeRight c t := (hc.slopeRight_mem hb ht).1

lemma IsChordCurveFree.slopeRight_eq (hc : IsChordCurveFree c) {b t : ℝ}
    (hb : Filter.Tendsto c (𝓝[>] (0 : ℝ)) (𝓝 b)) (ht : t ∈ Set.Ioo (0 : ℝ) b) :
    c (Work.OddEnvelope.slopeRight c t) = t := (hc.slopeRight_mem hb ht).2

lemma IsChordCurveFree.slopeLeft_pos (hc : IsChordCurveFree c) {b t : ℝ}
    (hb : Filter.Tendsto c (𝓝[>] (0 : ℝ)) (𝓝 b)) (ht : t ∈ Set.Ioo (-b) 0) :
    0 < Work.OddEnvelope.slopeLeft c t := by
  obtain ⟨σ, hσ, hcσ⟩ := hc.exists_slope_of_mem_Ioo hb
    (show -t ∈ Set.Ioo (0 : ℝ) b from ⟨by linarith [ht.2], by linarith [ht.1]⟩)
  have h1 : Work.OddEnvelope.slopeRight c (-t) = σ := hc.slopeRight_eq_of hσ hcσ
  show 0 < Work.OddEnvelope.slopeRight c (-t)
  rw [h1]
  exact hσ

/-! ## Continuity of `slopeRight` -/

/-- **`slopeRight c` is continuous at every point of the range of `c`.**  Two-sided bracket
argument: if `σ₀ - e` and `σ₀ + e` are both positive then every point of the open interval
`(c (σ₀+e), c (σ₀-e))` is the image of some slope in `(σ₀-e, σ₀+e)`; so near `c σ₀` the inverse
slope stays within `e` of `σ₀`. -/
lemma IsChordCurveFree.continuousAt_slopeRight (hc : IsChordCurveFree c) {σ₀ : ℝ}
    (hσ₀ : 0 < σ₀) : ContinuousAt (Work.OddEnvelope.slopeRight c) (c σ₀) := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  set e : ℝ := min (ε / 2) (σ₀ / 2) with he
  have he_pos : 0 < e := lt_min (by linarith) (by linarith)
  have he_le : e ≤ ε / 2 := min_le_left _ _
  have he_lt_ε : e < ε := by linarith
  have he_le' : e ≤ σ₀ / 2 := min_le_right _ _
  have hσ₁pos : 0 < σ₀ - e := by linarith
  have hσ₂pos : 0 < σ₀ + e := by linarith
  have hlow : c (σ₀ + e) < c σ₀ := hc.strictAntiOn hσ₀ hσ₂pos (by linarith)
  have hhigh : c σ₀ < c (σ₀ - e) := hc.strictAntiOn hσ₁pos hσ₀ (by linarith)
  refine ⟨min (c σ₀ - c (σ₀ + e)) (c (σ₀ - e) - c σ₀),
    lt_min (by linarith) (by linarith), ?_⟩
  intro t ht
  rw [Real.dist_eq] at ht ⊢
  have htlow : c (σ₀ + e) < t := by
    have h1 : |t - c σ₀| < c σ₀ - c (σ₀ + e) := lt_of_lt_of_le ht (min_le_left _ _)
    have := (abs_lt.mp h1).1
    linarith
  have hthigh : t < c (σ₀ - e) := by
    have h2 : |t - c σ₀| < c (σ₀ - e) - c σ₀ := lt_of_lt_of_le ht (min_le_right _ _)
    have := (abs_lt.mp h2).2
    linarith
  have hcont : ContinuousOn c (Set.Icc (σ₀ - e) (σ₀ + e)) :=
    hc.smooth.continuousOn.mono (fun x hx => lt_of_lt_of_le hσ₁pos hx.1)
  have hsub := intermediate_value_Icc' (by linarith : σ₀ - e ≤ σ₀ + e) hcont
  have htmem : t ∈ Set.Icc (c (σ₀ + e)) (c (σ₀ - e)) := ⟨htlow.le, hthigh.le⟩
  obtain ⟨σ, hσmem, hσeq⟩ := hsub htmem
  have hσpos : 0 < σ := lt_of_lt_of_le hσ₁pos hσmem.1
  have h1 : Work.OddEnvelope.slopeRight c t = σ := hc.slopeRight_eq_of hσpos hσeq
  have h2 : Work.OddEnvelope.slopeRight c (c σ₀) = σ₀ := hc.slopeRight_eq_of hσ₀ rfl
  rw [h1, h2]
  rw [abs_lt]
  constructor <;> linarith [hσmem.1, hσmem.2]

/-- `slopeRight c` is continuous on the range `(0,b)` of `c`. -/
lemma IsChordCurveFree.continuousOn_slopeRight (hc : IsChordCurveFree c) {b : ℝ}
    (hb : Filter.Tendsto c (𝓝[>] (0 : ℝ)) (𝓝 b)) :
    ContinuousOn (Work.OddEnvelope.slopeRight c) (Set.Ioo (0 : ℝ) b) := by
  rw [isOpen_Ioo.continuousOn_iff]
  intro t ht
  obtain ⟨σ, hσ, hσt⟩ := hc.exists_slope_of_mem_Ioo hb ht
  rw [← hσt]
  exact hc.continuousAt_slopeRight hσ

/-- `slopeLeft x t = slopeRight x (-t)`, so it is continuous on `(-b, 0)` whenever `slopeRight x`
is continuous on `(0,b)`. -/
lemma IsChordCurveFree.continuousOn_slopeLeft (hc : IsChordCurveFree c) {b : ℝ}
    (hb : Filter.Tendsto c (𝓝[>] (0 : ℝ)) (𝓝 b)) :
    ContinuousOn (Work.OddEnvelope.slopeLeft c) (Set.Ioo (-b) 0) := by
  have hneg : ContinuousOn (fun t : ℝ => -t) (Set.Ioo (-b) (0 : ℝ)) := continuous_neg.continuousOn
  have hmaps : MapsTo (fun t : ℝ => -t) (Set.Ioo (-b) (0 : ℝ)) (Set.Ioo (0 : ℝ) b) :=
    fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hcomp := (hc.continuousOn_slopeRight hb).comp hneg hmaps
  refine hcomp.congr ?_
  intro t _
  simp only [Work.OddEnvelope.slopeLeft, Work.OddEnvelope.slopeRight, Function.comp_apply]

end

end Work.OddCurve.Free
