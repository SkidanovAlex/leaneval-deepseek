import Mathlib
import Submission.Work.Drive.blurSlicesScheduled
import Submission.Work.Drive.chamferJunctionDefs
import Submission.Work.Drive.chamferLoopGenBlur
import Submission.Work.Drive.sweepFamOfSlicesOfCone
import Submission.Work.Drive.schedContinuity
import Submission.Work.Drive.cornerSignSplit

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-! ## Private copy of the local-cone helpers

The proof below uses its own copy of the auxiliary lemmas of the local-cone development (namespace `ScAux`), so that it does not depend on the `sorry` of the pin module. -/

namespace ScAux

open LeanEval.KnotTheory.Quadrisecant




/-! ## Elementary helpers -/

/-- `clampI` is continuous (`r` is evaluated along the clamped branch lifts). -/
lemma continuous_clampI_lc : Continuous (fun x : ℝ => (clampI x : Set.Icc (0 : ℝ) 1)) := by
  unfold clampI
  fun_prop

lemma continuous_taR_lc {d : BandArcData} (D : SweepData d) : Continuous (taR D) :=
  D.cont_ta.comp continuous_clampI_lc

lemma continuous_tbR_lc {d : BandArcData} (D : SweepData d) : Continuous (tbR D) :=
  D.cont_tb.comp continuous_clampI_lc

lemma continuous_sweepW'_lc {d : BandArcData} (D : SweepData d) : Continuous (sweepW' D) :=
  (continuous_tbR_lc D).sub (continuous_taR_lc D)

/-- **Slacked monotonicity of the `n`-coordinate of the knot.**  If `ν ≤ ⟪n, r'⟫` on `[a,b]`, then
`ν (y - x) ≤ ⟪n, r y - r x⟫` for `a ≤ x ≤ y ≤ b`. -/
lemma inner_knot_slack_lc {r : ℝ → Space} (hr : IsSmoothKnot r) {n : Space} {a b ν : ℝ}
    (h : ∀ x ∈ Set.Icc a b, ν ≤ inner ℝ n (deriv r x)) :
    ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, x ≤ y → ν * (y - x) ≤ inner ℝ n (r y - r x) := by
  have hcont : ContinuousOn (fun x : ℝ => inner ℝ n (r x) - ν * x) (Set.Icc a b) :=
    ((continuous_const.inner hr.smooth.continuous).sub
      (continuous_const.mul continuous_id)).continuousOn
  have hdiff : DifferentiableOn ℝ (fun x : ℝ => inner ℝ n (r x) - ν * x)
      (interior (Set.Icc a b)) := by
    intro x hx
    exact ((((hasDerivAt_const x n).inner ℝ
      ((hr.smooth.differentiable (by simp) x).hasDerivAt)).sub
      ((hasDerivAt_id x).const_mul ν)).differentiableAt).differentiableWithinAt
  have hder : ∀ x ∈ interior (Set.Icc a b),
      0 ≤ deriv (fun x : ℝ => inner ℝ n (r x) - ν * x) x := by
    intro x hx
    have h1 : HasDerivAt (fun x : ℝ => inner ℝ n (r x)) (inner ℝ n (deriv r x)) x := by
      simpa using (hasDerivAt_const x n).inner ℝ
        ((hr.smooth.differentiable (by simp) x).hasDerivAt)
    have h2 : HasDerivAt (fun x : ℝ => ν * x) (ν * 1) x := (hasDerivAt_id x).const_mul ν
    have h3 : deriv ((fun x : ℝ => inner ℝ n (r x)) - (fun x : ℝ => ν * x)) x
        = inner ℝ n (deriv r x) - ν := by
      have := (h1.sub h2).deriv
      simpa only [mul_one] using this
    change 0 ≤ deriv ((fun x : ℝ => inner ℝ n (r x)) - (fun x : ℝ => ν * x)) x
    rw [h3]
    have := h x (interior_subset hx)
    linarith
  have hmono := monotoneOn_of_deriv_nonneg (convex_Icc a b) hcont hdiff hder
  intro x hx y hy hxy
  have hle := hmono hx hy hxy
  simp only [Pi.sub_apply] at hle
  rw [inner_sub_right]
  nlinarith [hle]

/-- Differences of points of the chord are multiples of the chord vector. -/
lemma sweepChord'_sub_lc {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    (s ξ₁ ξ₂ : ℝ) :
    sweepChord' r D s ξ₂ - sweepChord' r D s ξ₁ = (ξ₂ - ξ₁) • (r (tbR D s) - r (taR D s)) := by
  simp only [sweepChord']
  module

/-- The increment of an affine interpolation. -/
lemma smul_interp_sub_lc (A C : Space) (t₁ t₂ : ℝ) :
    ((1 - t₂) • A + t₂ • C) - ((1 - t₁) • A + t₁ • C) = (t₂ - t₁) • (C - A) := by
  module

/-! ## The branches of the scheduled profile on their closed intervals -/

lemma prof_eq_arc {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {lay a b s u : ℝ}
    (hu : u ≤ 1 / 2) :
    chamferLoopProf r D lay a b s u = sweepArc' r D s (a + (1 - 2 * a) * (2 * u)) := by
  simp only [chamferLoopProf, if_pos hu]

lemma prof_eq_ch1 {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {lay a b s u : ℝ}
    (h1 : 1 / 2 ≤ u) (h2 : u ≤ 1 / 2 + lay / 2) :
    chamferLoopProf r D lay a b s u
      = (1 - (2 * u - 1) / lay) • sweepArc' r D s (1 - a)
        + ((2 * u - 1) / lay) • sweepChord' r D s (1 - b) := by
  rcases eq_or_lt_of_le h1 with h | h
  · subst h
    rw [prof_eq_arc D (le_refl (1 / 2 : ℝ))]
    have h1' : a + (1 - 2 * a) * (2 * ((1 : ℝ) / 2)) = 1 - a := by ring
    have h2' : (2 * ((1 : ℝ) / 2) - 1) / lay = 0 := by simp
    rw [h1', h2']
    simp
  · simp only [chamferLoopProf, if_neg (not_le.mpr h), if_pos h2]

lemma prof_eq_chord {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {lay a b s u : ℝ}
    (hl0 : 0 < lay) (hl1 : lay < 1 / 2)
    (h1 : 1 / 2 + lay / 2 ≤ u) (h2 : u ≤ 1 - lay / 2) :
    chamferLoopProf r D lay a b s u
      = sweepChord' r D s ((1 - b) - ((u - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * b)) := by
  rcases eq_or_lt_of_le h1 with h | h
  · subst h
    simp only [chamferLoopProf, if_neg (not_le.mpr (by linarith : (1 : ℝ) / 2 < 1 / 2 + lay / 2)),
      if_pos le_rfl]
    have hq : (2 * ((1 : ℝ) / 2 + lay / 2) - 1) / lay = 1 := by
      rw [div_eq_iff (ne_of_gt hl0)]
      ring
    rw [hq]
    have h0 : (((1 : ℝ) / 2 + lay / 2) - (1 / 2 + lay / 2)) / (1 / 2 - lay) = 0 := by simp
    rw [h0]
    simp
  · simp only [chamferLoopProf, if_neg (not_le.mpr (by linarith : (1 : ℝ) / 2 < u)),
      if_neg (not_le.mpr h), if_pos h2]

lemma prof_eq_cham2 {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {lay a b s u : ℝ}
    (hl0 : 0 < lay) (hl1 : lay < 1 / 2) (h : 1 - lay / 2 ≤ u) :
    chamferLoopProf r D lay a b s u
      = (1 - (u - (1 - lay / 2)) / (lay / 2)) • sweepChord' r D s b
        + ((u - (1 - lay / 2)) / (lay / 2)) • sweepArc' r D s a := by
  rcases eq_or_lt_of_le h with h | h
  · subst h
    simp only [chamferLoopProf, if_neg (not_le.mpr (by linarith : (1 : ℝ) / 2 < 1 - lay / 2)),
      if_neg (not_le.mpr (by linarith : (1 : ℝ) / 2 + lay / 2 < 1 - lay / 2)), if_pos le_rfl]
    have hq : (((1 : ℝ) - lay / 2) - (1 / 2 + lay / 2)) / (1 / 2 - lay) = 1 := by
      rw [div_eq_one_iff_eq (by linarith : ((1 : ℝ) / 2 - lay) ≠ 0)]
      ring
    rw [hq, one_mul]
    have hX : (1 - b) - (1 - 2 * b) = b := by ring
    rw [hX]
    have hq2 : (((1 : ℝ) - lay / 2) - (1 - lay / 2)) / (lay / 2) = 0 := by simp
    rw [hq2]
    simp
  · simp only [chamferLoopProf, if_neg (not_le.mpr (by linarith : (1 : ℝ) / 2 < u)),
      if_neg (not_le.mpr (by linarith : (1 : ℝ) / 2 + lay / 2 < u)), if_neg (not_le.mpr h)]

/-! ## The four piece-growth lemmas -/

/-- **Arc piece.** -/
theorem growth_arc_branch {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) {lay a b σ W₁ W₂ dd : ℝ} {n : Space}
    (ha : 2 * a < 1) (hW : 0 < sweepW' D σ)
    (harc : ∀ u ∈ Set.Icc W₁ W₂, dd ≤ ((1 - 2 * a) * (2 * sweepW' D σ))
        * inner ℝ n (deriv r (taR D σ + (a + (1 - 2 * a) * (2 * u)) * sweepW' D σ))) :
    ∀ u v : ℝ, W₁ ≤ u → u ≤ v → v ≤ min W₂ (1 / 2) →
      dd * (v - u) ≤ inner ℝ n (chamferLoopProf r D lay a b σ v
        - chamferLoopProf r D lay a b σ u) := by
  intro u v hu huv hv
  have hv1 : v ≤ 1 / 2 := le_trans hv (min_le_right _ _)
  have hu1 : u ≤ 1 / 2 := le_trans huv hv1
  have hv2 : v ≤ W₂ := le_trans hv (min_le_left _ _)
  rw [prof_eq_arc D hu1, prof_eq_arc D hv1]
  simp only [sweepArc']
  set m : ℝ := (1 - 2 * a) * (2 * sweepW' D σ) with hm
  have hmpos : 0 < m := by
    rw [hm]
    nlinarith [hW]
  have hx : ∀ w : ℝ, taR D σ + (a + (1 - 2 * a) * (2 * w)) * sweepW' D σ
      = (taR D σ + a * sweepW' D σ) + m * w := by
    intro w
    rw [hm]
    ring
  set x₁ : ℝ := (taR D σ + a * sweepW' D σ) + m * u with hx₁
  set x₂ : ℝ := (taR D σ + a * sweepW' D σ) + m * v with hx₂
  have hxle : x₁ ≤ x₂ := by
    rw [hx₁, hx₂]
    nlinarith [hmpos, huv]
  have hx1eq : taR D σ + (a + (1 - 2 * a) * (2 * u)) * sweepW' D σ = x₁ := by
    rw [hx u, hx₁]
  have hx2eq : taR D σ + (a + (1 - 2 * a) * (2 * v)) * sweepW' D σ = x₂ := by
    rw [hx v, hx₂]
  have hbound : ∀ x ∈ Set.Icc x₁ x₂, dd / m ≤ inner ℝ n (deriv r x) := by
    intro x hxmem
    obtain ⟨hxl, hxr⟩ := hxmem
    set w : ℝ := u + (x - x₁) / m with hw
    have hxw : (taR D σ + a * sweepW' D σ) + m * w = x := by
      rw [hw, hx₁]
      field_simp
      ring
    have hw1 : W₁ ≤ w := by
      rw [hw]
      have h0 : 0 ≤ (x - x₁) / m := div_nonneg (by linarith) hmpos.le
      linarith
    have hw2 : w ≤ W₂ := by
      have hvu : m * (v - u) = x₂ - x₁ := by
        rw [hx₁, hx₂]; ring
      have hdiv : (x - x₁) / m ≤ v - u := by
        rw [div_le_iff₀ hmpos]
        nlinarith [hxr]
      rw [hw]
      linarith
    have h := harc w ⟨hw1, hw2⟩
    have hxw' : taR D σ + (a + (1 - 2 * a) * (2 * w)) * sweepW' D σ = x := by
      rw [hx w]
      exact hxw
    rw [hxw'] at h
    rw [div_le_iff₀ hmpos]
    linarith [h, mul_comm m (inner ℝ n (deriv r x))]
  have hslack := inner_knot_slack_lc hr hbound x₁ ⟨le_rfl, hxle⟩ x₂ ⟨hxle, le_rfl⟩ hxle
  have hx21 : x₂ - x₁ = m * (v - u) := by
    rw [hx₁, hx₂]; ring
  rw [hx21] at hslack
  have hsimp : dd / m * (m * (v - u)) = dd * (v - u) := by
    rw [show dd / m * (m * (v - u)) = (dd * (v - u) * m) / m by ring]
    exact mul_div_cancel_right₀ (dd * (v - u)) (ne_of_gt hmpos)
  rw [hsimp] at hslack
  rwa [hx1eq, hx2eq]

/-- **First chamfer piece.** -/
theorem growth_ch1_branch {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lay a b σ W₁ W₂ dd : ℝ} {n : Space} (hl0 : 0 < lay)
    (hU : dd ≤ (2 / lay) * inner ℝ n (sweepChord' r D σ (1 - b) - sweepArc' r D σ (1 - a))) :
    ∀ u v : ℝ, max W₁ (1 / 2) ≤ u → u ≤ v → v ≤ min W₂ (1 / 2 + lay / 2) →
      dd * (v - u) ≤ inner ℝ n (chamferLoopProf r D lay a b σ v
        - chamferLoopProf r D lay a b σ u) := by
  intro u v hu huv hv
  have hu1 : (1 : ℝ) / 2 ≤ u := le_trans (le_max_right _ _) hu
  have hv1 : v ≤ 1 / 2 + lay / 2 := le_trans hv (min_le_right _ _)
  have hv2 : (1 : ℝ) / 2 ≤ v := le_trans hu1 huv
  rw [prof_eq_ch1 D hv2 hv1, prof_eq_ch1 D hu1 (le_trans huv hv1)]
  rw [smul_interp_sub_lc]
  rw [inner_smul_right]
  have hval : (2 * v - 1) / lay - (2 * u - 1) / lay = (v - u) * (2 / lay) := by
    rw [← div_sub_div_same]
    field_simp
    ring
  rw [hval]
  have hstep := mul_le_mul_of_nonneg_left hU (by linarith : (0 : ℝ) ≤ v - u)
  calc dd * (v - u) = (v - u) * dd := by ring
    _ ≤ (v - u) * ((2 / lay)
          * inner ℝ n (sweepChord' r D σ (1 - b) - sweepArc' r D σ (1 - a))) := hstep
    _ = (v - u) * (2 / lay)
          * inner ℝ n (sweepChord' r D σ (1 - b) - sweepArc' r D σ (1 - a)) := by ring

/-- **Chord piece** (traversed backwards). -/
theorem growth_chord_branch {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lay a b σ W₁ W₂ dd : ℝ} {n : Space} (hl0 : 0 < lay) (hl1 : lay < 1 / 2)
    (hV : dd ≤ ((1 - 2 * b) / (1 / 2 - lay)) * inner ℝ n (r (taR D σ) - r (tbR D σ))) :
    ∀ u v : ℝ, max W₁ (1 / 2 + lay / 2) ≤ u → u ≤ v → v ≤ min W₂ (1 - lay / 2) →
      dd * (v - u) ≤ inner ℝ n (chamferLoopProf r D lay a b σ v
        - chamferLoopProf r D lay a b σ u) := by
  intro u v hu huv hv
  have hu1 : (1 : ℝ) / 2 + lay / 2 ≤ u := le_trans (le_max_right _ _) hu
  have hv1 : v ≤ 1 - lay / 2 := le_trans hv (min_le_right _ _)
  have hv2 : (1 : ℝ) / 2 + lay / 2 ≤ v := le_trans hu1 huv
  rw [prof_eq_chord D hl0 hl1 hv2 hv1, prof_eq_chord D hl0 hl1 hu1 (le_trans huv hv1)]
  rw [sweepChord'_sub_lc, inner_smul_right]
  have hξ : ((1 - b) - ((v - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * b))
      - ((1 - b) - ((u - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * b))
      = -((v - u) * ((1 - 2 * b) / (1 / 2 - lay))) := by
    rw [← div_sub_div_same]
    field_simp
    ring
  rw [hξ]
  have hneg : inner ℝ n (r (tbR D σ) - r (taR D σ))
      = - inner ℝ n (r (taR D σ) - r (tbR D σ)) := by
    rw [← inner_neg_right, neg_sub]
  have hkey : -((v - u) * ((1 - 2 * b) / (1 / 2 - lay)))
        * inner ℝ n (r (tbR D σ) - r (taR D σ))
      = (v - u) * (((1 - 2 * b) / (1 / 2 - lay))
          * inner ℝ n (r (taR D σ) - r (tbR D σ))) := by
    rw [hneg]
    ring
  rw [hkey]
  have hstep := mul_le_mul_of_nonneg_left hV (by linarith : (0 : ℝ) ≤ v - u)
  calc dd * (v - u) = (v - u) * dd := by ring
    _ ≤ (v - u) * (((1 - 2 * b) / (1 / 2 - lay))
          * inner ℝ n (r (taR D σ) - r (tbR D σ))) := hstep
    _ = (v - u) * (((1 - 2 * b) / (1 / 2 - lay))
          * inner ℝ n (r (taR D σ) - r (tbR D σ))) := by ring

/-- **Second chamfer piece.** -/
theorem growth_cham2_branch {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lay a b σ W₁ W₂ dd : ℝ} {n : Space} (hl0 : 0 < lay) (hl1 : lay < 1 / 2)
    (hU : dd ≤ (2 / lay) * inner ℝ n (sweepArc' r D σ a - sweepChord' r D σ b)) :
    ∀ u v : ℝ, max W₁ (1 - lay / 2) ≤ u → u ≤ v → v ≤ W₂ →
      dd * (v - u) ≤ inner ℝ n (chamferLoopProf r D lay a b σ v
        - chamferLoopProf r D lay a b σ u) := by
  intro u v hu huv hv
  have hu1 : 1 - lay / 2 ≤ u := le_trans (le_max_right _ _) hu
  have hv1 : 1 - lay / 2 ≤ v := le_trans hu1 huv
  rw [prof_eq_cham2 D hl0 hl1 hv1, prof_eq_cham2 D hl0 hl1 hu1]
  rw [smul_interp_sub_lc]
  rw [inner_smul_right]
  have hval : (v - (1 - lay / 2)) / (lay / 2) - (u - (1 - lay / 2)) / (lay / 2)
      = (v - u) * (2 / lay) := by
    rw [← div_sub_div_same]
    field_simp
    ring
  rw [hval]
  have hstep := mul_le_mul_of_nonneg_left hU (by linarith : (0 : ℝ) ≤ v - u)
  calc dd * (v - u) = (v - u) * dd := by ring
    _ ≤ (v - u) * ((2 / lay) * inner ℝ n (sweepArc' r D σ a - sweepChord' r D σ b)) := hstep
    _ = (v - u) * (2 / lay)
          * inner ℝ n (sweepArc' r D σ a - sweepChord' r D σ b) := by ring

/-- **Gluing two rate-monotone pieces.** -/
theorem growth_glue {F : ℝ → Space} {n : Space} {dd α β γ : ℝ}
    (h1 : ∀ u v : ℝ, α ≤ u → u ≤ v → v ≤ β → dd * (v - u) ≤ inner ℝ n (F v - F u))
    (h2 : ∀ u v : ℝ, β ≤ u → u ≤ v → v ≤ γ → dd * (v - u) ≤ inner ℝ n (F v - F u)) :
    ∀ u v : ℝ, α ≤ u → u ≤ v → v ≤ γ → dd * (v - u) ≤ inner ℝ n (F v - F u) := by
  intro u v hu huv hv
  by_cases hc : v ≤ β
  · exact h1 u v hu huv hc
  · rw [not_le] at hc
    by_cases hc2 : u ≤ β
    · have h3 := h1 u β hu hc2 le_rfl
      have h4 := h2 β v le_rfl hc.le hv
      have harg : F v - F u = (F β - F u) + (F v - F β) := by abel
      rw [harg, inner_add_right]
      have hd : dd * (β - u) + dd * (v - β) = dd * (v - u) := by ring
      linarith
    · rw [not_le] at hc2
      exact h2 u v hc2.le huv hv


/-! ## Margins from continuity -/

/-- **A margin from a one-variable continuity datum.** -/
lemma margin_of_continuousAt₁ {f : ℝ → ℝ} {x₀ : ℝ} (hf : ContinuousAt f x₀) (h : 0 < f x₀) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, |x - x₀| ≤ δ → f x₀ / 2 ≤ f x := by
  obtain ⟨ε, hε, hε'⟩ := Metric.continuousAt_iff.mp hf (f x₀ / 2) (by linarith)
  refine ⟨ε / 2, by linarith, ?_⟩
  intro x hx
  have hd : dist x x₀ < ε := by
    rw [Real.dist_eq]
    linarith
  have h2 := hε' hd
  rw [Real.dist_eq] at h2
  linarith [(abs_lt.mp h2).1]

/-- **A margin from a two-variable continuity datum.** -/
lemma margin_of_continuousAt₂ {G : ℝ × ℝ → ℝ} {p₀ : ℝ × ℝ} (hG : ContinuousAt G p₀)
    (h : 0 < G p₀) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s u : ℝ, |s - p₀.1| ≤ δ → |u - p₀.2| ≤ δ → G p₀ / 2 ≤ G (s, u) := by
  obtain ⟨ε, hε, hε'⟩ := Metric.continuousAt_iff.mp hG (G p₀ / 2) (by linarith)
  refine ⟨ε / 2, by linarith, ?_⟩
  intro s u hs hu
  have hd : dist (s, u) p₀ < ε := by
    rw [Prod.dist_eq, max_lt_iff]
    refine ⟨?_, ?_⟩
    · rw [Real.dist_eq]; linarith
    · rw [Real.dist_eq]; linarith
  have h2 := hε' hd
  rw [Real.dist_eq] at h2
  linarith [(abs_lt.mp h2).1]


/-! ## Continuity of the `s`-dependent chord data -/

lemma continuousAt_sweepChord'_lc {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) {f : ℝ → ℝ} {σ₀ : ℝ} (hf : ContinuousAt f σ₀) :
    ContinuousAt (fun s : ℝ => sweepChord' r D s (f s)) σ₀ := by
  have hta : Continuous (taR D) := continuous_taR_lc D
  have htb : Continuous (tbR D) := continuous_tbR_lc D
  have hrc : Continuous r := hr.smooth.continuous
  simp only [sweepChord']
  fun_prop

lemma continuousAt_sweepArc'_lc {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) {f : ℝ → ℝ} {σ₀ : ℝ} (hf : ContinuousAt f σ₀) :
    ContinuousAt (fun s : ℝ => sweepArc' r D s (f s)) σ₀ := by
  have hta : Continuous (taR D) := continuous_taR_lc D
  have htb : Continuous (tbR D) := continuous_tbR_lc D
  have hws : Continuous (sweepW' D) := continuous_sweepW'_lc D
  have hrc : Continuous r := hr.smooth.continuous
  simp only [sweepArc']
  fun_prop

/-! ## Wedge directions at a junction -/

/-- If `v ≠ 0`, `V ≠ 0` and `v` is not a positive multiple of `V`, then `v` and the reversed chord
direction `-V` lie in a common open half-space. -/
lemma exists_wedge_of_not_multiple {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {v V : E} (hv : v ≠ 0) (hV : V ≠ 0) (h : ∀ k : ℝ, 0 < k → v ≠ k • V) :
    ∃ n : E, n ≠ 0 ∧ 0 < inner ℝ n v ∧ 0 < inner ℝ n (-V) := by
  have hne : ¬ ∃ m : ℝ, 0 < m ∧ V = m • v := by
    rintro ⟨m, hm, hmV⟩
    refine h (1 / m) (by positivity) ?_
    rw [hmV, ← mul_smul]
    have h1 : (1 / m) * m = 1 := by field_simp
    rw [h1, one_smul]
  exact exists_wedge_direction_of_not_antiparallel (E := E) hv hV hne

/-- If `v ≠ 0`, `V ≠ 0` and `V` is not a *negative* multiple of `v`, then `v` and `V` lie in a
common open half-space. -/
lemma exists_wedge_of_not_negMultiple {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {v V : E} (hv : v ≠ 0) (hV : V ≠ 0) (h : ∀ k : ℝ, 0 < k → V ≠ (-k) • v) :
    ∃ n : E, n ≠ 0 ∧ 0 < inner ℝ n v ∧ 0 < inner ℝ n V := by
  have hne : ¬ ∃ m : ℝ, 0 < m ∧ (-V) = m • v := by
    rintro ⟨m, hm, hmV⟩
    refine h m hm ?_
    rw [← neg_neg V, hmV, neg_smul]
  obtain ⟨n, hn, h1, h2⟩ :=
    exists_wedge_direction_of_not_antiparallel (E := E) hv (neg_ne_zero.mpr hV) hne
  exact ⟨n, hn, h1, by simpa [neg_neg] using h2⟩

/-- **The growth interface of the local cone.**  On the sweep-parameter window
`[σ₀ - δ, σ₀ + δ]`, the profile `chamferLoopProf r D lay (α s) (β s) s` grows at rate `dd > 0` in
the direction `n` on the whole profile window `[W₁, W₂]`. -/
def GrowthOn (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lay : ℝ) (α β : ℝ → ℝ)
    (σ₀ W₁ W₂ : ℝ) (n : Space) (dd δ : ℝ) : Prop :=
  ∀ s ∈ Set.Icc (σ₀ - δ) (σ₀ + δ), ∀ u v : ℝ, W₁ ≤ u → u ≤ v → v ≤ W₂ →
    dd * (v - u) ≤ inner ℝ n (chamferLoopProf r D lay (α s) (β s) s v
      - chamferLoopProf r D lay (α s) (β s) s u)

/-- **The arc-interior window.**  If the profile window `[u₀-δu, u₀+δu]` lies in the interior of the
retained arc (i.e. `u₀ ∈ (0,1/2)`), then the tangent direction `velocity r x₀` at the arc point of the
base profile pairs positively with the whole arc range of the window, uniformly over a
sweep-parameter window. -/
theorem localCone_arcWindow {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) {lay : ℝ} (hlay0 : 0 < lay) {α β : ℝ → ℝ} {σ₀ u₀ : ℝ}
    (hαc : ContinuousAt α σ₀) (ha0 : 0 < α σ₀) (ha1 : 2 * α σ₀ < 1)
    (hW : 0 < sweepW' D σ₀) (hu0 : 0 < u₀) (hu1 : u₀ < 1 / 2) :
    ∃ (n : Space) (δu δ dd : ℝ), 0 < δu ∧ 0 < δ ∧ 0 < dd ∧
      GrowthOn r D lay α β σ₀ (u₀ - δu) (u₀ + δu) n dd δ := by
  have hd : Continuous (deriv r) := hr.smooth.continuous_deriv le_top
  set x₀ : ℝ := taR D σ₀ + (α σ₀ + (1 - 2 * α σ₀) * (2 * u₀)) * sweepW' D σ₀ with hx₀
  set n : Space := deriv r x₀ with hn
  have hta : Continuous (fun p : ℝ × ℝ => taR D p.1) := (continuous_taR_lc D).comp continuous_fst
  have hWs : Continuous (fun p : ℝ × ℝ => sweepW' D p.1) := (continuous_sweepW'_lc D).comp continuous_fst
  have hα : ContinuousAt (fun p : ℝ × ℝ => α p.1) (σ₀, u₀) := hαc.comp continuousAt_fst
  have hmap : ContinuousAt (fun p : ℝ × ℝ =>
      taR D p.1 + (α p.1 + (1 - 2 * α p.1) * (2 * p.2)) * sweepW' D p.1) (σ₀, u₀) :=
    hta.continuousAt.add
      ((hα.add ((continuousAt_const.sub (hα.const_mul 2)).mul
        (continuousAt_const.mul continuousAt_snd))).mul hWs.continuousAt)
  have hG : ContinuousAt (fun p : ℝ × ℝ => inner ℝ n
      (deriv r (taR D p.1 + (α p.1 + (1 - 2 * α p.1) * (2 * p.2)) * sweepW' D p.1)))
      (σ₀, u₀) :=
    ContinuousAt.inner continuousAt_const (hd.continuousAt.comp hmap)
  have hGpos : 0 < inner ℝ n (deriv r x₀) := by
    rw [hn, real_inner_self_eq_norm_sq]
    exact pow_pos (norm_pos_iff.mpr (hr.regular x₀)) 2
  obtain ⟨δA, hδA, hmA⟩ := margin_of_continuousAt₂ hG hGpos
  have hcont1 : ContinuousAt (fun s : ℝ => 1 - 2 * α s) σ₀ := by fun_prop
  have hpos1 : 0 < 1 - 2 * α σ₀ := by linarith
  obtain ⟨δ1, hδ1, hm1⟩ := margin_of_continuousAt₁ hcont1 hpos1
  have hcont2 : ContinuousAt (fun s : ℝ => sweepW' D s) σ₀ :=
    (continuous_sweepW'_lc D).continuousAt
  obtain ⟨δ2, hδ2, hm2⟩ := margin_of_continuousAt₁ hcont2 hW
  have hApos : 0 < inner ℝ n (deriv r x₀) / 2 := by linarith
  refine ⟨n, min δA (min (u₀ / 2) ((1 / 2 - u₀) / 2)), min δA (min δ1 δ2),
    ((1 - 2 * α σ₀) / 2) * (2 * (sweepW' D σ₀ / 2)) * (inner ℝ n (deriv r x₀) / 2),
    lt_min hδA (lt_min (by linarith) (by linarith)),
    lt_min hδA (lt_min hδ1 hδ2), by positivity, ?_⟩
  intro s hs u v hu huv hv
  have hδuA : min δA (min (u₀ / 2) ((1 / 2 - u₀) / 2)) ≤ δA := min_le_left _ _
  have hδu1 : min δA (min (u₀ / 2) ((1 / 2 - u₀) / 2)) ≤ (1 / 2 - u₀) / 2 :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hδA' : min δA (min δ1 δ2) ≤ δA := min_le_left _ _
  have hδ1' : min δA (min δ1 δ2) ≤ δ1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ2' : min δA (min δ1 δ2) ≤ δ2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hsA : |s - σ₀| ≤ δA := by
    rw [abs_le]
    exact ⟨by linarith [hs.1, hδA'], by linarith [hs.2, hδA']⟩
  have hs1 : |s - σ₀| ≤ δ1 := by
    rw [abs_le]
    exact ⟨by linarith [hs.1, hδ1'], by linarith [hs.2, hδ1']⟩
  have hs2 : |s - σ₀| ≤ δ2 := by
    rw [abs_le]
    exact ⟨by linarith [hs.1, hδ2'], by linarith [hs.2, hδ2']⟩
  have huA : |u - u₀| ≤ δA := by
    rw [abs_le]
    exact ⟨by linarith [hu, hδuA], by linarith [hu, huv, hv, hδuA]⟩
  have hWs : 0 < sweepW' D s := by
    have := hm2 s hs2
    linarith
  have hαs : 0 < 1 - 2 * α s := by
    have := hm1 s hs1
    linarith
  have harc : ∀ w ∈ Set.Icc (u₀ - min δA (min (u₀ / 2) ((1 / 2 - u₀) / 2)))
      (u₀ + min δA (min (u₀ / 2) ((1 / 2 - u₀) / 2))),
      ((1 - 2 * α σ₀) / 2) * (2 * (sweepW' D σ₀ / 2)) * (inner ℝ n (deriv r x₀) / 2)
        ≤ ((1 - 2 * α s) * (2 * sweepW' D s))
          * inner ℝ n (deriv r (taR D s + (α s + (1 - 2 * α s) * (2 * w)) * sweepW' D s)) := by
    intro w hw
    have hwA : |w - u₀| ≤ δA := by
      rw [abs_le]
      exact ⟨by linarith [hw.1, hδuA], by linarith [hw.2, hδuA]⟩
    have hm := hmA s w hsA hwA
    have h1 := hm1 s hs1
    have h2 := hm2 s hs2
    have hnn : 0 ≤ inner ℝ n
        (deriv r (taR D s + (α s + (1 - 2 * α s) * (2 * w)) * sweepW' D s)) := by linarith
    have hp : ((1 - 2 * α σ₀) / 2) * (2 * (sweepW' D σ₀ / 2))
        ≤ (1 - 2 * α s) * (2 * sweepW' D s) :=
      mul_le_mul h1 (by linarith) (by linarith) (by linarith)
    exact mul_le_mul hp hm (by positivity) (by positivity)
  have hmin : min (u₀ + min δA (min (u₀ / 2) ((1 / 2 - u₀) / 2))) (1 / 2)
      = u₀ + min δA (min (u₀ / 2) ((1 / 2 - u₀) / 2)) := by
    rw [min_eq_left]
    linarith [hδu1]
  refine growth_arc_branch hr D (a := α s) (b := β s) (by linarith) hWs harc u v hu huv ?_
  rw [hmin]
  exact hv


end ScAux

/-! ## The transfer from the profile window to the loop parameter -/

/-- On a `t`-window that stays inside one cell of the sawtooth and with `sweepParam t₀ = u₀`, the
sawtooth is the affine function `u₀ + (t - t₀)/period`. -/
lemma sc_sweepParam_window {t₀ u₀ δu : ℝ} (hu₀ : sweepParam t₀ = u₀)
    (h0 : 0 ≤ u₀ - δu) (h1 : u₀ + δu < 1) :
    ∀ t ∈ Set.Icc (t₀ - δu * period) (t₀ + δu * period),
      sweepParam t = u₀ + (t - t₀) / period := by
  intro t ht
  have hT : (0 : ℝ) < period := period_pos
  have hTne : period ≠ 0 := ne_of_gt hT
  have hlo : t / period ≥ t₀ / period - δu := by
    have h := div_le_div_of_nonneg_right ht.1 hT.le
    rw [sub_div, mul_div_cancel_right₀ δu hTne] at h
    exact h
  have hhi : t / period ≤ t₀ / period + δu := by
    have h := div_le_div_of_nonneg_right ht.2 hT.le
    rw [add_div, mul_div_cancel_right₀ δu hTne] at h
    exact h
  have hfloor : (⌊t₀ / period⌋ : ℝ) = t₀ / period - u₀ := by
    have h := hu₀; simp only [sweepParam] at h; linarith
  have hk : ⌊t / period⌋ = ⌊t₀ / period⌋ := by
    refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
    · rw [hfloor]; linarith
    · rw [hfloor]; linarith
  rw [sweepParam, hk, hfloor]
  ring

/-- **The transfer inside one cell.** -/
lemma sc_growth_cell {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {lay : ℝ}
    {α β : ℝ → ℝ} {σ₀ u₀ δu dd δ : ℝ} {n : Space} {t₀ : ℝ}
    (hG : ScAux.GrowthOn r D lay α β σ₀ (u₀ - δu) (u₀ + δu) n dd δ)
    (hu₀ : sweepParam t₀ = u₀) (h0 : 0 ≤ u₀ - δu) (h1 : u₀ + δu < 1) :
    ∀ s ∈ Set.Icc (σ₀ - δ) (σ₀ + δ), ∀ t₁ ∈ Set.Icc (t₀ - δu * period) (t₀ + δu * period),
      ∀ t₂ ∈ Set.Icc (t₀ - δu * period) (t₀ + δu * period), t₁ ≤ t₂ →
      (dd / period) * (t₂ - t₁) ≤ inner ℝ n
        (chamferLoopGen r D lay α β s t₂ - chamferLoopGen r D lay α β s t₁) := by
  intro s hs t₁ ht1 t₂ ht2 ht12
  have hT : (0 : ℝ) < period := period_pos
  have hsw := sc_sweepParam_window hu₀ h0 h1
  rw [chamferLoopGen_eq_prof', chamferLoopGen_eq_prof', hsw t₂ ht2, hsw t₁ ht1]
  have hu1 : u₀ - δu ≤ u₀ + (t₁ - t₀) / period := by
    have h : -δu ≤ (t₁ - t₀) / period := by
      rw [le_div_iff₀ hT]; linarith [ht1.1]
    linarith
  have hu2 : u₀ + (t₂ - t₀) / period ≤ u₀ + δu := by
    have h : (t₂ - t₀) / period ≤ δu := by
      rw [div_le_iff₀ hT]; linarith [ht2.2]
    linarith
  have hle : u₀ + (t₁ - t₀) / period ≤ u₀ + (t₂ - t₀) / period := by
    have h : (t₁ - t₀) / period ≤ (t₂ - t₀) / period :=
      div_le_div_of_nonneg_right (by linarith) hT.le
    linarith
  have hmain := hG s hs (u₀ + (t₁ - t₀) / period) (u₀ + (t₂ - t₀) / period) hu1 hle hu2
  have hdiff : (u₀ + (t₂ - t₀) / period) - (u₀ + (t₁ - t₀) / period) = (t₂ - t₁) / period := by
    ring
  rw [hdiff] at hmain
  have hc : (dd / period) * (t₂ - t₁) = dd * ((t₂ - t₁) / period) := by ring
  linarith [hmain, hc.le]

/-- The sawtooth on a `t`-window crossing the cell boundary `t₀ - u₀·period` from the left. -/
lemma sc_sweepParam_window_wrapL {t₀ u₀ δu : ℝ} (hu₀ : sweepParam t₀ = u₀)
    (hu₀0 : 0 ≤ u₀) (h0 : u₀ < δu) (h1 : u₀ + δu < 1) :
    ∀ t ∈ Set.Icc (t₀ - δu * period) (t₀ + δu * period),
      (t < t₀ - u₀ * period → sweepParam t = u₀ + (t - t₀) / period + 1) ∧
      (t₀ - u₀ * period ≤ t → sweepParam t = u₀ + (t - t₀) / period) := by
  intro t ht
  have hT : (0 : ℝ) < period := period_pos
  have hTne : period ≠ 0 := ne_of_gt hT
  have hfloor : (⌊t₀ / period⌋ : ℝ) = t₀ / period - u₀ := by
    have h := hu₀; simp only [sweepParam] at h; linarith
  have hlo : t / period ≥ t₀ / period - δu := by
    have h := div_le_div_of_nonneg_right ht.1 hT.le
    rw [sub_div, mul_div_cancel_right₀ δu hTne] at h
    exact h
  have hhi : t / period ≤ t₀ / period + δu := by
    have h := div_le_div_of_nonneg_right ht.2 hT.le
    rw [add_div, mul_div_cancel_right₀ δu hTne] at h
    exact h
  constructor
  · intro htlt
    have h1 : t - t₀ < -u₀ * period := by linarith [htlt]
    have h2 : (t - t₀) / period < -u₀ := by
      rw [div_lt_iff₀ hT]; exact h1
    have h3 : (t - t₀) / period = t / period - t₀ / period := sub_div t t₀ period
    have hlt : t / period < (⌊t₀ / period⌋ : ℝ) := by rw [hfloor]; linarith [h2, h3]
    rw [hfloor] at hlt
    have hk : ⌊t / period⌋ = ⌊t₀ / period⌋ - 1 := by
      refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
      · push_cast; rw [hfloor]; linarith [hu₀0, h1]
      · push_cast; rw [hfloor]; linarith [hlt]
    rw [sweepParam, hk]
    push_cast
    rw [hfloor]
    ring
  · intro htge
    have h1 : -u₀ * period ≤ t - t₀ := by linarith [htge]
    have h2 : -u₀ ≤ (t - t₀) / period := by
      rw [le_div_iff₀ hT]; exact h1
    have h3 : (t - t₀) / period = t / period - t₀ / period := sub_div t t₀ period
    have hge : ((⌊t₀ / period⌋ : ℤ) : ℝ) ≤ t / period := by rw [hfloor]; linarith [h2, h3]
    have hlt : t / period < ((⌊t₀ / period⌋ : ℤ) : ℝ) + 1 := by
      rw [hfloor]; linarith
    have hk : ⌊t / period⌋ = ⌊t₀ / period⌋ := Int.floor_eq_iff.mpr ⟨hge, hlt⟩
    rw [sweepParam, hk, hfloor]
    ring

/-- The profile loop is closed: `P 1 = P 0`. -/
lemma sc_prof_one_eq_zero {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {lay a b s : ℝ}
    (hl0 : 0 < lay) (hl1 : lay < 1 / 2) :
    chamferLoopProf r D lay a b s 1 = chamferLoopProf r D lay a b s 0 := by
  have h0 : chamferLoopProf r D lay a b s 0 = sweepArc' r D s a := by
    rw [ScAux.prof_eq_arc D (u := 0) (by norm_num)]
    congr 1
    ring
  have h1 : chamferLoopProf r D lay a b s 1 = sweepArc' r D s a := by
    rw [ScAux.prof_eq_cham2 D (u := 1) hl0 hl1 (by linarith : (1 : ℝ) - lay / 2 ≤ 1)]
    have hd : lay / 2 ≠ 0 := by positivity
    have hq : (1 - (1 - lay / 2)) / (lay / 2) = 1 := by
      rw [show (1 : ℝ) - (1 - lay / 2) = lay / 2 by ring, div_self hd]
    rw [hq]
    simp
  rw [h0, h1]

/-- **The wrap transfer (left).** -/
lemma sc_growth_wrapL {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {lay : ℝ}
    (hl0 : 0 < lay) (hl1 : lay < 1 / 2) {α β : ℝ → ℝ} {σ₀ u₀ δu dd δ : ℝ} {n : Space} {t₀ : ℝ}
    (hR : ScAux.GrowthOn r D lay α β σ₀ 0 (u₀ + δu) n dd δ)
    (hL : ScAux.GrowthOn r D lay α β σ₀ (1 - (δu - u₀)) 1 n dd δ)
    (hu₀ : sweepParam t₀ = u₀) (hu₀0 : 0 ≤ u₀) (h0 : u₀ < δu) (h1 : u₀ + δu < 1) :
    ∀ s ∈ Set.Icc (σ₀ - δ) (σ₀ + δ), ∀ t₁ ∈ Set.Icc (t₀ - δu * period) (t₀ + δu * period),
      ∀ t₂ ∈ Set.Icc (t₀ - δu * period) (t₀ + δu * period), t₁ ≤ t₂ →
      (dd / period) * (t₂ - t₁) ≤ inner ℝ n
        (chamferLoopGen r D lay α β s t₂ - chamferLoopGen r D lay α β s t₁) := by
  intro s hs t₁ ht1 t₂ ht2 ht12
  have hT : (0 : ℝ) < period := period_pos
  have hsw := sc_sweepParam_window_wrapL (t₀ := t₀) (u₀ := u₀) (δu := δu) hu₀ hu₀0 h0 h1
  have hP1 : chamferLoopProf r D lay (α s) (β s) s 1 = chamferLoopProf r D lay (α s) (β s) s 0 :=
    sc_prof_one_eq_zero D hl0 hl1
  by_cases hcase2 : t₂ < t₀ - u₀ * period
  · have ht1' : t₁ < t₀ - u₀ * period := lt_of_le_of_lt ht12 hcase2
    rw [chamferLoopGen_eq_prof', chamferLoopGen_eq_prof',
      (hsw t₂ ht2).1 hcase2, (hsw t₁ ht1).1 ht1']
    have hmem1 : 1 - (δu - u₀) ≤ u₀ + (t₁ - t₀) / period + 1 := by
      have h : -δu ≤ (t₁ - t₀) / period := by
        rw [le_div_iff₀ hT]; linarith [ht1.1]
      linarith
    have hmem2 : u₀ + (t₂ - t₀) / period + 1 ≤ 1 := by
      have h : (t₂ - t₀) / period < -u₀ := by
        rw [div_lt_iff₀ hT]; linarith [hcase2]
      linarith
    have hle : u₀ + (t₁ - t₀) / period + 1 ≤ u₀ + (t₂ - t₀) / period + 1 := by
      have h : (t₁ - t₀) / period ≤ (t₂ - t₀) / period :=
        div_le_div_of_nonneg_right (by linarith) hT.le
      linarith
    have hm := hL s hs (u₀ + (t₁ - t₀) / period + 1) (u₀ + (t₂ - t₀) / period + 1)
      hmem1 hle hmem2
    have hdiff : (u₀ + (t₂ - t₀) / period + 1) - (u₀ + (t₁ - t₀) / period + 1)
        = (t₂ - t₁) / period := by ring
    rw [hdiff] at hm
    have hc : (dd / period) * (t₂ - t₁) = dd * ((t₂ - t₁) / period) := by ring
    linarith [hm, hc.le]
  · rw [not_lt] at hcase2
    by_cases hcase1 : t₀ - u₀ * period ≤ t₁
    · rw [chamferLoopGen_eq_prof', chamferLoopGen_eq_prof',
        (hsw t₂ ht2).2 hcase2, (hsw t₁ ht1).2 hcase1]
      have hmem1 : 0 ≤ u₀ + (t₁ - t₀) / period := by
        have h : -u₀ ≤ (t₁ - t₀) / period := by
          rw [le_div_iff₀ hT]; linarith [hcase1]
        linarith
      have hmem2 : u₀ + (t₂ - t₀) / period ≤ u₀ + δu := by
        have h : (t₂ - t₀) / period ≤ δu := by
          rw [div_le_iff₀ hT]; linarith [ht2.2]
        linarith
      have hle : u₀ + (t₁ - t₀) / period ≤ u₀ + (t₂ - t₀) / period := by
        have h : (t₁ - t₀) / period ≤ (t₂ - t₀) / period :=
          div_le_div_of_nonneg_right (by linarith) hT.le
        linarith
      have hm := hR s hs (u₀ + (t₁ - t₀) / period) (u₀ + (t₂ - t₀) / period) hmem1 hle hmem2
      have hdiff : (u₀ + (t₂ - t₀) / period) - (u₀ + (t₁ - t₀) / period)
          = (t₂ - t₁) / period := by ring
      rw [hdiff] at hm
      have hc : (dd / period) * (t₂ - t₁) = dd * ((t₂ - t₁) / period) := by ring
      linarith [hm, hc.le]
    · rw [not_le] at hcase1
      rw [chamferLoopGen_eq_prof', chamferLoopGen_eq_prof',
        (hsw t₂ ht2).2 hcase2, (hsw t₁ ht1).1 hcase1]
      have hmemR1 : 0 ≤ u₀ + (t₂ - t₀) / period := by
        have h : -u₀ ≤ (t₂ - t₀) / period := by
          rw [le_div_iff₀ hT]; linarith [hcase2]
        linarith
      have hmemR2 : u₀ + (t₂ - t₀) / period ≤ u₀ + δu := by
        have h : (t₂ - t₀) / period ≤ δu := by
          rw [div_le_iff₀ hT]; linarith [ht2.2]
        linarith
      have hmemL1 : 1 - (δu - u₀) ≤ u₀ + (t₁ - t₀) / period + 1 := by
        have h : -δu ≤ (t₁ - t₀) / period := by
          rw [le_div_iff₀ hT]; linarith [ht1.1]
        linarith
      have hmemL2 : u₀ + (t₁ - t₀) / period + 1 ≤ 1 := by
        have h : (t₁ - t₀) / period < -u₀ := by
          rw [div_lt_iff₀ hT]; linarith [hcase1]
        linarith
      have hmR := hR s hs 0 (u₀ + (t₂ - t₀) / period) le_rfl hmemR1 hmemR2
      have hmL := hL s hs (u₀ + (t₁ - t₀) / period + 1) 1 hmemL1 hmemL2 le_rfl
      have hsplit : chamferLoopProf r D lay (α s) (β s) s (u₀ + (t₂ - t₀) / period)
            - chamferLoopProf r D lay (α s) (β s) s (u₀ + (t₁ - t₀) / period + 1)
          = (chamferLoopProf r D lay (α s) (β s) s (u₀ + (t₂ - t₀) / period)
              - chamferLoopProf r D lay (α s) (β s) s 0)
            + (chamferLoopProf r D lay (α s) (β s) s 1
              - chamferLoopProf r D lay (α s) (β s) s (u₀ + (t₁ - t₀) / period + 1)) := by
        rw [hP1]; abel
      rw [hsplit, inner_add_right]
      have harith : dd * ((t₂ - t₁) / period)
          = dd * (u₀ + (t₂ - t₀) / period - 0)
            + dd * (1 - (u₀ + (t₁ - t₀) / period + 1)) := by ring
      have hc : (dd / period) * (t₂ - t₁) = dd * ((t₂ - t₁) / period) := by ring
      linarith [hmR, hmL, harith.le, hc.le]

/-! ## Lifting the four branch rate facts to the profile window -/

lemma sc_growthOn_arc {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData} (D : SweepData d)
    {lay : ℝ} {α β : ℝ → ℝ} {σ₀ W₁ W₂ dd δ : ℝ} {n : Space}
    (hα : ∀ s ∈ Set.Icc (σ₀ - δ) (σ₀ + δ), 2 * α s < 1)
    (hWs : ∀ s ∈ Set.Icc (σ₀ - δ) (σ₀ + δ), 0 < sweepW' D s)
    (hW₂ : W₂ ≤ 1 / 2)
    (harc : ∀ s ∈ Set.Icc (σ₀ - δ) (σ₀ + δ), ∀ u ∈ Set.Icc W₁ W₂,
        dd ≤ ((1 - 2 * α s) * (2 * sweepW' D s)) *
          inner ℝ n (deriv r (taR D s + (α s + (1 - 2 * α s) * (2 * u)) * sweepW' D s))) :
    ScAux.GrowthOn r D lay α β σ₀ W₁ W₂ n dd δ := by
  intro s hs u v hu huv hv
  refine ScAux.growth_arc_branch hr D (a := α s) (b := β s) (hα s hs) (hWs s hs)
    (fun u hu => harc s hs u hu) u v hu huv ?_
  rwa [min_eq_left hW₂]

lemma sc_growthOn_ch1 {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lay : ℝ} {α β : ℝ → ℝ} {σ₀ W₁ W₂ dd δ : ℝ} {n : Space}
    (hl0 : 0 < lay) (hW₁ : 1 / 2 ≤ W₁) (hW₂ : W₂ ≤ 1 / 2 + lay / 2)
    (hU : ∀ s ∈ Set.Icc (σ₀ - δ) (σ₀ + δ),
        dd ≤ (2 / lay) * inner ℝ n (sweepChord' r D s (1 - β s) - sweepArc' r D s (1 - α s))) :
    ScAux.GrowthOn r D lay α β σ₀ W₁ W₂ n dd δ := by
  intro s hs u v hu huv hv
  refine ScAux.growth_ch1_branch (lay := lay) (a := α s) (b := β s) (σ := s)
    (W₁ := W₁) (W₂ := W₂) (dd := dd) (n := n) D hl0 (hU s hs) u v ?_ huv ?_
  · rwa [max_eq_left hW₁]
  · rwa [min_eq_left hW₂]

lemma sc_growthOn_chord {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lay : ℝ} {α β : ℝ → ℝ} {σ₀ W₁ W₂ dd δ : ℝ} {n : Space}
    (hl0 : 0 < lay) (hl1 : lay < 1 / 2) (hW₁ : 1 / 2 + lay / 2 ≤ W₁) (hW₂ : W₂ ≤ 1 - lay / 2)
    (hV : ∀ s ∈ Set.Icc (σ₀ - δ) (σ₀ + δ),
        dd ≤ ((1 - 2 * β s) / (1 / 2 - lay)) *
          inner ℝ n (r (taR D s) - r (tbR D s))) :
    ScAux.GrowthOn r D lay α β σ₀ W₁ W₂ n dd δ := by
  intro s hs u v hu huv hv
  refine ScAux.growth_chord_branch (lay := lay) (a := α s) (b := β s) (σ := s)
    (W₁ := W₁) (W₂ := W₂) (dd := dd) (n := n) D hl0 hl1 (hV s hs) u v ?_ huv ?_
  · rwa [max_eq_left hW₁]
  · rwa [min_eq_left hW₂]

lemma sc_growthOn_cham2 {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lay : ℝ} {α β : ℝ → ℝ} {σ₀ W₁ W₂ dd δ : ℝ} {n : Space}
    (hl0 : 0 < lay) (hl1 : lay < 1 / 2) (hW₁ : 1 - lay / 2 ≤ W₁)
    (hU : ∀ s ∈ Set.Icc (σ₀ - δ) (σ₀ + δ),
        dd ≤ (2 / lay) * inner ℝ n (sweepArc' r D s (α s) - sweepChord' r D s (β s))) :
    ScAux.GrowthOn r D lay α β σ₀ W₁ W₂ n dd δ := by
  intro s hs u v hu huv hv
  refine ScAux.growth_cham2_branch (lay := lay) (a := α s) (b := β s) (σ := s)
    (W₁ := W₁) (W₂ := W₂) (dd := dd) (n := n) D hl0 hl1 (hU s hs) u v ?_ huv hv
  rwa [max_eq_left hW₁]

/-- **Gluing two profile windows.** -/
lemma sc_growthOn_glue {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {lay : ℝ}
    {α β : ℝ → ℝ} {σ₀ W₁ W₂ W₃ dd δ : ℝ} {n : Space}
    (h1 : ScAux.GrowthOn r D lay α β σ₀ W₁ W₂ n dd δ)
    (h2 : ScAux.GrowthOn r D lay α β σ₀ W₂ W₃ n dd δ) :
    ScAux.GrowthOn r D lay α β σ₀ W₁ W₃ n dd δ := by
  intro s hs u v hu huv hv
  exact ScAux.growth_glue (h1 s hs) (h2 s hs) u v hu huv hv

/-! ## Margins from the pointwise junction data -/

/-- **Arc-direction margin** on a window of profile parameters around `uW`. -/
lemma sc_arc_margin {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData} (D : SweepData d)
    {α : ℝ → ℝ} {σ₀ uW : ℝ} {n : Space}
    (hαc : ContinuousAt α σ₀) (hα1 : 2 * α σ₀ < 1) (hW0 : 0 < sweepW' D σ₀)
    (hpos : 0 < inner ℝ n
      (deriv r (taR D σ₀ + (α σ₀ + (1 - 2 * α σ₀) * (2 * uW)) * sweepW' D σ₀))) :
    ∃ δ dd : ℝ, 0 < δ ∧ 0 < dd ∧
      ∀ s ∈ Set.Icc (σ₀ - δ) (σ₀ + δ), ∀ u ∈ Set.Icc (uW - δ) (uW + δ),
        dd ≤ ((1 - 2 * α s) * (2 * sweepW' D s)) *
          inner ℝ n (deriv r (taR D s + (α s + (1 - 2 * α s) * (2 * u)) * sweepW' D s)) := by
  have hd : Continuous (deriv r) := hr.smooth.continuous_deriv le_top
  have hta : ContinuousAt (fun p : ℝ × ℝ => taR D p.1) (σ₀, uW) :=
    (ScAux.continuous_taR_lc D).continuousAt.comp continuous_fst.continuousAt
  have hWt : ContinuousAt (fun p : ℝ × ℝ => sweepW' D p.1) (σ₀, uW) :=
    (ScAux.continuous_sweepW'_lc D).continuousAt.comp continuous_fst.continuousAt
  have hαt : ContinuousAt (fun p : ℝ × ℝ => α p.1) (σ₀, uW) :=
    hαc.comp continuous_fst.continuousAt
  have hmap : ContinuousAt (fun p : ℝ × ℝ =>
      taR D p.1 + (α p.1 + (1 - 2 * α p.1) * (2 * p.2)) * sweepW' D p.1) (σ₀, uW) := by
    have h2α : ContinuousAt (fun p : ℝ × ℝ => 2 * α p.1) (σ₀, uW) :=
      continuousAt_const.mul hαt
    have h12α : ContinuousAt (fun p : ℝ × ℝ => 1 - 2 * α p.1) (σ₀, uW) :=
      continuousAt_const.sub h2α
    have h2u : ContinuousAt (fun p : ℝ × ℝ => 2 * p.2) (σ₀, uW) :=
      continuousAt_const.mul continuous_snd.continuousAt
    exact hta.add ((hαt.add (h12α.mul h2u)).mul hWt)
  have hG : ContinuousAt (fun p : ℝ × ℝ => inner ℝ n
      (deriv r (taR D p.1 + (α p.1 + (1 - 2 * α p.1) * (2 * p.2)) * sweepW' D p.1)))
      (σ₀, uW) :=
    ContinuousAt.inner continuousAt_const (hd.continuousAt.comp hmap)
  obtain ⟨δA, hδA, hmA⟩ := ScAux.margin_of_continuousAt₂ hG hpos
  have h12α : ContinuousAt (fun s : ℝ => 1 - 2 * α s) σ₀ :=
    continuousAt_const.sub (continuousAt_const.mul hαc)
  obtain ⟨δ1, hδ1, hm1⟩ := ScAux.margin_of_continuousAt₁ h12α (by linarith)
  obtain ⟨δ2, hδ2, hm2⟩ := ScAux.margin_of_continuousAt₁
    ((ScAux.continuous_sweepW'_lc D).continuousAt) hW0
  refine ⟨min δA (min δ1 δ2),
    ((1 - 2 * α σ₀) / 2) * (2 * (sweepW' D σ₀ / 2))
      * (inner ℝ n (deriv r (taR D σ₀ + (α σ₀ + (1 - 2 * α σ₀) * (2 * uW)) * sweepW' D σ₀)) / 2),
    lt_min hδA (lt_min hδ1 hδ2),
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith), ?_⟩
  intro s hs u hu
  have hleA : min δA (min δ1 δ2) ≤ δA := min_le_left _ _
  have hle1 : min δA (min δ1 δ2) ≤ δ1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hle2 : min δA (min δ1 δ2) ≤ δ2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hsA : |s - (σ₀, uW).1| ≤ δA := by
    rw [abs_le]; exact ⟨by linarith [hs.1, hleA], by linarith [hs.2, hleA]⟩
  have huA : |u - (σ₀, uW).2| ≤ δA := by
    rw [abs_le]; exact ⟨by linarith [hu.1, hleA], by linarith [hu.2, hleA]⟩
  have hs1 : |s - σ₀| ≤ δ1 := by
    rw [abs_le]; exact ⟨by linarith [hs.1, hle1], by linarith [hs.2, hle1]⟩
  have hs2 : |s - σ₀| ≤ δ2 := by
    rw [abs_le]; exact ⟨by linarith [hs.1, hle2], by linarith [hs.2, hle2]⟩
  have hm := hmA s u hsA huA
  have h1 := hm1 s hs1
  have h2 := hm2 s hs2
  have hnn : 0 ≤ inner ℝ n (deriv r (taR D s + (α s + (1 - 2 * α s) * (2 * u)) * sweepW' D s)) := by
    linarith [hm]
  have hb : 0 ≤ (1 - 2 * α s) * (2 * sweepW' D s) :=
    mul_nonneg (by linarith [h1]) (by linarith [h2])
  have hp : ((1 - 2 * α σ₀) / 2) * (2 * (sweepW' D σ₀ / 2)) ≤ (1 - 2 * α s) * (2 * sweepW' D s) :=
    mul_le_mul h1 (by linarith [h2]) (by linarith [hW0]) (by linarith [h1])
  exact mul_le_mul hp hm (by linarith [hpos]) hb

/-- **First-chamfer margin**: the pairing `⟪n, U₁(s)⟫` on a sweep-parameter window. -/
lemma sc_ch1_margin {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData} (D : SweepData d)
    {lay : ℝ} (hl0 : 0 < lay) {α β : ℝ → ℝ} {σ₀ : ℝ} {n : Space}
    (hαc : ContinuousAt α σ₀) (hβc : ContinuousAt β σ₀)
    (hpos : 0 < inner ℝ n (sweepChord' r D σ₀ (1 - β σ₀) - sweepArc' r D σ₀ (1 - α σ₀))) :
    ∃ δ dd : ℝ, 0 < δ ∧ 0 < dd ∧
      ∀ s ∈ Set.Icc (σ₀ - δ) (σ₀ + δ),
        dd ≤ (2 / lay) * inner ℝ n
          (sweepChord' r D s (1 - β s) - sweepArc' r D s (1 - α s)) := by
  have h1β : ContinuousAt (fun s : ℝ => 1 - β s) σ₀ := continuousAt_const.sub hβc
  have h1α : ContinuousAt (fun s : ℝ => 1 - α s) σ₀ := continuousAt_const.sub hαc
  have hcont : ContinuousAt (fun s : ℝ => inner ℝ n
      (sweepChord' r D s (1 - β s) - sweepArc' r D s (1 - α s))) σ₀ :=
    ContinuousAt.inner continuousAt_const
      ((ScAux.continuousAt_sweepChord'_lc hr D h1β).sub
        (ScAux.continuousAt_sweepArc'_lc hr D h1α))
  obtain ⟨δ, hδ, hm⟩ := ScAux.margin_of_continuousAt₁ hcont hpos
  refine ⟨δ, (2 / lay) * (inner ℝ n
      (sweepChord' r D σ₀ (1 - β σ₀) - sweepArc' r D σ₀ (1 - α σ₀)) / 2), hδ,
    mul_pos (by positivity) (by linarith), ?_⟩
  intro s hs
  have hs' : |s - σ₀| ≤ δ := by
    rw [abs_le]; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have h := hm s hs'
  have h2 : (2 / lay) * (inner ℝ n (sweepChord' r D σ₀ (1 - β σ₀)
      - sweepArc' r D σ₀ (1 - α σ₀)) / 2)
      ≤ (2 / lay) * inner ℝ n (sweepChord' r D s (1 - β s) - sweepArc' r D s (1 - α s)) :=
    mul_le_mul_of_nonneg_left h (by positivity)
  linarith [h2]

/-- **Chord margin**: the pairing `⟪n, r (taR s) - r (tbR s)⟫` on a sweep-parameter window. -/
lemma sc_chord_margin {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData} (D : SweepData d)
    {lay : ℝ} (hl1 : lay < 1 / 2) {β : ℝ → ℝ} {σ₀ : ℝ} {n : Space}
    (hβc : ContinuousAt β σ₀) (hβ1 : 2 * β σ₀ < 1)
    (hpos : 0 < inner ℝ n (r (taR D σ₀) - r (tbR D σ₀))) :
    ∃ δ dd : ℝ, 0 < δ ∧ 0 < dd ∧
      ∀ s ∈ Set.Icc (σ₀ - δ) (σ₀ + δ),
        dd ≤ ((1 - 2 * β s) / (1 / 2 - lay)) * inner ℝ n (r (taR D s) - r (tbR D s)) := by
  have hrc : Continuous r := hr.smooth.continuous
  have hcont : ContinuousAt (fun s : ℝ => inner ℝ n (r (taR D s) - r (tbR D s))) σ₀ :=
    ContinuousAt.inner continuousAt_const
      (((hrc.comp (ScAux.continuous_taR_lc D)).continuousAt).sub
        ((hrc.comp (ScAux.continuous_tbR_lc D)).continuousAt))
  obtain ⟨δA, hδA, hmA⟩ := ScAux.margin_of_continuousAt₁ hcont hpos
  have h1β : ContinuousAt (fun s : ℝ => 1 - 2 * β s) σ₀ :=
    continuousAt_const.sub (continuousAt_const.mul hβc)
  obtain ⟨δB, hδB, hmB⟩ := ScAux.margin_of_continuousAt₁ h1β (by linarith)
  have hnum : (0 : ℝ) < (1 - 2 * β σ₀) / 2 := by linarith
  have hden0 : (0 : ℝ) < (1 : ℝ) / 2 - lay := by linarith
  have hpp : (0 : ℝ) < inner ℝ n (r (taR D σ₀) - r (tbR D σ₀)) / 2 := by linarith
  refine ⟨min δA δB, (((1 - 2 * β σ₀) / 2) / (1 / 2 - lay))
      * (inner ℝ n (r (taR D σ₀) - r (tbR D σ₀)) / 2), lt_min hδA hδB,
    mul_pos (div_pos hnum hden0) hpp, ?_⟩
  intro s hs
  have hsA : |s - σ₀| ≤ δA := by
    rw [abs_le]
    exact ⟨by linarith [hs.1, min_le_left δA δB], by linarith [hs.2, min_le_left δA δB]⟩
  have hsB : |s - σ₀| ≤ δB := by
    rw [abs_le]
    exact ⟨by linarith [hs.1, min_le_right δA δB], by linarith [hs.2, min_le_right δA δB]⟩
  have hA := hmA s hsA
  have hB := hmB s hsB
  have h2 : (1 - 2 * β σ₀) / 2 / (1 / 2 - lay) ≤ (1 - 2 * β s) / (1 / 2 - lay) :=
    div_le_div_of_nonneg_right (by linarith [hB]) hden0.le
  have h3 : (0 : ℝ) ≤ (1 - 2 * β s) / (1 / 2 - lay) :=
    div_nonneg (by linarith [hB]) hden0.le
  exact mul_le_mul h2 hA (by linarith [hpos]) h3

/-- **Second-chamfer margin**: the pairing `⟪n, U₂(s)⟫` on a sweep-parameter window. -/
lemma sc_cham2_margin {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData} (D : SweepData d)
    {lay : ℝ} (hl0 : 0 < lay) {α β : ℝ → ℝ} {σ₀ : ℝ} {n : Space}
    (hαc : ContinuousAt α σ₀) (hβc : ContinuousAt β σ₀)
    (hpos : 0 < inner ℝ n (sweepArc' r D σ₀ (α σ₀) - sweepChord' r D σ₀ (β σ₀))) :
    ∃ δ dd : ℝ, 0 < δ ∧ 0 < dd ∧
      ∀ s ∈ Set.Icc (σ₀ - δ) (σ₀ + δ),
        dd ≤ (2 / lay) * inner ℝ n (sweepArc' r D s (α s) - sweepChord' r D s (β s)) := by
  have hcont : ContinuousAt (fun s : ℝ => inner ℝ n
      (sweepArc' r D s (α s) - sweepChord' r D s (β s))) σ₀ :=
    ContinuousAt.inner continuousAt_const
      ((ScAux.continuousAt_sweepArc'_lc hr D hαc).sub
        (ScAux.continuousAt_sweepChord'_lc hr D hβc))
  obtain ⟨δ, hδ, hm⟩ := ScAux.margin_of_continuousAt₁ hcont hpos
  refine ⟨δ, (2 / lay) * (inner ℝ n
      (sweepArc' r D σ₀ (α σ₀) - sweepChord' r D σ₀ (β σ₀)) / 2), hδ,
    mul_pos (by positivity) (by linarith), ?_⟩
  intro s hs
  have hs' : |s - σ₀| ≤ δ := by
    rw [abs_le]; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have h := hm s hs'
  have h2 : (2 / lay) * (inner ℝ n (sweepArc' r D σ₀ (α σ₀)
      - sweepChord' r D σ₀ (β σ₀)) / 2)
      ≤ (2 / lay) * inner ℝ n (sweepArc' r D s (α s) - sweepChord' r D s (β s)) :=
    mul_le_mul_of_nonneg_left h (by positivity)
  linarith [h2]
/-! ## The final assembly helpers -/

/-- **Final assembly inside one cell.** -/
lemma sc_final {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {lay : ℝ}
    {α β : ℝ → ℝ} {σ₀ u₀ δ η dd : ℝ} {n : Space} {t₀ : ℝ}
    (hGr : ScAux.GrowthOn r D lay α β σ₀ (u₀ - η) (u₀ + η) n dd δ)
    (hu₀ : sweepParam t₀ = u₀) (h0 : 0 ≤ u₀ - η) (h1 : u₀ + η < 1) :
    ∀ s ∈ Set.Icc (σ₀ - min δ (η * period)) (σ₀ + min δ (η * period)),
      ∀ t₁ t₂ : ℝ, t₀ - min δ (η * period) ≤ t₁ → t₁ ≤ t₂ →
        t₂ ≤ t₀ + min δ (η * period) →
        (dd / period) * (t₂ - t₁) ≤ inner ℝ n
          (chamferLoopGen r D lay α β s t₂ - chamferLoopGen r D lay α β s t₁) := by
  intro s hs t₁ t₂ ht1 ht12 ht2
  have hper : (0 : ℝ) < period := period_pos
  have hεδ : min δ (η * period) ≤ δ := min_le_left _ _
  have hεη : min δ (η * period) ≤ η * period := min_le_right _ _
  have hdiv : min δ (η * period) / period ≤ η := by
    have h := div_le_div_of_nonneg_right hεη hper.le
    rwa [mul_div_cancel_right₀ η (ne_of_gt hper)] at h
  have hG' : ScAux.GrowthOn r D lay α β σ₀ (u₀ - min δ (η * period) / period)
      (u₀ + min δ (η * period) / period) n dd δ :=
    fun s hs' u v hu huv hv => hGr s hs' u v (by linarith [hdiv]) huv (by linarith [hdiv])
  have h0' : (0 : ℝ) ≤ u₀ - min δ (η * period) / period := by linarith [hdiv, h0]
  have h1' : u₀ + min δ (η * period) / period < 1 := by linarith [hdiv, h1]
  have hmain := sc_growth_cell (D := D) (lay := lay) (α := α) (β := β) (σ₀ := σ₀)
    (u₀ := u₀) (δu := min δ (η * period) / period) (dd := dd) (δ := δ) (n := n) (t₀ := t₀)
    hG' hu₀ h0' h1'
  rw [div_mul_cancel₀ _ (ne_of_gt hper)] at hmain
  exact hmain s ⟨by linarith [hs.1, hεδ], by linarith [hs.2, hεδ]⟩ t₁
    ⟨ht1, by linarith⟩ t₂ ⟨by linarith, ht2⟩ ht12

/-- **Final assembly across the wrap.** -/
lemma sc_final_wrap {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {lay : ℝ}
    (hl0 : 0 < lay) (hl1 : lay < 1 / 2) {α β : ℝ → ℝ} {σ₀ u₀ δ η dd : ℝ} {n : Space} {t₀ : ℝ}
    (hR : ScAux.GrowthOn r D lay α β σ₀ 0 (u₀ + η) n dd δ)
    (hL : ScAux.GrowthOn r D lay α β σ₀ (1 - (η - u₀)) 1 n dd δ)
    (hu₀ : sweepParam t₀ = u₀) (hu₀0 : 0 ≤ u₀) (h0p : u₀ * period < min δ (η * period))
    (h1 : u₀ + η < 1) :
    ∀ s ∈ Set.Icc (σ₀ - min δ (η * period)) (σ₀ + min δ (η * period)),
      ∀ t₁ t₂ : ℝ, t₀ - min δ (η * period) ≤ t₁ → t₁ ≤ t₂ →
        t₂ ≤ t₀ + min δ (η * period) →
        (dd / period) * (t₂ - t₁) ≤ inner ℝ n
          (chamferLoopGen r D lay α β s t₂ - chamferLoopGen r D lay α β s t₁) := by
  intro s hs t₁ t₂ ht1 ht12 ht2
  have hper : (0 : ℝ) < period := period_pos
  have hεδ : min δ (η * period) ≤ δ := min_le_left _ _
  have hεη : min δ (η * period) ≤ η * period := min_le_right _ _
  have hdiv : min δ (η * period) / period ≤ η := by
    have h := div_le_div_of_nonneg_right hεη hper.le
    rwa [mul_div_cancel_right₀ η (ne_of_gt hper)] at h
  have h0' : u₀ < min δ (η * period) / period := by
    rw [lt_div_iff₀ hper]; exact h0p
  have hR' : ScAux.GrowthOn r D lay α β σ₀ 0 (u₀ + min δ (η * period) / period) n dd δ :=
    fun s hs' u v hu huv hv => hR s hs' u v hu huv (by linarith [hdiv, hv])
  have hL' : ScAux.GrowthOn r D lay α β σ₀
      (1 - (min δ (η * period) / period - u₀)) 1 n dd δ :=
    fun s hs' u v hu huv hv => hL s hs' u v (by linarith [hdiv, hu]) huv hv
  have hmain := sc_growth_wrapL (D := D) (lay := lay) (α := α) (β := β) (σ₀ := σ₀)
    (u₀ := u₀) (δu := min δ (η * period) / period) (dd := dd) (δ := δ) (n := n) (t₀ := t₀)
    hl0 hl1 hR' hL' hu₀ hu₀0 h0' (by linarith [hdiv, h1])
  rw [div_mul_cancel₀ _ (ne_of_gt hper)] at hmain
  exact hmain s ⟨by linarith [hs.1, hεδ], by linarith [hs.2, hεδ]⟩ t₁
    ⟨ht1, by linarith⟩ t₂ ⟨by linarith, ht2⟩ ht12

/-- **A common window for `2α s < 1` and `0 < sweepW' D s`.** -/
lemma sc_alpha_w_margin {d : BandArcData} (D : SweepData d) {α : ℝ → ℝ} {σ₀ : ℝ}
    (hαc : ContinuousAt α σ₀) (hα1 : 2 * α σ₀ < 1) (hW0 : 0 < sweepW' D σ₀) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Set.Icc (σ₀ - δ) (σ₀ + δ), 2 * α s < 1 ∧ 0 < sweepW' D s := by
  have hf : ContinuousAt (fun s : ℝ => 1 - 2 * α s) σ₀ :=
    continuousAt_const.sub (continuousAt_const.mul hαc)
  obtain ⟨δ1, hδ1, hm1⟩ := ScAux.margin_of_continuousAt₁
    (f := fun s : ℝ => 1 - 2 * α s) hf (by linarith : (0 : ℝ) < 1 - 2 * α σ₀)
  obtain ⟨δ2, hδ2, hm2⟩ := ScAux.margin_of_continuousAt₁
    ((ScAux.continuous_sweepW'_lc D).continuousAt) hW0
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun s hs => ⟨?_, ?_⟩⟩
  · have hs1 : |s - σ₀| ≤ δ1 := by
      rw [abs_le]
      exact ⟨by linarith [hs.1, min_le_left δ1 δ2], by linarith [hs.2, min_le_left δ1 δ2]⟩
    have := hm1 s hs1; linarith
  · have hs2 : |s - σ₀| ≤ δ2 := by
      rw [abs_le]
      exact ⟨by linarith [hs.1, min_le_right δ1 δ2], by linarith [hs.2, min_le_right δ1 δ2]⟩
    have := hm2 s hs2; linarith

/-- **The secant cone of the scheduled chamfer loop, own proof.** -/
theorem sc_localCone {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) {lay : ℝ} (hlay0 : 0 < lay) (hlay : lay ≤ 1 / 4) {α β : ℝ → ℝ}
    {σ₀ : ℝ} (hσ₀ : σ₀ ∈ Set.Ioo (0 : ℝ) 1) (hαc : ContinuousAt α σ₀)
    (hβc : ContinuousAt β σ₀) (hJ : ChamferJunctionOK r D α β σ₀) (t₀ : ℝ) :
    ∃ (n : Space) (ε c : ℝ), 0 < ε ∧ 0 < c ∧
      ∀ s ∈ Set.Icc (σ₀ - ε) (σ₀ + ε), ∀ t₁ t₂ : ℝ,
        t₀ - ε ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ t₀ + ε →
          c * (t₂ - t₁) ≤ inner ℝ n
            (chamferLoopGen r D lay α β s t₂ - chamferLoopGen r D lay α β s t₁) := by
  obtain ⟨hab, hw, ha0, ha1, hb0, hb1, hAB1, hAB2, hJ1, hJ2, hJ3, hJ4⟩ := hJ
  have hlay1 : lay < 1 / 2 := by linarith
  set u₀ : ℝ := sweepParam t₀ with hu₀def
  have hu₀ : sweepParam t₀ = u₀ := hu₀def.symm
  have hu₀0 : 0 ≤ u₀ := by rw [hu₀def]; exact (sweepParam_mem t₀).1
  rcases lt_trichotomy u₀ (1 / 2) with hcase | hcase | hcase
  · rcases eq_or_lt_of_le hu₀0 with h0eq | h0lt
    · -- ### the wrap at `u₀ = 0`
      have h0eq' : u₀ = 0 := h0eq.symm
      obtain ⟨n, hn0, hnpB, hnU2⟩ := ScAux.exists_wedge_of_not_negMultiple (E := Space)
        (v := velocity r (taR D σ₀ + (α σ₀) * sweepW' D σ₀))
        (V := sweepArc' r D σ₀ (α σ₀) - sweepChord' r D σ₀ (β σ₀))
        (hr.regular _) (sub_ne_zero.mpr hAB1) hJ4
      have hpt : taR D σ₀ + (α σ₀) * sweepW' D σ₀
          = taR D σ₀ + (α σ₀ + (1 - 2 * α σ₀) * (2 * 0)) * sweepW' D σ₀ := by ring
      have hpos_arc : 0 < inner ℝ n (deriv r (taR D σ₀
          + (α σ₀ + (1 - 2 * α σ₀) * (2 * 0)) * sweepW' D σ₀)) := by
        rw [← hpt]; exact hnpB
      obtain ⟨δa, dda, hδa, hdda, harca⟩ := sc_arc_margin hr D (uW := 0) hαc ha1 hw hpos_arc
      obtain ⟨δu, ddu, hδu, hddu, hU2m⟩ := sc_cham2_margin hr D hlay0 hαc hβc hnU2
      obtain ⟨δaw, hδaw, haw⟩ := sc_alpha_w_margin D hαc ha1 hw
      set δ : ℝ := min (min δa δu) δaw with hδdef
      set η : ℝ := min (min (lay / 2) (1 / 4)) δa with hηdef
      have hδ0 : 0 < δ := by rw [hδdef]; exact lt_min (lt_min hδa hδu) hδaw
      have hη0 : 0 < η := by
        rw [hηdef]; exact lt_min (lt_min (by linarith) (by norm_num)) hδa
      have hηlay : η ≤ lay / 2 := by
        rw [hηdef]
        exact le_trans (min_le_left (min (lay / 2) (1 / 4)) δa)
          (min_le_left (lay / 2) (1 / 4))
      have hηa : η ≤ δa := by
        rw [hηdef]; exact min_le_right (min (lay / 2) (1 / 4)) δa
      have hδa' : δ ≤ δa := by
        rw [hδdef]
        exact le_trans (min_le_left (min δa δu) δaw) (min_le_left δa δu)
      have hδu' : δ ≤ δu := by
        rw [hδdef]
        exact le_trans (min_le_left (min δa δu) δaw) (min_le_right δa δu)
      have hδaw' : δ ≤ δaw := by
        rw [hδdef]; exact min_le_right (min δa δu) δaw
      have hR : ScAux.GrowthOn r D lay α β σ₀ 0 (u₀ + η) n (min dda ddu) δ := by
        rw [h0eq', zero_add]
        refine sc_growthOn_arc hr D (fun s hs => (haw s ?_).1) (fun s hs => (haw s ?_).2)
          (by linarith) (fun s hs u hu => ?_)
        · exact ⟨by linarith [hs.1, hδaw'], by linarith [hs.2, hδaw']⟩
        · exact ⟨by linarith [hs.1, hδaw'], by linarith [hs.2, hδaw']⟩
        · have h := harca s ⟨by linarith [hs.1, hδa'], by linarith [hs.2, hδa']⟩ u
            ⟨by linarith [hu.1, hηa], by linarith [hu.2, hηa]⟩
          linarith [h, min_le_left dda ddu]
      have hL : ScAux.GrowthOn r D lay α β σ₀ (1 - (η - u₀)) 1 n (min dda ddu) δ := by
        rw [h0eq', sub_zero]
        refine sc_growthOn_cham2 D hlay0 hlay1 (by linarith) (fun s hs => ?_)
        have h := hU2m s ⟨by linarith [hs.1, hδu'], by linarith [hs.2, hδu']⟩
        linarith [h, min_le_right dda ddu]
      have hfin := sc_final_wrap (D := D) (α := α) (β := β) (σ₀ := σ₀) (u₀ := u₀)
        (δ := δ) (η := η) (dd := min dda ddu) (n := n) (t₀ := t₀)
        hlay0 hlay1 hR hL hu₀ hu₀0
        (by rw [h0eq', zero_mul]; exact lt_min hδ0 (mul_pos hη0 period_pos))
        (by rw [h0eq', zero_add]; linarith)
      exact ⟨n, min δ (η * period), (min dda ddu) / period,
        lt_min hδ0 (mul_pos hη0 period_pos), div_pos (lt_min hdda hddu) period_pos, hfin⟩
    · -- ### the arc interior `0 < u₀ < 1/2`
      obtain ⟨n, δu, δ, dd, hδu, hδ, hdd, hG⟩ :=
        ScAux.localCone_arcWindow hr D hlay0 hαc ha0 ha1 hw h0lt hcase
      set η : ℝ := min (u₀ / 2) δu with hηdef
      have hη0 : 0 < η := by rw [hηdef]; exact lt_min (by linarith) hδu
      have hηu : η ≤ u₀ / 2 := by rw [hηdef]; exact min_le_left _ _
      have hηu' : η ≤ δu := by rw [hηdef]; exact min_le_right _ _
      have hGr : ScAux.GrowthOn r D lay α β σ₀ (u₀ - η) (u₀ + η) n dd δ :=
        fun s hs u v hu huv hv => hG s hs u v (by linarith [hηu']) huv (by linarith [hηu'])
      have hfin := sc_final (D := D) (α := α) (β := β) (σ₀ := σ₀) (u₀ := u₀) (δ := δ)
        (η := η) (dd := dd) (n := n) (t₀ := t₀) hGr hu₀ (by linarith [hηu])
        (by linarith [hηu, hcase])
      exact ⟨n, min δ (η * period), dd / period,
        lt_min hδ (mul_pos hη0 period_pos), div_pos hdd period_pos, hfin⟩
  · -- ### the head junction `u₀ = 1/2`
    obtain ⟨n, hn0, hnpA, hnU₁⟩ := ScAux.exists_wedge_of_not_negMultiple (E := Space)
      (v := velocity r (taR D σ₀ + (1 - α σ₀) * sweepW' D σ₀))
      (V := sweepChord' r D σ₀ (1 - β σ₀) - sweepArc' r D σ₀ (1 - α σ₀))
      (hr.regular _) (sub_ne_zero.mpr (Ne.symm hAB2)) hJ1
    have hpt : taR D σ₀ + (1 - α σ₀) * sweepW' D σ₀
        = taR D σ₀ + (α σ₀ + (1 - 2 * α σ₀) * (2 * (1 / 2))) * sweepW' D σ₀ := by ring
    have hpos_arc : 0 < inner ℝ n (deriv r (taR D σ₀
        + (α σ₀ + (1 - 2 * α σ₀) * (2 * (1 / 2))) * sweepW' D σ₀)) := by
      rw [← hpt]; exact hnpA
    obtain ⟨δa, dda, hδa, hdda, harca⟩ := sc_arc_margin hr D (uW := 1 / 2) hαc ha1 hw hpos_arc
    obtain ⟨δu, ddu, hδu, hddu, hU1m⟩ := sc_ch1_margin hr D hlay0 hαc hβc hnU₁
    obtain ⟨δaw, hδaw, haw⟩ := sc_alpha_w_margin D hαc ha1 hw
    set δ : ℝ := min (min δa δu) δaw with hδdef
    set η : ℝ := min (min (lay / 2) (1 / 4)) δa with hηdef
    have hδ0 : 0 < δ := by rw [hδdef]; exact lt_min (lt_min hδa hδu) hδaw
    have hη0 : 0 < η := by
      rw [hηdef]; exact lt_min (lt_min (by linarith) (by norm_num)) hδa
    have hηlay : η ≤ lay / 2 := by
      rw [hηdef]
      exact le_trans (min_le_left (min (lay / 2) (1 / 4)) δa)
        (min_le_left (lay / 2) (1 / 4))
    have hηa : η ≤ δa := by
      rw [hηdef]; exact min_le_right (min (lay / 2) (1 / 4)) δa
    have hδa' : δ ≤ δa := by
      rw [hδdef]
      exact le_trans (min_le_left (min δa δu) δaw) (min_le_left δa δu)
    have hδu' : δ ≤ δu := by
      rw [hδdef]
      exact le_trans (min_le_left (min δa δu) δaw) (min_le_right δa δu)
    have hδaw' : δ ≤ δaw := by
      rw [hδdef]; exact min_le_right (min δa δu) δaw
    have hA : ScAux.GrowthOn r D lay α β σ₀ (u₀ - η) u₀ n (min dda ddu) δ := by
      rw [hcase]
      refine sc_growthOn_arc hr D (fun s hs => (haw s ?_).1) (fun s hs => (haw s ?_).2)
        (by norm_num) (fun s hs u hu => ?_)
      · exact ⟨by linarith [hs.1, hδaw'], by linarith [hs.2, hδaw']⟩
      · exact ⟨by linarith [hs.1, hδaw'], by linarith [hs.2, hδaw']⟩
      · have h := harca s ⟨by linarith [hs.1, hδa'], by linarith [hs.2, hδa']⟩ u
          ⟨by linarith [hu.1, hηa], by linarith [hu.2, hηa]⟩
        linarith [h, min_le_left dda ddu]
    have hB : ScAux.GrowthOn r D lay α β σ₀ u₀ (u₀ + η) n (min dda ddu) δ := by
      rw [hcase]
      refine sc_growthOn_ch1 D hlay0 (by norm_num) (by linarith) (fun s hs => ?_)
      have h := hU1m s ⟨by linarith [hs.1, hδu'], by linarith [hs.2, hδu']⟩
      linarith [h, min_le_right dda ddu]
    have hAB : ScAux.GrowthOn r D lay α β σ₀ (u₀ - η) (u₀ + η) n (min dda ddu) δ :=
      sc_growthOn_glue D hA hB
    have hfin := sc_final (D := D) (α := α) (β := β) (σ₀ := σ₀) (u₀ := u₀) (δ := δ)
      (η := η) (dd := min dda ddu) (n := n) (t₀ := t₀) hAB hu₀
      (by rw [hcase]; linarith) (by rw [hcase]; linarith)
    exact ⟨n, min δ (η * period), (min dda ddu) / period,
      lt_min hδ0 (mul_pos hη0 period_pos), div_pos (lt_min hdda hddu) period_pos, hfin⟩
  · -- ### `u₀ > 1/2`
    rcases lt_trichotomy u₀ (1 / 2 + lay / 2) with hcase2 | hcase2 | hcase2
    · -- #### the first chamfer interior
      have hU₁ne : sweepChord' r D σ₀ (1 - β σ₀) - sweepArc' r D σ₀ (1 - α σ₀) ≠ 0 :=
        sub_ne_zero.mpr (Ne.symm hAB2)
      have hnpos : 0 < inner ℝ (sweepChord' r D σ₀ (1 - β σ₀) - sweepArc' r D σ₀ (1 - α σ₀))
          (sweepChord' r D σ₀ (1 - β σ₀) - sweepArc' r D σ₀ (1 - α σ₀)) := by
        rw [real_inner_self_eq_norm_sq]
        exact pow_pos (norm_pos_iff.mpr hU₁ne) 2
      obtain ⟨δ, dd, hδ, hdd, hUm⟩ := sc_ch1_margin hr D hlay0 hαc hβc hnpos
      set η : ℝ := min ((u₀ - 1 / 2) / 2) (((1 / 2 + lay / 2) - u₀) / 2) with hηdef
      have hη0 : 0 < η := by rw [hηdef]; exact lt_min (by linarith) (by linarith)
      have hη1 : η ≤ (u₀ - 1 / 2) / 2 := by rw [hηdef]; exact min_le_left _ _
      have hη2 : η ≤ ((1 / 2 + lay / 2) - u₀) / 2 := by rw [hηdef]; exact min_le_right _ _
      have hGr : ScAux.GrowthOn r D lay α β σ₀ (u₀ - η) (u₀ + η)
          (sweepChord' r D σ₀ (1 - β σ₀) - sweepArc' r D σ₀ (1 - α σ₀)) dd δ :=
        sc_growthOn_ch1 D hlay0 (by linarith [hη1, hcase]) (by linarith [hη2, hcase2])
          (fun s hs => hUm s ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      have hfin := sc_final (D := D) (α := α) (β := β) (σ₀ := σ₀) (u₀ := u₀) (δ := δ)
        (η := η) (dd := dd) (n := sweepChord' r D σ₀ (1 - β σ₀) - sweepArc' r D σ₀ (1 - α σ₀))
        (t₀ := t₀) hGr hu₀ (by linarith [hη1, hcase]) (by linarith [hη2, hcase2, hlay1])
      exact ⟨_, min δ (η * period), dd / period,
        lt_min hδ (mul_pos hη0 period_pos), div_pos hdd period_pos, hfin⟩
    · -- #### the second junction `u₀ = 1/2 + lay/2`
      obtain ⟨n, hn0, hnU₁, hnV⟩ := ScAux.exists_wedge_of_not_multiple (E := Space)
        (v := sweepChord' r D σ₀ (1 - β σ₀) - sweepArc' r D σ₀ (1 - α σ₀))
        (V := r (tbR D σ₀) - r (taR D σ₀))
        (sub_ne_zero.mpr (Ne.symm hAB2)) (sub_ne_zero.mpr (Ne.symm hab)) hJ2
      have hnV' : 0 < inner ℝ n (r (taR D σ₀) - r (tbR D σ₀)) := by
        have h := hnV; rw [neg_sub] at h; exact h
      obtain ⟨δu, ddu, hδu, hddu, hU1m⟩ := sc_ch1_margin hr D hlay0 hαc hβc hnU₁
      obtain ⟨δv, ddv, hδv, hddv, hVm⟩ := sc_chord_margin hr D hlay1 hβc hb1 hnV'
      set δ : ℝ := min δu δv with hδdef
      set η : ℝ := min (lay / 2) (1 / 2 - lay) with hηdef
      have hδ0 : 0 < δ := by rw [hδdef]; exact lt_min hδu hδv
      have hη0 : 0 < η := by rw [hηdef]; exact lt_min (by linarith) (by linarith)
      have hη1 : η ≤ lay / 2 := by rw [hηdef]; exact min_le_left _ _
      have hη2 : η ≤ 1 / 2 - lay := by rw [hηdef]; exact min_le_right _ _
      have hδu' : δ ≤ δu := by rw [hδdef]; exact min_le_left _ _
      have hδv' : δ ≤ δv := by rw [hδdef]; exact min_le_right _ _
      have hA : ScAux.GrowthOn r D lay α β σ₀ (u₀ - η) u₀ n (min ddu ddv) δ := by
        rw [hcase2]
        refine sc_growthOn_ch1 D hlay0 (by linarith) (by linarith) (fun s hs => ?_)
        have h := hU1m s ⟨by linarith [hs.1, hδu'], by linarith [hs.2, hδu']⟩
        linarith [h, min_le_left ddu ddv]
      have hB : ScAux.GrowthOn r D lay α β σ₀ u₀ (u₀ + η) n (min ddu ddv) δ := by
        rw [hcase2]
        refine sc_growthOn_chord D hlay0 hlay1 (by linarith) (by linarith) (fun s hs => ?_)
        have h := hVm s ⟨by linarith [hs.1, hδv'], by linarith [hs.2, hδv']⟩
        linarith [h, min_le_right ddu ddv]
      have hAB : ScAux.GrowthOn r D lay α β σ₀ (u₀ - η) (u₀ + η) n (min ddu ddv) δ :=
        sc_growthOn_glue D hA hB
      have hfin := sc_final (D := D) (α := α) (β := β) (σ₀ := σ₀) (u₀ := u₀) (δ := δ)
        (η := η) (dd := min ddu ddv) (n := n) (t₀ := t₀) hAB hu₀
        (by rw [hcase2]; linarith) (by rw [hcase2]; linarith)
      exact ⟨n, min δ (η * period), (min ddu ddv) / period,
        lt_min hδ0 (mul_pos hη0 period_pos), div_pos (lt_min hddu hddv) period_pos, hfin⟩
    · -- #### `u₀ > 1/2 + lay/2`
      rcases lt_trichotomy u₀ (1 - lay / 2) with hcase3 | hcase3 | hcase3
      · -- ##### the chord interior
        have hVne : r (taR D σ₀) - r (tbR D σ₀) ≠ 0 := sub_ne_zero.mpr hab
        have hnpos : 0 < inner ℝ (r (taR D σ₀) - r (tbR D σ₀))
            (r (taR D σ₀) - r (tbR D σ₀)) := by
          rw [real_inner_self_eq_norm_sq]
          exact pow_pos (norm_pos_iff.mpr hVne) 2
        obtain ⟨δ, dd, hδ, hdd, hVm⟩ := sc_chord_margin hr D hlay1 hβc hb1 hnpos
        set η : ℝ := min ((u₀ - (1 / 2 + lay / 2)) / 2) (((1 - lay / 2) - u₀) / 2) with hηdef
        have hη0 : 0 < η := by rw [hηdef]; exact lt_min (by linarith) (by linarith)
        have hη1 : η ≤ (u₀ - (1 / 2 + lay / 2)) / 2 := by rw [hηdef]; exact min_le_left _ _
        have hη2 : η ≤ ((1 - lay / 2) - u₀) / 2 := by rw [hηdef]; exact min_le_right _ _
        have hGr : ScAux.GrowthOn r D lay α β σ₀ (u₀ - η) (u₀ + η)
            (r (taR D σ₀) - r (tbR D σ₀)) dd δ :=
          sc_growthOn_chord D hlay0 hlay1 (by linarith [hη1, hcase2]) (by linarith [hη2, hcase3])
            (fun s hs => hVm s ⟨by linarith [hs.1], by linarith [hs.2]⟩)
        have hfin := sc_final (D := D) (α := α) (β := β) (σ₀ := σ₀) (u₀ := u₀) (δ := δ)
          (η := η) (dd := dd) (n := r (taR D σ₀) - r (tbR D σ₀)) (t₀ := t₀) hGr hu₀
          (by linarith [hη1, hcase2]) (by linarith [hη2, hcase3, hlay1])
        exact ⟨_, min δ (η * period), dd / period,
          lt_min hδ (mul_pos hη0 period_pos), div_pos hdd period_pos, hfin⟩
      · -- ##### the third junction `u₀ = 1 - lay/2`
        obtain ⟨n, hn0, hnU2, hnV⟩ := ScAux.exists_wedge_of_not_multiple (E := Space)
          (v := sweepArc' r D σ₀ (α σ₀) - sweepChord' r D σ₀ (β σ₀))
          (V := r (tbR D σ₀) - r (taR D σ₀))
          (sub_ne_zero.mpr hAB1) (sub_ne_zero.mpr (Ne.symm hab)) hJ3
        have hnV' : 0 < inner ℝ n (r (taR D σ₀) - r (tbR D σ₀)) := by
          have h := hnV; rw [neg_sub] at h; exact h
        obtain ⟨δv, ddv, hδv, hddv, hVm⟩ := sc_chord_margin hr D hlay1 hβc hb1 hnV'
        obtain ⟨δu, ddu, hδu, hddu, hU2m⟩ := sc_cham2_margin hr D hlay0 hαc hβc hnU2
        set δ : ℝ := min δv δu with hδdef
        set η : ℝ := min (1 / 2 - lay) (lay / 4) with hηdef
        have hδ0 : 0 < δ := by rw [hδdef]; exact lt_min hδv hδu
        have hη0 : 0 < η := by rw [hηdef]; exact lt_min (by linarith) (by linarith)
        have hη1 : η ≤ 1 / 2 - lay := by rw [hηdef]; exact min_le_left _ _
        have hη2 : η ≤ lay / 4 := by rw [hηdef]; exact min_le_right _ _
        have hδv' : δ ≤ δv := by rw [hδdef]; exact min_le_left _ _
        have hδu' : δ ≤ δu := by rw [hδdef]; exact min_le_right _ _
        have hA : ScAux.GrowthOn r D lay α β σ₀ (u₀ - η) u₀ n (min ddv ddu) δ := by
          rw [hcase3]
          refine sc_growthOn_chord D hlay0 hlay1 (by linarith) (by linarith) (fun s hs => ?_)
          have h := hVm s ⟨by linarith [hs.1, hδv'], by linarith [hs.2, hδv']⟩
          linarith [h, min_le_left ddv ddu]
        have hB : ScAux.GrowthOn r D lay α β σ₀ u₀ (u₀ + η) n (min ddv ddu) δ := by
          rw [hcase3]
          refine sc_growthOn_cham2 D hlay0 hlay1 (by linarith) (fun s hs => ?_)
          have h := hU2m s ⟨by linarith [hs.1, hδu'], by linarith [hs.2, hδu']⟩
          linarith [h, min_le_right ddv ddu]
        have hAB : ScAux.GrowthOn r D lay α β σ₀ (u₀ - η) (u₀ + η) n (min ddv ddu) δ :=
          sc_growthOn_glue D hA hB
        have hfin := sc_final (D := D) (α := α) (β := β) (σ₀ := σ₀) (u₀ := u₀) (δ := δ)
          (η := η) (dd := min ddv ddu) (n := n) (t₀ := t₀) hAB hu₀
          (by rw [hcase3]; linarith [hη1]) (by rw [hcase3]; linarith [hη2, hlay0])
        exact ⟨n, min δ (η * period), (min ddv ddu) / period,
          lt_min hδ0 (mul_pos hη0 period_pos), div_pos (lt_min hddv hddu) period_pos, hfin⟩
      · -- ##### the second chamfer interior
        have hU₂ne : sweepArc' r D σ₀ (α σ₀) - sweepChord' r D σ₀ (β σ₀) ≠ 0 :=
          sub_ne_zero.mpr hAB1
        have hnpos : 0 < inner ℝ (sweepArc' r D σ₀ (α σ₀) - sweepChord' r D σ₀ (β σ₀))
            (sweepArc' r D σ₀ (α σ₀) - sweepChord' r D σ₀ (β σ₀)) := by
          rw [real_inner_self_eq_norm_sq]
          exact pow_pos (norm_pos_iff.mpr hU₂ne) 2
        obtain ⟨δ, dd, hδ, hdd, hUm⟩ := sc_cham2_margin hr D hlay0 hαc hβc hnpos
        set η : ℝ := min ((u₀ - (1 - lay / 2)) / 2) ((1 - u₀) / 2) with hηdef
        have hη0 : 0 < η := by
          rw [hηdef]
          exact lt_min (by linarith) (by linarith [(sweepParam_mem t₀).2, hu₀def])
        have hη1 : η ≤ (u₀ - (1 - lay / 2)) / 2 := by rw [hηdef]; exact min_le_left _ _
        have hη2 : η ≤ (1 - u₀) / 2 := by rw [hηdef]; exact min_le_right _ _
        have hGr : ScAux.GrowthOn r D lay α β σ₀ (u₀ - η) (u₀ + η)
            (sweepArc' r D σ₀ (α σ₀) - sweepChord' r D σ₀ (β σ₀)) dd δ :=
          sc_growthOn_cham2 D hlay0 hlay1 (by linarith [hη1, hcase3])
            (fun s hs => hUm s ⟨by linarith [hs.1], by linarith [hs.2]⟩)
        have hfin := sc_final (D := D) (α := α) (β := β) (σ₀ := σ₀) (u₀ := u₀) (δ := δ)
          (η := η) (dd := dd) (n := sweepArc' r D σ₀ (α σ₀) - sweepChord' r D σ₀ (β σ₀))
          (t₀ := t₀) hGr hu₀ (by linarith [hη1, hcase3])
          (by linarith [hη2, (sweepParam_mem t₀).2, hu₀def])
        exact ⟨_, min δ (η * period), dd / period,
          lt_min hδ (mul_pos hη0 period_pos), div_pos hdd period_pos, hfin⟩

/-- **The slices clause of the scheduled chamfer loop at a fixed layout `lay`**: on a window
`[a,b] ⊂ (0,1)`, given the per-`σ` junction data and the per-`σ` raw injectivity on the clamped
window `[a/2, (1+b)/2]`, there is a width threshold `L` such that all blur widths `δ₁, δ₂ ≤ L` give
injected blurred scheduled slices with non-vanishing velocity.  The layout is a *parameter* (the
`∀ lay ≤ L` form is FALSE: the loop's `t`-Lipschitz constant is `Θ(1/lay)`).  Discharge the `hloc`
and `hinj` inputs of the proved `Work.Drive.chamferLoopGen_blurSlices_of_localCone`
(`Drive/blurSlicesScheduled.lean`) from `hJ` (via `Work.Drive.chamferLoopGen_localCone`, whose
`ContinuousAt` side conditions come from `schedContinuity`) and `hI`. -/
theorem chamferLoopGen_slicesClause {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) {ρ₀ δs cQ : ℝ} (hδs : 0 < δs)
    {lay : ℝ} (hlay0 : 0 < lay) (hlay : lay ≤ 1 / 4)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hJ : ∀ σ ∈ Set.Icc (a / 2) ((1 + b) / 2),
      ChamferJunctionOK r D (schedAlpha lay ρ₀ δs D) (schedBeta r lay ρ₀ δs cQ D) σ)
    (hI : ∀ σ ∈ Set.Icc (a / 2) ((1 + b) / 2),
      Set.InjOn (chamferLoopGen r D lay (schedAlpha lay ρ₀ δs D) (schedBeta r lay ρ₀ δs cQ D) σ)
        (Set.Ico 0 period)) :
    ∃ L : ℝ, 0 < L ∧
      ∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ L → 0 < δ₂ → δ₂ ≤ L → ∀ σ ∈ Set.Icc a b,
        Set.InjOn (fun t : ℝ => sweepFamOf
            (chamferLoopGen r D lay (schedAlpha lay ρ₀ δs D) (schedBeta r lay ρ₀ δs cQ D))
            δ₁ δ₂ σ t) (Set.Ico 0 period) ∧
        (∀ t : ℝ, velocity (fun t : ℝ => sweepFamOf
            (chamferLoopGen r D lay (schedAlpha lay ρ₀ δs D) (schedBeta r lay ρ₀ δs cQ D))
            δ₁ δ₂ σ t) t ≠ 0) := by
  have hloc : ∀ σ₀ ∈ Set.Icc (a / 2) ((1 + b) / 2), ∀ t₀ ∈ Set.Icc (0 : ℝ) period,
      ∃ (n : Space) (ε c : ℝ), 0 < ε ∧ 0 < c ∧
        ∀ s ∈ Set.Icc (σ₀ - ε) (σ₀ + ε), ∀ t₁ t₂ : ℝ, t₀ - ε ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ t₀ + ε →
          c * (t₂ - t₁) ≤ inner ℝ n
            (schedLoop r D lay ρ₀ δs cQ s t₂ - schedLoop r D lay ρ₀ δs cQ s t₁) := by
    intro σ₀ hσ₀ t₀ ht₀
    have hσ0' : σ₀ ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hσ₀.1, ha], by linarith [hσ₀.2, hb]⟩
    have hK := hJ σ₀ hσ₀
    have hWne : sweepW' D σ₀ ≠ 0 := ne_of_gt hK.2.1
    have hLne : ‖r (tbR D σ₀) - r (taR D σ₀)‖ ≠ 0 := by
      rw [norm_ne_zero_iff]; intro h; exact hK.1 (eq_of_sub_eq_zero h).symm
    obtain ⟨n, ε, c, hε, hc, hcone⟩ :=
      sc_localCone hr D hlay0 hlay hσ0'
        (continuousAt_schedAlpha D lay ρ₀ δs hWne)
        (continuousAt_schedBeta D hr.smooth.continuous hLne) hK t₀
    exact ⟨n, ε, c, hε, hc, fun s hs t₁ t₂ h1 h2 h3 =>
      by simpa only [schedLoop] using hcone s hs t₁ t₂ h1 h2 h3⟩
  have hinj : ∀ s ∈ Set.Icc (a / 2) ((1 + b) / 2),
      Set.InjOn (schedLoop r D lay ρ₀ δs cQ s) (Set.Ico (0 : ℝ) period) :=
    fun s hs => hI s hs
  obtain ⟨L, hL, _hLa, _hLb, hmain⟩ :=
    chamferLoopGen_blurSlices_of_localCone' hr D hlay0 hlay hδs ha hab hb hloc hinj
  exact ⟨L, hL, hmain⟩


end Work.Drive
