import Mathlib
import Submission.Work.OddCurve.LowSlope.Extension
import Submission.Work.OddEnvelope.ChordCurve
import Submission.Work.OddEnvelope.Branch

/-!
# Transferring the moment equations along agreement of the chord curves

If two envelope curves `(X, Y)` and `(x, y)` for the same bump `h` agree on the half-line `s ≥ a`,
then the two moment integrals `(A)`, `(B)` of the odd case agree as well, for every slope `s ≥ a`.

The mathematical content is that the *envelope profile built from a chord curve only sees the
curve at the slopes up to the given point*: for `t ∈ (-(x s), y s)` the slope `σ` with `y σ = t`
(or `x σ = -t`) satisfies `σ > s ≥ a`, so it lies in the region where the two curves agree, and
hence `envelopeProfile h x y` and `envelopeProfile h X Y` coincide on the whole section.  The
integration endpoints coincide too, so both moment integrals agree.

The main theorem `momentEqs_transfer` then transports the two moment equations from `(X, Y)` to
`(x, y)`.  On the slopes `s > 1 - 3τ` this is immediate; at the single slope `s = 1 - 3τ`, which is
the only exponent not covered by the hypothesis `hA`/`hB`, both sides are obtained as limits from
the right, using
* `Work.OddCurve.hasDerivAt_momentA` (differentiability of `momentA` in the slope), and
* `Work.OddCurve.LowSlope.continuousAt_momentB` (continuity of `momentB` in the slope, proved
  below by a dominated-convergence argument in which the bump is precomposed with a smooth
  reparametrisation so that the integrand becomes globally continuous).
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-! ## Agreement of the inverse slopes -/

/-- If two chord curves agree at `s` and above it, then their inverse slopes agree on `(0, c s]`.
The equality case `u = c s` gives the slope `s` on both sides. -/
lemma slopeRight_eq_of_agree {c C : ℝ → ℝ} (hc : Work.OddEnvelope.IsChordCurve c)
    (hC : Work.OddEnvelope.IsChordCurve C) {s : ℝ} (hs : 0 < s) (hcs : c s = C s)
    (hag : ∀ σ : ℝ, s < σ → c σ = C σ) {u : ℝ} (hu : 0 < u) (hu_le : u ≤ c s) :
    Work.OddEnvelope.slopeRight c u = Work.OddEnvelope.slopeRight C u := by
  rcases lt_or_eq_of_le hu_le with hlt | heq
  · have huI : u ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨hu, lt_of_lt_of_le hlt (le_of_lt (hc.lt_one hs))⟩
    have hσpos : 0 < Work.OddEnvelope.slopeRight c u := hc.slopeRight_pos huI
    have hcσ : c (Work.OddEnvelope.slopeRight c u) = u := hc.slopeRight_eq huI
    have hσs : s < Work.OddEnvelope.slopeRight c u := by
      rcases lt_trichotomy (Work.OddEnvelope.slopeRight c u) s with h | h | h
      · have h' := hc.strictAntiOn hσpos hs h
        linarith
      · rw [h] at hcσ
        linarith
      · exact h
    have hCσ : C (Work.OddEnvelope.slopeRight c u) = u := by rw [← hag _ hσs, hcσ]
    exact hC.slopeRight_eq_of huI hσpos hCσ
  · have huI : u ∈ Set.Ioo (0 : ℝ) 1 := ⟨hu, by rw [heq]; exact hc.lt_one hs⟩
    have h1 : Work.OddEnvelope.slopeRight c u = s := (hc.slopeRight_eq_of huI hs heq.symm).symm
    have h2 : Work.OddEnvelope.slopeRight C u = s :=
      (hC.slopeRight_eq_of huI hs (by rw [← hcs, heq])).symm
    rw [h1, h2]

/-! ## Agreement of the two envelope profiles on the section -/

/-- If two envelope curves for the same bump agree at the slope `s` and above it, then their
envelope profiles agree on the whole section `[-(x s), y s]`. -/
lemma envelopeProfile_eqOn_of_agree {h X Y x y : ℝ → ℝ}
    (hX : Work.OddEnvelope.IsEnvelopeCurve h X Y) (hx : Work.OddEnvelope.IsEnvelopeCurve h x y)
    {s : ℝ} (hs : 0 < s) (hxs : x s = X s) (hys : y s = Y s)
    (hag : ∀ σ : ℝ, s < σ → x σ = X σ ∧ y σ = Y σ) :
    Set.EqOn (Work.OddEnvelope.envelopeProfile h x y) (Work.OddEnvelope.envelopeProfile h X Y)
      (Set.Icc (-(x s)) (y s)) := by
  intro t ht
  rcases lt_trichotomy t 0 with hneg | heq | hpos
  · -- left branch: `-t ∈ (0, x s]`
    have hmemt : t ∈ Set.Ioo (-1 : ℝ) 0 :=
      ⟨by have hxm1 := hx.toChordCurve_x.lt_one hs; linarith [ht.1], hneg⟩
    have hslope : Work.OddEnvelope.slopeLeft x t = Work.OddEnvelope.slopeLeft X t := by
      have h := slopeRight_eq_of_agree hx.toChordCurve_x hX.toChordCurve_x hs hxs
        (fun σ hσ => (hag σ hσ).1) (by linarith : 0 < -t) (by linarith [ht.1] : -t ≤ x s)
      simpa only [Work.OddEnvelope.slopeLeft, Work.OddEnvelope.slopeRight] using h
    rw [Work.OddEnvelope.envelopeProfile_of_neg hmemt, Work.OddEnvelope.envelopeProfile_of_neg hmemt]
    simp only [Work.OddEnvelope.envelopeLeft, hslope]
  · rw [heq, Work.OddEnvelope.envelopeProfile_zero, Work.OddEnvelope.envelopeProfile_zero]
  · -- right branch: `t ∈ (0, y s]`
    have hys1 : y s < 1 := hx.toChordCurve_y.lt_one hs
    have ht1 : t < 1 := lt_of_le_of_lt ht.2 hys1
    have htY : t ≤ Y s := by rw [← hys]; exact ht.2
    have hYs1 : Y s < 1 := by rw [← hys]; exact hys1
    have ht1' : t < 1 := lt_of_le_of_lt htY hYs1
    have hslope : Work.OddEnvelope.slopeRight y t = Work.OddEnvelope.slopeRight Y t :=
      slopeRight_eq_of_agree hx.toChordCurve_y hX.toChordCurve_y hs hys
        (fun σ hσ => (hag σ hσ).2) hpos ht.2
    rw [Work.OddEnvelope.envelopeProfile_of_pos ⟨hpos, ht1⟩,
      Work.OddEnvelope.envelopeProfile_of_pos ⟨hpos, ht1'⟩]
    simp only [Work.OddEnvelope.envelopeRight, hslope]

/-! ## Transfer of the two moment integrals -/

/-- **Transfer of `(A)`.**  If `(x, y)` agrees with `(X, Y)` on `[a, ∞)` then the volume moment
integrals coincide for every slope `s ≥ a`. -/
lemma momentA_eq_of_agree {n : ℕ} {h X Y x y : ℝ → ℝ}
    (hX : Work.OddEnvelope.IsEnvelopeCurve h X Y) (hx : Work.OddEnvelope.IsEnvelopeCurve h x y)
    {a s : ℝ} (hag : ∀ σ : ℝ, a ≤ σ → x σ = X σ ∧ y σ = Y σ) (has : a ≤ s) (hs0 : 0 < s) :
    Work.OddCurve.momentA n h x y (Work.OddEnvelope.envelopeProfile h x y) s =
      Work.OddCurve.momentA n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s := by
  have hxs : x s = X s := (hag s has).1
  have hys : y s = Y s := (hag s has).2
  have hle : -(X s) ≤ Y s := by
    rw [← hxs, ← hys]
    have h1 := hx.toChordCurve_x.pos hs0
    have h2 := hx.toChordCurve_y.pos hs0
    linarith
  have heq := envelopeProfile_eqOn_of_agree hX hx hs0 hxs hys
    (fun σ hσ => hag σ (le_trans has hσ.le))
  rw [Work.OddCurve.momentA_def, Work.OddCurve.momentA_def, hxs, hys]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Set.Icc (-(x s)) (y s) := by
    rw [Set.uIcc_of_le hle] at ht
    rwa [← hxs, ← hys] at ht
  have hft : (Work.OddEnvelope.envelopeProfile h x y) t =
      (Work.OddEnvelope.envelopeProfile h X Y) t := heq ht'
  simp only [Work.OddCurve.rad_def, hft]

/-- **Transfer of `(B)`.**  Same statement for the centroid moment integral. -/
lemma momentB_eq_of_agree {n : ℕ} {h X Y x y : ℝ → ℝ}
    (hX : Work.OddEnvelope.IsEnvelopeCurve h X Y) (hx : Work.OddEnvelope.IsEnvelopeCurve h x y)
    {a s : ℝ} (hag : ∀ σ : ℝ, a ≤ σ → x σ = X σ ∧ y σ = Y σ) (has : a ≤ s) (hs0 : 0 < s) :
    Work.OddCurve.momentB n h x y (Work.OddEnvelope.envelopeProfile h x y) s =
      Work.OddCurve.momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s := by
  have hxs : x s = X s := (hag s has).1
  have hys : y s = Y s := (hag s has).2
  have hle : -(X s) ≤ Y s := by
    rw [← hxs, ← hys]
    have h1 := hx.toChordCurve_x.pos hs0
    have h2 := hx.toChordCurve_y.pos hs0
    linarith
  have heq := envelopeProfile_eqOn_of_agree hX hx hs0 hxs hys
    (fun σ hσ => hag σ (le_trans has hσ.le))
  rw [Work.OddCurve.momentB_def, Work.OddCurve.momentB_def, hxs, hys]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Set.Icc (-(x s)) (y s) := by
    rw [Set.uIcc_of_le hle] at ht
    rwa [← hxs, ← hys] at ht
  have hft : (Work.OddEnvelope.envelopeProfile h x y) t =
      (Work.OddEnvelope.envelopeProfile h X Y) t := heq ht'
  simp only [Work.OddCurve.rad_def, hft]

/-! ## Continuity of `(B)` in the slope -/

/-- **`momentB` is continuous in the slope.**  The proof replaces the bump `h` by the globally
smooth function `u ↦ h (c u)`, where `c` is a smooth reparametrisation with `c = id` on a
neighbourhood of `s` (built from a `ContDiffBump`) and range in `(0, ∞)`: the moment integrand
then becomes *globally* continuous in `(u, t)`, so its integral over the fixed interval `[-1,1]`
is continuous in `u`; on the neighbourhood it agrees with `momentB`. -/
lemma continuousAt_momentB {n : ℕ} {h x y : ℝ → ℝ} (hx : Work.OddEnvelope.IsEnvelopeCurve h x y)
    {s : ℝ} (hs : 0 < s) :
    ContinuousAt (fun u : ℝ => Work.OddCurve.momentB n h x y
      (Work.OddEnvelope.envelopeProfile h x y) u) s := by
  set F : ℝ → ℝ := Work.OddEnvelope.envelopeProfile h x y with hF
  have hFcont : Continuous F := by
    rw [hF]
    exact Work.OddCurve.continuous_envelopeProfile hx
  let b : ContDiffBump (s : ℝ) := ⟨s / 4, s / 2, by linarith, by linarith⟩
  let c : ℝ → ℝ := fun u => s + (u - s) * (b u)
  let H : ℝ → ℝ := fun u => h (c u)
  have hc_smooth : ContDiff ℝ ∞ c := by
    have hb_cont : ContDiff ℝ ∞ (fun u : ℝ => (b u : ℝ)) := b.contDiff
    have h1 : ContDiff ℝ ∞ (fun u : ℝ => u - s) := contDiff_id.sub contDiff_const
    have h2 : ContDiff ℝ ∞ (fun u : ℝ => (u - s) * (b u : ℝ)) := h1.mul hb_cont
    have h3 : ContDiff ℝ ∞ (fun u : ℝ => s + (u - s) * (b u : ℝ)) := contDiff_const.add h2
    simpa [c] using h3
  have hc_self : ∀ u : ℝ, u ∈ Metric.ball s (s / 4) → c u = u := by
    intro u hu
    have h1 : b u = 1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hu)
    simp [c, h1]
  have hcpos : ∀ u : ℝ, 0 < c u := by
    intro u
    rcases lt_or_ge |u - s| (s / 2) with h | h
    · have hb0 : 0 ≤ b u := b.nonneg
      have hb1 : b u ≤ 1 := b.le_one
      have hle : |c u - s| ≤ |u - s| := by
        have h' : c u - s = (u - s) * b u := by simp [c]
        rw [h', abs_mul, abs_of_nonneg hb0]
        nlinarith [abs_nonneg (u - s), hb1]
      have hlt : |c u - s| < s / 2 := lt_of_le_of_lt hle h
      have := neg_abs_le (c u - s)
      linarith
    · have hb0 : b u = 0 := b.zero_of_le_dist (by rwa [Real.dist_eq])
      simp [c, hb0, hs]
  have hH_smooth : ContDiff ℝ ∞ H := by
    have hcomp := hx.smooth_h.comp (s := Set.univ) (t := Set.Ioi 0) hc_smooth.contDiffOn
      (fun u _ => hcpos u)
    rw [contDiffOn_univ] at hcomp
    simpa [H, Function.comp_def] using hcomp
  have hdHcont : Continuous (deriv H) := hH_smooth.continuous_deriv (by simp)
  have hcont_int : Continuous fun u : ℝ => ∫ t in (-1 : ℝ)..1,
      Work.OddCurve.rad H F (c u) t ^ (n - 1) * Real.sqrt (Work.OddCurve.rad H F (c u) t) *
        (t + deriv H (c u)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume)
    show Continuous fun p : ℝ × ℝ =>
      (F p.2 ^ 2 - (c p.1 * p.2 + H (c p.1)) ^ 2) ^ (n - 1) *
        Real.sqrt (F p.2 ^ 2 - (c p.1 * p.2 + H (c p.1)) ^ 2) * (p.2 + deriv H (c p.1))
    fun_prop
  have hev : (fun u : ℝ => Work.OddCurve.momentB n h x y F u) =ᶠ[𝓝 s]
      (fun u : ℝ => ∫ t in (-1 : ℝ)..1,
        Work.OddCurve.rad H F (c u) t ^ (n - 1) * Real.sqrt (Work.OddCurve.rad H F (c u) t) *
          (t + deriv H (c u))) := by
    filter_upwards [Metric.ball_mem_nhds s (by linarith : (0 : ℝ) < s / 4)] with u hu
    have hu0 : 0 < u := by
      have hd : dist u s < s / 4 := Metric.mem_ball.mp hu
      rw [Real.dist_eq] at hd
      have := neg_abs_le (u - s)
      linarith
    have hmu := Work.OddCurve.moment_eqs_eq_integral_Icc n hx hu0 (a := -1) (b := 1)
      (by have h := hx.toChordCurve_x.lt_one hu0; linarith)
      (le_of_lt (hx.toChordCurve_y.lt_one hu0))
    rw [hmu.2, hF]
    apply intervalIntegral.integral_congr
    intro t _
    have hcu : c u = u := hc_self u hu
    have hHu : H u = h u := by simp [H, hcu]
    have hdHu : deriv H u = deriv h u := by
      have hball : Metric.ball s (s / 4) ∈ 𝓝 u := Metric.isOpen_ball.mem_nhds hu
      have heqev : H =ᶠ[𝓝 u] h := by
        filter_upwards [hball] with v hv
        simp [H, hc_self v hv]
      exact heqev.deriv_eq
    simp only [Work.OddCurve.rad_def, hcu, hHu, hdHu]
  exact hcont_int.continuousAt.congr hev.symm

/-! ## Equality at the left endpoint of a half-line of equality -/

/-- If `g` and `G` are continuous at `s` and agree on `(s, T]`, then they agree at `s`. -/
lemma eq_at_of_continuousAt_of_eqOn_Ioc {g G : ℝ → ℝ} {s T : ℝ} (hsT : s < T)
    (hg : ContinuousAt g s) (hG : ContinuousAt G s) (h : ∀ u : ℝ, s < u → u ≤ T → g u = G u) :
    g s = G s := by
  have hmem : Set.Ioc s T ∈ 𝓝[>] s := Ioc_mem_nhdsGT hsT
  have hev : g =ᶠ[𝓝[>] s] G := by
    filter_upwards [hmem] with u hu
    exact h u hu.1 hu.2
  have h1 : Tendsto g (𝓝[>] s) (𝓝 (g s)) := hg.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto g (𝓝[>] s) (𝓝 (G s)) :=
    (hG.tendsto.mono_left nhdsWithin_le_nhds).congr' hev.symm
  exact tendsto_nhds_unique h1 h2

/-! ## The transfer of the moment equations -/

theorem momentEqs_transfer (n : ℕ) (hn : 1 ≤ n) {h X Y x y : ℝ → ℝ} {a : ℝ}
    (hX : Work.OddEnvelope.IsEnvelopeCurve h X Y)
    (hx : Work.OddEnvelope.IsEnvelopeCurve h x y)
    (ha : 1 - 3 * Work.OddVolterra.tau ≤ a)
    (hagree : ∀ s : ℝ, a ≤ s → x s = X s ∧ y s = Y s)
    (hA : ∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau < s → s ≤ 1 →
      Work.OddCurve.momentA n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s =
        Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2))
    (hB : ∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau < s → s ≤ 1 →
      Work.OddCurve.momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s = 0) :
    (∀ s : ℝ, a ≤ s → s ≤ 1 →
      Work.OddCurve.momentA n h x y (Work.OddEnvelope.envelopeProfile h x y) s =
        Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2)) ∧
    (∀ s : ℝ, a ≤ s → s ≤ 1 →
      Work.OddCurve.momentB n h x y (Work.OddEnvelope.envelopeProfile h x y) s = 0) := by
  have hτ : (0 : ℝ) < 1 - 3 * Work.OddVolterra.tau := by norm_num [Work.OddVolterra.tau]
  have hτ1 : 1 - 3 * Work.OddVolterra.tau < 1 := by norm_num [Work.OddVolterra.tau]
  constructor
  · intro s has hs1
    have hs0 : 0 < s := by linarith [hτ, ha, has]
    rw [momentA_eq_of_agree (n := n) hX hx hagree has hs0]
    by_cases hgt : 1 - 3 * Work.OddVolterra.tau < s
    · exact hA s hgt hs1
    · have hseq : s = 1 - 3 * Work.OddVolterra.tau :=
        le_antisymm (le_of_not_gt hgt) (le_trans ha has)
      rw [hseq]
      exact eq_at_of_continuousAt_of_eqOn_Ioc
        (g := fun u : ℝ => Work.OddCurve.momentA n h X Y
          (Work.OddEnvelope.envelopeProfile h X Y) u)
        (G := fun u : ℝ => Work.OddCurve.refConst n / Real.sqrt (1 + u ^ 2))
        (s := 1 - 3 * Work.OddVolterra.tau) (T := 1) hτ1
        (Work.OddCurve.hasDerivAt_momentA hn hX hτ).continuousAt
        (continuous_const.div (Real.continuous_sqrt.comp (by fun_prop))
          (fun u => ne_of_gt (Real.sqrt_pos.mpr (by positivity)))).continuousAt
        (fun u hu hu1 => hA u hu hu1)
  · intro s has hs1
    have hs0 : 0 < s := by linarith [hτ, ha, has]
    rw [momentB_eq_of_agree (n := n) hX hx hagree has hs0]
    by_cases hgt : 1 - 3 * Work.OddVolterra.tau < s
    · exact hB s hgt hs1
    · have hseq : s = 1 - 3 * Work.OddVolterra.tau :=
        le_antisymm (le_of_not_gt hgt) (le_trans ha has)
      rw [hseq]
      exact eq_at_of_continuousAt_of_eqOn_Ioc
        (g := fun u : ℝ => Work.OddCurve.momentB n h X Y
          (Work.OddEnvelope.envelopeProfile h X Y) u)
        (G := fun _ : ℝ => (0 : ℝ))
        (s := 1 - 3 * Work.OddVolterra.tau) (T := 1) hτ1
        (continuousAt_momentB hX hτ) continuousAt_const
        (fun u hu hu1 => hB u hu hu1)

end

end Work.OddCurve.LowSlope
