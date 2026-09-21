import Mathlib
import Submission.Work.OddBridge.Defs
import Submission.Work.OddVolterra.Assembly
import Submission.Work.OddVolterra.RowIdentity.odd_rowH
import Submission.Work.OddVolterra.RowIdentity.section_box
import Submission.Work.OddVolterra.RowIdentity.Qy_Qx_rect_pos
import Submission.Work.OddVolterra.RowIdentity.contDiffOn_AH
import Submission.Work.OddVolterra.Window.contDiffOn_fixed_window
import Submission.Work.OddVolterra.Smooth.Qy_pos_of_isEnvelopeCurve
import Submission.Work.OddVolterra.Smooth.contDiffAt_WWH
import Submission.Work.OddVolterra.Smooth.ParametricIntegral
import Submission.Work.OddEnvelope.Close.isEnvelopeCurve_of_close

/-!
# Smoothness of the odd centroid moment `momentH` for a transition-slope curve

The centroid moment of the odd-dimensional transition-slope argument,

`momentH n h x y f u = ∫_t in (-(x u))..(y u), ψ(u,t)^{n-1} √(ψ(u,t)) · ∂_sL(u,t)`,
`ψ u t = f t² - L(u,t)²`,

has a *fractional-power* singularity at the two moving endpoints `t = y u` and `t = -x u`, where
the radicand vanishes.  Following the row-identity chapter
(`Work.OddVolterra.RowIdentity.odd_rowH`) we split, near a slope `s ∈ (0,1)`,

`momentH = AAfH + WWH`

into the integral `AAfH` over the fixed window `(-X₁, X₁)` (where the profile is the semicircle,
so the radicand is bounded away from `0` and the usual parametric-integral argument applies) and
the swept integral `WWH u = ∫_σ in u..1, (σ-u)^{n-1/2} · AH u σ`, whose singularity is removed by
the substitution `σ = u + θ²(1-u)`.

This file proves the `C^∞` statement `Work.OddBridge.ContH` — smoothness of
`u ↦ momentH n h x y (envelopeProfile h x y) u` on `(0,1)` — and deduces the requested bridge
`Work.OddBridge.contH_of_curveData` from the Volterra transition-slope data.
-/

namespace Work.OddBridge

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-! ## From the Volterra `CurveData` to the envelope-curve hypothesis -/

/-- The Volterra transition-slope data `Work.OddVolterra.CurveData` is an envelope curve in the
sense of `Work.OddEnvelope.IsEnvelopeCurve` (this is the closeness hypothesis `1/100` of
`Work.OddEnvelope.Close.isEnvelopeCurve_of_close`). -/
theorem curveData_isEnvelopeCurve (n : ℕ) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hdata : Work.OddVolterra.CurveData n h x y) :
    Work.OddEnvelope.IsEnvelopeCurve h x y := by
  have h0 : h 0 = 0 := by
    by_contra hne
    have hmem := hsupp (Function.mem_support.mpr hne)
    rw [Set.mem_Icc] at hmem
    rw [Work.OddVolterra.tau] at hmem
    norm_num at hmem
  have hsupp' : Function.support h ⊆
      Set.Icc (1 - 2 * Work.OddEnvelope.tau) (1 - Work.OddEnvelope.tau) := hsupp
  exact Work.OddEnvelope.Close.isEnvelopeCurve_of_close (hδ := le_rfl)
    hdata.smooth_x hdata.smooth_y hh.contDiffOn hdata.deriv_x_neg hdata.deriv_y_neg
    hdata.tendsto_x hdata.tendsto_y hdata.tail_x hdata.tail_y h0 hsupp'
    hdata.close_x hdata.close_y hdata.close_h

/-! ## Small facts about the envelope profile

These are the few facts about `Work.OddEnvelope.envelopeProfile` that the row-identity setup
consumes, proved directly from the (stable) envelope chapter. -/

/-- `profileX 1 < tStar`: the chord function is strictly decreasing and `1 - τ < 1`. -/
lemma profileX_one_lt_tStar :
    Commons.Geometry.Ulam.profileX 1 < Work.OddEnvelope.tStar := by
  have h1 : (0 : ℝ) < 1 - Work.OddEnvelope.tau := Work.OddEnvelope.one_sub_tau_pos
  have h2 : 1 - Work.OddEnvelope.tau < 1 := by
    have := Work.OddEnvelope.tau_pos; linarith
  have h3 : Work.OddEnvelope.profileX 1 < Work.OddEnvelope.profileX (1 - Work.OddEnvelope.tau) :=
    Work.OddEnvelope.profileX_strictAntiOn h1 (by norm_num) h2
  rw [Work.OddEnvelope.tStar]
  exact h3

/-- On the fixed window `(-X₁, X₁)` the envelope profile is the semicircle, so the semicircle
radicand of the row identity is positive there. -/
lemma psi_semicircle_pos_of_envelope {h x y : ℝ → ℝ} (H : Work.OddEnvelope.IsEnvelopeCurve h x y)
    {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) {t : ℝ}
    (ht : t ∈ Set.Ioo (-(Commons.Geometry.Ulam.profileX 1))
      (Commons.Geometry.Ulam.profileX 1)) :
    0 < Work.OddVolterra.psi h Commons.Geometry.Ulam.semicircle u t := by
  have hstar : t ∈ Set.Ioo (-(Work.OddEnvelope.tStar)) (Work.OddEnvelope.tStar) :=
    ⟨by linarith [ht.1, profileX_one_lt_tStar], by linarith [ht.2, profileX_one_lt_tStar]⟩
  have hfsemi : Work.OddEnvelope.envelopeProfile h x y t
      = Commons.Geometry.Ulam.semicircle t := by
    rw [Work.OddEnvelope.envelopeProfile_eq_semicircle H hstar]
    rfl
  have htail_x : x 1 = Commons.Geometry.Ulam.profileX 1 := by
    rw [H.x_tail 1 (by have := Work.OddEnvelope.tau_pos; linarith)]
    rfl
  have htail_y : y 1 = Commons.Geometry.Ulam.profileX 1 := by
    rw [H.y_tail 1 (by have := Work.OddEnvelope.tau_pos; linarith)]
    rfl
  have hone : (1 : ℝ) ∈ Set.Ioi 0 := by norm_num
  have hx1 : Commons.Geometry.Ulam.profileX 1 ≤ x u := by
    rw [← htail_x]
    rcases lt_or_eq_of_le hu1 with hlt | heq
    · exact (H.toChordCurve_x.strictAntiOn hu hone hlt).le
    · rw [heq]
  have hy1 : Commons.Geometry.Ulam.profileX 1 ≤ y u := by
    rw [← htail_y]
    rcases lt_or_eq_of_le hu1 with hlt | heq
    · exact (H.toChordCurve_y.strictAntiOn hu hone hlt).le
    · rw [heq]
  have hmem : t ∈ Set.Ioo (-(x u)) (y u) := ⟨by linarith [ht.1, hx1], by linarith [ht.2, hy1]⟩
  have hpos := Work.OddEnvelope.envelopeProfile_sub_sq_pos H
    (Work.OddEnvelope.concaveOn_envelopeProfile H) hu t hmem
  have hcongr : Work.OddVolterra.psi h (Work.OddEnvelope.envelopeProfile h x y) u t
      = Work.OddVolterra.psi h Commons.Geometry.Ulam.semicircle u t := by
    unfold Work.OddVolterra.psi Work.OddVolterra.line
    rw [hfsemi]
  rw [← hcongr]
  exact hpos

/-! ## The row-identity setup attached to an envelope curve -/

/-- The `Setup` of the odd row-identity chapter, produced from an envelope curve at a single
slope `s ∈ (0,1)` (so that `a = c = s`). -/
noncomputable def envelopeSetup (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (H : Work.OddEnvelope.IsEnvelopeCurve h x y) {s : ℝ}
    (hs : 0 < s) (hs1 : s < 1) : Work.OddVolterra.RowIdentity.Setup where
  n := n
  hn := hn
  a := s
  c := s
  ha := hs
  hac := le_rfl
  hc1 := hs1
  h := h
  x := x
  y := y
  f := Work.OddEnvelope.envelopeProfile h x y
  hh := hh
  hx := H.smooth_x
  hy := H.smooth_y
  hf := Work.OddEnvelope.envelopeProfile_contDiffOn H
  hxy := fun u hu => ⟨Work.OddEnvelope.envelopeProfile_root_right H hu.1,
    Work.OddEnvelope.envelopeProfile_root_left H hu.1⟩
  hxdec := fun σ hσ => (H.x_deriv_neg σ (lt_trans hs hσ.1)).le
  hydec := fun σ hσ => (H.y_deriv_neg σ (lt_trans hs hσ.1)).le
  hxb := by
    rw [H.x_tail 1 (by have := Work.OddEnvelope.tau_pos; linarith)]
    rfl
  hyb := by
    rw [H.y_tail 1 (by have := Work.OddEnvelope.tau_pos; linarith)]
    rfl
  hfb := fun t ht => by
    have hstar : t ∈ Set.Ioo (-(Work.OddEnvelope.tStar)) (Work.OddEnvelope.tStar) :=
      ⟨by linarith [ht.1, profileX_one_lt_tStar], by linarith [ht.2, profileX_one_lt_tStar]⟩
    rw [Work.OddEnvelope.envelopeProfile_eq_semicircle H hstar]
    rfl
  hxle := fun σ hσ => by
    rcases lt_or_eq_of_le hσ.2 with hlt | heq
    · exact (H.toChordCurve_x.strictAntiOn (lt_of_lt_of_le hs hσ.1)
        (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num) hlt).le
    · rw [heq]
  hyle := fun σ hσ => by
    rcases lt_or_eq_of_le hσ.2 with hlt | heq
    · exact (H.toChordCurve_y.strictAntiOn (lt_of_lt_of_le hs hσ.1)
        (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num) hlt).le
    · rw [heq]
  hord := by
    have hx := H.x_tail 1 (by have := Work.OddEnvelope.tau_pos; linarith)
    have hy := H.y_tail 1 (by have := Work.OddEnvelope.tau_pos; linarith)
    rw [hx, hy]
    have hpos : 0 < Work.OddEnvelope.profileX 1 := Work.OddEnvelope.profileX_pos 1
    linarith
  hint := fun σ hσ => Work.OddEnvelope.envelopeProfile_mem_Ioo H (lt_of_lt_of_le hs hσ.1)
  hKden := fun u σ hu huσ hσ1 =>
    Work.OddVolterra.Smooth.Qy_pos_of_isEnvelopeCurve H u σ (lt_of_lt_of_le hs hu) huσ hσ1
  hmid := fun σ hσ t ht =>
    psi_semicircle_pos_of_envelope H (lt_of_lt_of_le hs hσ.1) hσ.2 ht

/-! ## `C^∞` smoothness of the swept centroid integral `WWH` -/

/-- The substitution `σ = u + θ²(1-u)` turns the fractional power `(σ-u)^{n-1/2}` of the swept
centroid integral into the *integer* power `θ^{2n}`; since the coefficient `AH` is `C^∞` on the
rectangle where the frozen radicands are positive, the substituted integral is `C^∞` in `u`
(differentiating under the integral sign) and so is the prefactor `(1-u)^{n+1/2}` near `s < 1`.

This is the `C^∞` strengthening of `Work.OddVolterra.Smooth.contDiffAt_WWH` (which records only
the finite order `n`). -/
theorem contDiffAt_WWH_top {n : ℕ} {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hx : ContDiffOn ℝ (⊤ : ℕ∞) x (Set.Ioi 0)) (hy : ContDiffOn ℝ (⊤ : ℕ∞) y (Set.Ioi 0))
    {s δ : ℝ} (hs1 : s < 1) (hδ : 0 < δ) (hsδ : 0 < s - δ)
    (hQy : ∀ u σ : ℝ, u ∈ Set.Ioo (s - δ) (s + δ) → σ ∈ Set.Ioo (s - δ) (1 + δ) →
      0 < Work.OddVolterra.RowIdentity.QyH h y u σ)
    (hQx : ∀ u σ : ℝ, u ∈ Set.Ioo (s - δ) (s + δ) → σ ∈ Set.Ioo (s - δ) (1 + δ) →
      0 < Work.OddVolterra.RowIdentity.QxH h x u σ) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℝ => Work.OddVolterra.RowIdentity.WWH n h x y u) s := by
  have hs0 : 0 < s := by linarith
  -- the open set of `(u,θ)` on which the substituted integrand is smooth
  set V : Set (ℝ × ℝ) :=
    {q : ℝ × ℝ | q.1 ∈ Set.Ioo (s - δ) (s + δ) ∧
      q.1 + q.2 ^ 2 * (1 - q.1) ∈ Set.Ioo (s - δ) (1 + δ)} with hVdef
  have hVopen : IsOpen V := by
    rw [hVdef]
    exact (isOpen_Ioo.preimage continuous_fst).inter (isOpen_Ioo.preimage (by fun_prop))
  have hA : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => Work.OddVolterra.RowIdentity.AH n h x y p.1 p.2)
      (Set.Ioo (s - δ) (s + δ) ×ˢ Set.Ioo (s - δ) (1 + δ)) :=
    Work.OddVolterra.RowIdentity.contDiffOn_AH hsδ hh hx hy
      (fun u σ hu hσ => ⟨hQy u σ hu hσ, hQx u σ hu hσ⟩)
  have hcomp : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ =>
        Work.OddVolterra.RowIdentity.AH n h x y q.1 (q.1 + q.2 ^ 2 * (1 - q.1))) V := by
    have h1 : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun q : ℝ × ℝ => (q.1, q.1 + q.2 ^ 2 * (1 - q.1))) Set.univ := by fun_prop
    have h2 := hA.comp (h1.mono (Set.subset_univ V)) (fun q hq => by rw [hVdef] at hq; exact hq)
    simpa [Function.comp_def] using h2
  have hF : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ =>
        2 * q.2 ^ (2 * n) * Work.OddVolterra.RowIdentity.AH n h x y q.1
          (q.1 + q.2 ^ 2 * (1 - q.1))) V := by
    have hpow : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => 2 * q.2 ^ (2 * n)) V := by fun_prop
    simpa only [Pi.mul_apply] using hpow.mul hcomp
  have hseg : ∀ θ ∈ Set.uIcc (0 : ℝ) 1, (s, θ) ∈ V := by
    intro θ hθ
    rw [hVdef]
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hθ
    have hθ2 : θ ^ 2 ≤ 1 := by nlinarith [hθ.1, hθ.2]
    have hlow : 0 ≤ θ ^ 2 * (1 - s) := mul_nonneg (sq_nonneg θ) (by linarith)
    have hhigh : θ ^ 2 * (1 - s) ≤ 1 * (1 - s) :=
      mul_le_mul_of_nonneg_right hθ2 (by linarith)
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hG : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun u : ℝ => ∫ θ in (0 : ℝ)..1,
        2 * θ ^ (2 * n) * Work.OddVolterra.RowIdentity.AH n h x y u (u + θ ^ 2 * (1 - u))) s :=
    Work.OddVolterra.Smooth.Alt.contDiffAt_integral_of_contDiffOn hVopen hF hseg
  have hp : ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℝ => (1 - u) ^ ((n : ℝ) + 1 / 2)) s := by
    have hne : (1 : ℝ) - s ≠ 0 := sub_ne_zero.mpr (by linarith : (1 : ℝ) ≠ s)
    exact (contDiffAt_const.sub contDiffAt_id).rpow contDiffAt_const hne
  have hprod : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun u : ℝ => (1 - u) ^ ((n : ℝ) + 1 / 2)
        * ∫ θ in (0 : ℝ)..1,
            2 * θ ^ (2 * n) * Work.OddVolterra.RowIdentity.AH n h x y u (u + θ ^ 2 * (1 - u))) s :=
    hp.mul hG
  refine hprod.congr_of_eventuallyEq ?_
  have hmin : 0 < min s (1 - s) := lt_min hs0 (by linarith)
  filter_upwards [Metric.ball_mem_nhds s hmin] with u hu
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hu
  have hu0 : 0 < u := by
    have := hu.1
    have hm : min s (1 - s) ≤ s := min_le_left _ _
    linarith
  have hu1 : u < 1 := by
    have := hu.2
    have hm : min s (1 - s) ≤ 1 - s := min_le_right _ _
    linarith
  exact Work.OddVolterra.Smooth.WWH_eq_subst n h x y hu0 hu1

/-! ## Smoothness of the centroid moment -/

/-- **`C^∞` smoothness of the centroid moment** for the envelope profile of an envelope curve:
`u ↦ momentH n h x y (envelopeProfile h x y) u` is `C^∞` on `(0,1)`.

At a slope `s ∈ (0,1)` we use the row-identity split `momentH = AAfH + WWH` on a neighbourhood of
`s`: the fixed-window part `AAfH` is smooth there by `contDiffOn_fixed_window`, and the swept part
by `contDiffAt_WWH_top`. -/
theorem contDiffOn_momentH_of_isEnvelopeCurve (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (H : Work.OddEnvelope.IsEnvelopeCurve h x y) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun u : ℝ => Work.OddVolterra.momentH n h x y
        (Work.OddEnvelope.envelopeProfile h x y) u) (Set.Ioo 0 1) := by
  intro s hs
  rw [contDiffWithinAt_iff_contDiffAt (isOpen_Ioo.mem_nhds hs)]
  let S : Work.OddVolterra.RowIdentity.Setup := envelopeSetup n hn hh H hs.1 hs.2
  have hS : s ∈ Set.Icc S.a S.c := ⟨le_rfl, le_rfl⟩
  obtain ⟨δB, hδBpos, c₀, d₀, hc₀, hc₀d₀, hd₀, hboxB⟩ :=
    Work.OddVolterra.RowIdentity.section_box S hS
  obtain ⟨δQ, hδQpos, hQrect⟩ := Work.OddVolterra.RowIdentity.Qy_Qx_rect_pos S hS
  obtain ⟨δS, hδSpos, hδSC⟩ :=
    Work.OddVolterra.Window.contDiffOn_fixed_window S.n S.hn S.hh (by
      obtain ⟨ε, hε, hε'⟩ := Work.OddVolterra.RowIdentity.Setup.Psi_window_pos S hS
      exact ⟨ε, hε, fun u hu t ht => by
        simpa [Work.OddVolterra.RowIdentity.Psi, Work.OddVolterra.line] using hε' u hu t ht⟩)
  have hs0 : 0 < s := hs.1
  have hs1 : s < 1 := hs.2
  set δ : ℝ := min (min δQ δB) (min δS (min (s / 2) ((1 - s) / 2))) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min (lt_min hδQpos hδBpos) (lt_min hδSpos (lt_min (by linarith) (by linarith)))
  have hδQ : δ ≤ δQ := by
    rw [hδdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hδB : δ ≤ δB := by
    rw [hδdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hδS : δ ≤ δS := by
    rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδs : δ ≤ s / 2 := by
    rw [hδdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ1s : δ ≤ (1 - s) / 2 := by
    rw [hδdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hδs' : δ < s := by linarith
  have hδ1s' : δ < 1 - s := by linarith
  -- positivity of the frozen endpoint factors on the box
  have hQbox : ∀ u σ : ℝ, u ∈ Set.Ioo (s - δ) (s + δ) → σ ∈ Set.Ioo (s - δ) (1 + δ) →
      0 < Work.OddVolterra.RowIdentity.QyH S.h S.y u σ ∧
      0 < Work.OddVolterra.RowIdentity.QxH S.h S.x u σ := by
    intro u σ hu hσ
    exact hQrect (u, σ)
      ⟨⟨by linarith [hu.1, hδQ], by linarith [hu.2, hδQ]⟩,
       ⟨by linarith [hσ.1, hδQ], by linarith [hσ.2, hδQ]⟩⟩
  -- smoothness of the fixed-window part
  have hfixed : ContDiffOn ℝ (⊤ : ℕ∞)
      (Work.OddVolterra.RowIdentity.AAfH S.n S.h S.f) (Set.Ioo (s - δ) (s + δ)) := by
    rw [Work.OddVolterra.RowIdentity.AAfH_eq_window S]
    exact hδSC.mono (Set.Ioo_subset_Ioo (by linarith [hδS]) (by linarith [hδS]))
  -- smoothness of the swept part
  have hWW : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun u : ℝ => Work.OddVolterra.RowIdentity.WWH S.n S.h S.x S.y u) s :=
    contDiffAt_WWH_top S.hh S.hx S.hy hs1 hδpos (by linarith)
      (fun u σ hu hσ => (hQbox u σ hu hσ).1) (fun u σ hu hσ => (hQbox u σ hu hσ).2)
  -- the eventual split `momentH = AAfH + WWH`
  have hev : (fun u : ℝ => Work.OddVolterra.momentH S.n S.h S.x S.y S.f u)
      =ᶠ[𝓝 s] (fun u : ℝ => Work.OddVolterra.RowIdentity.AAfH S.n S.h S.f u
        + Work.OddVolterra.RowIdentity.WWH S.n S.h S.x S.y u) := by
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds s hδpos) (fun u hu => ?_)
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hu
    have hu_pos : 0 < u := by linarith [hu.1, hδs, hs0]
    have hu1 : u ≤ 1 := by linarith [hu.2, hδ1s, hs1]
    refine Work.OddVolterra.RowIdentity.momentH_eq_AAH_add_WWH (c := c₀) (d := d₀) S
      hu_pos hu1 ?_ ?_ ?_ ?_ ?_
    · have hfcont : ContinuousOn S.f (Set.Icc c₀ d₀) :=
        (S.hf.continuousOn).mono (fun t ht => ⟨by linarith [ht.1, hc₀], by linarith [ht.2, hd₀]⟩)
      have hpsi : ContinuousOn (fun t : ℝ => Work.OddVolterra.psi S.h S.f u t)
          (Set.Icc c₀ d₀) := by
        unfold Work.OddVolterra.psi Work.OddVolterra.line
        exact (hfcont.pow 2).sub
          (((continuousOn_const.mul continuousOn_id).add continuousOn_const).pow 2)
      have hls : ContinuousOn (fun t : ℝ => Work.OddVolterra.lineSlope S.h u t)
          (Set.Icc c₀ d₀) := by
        unfold Work.OddVolterra.lineSlope; fun_prop
      exact ((hpsi.pow (S.n - 1)).mul hpsi.sqrt).mul hls
    · intro σ hσ
      exact hboxB σ ⟨by linarith [hσ.1, hu.1, hδB], hσ.2⟩
    · intro σ hσ
      exact S.hxy σ ⟨lt_of_lt_of_le hu_pos hσ.1.le, hσ.2⟩
    · intro σ hσ
      exact (hQbox u σ ⟨by linarith [hu.1], by linarith [hu.2]⟩
        ⟨by linarith [hσ.1, hu.1], by linarith [hσ.2]⟩).1
    · intro σ hσ
      exact (hQbox u σ ⟨by linarith [hu.1], by linarith [hu.2]⟩
        ⟨by linarith [hσ.1, hu.1], by linarith [hσ.2]⟩).2
  have hmain : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun u : ℝ => Work.OddVolterra.RowIdentity.AAfH S.n S.h S.f u
        + Work.OddVolterra.RowIdentity.WWH S.n S.h S.x S.y u) s :=
    (hfixed.contDiffAt (isOpen_Ioo.mem_nhds ⟨by linarith [hδpos], by linarith [hδpos]⟩)).add hWW
  exact hmain.congr_of_eventuallyEq hev

/-! ## The requested bridge -/

theorem contH_of_curveData (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hdata : Work.OddVolterra.CurveData n h x y) :
    Work.OddBridge.ContH n h x y :=
  contDiffOn_momentH_of_isEnvelopeCurve n hn hh
    (curveData_isEnvelopeCurve n hh hsupp hdata)

end

end Work.OddBridge
