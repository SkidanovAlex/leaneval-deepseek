import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddEnvelope.Defs
import Submission.Work.OddEnvelope.Main
import Submission.Work.OddEnvelope.NonDegenerate
import Submission.Work.OddVolterra.RowIdentity.Basic
import Submission.Work.OddVolterra.RowIdentity.contDiffAt_AA
import Submission.Work.OddVolterra.RowIdentity.contDiffAt_WW
import Submission.Work.OddVolterra.RowIdentity.Qy_Qx_rect_pos
import Submission.Work.OddVolterra.RowIdentity.section_box
import Submission.Work.OddVolterra.RowIdentity.momentF_eq_AA_add_WW
import Submission.Work.OddVolterra.Smooth.Qy_pos_of_isEnvelopeCurve
import Submission.Work.OddVolterra.Smooth.contDiffAt_AA_top
import Submission.Work.OddVolterra.Smooth.contDiffAt_WW_top

/-!
# Smoothness of the first moment expression of the odd case

The first moment expression of Ryabogin's transition-slope argument is

`u ↦ momentF n h x y (envelopeProfile h x y) u - momentRHS n u`,

the integral of `ψ^{n+1/2}` over the section `(-x u, y u)` of the envelope profile, minus the
right-hand side `C/√(1+u²)` of the ball.  We prove here that it is `C^∞` on `(0,1)`.

The proof has three inputs, all of them already available in the workspace:

* the setup of the odd row identity (`Work.OddVolterra.RowIdentity.Setup`) built from the envelope
  curve `IsEnvelopeCurve h x y`;
* the smoothness of the two pieces of the split `momentF = AA + WW`
  (`Work.OddVolterra.RowIdentity.contDiffAt_AA`, `..._WW`, upgraded to `C^∞` here);
* the split itself, `Work.OddVolterra.RowIdentity.momentF_eq_AA_add_WW`.
-/

namespace Work.OddVolterra.Smooth

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

variable {h x y : ℝ → ℝ}

/-! ## The perturbation is globally smooth -/

/-- The perturbation `h` of an envelope curve is smooth on all of `ℝ`: it is smooth on `(0,∞)`
and supported in `[1-2τ, 1-τ]`, a compact interval in the interior of `(0,∞)`. -/
theorem momentFSub_contDiff_h (H : Work.OddEnvelope.IsEnvelopeCurve h x y) :
    ContDiff ℝ (⊤ : ℕ∞) h := by
  rw [contDiff_iff_contDiffAt]
  intro t
  rcases lt_or_ge 0 t with ht | ht
  · simpa using (H.smooth_h.contDiffAt (isOpen_Ioi.mem_nhds ht))
  · have hnot : t ∉ tsupport h := by
      intro hmem
      have h1 : t ∈ Set.Icc (1 - 2 * Work.OddEnvelope.tau) (1 - Work.OddEnvelope.tau) :=
        closure_minimal H.h_support isClosed_Icc hmem
      have h2 : (0 : ℝ) < 1 - 2 * Work.OddEnvelope.tau := Work.OddEnvelope.one_sub_two_tau_pos
      linarith [h1.1]
    have hev : h =ᶠ[𝓝 t] 0 := notMem_tsupport_iff_eventuallyEq.mp hnot
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev

/-! ## The two semicircle functions and the two chord functions agree

`Work.OddEnvelope` and `Commons.Geometry.Ulam` define `profileX` and `semicircle` by the same
formulas; the two definitions are interchangeable (they unfold to the same term). -/

@[simp] lemma momentFSub_oddEnvelope_profileX_eq (t : ℝ) :
    Work.OddEnvelope.profileX t = Commons.Geometry.Ulam.profileX t := rfl

@[simp] lemma momentFSub_oddEnvelope_semicircle_eq (t : ℝ) :
    Work.OddEnvelope.semicircle t = Commons.Geometry.Ulam.semicircle t := rfl

/-- The unperturbed half-width `tStar` of the profile is strictly larger than `profileX 1`: the
chord function is strictly decreasing and `1 - τ < 1`. -/
lemma momentFSub_profileX_one_lt_tStar : Commons.Geometry.Ulam.profileX 1 < Work.OddEnvelope.tStar := by
  have h1 : (0 : ℝ) < 1 - Work.OddEnvelope.tau := Work.OddEnvelope.one_sub_tau_pos
  have h2 : 1 - Work.OddEnvelope.tau < 1 := by
    have := Work.OddEnvelope.tau_pos; linarith
  have h3 : Work.OddEnvelope.profileX 1 < Work.OddEnvelope.profileX (1 - Work.OddEnvelope.tau) :=
    Work.OddEnvelope.profileX_strictAntiOn h1 (by norm_num) h2
  simpa [Work.OddEnvelope.tStar] using h3

/-! ## The middle radicand is positive -/

/-- On the middle window `(-profileX 1, profileX 1)` the envelope profile is the semicircle, so
the radicand of the semicircle is the radicand of the profile, which is positive. -/
theorem momentFSub_psi_semicircle_pos (H : Work.OddEnvelope.IsEnvelopeCurve h x y)
    {s t : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (ht : t ∈ Set.Ioo (-(Commons.Geometry.Ulam.profileX 1))
      (Commons.Geometry.Ulam.profileX 1)) :
    0 < Work.OddVolterra.psi h Commons.Geometry.Ulam.semicircle s t := by
  have htau : 1 - Work.OddEnvelope.tau ≤ (1 : ℝ) := by
    have := Work.OddEnvelope.tau_pos; linarith
  have hstar : t ∈ Set.Ioo (-(Work.OddEnvelope.tStar)) (Work.OddEnvelope.tStar) :=
    ⟨by linarith [ht.1, momentFSub_profileX_one_lt_tStar], by linarith [ht.2, momentFSub_profileX_one_lt_tStar]⟩
  have hfsemi : Work.OddEnvelope.envelopeProfile h x y t
      = Commons.Geometry.Ulam.semicircle t := by
    rw [Work.OddEnvelope.envelopeProfile_eq_semicircle H hstar]
    rfl
  have htail_x : x 1 = Commons.Geometry.Ulam.profileX 1 := by
    rw [H.x_tail 1 htau]; rfl
  have htail_y : y 1 = Commons.Geometry.Ulam.profileX 1 := by
    rw [H.y_tail 1 htau]; rfl
  have hone : (1 : ℝ) ∈ Set.Ioi 0 := by norm_num
  have hx1 : Commons.Geometry.Ulam.profileX 1 ≤ x s := by
    rw [← htail_x]
    rcases lt_or_eq_of_le hs1 with hlt | heq
    · exact (H.toChordCurve_x.strictAntiOn hs hone hlt).le
    · rw [heq]
  have hy1 : Commons.Geometry.Ulam.profileX 1 ≤ y s := by
    rw [← htail_y]
    rcases lt_or_eq_of_le hs1 with hlt | heq
    · exact (H.toChordCurve_y.strictAntiOn hs hone hlt).le
    · rw [heq]
  have hmem : t ∈ Set.Ioo (-(x s)) (y s) := ⟨by linarith [ht.1, hx1], by linarith [ht.2, hy1]⟩
  have hpos := Work.OddEnvelope.envelopeProfile_sub_sq_pos H
    (Work.OddEnvelope.concaveOn_envelopeProfile H) hs t hmem
  have hcongr : Work.OddVolterra.psi h (Work.OddEnvelope.envelopeProfile h x y) s t
      = Work.OddVolterra.psi h Commons.Geometry.Ulam.semicircle s t := by
    unfold Work.OddVolterra.psi Work.OddVolterra.line
    rw [hfsemi]
  rw [← hcongr]
  exact hpos


/-! ## The setup of the odd row identity from an envelope curve -/

/-- `x 1 = profileX 1`: beyond the perturbation window the curve is the semicircle. -/
lemma momentFSub_x_one_eq (H : Work.OddEnvelope.IsEnvelopeCurve h x y) :
    x 1 = Commons.Geometry.Ulam.profileX 1 := by
  rw [H.x_tail 1 (by have := Work.OddEnvelope.tau_pos; linarith)]
  rfl

/-- `y 1 = profileX 1`. -/
lemma momentFSub_y_one_eq (H : Work.OddEnvelope.IsEnvelopeCurve h x y) :
    y 1 = Commons.Geometry.Ulam.profileX 1 := by
  rw [H.y_tail 1 (by have := Work.OddEnvelope.tau_pos; linarith)]
  rfl

/-- The `Setup` of the odd row-identity chapter, produced from an envelope curve at a single
slope `s ∈ (0,1)` (so that `a = c = s`). -/
noncomputable def momentFSub_setup (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    Work.OddVolterra.RowIdentity.Setup where
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
  hh := momentFSub_contDiff_h H
  hx := H.smooth_x
  hy := H.smooth_y
  hf := Work.OddEnvelope.envelopeProfile_contDiffOn H
  hxy := fun u hu => ⟨Work.OddEnvelope.envelopeProfile_root_right H hu.1,
    Work.OddEnvelope.envelopeProfile_root_left H hu.1⟩
  hxdec := fun σ hσ => (H.x_deriv_neg σ (lt_trans hs hσ.1)).le
  hydec := fun σ hσ => (H.y_deriv_neg σ (lt_trans hs hσ.1)).le
  hxb := momentFSub_x_one_eq H
  hyb := momentFSub_y_one_eq H
  hfb := fun t ht => by
    have hstar : t ∈ Set.Ioo (-(Work.OddEnvelope.tStar)) (Work.OddEnvelope.tStar) :=
      ⟨by linarith [ht.1, momentFSub_profileX_one_lt_tStar], by linarith [ht.2, momentFSub_profileX_one_lt_tStar]⟩
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
    rw [momentFSub_x_one_eq H, momentFSub_y_one_eq H]
    linarith [show (0 : ℝ) < Commons.Geometry.Ulam.profileX 1 from Work.OddEnvelope.profileX_pos 1]
  hint := fun σ hσ => by
    have hσ0 : 0 < σ := lt_of_lt_of_le hs hσ.1
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · have := H.toChordCurve_x.lt_one hσ0; linarith
    · have := H.toChordCurve_x.pos hσ0; linarith
    · have := H.toChordCurve_y.pos hσ0; linarith
    · have := H.toChordCurve_y.lt_one hσ0; linarith
  hKden := fun u σ hu huσ hσ1 => Qy_pos_of_isEnvelopeCurve H u σ (lt_of_lt_of_le hs hu) huσ hσ1
  hmid := fun σ hσ t ht =>
    momentFSub_psi_semicircle_pos H (lt_of_lt_of_le hs hσ.1) hσ.2 ht

/-! ## Smoothness of the right-hand side -/

lemma momentFSub_contDiff_momentRHS (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (momentRHS n) := by
  unfold momentRHS
  refine ContDiff.div contDiff_const ?_ ?_
  · refine ContDiff.sqrt (contDiff_const.add (contDiff_id.pow 2)) ?_
    intro s; positivity
  · intro s; positivity


/-! ## The main theorem -/

theorem contDiffOn_momentF_sub (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun u : ℝ => Work.OddVolterra.momentF n h x y
        (Work.OddEnvelope.envelopeProfile h x y) u - Work.OddVolterra.momentRHS n u)
      (Set.Ioo 0 1) := by
  intro s hs
  rw [contDiffWithinAt_iff_contDiffAt (isOpen_Ioo.mem_nhds hs)]
  -- the setup of the row identity at the slope `s`
  let S : Work.OddVolterra.RowIdentity.Setup := momentFSub_setup n hn H hs.1 hs.2
  have hS : s ∈ Set.Icc S.a S.c := ⟨le_rfl, le_rfl⟩
  obtain ⟨δ, hδpos, c₀, d₀, hc₀, hc₀d₀, hd₀, hbox⟩ :=
    Work.OddVolterra.RowIdentity.section_box S hS
  obtain ⟨δQ, hδQpos, hQrect⟩ := Work.OddVolterra.RowIdentity.Qy_Qx_rect_pos S hS
  have hAA : ContDiffAt ℝ (⊤ : ℕ∞) (Work.OddVolterra.RowIdentity.AA n h) s :=
    contDiffAt_AA_top S hS
  have hWW : ContDiffAt ℝ (⊤ : ℕ∞) (Work.OddVolterra.RowIdentity.WW n h x y) s :=
    contDiffAt_WW_top S hS hδQpos (fun q hq => (hQrect q hq).1) (fun q hq => (hQrect q hq).2)
  have hRHS : ContDiffAt ℝ (⊤ : ℕ∞) (Work.OddVolterra.momentRHS n) s :=
    (momentFSub_contDiff_momentRHS n).contDiffAt
  -- the split `momentF = AA + WW` holds near `s`
  have hsplit : (fun u : ℝ => Work.OddVolterra.RowIdentity.AA n h u
        + Work.OddVolterra.RowIdentity.WW n h x y u)
      =ᶠ[𝓝 s] (fun u : ℝ => Work.OddVolterra.momentF n h x y
        (Work.OddEnvelope.envelopeProfile h x y) u) := by
    have hε : 0 < min δ (min s (1 - s)) :=
      lt_min hδpos (lt_min hs.1 (by linarith [hs.2]))
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds s hε) (fun u hu => ?_)
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hu
    have hεδ : min δ (min s (1 - s)) ≤ δ := min_le_left _ _
    have hεs : min δ (min s (1 - s)) ≤ s :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    have hε1s : min δ (min s (1 - s)) ≤ 1 - s :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    have hu_pos : 0 < u := by linarith [hu.1]
    have hu1 : u ≤ 1 := by linarith [hu.2]
    have hfx : Work.OddEnvelope.envelopeProfile h x y = S.f := rfl
    have hfcont : ContinuousOn (Work.OddEnvelope.envelopeProfile h x y) (Set.Icc c₀ d₀) :=
      (Work.OddEnvelope.envelopeProfile_contDiffOn H).continuousOn.mono
        (fun t ht => ⟨by linarith [ht.1, hc₀], by linarith [ht.2, hd₀]⟩)
    have hpsi : ContinuousOn
        (fun t : ℝ => Work.OddVolterra.psi h (Work.OddEnvelope.envelopeProfile h x y) u t)
        (Set.Icc c₀ d₀) := by
      unfold Work.OddVolterra.psi Work.OddVolterra.line
      exact (hfcont.pow 2).sub
        (((continuousOn_const.mul continuousOn_id).add continuousOn_const).pow 2)
    have hc : ContinuousOn
        (Work.OddVolterra.momentIntegrand n h (Work.OddEnvelope.envelopeProfile h x y) u)
        (Set.Icc c₀ d₀) :=
      (hpsi.pow n).mul hpsi.sqrt
    have hbox' : ∀ σ ∈ Set.Icc u 1, c₀ < -(S.x σ) ∧ -(S.x σ) ≤ d₀ ∧
        c₀ ≤ S.y σ ∧ S.y σ < d₀ :=
      fun σ hσ => hbox σ ⟨by linarith [hσ.1], hσ.2⟩
    have henv : ∀ σ ∈ Set.Ioc u 1,
        S.f (S.y σ) = σ * S.y σ + S.h σ ∧ S.f (-(S.x σ)) = -(σ * (-(S.x σ)) + S.h σ) :=
      fun σ hσ => ⟨Work.OddEnvelope.envelopeProfile_root_right H (lt_trans hu_pos hσ.1),
        Work.OddEnvelope.envelopeProfile_root_left H (lt_trans hu_pos hσ.1)⟩
    have hQy : ∀ σ ∈ Set.Icc u 1, 0 < Work.OddVolterra.RowIdentity.Qy S.h S.y u σ :=
      fun σ hσ => (Qy_pos_of_isEnvelopeCurve H u σ hu_pos hσ.1 hσ.2).1
    have hQx : ∀ σ ∈ Set.Icc u 1, 0 < Work.OddVolterra.RowIdentity.Qx S.h S.x u σ :=
      fun σ hσ => (Qy_pos_of_isEnvelopeCurve H u σ hu_pos hσ.1 hσ.2).2
    exact (Work.OddVolterra.RowIdentity.momentF_eq_AA_add_WW S hu_pos hu1 hc hbox' henv
      hQy hQx).symm
  -- conclude
  have hmain : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun u : ℝ => Work.OddVolterra.RowIdentity.AA n h u
        + Work.OddVolterra.RowIdentity.WW n h x y u - Work.OddVolterra.momentRHS n u) s :=
    (hAA.add hWW).sub hRHS
  refine hmain.congr_of_eventuallyEq ?_
  filter_upwards [hsplit] with u hu
  rw [← hu]



end

end Work.OddVolterra.Smooth
