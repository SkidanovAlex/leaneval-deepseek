import Mathlib
import Submission.Work.RHContract.Corpus
import Submission.Work.RHContract.B.Phi_secondDeriv
import Submission.Work.RHContract.B.zeta_neg_of_mem_Ioo
import Submission.Work.RHContract.B.zeta_tube
import Submission.Work.RHContract.B.double_primitive_ball

namespace Work.RHContract.B

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

private lemma convex_re_gt (θ : ℝ) : Convex ℝ {z : ℂ | θ < z.re} := by
  have hre : IsLinearMap ℝ (fun z : ℂ => z.re) := by refine ⟨?_, ?_⟩ <;> simp
  exact (convex_Ioi θ).is_linear_preimage hre

private lemma convex_re_lt (θ : ℝ) : Convex ℝ {z : ℂ | z.re < θ} := by
  have hre : IsLinearMap ℝ (fun z : ℂ => z.re) := by refine ⟨?_, ?_⟩ <;> simp
  exact (convex_Iio θ).is_linear_preimage hre

private lemma convex_im_gt (θ : ℝ) : Convex ℝ {z : ℂ | θ < z.im} := by
  have him : IsLinearMap ℝ (fun z : ℂ => z.im) := by refine ⟨?_, ?_⟩ <;> simp
  exact (convex_Ioi θ).is_linear_preimage him

private lemma convex_im_lt (θ : ℝ) : Convex ℝ {z : ℂ | z.im < θ} := by
  have him : IsLinearMap ℝ (fun z : ℂ => z.im) := by refine ⟨?_, ?_⟩ <;> simp
  exact (convex_Iio θ).is_linear_preimage him

/-- If `ζ (s+1) ≠ 0`, `s ≠ 0` and `s + 1 ≠ 0`, then `h2Closed` is analytic at `s`. -/
lemma analyticAt_h2Closed (s : ℂ) (hs0 : s ≠ 0) (hsm : s + 1 ≠ 0) (hs1 : s + 1 ≠ 1)
    (hz : riemannZeta (s + 1) ≠ 0) : AnalyticAt ℂ Landau.h2Closed s := by
  have hζ : AnalyticAt ℂ riemannZeta (s + 1) := analyticOn_riemannZeta (s+1) (by simpa using hs1)
  have hlin : AnalyticAt ℂ (fun z : ℂ => z + 1) s := by fun_prop
  have h1 : AnalyticAt ℂ (fun z : ℂ => riemannZeta (z + 1)) s :=
    (by simpa [Function.comp_def] using hζ.comp (f := fun z : ℂ => z + 1) (x := s) hlin)
  have h2 : AnalyticAt ℂ (fun z : ℂ => deriv riemannZeta (z + 1)) s :=
    (by simpa [Function.comp_def] using hζ.deriv.comp (f := fun z : ℂ => z + 1) (x := s) hlin)
  have hmem : (2:ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; left; norm_num
  have hexp : AnalyticAt ℂ (fun z : ℂ => (2:ℂ) ^ (-z)) s :=
    (analyticAt_const (v := (2:ℂ)) (x := s)).cpow analyticAt_id.neg hmem
  rw [show Landau.h2Closed = fun z : ℂ =>
      (-(deriv riemannZeta (z + 1))/riemannZeta (z + 1) - (z + 1)/z)/(z + 1)
        + (1 - (2:ℂ) ^ (-z))/z from rfl]
  exact ((((h2.neg.div h1 hz)).sub ((hlin).div analyticAt_id hs0)).div hlin hsm).add
    ((analyticAt_const.sub hexp).div analyticAt_id hs0)

/-- `h2Minus = h2Closed − h2Closed′` is analytic wherever `h2Closed` is. -/
lemma analyticAt_h2Minus (s : ℂ) (hs0 : s ≠ 0) (hsm : s + 1 ≠ 0) (hs1 : s + 1 ≠ 1)
    (hz : riemannZeta (s + 1) ≠ 0) : AnalyticAt ℂ Landau.h2Minus s := by
  have hc := analyticAt_h2Closed s hs0 hsm hs1 hz
  unfold Landau.h2Minus
  exact hc.sub hc.deriv

/-- `h2Minus` is analytic at every real point of `(−1/2, 0)`. -/
lemma analyticAt_h2Minus_real (c : ℝ) (hc1 : -(1 / 2 : ℝ) < c) (hc2 : c < 0) :
    AnalyticAt ℂ Landau.h2Minus (c : ℂ) := by
  have hcast : (c : ℂ) + 1 = ((c + 1 : ℝ) : ℂ) := by push_cast; ring
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast (ne_of_lt hc2)
  have hcm : (c : ℂ) + 1 ≠ 0 := by
    rw [hcast]; exact_mod_cast (by linarith : c + 1 ≠ 0)
  have hs1 : (c : ℂ) + 1 ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hz : riemannZeta ((c : ℂ) + 1) ≠ 0 := by
    have h := zeta_neg_of_mem_Ioo (c + 1) (by linarith) (by linarith)
    rw [hcast]; intro hzero; rw [hzero] at h; simp at h
  exact analyticAt_h2Minus (c : ℂ) hc0 hcm hs1 hz

lemma analyticAt_of_analyticOn_isOpen {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : AnalyticOn ℂ f U) {x : ℂ} (hx : x ∈ U) : AnalyticAt ℂ f x :=
  analyticWithinAt_univ.mp
    ((hf x hx).mono_of_mem_nhdsWithin (by rw [nhdsWithin_univ]; exact hU.mem_nhds hx))

lemma exists_ball_analyticOn_of_analyticAt {f : ℂ → ℂ} {c : ℂ} (h : AnalyticAt ℂ f c) :
    ∃ r > 0, AnalyticOn ℂ f (Metric.ball c r) := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt] at h
  rcases Metric.mem_nhds_iff.mp h with ⟨r, hr, hball⟩
  exact ⟨r, hr, (Complex.analyticOn_iff_differentiableOn Metric.isOpen_ball).mpr
    (fun z hz => (hball hz).differentiableWithinAt)⟩

/-- The bridging region. -/
def bridge (c δ : ℝ) : Set ℂ :=
  {s : ℂ | c < s.re ∧ 0 < s.im ∧ s.im < δ} ∪
    {s : ℂ | c < s.re ∧ s.re < 0 ∧ -δ < s.im ∧ s.im < δ}

lemma isOpen_bridge (c δ : ℝ) : IsOpen (bridge c δ) := by
  unfold bridge
  refine IsOpen.union ?_ ?_
  · exact (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const))
  · exact (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        ((isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const)))

lemma convex_bridgeA (c δ : ℝ) : Convex ℝ {s : ℂ | c < s.re ∧ 0 < s.im ∧ s.im < δ} := by
  have h1 : {s : ℂ | c < s.re ∧ 0 < s.im ∧ s.im < δ}
      = ({s : ℂ | c < s.re} ∩ {s : ℂ | 0 < s.im}) ∩ {s : ℂ | s.im < δ} := by
    ext s; simp only [mem_inter_iff, mem_ofPred_eq]; tauto
  rw [h1]
  exact ((convex_re_gt c).inter (convex_im_gt 0)).inter (convex_im_lt δ)

lemma convex_bridgeB (c δ : ℝ) :
    Convex ℝ {s : ℂ | c < s.re ∧ s.re < 0 ∧ -δ < s.im ∧ s.im < δ} := by
  have h1 : {s : ℂ | c < s.re ∧ s.re < 0 ∧ -δ < s.im ∧ s.im < δ}
      = ({s : ℂ | c < s.re} ∩ {s : ℂ | s.re < 0})
        ∩ ({s : ℂ | -δ < s.im} ∩ {s : ℂ | s.im < δ}) := by
    ext s; simp only [mem_inter_iff, mem_ofPred_eq]; tauto
  rw [h1]
  exact ((convex_re_gt c).inter (convex_re_lt 0)).inter
    ((convex_im_gt (-δ)).inter (convex_im_lt δ))

lemma isPreconnected_bridge (c δ : ℝ) (hδ : 0 < δ) (hc : c < 0) :
    IsPreconnected (bridge c δ) := by
  unfold bridge
  have hA : IsPreconnected {s : ℂ | c < s.re ∧ 0 < s.im ∧ s.im < δ} :=
    (convex_bridgeA c δ).isPreconnected
  have hB : IsPreconnected {s : ℂ | c < s.re ∧ s.re < 0 ∧ -δ < s.im ∧ s.im < δ} :=
    (convex_bridgeB c δ).isPreconnected
  set x : ℂ := ((c / 2 : ℝ) : ℂ) + ((δ / 2 : ℝ) : ℂ) * Complex.I with hx
  have hxre : x.re = c / 2 := by simp [hx]
  have hxim : x.im = δ / 2 := by simp [hx]
  refine IsPreconnected.union x ?_ ?_ hA hB
  · exact ⟨by rw [hxre]; linarith, by rw [hxim]; linarith, by rw [hxim]; linarith⟩
  · exact ⟨by rw [hxre]; linarith, by rw [hxre]; linarith,
      by rw [hxim]; linarith, by rw [hxim]; linarith⟩

lemma bridge_sub_re {c δ : ℝ} {s : ℂ} (hs : s ∈ bridge c δ) : c < s.re := by
  rcases hs with ⟨h, _⟩ | ⟨h, _⟩
  · exact h
  · exact h

/-- `h2Minus` is analytic on the bridging region, provided ζ has no zeros in the thin strip
`{c+1 ≤ Re w ≤ 1, |Im w| < δ}` away from the pole at `w = 1`. -/
lemma analyticOn_h2Minus_bridge (c δ : ℝ) (hδ : 0 < δ) (hc1 : -(1 / 2 : ℝ) < c)
    (htube : ∀ w : ℂ, c + 1 ≤ w.re → w.re ≤ 1 → w ≠ 1 → |w.im| < δ →
      riemannZeta w ≠ 0) :
    AnalyticOn ℂ Landau.h2Minus (bridge c δ) := by
  intro s hs
  refine AnalyticAt.analyticWithinAt ?_
  have hlin1 : (s + 1).re = s.re + 1 := by simp
  have hlin2 : (s + 1).im = s.im := by simp
  rcases hs with ⟨hcre, him0, himδ⟩ | ⟨hcre, hre0, hδ1, hδ2⟩
  · have hs0 : s ≠ 0 := by intro h; rw [h] at him0; simp at him0
    have hs1 : s + 1 ≠ 1 := by intro h; exact hs0 (by linear_combination h)
    have hsm : s + 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hz : riemannZeta (s + 1) ≠ 0 := by
      by_cases h : 0 ≤ s.re
      · exact riemannZeta_ne_zero_of_one_le_re (by rw [hlin1]; linarith)
      · push_neg at h
        refine htube (s + 1) (by rw [hlin1]; linarith) (by rw [hlin1]; linarith) hs1 ?_
        rw [hlin2, abs_of_pos him0]; exact himδ
    exact analyticAt_h2Minus s hs0 hsm hs1 hz
  · have hs0 : s ≠ 0 := by intro h; rw [h] at hre0; simp at hre0
    have hs1 : s + 1 ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hsm : s + 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hz : riemannZeta (s + 1) ≠ 0 := by
      refine htube (s + 1) (by rw [hlin1]; linarith) (by rw [hlin1]; linarith) hs1 ?_
      rw [hlin2, abs_lt]; exact ⟨hδ1, hδ2⟩
    exact analyticAt_h2Minus s hs0 hsm hs1 hz

/-- The identity theorem in the special case needed here (field `ℂ` fixed by hand, so that
type-class inference does not have to choose between `ℂ` and `ℝ`). -/
private lemma analytic_eqOn_of_preconnected (f g : ℂ → ℂ) {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U) (hU : IsPreconnected U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hfg : f =ᶠ[𝓝 z₀] g) : EqOn f g U :=
  AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hf hg hU hz₀ hfg

theorem continuation_neg (c : ℝ) (hc1 : -(1 / 2 : ℝ) < c) (hc2 : c < 0)
    (H : ℂ → ℂ) (hH : AnalyticOn ℂ H {s : ℂ | c < s.re})
    (hHΦ : ∀ s : ℂ, 0 < s.re → H s = Work.RHContract.Landau.Phi s) :
    ∃ r : ℝ, 0 < r ∧ ∃ Φtilde : ℂ → ℂ,
      AnalyticOn ℂ Φtilde (Metric.ball (c : ℂ) r) ∧
      ∀ s : ℂ, c < s.re → Φtilde s = H s := by
  classical
  obtain ⟨δ, hδpos, htube⟩ := zeta_tube c hc1 hc2
  obtain ⟨r₁, hr₁pos, hr₁⟩ := exists_ball_analyticOn_of_analyticAt (analyticAt_h2Minus_real c hc1 hc2)
  set r : ℝ := min (min r₁ δ) (-c) / 2 with hrdef
  have hrpos : 0 < r := by
    rw [hrdef]
    exact div_pos (lt_min (lt_min hr₁pos hδpos) (by linarith)) (by norm_num)
  have hr_le_r₁ : r ≤ r₁ := by
    rw [hrdef]
    have h1 : min (min r₁ δ) (-c) ≤ r₁ := le_trans (min_le_left _ _) (min_le_left _ _)
    nlinarith [hr₁pos]
  have hr_le_δ : r ≤ δ := by
    rw [hrdef]
    have h1 : min (min r₁ δ) (-c) ≤ δ := le_trans (min_le_left _ _) (min_le_right _ _)
    nlinarith [hδpos]
  have hr_lt : r < -c := by
    rw [hrdef]
    have h1 : min (min r₁ δ) (-c) ≤ -c := min_le_right _ _
    nlinarith [hc2]
  have hr_an : AnalyticOn ℂ Landau.h2Minus (Metric.ball (c:ℂ) r) :=
    hr₁.mono (Metric.ball_subset_ball hr_le_r₁)
  set U : Set ℂ := bridge c δ with hUdef
  have hUopen : IsOpen U := isOpen_bridge c δ
  have hUpre : IsPreconnected U := isPreconnected_bridge c δ hδpos hc2
  set z₀ : ℂ := ((1 / 2 : ℝ) : ℂ) + ((δ / 2 : ℝ) : ℂ) * Complex.I with hz₀def
  have hz₀ : z₀ ∈ U := by
    rw [hUdef, hz₀def]
    refine Or.inl ⟨?_, ?_, ?_⟩ <;> simp <;> linarith
  have hPhi2 : ∀ w : ℂ, 0 < w.re → deriv (deriv H) w = Landau.h2Minus w := by
    intro w hw
    have hQ : ∀ᶠ z in 𝓝 w, 0 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw
    have h2 : deriv H =ᶠ[𝓝 w] deriv Landau.Phi := by
      filter_upwards [hQ] with z hz
      have hzQ : ∀ᶠ z' in 𝓝 z, 0 < z'.re :=
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
      have hzQ' : H =ᶠ[𝓝 z] Landau.Phi := hzQ.mono (fun z' hz' => hHΦ z' hz')
      exact hzQ'.deriv_eq
    rw [h2.deriv_eq, Phi_secondDeriv w hw]
  have hEqU : EqOn (deriv (deriv H)) Landau.h2Minus U := by
    refine analytic_eqOn_of_preconnected (deriv (deriv H)) Landau.h2Minus ?_ ?_ hUpre hz₀ ?_
    · intro z hz
      exact ((analyticAt_of_analyticOn_isOpen
        (isOpen_lt continuous_const Complex.continuous_re) hH (bridge_sub_re hz)).deriv).deriv
    · exact (hUopen.analyticOn_iff_analyticOnNhd).mp
        (analyticOn_h2Minus_bridge c δ hδpos hc1 htube)
    · have hz₀Q : ∀ᶠ z in 𝓝 z₀, 0 < z.re :=
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by rw [hz₀def]; simp)
      filter_upwards [hz₀Q] with z hz
      exact hPhi2 z hz
  have hsU : ∀ z ∈ (Metric.ball (c:ℂ) r ∩ {z : ℂ | c < z.re}), z ∈ U := by
    intro z hz
    obtain ⟨hzball, hzre⟩ := hz
    have hzb : ‖z - (c:ℂ)‖ < r := by
      rw [Metric.mem_ball, Complex.dist_eq] at hzball; exact hzball
    rw [hUdef]
    refine Or.inr ⟨hzre, ?_, ?_, ?_⟩
    · have h1 : |z.re - c| ≤ ‖z - c‖ := by
        have h := Complex.abs_re_le_norm (z - c); simpa using h
      have h2 : z.re - c < r := lt_of_le_of_lt (le_trans (le_abs_self _) h1) hzb
      linarith
    · have h1 : |z.im| ≤ ‖z - c‖ := by
        have h := Complex.abs_im_le_norm (z - c); simpa using h
      exact (abs_lt.mp (lt_of_lt_of_le (lt_of_le_of_lt h1 hzb) hr_le_δ)).1
    · have h1 : |z.im| ≤ ‖z - c‖ := by
        have h := Complex.abs_im_le_norm (z - c); simpa using h
      exact (abs_lt.mp (lt_of_lt_of_le (lt_of_le_of_lt h1 hzb) hr_le_δ)).2
  set a : ℂ := ((c + r / 2 : ℝ) : ℂ) with hadef
  have ha_re : a.re = c + r / 2 := by rw [hadef]; simp
  have ha : a ∈ Metric.ball (c:ℂ) r := by
    rw [Metric.mem_ball, Complex.dist_eq]
    have h : a - (c:ℂ) = ((r / 2 : ℝ) : ℂ) := by rw [hadef]; push_cast; ring
    rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < r / 2)]
    linarith
  have haP : c < a.re := by rw [ha_re]; linarith
  obtain ⟨P, hPan, hPa, hPda, hP2⟩ :=
    double_primitive_ball Landau.h2Minus (c:ℂ) r hr_an a ha (H a) (deriv H a)
  set s : Set ℂ := Metric.ball (c:ℂ) r ∩ {z : ℂ | c < z.re} with hsdef
  have hsopen : IsOpen s := Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hsconv : Convex ℝ s := (convex_ball (c:ℂ) r).inter (convex_re_gt c)
  have ha_mem : a ∈ s := ⟨ha, haP⟩
  have hPH : ∀ z ∈ s, P z = H z := by
    intro z hz
    have hd2 : ∀ w ∈ s, deriv (deriv (P - H)) w = 0 := by
      intro w hw
      have hwU : w ∈ U := hsU w hw
      have haneq : deriv (P - H) =ᶠ[𝓝 w] deriv P - deriv H := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hw.1,
          (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw.2] with u hu1 hu2
        exact deriv_sub
          ((analyticAt_of_analyticOn_isOpen Metric.isOpen_ball hPan hu1).differentiableAt)
          ((analyticAt_of_analyticOn_isOpen
            (isOpen_lt continuous_const Complex.continuous_re) hH hu2).differentiableAt)
      rw [haneq.deriv_eq]
      rw [deriv_sub
        (((analyticAt_of_analyticOn_isOpen Metric.isOpen_ball hPan hw.1).deriv).differentiableAt)
        (((analyticAt_of_analyticOn_isOpen
          (isOpen_lt continuous_const Complex.continuous_re) hH hw.2).deriv).differentiableAt)]
      rw [hP2 w hw.1, hEqU hwU]
      ring
    have hdiff1 : DifferentiableOn ℂ (deriv (P - H)) s := by
      intro w hw
      exact (((analyticAt_of_analyticOn_isOpen Metric.isOpen_ball hPan hw.1).sub
        (analyticAt_of_analyticOn_isOpen
          (isOpen_lt continuous_const Complex.continuous_re) hH hw.2)).deriv).differentiableAt.differentiableWithinAt
    have hconst1 : ∀ y ∈ s, deriv (P - H) y = deriv (P - H) a := fun y hy =>
      IsOpen.is_const_of_deriv_eq_zero hsopen hsconv.isPreconnected hdiff1
        (fun w hw => hd2 w hw) hy ha_mem
    have hderiv0 : EqOn (deriv (P - H)) 0 s := by
      intro w hw
      have hsub : deriv (P - H) a = deriv P a - deriv H a :=
        deriv_sub ((analyticAt_of_analyticOn_isOpen Metric.isOpen_ball hPan ha).differentiableAt)
          ((analyticAt_of_analyticOn_isOpen
            (isOpen_lt continuous_const Complex.continuous_re) hH haP).differentiableAt)
      rw [hconst1 w hw, hsub, hPda]
      simp only [Pi.zero_apply]
      ring
    have hdiff0 : DifferentiableOn ℂ (P - H) s := by
      intro w hw
      exact ((analyticAt_of_analyticOn_isOpen Metric.isOpen_ball hPan hw.1).sub
        (analyticAt_of_analyticOn_isOpen
          (isOpen_lt continuous_const Complex.continuous_re) hH hw.2)).differentiableAt.differentiableWithinAt
    have hconst0 : (P - H) z = (P - H) a :=
      IsOpen.is_const_of_deriv_eq_zero hsopen hsconv.isPreconnected hdiff0 hderiv0 hz ha_mem
    have hz0 : (P - H) z = 0 := by
      rw [hconst0]
      show P a - H a = 0
      rw [hPa]; ring
    have hz1 : P z - H z = 0 := by simpa only [Pi.sub_apply] using hz0
    exact sub_eq_zero.mp hz1
  set Φtilde : ℂ → ℂ := fun z => if c < z.re then H z else P z with hΦdef
  refine ⟨r, hrpos, Φtilde, ?_, ?_⟩
  · intro z hz
    have hPz : AnalyticAt ℂ P z := analyticAt_of_analyticOn_isOpen Metric.isOpen_ball hPan hz
    have heq : P =ᶠ[𝓝 z] Φtilde := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
      rw [hΦdef]
      by_cases h : c < w.re
      · simp only [h, if_true]
        exact hPH w ⟨hw, h⟩
      · simp only [h, if_false]
    exact (AnalyticAt.congr hPz heq).analyticWithinAt
  · intro z hz
    rw [hΦdef]
    simp only [hz, if_true]

end

end Work.RHContract.B
