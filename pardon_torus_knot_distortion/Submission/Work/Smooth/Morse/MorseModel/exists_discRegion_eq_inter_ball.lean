import Mathlib
import Submission.Work.Smooth.Morse.Defs
import Submission.Work.Smooth.Morse.Immersion
import Submission.Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen
import Submission.Work.SurgeryInvariance.API
import Submission.Work.Smooth.Morse.MorseModel.exists_lower_bound_of_injective
import Submission.Work.Smooth.Morse.MorseModel.exists_disc_param_of_chart

/-!
# A small Euclidean ball of the surface is an embedded disc

For `ψ : Submission.Diffeo` let `F = ψ(S¹×S¹)` be the surface of the challenge, a smoothly
embedded torus.  This file proves `Work.Smooth.Morse.MorseModel.exists_discRegion_eq_inter_ball`:
**every point `x` of `F` has a Euclidean ball `B(x,δ)` whose trace on `F` is the carrier of an
embedded disc of the surface**, whose interior contains `x`.

The proof is a local computation at a parameter point `p` with `param ψ p = x`:

* `param ψ` is a `C^∞` immersion, so at `p` its derivative `A₀` is injective; picking a linear
  isomorphism `Φ z = (z.re, z.im)` we get a positive lower bound `c₀` for `A₀ = fderiv param p ∘ Φ`;
* the chart `u_s z = param ψ (p + s • Φ z)` of the surface at scale `s` therefore has
  `‖fderiv u_s z - fderiv u_s 0‖ ≤ s c₀ / 4` on the unit disc, once `s` is small enough (the
  derivative of `param ψ` is continuous at `p`);
* the radial lemma `exists_disc_param_of_chart` then realises the trace of a small Euclidean ball
  on the chart as the image of the closed unit disc;
* finally, the trace `param ψ '' U` of a small *parameter* ball `U` around `p` is open in the
  compact surface `F`, so it contains the whole trace of some Euclidean ball around `x`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.Morse.MorseModel

noncomputable section

/-! ## The identification `ℂ ≅ ℝ²` -/

/-- The continuous linear map `z ↦ (z.re, z.im)`, identifying the plane of the parameter domain
with the field of complex numbers. -/
def phiL : ℂ →L[ℝ] ℝ × ℝ := Complex.reCLM.prod Complex.imCLM

@[simp] theorem phiL_apply (z : ℂ) : phiL z = (z.re, z.im) := rfl

theorem phiL_injective : Function.Injective phiL := fun z w h => by
  have h1 : z.re = w.re := congrArg Prod.fst h
  have h2 : z.im = w.im := congrArg Prod.snd h
  exact Complex.ext h1 h2

theorem phiL_ne_zero : phiL ≠ 0 := by
  intro h
  have h1 : phiL 1 = (0 : ℝ × ℝ) := by rw [h]; rfl
  rw [phiL_apply, Complex.one_re, Complex.one_im] at h1
  exact one_ne_zero (congrArg Prod.fst h1)

theorem phiL_norm_pos : 0 < ‖phiL‖ := norm_pos_iff.mpr phiL_ne_zero

/-! ## The scaled chart of the surface at a parameter point -/

/-- The chart of the surface `F = ψ(S¹×S¹)` at the parameter point `p`, scaled by `s > 0`:
`z ↦ param ψ (p + s • (z.re, z.im))`.  Its image is the trace on `F` of the Euclidean ball of
radius `s` around `p` in the parameter plane. -/
def chart (ψ : Submission.Diffeo) (p : ℝ × ℝ) (s : ℝ) : ℂ → R3 :=
  fun z => Work.Smooth.Morse.param ψ (p + s • phiL z)

theorem chart_apply (ψ : Submission.Diffeo) (p : ℝ × ℝ) (s : ℝ) (z : ℂ) :
    chart ψ p s z = Work.Smooth.Morse.param ψ (p + s • phiL z) := rfl

@[simp] theorem chart_zero (ψ : Submission.Diffeo) (p : ℝ × ℝ) (s : ℝ) :
    chart ψ p s 0 = Work.Smooth.Morse.param ψ p := by
  show Work.Smooth.Morse.param ψ (p + s • phiL (0 : ℂ)) = Work.Smooth.Morse.param ψ p
  congr 1
  rw [phiL_apply]
  ext <;> simp

theorem chart_continuous (ψ : Submission.Diffeo) (p : ℝ × ℝ) (s : ℝ) :
    Continuous (chart ψ p s) :=
  (Work.Smooth.Morse.param_continuous ψ).comp (by fun_prop)

theorem chart_contDiff (ψ : Submission.Diffeo) (p : ℝ × ℝ) (s : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chart ψ p s) :=
  (Work.Smooth.Morse.param_contDiff ψ).comp (by fun_prop)

theorem fderiv_chart (ψ : Submission.Diffeo) (p : ℝ × ℝ) (s : ℝ) (z : ℂ) :
    fderiv ℝ (chart ψ p s) z =
      (fderiv ℝ (Work.Smooth.Morse.param ψ) (p + s • phiL z)).comp (s • phiL) := by
  have hg : HasFDerivAt (fun z : ℂ => p + s • phiL z) (s • phiL) z :=
    ((s • phiL).hasFDerivAt).const_add p
  have hp : HasFDerivAt (Work.Smooth.Morse.param ψ)
      (fderiv ℝ (Work.Smooth.Morse.param ψ) (p + s • phiL z)) (p + s • phiL z) :=
    ((Work.Smooth.Morse.param_contDiff ψ).differentiable (by simp)).differentiableAt.hasFDerivAt
  exact (hp.comp z hg).fderiv

/-- **The image of the unit disc of parameters is the trace of the Euclidean ball of radius `s`
around `p`** (in the parameter plane): the scaled chart `z ↦ p + s • (z.re, z.im)` carries the
open unit disc onto the open Euclidean disc of radius `s` about `p`. -/
theorem chart_ball_image (p : ℝ × ℝ) {s : ℝ} (hs : 0 < s) :
    (fun z : ℂ => p + s • phiL z) '' Metric.ball (0 : ℂ) 1
      = {q : ℝ × ℝ | (q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2 < s ^ 2} := by
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [Metric.mem_ball, dist_zero_right] at hz
    show ((p + s • phiL z).1 - p.1) ^ 2 + ((p + s • phiL z).2 - p.2) ^ 2 < s ^ 2
    have h₁ : (p + s • phiL z).1 - p.1 = s * z.re := by
      show p.1 + s * z.re - p.1 = s * z.re
      ring
    have h₂ : (p + s • phiL z).2 - p.2 = s * z.im := by
      show p.2 + s * z.im - p.2 = s * z.im
      ring
    rw [h₁, h₂]
    have hzsq : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have hcalc : (s * z.re) ^ 2 + (s * z.im) ^ 2 = s ^ 2 * ‖z‖ ^ 2 := by
      rw [← hzsq]; ring
    rw [hcalc]
    have h1 : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z, hz]
    nlinarith [sq_pos_of_pos hs]
  · intro hq
    refine ⟨⟨(q.1 - p.1) / s, (q.2 - p.2) / s⟩, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right]
      have hzsq : ‖(⟨(q.1 - p.1) / s, (q.2 - p.2) / s⟩ : ℂ)‖ ^ 2
          = ((q.1 - p.1) / s) ^ 2 + ((q.2 - p.2) / s) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
      have hlt : ‖(⟨(q.1 - p.1) / s, (q.2 - p.2) / s⟩ : ℂ)‖ ^ 2 < 1 := by
        rw [hzsq]
        have h3 : ((q.1 - p.1) / s) ^ 2 + ((q.2 - p.2) / s) ^ 2
            = ((q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2) / s ^ 2 := by
          rw [div_pow, div_pow, ← add_div]
        rw [h3, div_lt_one (by positivity)]
        simpa using hq
      nlinarith [norm_nonneg (⟨(q.1 - p.1) / s, (q.2 - p.2) / s⟩ : ℂ)]
    · have h1 : s * ((q.1 - p.1) / s) = q.1 - p.1 := mul_div_cancel₀ _ hs.ne'
      have h2 : s * ((q.2 - p.2) / s) = q.2 - p.2 := mul_div_cancel₀ _ hs.ne'
      simp only [phiL_apply]
      ext <;> simp [h1, h2]


set_option maxHeartbeats 1000000 in
/-- **A small Euclidean ball of the surface is an embedded disc.**

For every point `x` of the surface `F = ψ(S¹×S¹)` there is `δ > 0` and an embedded disc `D` of the
surface whose carrier is exactly the trace `F ∩ closedBall x δ` of the Euclidean ball of radius
`δ` around `x`, and whose interior contains `x`. -/
theorem exists_discRegion_eq_inter_ball (ψ : Submission.Diffeo) (x : LeanEval.KnotTheory.PardonDistortion.R3) (hx : x ∈ (Work.Smooth.Morse.torus ψ).carrier) : ∃ δ : ℝ, 0 < δ ∧ ∃ D : Work.SurgeryInvariance.DiscRegion (Work.Smooth.Morse.torus ψ), D.carrier = (Work.Smooth.Morse.torus ψ).carrier ∩ Metric.closedBall x δ ∧ x ∈ D.interior := by
  have hxcar : x ∈ (Work.Smooth.Morse.torus ψ).carrier := hx
  obtain ⟨p, hp⟩ : ∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = x := hx
  -- ## Step 1: the derivative of the parametrisation at `p` is injective, with a lower bound
  have hinj : Function.Injective ((fderiv ℝ (Work.Smooth.Morse.param ψ) p).comp phiL) :=
    (Work.Smooth.Morse.Immersion.isImmersion ψ p).comp phiL_injective
  obtain ⟨c₀, hc₀pos, hc₀⟩ := exists_lower_bound_of_injective hinj
  have hΦpos : 0 < ‖phiL‖ := phiL_norm_pos
  -- ## Step 2: the derivative of the parametrisation is continuous at `p`
  have hcontAt : ContinuousAt (fderiv ℝ (Work.Smooth.Morse.param ψ)) p :=
    ((Work.Smooth.Morse.param_contDiff ψ).continuous_fderiv (by simp)).continuousAt
  have htarget : 0 < c₀ / 4 / ‖phiL‖ := by positivity
  obtain ⟨ρ, hρpos, hρ⟩ := Metric.continuousAt_iff.mp hcontAt (c₀ / 4 / ‖phiL‖) htarget
  -- ## Step 3: a small scale `s`, the chart `chart ψ p s`, and the constants `c = s * c₀`,
  -- `ε = s * c₀ / 4`
  have hden : (0 : ℝ) < 2 * (‖phiL‖ + 1) := by positivity
  obtain ⟨s, hspos, hsρ, hsΦρ⟩ : ∃ s : ℝ, 0 < s ∧ s ≤ ρ / (2 * (‖phiL‖ + 1)) ∧
      s * ‖phiL‖ < ρ := by
    refine ⟨min (ρ / (2 * (‖phiL‖ + 1))) (1 / 2), lt_min (div_pos hρpos hden) (by norm_num),
      min_le_left _ _, ?_⟩
    calc min (ρ / (2 * (‖phiL‖ + 1))) (1 / 2) * ‖phiL‖
        ≤ (ρ / (2 * (‖phiL‖ + 1))) * ‖phiL‖ :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _)
      _ < ρ := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
          nlinarith [norm_nonneg phiL]
  have hfd_close : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      dist (fderiv ℝ (Work.Smooth.Morse.param ψ) (p + s • phiL z))
        (fderiv ℝ (Work.Smooth.Morse.param ψ) p) < c₀ / 4 / ‖phiL‖ := by
    intro z hz
    apply hρ
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    rw [dist_eq_norm]
    calc ‖p + s • phiL z - p‖ = ‖s • phiL z‖ := by rw [add_sub_cancel_left]
      _ = s * ‖phiL z‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hspos]
      _ ≤ s * (‖phiL‖ * ‖z‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm phiL z) (le_of_lt hspos)
      _ ≤ s * ‖phiL‖ :=
          mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (norm_nonneg phiL) hz)
            (le_of_lt hspos)
      _ < ρ := hsΦρ
  have hεc : 4 * (s * c₀ / 4) ≤ s * c₀ := le_of_eq (by ring)
  have hA_low : ∀ v : ℂ, (s * c₀) * ‖v‖
      ≤ ‖(s • ((fderiv ℝ (Work.Smooth.Morse.param ψ) p).comp phiL)) v‖ := by
    intro v
    rw [smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hspos]
    calc (s * c₀) * ‖v‖ = s * (c₀ * ‖v‖) := by ring
      _ ≤ s * ‖((fderiv ℝ (Work.Smooth.Morse.param ψ) p).comp phiL) v‖ :=
          mul_le_mul_of_nonneg_left (hc₀ v) (le_of_lt hspos)
  have hboundUp : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      ‖fderiv ℝ (chart ψ p s) z - s • ((fderiv ℝ (Work.Smooth.Morse.param ψ) p).comp phiL)‖
        ≤ s * c₀ / 4 := by
    intro z hz
    rw [fderiv_chart]
    have hsplit : (fderiv ℝ (Work.Smooth.Morse.param ψ) (p + s • phiL z)).comp (s • phiL)
        - s • ((fderiv ℝ (Work.Smooth.Morse.param ψ) p).comp phiL)
        = s • ((fderiv ℝ (Work.Smooth.Morse.param ψ) (p + s • phiL z)
            - fderiv ℝ (Work.Smooth.Morse.param ψ) p).comp phiL) := by
      ext v
      simp [mul_sub]
    rw [hsplit, norm_smul, Real.norm_eq_abs, abs_of_pos hspos]
    have hcomp : ‖((fderiv ℝ (Work.Smooth.Morse.param ψ) (p + s • phiL z)
        - fderiv ℝ (Work.Smooth.Morse.param ψ) p).comp phiL)‖
        ≤ ‖fderiv ℝ (Work.Smooth.Morse.param ψ) (p + s • phiL z)
            - fderiv ℝ (Work.Smooth.Morse.param ψ) p‖ * ‖phiL‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    have hclose : ‖fderiv ℝ (Work.Smooth.Morse.param ψ) (p + s • phiL z)
        - fderiv ℝ (Work.Smooth.Morse.param ψ) p‖ ≤ c₀ / 4 / ‖phiL‖ := by
      have h := le_of_lt (hfd_close z hz)
      rwa [dist_eq_norm] at h
    calc s * ‖((fderiv ℝ (Work.Smooth.Morse.param ψ) (p + s • phiL z)
            - fderiv ℝ (Work.Smooth.Morse.param ψ) p).comp phiL)‖
        ≤ s * (‖fderiv ℝ (Work.Smooth.Morse.param ψ) (p + s • phiL z)
            - fderiv ℝ (Work.Smooth.Morse.param ψ) p‖ * ‖phiL‖) :=
          mul_le_mul_of_nonneg_left hcomp (le_of_lt hspos)
      _ ≤ s * ((c₀ / 4 / ‖phiL‖) * ‖phiL‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hclose (norm_nonneg _))
            (le_of_lt hspos)
      _ = s * (c₀ / 4) := by rw [div_mul_cancel₀ _ hΦpos.ne']
      _ = s * c₀ / 4 := by ring
  have hdiff : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      HasFDerivAt (chart ψ p s) (fderiv ℝ (chart ψ p s) z) z := fun z _ =>
    ((chart_contDiff ψ p s).differentiable (by simp)).differentiableAt.hasFDerivAt
  -- ## Step 4: the trace of a small *parameter* ball around `p` is open in the surface
  have hUopen : IsOpen {q : ℝ × ℝ | (q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2 < s ^ 2} :=
    isOpen_lt (by fun_prop) continuous_const
  have hpU : p ∈ {q : ℝ × ℝ | (q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2 < s ^ 2} := by
    have hzero : (p.1 - p.1) ^ 2 + (p.2 - p.2) ^ 2 = 0 := by ring
    show (p.1 - p.1) ^ 2 + (p.2 - p.2) ^ 2 < s ^ 2
    rw [hzero]
    positivity
  have hVopen : Work.SurgeryInvariance.IsOpenInCarrier (Work.Smooth.Morse.torus ψ)
      (Work.Smooth.Morse.param ψ ''
        {q : ℝ × ℝ | (q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2 < s ^ 2}) :=
    Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen ψ hUopen
  have hxV : x ∈ Work.Smooth.Morse.param ψ ''
      {q : ℝ × ℝ | (q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2 < s ^ 2} := ⟨p, hpU, hp⟩
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := Metric.isOpen_iff.mp hVopen ⟨x, hxcar⟩ hxV
  -- every point of that trace is the image of a point of the open unit disc
  have hVchart : ∀ y ∈ Work.Smooth.Morse.param ψ ''
      {q : ℝ × ℝ | (q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2 < s ^ 2},
      ∃ z ∈ Metric.ball (0 : ℂ) 1, chart ψ p s z = y := by
    rintro y ⟨q, hq, hqy⟩
    rw [← chart_ball_image p hspos] at hq
    obtain ⟨z, hz, hzq⟩ := hq
    simp only [] at hzq
    exact ⟨z, hz, by
      show Work.Smooth.Morse.param ψ (p + s • phiL z) = y
      rw [hzq, hqy]⟩
  have hcover : ∀ y ∈ (Work.Smooth.Morse.torus ψ).carrier, dist y x < δ₀ →
      ∃ z ∈ Metric.closedBall (0 : ℂ) 1, chart ψ p s z = y := by
    intro y hy hd
    have hmem : (⟨y, hy⟩ : (Work.Smooth.Morse.torus ψ).carrier) ∈
        Subtype.val ⁻¹' (Work.Smooth.Morse.param ψ ''
          {q : ℝ × ℝ | (q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2 < s ^ 2}) :=
      hδ₀ (by rw [Metric.mem_ball, Subtype.dist_eq]; exact hd)
    obtain ⟨z, hz, hzy⟩ := hVchart y hmem
    exact ⟨z, Metric.ball_subset_closedBall hz, hzy⟩
  -- ## Step 5: the final radius `δ`
  have hcε : (0 : ℝ) < s * c₀ - s * c₀ / 4 := by nlinarith [hc₀pos, hspos]
  obtain ⟨δ, hδpos, hδδ₀, hδrad⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < δ₀ ∧ δ < s * c₀ - s * c₀ / 4 := by
    refine ⟨min δ₀ (s * c₀ - s * c₀ / 4) / 2, half_pos (lt_min hδ₀pos hcε), ?_, ?_⟩
    · have h := min_le_left δ₀ (s * c₀ - s * c₀ / 4)
      have h' := lt_min hδ₀pos hcε
      linarith
    · have h := min_le_right δ₀ (s * c₀ - s * c₀ / 4)
      have h' := lt_min hδ₀pos hcε
      linarith
  -- ## Step 6: the radial lemma realises the trace of `closedBall x δ` on the chart
  obtain ⟨e, heinj, he_range, he_open, he0⟩ :=
    exists_disc_param_of_chart (u := chart ψ p s) (x := x)
      (A := s • ((fderiv ℝ (Work.Smooth.Morse.param ψ) p).comp phiL))
      (c := s * c₀) (ε := s * c₀ / 4) (δ := δ)
      (chart_continuous ψ p s) (by positivity) (by positivity) hεc hδpos hδrad hA_low
      (by rw [chart_zero, hp]) hdiff hboundUp
  -- ## Step 7: the range and the open part of `e` are the traces of the ball
  have hparam_mem : ∀ z : ℂ, Work.Smooth.Morse.param ψ (p + s • phiL z)
      ∈ (Work.Smooth.Morse.torus ψ).carrier := fun z => Work.Smooth.Morse.param_mem ψ _
  have hrange : Set.range e = (Work.Smooth.Morse.torus ψ).carrier ∩ Metric.closedBall x δ := by
    ext y
    constructor
    · intro hy
      rw [he_range] at hy
      obtain ⟨⟨z, -, hzy⟩, hdist⟩ := hy
      exact ⟨by rw [← hzy]; exact hparam_mem z,
        by rw [Metric.mem_closedBall, dist_eq_norm]; exact hdist⟩
    · rintro ⟨hyc, hyb⟩
      rw [Metric.mem_closedBall, dist_eq_norm] at hyb
      obtain ⟨z, hz, hzy⟩ :=
        hcover y hyc (by rw [dist_eq_norm]; exact lt_of_le_of_lt hyb hδδ₀)
      rw [he_range]
      exact ⟨⟨z, hz, hzy⟩, hyb⟩
  have hinterior : e '' {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ < 1}
      = (Work.Smooth.Morse.torus ψ).carrier ∩ Metric.ball x δ := by
    ext y
    constructor
    · intro hy
      rw [he_open] at hy
      obtain ⟨⟨z, -, hzy⟩, hdist⟩ := hy
      exact ⟨by rw [← hzy]; exact hparam_mem z,
        by rw [Metric.mem_ball, dist_eq_norm]; exact hdist⟩
    · rintro ⟨hyc, hyb⟩
      rw [Metric.mem_ball, dist_eq_norm] at hyb
      obtain ⟨z, hz, hzy⟩ :=
        hcover y hyc (by rw [dist_eq_norm]; exact lt_of_lt_of_le hyb (le_of_lt hδδ₀))
      rw [he_open]
      exact ⟨⟨z, hz, hzy⟩, hyb⟩
  -- ## Step 8: assemble the disc
  have hmem_e : ∀ z : Metric.closedBall (0 : ℂ) 1,
      e z ∈ (Work.Smooth.Morse.torus ψ).carrier := by
    intro z
    have h : e z ∈ Set.range e := ⟨z, rfl⟩
    rw [hrange] at h
    exact h.1
  have hopen_int : Work.SurgeryInvariance.IsOpenInCarrier (Work.Smooth.Morse.torus ψ)
      (e '' {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ < 1}) := by
    rw [hinterior]
    exact Work.SurgeryInvariance.isOpenInCarrier_carrier_inter
      (P := Work.Smooth.Morse.torus ψ) Metric.isOpen_ball
  have hxint : x ∈ e '' {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ < 1} := by
    rw [hinterior]
    exact ⟨hxcar, by rw [Metric.mem_ball, dist_self]; exact hδpos⟩
  exact ⟨δ, hδpos,
    ⟨{ e := e, inj := heinj, mem := hmem_e, open_interior := hopen_int }, hrange, hxint⟩⟩

end

end Work.Smooth.Morse.MorseModel
