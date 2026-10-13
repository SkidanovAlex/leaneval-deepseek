import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs
import Submission.Work.FTS_StreamBdry.SB1.Engine
import Submission.Work.FTS_StreamBdry.SB1.psiP_ode
import Submission.Work.FTS_StreamBdry.SB3.psiP_c2
import Submission.Work.FTS_StreamBdry.SB3.psiP_DzLe
import Submission.Work.FTS_StreamBdry.SB3.psiP_D3_le
import Submission.Work.FTS_StreamBdry.SB3.pth_DzIter_le
import Submission.Work.FTS_StreamBdry.SB3.law_psiP
import Submission.Work.FTS_StreamBdry.SB25.lip_edge_trace
import Submission.Work.FTS_StreamBdry.SB25.axis_tan_bound
import Submission.Work.FTS_StreamBdry.SB25.axis_d2_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25.pze_aux` — helper lemmas for the leaf B5 (`psiP_edge_zero`)

Elementary one-variable bounds, filter (squeezing) lemmas along `𝓝[Qd] (z₀,0)`, smoothness of
`θ ↦ tan θ` / of `Vop` / of `pz` on the open quadrant, congruence of partial derivatives on an open
set, and the two second-derivative identities
`∂_z²P = (D_z²P - D_zP)/z²`, `∂_θ²P = ∂_θ(V P) + (1/cos²θ + tan²θ)P + tan θ·(V P)`.
-/


noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB25

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK)
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false


/-! ## §1 Elementary one-variable bounds -/

/-- `|tan θ| ≤ 2θ` on `[0, 1/2]` (from `cos θ ≥ 1 - θ²/2 ≥ 7/8` and `sin θ ≤ θ`). -/
lemma pze_tan_abs_le_two_mul {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1 / 2) :
    |Real.tan θ| ≤ 2 * θ := by
  rcases lt_or_eq_of_le h0 with hlt | heq
  · have hcos : (7 : ℝ) / 8 ≤ Real.cos θ := by
      have hx := Real.one_sub_sq_div_two_le_cos (x := θ)
      have h2 : θ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith
      linarith
    have hcospos : 0 < Real.cos θ := by linarith
    have htanpos : 0 < Real.tan θ :=
      Real.tan_pos_of_pos_of_lt_pi_div_two hlt (by linarith [h1, Real.pi_gt_three])
    rw [abs_of_pos htanpos, Real.tan_eq_sin_div_cos, div_le_iff₀ hcospos]
    have hsin : Real.sin θ ≤ θ := Real.sin_le h0
    have hc1 : (1 : ℝ) ≤ 2 * Real.cos θ := by linarith
    have hθ2 : θ ≤ 2 * θ * Real.cos θ := by
      calc θ = θ * 1 := by ring
        _ ≤ θ * (2 * Real.cos θ) := mul_le_mul_of_nonneg_left hc1 h0
        _ = 2 * θ * Real.cos θ := by ring
    linarith
  · subst heq; simp

/-- `1/cos²θ ≤ 2` on `[0, 1/2]`. -/
lemma pze_one_div_cos_sq_le_two {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1 / 2) :
    1 / Real.cos θ ^ 2 ≤ 2 := by
  have hcos : (7 : ℝ) / 8 ≤ Real.cos θ := by
    have hx := Real.one_sub_sq_div_two_le_cos (x := θ)
    have h2 : θ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith
    linarith
  have hsq : ((7 : ℝ) / 8) ^ 2 ≤ Real.cos θ ^ 2 := by nlinarith
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < Real.cos θ ^ 2)]
  nlinarith

/-- `tan²θ ≤ 1` on `[0, 1/2]`. -/
lemma pze_tan_sq_le_one {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1 / 2) :
    Real.tan θ ^ 2 ≤ 1 := by
  have h := pze_tan_abs_le_two_mul h0 h1
  have h2 : (2 * θ) ^ 2 ≤ 1 := by nlinarith
  nlinarith [abs_nonneg (Real.tan θ), sq_abs (Real.tan θ)]

/-- The coefficient `1/cos²θ + tan²θ` is bounded by `3` on `[0, 1/2]`. -/
lemma pze_one_div_cos_sq_add_tan_sq_abs_le_three {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1 / 2) :
    |1 / Real.cos θ ^ 2 + Real.tan θ ^ 2| ≤ 3 := by
  have ha := pze_one_div_cos_sq_le_two h0 h1
  have hb := pze_tan_sq_le_one h0 h1
  have hc : (0 : ℝ) ≤ Real.cos θ ^ 2 := sq_nonneg _
  rw [abs_of_nonneg (by positivity)]
  linarith

/-- `sin 2θ ≤ 2θ` for `θ ≥ 0`. -/
lemma pze_s2_le_two_mul {θ : ℝ} (h0 : 0 ≤ θ) : Work.Construction.s2 θ ≤ 2 * θ := by
  rw [Work.Construction.s2_eq]
  have h := Real.sin_le (by linarith : (0 : ℝ) ≤ 2 * θ)
  linarith

/-! ## §2 Filters: squeezing along `𝓝[Qd] (z₀,0)` -/

/-- A function eventually bounded by `u(θ)` with `u` continuous and `u 0 = 0` tends to `0`. -/
lemma pze_tendsto_zero_of_eventually_le {g : ℝ × ℝ → ℝ} {z0 : ℝ} {u : ℝ → ℝ}
    (hu : Continuous u) (hu0 : u 0 = 0)
    (h : ∀ᶠ p in 𝓝[Work.Construction.Qd] (z0, 0), |g p| ≤ u p.2) :
    Filter.Tendsto g (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 0) := by
  have hcont : Continuous fun p : ℝ × ℝ => u p.2 := hu.comp continuous_snd
  have h1 : Filter.Tendsto (fun p : ℝ × ℝ => u p.2)
      (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 0) := by
    have h2 := hcont.tendsto (z0, 0)
    have h3 : Filter.Tendsto (fun p : ℝ × ℝ => u p.2)
        (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 (u 0)) := h2.mono_left nhdsWithin_le_nhds
    simpa [hu0] using h3
  have h4 : Filter.Tendsto (fun p : ℝ × ℝ => |g p|)
      (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun p => abs_nonneg _) h h1
  have h5 : Filter.Tendsto (fun p : ℝ × ℝ => ‖g p - 0‖)
      (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 0) := by
    simpa only [sub_zero, Real.norm_eq_abs] using h4
  exact tendsto_iff_norm_sub_tendsto_zero.mpr h5

/-- A function agreeing with a continuous `c` up to `u(θ)` (with `u` continuous, `u 0 = 0`) tends
to the value of `c` at the corner point. -/
lemma pze_tendsto_of_eventually_le_add {g c : ℝ × ℝ → ℝ} {z0 : ℝ} {u : ℝ → ℝ}
    (hz0 : 0 < z0)
    (hc : ContinuousOn c (Ioi 0 ×ˢ (Set.univ : Set ℝ)))
    (hu : Continuous u) (hu0 : u 0 = 0)
    (h : ∀ᶠ p in 𝓝[Work.Construction.Qd] (z0, 0), |g p - c p| ≤ u p.2) :
    Filter.Tendsto g (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 (c (z0, 0))) := by
  have hmem : (Ioi 0 ×ˢ (Set.univ : Set ℝ)) ∈ 𝓝 ((z0, 0) : ℝ × ℝ) :=
    (isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hz0, trivial⟩
  have hct : Filter.Tendsto c (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 (c (z0, 0))) :=
    (hc.continuousAt hmem).tendsto.mono_left nhdsWithin_le_nhds
  have hzero : Filter.Tendsto (fun p : ℝ × ℝ => g p - c p)
      (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 0) :=
    pze_tendsto_zero_of_eventually_le hu hu0 h
  have hsum : Filter.Tendsto (fun p : ℝ × ℝ => c p + (g p - c p))
      (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 (c (z0, 0))) := by
    simpa using hct.add hzero
  exact hsum.congr (fun p => by ring)

/-- A pointwise fact on the quadrant is eventually true along `𝓝[Qd] (z₀,0)`. -/
lemma pze_eventually_of_mem_Qd {z0 : ℝ} {p : ℝ × ℝ → Prop}
    (h : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → p (z, θ)) :
    ∀ᶠ q in 𝓝[Work.Construction.Qd] (z0, 0), p q :=
  Eventually.mono self_mem_nhdsWithin fun q hq => h q.1 q.2 hq

/-- Eventually, the second coordinate is `< c` for any `c > 0`. -/
lemma pze_eventually_snd_lt {z0 c : ℝ} (hc : 0 < c) :
    ∀ᶠ p : ℝ × ℝ in 𝓝[Work.Construction.Qd] (z0, 0), p.2 < c := by
  have h : Iio c ∈ 𝓝 (0 : ℝ) := isOpen_Iio.mem_nhds hc
  exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
    ((continuous_snd.continuousAt (x := (z0, 0))).preimage_mem_nhds h)

/-- Eventually, the first coordinate exceeds `z₀/2`. -/
lemma pze_eventually_fst_gt {z0 : ℝ} (hz0 : 0 < z0) :
    ∀ᶠ p : ℝ × ℝ in 𝓝[Work.Construction.Qd] (z0, 0), z0 / 2 < p.1 := by
  have hmem : (z0 : ℝ) ∈ Ioi (z0 / 2) := by show z0 / 2 < z0; linarith
  have h : Ioi (z0 / 2) ∈ 𝓝 z0 := isOpen_Ioi.mem_nhds hmem
  exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
    ((continuous_fst.continuousAt (x := (z0, 0))).preimage_mem_nhds h)

/-! ## §2b Coordinate facts at a point of the quadrant -/

/-- At a point of the quadrant the first coordinate is positive. -/
lemma pze_pos_fst {p : ℝ × ℝ} (hp : p ∈ Work.Construction.Qd) : 0 < p.1 := (mem_Qd.mp hp).1

/-- At a point of the quadrant the second coordinate is positive. -/
lemma pze_pos_snd {p : ℝ × ℝ} (hp : p ∈ Work.Construction.Qd) : 0 < p.2 := (mem_Qd.mp hp).2.1

/-- At a point of the quadrant the second coordinate is `< π/2`. -/
lemma pze_snd_lt {p : ℝ × ℝ} (hp : p ∈ Work.Construction.Qd) : p.2 < π / 2 :=
  (mem_Qd.mp hp).2.2

/-- At a point of the quadrant the second coordinate lies in `(0,π/2)`. -/
lemma pze_theta_mem {p : ℝ × ℝ} (hp : p ∈ Work.Construction.Qd) : p.2 ∈ Ioo (0 : ℝ) (π / 2) :=
  ⟨pze_pos_snd hp, pze_snd_lt hp⟩

/-- At a point of the quadrant the second coordinate lies in the closed strip `Iθ`. -/
lemma pze_theta_Iθ {p : ℝ × ℝ} (hp : p ∈ Work.Construction.Qd) : p.2 ∈ Work.Spaces.Iθ :=
  ⟨le_of_lt (pze_pos_snd hp), le_of_lt (pze_snd_lt hp)⟩

/-- `s2 = sin 2θ` is positive on the quadrant. -/
lemma pze_s2_pos {p : ℝ × ℝ} (hp : p ∈ Work.Construction.Qd) :
    0 < Work.Construction.s2 p.2 :=
  s2_pos_of_Ioo (pze_theta_mem hp)

/-- `s2 = sin 2θ` is nonnegative on the quadrant. -/
lemma pze_s2_nonneg {p : ℝ × ℝ} (hp : p ∈ Work.Construction.Qd) :
    0 ≤ Work.Construction.s2 p.2 := le_of_lt (pze_s2_pos hp)

/-- `cos θ` is positive on the quadrant. -/
lemma pze_cos_pos {p : ℝ × ℝ} (hp : p ∈ Work.Construction.Qd) : 0 < Real.cos p.2 :=
  cos_pos_of_Ioo (pze_theta_mem hp)

/-! ## §3 Smoothness on the quadrant -/

/-- `θ ↦ tan θ` is `C^n` on the open quadrant. -/
lemma pze_contDiffOn_tan_Qd {n : ℕ} :
    ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.tan p.2) Work.Construction.Qd := by
  have hsin : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin p.2) Work.Construction.Qd :=
    Real.contDiff_sin.comp_contDiffOn contDiff_snd.contDiffOn
  have hcos : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.cos p.2) Work.Construction.Qd :=
    Real.contDiff_cos.comp_contDiffOn contDiff_snd.contDiffOn
  refine (hsin.div hcos (fun p hp => ne_of_gt (cos_pos_of_Qd hp))).congr (fun p _ => ?_)
  exact Real.tan_eq_sin_div_cos p.2

/-- The `z`-partial of a `C²` function on the quadrant is `C¹`. -/
lemma pze_contDiffOn_uncurry_pz_Qd {G : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ 2 (Function.uncurry G) Work.Construction.Qd) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz G)) Work.Construction.Qd :=
  Work.FTS_StreamBdry.SB3.psiP_D3_aux_pz_smooth Work.FTS_StreamBdry.SB1.isOpen_Qd
    (n := 1) h

/-- `Vop` of a `C³` function on the quadrant is `C²`. -/
lemma pze_contDiffOn_uncurry_Vop_Qd {Ψ : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd) :
    ContDiffOn ℝ 2 (Function.uncurry (Work.Construction.Vop Ψ)) Work.Construction.Qd := by
  have hpth : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pth Ψ)) Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB3.contDiffOn_uncurry_pth_qd (n := 2) h
  have h2 : ContDiffOn ℝ 2 (Function.uncurry Ψ) Work.Construction.Qd := h.of_le (by norm_num)
  refine (hpth.sub ((pze_contDiffOn_tan_Qd (n := 2)).mul h2)).congr (fun p _ => ?_)
  simp only [Function.uncurry, Work.Construction.Vop]

/-! ## §4 Congruence of partial derivatives on the quadrant -/

/-- Partial `z`-derivatives agree for functions agreeing on an open set. -/
lemma pze_pz_congr_of_isOpen {f g : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (h : ∀ p ∈ U, f p.1 p.2 = g p.1 p.2) {z θ : ℝ} (hmem : (z, θ) ∈ U) :
    Work.Spaces.pz f z θ = Work.Spaces.pz g z θ := by
  have hev : (fun z' => f z' θ) =ᶠ[𝓝 z] (fun z' => g z' θ) := by
    filter_upwards [(continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => θ)).continuousAt.preimage_mem_nhds
      (hU.mem_nhds hmem)] with z' hz'
    exact h (z', θ) hz'
  exact hev.deriv_eq

/-- Partial `θ`-derivatives agree for functions agreeing on an open set. -/
lemma pze_pth_congr_of_isOpen {f g : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (h : ∀ p ∈ U, f p.1 p.2 = g p.1 p.2) {z θ : ℝ} (hmem : (z, θ) ∈ U) :
    Work.Spaces.pth f z θ = Work.Spaces.pth g z θ := by
  have hev : (fun θ' => f z θ') =ᶠ[𝓝 θ] (fun θ' => g z θ') := by
    filter_upwards [((continuous_const : Continuous fun _ : ℝ => z).prodMk continuous_id).continuousAt.preimage_mem_nhds
      (hU.mem_nhds hmem)] with θ' hθ'
    exact h (z, θ') hθ'
  exact hev.deriv_eq

/-! ## §5 The two second-derivative identities -/

/-- `∂_z²P = (D_z²P - D_zP)/z²` on the quadrant, from the product rule. -/
lemma pze_pz_pz_eq {P : ℝ → ℝ → ℝ}
    (hP2 : ContDiffOn ℝ 2 (Function.uncurry P) Work.Construction.Qd)
    {z θ : ℝ} (hmem : (z, θ) ∈ Work.Construction.Qd) :
    Work.Spaces.pz (Work.Spaces.pz P) z θ
      = (Work.Spaces.DzIter 2 P z θ - Work.Spaces.DzIter 1 P z θ) / z ^ 2 := by
  have hz : z ≠ 0 := ne_of_gt (Qd_pos hmem)
  have hQd := Work.FTS_StreamBdry.SB1.isOpen_Qd
  have hpz1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz P)) Work.Construction.Qd :=
    pze_contDiffOn_uncurry_pz_Qd hP2
  have hpzdiff : DifferentiableAt ℝ (fun z' => Work.Spaces.pz P z' θ) z :=
    Work.Spaces.differentiableAt_curry_left
      ((hpz1.differentiableOn (by norm_num)).differentiableAt (hQd.mem_nhds hmem))
  have h2 : Work.Spaces.pz (Work.Spaces.DzIter 1 P) z θ
      = Work.Spaces.pz P z θ + z * Work.Spaces.pz (Work.Spaces.pz P) z θ := by
    show deriv (fun z' => Work.Spaces.DzIter 1 P z' θ) z = _
    have hev : (fun z' => Work.Spaces.DzIter 1 P z' θ)
        = fun z' => z' * Work.Spaces.pz P z' θ := by
      funext z'; rfl
    have hdm : deriv (fun z' => z' * Work.Spaces.pz P z' θ) z
        = deriv (fun z' : ℝ => z') z * Work.Spaces.pz P z θ
          + z * deriv (fun z' => Work.Spaces.pz P z' θ) z :=
      deriv_mul differentiableAt_id hpzdiff
    rw [hev, hdm, deriv_id'']
    simp only [one_mul]
    rfl
  have hmain : Work.Spaces.DzIter 2 P z θ
      = z * Work.Spaces.pz P z θ + z ^ 2 * Work.Spaces.pz (Work.Spaces.pz P) z θ := by
    show z * Work.Spaces.pz (Work.Spaces.DzIter 1 P) z θ = _
    rw [h2]; ring
  have h1 : Work.Spaces.DzIter 1 P z θ = z * Work.Spaces.pz P z θ := rfl
  rw [hmain, h1, eq_div_iff (pow_ne_zero 2 hz)]
  ring

/-- The `θ`-derivative split `∂_θ²P = ∂_θ(V P) + (1/cos²θ + tan²θ)·P + tan θ·(V P)`. -/
lemma pze_pth_pth_eq {P : ℝ → ℝ → ℝ}
    (hP2 : ContDiffOn ℝ 2 (Function.uncurry P) Work.Construction.Qd)
    {z θ : ℝ} (hmem : (z, θ) ∈ Work.Construction.Qd) :
    Work.Spaces.pth (Work.Spaces.pth P) z θ
      = Work.Spaces.pth (Work.Construction.Vop P) z θ
        + (1 / Real.cos θ ^ 2 + Real.tan θ ^ 2) * P z θ
        + Real.tan θ * Work.Construction.Vop P z θ := by
  have hcos : Real.cos θ ≠ 0 := ne_of_gt (cos_pos_of_Qd hmem)
  have hQd := Work.FTS_StreamBdry.SB1.isOpen_Qd
  have hPdiff : DifferentiableAt ℝ (fun θ' => P z θ') θ :=
    Work.Spaces.differentiableAt_curry_right
      ((hP2.differentiableOn (by norm_num)).differentiableAt (hQd.mem_nhds hmem))
  have hpth1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth P)) Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB3.contDiffOn_uncurry_pth_qd (n := 1) hP2
  have hpthdiff : DifferentiableAt ℝ (fun θ' => Work.Spaces.pth P z θ') θ :=
    Work.Spaces.differentiableAt_curry_right
      ((hpth1.differentiableOn (by norm_num)).differentiableAt (hQd.mem_nhds hmem))
  have htan : DifferentiableAt ℝ Real.tan θ := Real.differentiableAt_tan.mpr hcos
  have hd2 : DifferentiableAt ℝ (fun θ' => Real.tan θ' * P z θ') θ := htan.mul hPdiff
  have hd1 : DifferentiableAt ℝ (fun θ' => Work.Construction.Vop P z θ') θ := by
    have h := hpthdiff.sub hd2
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun θ' => ?_))
    show Work.Construction.Vop P z θ' = Work.Spaces.pth P z θ' - Real.tan θ' * P z θ'
    simp only [Work.Construction.Vop]
  have hstep : Work.Spaces.pth (Work.Spaces.pth P) z θ
      = deriv (fun θ' => Work.Construction.Vop P z θ' + Real.tan θ' * P z θ') θ := by
    show deriv (fun θ' => Work.Spaces.pth P z θ') θ = _
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards with θ'
    show Work.Spaces.pth P z θ' = Work.Construction.Vop P z θ' + Real.tan θ' * P z θ'
    rw [Work.Construction.Vop]; ring
  have hstep2 : deriv (fun θ' => Work.Construction.Vop P z θ' + Real.tan θ' * P z θ') θ
      = deriv (fun θ' => Work.Construction.Vop P z θ') θ
        + deriv (fun θ' => Real.tan θ' * P z θ') θ :=
    deriv_add hd1 hd2
  rw [hstep, hstep2]
  have hmul : deriv (fun θ' => Real.tan θ' * P z θ') θ
      = 1 / Real.cos θ ^ 2 * P z θ + Real.tan θ * Work.Spaces.pth P z θ := by
    have hdm : deriv (fun θ' => Real.tan θ' * P z θ') θ
        = deriv Real.tan θ * P z θ + Real.tan θ * deriv (fun θ' => P z θ') θ :=
      deriv_mul htan hPdiff
    rw [hdm, Real.deriv_tan]
    rfl
  rw [hmul]
  have hpthV : Work.Spaces.pth P z θ
      = Work.Construction.Vop P z θ + Real.tan θ * P z θ := by
    rw [Work.Construction.Vop]; ring
  rw [hpthV]
  have hdv : deriv (fun θ' => Work.Construction.Vop P z θ') θ
      = Work.Spaces.pth (Work.Construction.Vop P) z θ := rfl
  rw [hdv]
  ring


end Work.FTS_StreamBdry.SB25
