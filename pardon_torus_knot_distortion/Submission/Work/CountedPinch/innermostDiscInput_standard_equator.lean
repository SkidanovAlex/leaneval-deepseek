import Mathlib
import Submission.Work.CountedPinch.tameSlice_standard_equator
import Submission.Work.PinchCounted.exists_traceCircleFamily_z
import Submission.Work.InnermostDisk.Defs

namespace Work.CountedPinch

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.CoreTopology

noncomputable section

/-! ## The flat disc bounded by the inner latitude

The equator slice `{z = 1/2}` meets the standard torus along the two latitude circles of radii
`2 ± √3/2`; the *inner* one, `longitudeCurve standard (5π/6)`, has radius `2 - √3/2` and the disc it
bounds in the plane `{z = 1/2}` has interior disjoint from the torus.  We present that disc as an
embedding of the closed unit disc, `latDisc`. -/

/-- The radius `2 + cos (5π/6) = 2 - √3/2` of the inner latitude circle. -/
def eqRad : ℝ := 2 - Real.sqrt 3 / 2

/-- The embedding `𝔻 → ℝ³` of the flat disc of radius `2 - √3/2` in the plane `{z = 1/2}`. -/
def latDiscFun (z : Metric.closedBall (0 : ℂ) 1) : R3 :=
  WithLp.toLp 2 (fun i : Fin 3 =>
    if i.val = 0 then (2 - Real.sqrt 3 / 2) * (z : ℂ).re
    else if i.val = 1 then (2 - Real.sqrt 3 / 2) * (z : ℂ).im
    else 1 / 2)

theorem latDiscFun_cont : Continuous latDiscFun := by
  unfold latDiscFun
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp (continuous_pi fun i => ?_)
  fin_cases i <;> simp only [Fin.isValue, Fin.zero_eta, ↓reduceIte]
  · exact continuous_const.mul (Complex.continuous_re.comp continuous_subtype_val)
  · exact continuous_const.mul (Complex.continuous_im.comp continuous_subtype_val)
  · exact continuous_const

/-- The flat disc bounded by the inner latitude, as a continuous map. -/
def latDisc : C(Metric.closedBall (0 : ℂ) 1, R3) := ⟨latDiscFun, latDiscFun_cont⟩

theorem latDisc_ofLp (z : Metric.closedBall (0 : ℂ) 1) (i : Fin 3) :
    (latDisc z).ofLp i = if i.val = 0 then (2 - Real.sqrt 3 / 2) * (z : ℂ).re
      else if i.val = 1 then (2 - Real.sqrt 3 / 2) * (z : ℂ).im else 1 / 2 := by
  show (latDiscFun z).ofLp i = _
  simp only [latDiscFun, WithLp.ofLp_toLp]

theorem latDisc_ofLp_zero (z : Metric.closedBall (0 : ℂ) 1) :
    (latDisc z).ofLp 0 = (2 - Real.sqrt 3 / 2) * (z : ℂ).re := by
  rw [latDisc_ofLp]; norm_num

theorem latDisc_ofLp_one (z : Metric.closedBall (0 : ℂ) 1) :
    (latDisc z).ofLp 1 = (2 - Real.sqrt 3 / 2) * (z : ℂ).im := by
  rw [latDisc_ofLp]; norm_num

theorem latDisc_ofLp_two (z : Metric.closedBall (0 : ℂ) 1) :
    (latDisc z).ofLp 2 = 1 / 2 := by
  rw [latDisc_ofLp]; norm_num

/-! ## Elementary numerical facts -/

theorem eqRad_pos : (0 : ℝ) < 2 - Real.sqrt 3 / 2 := by
  have : Real.sqrt 3 < 4 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

theorem eqRad_lt_four : (2 : ℝ) - Real.sqrt 3 / 2 < 4 := by
  have := Real.sqrt_nonneg 3; linarith

theorem eqRad_ge_half : (1 : ℝ) / 2 ≤ 2 - Real.sqrt 3 / 2 := by
  have : Real.sqrt 3 ≤ 3 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
  linarith

theorem cos_five_pi_div_six : Real.cos (5 * Real.pi / 6) = -(Real.sqrt 3 / 2) := by
  have h : 5 * Real.pi / 6 = Real.pi - Real.pi / 6 := by ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_six]

/-! ## The disc is embedded and its boundary is the inner latitude -/

theorem latDisc_injective : Function.Injective latDisc := by
  intro z w hzw
  have h0 := congrArg (fun y : R3 => y.ofLp 0) hzw
  have h1 := congrArg (fun y : R3 => y.ofLp 1) hzw
  rw [latDisc_ofLp_zero, latDisc_ofLp_zero] at h0
  rw [latDisc_ofLp_one, latDisc_ofLp_one] at h1
  have hr : (2 - Real.sqrt 3 / 2 : ℝ) ≠ 0 := ne_of_gt eqRad_pos
  have hre : (z : ℂ).re = (w : ℂ).re := mul_left_cancel₀ hr h0
  have him : (z : ℂ).im = (w : ℂ).im := mul_left_cancel₀ hr h1
  exact Subtype.ext (Complex.ext hre him)

theorem latDisc_boundary (θ : ℝ) :
    latDisc (circlePoint θ) = (longitudeCurve standard (5 * Real.pi / 6)).γ θ := by
  have hc : ((circlePoint θ : Metric.closedBall (0 : ℂ) 1) : ℂ) =
      (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    rw [circlePoint_coe, Complex.exp_ofReal_mul_I]
  have hre : ((circlePoint θ : Metric.closedBall (0 : ℂ) 1) : ℂ).re = Real.cos θ := by
    rw [hc]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re]
    ring
  have him : ((circlePoint θ : Metric.closedBall (0 : ℂ) 1) : ℂ).im = Real.sin θ := by
    rw [hc]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re]
    ring
  refine WithLp.ofLp_injective 2 ?_
  funext i
  fin_cases i
  · change (latDisc (circlePoint θ)).ofLp 0 =
      ((longitudeCurve standard (5 * Real.pi / 6)).γ θ).ofLp 0
    rw [latDisc_ofLp_zero, hre, Work.CoreTopology.longitudeCurve_apply,
      Work.CoreTopology.standard_psi, Work.Core.torusMap_apply_zero, cos_five_pi_div_six]
    ring
  · change (latDisc (circlePoint θ)).ofLp 1 =
      ((longitudeCurve standard (5 * Real.pi / 6)).γ θ).ofLp 1
    rw [latDisc_ofLp_one, him, Work.CoreTopology.longitudeCurve_apply,
      Work.CoreTopology.standard_psi, Work.Core.torusMap_apply_one, cos_five_pi_div_six]
    ring
  · change (latDisc (circlePoint θ)).ofLp 2 =
      ((longitudeCurve standard (5 * Real.pi / 6)).γ θ).ofLp 2
    rw [latDisc_ofLp_two, Work.CoreTopology.longitudeCurve_apply,
      Work.CoreTopology.standard_psi, Work.Core.torusMap_apply_two, sin_five_pi_div_six]

/-! ## The disc lies in the flat disc `cutDisc 4 0 refl (1/2)` -/

theorem latDisc_mem (z : Metric.closedBall (0 : ℂ) 1) :
    latDisc z ∈ Work.BoxShrink.Core.cutDisc 4 (0 : R3) (Equiv.refl (Fin 3)) (1 / 2) := by
  have hz : ‖(z : ℂ)‖ ≤ 1 := by
    have := z.2; rw [Metric.mem_closedBall, dist_zero_right] at this; exact this
  have key : ∀ i : Fin 3, |(latDisc z).ofLp i| ≤ 2 - Real.sqrt 3 / 2 := by
    intro i
    rw [latDisc_ofLp]
    split_ifs with h0 h1
    · rw [abs_mul, abs_of_pos eqRad_pos]
      nlinarith [Complex.abs_re_le_norm (z : ℂ), hz, eqRad_pos]
    · rw [abs_mul, abs_of_pos eqRad_pos]
      nlinarith [Complex.abs_im_le_norm (z : ℂ), hz, eqRad_pos]
    · rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; exact eqRad_ge_half
  rw [Work.BoxShrink.Core.mem_cutDisc, Submission.mem_PBox]
  refine ⟨?_, ?_⟩
  · intro i
    have h4 : (4 : ℝ) ≤ Submission.boxSide i * 4 := by
      nlinarith [Submission.one_le_boxSide i]
    have h4' : (2 - Real.sqrt 3 / 2 : ℝ) < Submission.boxSide i * 4 :=
      lt_of_lt_of_le eqRad_lt_four h4
    calc |(latDisc z).ofLp (Equiv.refl (Fin 3) i) - (0 : R3).ofLp (Equiv.refl (Fin 3) i)|
        = |(latDisc z).ofLp i| := by simp
      _ ≤ 2 - Real.sqrt 3 / 2 := key i
      _ < Submission.boxSide i * 4 := h4'
  · rw [Equiv.refl_apply, latDisc_ofLp]
    norm_num

/-! ## The interior of the disc misses the torus -/

/-- **The radius bound behind the disjointness**: any point of the standard torus in the plane
`{z = 1/2}` has planar radius at least `2 - √3/2` (its meridian parameter satisfies `sin φ = 1/2`,
hence `cos φ = ±√3/2`). -/
theorem sq_sum_ge (y : R3) (hy : y ∈ standard.carrier) (hy2 : y 2 = 1 / 2) :
    (2 - Real.sqrt 3 / 2) ^ 2 ≤ (y 0) ^ 2 + (y 1) ^ 2 := by
  obtain ⟨θ, φ, hθφ⟩ := (ParamTorus.mem_carrier_iff _ _).mp hy
  rw [← hθφ] at hy2 ⊢
  rw [Work.CoreTopology.standard_psi] at hy2 ⊢
  rw [Work.Core.torusMap_apply_two] at hy2
  rw [Work.Core.torusMap_apply_zero, Work.Core.torusMap_apply_one]
  have hcos : Real.cos φ ^ 2 = 3 / 4 := by
    nlinarith [Real.sin_sq_add_cos_sq φ, hy2]
  have hlt : Real.cos φ = Real.sqrt 3 / 2 ∨ Real.cos φ = -(Real.sqrt 3 / 2) := by
    have h : Real.cos φ ^ 2 = (Real.sqrt 3 / 2) ^ 2 := by
      rw [hcos, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; norm_num
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp h) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hsq : (2 + Real.cos φ) ^ 2 ≥ (2 - Real.sqrt 3 / 2) ^ 2 := by
    rcases hlt with h | h
    · rw [h]; nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    · rw [h]; ring_nf; norm_num
  calc (2 - Real.sqrt 3 / 2) ^ 2 ≤ (2 + Real.cos φ) ^ 2 := hsq
    _ = (2 + Real.cos φ) ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by
        rw [Real.cos_sq_add_sin_sq θ]; ring
    _ = ((2 + Real.cos φ) * Real.cos θ) ^ 2 + ((2 + Real.cos φ) * Real.sin θ) ^ 2 := by ring

/-- **The interior of `latDisc` is disjoint from the torus**: a point of the open disc has planar
radius `< 2 - √3/2`, while every point of the torus in the plane `{z = 1/2}` has planar radius
`≥ 2 - √3/2`. -/
theorem latDisc_no_interior (z : Metric.closedBall (0 : ℂ) 1) (hz : ‖(z : ℂ)‖ < 1)
    (hc : latDisc z ∈ standard.carrier) : False := by
  have hy2 : (latDisc z).ofLp 2 = 1 / 2 := latDisc_ofLp_two z
  have hge := sq_sum_ge (latDisc z) hc hy2
  have hlt : (latDisc z).ofLp 0 ^ 2 + (latDisc z).ofLp 1 ^ 2 < (2 - Real.sqrt 3 / 2) ^ 2 := by
    have hnorm : ‖(z : ℂ)‖ ^ 2 < 1 := by nlinarith [norm_nonneg (z : ℂ)]
    have h1 : ((z : ℂ).re) ^ 2 + ((z : ℂ).im) ^ 2 = ‖(z : ℂ)‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    have hpos2 : (0 : ℝ) < (2 - Real.sqrt 3 / 2) ^ 2 := pow_pos eqRad_pos 2
    rw [latDisc_ofLp_zero, latDisc_ofLp_one]
    calc ((2 - Real.sqrt 3 / 2) * (z : ℂ).re) ^ 2 + ((2 - Real.sqrt 3 / 2) * (z : ℂ).im) ^ 2
        = (2 - Real.sqrt 3 / 2) ^ 2 * (((z : ℂ).re) ^ 2 + ((z : ℂ).im) ^ 2) := by ring
      _ = (2 - Real.sqrt 3 / 2) ^ 2 * ‖(z : ℂ)‖ ^ 2 := by rw [h1]
      _ < (2 - Real.sqrt 3 / 2) ^ 2 * 1 := mul_lt_mul_of_pos_left hnorm hpos2
      _ = (2 - Real.sqrt 3 / 2) ^ 2 := mul_one _
  linarith

/-! ## The centre of Pardon's box -/

/-- The box centre `0`, written as in the statement of the target. -/
theorem boxCenter_eq_zero :
    (WithLp.toLp 2 (![0, 0, 0] : Fin 3 → ℝ) : R3) = 0 := by
  ext i
  fin_cases i <;> simp

/-! ## The target -/

/-- **A non-degenerate instance of the innermost-disc input at the flat disc**: the standard torus,
the box `PBox 4 0 (refl (Fin 3))` (which contains the whole torus) and the plane `{z = 1/2}`, whose
trace is the two latitude circles `longitudeCurve standard (π/6)` (radius `2 + √3/2`) and
`longitudeCurve standard (5π/6)` (radius `2 - √3/2`).

An innermost disc of the flat disc `cutDisc 4 0 (refl (Fin 3)) (1/2)` is the planar disc bounded by
the *inner* latitude: it is an embedded disc of `ℝ³`, its boundary is that latitude circle (which is
simple and essential in the surface, with winding `(1,0)`), its interior lies in the plane `{z = 1/2}`
and meets the surface only at its boundary — because `F ∩ {z = 1/2}` is exactly the two latitudes,
of radii `2 ± √3/2` — and its boundary lies in the flat disc.  Hence
`Work.InnermostDisk.InnermostDiscInput standard (cutDisc 4 0 (refl (Fin 3)) (1/2))`.

The hypothesis of `InnermostDiscInput` (the existence of an essential loop inside the flat disc) is
satisfied there — the inner latitude itself is such a loop — so the statement is not vacuous.  With
`transverseSlice_std_four` and `tameSlice_standard_equator` this completes the body of
`Work.CountedPinch.CountedPlaneInput` at a configuration whose slice is non-empty. -/
theorem innermostDiscInput_standard_equator :
    Work.InnermostDisk.InnermostDiscInput Work.CoreTopology.standard
      (Work.BoxShrink.Core.cutDisc 4
        (WithLp.toLp 2 (![0, 0, 0] : Fin 3 → ℝ)) (Equiv.refl (Fin 3)) (1 / 2)) := by
  rw [boxCenter_eq_zero]
  intro _
  refine ⟨{
    α := longitudeCurve standard (5 * Real.pi / 6)
    simple := longitudeCurve_simple _ _
    essential := longitudeCurve_essential _ _
    mem := fun t => longitudeCurve_mem_cutDisc (5 * Real.pi / 6) t sin_five_pi_div_six
    e := latDisc
    inj := latDisc_injective
    boundary := latDisc_boundary
    e_mem := fun z => latDisc_mem z
    ι := PEmpty
    fintype := inferInstance
    curves := fun i => PEmpty.elim i
    curves_simple := fun i => PEmpty.elim i
    curves_inessential := fun i => PEmpty.elim i
    curves_disjoint := fun i => PEmpty.elim i
    curves_subset := fun i => PEmpty.elim i
    covers := fun z hz hc => (latDisc_no_interior z hz hc).elim }⟩

end

end Work.CountedPinch
