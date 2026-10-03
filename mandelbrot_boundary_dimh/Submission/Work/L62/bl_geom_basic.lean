import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.basic

/-!
# `Work.L62.bl_geom_basic` — the elementary geometry of `τ₀ ∘ π` on the lower component

The target `Work.L62.tau0_Bl_geometry` describes the cylinder neighbourhood
`{0} ∪ τ₀(π(Bl))` of the lower end of the horn map.  This file collects the elementary,
self-contained facts that it (and the lemmas split off it) rest on:

* the algebra of `τ₀ w = -1/w` (`τ₀` is an involution, `‖τ₀ ζ‖ = 1/‖ζ‖`) and of the composite
  `w ↦ τ₀ (π w) = -e^{-2πiw}`, namely `‖τ₀ (π w)‖ = e^{2π Im w}` and its continuity;
* `π` is an open map (`π '' S` is open for open `S`);
* the imaginary part of the lift `log ζ/(2πi)` (as in `Work.L62.avail_up`);
* the two geometric consequences of the interface fields `HornData.upper`/`lower`/`disj`:
  `Bl ⊆ {Im ≤ η}` and `{ζ : e^{2πη} < ‖ζ‖} ⊆ π '' Bl`.
-/

namespace Work.L62

open MandelDim Set Filter Topology Metric
open scoped Topology

noncomputable section

variable {g₀ : ℂ → ℂ} {D : Set ℂ}

/-! ## The algebra of `τ₀` and of `τ₀ ∘ π` -/

/-- `τ₀` is an involution (with the junk value `τ₀ 0 = 0`). -/
theorem tau0_tau0 (x : ℂ) : tau0 (tau0 x) = x := by
  simp only [tau0, div_eq_mul_inv, mul_inv_rev, inv_neg, inv_inv]
  ring

/-- `‖τ₀ ζ‖ = 1/‖ζ‖`. -/
theorem norm_tau0 (ζ : ℂ) : ‖tau0 ζ‖ = 1 / ‖ζ‖ := by
  simp [tau0]

/-- `τ₀ (π w) = -e^{-2πiw}`. -/
theorem tau0_piExp (w : ℂ) :
    tau0 (piExp w) = -(Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))) := by
  rw [tau0, piExp, div_eq_mul_inv, ← Complex.exp_neg]
  ring

/-- `‖τ₀ (π w)‖ = e^{2π Im w}`. -/
theorem norm_tau0_piExp (w : ℂ) : ‖tau0 (piExp w)‖ = Real.exp (2 * Real.pi * w.im) := by
  rw [tau0_piExp, norm_neg, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

/-- The composite `w ↦ τ₀ (π w)` is continuous (it is `-e^{-2πiw}` — the denominator never
vanishes, so the junk value `τ₀ 0 = 0` is never used). -/
theorem continuous_tau0_piExp : Continuous (fun w : ℂ => tau0 (piExp w)) := by
  rw [show (fun w : ℂ => tau0 (piExp w))
      = fun w : ℂ => -(Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))) from
    funext fun w => tau0_piExp w]
  fun_prop

/-- `τ₀` is continuous at every non-zero point. -/
theorem continuousAt_tau0 {x : ℂ} (hx : x ≠ 0) : ContinuousAt tau0 x := by
  rw [show tau0 = fun z : ℂ => (-1 : ℂ) / z from rfl]
  exact continuousAt_const.div continuousAt_id hx

/-- The imaginary part of the lift `log ζ / (2πi)`. -/
theorem log_div_im (ζ : ℂ) :
    (Complex.log ζ / (2 * (Real.pi : ℂ) * Complex.I)).im
      = -(Real.log ‖ζ‖ / (2 * Real.pi)) := by
  rw [Complex.div_im, Complex.log_re, Complex.log_im]
  have h1 : (2 * (Real.pi : ℂ) * Complex.I).re = 0 := by simp
  have h2 : (2 * (Real.pi : ℂ) * Complex.I).im = 2 * Real.pi := by simp
  have h3 : Complex.normSq ((2 : ℂ) * Real.pi * Complex.I) = (2 * Real.pi) ^ 2 := by
    rw [show ((2 : ℂ) * Real.pi * Complex.I) = ↑(2 * Real.pi) * Complex.I by push_cast; ring]
    rw [Complex.normSq_apply]
    simp
    ring
  rw [h1, h2, h3]
  field_simp
  ring

/-! ## `π` is an open map -/

theorem isOpenMap_piExp : IsOpenMap piExp := by
  have he : piExp = fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * w) := rfl
  rw [he]
  have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
  have h2 : (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * w))
      = Complex.exp ∘ ⇑(Homeomorph.mulLeft₀ (2 * (Real.pi : ℂ) * Complex.I) hc) := by
    funext w
    rw [Function.comp_apply, Homeomorph.coe_mulLeft₀]
  rw [h2]
  exact Complex.isOpenMap_exp.comp (Homeomorph.mulLeft₀ _ hc).isOpenMap

theorem isOpen_piExp_image {S : Set ℂ} (hS : IsOpen S) : IsOpen (piExp '' S) := by
  rw [isOpen_iff_mem_nhds]
  rintro ζ ⟨w, hw, rfl⟩
  exact isOpenMap_piExp.image_mem_nhds (hS.mem_nhds hw)

/-! ## The geometry of `Bl` -/

/-- `Bl` is bounded above by `η` (otherwise it would meet `Bu`). -/
theorem Bl_im_le (d : ParabData g₀ D) (hd : HornData d) {w : ℂ} (hw : w ∈ hd.Bl) :
    w.im ≤ hd.η := by
  by_contra h
  exact hd.disj.le_bot ⟨hd.upper (lt_of_not_ge h), hw⟩

/-- Every point of modulus `> e^{2πη}` has a lift below the line `Im = -η`, hence lies in
`π '' Bl`: the principal lift `log ζ/(2πi)` has imaginary part `-log‖ζ‖/(2π) < -η`. -/
theorem mem_piExp_image_Bl_of_norm_gt (d : ParabData g₀ D) (hd : HornData d) {ζ : ℂ}
    (hζ : ζ ≠ 0) (h : Real.exp (2 * Real.pi * hd.η) < ‖ζ‖) : ζ ∈ piExp '' hd.Bl := by
  refine ⟨Complex.log ζ / (2 * (Real.pi : ℂ) * Complex.I), hd.lower ?_,
    Work.Horn.MandelDim.piExp_log_div ζ hζ⟩
  have hpos : (0 : ℝ) < ‖ζ‖ := norm_pos_iff.mpr hζ
  have hlog : 2 * Real.pi * hd.η < Real.log ‖ζ‖ := by
    have h1 := Real.log_lt_log (Real.exp_pos _) h
    rwa [Real.log_exp] at h1
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have h2 : hd.η < Real.log ‖ζ‖ / (2 * Real.pi) := by
    have := (lt_div_iff₀ h2pi).mpr (by linarith : hd.η * (2 * Real.pi) < Real.log ‖ζ‖)
    exact this
  show (Complex.log ζ / (2 * (Real.pi : ℂ) * Complex.I)).im < -hd.η
  rw [log_div_im]
  linarith

end

end Work.L62
