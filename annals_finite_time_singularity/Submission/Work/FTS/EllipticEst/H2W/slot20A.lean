import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.EllipticEst.H2W.z2pzIter2Comm
import Submission.Work.FTS.EllipticEst.H2W.bslOp_zsq_pzIter2
import Submission.Work.FTS.EllipticEst.H2W.angL0weak
import Submission.Work.FTS.EllipticEst.H2W.weakSliceDerivBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! # `slot20A` — the `(2,0)`-slot of `A = z²∂_z²Ψ` with the `γ`-weight

Target: `α⁴ · L2Sq (D_θ²A · Wt α) ≤ K · (α⁴ · P + HkSq α 2 F)` with `A := z²∂_z²Ψ` and

  `P := Σ_{j<3} L2Sq (z²∂_z²(D_z^jΨ) · w/sin(2θ)^{η/2})`

the *pure* part of the `ℋ²`-norm of `A` (identified with `Σ_{j<3} L2Sq(D_z^jA·w/s^{η/2})` by
`z2pzIter2Comm`).

## What is in this file

The **elementary (pointwise) layer** of the reduction of the target to the sharp analytic input
it needs, the statement of that input, and the reduction itself:

* `Az` — the twisted datum `A = z²∂_z²Ψ`;
* `Az_zero_left`, `Az_zero_right` — the slices of `A` vanish at the angular endpoints;
* `zsq_pzIter2` — `A = D_z²Ψ − D_zΨ` on the open quadrant;
* `DthIter_two_eq_pth` — `D_θ²f = sin²(2θ)∂_θ²f + 2 sin(2θ)cos(2θ)∂_θf`;
* `pth_zsq_mul` — `∂_θ(z²g) = z²∂_θg`;
* `quad_core`, `slot20A_pt_le` — the pointwise weight chain
  `(D_θ²A·Wt α)² ≤ 2 (∂_θ²A·w/s^{η/2})² + 8 (∂_θA·w/s^{η/2})²` on the open quadrant;
* `L2Sq_nonneg`, `HkSq_nonneg` — nonnegativity of the two functionals (Mathlib's totalised
  integral takes the value `0` on a non-integrable nonneg integrand, never a negative value);
* `Slot20AHonest` / `Slot20AJunk` / `slot20A_of_sharp` — the two analytic inputs and the
  reduction of the target to them.

## Why the "naive" route does not suffice (see `NOTES_slot20A.md`)

The route proposed in `H2W/NOTES_weakMixedA.md` §2 (reduce the slot to the `η`-weighted second
angular derivative of `A` and invoke `angL0weak` for the datum `A`) is **not sufficient**: if
`A`'s `θ`-profile near an endpoint behaves like `θ^b` with `(γ−1)/2 < b < (3+η)/2`, then the
target's slot `∫(D_θ²A)² sin(2θ)^{−γ}` is honest and non-zero while *every* `η`-weighted
quantity of that route is non-integrable (Bochner value `0`), so a chain
`slot ≤ C·(η-weighted quantities)` is false there.  The target really needs the *`γ`-weighted*
slot estimate for the twisted datum `A` — the `A`-datum analogue of Steps 4–5 of `prop:H2`,
which `H2W/NOTES_mixedA.md` §4 records as the missing sharp analytic chapter.
-/

/-! ## The twisted datum `A = z²∂_z²Ψ` -/

/-- `A = z²∂_z²Ψ`: the radial second derivative of the stream function (the datum of `prop:H2`
whose `ℋ²`-norm is estimated there). -/
def Az (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ

/-- A `θ`-slice which vanishes identically has vanishing iterated `z`-derivatives. -/
theorem pzIter_eq_zero_of_slice_eq_zero {f : ℝ → ℝ → ℝ} {θ₀ : ℝ} (h : ∀ z, f z θ₀ = 0) :
    ∀ (n : ℕ) (z : ℝ), Work.Spaces.pzIter n f z θ₀ = 0 := by
  intro n
  induction n with
  | zero => intro z; exact h z
  | succ k ih =>
      intro z
      have hone : (fun z' => Work.Spaces.pzIter k f z' θ₀) = fun _ => (0 : ℝ) := funext ih
      show deriv (fun z' => Work.Spaces.pzIter k f z' θ₀) z = 0
      rw [hone, deriv_const]

/-- The `θ = 0` — slices of `A = z²∂_z²Ψ` vanish. -/
theorem Az_zero_left (Ψ : ℝ → ℝ → ℝ) (h : ∀ z, Ψ z 0 = 0) (z : ℝ) : Az Ψ z 0 = 0 := by
  simp only [Az, pzIter_eq_zero_of_slice_eq_zero h 2 z, mul_zero]

/-- The `θ = π/2` — slices of `A = z²∂_z²Ψ` vanish. -/
theorem Az_zero_right (Ψ : ℝ → ℝ → ℝ) (h : ∀ z, Ψ z (Real.pi / 2) = 0) (z : ℝ) :
    Az Ψ z (Real.pi / 2) = 0 := by
  simp only [Az, pzIter_eq_zero_of_slice_eq_zero h 2 z, mul_zero]

/-- **`A = D_z²Ψ − D_zΨ` on the open quadrant** (the operator identity `z²∂_z² = D_z² − D_z`). -/
theorem zsq_pzIter2 {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Az Ψ z θ = Work.Spaces.DzIter 2 Ψ z θ - Work.Spaces.DzIter 1 Ψ z θ :=
  Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_eq_open Ψ hΨ hz hθ

/-! ## The expansion of `D_θ²` and the pull-out of the `z²`-weight -/

/-- `(sin 2·)' = 2cos(2·)`. -/
theorem hasDerivAt_sin_two (θ : ℝ) :
    HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (2 * Real.cos (2 * θ)) θ := by
  have h : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h2 := h.sin
  rwa [show Real.cos (2 * θ) * 2 = 2 * Real.cos (2 * θ) by ring] at h2

/-- **The expansion of `D_θ²`**: `D_θ²f = sin²(2θ)·∂_θ²f + 2 sin(2θ)cos(2θ)·∂_θf`. -/
theorem DthIter_two_eq_pth (f : ℝ → ℝ → ℝ) (z θ : ℝ)
    (h2 : DifferentiableAt ℝ (fun t => deriv (fun t' => f z t') t) θ) :
    Work.Spaces.DthIter 2 f z θ
      = (Real.sin (2 * θ)) ^ 2 * Work.Spaces.pthIter 2 f z θ
        + 2 * Real.sin (2 * θ) * Real.cos (2 * θ) * Work.Spaces.pth f z θ := by
  have hs := hasDerivAt_sin_two θ
  have hd : HasDerivAt (fun t : ℝ => deriv (fun t' => f z t') t)
      (deriv (fun t : ℝ => deriv (fun t' => f z t') t) θ) θ := h2.hasDerivAt
  have hmul := hs.mul hd
  show Real.sin (2 * θ) * deriv (fun t : ℝ => Real.sin (2 * t) * deriv (fun t' => f z t') t) θ = _
  rw [show (fun t : ℝ => Real.sin (2 * t) * deriv (fun t' => f z t') t)
      = (fun t : ℝ => Real.sin (2 * t)) * (fun t : ℝ => deriv (fun t' => f z t') t) from rfl]
  rw [hmul.deriv]
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
  ring

/-- **The pull-out**: `∂_θ(z²·g) = z²·∂_θg`. -/
theorem pth_zsq_mul (g : ℝ → ℝ → ℝ) (z θ : ℝ)
    (h : DifferentiableAt ℝ (fun t => g z t) θ) :
    Work.Spaces.pth (fun z θ => z ^ 2 * g z θ) z θ = z ^ 2 * Work.Spaces.pth g z θ := by
  have hd : HasDerivAt (fun t : ℝ => g z t) (deriv (fun t : ℝ => g z t) θ) θ := h.hasDerivAt
  have := hd.const_mul (z ^ 2)
  show deriv (fun t : ℝ => z ^ 2 * g z t) θ = z ^ 2 * deriv (fun t : ℝ => g z t) θ
  exact this.deriv

/-! ## Elementary weight facts -/

/-- `sin(2θ) ∈ [0,1]` on `Iθ`. -/
theorem sin_two_mem {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) ∧ Real.sin (2 * θ) ≤ 1 :=
  ⟨Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩,
    Real.sin_le_one _⟩

/-- `sin(2θ) > 0` on the open interval. -/
theorem sin_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- For `α ≤ 1/4` and `s = sin(2θ) ∈ [0,1]`: `s^{4-γ} ≤ s^{-η}`. -/
theorem rpow_four_sub_gam_le {α : ℝ} (hα4 : α ≤ 1 / 4) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    s ^ ((4 : ℝ) - Work.Spaces.gam α) ≤ s ^ (-(Work.Spaces.eta)) := by
  have hgam : (4 : ℝ) - Work.Spaces.gam α ≠ 0 := by
    simp only [Work.Spaces.gam]; intro hc; linarith
  have heta : -(Work.Spaces.eta) ≠ 0 := by simp only [Work.Spaces.eta]; norm_num
  have hexp : -(Work.Spaces.eta) ≤ (4 : ℝ) - Work.Spaces.gam α := by
    simp only [Work.Spaces.gam, Work.Spaces.eta]; linarith
  rcases eq_or_lt_of_le hs0 with h | h
  · rw [← h, Real.zero_rpow hgam, Real.zero_rpow heta]
  · exact Real.rpow_le_rpow_of_exponent_ge h hs1 hexp

/-- For `α ≤ 1/4` and `s = sin(2θ) ∈ [0,1]`: `s^{2-γ} ≤ s^{-η}`. -/
theorem rpow_two_sub_gam_le {α : ℝ} (hα4 : α ≤ 1 / 4) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    s ^ ((2 : ℝ) - Work.Spaces.gam α) ≤ s ^ (-(Work.Spaces.eta)) := by
  have hgam : (2 : ℝ) - Work.Spaces.gam α ≠ 0 := by
    simp only [Work.Spaces.gam]; intro hc; linarith
  have heta : -(Work.Spaces.eta) ≠ 0 := by simp only [Work.Spaces.eta]; norm_num
  have hexp : -(Work.Spaces.eta) ≤ (2 : ℝ) - Work.Spaces.gam α := by
    simp only [Work.Spaces.gam, Work.Spaces.eta]; linarith
  rcases eq_or_lt_of_le hs0 with h | h
  · rw [← h, Real.zero_rpow hgam, Real.zero_rpow heta]
  · exact Real.rpow_le_rpow_of_exponent_ge h hs1 hexp

/-- `s^{4-γ} = s⁴·s^{-γ}` for `s > 0`. -/
theorem rpow_four_sub_gam_eq {α : ℝ} {s : ℝ} (hs : 0 < s) :
    s ^ ((4 : ℝ) - Work.Spaces.gam α) = s ^ 4 * s ^ (-(Work.Spaces.gam α)) := by
  rw [← Real.rpow_natCast s 4, ← Real.rpow_add hs]
  ring_nf

/-- `s^{2-γ} = s²·s^{-γ}` for `s > 0`. -/
theorem rpow_two_sub_gam_eq {α : ℝ} {s : ℝ} (hs : 0 < s) :
    s ^ ((2 : ℝ) - Work.Spaces.gam α) = s ^ 2 * s ^ (-(Work.Spaces.gam α)) := by
  rw [← Real.rpow_natCast s 2, ← Real.rpow_add hs]
  ring_nf

/-- `(w·s^{-g/2})² = w²·s^{-g}` for `s > 0`. -/
theorem mul_rpow_half_sq {g w s : ℝ} (hs : 0 < s) :
    (w * s ^ (-(g / 2))) ^ 2 = w ^ 2 * s ^ (-g) := by
  rw [mul_pow, ← Real.rpow_natCast (s ^ (-(g / 2))) 2, ← Real.rpow_mul hs.le]
  congr 1
  ring_nf

/-- `(w/s^{g/2})² = w²·s^{-g}` for `s > 0`. -/
theorem div_rpow_half_sq {g w s : ℝ} (hs : 0 < s) :
    (w / s ^ (g / 2)) ^ 2 = w ^ 2 * s ^ (-g) := by
  have h1 : w / s ^ (g / 2) = w * s ^ (-(g / 2)) := by
    rw [div_eq_mul_inv, Real.rpow_neg hs.le]
  rw [h1]
  exact mul_rpow_half_sq hs

/-! ## The pointwise weight chain -/

/-- The algebraic core `(s²X + 2scY)² ≤ 2s⁴X² + 8s²Y²` (valid for `c² ≤ 1`). -/
theorem quad_core {s c X Y : ℝ} (hc2 : c ^ 2 ≤ 1) :
    (s ^ 2 * X + 2 * s * c * Y) ^ 2 ≤ 2 * s ^ 4 * X ^ 2 + 8 * s ^ 2 * Y ^ 2 := by
  have h1 : (0 : ℝ) ≤ 1 - c ^ 2 := by linarith
  have h2 : (0 : ℝ) ≤ (s * Y) ^ 2 * (1 - c ^ 2) := mul_nonneg (sq_nonneg _) h1
  nlinarith [sq_nonneg (s ^ 2 * X - 2 * s * c * Y), h2]

/-- The two weight upgrades, `s ∈ [0,1]`, `α ≤ 1/4`. -/
theorem weight_upgrade {α : ℝ} (hα4 : α ≤ 1 / 4) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (w X Y : ℝ) :
    2 * X ^ 2 * (w ^ 2 * s ^ ((4 : ℝ) - Work.Spaces.gam α))
        + 8 * Y ^ 2 * (w ^ 2 * s ^ ((2 : ℝ) - Work.Spaces.gam α))
      ≤ 2 * X ^ 2 * (w ^ 2 * s ^ (-(Work.Spaces.eta)))
        + 8 * Y ^ 2 * (w ^ 2 * s ^ (-(Work.Spaces.eta))) := by
  have h1 : w ^ 2 * s ^ ((4 : ℝ) - Work.Spaces.gam α) ≤ w ^ 2 * s ^ (-(Work.Spaces.eta)) :=
    mul_le_mul_of_nonneg_left (rpow_four_sub_gam_le hα4 hs0 hs1) (sq_nonneg w)
  have h2 : w ^ 2 * s ^ ((2 : ℝ) - Work.Spaces.gam α) ≤ w ^ 2 * s ^ (-(Work.Spaces.eta)) :=
    mul_le_mul_of_nonneg_left (rpow_two_sub_gam_le hα4 hs0 hs1) (sq_nonneg w)
  have h3 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 2 * X ^ 2 by positivity)
  have h4 := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 8 * Y ^ 2 by positivity)
  linarith

/-- **The pointwise weight chain.**  Given the expansion
`D_θ²f = sin²(2θ)·∂_θ²f + 2 sin(2θ)cos(2θ)·∂_θf` at `(z,θ)` (see `DthIter_two_eq_pth`),

  `(D_θ²f · Wt α)² ≤ 2 (∂_θ²f · w/s^{η/2})² + 8 (∂_θf · w/s^{η/2})²`. -/
theorem slot20A_pt_le (α : ℝ) (hα4 : α ≤ 1 / 4) (F : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hexp : Work.Spaces.DthIter 2 F z θ
      = Real.sin (2 * θ) ^ 2 * Work.Spaces.pthIter 2 F z θ
        + 2 * Real.sin (2 * θ) * Real.cos (2 * θ) * Work.Spaces.pth F z θ) :
    (Work.Spaces.DthIter 2 F z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ 2 * (Work.Spaces.pthIter 2 F z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        + 8 * (Work.Spaces.pth F z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  have hs : 0 < Real.sin (2 * θ) := sin_two_pos hθ
  obtain ⟨hs0, hs1⟩ := sin_two_mem ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hc2 : (Real.cos (2 * θ)) ^ 2 ≤ 1 := by simpa [sq] using Real.cos_sq_le_one (2 * θ)
  -- normalize the two divisions on the right hand side
  have hdiv : ∀ a : ℝ,
      (a * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = (a * Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2 := by
    intro a
    congr 1
    rw [div_eq_mul_inv, Real.rpow_neg hs.le]
    ring
  have hW : (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    mul_rpow_half_sq (g := Work.Spaces.gam α) (w := Work.Spaces.w z) hs
  have hZ : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    rw [← Real.rpow_natCast ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) 2,
      ← Real.rpow_mul hs.le]
    congr 1
    ring
  have hZ2 : ∀ a : ℝ,
      (a * Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2
        = a ^ 2 * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
    intro a
    rw [mul_pow, mul_pow, hZ]
    ring
  rw [hdiv, hdiv, hexp, mul_pow, Work.Spaces.Wt, Work.Spaces.wTheta, hW]
  have hquad : (Real.sin (2 * θ) ^ 2 * Work.Spaces.pthIter 2 F z θ
        + 2 * Real.sin (2 * θ) * Real.cos (2 * θ) * Work.Spaces.pth F z θ) ^ 2
      ≤ 2 * (Real.sin (2 * θ)) ^ 4 * (Work.Spaces.pthIter 2 F z θ) ^ 2
        + 8 * (Real.sin (2 * θ)) ^ 2 * (Work.Spaces.pth F z θ) ^ 2 := by
    have := quad_core (X := Work.Spaces.pthIter 2 F z θ) (Y := Work.Spaces.pth F z θ)
      (s := Real.sin (2 * θ)) (c := Real.cos (2 * θ)) hc2
    simpa only [mul_assoc] using this
  have hstep := mul_le_mul_of_nonneg_right hquad
    (sq_nonneg (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))))
  rw [hW] at hstep
  have hexpand : (2 * (Real.sin (2 * θ)) ^ 4 * (Work.Spaces.pthIter 2 F z θ) ^ 2
        + 8 * (Real.sin (2 * θ)) ^ 2 * (Work.Spaces.pth F z θ) ^ 2)
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      = 2 * (Work.Spaces.pthIter 2 F z θ) ^ 2
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ ((4 : ℝ) - Work.Spaces.gam α))
        + 8 * (Work.Spaces.pth F z θ) ^ 2
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ ((2 : ℝ) - Work.Spaces.gam α)) := by
    rw [rpow_four_sub_gam_eq (α := α) hs, rpow_two_sub_gam_eq (α := α) hs]
    ring
  rw [hexpand] at hstep
  have hup := weight_upgrade hα4 hs0 hs1 (Work.Spaces.w z)
    (Work.Spaces.pthIter 2 F z θ) (Work.Spaces.pth F z θ)
  rw [hZ2, hZ2]
  linarith [hstep, hup]

/-! ## Nonnegativity of the two functionals -/

/-- `L2Sq` is nonnegative (a non-integrable nonneg integrand has Bochner value `0`). -/
theorem L2Sq_nonneg (g : ℝ → ℝ → ℝ) : 0 ≤ Work.Spaces.L2Sq g := by
  rw [Work.Spaces.L2Sq]
  refine integral_nonneg ?_
  intro z
  exact integral_nonneg (fun θ => sq_nonneg _)

/-- The `ℋ^k`-integrand is nonnegative. -/
theorem HkIntegrand_nonneg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    0 ≤ Work.Spaces.HkIntegrand α k f z θ := by
  rw [Work.Spaces.HkIntegrand]
  refine add_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) ?_
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  split_ifs with h
  · exact sq_nonneg _
  · exact le_refl 0

/-- `HkSq` is nonnegative. -/
theorem HkSq_nonneg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) : 0 ≤ Work.Spaces.HkSq α k f := by
  rw [Work.Spaces.HkSq]
  refine integral_nonneg ?_
  intro z
  exact integral_nonneg (fun θ => HkIntegrand_nonneg α k f z θ)

/-- **The `(2,0)`-slot of a function is a summand of its `ℋ²`-integrand** (pointwise). -/
theorem mixed_zero_two_sq_le_HkIntegrand (α : ℝ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) :
    (Work.Spaces.mixed 0 2 F z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 2 F z θ := by
  have hnnj : ∀ i ∈ Finset.range 3, (0 : ℝ) ≤ ∑ j ∈ Finset.range 3,
      (if 1 ≤ i ∧ i + j ≤ 2 then
        (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
    intro i _
    exact Finset.sum_nonneg (fun j _ => by split_ifs with h; exacts [sq_nonneg _, le_refl 0])
  have h1 : (if 1 ≤ 2 ∧ 2 + 0 ≤ 2 then
        (Work.Spaces.mixed 0 2 F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
      ≤ ∑ j ∈ Finset.range 3,
          (if 1 ≤ 2 ∧ 2 + j ≤ 2 then
            (Work.Spaces.mixed j 2 F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
    refine Finset.single_le_sum (s := Finset.range 3)
      (f := fun j => if 1 ≤ 2 ∧ 2 + j ≤ 2 then
        (Work.Spaces.mixed j 2 F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) ?_ ?_
    · intro j _
      split_ifs with h
      · exact sq_nonneg _
      · exact le_refl 0
    · exact Finset.mem_range.mpr (by norm_num : 0 < 3)
  have h2 : (∑ j ∈ Finset.range 3,
        (if 1 ≤ 2 ∧ 2 + j ≤ 2 then
          (Work.Spaces.mixed j 2 F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ ∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3,
          (if 1 ≤ i ∧ i + j ≤ 2 then
            (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
    refine Finset.single_le_sum (s := Finset.range 3)
      (f := fun i => ∑ j ∈ Finset.range 3,
        (if 1 ≤ i ∧ i + j ≤ 2 then
          (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) hnnj ?_
    exact Finset.mem_range.mpr (by norm_num : 2 < 3)
  have hred : (if 1 ≤ 2 ∧ 2 + 0 ≤ 2 then
      (Work.Spaces.mixed 0 2 F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
      = (Work.Spaces.mixed 0 2 F z θ * Work.Spaces.Wt α z θ) ^ 2 := by norm_num
  rw [hred] at h1
  rw [Work.Spaces.HkIntegrand]
  exact le_trans (le_trans h1 h2) (le_add_of_nonneg_left (Finset.sum_nonneg (fun i _ => sq_nonneg _)))

/-- **The `(2,0)`-slot of `F` is dominated by `HkSq α 2 F`** (the source slot). -/
theorem mixed_zero_two_le_HkSq (α : ℝ) (F : ℝ → ℝ → ℝ) (hF : Work.Spaces.HkMem α 2 F) :
    Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 0 2 F z θ * Work.Spaces.Wt α z θ)
      ≤ Work.Spaces.HkSq α 2 F := by
  rw [Work.Spaces.L2Sq, Work.Spaces.HkSq]
  refine integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun z => integral_nonneg (fun θ => sq_nonneg _))) hF.2 ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
  exact integral_mono_of_nonneg (Filter.Eventually.of_forall (fun θ => sq_nonneg _))
    (hF.1 z hz) (Filter.Eventually.of_forall (fun θ => mixed_zero_two_sq_le_HkIntegrand α F z θ))

/-! ## The slots of a function are dominated by its `ℋ²`-norm -/

/-- **A pointwise bound of a square by the `ℋ²`-integrand gives the `L2Sq ≤ HkSq` bound.** -/
theorem L2Sq_sq_le_HkSq_of_le (α : ℝ) (F g : ℝ → ℝ → ℝ) (hF : Work.Spaces.HkMem α 2 F)
    (h2 : ∀ z θ, (g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 2 F z θ) :
    Work.Spaces.L2Sq g ≤ Work.Spaces.HkSq α 2 F := by
  rw [Work.Spaces.L2Sq, Work.Spaces.HkSq]
  refine integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun z => integral_nonneg (fun θ => sq_nonneg _))) hF.2 ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
  exact integral_mono_of_nonneg (Filter.Eventually.of_forall (fun θ => sq_nonneg _))
    (hF.1 z hz) (Filter.Eventually.of_forall (fun θ => h2 z θ))

/-- **A mixed slot of a function is a summand of its `ℋ²`-integrand** (pointwise). -/
theorem mixed_sq_le_HkIntegrand (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) {i j : ℕ}
    (hi : 1 ≤ i) (hij : i + j ≤ k) :
    (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k F z θ := by
  have hik : i ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
  have hjk : j ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
  have hnn : ∀ i' ∈ Finset.range (k + 1), (0 : ℝ) ≤ ∑ j' ∈ Finset.range (k + 1),
      (if 1 ≤ i' ∧ i' + j' ≤ k then
        (Work.Spaces.mixed j' i' F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
    intro i' _
    exact Finset.sum_nonneg (fun j' _ => by split_ifs with h; exacts [sq_nonneg _, le_refl 0])
  have h1 : (if 1 ≤ i ∧ i + j ≤ k then
        (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
      ≤ ∑ j' ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j' ≤ k then
            (Work.Spaces.mixed j' i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
    refine Finset.single_le_sum (s := Finset.range (k + 1))
      (f := fun j' => if 1 ≤ i ∧ i + j' ≤ k then
        (Work.Spaces.mixed j' i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) ?_ hjk
    intro j' _
    split_ifs with h
    · exact sq_nonneg _
    · exact le_refl 0
  have hred : (if 1 ≤ i ∧ i + j ≤ k then
        (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
      = (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 := by
    rw [if_pos ⟨hi, hij⟩]
  rw [hred] at h1
  have h2 : (∑ j' ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j' ≤ k then
          (Work.Spaces.mixed j' i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ ∑ i' ∈ Finset.range (k + 1), ∑ j' ∈ Finset.range (k + 1),
          (if 1 ≤ i' ∧ i' + j' ≤ k then
            (Work.Spaces.mixed j' i' F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
    refine Finset.single_le_sum (s := Finset.range (k + 1))
      (f := fun i' => ∑ j' ∈ Finset.range (k + 1),
        (if 1 ≤ i' ∧ i' + j' ≤ k then
          (Work.Spaces.mixed j' i' F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) hnn hik
  rw [Work.Spaces.HkIntegrand]
  exact le_trans (le_trans h1 h2)
    (le_add_of_nonneg_left (Finset.sum_nonneg (fun i' _ => sq_nonneg _)))

/-- **A pure (`D_z`-only) slot of a function is a summand of its `ℋ²`-integrand** (pointwise). -/
theorem dzIter_sq_le_HkIntegrand (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) {i : ℕ} (hi : i ≤ k) :
    (Work.Spaces.DzIter i F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ Work.Spaces.HkIntegrand α k F z θ := by
  have hik : i ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
  have h1 : (Work.Spaces.DzIter i F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ ∑ i' ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i' F z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
    Finset.single_le_sum (s := Finset.range (k + 1))
      (f := fun i' => (Work.Spaces.DzIter i' F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      (fun i' _ => sq_nonneg _) hik
  rw [Work.Spaces.HkIntegrand]
  exact le_trans h1 (le_add_of_nonneg_right (Finset.sum_nonneg (fun i' _ =>
    Finset.sum_nonneg (fun j' _ => by split_ifs with h; exacts [sq_nonneg _, le_refl 0]))))

/-- **The mixed slots of a function are dominated by its `ℋ²`-norm.** -/
theorem mixed_le_HkSq (α : ℝ) (F : ℝ → ℝ → ℝ) (hF : Work.Spaces.HkMem α 2 F) {i j : ℕ}
    (hi : 1 ≤ i) (hij : i + j ≤ 2) :
    Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ)
      ≤ Work.Spaces.HkSq α 2 F :=
  L2Sq_sq_le_HkSq_of_le α F _ hF (fun z θ => mixed_sq_le_HkIntegrand α 2 F z θ hi hij)

/-- **The pure slots of a function are dominated by its `ℋ²`-norm.** -/
theorem pure_le_HkSq (α : ℝ) (F : ℝ → ℝ → ℝ) (hF : Work.Spaces.HkMem α 2 F) {i : ℕ} (hi : i ≤ 2) :
    Work.Spaces.L2Sq (fun z θ => Work.Spaces.DzIter i F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      ≤ Work.Spaces.HkSq α 2 F :=
  L2Sq_sq_le_HkSq_of_le α F _ hF (fun z θ => dzIter_sq_le_HkIntegrand α 2 F z θ hi)

/-! ## The target's hypothesis block, the honest class for `A`, and the two inputs -/

/-- The target's hypothesis block (unbundled): the paper's class for `(F, Ψ)`. -/
def Slot20Hyps (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) : Prop :=
  (∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ) ∧
  (∀ z, Ψ z 0 = 0) ∧ (∀ z, Ψ z (Real.pi / 2) = 0) ∧
  (∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun z => Ψ z θ) Filter.atTop (nhds 0)) ∧
  Work.Elliptic.OrthCond F ∧ Work.Elliptic.OrthCond Ψ ∧
  (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) ∧
  Work.Spaces.HkMem α 2 F

/-- **The honest class for the twisted datum `A = z²∂_z²Ψ`** (see `NOTES_slot20A.md`): the
equation for `A`, its Dirichlet data, its decay in `z`, both of its solvability conditions, and
the `ℋ⁰`-memberships of `A`, `z²∂_z²A` and `∂_θ²A`.  These are the hypotheses that the `A`-datum
analogue of the paper's Steps 4–5 consumes. -/
def AzHonest (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) : Prop :=
  (∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
    Work.Elliptic.bslOp α (Az Ψ) z θ = z ^ 2 * Work.Spaces.pzIter 2 F z θ) ∧
  (∀ z, Az Ψ z 0 = 0) ∧ (∀ z, Az Ψ z (Real.pi / 2) = 0) ∧
  (∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun z => Az Ψ z θ) Filter.atTop (nhds 0)) ∧
  Work.Elliptic.OrthCond (Az Ψ) ∧
  Work.Elliptic.OrthCond (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 F z θ) ∧
  Work.Spaces.HkMem α 0 (Az Ψ) ∧
  Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Az Ψ) z θ) ∧
  Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 (Az Ψ))

/-- The honest class *without* the decay conjunct.  The decay of `A` is **not** implied by
`Slot20Hyps` (only the decay of `Ψ` is: see the counterexample in `NOTES_slot20A.md` §4), so the
sharp estimate is needed in this stronger form as well. -/
def AzHonestNoDecay (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) : Prop :=
  (∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
    Work.Elliptic.bslOp α (Az Ψ) z θ = z ^ 2 * Work.Spaces.pzIter 2 F z θ) ∧
  (∀ z, Az Ψ z 0 = 0) ∧ (∀ z, Az Ψ z (Real.pi / 2) = 0) ∧
  Work.Elliptic.OrthCond (Az Ψ) ∧
  Work.Elliptic.OrthCond (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 F z θ) ∧
  Work.Spaces.HkMem α 0 (Az Ψ) ∧
  Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Az Ψ) z θ) ∧
  Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 (Az Ψ))

/-- The target's left-hand side. -/
def slotLHS (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ :=
  α ^ 4 * Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 0 2 (Az Ψ) z θ
    * Work.Spaces.Wt α z θ)

/-- The target's right-hand side (with the constant). -/
def slotRHS (K α : ℝ) (F Ψ : ℝ → ℝ → ℝ) : ℝ :=
  K * (α ^ 4 * (∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
      z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
    + Work.Spaces.HkSq α 2 F)

/-- **Input 1 — the honest-class sharp `(2,0)`-slot estimate for the twisted datum `A`**: the
`A`-datum analogue of Steps 4–5 of `prop:H2` (the "missing sharp analytic chapter" of
`NOTES_mixedA.md` §4).  The conclusion drops the pure part.  Delegated (with the review of
`FTS/EllipticEst/H2W/slot20A_shiftSharp`); note the *source* honesty `HkMem α 2 F` — without it
`HkSq α 2 F` can be the junk value `0` (the reviewers' counterexample) — which is the first
conjunct below. -/
def Slot20AHonest (C : ℝ) : Prop :=
  ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Slot20Hyps α F Ψ → AzHonest α F Ψ → slotLHS α Ψ ≤ C * Work.Spaces.HkSq α 2 F

/-- **Input 1' — the decay-free form** of Input 1 (same conclusion, `AzHonest` weakened by
dropping the decay conjunct).  Delegated as `FTS/EllipticEst/H2W/slot20A_shiftStrong`; this is
the form the reduction prefers, since `Slot20Hyps` does **not** imply the decay of `A`
(counterexample in `NOTES_slot20A.md` §4). -/
def Slot20AHonestNoDecay (C : ℝ) : Prop :=
  ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Slot20Hyps α F Ψ → AzHonestNoDecay α F Ψ → slotLHS α Ψ ≤ C * Work.Spaces.HkSq α 2 F

/-- **Input 2 — the remaining (non-honest) case**: the target's inequality for the data of the
class for which the honest class `AzHonest` *fails*.  This is *not* the "junk bridge" of the
earlier draft of this file (which was **false**: `AzHonest`'s decay conjunct can fail while the
slot is an honest positive integral — see `NOTES_slot20A.md` §4); it is the genuinely remaining
case, and it must be proved by the kind of argument that produces the sharp estimate itself
(the pure part is *not* junk in general there). -/
def Slot20ABase (K : ℝ) : Prop :=
  ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Slot20Hyps α F Ψ → ¬ AzHonest α F Ψ → slotLHS α Ψ ≤ slotRHS K α F Ψ

/-- **The reduction.**  The honest-class sharp estimate together with the non-honest case give
the target: in the honest case the pure part of the right-hand side is dropped (it is `≥ 0` by
`L2Sq_nonneg`), in the other case Input 2 *is* the conclusion (with a larger constant). -/
theorem slot20A_of_sharp (hsh : ∃ C : ℝ, 0 < C ∧ Slot20AHonest C)
    (hbase : ∃ K : ℝ, 0 < K ∧ Slot20ABase K) :
    ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Slot20Hyps α F Ψ → slotLHS α Ψ ≤ slotRHS K α F Ψ := by
  obtain ⟨C, hC, hCs⟩ := hsh
  obtain ⟨K₀, hK₀, hKs⟩ := hbase
  have hCm1 : (0 : ℝ) < max C 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨max K₀ (max C 1),
    lt_of_lt_of_le zero_lt_one (le_trans (le_max_right C 1) (le_max_right K₀ (max C 1))), ?_⟩
  intro α F Ψ hα hα4 hhyps
  set P : ℝ := α ^ 4 * (∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
      z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) with hP
  have hpure : 0 ≤ P := by
    rw [hP]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun j _ => L2Sq_nonneg _))
  have hF : 0 ≤ Work.Spaces.HkSq α 2 F := HkSq_nonneg α 2 F
  have hsum : 0 ≤ P + Work.Spaces.HkSq α 2 F := add_nonneg hpure hF
  rcases em (AzHonest α F Ψ) with hA | hA
  · have h1 : slotLHS α Ψ ≤ C * Work.Spaces.HkSq α 2 F := hCs α F Ψ hα hα4 hhyps hA
    have h2 : C * Work.Spaces.HkSq α 2 F ≤ (max C 1) * Work.Spaces.HkSq α 2 F :=
      mul_le_mul_of_nonneg_right (le_max_left C 1) hF
    have h3 : (max C 1) * Work.Spaces.HkSq α 2 F ≤ (max C 1) * (P + Work.Spaces.HkSq α 2 F) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hpure) (le_of_lt hCm1)
    have h4 : (max C 1) * (P + Work.Spaces.HkSq α 2 F)
        ≤ (max K₀ (max C 1)) * (P + Work.Spaces.HkSq α 2 F) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hsum
    have h5 : slotRHS (max K₀ (max C 1)) α F Ψ
        = (max K₀ (max C 1)) * (P + Work.Spaces.HkSq α 2 F) := by
      rw [slotRHS, hP]
    rw [h5]
    linarith
  · have h0 : slotLHS α Ψ ≤ slotRHS K₀ α F Ψ := hKs α F Ψ hα hα4 hhyps hA
    have h6 : slotRHS K₀ α F Ψ = K₀ * (P + Work.Spaces.HkSq α 2 F) := by rw [slotRHS, hP]
    have h7 : K₀ * (P + Work.Spaces.HkSq α 2 F)
        ≤ (max K₀ (max C 1)) * (P + Work.Spaces.HkSq α 2 F) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hsum
    have h8 : slotRHS (max K₀ (max C 1)) α F Ψ
        = (max K₀ (max C 1)) * (P + Work.Spaces.HkSq α 2 F) := by rw [slotRHS, hP]
    rw [h8] at *
    linarith

/-! ## The final assembly (a pure re-packaging of `slot20A_of_sharp`) -/

/-- **The final assembly.**  The two inputs — the honest-class sharp estimate for the twisted
datum and the non-honest case — give the target in the *unbundled* form of its statement.  This
is the step that completes the target as soon as the delegated inputs
(`FTS/EllipticEst/H2W/slot20A_shiftSharp`, `FTS/EllipticEst/H2W/slot20A_base`) are available:
the proof of `slot20A` below is then `exact slot20A_of_inputs ⟨C, hC, …⟩ ⟨K, hK, …⟩`. -/
theorem slot20A_of_inputs (hsh : ∃ C : ℝ, 0 < C ∧ Slot20AHonest C)
    (hbase : ∃ K : ℝ, 0 < K ∧ Slot20ABase K) :
    ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      (∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ) →
      (∀ z, Ψ z 0 = 0) → (∀ z, Ψ z (Real.pi / 2) = 0) →
      (∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun z => Ψ z θ) Filter.atTop (nhds 0)) →
      Work.Elliptic.OrthCond F → Work.Elliptic.OrthCond Ψ →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
      Work.Spaces.HkMem α 2 F →
      α ^ 4 * Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 0 2
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * Work.Spaces.Wt α z θ)
        ≤ K * (α ^ 4 * (∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
              z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
            + Work.Spaces.HkSq α 2 F) := by
  obtain ⟨K, hK, hK'⟩ := slot20A_of_sharp hsh hbase
  exact ⟨K, hK, fun α F Ψ hα hα4 h1 h2 h3 h4 h5 h6 h7 h8 =>
    hK' α F Ψ hα hα4 ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩⟩

/-! ## The target -/

theorem slot20A : ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    (∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ) →
    (∀ z, Ψ z 0 = 0) → (∀ z, Ψ z (Real.pi / 2) = 0) →
    (∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun z => Ψ z θ) Filter.atTop (nhds 0)) →
    Work.Elliptic.OrthCond F → Work.Elliptic.OrthCond Ψ →
    (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
    Work.Spaces.HkMem α 2 F →
    α ^ 4 * Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 0 2
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * Work.Spaces.Wt α z θ)
      ≤ K * (α ^ 4 * (∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
            z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
          + Work.Spaces.HkSq α 2 F) := by
  -- Reduced (in `slot20A_of_sharp`) to the two inputs
  --   * `Slot20AHonest` — the honest-class sharp `(2,0)`-slot estimate for the twisted datum
  --     `A = z²∂_z²Ψ`, i.e. the `A`-datum analogue of Steps 4–5 of `prop:H2` (the missing sharp
  --     analytic chapter recorded in `H2W/NOTES_mixedA.md` §4) — delegated, with review:
  --     `FTS/EllipticEst/H2W/slot20A_shiftSharp` (the review found that the source honesty
  --     `HkMem α 2 F` is needed; it is included in `Slot20Hyps`);
  --   * `Slot20ABase` — the same inequality for the data for which `AzHonest` fails.  An earlier
  --     draft of this file claimed this case is *vacuous* (the slot collapses); that claim is
  --     FALSE (the `z`-decay conjunct of `AzHonest` can fail while the slot is an honest positive
  --     integral — see `NOTES_slot20A.md` §4).  This case must be proved by the same kind of
  --     argument that produces the sharp estimate.
  sorry

end

end Work.FTS.EllipticEst.H2W
