/-
# Propagation from above: largeness spreads to a set of definite measure

This is the missing half of the Harnack argument.  The from-below sliding-paraboloid method
(`Submission.Savin.Measure`, `Enlarge`, `Decay`, `WeakLEps`) shows that *smallness* spreads: the
contact sets are dense in measure and their points have small values, whence the weak `L^ε`
estimate for the superlevel sets.  The converse implication -- a point where the perturbation
`Φ = u - Q` is large forces a set of definite measure where `Φ` is still essentially as large --
is what turns a measure estimate into a *pointwise* bound (Harnack's inequality).

The proof uses the from-above contact bound `Submission.contact_bound_above_sigma2`, which requires
the *positive branch* but no smallness condition on the opening.  Consequently, unlike the
from-below chain, no barrier/growth lemma is needed: one slides paraboloids from above directly with
the opening dictated by the levels and applies the measure estimate
`Submission.contactSetAbove_measure`.

Geometric content.  Let `Φ` be a perturbation with `s2 (A + D²Φ) = 1`, `trOp (A + D²Φ) > 0`
(the perturbation of a solution `u` of `σ₂ = 1` with `Δu > 0` with respect to the quadratic
solution `Q`, `A = D²Q`).  Suppose `Φ x₀ ≥ H` and `Φ ≤ H'` on `closedBall x₀ b` (Savin's
dichotomy hypothesis).  Slide from above with opening `ã` and vertex in `closedBall x₀ (ηb)`.
- the paraboloid comparison at the centre `x₀` forces every minimiser to lie in `closedBall x₀ (b/2)`
  as soon as `ã b² > 2 (H' - H)/(1/4 - η)`;
- at a contact point the value of `Φ` is at least `H - ã b² η/2`;
- `contactSetAbove_measure` bounds the measure of the vertex ball by the measure of the contact set,
  so the contact set has measure at least `(ηb)⁴/(1 + 4c'/c)⁴` and all its points satisfy the
  level bound.

Choosing `η` universal and `ã b²` proportional to `H' - H` (so that the contact points still
satisfy `Φ ≥ H(1/2 + 1/M)` when `H' = M H`) gives exactly Savin's propagation step.
-/
import Mathlib
import ChallengeDeps
import Submission.Savin.MeasureAbove
import Submission.Savin.Harnack

open Metric MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace Topology ENNReal Pointwise

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable section

/-- Multiplying a function by a constant multiplies its Hessian operator by the same constant. -/
theorem hessOp_const_mul (c : ℝ) {φ : ℝ⁴ → ℝ} {x : ℝ⁴} (hφ : ContDiffAt ℝ 2 φ x) :
    hessOp (fun y => c * φ y) x = c • hessOp φ x := by
  have hφc : ContDiffAt ℝ 2 (fun y : ℝ⁴ => c * φ y) x := by
    simpa only [Pi.smul_apply, smul_eq_mul] using hφ.const_smul c
  refine clm_eq_of_inner_self_eq (hessOp_symm_of_contDiffAt hφc)
    (LinearMap.IsSymmetric.smul (by simp) (hessOp_symm_of_contDiffAt hφ)) fun v => ?_
  have hkey : iteratedFDeriv ℝ 2 (fun y : ℝ⁴ => c * φ y) x = c • iteratedFDeriv ℝ 2 φ x := by
    have hfun : (fun y : ℝ⁴ => c * φ y) = c • φ := by
      funext y; exact (smul_eq_mul c (φ y)).symm
    rw [hfun]
    exact iteratedFDeriv_const_smul_apply hφ
  have h1 : ⟪hessOp (fun y : ℝ⁴ => c * φ y) x v, v⟫
      = iteratedFDeriv ℝ 2 (fun y : ℝ⁴ => c * φ y) x ![v, v] := by
    rw [show hessOp (fun y : ℝ⁴ => c * φ y) x
        = InnerProductSpace.continuousLinearMapOfBilin
            (fderiv ℝ (fderiv ℝ (fun y : ℝ⁴ => c * φ y)) x) from rfl,
      InnerProductSpace.continuousLinearMapOfBilin_apply]
    exact (iteratedFDeriv_two_apply (𝕜 := ℝ) (fun y : ℝ⁴ => c * φ y) x ![v, v]).symm
  have h2 : ⟪hessOp φ x v, v⟫ = iteratedFDeriv ℝ 2 φ x ![v, v] := by
    rw [show hessOp φ x = InnerProductSpace.continuousLinearMapOfBilin
            (fderiv ℝ (fderiv ℝ φ) x) from rfl,
      InnerProductSpace.continuousLinearMapOfBilin_apply]
    exact (iteratedFDeriv_two_apply (𝕜 := ℝ) φ x ![v, v]).symm
  rw [h1, hkey]
  simp only [ContinuousMultilinearMap.smul_apply, ContinuousLinearMap.smul_apply,
    real_inner_smul_left, h2, smul_eq_mul]

/-- **Propagation from above** (normalised frame).  Let `w : ℝ⁴ → ℝ` be a `C²` perturbation with
`s2 (A + D²w) = 1` and `trOp (A + D²w) > 0` on `ball 0 (3/2)`, where `A` is a fixed symmetric
operator with `s2 A = 1`, `trOp A > 0` and `c ≤ cofOp A ≤ c'` in the quadratic form sense.
Suppose `μ ≤ w 0`, `w ≤ ν` on `closedBall 0 1`, `η ≤ 1/8`, and let `g > 0` be an opening with
`ν - μ < g(1/4-η)/2`.  Then a set of measure at least `η⁴/(1+4c'/c)⁴` inside `closedBall 0 (1/2)`
satisfies `w ≥ μ - gη²/2`.

Geometrically: sliding paraboloids of opening `g` from above with vertex in `closedBall 0 η`, one
checks that the minimiser over `closedBall 0 1` lies in `closedBall 0 (1/2)` (the value at `0` beats
the outside values by `g(1/4-η)/2 > ν - μ`), so every vertex is realised; the level loss at a
contact point is at most `(g/2)η²` because `w x ≥ w 0 + (g/2)(‖x-y‖²-‖y‖²) ≥ μ - (g/2)‖y‖²`. -/
theorem propagation_above {w : ℝ⁴ → ℝ} {A : ℝ⁴ →L[ℝ] ℝ⁴} (hA : A.IsSymmetric)
    (hA1 : s2 A = 1) (htrA : 0 < trOp A)
    (hw : ContDiffOn ℝ 2 w (ball 0 (3 / 2)))
    (heq : ∀ x ∈ ball 0 (3 / 2), s2 (A + hessOp w x) = 1)
    (hpos : ∀ x ∈ ball 0 (3 / 2), 0 < trOp (A + hessOp w x))
    {c c' : ℝ} (hc : 0 < c)
    (hcq : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪cofOp A v, v⟫)
    (hcq' : ∀ v : ℝ⁴, ⟪cofOp A v, v⟫ ≤ c' * ‖v‖ ^ 2)
    {μ ν μ' η g : ℝ} (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hg : 0 < g)
    (hw0 : μ ≤ w 0) (hsup : ∀ z ∈ closedBall 0 1, w z ≤ ν)
    (hwit : ν - μ < g * (1 / 4 - η) / 2)
    (hlevel : μ - g * η ^ 2 / 2 ≥ μ') :
    volume (closedBall (0 : ℝ⁴) η) ≤
      ENNReal.ofReal ((1 + 4 * c' / c) ^ 4) *
        volume ({z : ℝ⁴ | μ' ≤ w z} ∩ closedBall (0 : ℝ⁴) (1 / 2)) := by
  have hνμ : μ ≤ ν := le_trans hw0 (hsup 0 (by simp))
  have hq : 0 < 1 / 4 - η := by linarith
  -- the vertex property: every `y ∈ closedBall 0 η` occurs as a from-above vertex
  have hcontact : ∀ y ∈ closedBall (0 : ℝ⁴) η, ∃ x ∈ closedBall 0 (1 / 2),
      ∀ z ∈ closedBall 0 1,
        -w x + g / 2 * ‖x - y‖ ^ 2 ≤ -w z + g / 2 * ‖z - y‖ ^ 2 := by
    intro y hy
    have hyη : ‖y‖ ≤ η := by
      have := mem_closedBall.mp hy; rwa [dist_zero_right] at this
    have hcont : ContinuousOn (fun z : ℝ⁴ => -w z + g / 2 * ‖z - y‖ ^ 2) (closedBall 0 1) := by
      have h1 : ContinuousOn w (closedBall (0 : ℝ⁴) 1) :=
        hw.continuousOn.mono (closedBall_subset_ball (by norm_num))
      exact (h1.neg).add (Continuous.const_mul
        ((continuous_id.sub continuous_const).norm.pow 2) (g / 2) |>.continuousOn)
    obtain ⟨x, hxmem, hxmin⟩ := (isCompact_closedBall (0 : ℝ⁴) 1).exists_isMinOn
      ⟨0, by simp⟩ hcont
    have hxmin' : ∀ z ∈ closedBall (0 : ℝ⁴) 1,
        -w x + g / 2 * ‖x - y‖ ^ 2 ≤ -w z + g / 2 * ‖z - y‖ ^ 2 :=
      fun z hz => hxmin hz
    have hxhalf : ‖x‖ < 1 / 2 := by
      by_contra hcon
      push_neg at hcon
      have hgx : -w x + g / 2 * ‖x - y‖ ^ 2 ≥ -ν + g / 2 * (1 / 2 - η) ^ 2 := by
        have hwx : w x ≤ ν := hsup x hxmem
        have h2 : 1 / 2 - η ≤ ‖x - y‖ := by
          have h3 : ‖x‖ - ‖y‖ ≤ ‖x - y‖ :=
            le_trans (le_abs_self _) (abs_norm_sub_norm_le x y)
          linarith
        have h4 : 0 ≤ 1 / 2 - η := by linarith
        have h5 : (1 / 2 - η) ^ 2 ≤ ‖x - y‖ ^ 2 := pow_le_pow_left₀ h4 h2 2
        have h6 : 0 ≤ g / 2 := by linarith
        nlinarith [mul_le_mul_of_nonneg_left h5 h6]
      have hg0 : -w (0 : ℝ⁴) + g / 2 * ‖(0 : ℝ⁴) - y‖ ^ 2 ≤ -μ + g / 2 * η ^ 2 := by
        have h2 : ‖(0 : ℝ⁴) - y‖ = ‖y‖ := by rw [zero_sub, norm_neg]
        have h3 : ‖y‖ ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ (norm_nonneg y) hyη 2
        have h4 : 0 ≤ g / 2 := by linarith
        have h5 := mul_le_mul_of_nonneg_left h3 h4
        rw [h2]; nlinarith [hw0, h5]
      have hkey : g / 2 * ((1 / 2 - η) ^ 2 - η ^ 2) > ν - μ := by
        nlinarith [hwit, hq]
      have hcontra := hxmin' 0 (by simp)
      nlinarith [hcontra, hgx, hg0, hkey]
    exact ⟨x, by rw [mem_closedBall, dist_zero_right]; exact le_of_lt hxhalf, hxmin'⟩
  have hmeas := contactSetAbove_measure hw hA hA1 htrA heq hpos hc hg hcq hcq'
    isClosed_closedBall hcontact
  refine le_trans hmeas (mul_le_mul_of_nonneg_left (measure_mono ?_) (by simp))
  intro x hx
  rw [mem_contactSetAbove] at hx
  obtain ⟨hxhalf, hxy, hxmin⟩ := hx
  have hyη : ‖slideMapAbove g w x‖ ≤ η := by
    have := mem_closedBall.mp hxy; rwa [dist_zero_right] at this
  have h0 : (0 : ℝ⁴) ∈ closedBall 0 1 := by simp
  have hb : -w x + g / 2 * ‖x - slideMapAbove g w x‖ ^ 2
      ≤ -w 0 + g / 2 * ‖slideMapAbove g w x‖ ^ 2 := by
    have h := hxmin 0 h0
    rwa [zero_sub, norm_neg] at h
  have hsq : g / 2 * (‖x - slideMapAbove g w x‖ ^ 2 - ‖slideMapAbove g w x‖ ^ 2)
      ≥ -(g / 2 * η ^ 2) := by
    have h1 : ‖x - slideMapAbove g w x‖ ^ 2 ≥ 0 := sq_nonneg _
    have h2 : ‖slideMapAbove g w x‖ ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hyη 2
    have h3 : 0 ≤ g / 2 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h2 h3]
  have hfinal : μ' ≤ w x := by
    have h4 : w x ≥ w 0 + g / 2 * (‖x - slideMapAbove g w x‖ ^ 2
        - ‖slideMapAbove g w x‖ ^ 2) := by linarith
    linarith [hlevel, hsq, hw0]
  exact ⟨hfinal, hxhalf⟩

/-- Rescaling a set by `b > 0` about the centre `x₀` multiplies its Lebesgue measure by `b⁴`. -/
theorem volume_image_add_smul (x₀ : ℝ⁴) {b : ℝ} (hb : 0 < b) (S : Set ℝ⁴) :
    volume ((fun y : ℝ⁴ => x₀ + b • y) '' S) = ENNReal.ofReal (b ^ 4) * volume S := by
  have hcomp : (fun y : ℝ⁴ => x₀ + b • y)
      = (fun z : ℝ⁴ => x₀ + z) ∘ (fun y : ℝ⁴ => b • y) := rfl
  rw [hcomp, Set.image_comp, Set.image_smul]
  have htrans : volume ((fun z : ℝ⁴ => x₀ + z) '' (b • S)) = volume (b • S) := by
    have h := measure_preimage_add (volume : Measure ℝ⁴) x₀ ((fun z : ℝ⁴ => x₀ + z) '' (b • S))
    rw [← h]
    congr 1
    ext z
    constructor
    · rintro ⟨w, hw, hwz⟩
      have hwz' : w = z := add_left_cancel hwz
      rwa [hwz'] at hw
    · intro hz
      exact ⟨z, hz, rfl⟩
  rw [htrans, MeasureTheory.Measure.addHaar_smul]
  rw [show |b ^ Module.finrank ℝ ℝ⁴| = b ^ 4 by
    rw [finrank_euclideanSpace_fin, abs_of_pos (pow_pos hb 4)]]


/-- **Propagation from above** (localised form).  Let `Φ` be a `C²` perturbation on `ball x₀ (3b/2)`
with `s2 (A + D²Φ) = 1`, `trOp (A + D²Φ) > 0` and `c ≤ cofOp A ≤ c'` on that ball.  If
`H ≤ Φ x₀`, `Φ ≤ H'` on `closedBall x₀ b`, and `H' - H < b² g(1/4-η)/2` for some opening `g > 0`
(e.g. `g = 4(H'-H)/(b²(1/4-η))`), then a set of measure at least `(ηb)⁴/(1+4c'/c)⁴` inside
`closedBall x₀ (b/2)` satisfies `Φ ≥ H - b²gη²/2`.

Note that there is NO smallness condition on the opening or on `b`: only the positive-branch
hypothesis (hidden in the equation for `Φ`) is used. -/
theorem propagation_above_shifted {Φ : ℝ⁴ → ℝ} {A : ℝ⁴ →L[ℝ] ℝ⁴} {x₀ : ℝ⁴} {b H H' η g L : ℝ}
    (hA : A.IsSymmetric) (hA1 : s2 A = 1) (htrA : 0 < trOp A)
    (hb : 0 < b)
    (hΦ : ContDiffOn ℝ 2 Φ (ball x₀ (3 * b / 2)))
    (heq : ∀ x ∈ ball x₀ (3 * b / 2), s2 (A + hessOp Φ x) = 1)
    (hpos : ∀ x ∈ ball x₀ (3 * b / 2), 0 < trOp (A + hessOp Φ x))
    {c c' : ℝ} (hc : 0 < c)
    (hcq : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪cofOp A v, v⟫)
    (hcq' : ∀ v : ℝ⁴, ⟪cofOp A v, v⟫ ≤ c' * ‖v‖ ^ 2)
    (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hg : 0 < g)
    (hH : H ≤ Φ x₀) (hsup : ∀ z ∈ closedBall x₀ b, Φ z ≤ H')
    (hwit : H' - H < b ^ 2 * (g * (1 / 4 - η) / 2))
    (hlevel : H - b ^ 2 * (g * η ^ 2 / 2) ≥ L) :
    volume (closedBall x₀ (η * b)) ≤
      ENNReal.ofReal ((1 + 4 * c' / c) ^ 4) *
        volume ({z : ℝ⁴ | L ≤ Φ z} ∩ closedBall x₀ (b / 2)) := by
  have hb2 : (0 : ℝ) < b * b := by positivity
  have hbne : b * b ≠ 0 := ne_of_gt hb2
  set w : ℝ⁴ → ℝ := fun y => (b * b)⁻¹ * Φ (x₀ + b • y) with hwdef
  -- geometry of the rescaling
  have hball1 : ∀ y : ℝ⁴, ‖x₀ + b • y - x₀‖ = b * ‖y‖ := by
    intro y
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hb]
  have hmap : ∀ y : ℝ⁴, (x₀ + b • y ∈ ball x₀ (3 * b / 2)) ↔ y ∈ ball 0 (3 / 2) := by
    intro y
    simp only [mem_ball, dist_eq_norm, hball1 y, sub_zero]
    constructor <;> intro h <;> nlinarith [norm_nonneg y]
  have hΦaff : ContDiffOn ℝ 2 (fun y : ℝ⁴ => Φ (x₀ + b • y)) (ball 0 (3 / 2)) := by
    refine hΦ.comp ((contDiff_const.add (contDiff_id.const_smul b)).contDiffOn) ?_
    intro y hy
    exact (hmap y).mpr hy
  have hw : ContDiffOn ℝ 2 w (ball 0 (3 / 2)) := by
    have h2 := hΦaff.const_smul ((b * b)⁻¹)
    simpa only [hwdef, Pi.smul_apply, smul_eq_mul] using h2
  have hhess : ∀ y ∈ ball 0 (3 / 2), hessOp w y = hessOp Φ (x₀ + b • y) := by
    intro y hy
    have hy' : x₀ + b • y ∈ ball x₀ (3 * b / 2) := (hmap y).mpr hy
    have hcd : ContDiffAt ℝ 2 Φ (x₀ + b • y) :=
      hΦ.contDiffAt (isOpen_ball.mem_nhds hy')
    have hcdaff : ContDiffAt ℝ 2 (fun z : ℝ⁴ => Φ (x₀ + b • z)) y :=
      hΦaff.contDiffAt (isOpen_ball.mem_nhds hy)
    have hmul : hessOp w y = (b * b)⁻¹ • hessOp (fun z : ℝ⁴ => Φ (x₀ + b • z)) y := by
      rw [hwdef]
      exact hessOp_const_mul _ hcdaff
    have h1 : (b * b)⁻¹ * (b * b) = 1 := inv_mul_cancel₀ hbne
    calc hessOp w y = (b * b)⁻¹ • hessOp (fun z : ℝ⁴ => Φ (x₀ + b • z)) y := hmul
      _ = (b * b)⁻¹ • ((b * b) • hessOp Φ (x₀ + b • y)) := by rw [hessOp_comp_affine hcd]
      _ = ((b * b)⁻¹ * (b * b)) • hessOp Φ (x₀ + b • y) := by rw [smul_smul]
      _ = hessOp Φ (x₀ + b • y) := by rw [h1, one_smul]
  have heqw : ∀ y ∈ ball 0 (3 / 2), s2 (A + hessOp w y) = 1 := by
    intro y hy
    rw [hhess y hy]
    exact heq _ ((hmap y).mpr hy)
  have hposw : ∀ y ∈ ball 0 (3 / 2), 0 < trOp (A + hessOp w y) := by
    intro y hy
    rw [hhess y hy]
    exact hpos _ ((hmap y).mpr hy)
  -- the level data
  have hwval : ∀ y : ℝ⁴, w y = Φ (x₀ + b • y) / (b * b) := by
    intro y
    rw [hwdef, div_eq_inv_mul]
  have hw0 : H / (b * b) ≤ w 0 := by
    rw [hwval 0, smul_zero, add_zero]
    exact div_le_div_of_nonneg_right hH hb2.le
  have hsupw : ∀ z ∈ closedBall 0 1, w z ≤ H' / (b * b) := by
    intro z hz
    have hmem : x₀ + b • z ∈ closedBall x₀ b := by
      simp only [mem_closedBall, dist_eq_norm, hball1 z]
      have hz1 : ‖z‖ ≤ 1 := by simpa [mem_closedBall, dist_zero_right] using hz
      nlinarith [norm_nonneg z]
    have h1 := hsup _ hmem
    rw [hwval z]
    exact div_le_div_of_nonneg_right h1 hb2.le
  have hwit' : H' / (b * b) - H / (b * b) < g * (1 / 4 - η) / 2 := by
    have e : H' / (b * b) - H / (b * b) = (H' - H) / (b * b) := by ring
    rw [e, div_lt_iff₀ hb2]
    calc H' - H < b ^ 2 * (g * (1 / 4 - η) / 2) := hwit
      _ = (g * (1 / 4 - η) / 2) * (b * b) := by ring
  have hlevel' : H / (b * b) - g * η ^ 2 / 2 ≥ L / (b * b) := by
    have e : H / (b * b) - g * η ^ 2 / 2 = (H - b ^ 2 * (g * η ^ 2 / 2)) / (b * b) := by
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_right hlevel hb2.le
  have hmain := propagation_above hA hA1 htrA hw heqw hposw hc hcq hcq' hη hη8 hg
    hw0 hsupw hwit' hlevel'
  -- the set relation between the two frames
  have hset : {z : ℝ⁴ | L ≤ Φ z} ∩ closedBall x₀ (b / 2)
      = (fun y : ℝ⁴ => x₀ + b • y) '' ({z : ℝ⁴ | L / (b * b) ≤ w z} ∩ closedBall 0 (1 / 2)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hx1, hx2⟩ := hx
      have hx2' : ‖x - x₀‖ ≤ b / 2 := by
        simpa [mem_closedBall, dist_eq_norm] using hx2
      have hval : b • (b⁻¹ • (x - x₀)) = x - x₀ := by
        rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hb), one_smul]
      refine ⟨b⁻¹ • (x - x₀), ⟨?_, ?_⟩, ?_⟩
      · change L / (b * b) ≤ w (b⁻¹ • (x - x₀))
        rw [hwval, hval, add_sub_cancel]
        exact div_le_div_of_nonneg_right hx1 hb2.le
      · rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hb), inv_mul_le_iff₀ hb]
        linarith
      · change x₀ + b • (b⁻¹ • (x - x₀)) = x
        rw [hval, add_sub_cancel]
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · change L / (b * b) ≤ w y at hy1
        rw [hwval] at hy1
        have h2 : L / (b * b) * (b * b) ≤ Φ (x₀ + b • y) / (b * b) * (b * b) :=
          mul_le_mul_of_nonneg_right hy1 hb2.le
        rwa [div_mul_cancel₀ L hbne, div_mul_cancel₀ (Φ (x₀ + b • y)) hbne] at h2
      · rw [mem_closedBall, dist_eq_norm, hball1 y]
        have hy2' : ‖y‖ ≤ 1 / 2 := by simpa [mem_closedBall, dist_zero_right] using hy2
        nlinarith [norm_nonneg y]
  -- the ball also rescales
  have hballimg : closedBall x₀ (η * b) = (fun y : ℝ⁴ => x₀ + b • y) '' closedBall 0 η := by
    ext x
    constructor
    · intro hx
      have hx' : ‖x - x₀‖ ≤ η * b := by simpa [mem_closedBall, dist_eq_norm] using hx
      refine ⟨b⁻¹ • (x - x₀), ?_, ?_⟩
      · rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hb), inv_mul_le_iff₀ hb]
        linarith
      · change x₀ + b • (b⁻¹ • (x - x₀)) = x
        rw [show b • (b⁻¹ • (x - x₀)) = x - x₀ from by
          rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hb), one_smul], add_sub_cancel]
    · rintro ⟨y, hy, rfl⟩
      rw [mem_closedBall, dist_eq_norm, hball1 y]
      have hy' : ‖y‖ ≤ η := by simpa [mem_closedBall, dist_zero_right] using hy
      nlinarith [norm_nonneg y]
  rw [hballimg, volume_image_add_smul x₀ hb, hset, volume_image_add_smul x₀ hb]
  calc ENNReal.ofReal (b ^ 4) * volume (closedBall (0 : ℝ⁴) η)
      ≤ ENNReal.ofReal (b ^ 4) * (ENNReal.ofReal ((1 + 4 * c' / c) ^ 4) *
          volume ({z : ℝ⁴ | L / (b * b) ≤ w z} ∩ closedBall 0 (1 / 2))) :=
        mul_le_mul_of_nonneg_left hmain (by simp)
    _ = ENNReal.ofReal ((1 + 4 * c' / c) ^ 4) *
          (ENNReal.ofReal (b ^ 4) *
            volume ({z : ℝ⁴ | L / (b * b) ≤ w z} ∩ closedBall 0 (1 / 2))) := by
        rw [← mul_assoc, mul_comm (ENNReal.ofReal (b ^ 4))
          (ENNReal.ofReal ((1 + 4 * c' / c) ^ 4)), mul_assoc]

/-- **The propagation step used in the Harnack chain.**  With `M ≥ 4`, an opening `η > 0` with
`η ≤ 1/16` and `8(M-1)η² ≤ 1 - 2/M` (e.g. `η = 1/(8√M)`), and NO smallness condition on `b`:
if `Φ x₀ ≥ H > 0` and `Φ ≤ MH` on `closedBall x₀ b`, then a set of measure at least
`(ηb)⁴/(1+4c'/c)⁴` inside `closedBall x₀ (b/2)` satisfies `Φ ≥ 2H/M`.

(The opening is `g = 16(MH-H)/b²`, for which `H' - H < b²g(1/4-η)/2` because `η ≤ 1/16` gives
`8(1/4-η) > 1`, and the level loss is `b²gη²/2 = 8(M-1)Hη² ≤ H(1-2/M)`.) -/
theorem propagation_step {Φ : ℝ⁴ → ℝ} {A : ℝ⁴ →L[ℝ] ℝ⁴} {x₀ : ℝ⁴} {b M H η : ℝ}
    (hA : A.IsSymmetric) (hA1 : s2 A = 1) (htrA : 0 < trOp A)
    (hb : 0 < b) (hM : 4 ≤ M) (hHpos : 0 < H)
    (hη : 0 < η) (hη16 : η ≤ 1 / 16) (hlev0 : 8 * (M - 1) * η ^ 2 ≤ 1 - 2 / M)
    (hΦ : ContDiffOn ℝ 2 Φ (ball x₀ (3 * b / 2)))
    (heq : ∀ x ∈ ball x₀ (3 * b / 2), s2 (A + hessOp Φ x) = 1)
    (hpos : ∀ x ∈ ball x₀ (3 * b / 2), 0 < trOp (A + hessOp Φ x))
    {c c' : ℝ} (hc : 0 < c)
    (hcq : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪cofOp A v, v⟫)
    (hcq' : ∀ v : ℝ⁴, ⟪cofOp A v, v⟫ ≤ c' * ‖v‖ ^ 2)
    (hH : H ≤ Φ x₀) (hsup : ∀ z ∈ closedBall x₀ b, Φ z ≤ M * H) :
    volume (closedBall x₀ (η * b)) ≤
      ENNReal.ofReal ((1 + 4 * c' / c) ^ 4) *
        volume ({z : ℝ⁴ | 2 * H / M ≤ Φ z} ∩ closedBall x₀ (b / 2)) := by
  have hMpos : 0 < M := by linarith
  have hMb : b * b ≠ 0 := by positivity
  have hη8 : η ≤ 1 / 8 := by linarith
  set g : ℝ := 16 * (M * H - H) / (b * b) with hgdef
  have hgpos : 0 < g := by
    have h1 : 0 < M * H - H := by nlinarith
    rw [hgdef]
    exact div_pos (by linarith) (by positivity)
  -- the witness condition: `8(1/4-η) > 1`
  have hwit : M * H - H < b ^ 2 * (g * (1 / 4 - η) / 2) := by
    have hA' : 16 * (M * H - H) / (b * b) * (1 / 4 - η) / 2
        = (8 * (M * H - H) * (1 / 4 - η)) / (b * b) := by ring_nf
    rw [hgdef, hA', pow_two,
      show b * b * ((8 * (M * H - H) * (1 / 4 - η)) / (b * b))
        = 8 * (M * H - H) * (1 / 4 - η) from by
          rw [mul_comm (b * b), div_mul_cancel₀ _ hMb]]
    have h1 : 0 < M * H - H := by nlinarith
    nlinarith [hη16, h1]
  -- the level bound
  have hlevel : H - b ^ 2 * (g * η ^ 2 / 2) ≥ 2 * H / M := by
    have hA' : 16 * (M * H - H) / (b * b) * η ^ 2 / 2
        = (8 * (M * H - H) * η ^ 2) / (b * b) := by ring_nf
    rw [hgdef, hA', pow_two, ge_iff_le,
      show b * b * ((8 * (M * H - H) * η ^ 2) / (b * b))
        = 8 * (M * H - H) * η ^ 2 from by
          rw [mul_comm (b * b), div_mul_cancel₀ _ hMb]]
    have h1 : 8 * (M - 1) * H * η ^ 2 ≤ H * (1 - 2 / M) := by
      have h2 : 8 * (M - 1) * η ^ 2 ≤ 1 - 2 / M := hlev0
      nlinarith [mul_le_mul_of_nonneg_right h2 hHpos.le]
    have h2 : 8 * (M * H - H) * η ^ 2 = 8 * (M - 1) * H * η ^ 2 := by ring
    rw [h2]
    rw [div_le_iff₀ hMpos]
    have h3 : M * (8 * (M - 1) * H * η ^ 2) ≤ M * (H * (1 - 2 / M)) :=
      mul_le_mul_of_nonneg_left h1 hMpos.le
    have h4 : M * (H * (1 - 2 / M)) = M * H - 2 * H := by field_simp
    nlinarith [h3, h4]
  have hmain := propagation_above_shifted hA hA1 htrA hb hΦ heq hpos hc hcq hcq'
    hη hη8 hgpos hH hsup hwit hlevel
  exact hmain

end

end Submission
