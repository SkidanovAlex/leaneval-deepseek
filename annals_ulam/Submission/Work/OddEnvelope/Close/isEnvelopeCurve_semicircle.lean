import Mathlib
import Submission.Work.OddEnvelope.Defs

/-!
# The semicircle is an envelope curve

This file proves `Work.OddEnvelope.IsEnvelopeCurve (fun _ => 0) profileX profileX`: the
unperturbed chord-endpoint curve `x = y = profileX` of the unit semicircle, with zero
perturbation `h = 0`, satisfies the full hypothesis package of the odd-dimensional Ulam
construction.  In particular the profile recovered from it is the semicircle itself.

Everything is derived from the two closed forms for the derivatives of

  `profileX s = 1 / √(1 + s²)`,

namely `profileX' s = -s * profileX s ^ 3` and `profileX'' s = (2 s² - 1) * profileX s ^ 5`,
together with the algebraic identity `profileX s ^ 2 * (1 + s ^ 2) = 1`, which turns the
second-order shape conditions into the polynomial identity

  `2 (profileX' s)² - profileX s * profileX'' s = profileX s ^ 6 > 0`.
-/

namespace Work.OddEnvelope.Close

open Set Filter
open scoped ContDiff Topology

private lemma profileX_eq_inv (s : ℝ) :
    Work.OddEnvelope.profileX s = (Real.sqrt (1 + s ^ 2))⁻¹ := by
  simp [Work.OddEnvelope.profileX, one_div]

private lemma profileX_pos (s : ℝ) : 0 < Work.OddEnvelope.profileX s := by
  rw [profileX_eq_inv]
  exact inv_pos.2 (Real.sqrt_pos_of_pos (by positivity))

/-- `profileX s ^ 2 * (1 + s ^ 2) = 1`, the identity relating `profileX` to the rational
function `1/(1+s²)`. -/
private lemma profileX_sq (s : ℝ) : Work.OddEnvelope.profileX s ^ 2 * (1 + s ^ 2) = 1 := by
  have hq2 : (Real.sqrt (1 + s ^ 2)) ^ 2 = 1 + s ^ 2 := Real.sq_sqrt (by positivity)
  rw [profileX_eq_inv, inv_pow, hq2]
  exact inv_mul_cancel₀ (by positivity)

private lemma smooth_profileX :
    ContDiffOn ℝ ∞ Work.OddEnvelope.profileX (Set.Ioi 0) := by
  unfold Work.OddEnvelope.profileX
  apply ContDiffOn.div
  · exact contDiffOn_const
  · apply ContDiffOn.sqrt
    · fun_prop
    · intro x hx
      positivity
  · intro x hx
    exact ne_of_gt (Real.sqrt_pos_of_pos (by positivity))

/-- `deriv profileX s = -s * profileX s ^ 3`. -/
private lemma hasDerivAt_profileX (s : ℝ) :
    HasDerivAt Work.OddEnvelope.profileX (-s * Work.OddEnvelope.profileX s ^ 3) s := by
  have hq : 0 < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos_of_pos (by positivity)
  have hprof : Work.OddEnvelope.profileX = fun t : ℝ => (Real.sqrt (1 + t ^ 2))⁻¹ :=
    funext fun t => profileX_eq_inv t
  have hpx : Work.OddEnvelope.profileX s = (Real.sqrt (1 + s ^ 2))⁻¹ := profileX_eq_inv s
  have hinner : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * s) s := by
    have h2 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * s) s :=
      (hasDerivAt_pow 2 s).congr_deriv (by norm_num)
    exact h2.const_add 1
  have hsqrt : HasDerivAt (fun t : ℝ => Real.sqrt (1 + t ^ 2))
      ((2 * s) / (2 * Real.sqrt (1 + s ^ 2))) s :=
    hinner.sqrt (by positivity : (1 + s ^ 2) ≠ 0)
  have hinv := hsqrt.inv hq.ne'
  have hmain : HasDerivAt Work.OddEnvelope.profileX
      (-((2 * s) / (2 * Real.sqrt (1 + s ^ 2))) / (Real.sqrt (1 + s ^ 2)) ^ 2) s := by
    rw [hprof]
    exact hinv
  refine hmain.congr_deriv ?_
  rw [hpx]
  field_simp

private lemma deriv_profileX (s : ℝ) :
    deriv Work.OddEnvelope.profileX s = -s * Work.OddEnvelope.profileX s ^ 3 :=
  (hasDerivAt_profileX s).deriv

/-- `deriv (deriv profileX) s = (2 s² - 1) * profileX s ^ 5`. -/
private lemma deriv_deriv_profileX (s : ℝ) :
    deriv (deriv Work.OddEnvelope.profileX) s =
      (2 * s ^ 2 - 1) * Work.OddEnvelope.profileX s ^ 5 := by
  have hfun : deriv Work.OddEnvelope.profileX =
      fun t : ℝ => -t * Work.OddEnvelope.profileX t ^ 3 :=
    funext fun t => deriv_profileX t
  have hp : HasDerivAt (fun t : ℝ => -t) (-1) s :=
    (hasDerivAt_id s).neg
  have hpow : HasDerivAt (fun t : ℝ => Work.OddEnvelope.profileX t ^ 3)
      (3 * Work.OddEnvelope.profileX s ^ 2 * (-s * Work.OddEnvelope.profileX s ^ 3)) s :=
    (hasDerivAt_profileX s).pow 3
  have hmul : HasDerivAt (fun t : ℝ => -t * Work.OddEnvelope.profileX t ^ 3)
      ((-1) * Work.OddEnvelope.profileX s ^ 3 +
        (-s) * (3 * Work.OddEnvelope.profileX s ^ 2 *
          (-s * Work.OddEnvelope.profileX s ^ 3))) s :=
    hp.mul hpow
  have hval : ((-1) * Work.OddEnvelope.profileX s ^ 3 +
        (-s) * (3 * Work.OddEnvelope.profileX s ^ 2 *
          (-s * Work.OddEnvelope.profileX s ^ 3))) =
      (2 * s ^ 2 - 1) * Work.OddEnvelope.profileX s ^ 5 := by
    linear_combination (Work.OddEnvelope.profileX s ^ 3) * (profileX_sq s)
  calc deriv (deriv Work.OddEnvelope.profileX) s
      = deriv (fun t : ℝ => -t * Work.OddEnvelope.profileX t ^ 3) s := by rw [hfun]
    _ = _ := hmul.deriv
    _ = _ := hval

private lemma continuous_profileX : Continuous Work.OddEnvelope.profileX := by
  rw [show Work.OddEnvelope.profileX = fun t : ℝ => (Real.sqrt (1 + t ^ 2))⁻¹ from
    funext fun t => profileX_eq_inv t]
  apply Continuous.inv₀
  · exact (continuous_const.add (continuous_id.pow 2)).sqrt
  · intro x
    exact ne_of_gt (Real.sqrt_pos_of_pos (by positivity : (0 : ℝ) < 1 + x ^ 2))

private lemma deriv_zero : deriv (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 :=
  funext fun t => deriv_const t (0 : ℝ)

private lemma tendsto_profileX :
    Tendsto Work.OddEnvelope.profileX (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
  have h1 : Work.OddEnvelope.profileX 0 = 1 := by simp [Work.OddEnvelope.profileX]
  have h' : Tendsto Work.OddEnvelope.profileX (nhds 0)
      (nhds (Work.OddEnvelope.profileX 0)) :=
    continuous_profileX.continuousAt (x := 0)
  rw [h1] at h'
  exact h'.mono_left nhdsWithin_le_nhds

/-- **The unit semicircle is an envelope curve.**  With `h = 0` and `x = y = profileX`, every
field of `Work.OddEnvelope.IsEnvelopeCurve` holds: the curve is smooth, strictly decreasing,
tends to `1` at `0⁺`, equals `profileX` beyond the (empty) perturbation window, both chord
functions `s ↦ s * profileX s ± 0` are strictly increasing (their derivative is
`profileX s ^ 3 > 0`), and the second-order shape conditions reduce to
`profileX s ^ 6 > 0`. -/
theorem isEnvelopeCurve_semicircle :
    Work.OddEnvelope.IsEnvelopeCurve (fun _ : ℝ => 0) Work.OddEnvelope.profileX
      Work.OddEnvelope.profileX := by
  refine ⟨contDiffOn_const, smooth_profileX, smooth_profileX, rfl, ?_, ?_, ?_,
    tendsto_profileX, tendsto_profileX, (fun _ _ => rfl), (fun _ _ => rfl), ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [Function.mem_support] at hx
    exact absurd rfl hx
  · intro s hs
    rw [deriv_profileX s]
    nlinarith [mul_pos hs (pow_pos (profileX_pos s) 3)]
  · intro s hs
    rw [deriv_profileX s]
    nlinarith [mul_pos hs (pow_pos (profileX_pos s) 3)]
  · intro s _
    rw [deriv_profileX s, deriv_const]
    have hid : Work.OddEnvelope.profileX s + s * (-s * Work.OddEnvelope.profileX s ^ 3) + 0
        = Work.OddEnvelope.profileX s ^ 3 := by
      linear_combination (-(Work.OddEnvelope.profileX s)) * (profileX_sq s)
    rw [hid]
    exact pow_pos (profileX_pos s) 3
  · intro s _
    rw [deriv_profileX s, deriv_const]
    have hid : Work.OddEnvelope.profileX s + s * (-s * Work.OddEnvelope.profileX s ^ 3) - 0
        = Work.OddEnvelope.profileX s ^ 3 := by
      linear_combination (-(Work.OddEnvelope.profileX s)) * (profileX_sq s)
    rw [hid]
    exact pow_pos (profileX_pos s) 3
  · intro s _
    have hz2 : deriv (deriv (fun _ : ℝ => (0 : ℝ))) s = 0 := by
      rw [deriv_zero]
      exact deriv_const s (0 : ℝ)
    rw [deriv_profileX s, deriv_deriv_profileX s, deriv_const, hz2]
    have hid : 2 * (-s * Work.OddEnvelope.profileX s ^ 3) ^ 2 -
        Work.OddEnvelope.profileX s * ((2 * s ^ 2 - 1) * Work.OddEnvelope.profileX s ^ 5) +
        0 * (-s * Work.OddEnvelope.profileX s ^ 3) -
        0 * ((2 * s ^ 2 - 1) * Work.OddEnvelope.profileX s ^ 5) =
        Work.OddEnvelope.profileX s ^ 6 := by
      ring
    rw [hid]
    exact pow_pos (profileX_pos s) 6
  · intro s _
    have hz2 : deriv (deriv (fun _ : ℝ => (0 : ℝ))) s = 0 := by
      rw [deriv_zero]
      exact deriv_const s (0 : ℝ)
    rw [deriv_profileX s, deriv_deriv_profileX s, deriv_const, hz2]
    have hid : 2 * (-s * Work.OddEnvelope.profileX s ^ 3) ^ 2 -
        Work.OddEnvelope.profileX s * ((2 * s ^ 2 - 1) * Work.OddEnvelope.profileX s ^ 5) -
        0 * (-s * Work.OddEnvelope.profileX s ^ 3) +
        0 * ((2 * s ^ 2 - 1) * Work.OddEnvelope.profileX s ^ 5) =
        Work.OddEnvelope.profileX s ^ 6 := by
      ring
    rw [hid]
    exact pow_pos (profileX_pos s) 6

end Work.OddEnvelope.Close
