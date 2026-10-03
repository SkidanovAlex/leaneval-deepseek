import Mathlib

namespace Work.L62

open Function Filter
open scoped Topology

/-- If `H` preserves `U`, `L ∘ H = L + a` on `U` and `‖deriv L - 1‖ ≤ 1/2` on `U`, then every
iterate of `H` is differentiable on `U`, its derivative telescopes to
`deriv (H^[t]) z = deriv L z / deriv L (H^[t] z)`, and every iterate of `H` is `3`-Lipschitz on the
convex set `U`. -/
theorem deriv_iterate_eq {H L : ℂ → ℂ} {U : Set ℂ} {a : ℂ}
    (hUo : IsOpen U) (hUc : Convex ℝ U) (hHd : DifferentiableOn ℂ H U) (hLd : DifferentiableOn ℂ L U)
    (hHmem : ∀ w ∈ U, H w ∈ U) (hLH : ∀ w ∈ U, L (H w) = L w + a)
    (hb : ∀ w ∈ U, ‖deriv L w - 1‖ ≤ 1 / 2) :
    (∀ t : ℕ, ∀ z ∈ U, DifferentiableAt ℂ (H^[t]) z ∧
      deriv (H^[t]) z = deriv L z / deriv L (H^[t] z)) ∧
    (∀ t : ℕ, ∀ x ∈ U, ∀ y ∈ U, ‖(H^[t]) y - (H^[t]) x‖ ≤ 3 * ‖y - x‖) := by
  -- every iterate of `H` maps `U` into `U`
  have hmem : ∀ t : ℕ, ∀ w ∈ U, (H^[t]) w ∈ U := by
    intro t
    induction t with
    | zero => intro w hw; simpa using hw
    | succ t ih =>
      intro w hw
      rw [Function.iterate_succ_apply]
      exact ih (H w) (hHmem w hw)
  -- the pushed-forward identity `L (H^[t] w) = L w + t * a`
  have hLt : ∀ t : ℕ, ∀ w ∈ U, L ((H^[t]) w) = L w + (t : ℂ) * a := by
    intro t
    induction t with
    | zero => intro w hw; simp
    | succ t ih =>
      intro w hw
      rw [Function.iterate_succ_apply, ih (H w) (hHmem w hw), hLH w hw]
      push_cast
      ring
  -- iterates are holomorphic on `U`
  have hdiffOn : ∀ t : ℕ, DifferentiableOn ℂ (H^[t]) U := by
    intro t
    induction t with
    | zero => simpa using differentiableOn_id
    | succ t ih =>
      simpa [Function.iterate_succ] using ih.comp hHd (fun w hw => hHmem w hw)
  have hdiffAt : ∀ t : ℕ, ∀ z ∈ U, DifferentiableAt ℂ (H^[t]) z :=
    fun t z hz => (hdiffOn t).differentiableAt (hUo.mem_nhds hz)
  -- lower and upper bounds for `‖deriv L‖` on `U` coming from `‖deriv L - 1‖ ≤ 1/2`
  have hlow : ∀ w ∈ U, (1 : ℝ) / 2 ≤ ‖deriv L w‖ := by
    intro w hw
    have h := norm_sub_norm_le (1 : ℂ) (1 - deriv L w)
    have h1 : (1 : ℂ) - (1 - deriv L w) = deriv L w := by ring
    rw [norm_one, norm_sub_rev 1 (deriv L w), h1] at h
    linarith [hb w hw]
  have hup : ∀ w ∈ U, ‖deriv L w‖ ≤ 3 / 2 := by
    intro w hw
    have h := norm_sub_norm_le (deriv L w) (deriv L w - 1)
    have h1 : deriv L w - (deriv L w - 1) = (1 : ℂ) := by ring
    rw [h1, norm_one] at h
    linarith [hb w hw]
  have hnz : ∀ w ∈ U, deriv L w ≠ 0 := by
    intro w hw
    exact norm_pos_iff.mp (by linarith [hlow w hw])
  -- the telescoping formula for the derivative of the `t`-th iterate
  have hderiv : ∀ t : ℕ, ∀ z ∈ U, deriv (H^[t]) z = deriv L z / deriv L ((H^[t]) z) := by
    intro t z hz
    have hzmem : (H^[t]) z ∈ U := hmem t z hz
    have hcomp : deriv (fun w => L ((H^[t]) w)) z
        = deriv L ((H^[t]) z) * deriv (H^[t]) z := by
      simpa [Function.comp_def] using
        deriv_comp z (hLd.differentiableAt (hUo.mem_nhds hzmem)) (hdiffAt t z hz)
    have hcongr : (fun w => L ((H^[t]) w)) =ᶠ[𝓝 z] (fun w => L w + (t : ℂ) * a) :=
      Filter.eventuallyEq_of_mem (hUo.mem_nhds hz) (fun w hw => hLt t w hw)
    have hkey : deriv L ((H^[t]) z) * deriv (H^[t]) z = deriv L z := by
      rw [← hcomp, hcongr.deriv_eq, deriv_add_const]
    rw [eq_div_iff (hnz _ hzmem), mul_comm]
    exact hkey
  -- the uniform bound `‖(H^[t])'‖ ≤ 3` on `U`
  have hbound : ∀ t : ℕ, ∀ w ∈ U, ‖deriv (H^[t]) w‖ ≤ 3 := by
    intro t w hw
    rw [hderiv t w hw, norm_div, div_le_iff₀ (by linarith [hlow _ (hmem t w hw)])]
    linarith [hup w hw, hlow _ (hmem t w hw)]
  constructor
  · intro t z hz
    exact ⟨hdiffAt t z hz, hderiv t z hz⟩
  · intro t x hx y hy
    exact Convex.norm_image_sub_le_of_norm_deriv_le (f := H^[t]) (s := U) (C := 3)
      (fun z hz => hdiffAt t z hz) (fun z hz => hbound t z hz) hUc hx hy

end Work.L62
