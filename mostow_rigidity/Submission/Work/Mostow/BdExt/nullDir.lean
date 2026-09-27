import Mathlib
import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.BdExt.Basic

/-!
# The null direction of an escaping sequence

Let `u : ℕ → E n` be a sequence escaping to infinity in the hyperbolic chart (`‖u k‖ → ∞`)
whose Euclidean directions `dirv (u k)` converge to a boundary point `ξ`.  The *lift*

`k ↦ ‖u k‖⁻¹ • hlift (u k)`

of the sequence to the ambient space `ℝ^{Fin n ⊕ Fin 1}` then converges to the null vector
`theta ξ = (ξ, 1)`.  This is the coordinate statement that the visual compactification of `ℍⁿ`
is exactly the space of directions: the hyperboloid is asymptotic to the light cone, and
rescaling by `1/‖u‖` makes the time coordinate `‖u‖⁻¹ * √(1 + ‖u‖²)` tend to `1` while the
space coordinates tend to the direction of `u`.

The only algebraic input is the identity

`‖u‖⁻¹ * tpart u = √((‖u‖⁻¹)² + 1)`  (for `u ≠ 0`),

proved below as `inv_norm_mul_tpart`.
-/

namespace Work.Mostow.BdExt

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Filter

noncomputable section

variable {n : ℕ}

/-- The normalised time coordinate of the lift: for `u ≠ 0` the rescaled time component
`‖u‖⁻¹ * tpart u` is the square root `√(‖u‖⁻² + 1)`, whose limit as `‖u‖ → ∞` is `1`. -/
lemma inv_norm_mul_tpart (u : E n) (hu : u ≠ 0) :
    ‖u‖⁻¹ * tpart u = Real.sqrt ((‖u‖⁻¹)^2 + 1) := by
  have h : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have h2 : (‖u‖⁻¹)^2 * (1 + ‖u‖^2) = (‖u‖⁻¹)^2 + 1 := by
    have h3 : (‖u‖⁻¹)^2 * ‖u‖^2 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ h, one_pow]
    calc (‖u‖⁻¹)^2 * (1 + ‖u‖^2) = (‖u‖⁻¹)^2 * 1 + (‖u‖⁻¹)^2 * ‖u‖^2 := by ring
      _ = (‖u‖⁻¹)^2 + 1 := by rw [mul_one, h3]
  calc ‖u‖⁻¹ * tpart u
      = Real.sqrt ((‖u‖⁻¹)^2) * Real.sqrt (1 + ‖u‖^2) := by
        rw [Real.sqrt_sq (by positivity : (0:ℝ) ≤ ‖u‖⁻¹), tpart]
    _ = Real.sqrt ((‖u‖⁻¹)^2 * (1 + ‖u‖^2)) := (Real.sqrt_mul (sq_nonneg (‖u‖⁻¹)) (1 + ‖u‖^2)).symm
    _ = Real.sqrt ((‖u‖⁻¹)^2 + 1) := by rw [h2]

theorem nullDir (n : ℕ) (u : ℕ → Submission.Mostow.E n) (ξ : Submission.Mostow.E n)
    (hu : Filter.Tendsto (fun k => ‖u k‖) Filter.atTop Filter.atTop)
    (hd : Filter.Tendsto (fun k => Work.Mostow.BdExt.dirv (u k)) Filter.atTop (nhds ξ)) :
    Filter.Tendsto (fun k => (‖u k‖)⁻¹ • Submission.Mostow.hlift (u k)) Filter.atTop
      (nhds (Work.Mostow.theta ξ)) := by
  rw [tendsto_pi_nhds]
  intro z
  rcases z with i | j
  · -- spatial coordinates: these are exactly the coordinates of `dirv (u k)`
    have hcont : ContinuousAt (fun w : Submission.Mostow.E n => w i) ξ :=
      (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).continuousAt
    have h := hcont.tendsto.comp hd
    have hcomp : (fun k => (Work.Mostow.BdExt.dirv (u k)) i) =ᶠ[atTop]
        (fun k => ‖u k‖⁻¹ * (u k).ofLp i) :=
      EventuallyEq.of_eq (by funext k; simp [Work.Mostow.BdExt.dirv])
    have hgoal : Tendsto (fun k => ‖u k‖⁻¹ * (u k).ofLp i) atTop (nhds (ξ.ofLp i)) :=
      Filter.Tendsto.congr' hcomp h
    simpa only [Submission.Mostow.hlift, Work.Mostow.theta, Sum.elim_inl, Pi.smul_apply,
      smul_eq_mul] using hgoal
  · -- time coordinate: `‖u k‖⁻¹ * tpart (u k) → 1`
    fin_cases j
    have hlim : Tendsto (fun k => Real.sqrt ((‖u k‖⁻¹)^2 + 1)) atTop (nhds 1) := by
      have hcont : ContinuousAt (fun t : ℝ => Real.sqrt (t^2 + 1)) 0 := by fun_prop
      have h1 : Tendsto (fun k => Real.sqrt ((‖u k‖⁻¹)^2 + 1)) atTop
          (nhds (Real.sqrt ((0:ℝ)^2 + 1))) := hcont.tendsto.comp (tendsto_inv_atTop_zero.comp hu)
      simpa using h1
    have hev : (fun k => ‖u k‖⁻¹ * Submission.Mostow.tpart (u k)) =ᶠ[atTop]
        fun k => Real.sqrt ((‖u k‖⁻¹)^2 + 1) := by
      filter_upwards [hu.eventually_ge_atTop 1] with k hk
      exact inv_norm_mul_tpart (u k) (by
        intro h0; rw [h0, norm_zero] at hk; linarith)
    have hfin : Tendsto (fun k => ‖u k‖⁻¹ * Submission.Mostow.tpart (u k)) atTop (nhds 1) :=
      Filter.Tendsto.congr' hev.symm hlim
    simpa only [Submission.Mostow.hlift, Work.Mostow.theta, Sum.elim_inr, Pi.smul_apply,
      smul_eq_mul] using hfin

end

end Work.Mostow.BdExt
