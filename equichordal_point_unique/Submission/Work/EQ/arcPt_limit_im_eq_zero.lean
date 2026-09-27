import Mathlib
import Submission.Work.EQ.Defs
import Submission.Work.EQ.hetero_box
import Submission.Work.EQ.arc_iterate_aux

namespace Work.EQ

open Complex Filter
open scoped Topology

/-- Any limit of an `eqU`-orbit on the arc is a real point: if `θ m → L` and
`eqU a (arcPt a ρ₁ (θ m)) = arcPt a ρ₁ (θ (m+1))` for all `m`, then `(arcPt a ρ₁ L).im = 0`.
By `arcPt_continuousAt` (with `hC`), `arcPt a ρ₁ (θ m) - O₂` and `arcPt a ρ₁ (θ (m+1))` have
limits; the step identity rewritten as the division-free
`arcPt a ρ₁ (θ m) - O₂ = ‖arcPt a ρ₁ (θ m) - O₂‖ * (arcPt a ρ₁ (θ m) + arcPt a ρ₁ (θ (m+1)))`
(using `div_norm_mul_norm` of `arc_iterate_aux` and the unfolding of `eqU`) passes to the limit
as `arcPt a ρ₁ L - O₂ = s * (2 * arcPt a ρ₁ L)` with `s = ‖arcPt a ρ₁ L - O₂‖`, i.e.
`(1 - 2s) * arcPt a ρ₁ L = O₂`; `1 - 2s ≠ 0` since `O₂ = a/2 ≠ 0`, so taking imaginary parts of
the real multiple gives `(arcPt a ρ₁ L).im = 0`. -/
theorem arcPt_limit_im_eq_zero {a : ℝ} (ha0 : 0 < a) {ρ₁ ρ₂ : ℝ → ℝ}
    (hC : NormEqCurve a ρ₁ ρ₂) {θ : ℕ → ℝ} {L : ℝ}
    (hlim : Filter.Tendsto θ Filter.atTop (nhds L))
    (hstep : ∀ m, eqU a (arcPt a ρ₁ (θ m)) = arcPt a ρ₁ (θ (m + 1))) :
    (arcPt a ρ₁ L).im = 0 := by
  -- `O₂ = a/2`, seen as a complex number.
  set b : ℂ := ((a / 2 : ℝ) : ℂ) with hb
  have hbim : b.im = 0 := by rw [hb]; simp
  have hbne : b ≠ 0 := by
    intro h
    rw [hb] at h
    have := Complex.ofReal_eq_zero.mp h
    linarith
  -- Continuity of the parametrisation turns convergence of `θ` into convergence of the points.
  have hcont : ContinuousAt (fun t : ℝ => arcPt a ρ₁ t) L := arcPt_continuousAt hC L
  have hPlim : Tendsto (fun m => arcPt a ρ₁ (θ m)) atTop (nhds (arcPt a ρ₁ L)) :=
    hcont.tendsto.comp hlim
  have hQlim : Tendsto (fun m => arcPt a ρ₁ (θ (m + 1))) atTop (nhds (arcPt a ρ₁ L)) :=
    hcont.tendsto.comp ((Filter.tendsto_add_atTop_iff_nat (f := θ) 1).mpr hlim)
  -- The step identity, cleared of the denominator, holds at every index.
  have hEq : ∀ m, arcPt a ρ₁ (θ m) - b =
      ((‖arcPt a ρ₁ (θ m) - b‖ : ℝ) : ℂ) * (arcPt a ρ₁ (θ m) + arcPt a ρ₁ (θ (m + 1))) := by
    intro m
    have hs : eqU a (arcPt a ρ₁ (θ m)) = arcPt a ρ₁ (θ (m + 1)) := hstep m
    have h1 : (arcPt a ρ₁ (θ m) - b) / ((‖arcPt a ρ₁ (θ m) - b‖ : ℝ) : ℂ)
        = arcPt a ρ₁ (θ m) + arcPt a ρ₁ (θ (m + 1)) := by
      have h := hs
      simp only [eqU, hb] at h ⊢
      linear_combination h
    rw [← h1]
    rw [mul_comm, div_norm_mul_norm]
  -- Pass the identity to the limit.
  have hLHS : Tendsto (fun m => arcPt a ρ₁ (θ m) - b) atTop (nhds (arcPt a ρ₁ L - b)) :=
    hPlim.sub tendsto_const_nhds
  have hnormc : Tendsto (fun m => ((‖arcPt a ρ₁ (θ m) - b‖ : ℝ) : ℂ)) atTop
      (nhds ((‖arcPt a ρ₁ L - b‖ : ℝ) : ℂ)) :=
    hLHS.norm.ofReal
  have hsum : Tendsto (fun m => arcPt a ρ₁ (θ m) + arcPt a ρ₁ (θ (m + 1))) atTop
      (nhds (arcPt a ρ₁ L + arcPt a ρ₁ L)) := hPlim.add hQlim
  have hRHS : Tendsto (fun m => ((‖arcPt a ρ₁ (θ m) - b‖ : ℝ) : ℂ) *
      (arcPt a ρ₁ (θ m) + arcPt a ρ₁ (θ (m + 1)))) atTop
      (nhds (((‖arcPt a ρ₁ L - b‖ : ℝ) : ℂ) * (arcPt a ρ₁ L + arcPt a ρ₁ L))) :=
    hnormc.mul hsum
  have hRHS' : Tendsto (fun m => arcPt a ρ₁ (θ m) - b) atTop
      (nhds (((‖arcPt a ρ₁ L - b‖ : ℝ) : ℂ) * (arcPt a ρ₁ L + arcPt a ρ₁ L))) :=
    hRHS.congr (fun m => (hEq m).symm)
  have hkey : arcPt a ρ₁ L - b =
      ((‖arcPt a ρ₁ L - b‖ : ℝ) : ℂ) * (arcPt a ρ₁ L + arcPt a ρ₁ L) :=
    tendsto_nhds_unique hLHS hRHS'
  -- `(1 - 2‖arcPt a ρ₁ L - b‖) · arcPt a ρ₁ L = b`.
  have hkey2 : ((1 - 2 * ‖arcPt a ρ₁ L - b‖ : ℝ) : ℂ) * arcPt a ρ₁ L = b := by
    have hcast : ((1 - 2 * ‖arcPt a ρ₁ L - b‖ : ℝ) : ℂ)
        = 1 - 2 * ((‖arcPt a ρ₁ L - b‖ : ℝ) : ℂ) := by push_cast; ring
    rw [hcast]
    linear_combination hkey
  -- Imaginary parts: `(1 - 2s) · (arcPt a ρ₁ L).im = 0`.
  have him : (1 - 2 * ‖arcPt a ρ₁ L - b‖) * (arcPt a ρ₁ L).im = 0 := by
    have h := congrArg Complex.im hkey2
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, hbim] at h
    exact h
  have hne : (1 - 2 * ‖arcPt a ρ₁ L - b‖) ≠ 0 := by
    intro hz
    have hb0 : b = 0 := by rw [← hkey2, hz]; simp
    exact hbne hb0
  rcases mul_eq_zero.mp him with h | h
  · exact absurd h hne
  · exact h

end Work.EQ
