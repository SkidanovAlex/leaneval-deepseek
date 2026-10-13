import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.LinearAlgebra.Trace
import Submission.Work.ConstructionInstance.Defs
import Submission.Work.ConstructionInstance.div_cutDatum

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

noncomputable section

open Filter

/-! ## Smoothness of the profile off the plane `θ = 0`

This is the hypothesis `div_cutDatum` needs, and it is what makes the "off the two singular
sets" case go through: the profile `F = F_* + g` is `C¹` at every point `(z,θ)` with `θ ≠ 0`,
because the angular factor `Γ(θ) = (sinθcos²θ)^{p/3}` has a nonzero base there, while `g` is
smooth on the box `Ioi(-1) ×ˢ Ioo(-1)(π/2+1)` (`SmoothFar`).  On the two branches `θ > 0`,
`θ < 0` of the odd extension the profile is literally `F_* + g` resp. its reflection. -/

theorem contDiffAt_uncurry_profile {p : ℝ} {g : ℝ → ℝ → ℝ}
    (hsmooth : Work.Stability.SmoothFar g) {z θ : ℝ} (hz : -1 < z)
    (hθ : θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) (hθ0 : θ ≠ 0) :
    ContDiffAt ℝ 1 (Function.uncurry (Work.ConstructionInstance.profile p g)) (z, θ) := by
  have hle : (1 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder := by
    simp [Work.Stability.smoothOrder]
  -- `g` is `C¹` at `(z,θ')` for `θ'` in the open quadrant
  have hgbox : ∀ θ' ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ContDiffAt ℝ 1 (fun q : ℝ × ℝ => g q.1 q.2) (z, θ') := by
    intro θ' hθ'
    have hbox : (z, θ') ∈ Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1) :=
      ⟨hz, ⟨by linarith [hθ'.1], by linarith [hθ'.2]⟩⟩
    have h : ContDiffAt ℝ 1 (Function.uncurry g) (z, θ') :=
      ContDiffAt.of_le (hsmooth.contDiffAt ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds hbox)) hle
    simpa [Function.uncurry_def] using h
  -- the smooth branch `(z,θ) ↦ F_*(z,θ) + g(z,θ)`
  have hP : ∀ θ' ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ContDiffAt ℝ 1 (fun q : ℝ × ℝ => Work.Construction.Fstar p q.1 q.2 + g q.1 q.2) (z, θ') := by
    intro θ' hθ'
    have hGam : ContDiffAt ℝ 1
        (fun q : ℝ × ℝ => (Real.sin q.2 * Real.cos q.2 ^ 2) ^ (p / 3)) (z, θ') := by
      apply ContDiffAt.rpow
      · fun_prop
      · fun_prop
      · have h1 : 0 < Real.sin θ' :=
          Real.sin_pos_of_pos_of_lt_pi hθ'.1 (by linarith [hθ'.2, Real.pi_pos])
        have h2 : 0 < Real.cos θ' :=
          Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ'.1, Real.pi_pos], hθ'.2⟩
        positivity
    have hGam2 : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => Work.Spaces.Gam p q.2) (z, θ') := by
      simpa [Work.Spaces.Gam] using hGam
    have hFrad : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => Work.FM.Fstar q.1) (z, θ') := by
      apply ContDiffAt.div
      · fun_prop
      · fun_prop
      · have : (1 : ℝ) + z ≠ 0 := by linarith
        positivity
    have hFstar : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => Work.Construction.Fstar p q.1 q.2) (z, θ') := by
      have h := (ContDiffAt.const_smul (𝕜 := ℝ) p
        (ContDiffAt.div_const hGam2 (Work.Spaces.c p))).mul hFrad
      simpa [Work.Construction.Fstar, mul_assoc] using h
    exact hFstar.add (hgbox θ' hθ')
  rcases lt_trichotomy (0 : ℝ) θ with hpos | heq | hneg
  · have hev : Function.uncurry (Work.ConstructionInstance.profile p g)
        =ᶠ[nhds (z, θ)] (fun q : ℝ × ℝ => Work.Construction.Fstar p q.1 q.2 + g q.1 q.2) := by
      filter_upwards [IsOpen.mem_nhds (isOpen_lt continuous_const continuous_snd) hpos]
        with q hq
      show Work.ConstructionInstance.profile p g q.1 q.2 = _
      rw [Work.ConstructionInstance.profile_of_nonneg (le_of_lt hq)]
    exact (hP θ ⟨hpos, hθ.2⟩).congr_of_eventuallyEq hev
  · exact absurd heq.symm hθ0
  · have hmem' : -θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨by linarith, by linarith [hθ.1]⟩
    have hev : Function.uncurry (Work.ConstructionInstance.profile p g)
        =ᶠ[nhds (z, θ)]
          (fun q : ℝ × ℝ => -(Work.Construction.Fstar p q.1 (-q.2) + g q.1 (-q.2))) := by
      filter_upwards [IsOpen.mem_nhds (isOpen_lt continuous_snd continuous_const) hneg]
        with q hq
      show Work.ConstructionInstance.profile p g q.1 q.2 = _
      rw [Work.ConstructionInstance.profile_of_neg (not_le.mpr hq)]
    have hnegP : ContDiffAt ℝ 1
        (fun q : ℝ × ℝ => -(Work.Construction.Fstar p q.1 (-q.2) + g q.1 (-q.2))) (z, θ) := by
      have hcomp : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => (q.1, -q.2)) (z, θ) := by fun_prop
      have h3 := (hP (-θ) hmem').comp (z, θ) hcomp
      simpa [Function.comp_def] using h3.neg
    exact hnegP.congr_of_eventuallyEq hev

/-! ## Vanishing of the diagonal along coordinate lines on the axis and the plane -/

/-- On the symmetry axis (`radial x = 0`) and on the plane `x₃ = 0` (`axial x = 0`), the `i`-th
coordinate of the cut-off datum vanishes identically along the `i`-th coordinate line through
`x`.  On the axis this is because `e_θ` has vanishing `i`-th coordinate there; on the plane it is
because `e_θ` has vanishing `x₃`-coordinate, and along the two directions *inside* the plane the
angle `θ` is identically `0`, where the profile vanishes (`profile_zero`, using
`VanishTheta g`). -/
theorem omega0_coord_line_eq_zero {p : ℝ} (hp : p ≠ 0) {g : ℝ → ℝ → ℝ}
    (hvt : Work.Spaces.VanishTheta g) (L : ℝ) {x : R3}
    (hx : Work.Cyl.radial x = 0 ∨ Work.Cyl.axial x = 0) (i : Fin 3) (t : ℝ) :
    (Work.ConstructionInstance.omega₀ p g L (x + t • Work.Cyl.basisVec i)) i = 0 := by
  rw [omega₀_apply, omegaS_apply']
  simp only [PiLp.smul_apply, smul_eq_mul]
  rcases hx with hr | ha
  · have hx0 : x 0 = 0 := ((Work.Cyl.radial_eq_zero_iff x).mp hr).1
    have hx1 : x 1 = 0 := ((Work.Cyl.radial_eq_zero_iff x).mp hr).2
    have he : (Work.Cyl.eTheta (x + t • Work.Cyl.basisVec i)) i = 0 := by
      fin_cases i <;>
        simp [Work.Cyl.eTheta, Work.Cyl.angularVec, Work.Cyl.basisVec,
          FiniteTimeSingularity.e, hx0, hx1]
    rw [he, mul_zero, mul_zero]
  · have hx2 : x 2 = 0 := ha
    fin_cases i <;>
      simp [Work.Cyl.theta, Work.Cyl.axial, Work.Cyl.rho, Work.Cyl.eTheta,
        Work.Cyl.angularVec, Work.Cyl.basisVec, FiniteTimeSingularity.e,
        profile_zero hp hvt.1, hx2]

/-! ## The main theorem -/

/-- The cut-off datum `omega₀ p g L = χ(ρ/L)·omegaS p g` is divergence free for **every**
`x : ℝ³`.  Off the axis and off the plane this is `div_cutDatum`; on the two singular sets the
field is not differentiable (the Fréchet quotient along `e₂` resp. `e₀` blows up like
`h^{p/3-1}` resp. `h^{2p/3-1}`, both divergent for `p ≤ 1`), whence `fderiv = 0` by Mathlib's
`fderiv_zero_of_not_differentiableAt`; where `χ(ρ(x)/L) = 0` the datum vanishes on a
neighbourhood of `x` (the cut-off is `0` for `|ρ/L| ≥ 2`), so again `fderiv = 0`.  The
non-differentiability transfers from `omegaS` to the datum because the cut-off factor is smooth
and non-zero where it does not vanish. -/
theorem div_omega0_all {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ}
    (hvt : Work.Spaces.VanishTheta g) (hsmooth : Work.Stability.SmoothFar g) (L : ℝ) :
    ∀ x : Work.ConstructionInstance.R3,
      FiniteTimeSingularity.div (Work.ConstructionInstance.omega₀ p g L) x = 0 := by
  intro x
  by_cases hA : 0 < Work.Cyl.radial x ∧ Work.Cyl.axial x ≠ 0
  · -- off the axis and off the plane: the field is differentiable with the swirl structure
    have hr : 0 < Work.Cyl.radial x := hA.1
    have hθ0 : Work.Cyl.theta x ≠ 0 := by
      intro h
      have hquot : Work.Cyl.axial x / Work.Cyl.radial x = 0 := by
        rw [← Real.arctan_eq_zero_iff]; exact h
      rcases (div_eq_zero_iff.mp hquot) with h' | h'
      · exact hA.2 h'
      · exact absurd h' (ne_of_gt hr)
    have hθmem : Work.Cyl.theta x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩
    have hz : -1 < Work.Cyl.rho x ^ p :=
      lt_of_lt_of_le (by norm_num) (Real.rpow_nonneg (Work.Cyl.rho_nonneg x) p)
    exact div_cutDatum (contDiffAt_uncurry_profile hsmooth hz hθmem hθ0) hr
  · -- on the axis or on the plane
    have hcase : Work.Cyl.radial x = 0 ∨ Work.Cyl.axial x = 0 := by
      rcases not_and_or.mp hA with h | h
      · exact Or.inl (le_antisymm (not_lt.mp h) (Work.Cyl.radial_nonneg x))
      · exact Or.inr (not_not.mp h)
    by_cases hd : DifferentiableAt ℝ (Work.ConstructionInstance.omega₀ p g L) x
    · -- the diagonal of the Jacobian is computed along coordinate lines and vanishes
      rw [FiniteTimeSingularity.div, Work.Cyl.trace_fderiv_eq_sum]
      apply Finset.sum_eq_zero
      intro i _
      rw [Work.Cyl.fderiv_apply_coord (Work.ConstructionInstance.omega₀ p g L) x i i hd,
        Work.Cyl.pd_eq_deriv_line]
      rw [show (fun t : ℝ =>
            (Work.ConstructionInstance.omega₀ p g L (x + t • Work.Cyl.basisVec i)) i)
          = fun _ => 0
        from funext (omega0_coord_line_eq_zero hp.ne' hvt L hcase i)]
      simp
    · rw [FiniteTimeSingularity.div, fderiv_zero_of_not_differentiableAt hd]
      simp

end

end Work.ConstructionInstance
