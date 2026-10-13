import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.LinearAlgebra.Trace
import Submission.Work.ConstructionInstance.Defs
import Submission.Work.ConstructionInstance.div_omegaS
import Submission.Work.ConstructionInstance.div_omega0_all
import Submission.Work.ConstructionInstance.selfSim_scalar_differentiableAt
import Submission.Work.ConstructionInstance.selfSim_profile_eTheta_coord_eq_zero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

set_option linter.unusedVariables false

open FiniteTimeSingularity Work.Cyl

/-!
# `div (c⁻¹ • omegaSz p g (ρ^p/c)) = 0`

The time-dependent self-similar ansatz of the stability layer reads
`ω(x,t) = λ̄(t)⁻¹ • omegaSz p g (ρ(x)^p / λ̄(t)) x` (`Boxes.lean`): for *every* fixed value of the
scaling constant `c = λ̄(t)` this field must be divergence free, so that the Biot–Savart velocity
`u = BS ω` of the ansatz has the correct vorticity.

The field is a swirl field `A • e_θ` with scalar factor
`A(y) = c⁻¹ * profile p g (ρ(y)^p/c) (θ(y))`, so the two structural facts of the `Cyl` layer give
the result off the degeneracy set `{r = 0} ∪ {x₃ = 0}`:

* `div (A • e_θ) x = A x · div e_θ x + (fderiv A x)(e_θ x)` (`div_smul_eq`),
* `div e_θ = 0` off the axis (`div_eTheta`),
* `(fderiv A x)(e_θ x) = 0`: along the line `t ↦ x + t • e_θ(x)` both `ρ(x+t e_θ) = √(ρ(x)²+t²)`
  and `θ(x+t e_θ) = arctan(x₃/√(radSq(x)+t²))` are *even* functions of `t`
  (`rho_add_smul_eTheta`, `theta_add_smul_eTheta`), so the derivative of the (even) line function
  at `t = 0` vanishes (`deriv_zero_of_even`).

The profile is `C¹` at `(ρ(x)^p/c, θ(x))` only when `θ(x) ≠ 0` (the angular factor
`Γ(θ) = (sinθcos²θ)^{p/3}` is not differentiable at `θ = 0` for `p ≤ 1`), whence the on-axis and
in-plane cases are treated separately, by *not* differentiating at all: whenever the field happens
to be differentiable at `x`, each diagonal entry of its Jacobian is computed along a coordinate
line and vanishes, because on the axis, and on the plane, the paired coordinate of the field
vanishes identically along the paired coordinate line; and where the field is not differentiable
the Fréchet derivative is `0` in Mathlib (`fderiv_zero_of_not_differentiableAt`), hence so is its
trace.  This is the same dichotomy as in `div_omega0_all`.
-/

/-! ## The `e_θ`-derivative of the scalar factor vanishes

Along `t ↦ x + t • e_θ(x)` the *self-similar variable* `ρ^p/c` of the profile is even in `t`, and
so is the angle `θ`; hence the whole scalar factor is an even function of `t`. -/

private theorem selfSim_scalar_fderiv_eTheta {p c : ℝ} {g : ℝ → ℝ → ℝ} {x : R3}
    (hr : 0 < Work.Cyl.radial x)
    (hA : DifferentiableAt ℝ
      (fun y : R3 => c⁻¹ * Work.ConstructionInstance.profile p g (Work.Cyl.rho y ^ p / c)
        (Work.Cyl.theta y)) x) :
    fderiv ℝ
      (fun y : R3 => c⁻¹ * Work.ConstructionInstance.profile p g (Work.Cyl.rho y ^ p / c)
        (Work.Cyl.theta y)) x (Work.Cyl.eTheta x) = 0 := by
  rw [Work.Cyl.fderiv_apply_eq_deriv_line _ x _ hA]
  apply deriv_zero_of_even
  intro t
  rw [rho_add_smul_eTheta x hr (-t), rho_add_smul_eTheta x hr t,
    theta_add_smul_eTheta x hr (-t), theta_add_smul_eTheta x hr t, neg_sq]

/-- Divergence of a swirl field `F • e_θ` whose scalar factor has vanishing `e_θ`-derivative. -/
private theorem div_smul_eTheta_of_fderiv_zero {F : R3 → ℝ} {x : R3}
    (hF : DifferentiableAt ℝ F x) (hr : 0 < Work.Cyl.radial x)
    (h0 : fderiv ℝ F x (Work.Cyl.eTheta x) = 0) :
    FiniteTimeSingularity.div (fun y : R3 => F y • Work.Cyl.eTheta y) x = 0 := by
  change FiniteTimeSingularity.div (F • Work.Cyl.eTheta) x = 0
  rw [div_smul_eq F Work.Cyl.eTheta x hF (differentiableAt_eTheta x hr), div_eTheta x hr, h0,
    mul_zero, zero_add]

/-! ## Vanishing of the paired coordinate along the coordinate lines of the degenerate set

The two ingredients of the on-axis/in-plane branch are supplied by the fleet (and proved in
`selfSim_profile_eTheta_coord_eq_zero.lean`), so that this file stays an assembly:

* `selfSim_profile_eTheta_coord_eq_zero` — on the axis and on the plane the `i`-th coordinate of
  `profile p g (ρ^p/c) (θ) · e_θ` vanishes along the `i`-th coordinate line;
* `selfSim_scalar_differentiableAt` — the scalar factor `c⁻¹ * profile p g (ρ^p/c) (θ)` is
  differentiable off the axis at points where the profile is (used in the off-plane branch). -/

/-! ## The main theorem -/

theorem div_selfSim_field {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ}
    (hvt : Work.Spaces.VanishTheta g) (hsmooth : Work.Stability.SmoothFar g) {c : ℝ} (hc : 0 < c) :
    ∀ x : Work.ConstructionInstance.R3,
      FiniteTimeSingularity.div
        (fun y : Work.ConstructionInstance.R3 =>
          c⁻¹ • Work.ConstructionInstance.omegaSz p g (Work.Cyl.rho y ^ p / c) y) x = 0 := by
  intro x
  have hfield : (fun y : R3 => c⁻¹ • omegaSz p g (Work.Cyl.rho y ^ p / c) y)
      = fun y : R3 =>
          (c⁻¹ * profile p g (Work.Cyl.rho y ^ p / c) (Work.Cyl.theta y)) • Work.Cyl.eTheta y := by
    funext y
    rw [omegaSz_apply, smul_smul]
  rw [hfield]
  by_cases hgen : 0 < Work.Cyl.radial x ∧ Work.Cyl.axial x ≠ 0
  · -- off the axis and off the plane: the swirl-field computation
    have hr : 0 < Work.Cyl.radial x := hgen.1
    have hρpos : 0 < Work.Cyl.rho x := lt_of_lt_of_le hr (Work.Cyl.radial_le_rho x)
    have hθ0 : Work.Cyl.theta x ≠ 0 := by
      intro h
      have h1 : Work.Cyl.axial x / Work.Cyl.radial x = 0 := by
        rw [← Real.arctan_eq_zero_iff]
        exact h
      rcases div_eq_zero_iff.mp h1 with h2 | h2
      · exact hgen.2 h2
      · exact absurd h2 (ne_of_gt hr)
    have hz : -1 < Work.Cyl.rho x ^ p / c := by
      have hpos : 0 < Work.Cyl.rho x ^ p / c :=
        div_pos (Real.rpow_pos_of_pos hρpos p) hc
      linarith
    have hθmem : Work.Cyl.theta x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩
    have hF : Work.Cyl.DiffAt2 (profile p g) (Work.Cyl.rho x ^ p / c) (Work.Cyl.theta x) :=
      (contDiffAt_uncurry_profile hsmooth hz hθmem hθ0).differentiableAt (by norm_num)
    have hA := selfSim_scalar_differentiableAt (p := p) (c := c) (g := g) hr hF
    exact div_smul_eTheta_of_fderiv_zero hA hr (selfSim_scalar_fderiv_eTheta hr hA)
  · -- on the axis or on the plane: differentiate along coordinate lines, or not at all
    have hcase : Work.Cyl.radial x = 0 ∨ Work.Cyl.axial x = 0 := by
      rcases not_and_or.mp hgen with h | h
      · exact Or.inl (le_antisymm (not_lt.mp h) (Work.Cyl.radial_nonneg x))
      · exact Or.inr (not_not.mp h)
    by_cases hd : DifferentiableAt ℝ
        (fun y : R3 => (c⁻¹ * profile p g (Work.Cyl.rho y ^ p / c) (Work.Cyl.theta y))
          • Work.Cyl.eTheta y) x
    · rw [Work.Cyl.div_eq_sum_partials _ x hd]
      apply Finset.sum_eq_zero
      intro i _
      have hline : (fun t : ℝ => ((fun y : R3 =>
          (c⁻¹ * profile p g (Work.Cyl.rho y ^ p / c) (Work.Cyl.theta y))
            • Work.Cyl.eTheta y) (x + t • Work.Cyl.basisVec i)) i) = fun _ : ℝ => 0 := by
        funext t
        simp only [PiLp.smul_apply, smul_eq_mul]
        rw [mul_assoc, selfSim_profile_eTheta_coord_eq_zero hp.ne' hvt.1 hcase i t, mul_zero]
      rw [hline]
      simp
    · rw [FiniteTimeSingularity.div, fderiv_zero_of_not_differentiableAt hd]
      simp

end Work.ConstructionInstance
