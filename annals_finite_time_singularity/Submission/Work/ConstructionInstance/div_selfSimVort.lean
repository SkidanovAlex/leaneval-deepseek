/-
# `Work.ConstructionInstance.div_selfSimVort` — divergence-freeness of the constructed vorticity

The constructed (cut) self-similar vorticity of the construction is

  `ω(x,t) = λ̄(t)⁻¹ · χ(ρ(x)/L) · F(ρ(x)^p/λ̄(t), θ(x)) · e_θ(x)`   (`SelfSim.selfSimVort`),

i.e. the swirl field `A(x,t) • e_θ(x)` with scalar factor
`A = λ̄(t)⁻¹ · χ(ρ/L) · profile p g (ρ^p/λ̄(t)) (θ)`.  Every such field is divergence free:

* off the axis and off the plane `x₃ = 0` it is the *cut* swirl field
  `χ(ρ/L) • (c⁻¹ • omegaSz p g (ρ^p/c))`: the uncut factor is divergence free at **every** point
  (`div_selfSim_field`), and the cut-off factor costs nothing because
  `div (F • v) x = F x · div v x + (fderiv F x) (v x)` (`div_smul_eq`) while the second term
  vanishes — `v x` is parallel to `e_θ(x)` and `χ(ρ/L)` is invariant along the line
  `t ↦ x + t • e_θ(x)` (`ρ(x + t e_θ(x)) = √(ρ(x)² + t²)` is *even* in `t`,
  `rho_add_smul_eTheta`), so `(fderiv (χ(ρ/L)) x) (e_θ(x)) = 0` (`fderiv_chi_rho_div_eTheta`);
* on the axis (`r = 0`) and on the plane (`x₃ = 0`) we do not differentiate at all: if the field
  happens to be differentiable the divergence is the sum of the one-dimensional derivatives along
  the coordinate lines (`div_eq_sum_partials`) and each diagonal entry vanishes because on the
  axis, and on the plane, the paired coordinate of the field vanishes *identically* along the
  paired coordinate line (`selfSim_profile_eTheta_coord_eq_zero`); where the field is not
  differentiable the Fréchet derivative is `0` (`fderiv_zero_of_not_differentiableAt`), hence so
  is its trace.

The statement needs no positivity of `λ̄(t)` on the degeneracy set and no smoothness of `g` there;
off the degeneracy set `λ̄(t) > 0` is what makes the self-similar profile differentiable in the
`z`-variable (`selfSim_scalar_differentiableAt`), i.e. what makes the field differentiable at all.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.LinearAlgebra.Trace
import Submission.Work.ConstructionInstance.SelfSim
import Submission.Work.ConstructionInstance.div_omega0_all
import Submission.Work.ConstructionInstance.div_selfSim_field
import Submission.Work.ConstructionInstance.selfSim_scalar_differentiableAt
import Submission.Work.ConstructionInstance.selfSim_profile_eTheta_coord_eq_zero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

set_option linter.unusedVariables false

noncomputable section

open FiniteTimeSingularity Work.Cyl

/-! ## The cut-off factor `χ(ρ/L)` has vanishing derivative along `e_θ` -/

/-- `ρ` is even along the line `t ↦ x + t • e_θ(x)` (`rho_add_smul_eTheta`), hence so is the
cut-off factor `χ(ρ/L)`; its directional derivative at `x` along `e_θ` therefore vanishes. -/
lemma fderiv_chi_rho_div_eTheta {L : ℝ} {x : R3} (hr : 0 < Work.Cyl.radial x) :
    fderiv ℝ (fun y : R3 => Work.Stability.chi (Work.Cyl.rho y / L)) x (Work.Cyl.eTheta x) = 0 := by
  have hdiff : DifferentiableAt ℝ (fun y : R3 => Work.Cyl.rho y / L) x := by
    simpa only [div_eq_mul_inv] using
      (Work.Cyl.differentiableAt_rho_of_radial_pos x hr).mul_const L⁻¹
  have hF : DifferentiableAt ℝ
      (fun y : R3 => Work.Stability.chi (Work.Cyl.rho y / L)) x :=
    ((Work.Stability.chi_contDiff.differentiable (by simp)).differentiableAt).comp x hdiff
  rw [Work.Cyl.fderiv_apply_eq_deriv_line _ x _ hF]
  refine deriv_zero_of_even (fun t => ?_)
  rw [Work.ConstructionInstance.rho_add_smul_eTheta x hr (-t),
    Work.ConstructionInstance.rho_add_smul_eTheta x hr t, neg_sq]

/-! ## The coordinate-line vanishing on the axis and on the plane -/

/-- On the axis (`radial x = 0`) and on the plane `x₃ = 0` (`axial x = 0`) the `i`-th coordinate
of the constructed vorticity vanishes along the `i`-th coordinate line through `x`, at every time
`t`.  Only the first conjunct `g z 0 = 0` of `VanishTheta` and `p ≠ 0` are used: on the axis the
`i`-th coordinate of `e_θ` vanishes at the shifted point, and in the plane the angle `θ` vanishes
at the shifted point (for `i ≠ 2`), where the profile vanishes, while for `i = 2` the axial
component of `e_θ` vanishes. -/
lemma selfSimVort_coord_line_eq_zero {p : ℝ} (hp : p ≠ 0) {g : ℝ → ℝ → ℝ}
    (hg0 : ∀ z : ℝ, g z 0 = 0) {L : ℝ} {lam : ℝ → ℝ} {x : R3}
    (hx : Work.Cyl.radial x = 0 ∨ Work.Cyl.axial x = 0) (i : Fin 3) (s t : ℝ) :
    (selfSimVort p g L lam (x + s • Work.Cyl.basisVec i) t) i = 0 := by
  have hcoord : (selfSimVort p g L lam (x + s • Work.Cyl.basisVec i) t) i
      = (lam t)⁻¹ * (Work.Stability.chi (Work.Cyl.rho (x + s • Work.Cyl.basisVec i) / L)
          * (profile p g (Work.Cyl.rho (x + s • Work.Cyl.basisVec i) ^ p / lam t)
              (Work.Cyl.theta (x + s • Work.Cyl.basisVec i))
            * (Work.Cyl.eTheta (x + s • Work.Cyl.basisVec i)).ofLp i)) := by
    rw [selfSimVort_apply, omegaSz_apply]
    simp only [PiLp.smul_apply, smul_eq_mul]
  calc (selfSimVort p g L lam (x + s • Work.Cyl.basisVec i) t) i
      = (lam t)⁻¹ * (Work.Stability.chi (Work.Cyl.rho (x + s • Work.Cyl.basisVec i) / L)
          * (profile p g (Work.Cyl.rho (x + s • Work.Cyl.basisVec i) ^ p / lam t)
              (Work.Cyl.theta (x + s • Work.Cyl.basisVec i))
            * (Work.Cyl.eTheta (x + s • Work.Cyl.basisVec i)).ofLp i)) := hcoord
    _ = 0 := by
        simp [selfSim_profile_eTheta_coord_eq_zero hp hg0 hx i s]

/-! ## The main theorem -/

theorem div_selfSimVort {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ}
    (hvt : Work.Spaces.VanishTheta g) (hsmooth : Work.Spaces.SmoothNbhd g) {L : ℝ} (hL : 0 < L)
    {lam : ℝ → ℝ} {t : ℝ} (ht : 0 < lam t) :
    ∀ x : Work.ConstructionInstance.R3,
      FiniteTimeSingularity.div
        (fun y => Work.ConstructionInstance.selfSimVort p g L lam y t) x = 0 := by
  intro x
  have hsf : Work.Stability.SmoothFar g := Work.Stability.SmoothFar.of_smoothNbhd hsmooth
  -- the field is the cut-off factor times the uncut self-similar swirl field
  have hfield : (fun y : R3 => selfSimVort p g L lam y t)
      = (fun y : R3 => Work.Stability.chi (Work.Cyl.rho y / L))
        • (fun y : R3 => (lam t)⁻¹ • omegaSz p g (Work.Cyl.rho y ^ p / lam t) y) := by
    funext y
    rw [selfSimVort_apply]
    exact smul_comm (lam t)⁻¹ (Work.Stability.chi (Work.Cyl.rho y / L))
      (omegaSz p g (Work.Cyl.rho y ^ p / lam t) y)
  by_cases hgen : 0 < Work.Cyl.radial x ∧ Work.Cyl.axial x ≠ 0
  · -- off the axis and off the plane: the cut swirl field
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
    have hz : -1 < Work.Cyl.rho x ^ p / lam t := by
      have hpos : 0 < Work.Cyl.rho x ^ p / lam t :=
        div_pos (Real.rpow_pos_of_pos hρpos p) ht
      linarith
    have hθmem : Work.Cyl.theta x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩
    have hF2 : Work.Cyl.DiffAt2 (profile p g) (Work.Cyl.rho x ^ p / lam t) (Work.Cyl.theta x) :=
      (contDiffAt_uncurry_profile hsf hz hθmem hθ0).differentiableAt (by norm_num)
    -- differentiability of the cut-off factor and of the uncut swirl field at `x`
    have hFdiff : DifferentiableAt ℝ
        (fun y : R3 => Work.Stability.chi (Work.Cyl.rho y / L)) x := by
      have hdiff : DifferentiableAt ℝ (fun y : R3 => Work.Cyl.rho y / L) x := by
        simpa only [div_eq_mul_inv] using
          (Work.Cyl.differentiableAt_rho_of_radial_pos x hr).mul_const L⁻¹
      exact ((Work.Stability.chi_contDiff.differentiable (by simp)).differentiableAt).comp x hdiff
    have hVdiff : DifferentiableAt ℝ
        (fun y : R3 => (lam t)⁻¹ • omegaSz p g (Work.Cyl.rho y ^ p / lam t) y) x := by
      have hA := selfSim_scalar_differentiableAt (p := p) (c := lam t) (g := g) hr hF2
      have hE := differentiableAt_eTheta x hr
      have heq : (fun y : R3 => (lam t)⁻¹ • omegaSz p g (Work.Cyl.rho y ^ p / lam t) y)
          = (fun y : R3 => (lam t)⁻¹ * profile p g (Work.Cyl.rho y ^ p / lam t)
              (Work.Cyl.theta y)) • Work.Cyl.eTheta := by
        funext y
        simp [omegaSz_apply, smul_smul]
      rw [heq]
      exact hA.smul hE
    have hdivV : FiniteTimeSingularity.div
        (fun y : R3 => (lam t)⁻¹ • omegaSz p g (Work.Cyl.rho y ^ p / lam t) y) x = 0 :=
      div_selfSim_field hp hp1 hvt hsf ht x
    rw [hfield]
    rw [div_smul_eq _ _ x hFdiff hVdiff]
    rw [hdivV, mul_zero, zero_add]
    -- the only remaining term is `(fderiv (χ(ρ/L)) x) (v x)`, and `v x` is parallel to `e_θ`
    rw [omegaSz_apply, smul_smul, map_smul]
    rw [fderiv_chi_rho_div_eTheta hr]
    exact smul_zero _
  · -- on the axis or on the plane: differentiate along the coordinate lines, or not at all
    have hcase : Work.Cyl.radial x = 0 ∨ Work.Cyl.axial x = 0 := by
      rcases not_and_or.mp hgen with h | h
      · exact Or.inl (le_antisymm (not_lt.mp h) (Work.Cyl.radial_nonneg x))
      · exact Or.inr (not_not.mp h)
    by_cases hd : DifferentiableAt ℝ (fun y : R3 => selfSimVort p g L lam y t) x
    · rw [Work.Cyl.div_eq_sum_partials (fun y : R3 => selfSimVort p g L lam y t) x hd]
      refine Finset.sum_eq_zero fun i _ => ?_
      have hline : (fun s : ℝ => ((fun y : R3 => selfSimVort p g L lam y t)
          (x + s • Work.Cyl.basisVec i)).ofLp i) = fun _ : ℝ => 0 :=
        funext fun s => selfSimVort_coord_line_eq_zero hp.ne' hvt.1 hcase i s t
      rw [hline]
      simp
    · rw [FiniteTimeSingularity.div, fderiv_zero_of_not_differentiableAt hd]
      simp

end

end Work.ConstructionInstance
