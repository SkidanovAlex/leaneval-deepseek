/-
# `Work.ConstructionInstance.div_cutDatum` — divergence-freeness of the cut-off datum

The cut-off datum of the construction is `ω₀ = χ(ρ/L) · ωS`, and `ωS = F(ρ^p, θ) · e_θ` is a
"swirl" field: a scalar profile (a function of `(ρ, θ)`, hence of `(r, x₃)`) times the angular
frame vector `e_θ`.

Off the axis (`0 < radial x`) every such field is divergence free.  Indeed, writing
`e_θ = (1/r)·(r e_θ) = (1/r)·angularVec` with `angularVec(x) = (-x₁, x₀, 0)` linear, a field
`A(r, x₃)·e_θ` equals `(A(r,x₃)/r)·angularVec(x)`, and the divergence — the sum of the one
dimensional derivatives along the coordinate lines (`Work.Cyl.div_eq_sum_partials`) — is

  `div u = -x₁ · ∂₀ c + x₀ · ∂₁ c`,  `c = A(r,x₃)/r`,

where the chain rule along the `e₀`/`e₁` lines (`Work.Cyl.hasDerivAt_comp_cyl_e0`,
`Work.Cyl.hasDerivAt_comp_cyl_e1`) gives `∂₀ c = (x₀/r)·∂_r(A/r)` and
`∂₁ c = (x₁/r)·∂_r(A/r)`.  Hence `div u = 0` for every profile `A`.

The field `ω₀ = (χ(ρ/L)·F(ρ^p, θ))·e_θ` is of this shape with the profile
`Φ(r,z) = χ(ρP(r,z)/L)·F(ρP(r,z)^p, θP(r,z))` (`ρP(r,z) = √(r²+z²)`, `θP(r,z) = arctan(z/r)`);
`Φ` is differentiable at `(radial x, axial x)` because `(r,z) ↦ (ρP(r,z)^p, θP(r,z))` is
differentiable there (`0 < r`) and `F = profile p g` is `C¹` at the image point `(ρ(x)^p, θ(x))`
— the hypothesis `hg` — while the smooth cut-off factor `χ` costs nothing.

Everything is proved from the `Work.Cyl` calculus layer; the main theorem is
`Work.ConstructionInstance.div_cutDatum`.
-/
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Submission.Work.ConstructionInstance.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology
open scoped Topology Matrix NNReal ENNReal

namespace Work.ConstructionInstance

/-! ## The dictionary `(rho, theta)` on `ℝ³` vs `(rhoP, thetaP)` on the `(r,x₃)` half plane -/

private lemma rho_eq_rhoP' (y : R3) :
    Work.Cyl.rho y = Work.Cyl.rhoP (Work.Cyl.radial y) (Work.Cyl.axial y) := by
  rw [Work.Cyl.rho, Work.Cyl.rhoP, Work.Cyl.radial_sq]

private lemma theta_eq_thetaP' (y : R3) :
    Work.Cyl.theta y = Work.Cyl.thetaP (Work.Cyl.radial y) (Work.Cyl.axial y) := rfl

/-! ## Swirl fields are divergence free -/

/-- The field `A(r,x₃) • angularVec = (A(r,x₃)/r) • (r e_θ)` (the `r`-multiple of a swirl field,
which is the smooth object off the axis). -/
private def swirlField (A : ℝ → ℝ → ℝ) : R3 → R3 :=
  fun y => A (Work.Cyl.radial y) (Work.Cyl.axial y) • Work.Cyl.angularVec y

private lemma differentiableAt_angularVec (x : R3) :
    DifferentiableAt ℝ Work.Cyl.angularVec x := by
  have hcoord : ∀ j : Fin 3, DifferentiableAt ℝ (fun y : R3 => y j) x := fun j =>
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) x j).differentiableAt
  rw [show Work.Cyl.angularVec = fun y : R3 =>
      (-(y 1)) • Work.Cyl.e0 + (y 0) • Work.Cyl.e1 from by
    funext y
    apply PiLp.ext
    intro i
    fin_cases i <;>
      simp [Work.Cyl.angularVec, Work.Cyl.e0, Work.Cyl.e1, FiniteTimeSingularity.e]]
  exact (((hcoord 1).neg).smul_const Work.Cyl.e0).add ((hcoord 0).smul_const Work.Cyl.e1)

/-- **A swirl field `A(r,x₃)·e_θ` is divergence free** off the axis, for every profile `A` which
is differentiable at `(radial x, axial x)`. -/
private theorem div_swirlField {A : ℝ → ℝ → ℝ} (x : R3)
    (hA : Work.Cyl.DiffAt2 A (Work.Cyl.radial x) (Work.Cyl.axial x))
    (hr : 0 < Work.Cyl.radial x) :
    FiniteTimeSingularity.div (swirlField A) x = 0 := by
  have hrne : Work.Cyl.radial x ≠ 0 := ne_of_gt hr
  have hpair : DifferentiableAt ℝ (fun y : R3 => (Work.Cyl.radial y, Work.Cyl.axial y)) x :=
    (Work.Cyl.differentiableAt_radial x hrne).prodMk (Work.Cyl.differentiableAt_axial x)
  have hdiffA : DifferentiableAt ℝ (fun y : R3 => A (Work.Cyl.radial y) (Work.Cyl.axial y)) x := by
    have h := hA.comp x hpair
    convert h using 1
    funext y; rfl
  have hU : DifferentiableAt ℝ (swirlField A) x := by
    have h := hdiffA.smul (differentiableAt_angularVec x)
    convert h using 1
    funext y; rfl
  rw [Work.Cyl.div_eq_sum_partials _ x hU, Fin.sum_univ_three]
  simp only [Work.Cyl.basisVec_zero, Work.Cyl.basisVec_one, Work.Cyl.basisVec_two]
  have hd0 := Work.Cyl.hasDerivAt_comp_cyl_e0 A x hA hr
  have hd1 := Work.Cyl.hasDerivAt_comp_cyl_e1 A x hA hr
  have hline0 : (fun t : ℝ => (swirlField A (x + t • Work.Cyl.e0)) 0)
      = fun t : ℝ =>
          A (Work.Cyl.radial (x + t • Work.Cyl.e0)) (Work.Cyl.axial (x + t • Work.Cyl.e0))
            * (-(x 1)) := by
    funext t
    simp [swirlField, smul_eq_mul]
  have hline1 : (fun t : ℝ => (swirlField A (x + t • Work.Cyl.e1)) 1)
      = fun t : ℝ =>
          A (Work.Cyl.radial (x + t • Work.Cyl.e1)) (Work.Cyl.axial (x + t • Work.Cyl.e1))
            * (x 0) := by
    funext t
    simp [swirlField, smul_eq_mul]
  have hline2 : (fun t : ℝ => (swirlField A (x + t • Work.Cyl.eZ)) 2) = fun t : ℝ => 0 := by
    funext t
    simp [swirlField, smul_eq_mul]
  rw [hline0, hline1, hline2]
  rw [(hd0.mul_const (-(x 1))).deriv, (hd1.mul_const (x 0)).deriv]
  rw [deriv_const (0 : ℝ)]
  ring

/-- **The divergence of `φ(r,x₃) • e_θ` vanishes** off the axis, for every profile `φ` which is
differentiable at `(radial x, axial x)`.  This is the shape of `omegaS p g` and of `omega₀ p g L`
once their scalar factors are merged. -/
private theorem div_smul_eTheta_of_diffAt2 {φ : ℝ → ℝ → ℝ} (x : R3)
    (hφ : Work.Cyl.DiffAt2 φ (Work.Cyl.radial x) (Work.Cyl.axial x))
    (hr : 0 < Work.Cyl.radial x) :
    FiniteTimeSingularity.div
      (fun y : R3 => φ (Work.Cyl.radial y) (Work.Cyl.axial y) • Work.Cyl.eTheta y) x = 0 := by
  have hrne : Work.Cyl.radial x ≠ 0 := ne_of_gt hr
  -- the reduced profile `(r,z) ↦ φ(r,z)/r` is differentiable at `(radial x, axial x)`
  have hnum : DifferentiableAt ℝ (fun q : ℝ × ℝ => φ q.1 q.2)
      (Work.Cyl.radial x, Work.Cyl.axial x) := hφ
  have hinv : DifferentiableAt ℝ (fun q : ℝ × ℝ => (q.1)⁻¹)
      (Work.Cyl.radial x, Work.Cyl.axial x) :=
    (by fun_prop : DifferentiableAt ℝ (fun q : ℝ × ℝ => q.1)
        (Work.Cyl.radial x, Work.Cyl.axial x)).inv (by simpa using hrne)
  have hred : Work.Cyl.DiffAt2 (fun r z : ℝ => φ r z / r) (Work.Cyl.radial x) (Work.Cyl.axial x) := by
    have hmain : DifferentiableAt ℝ (fun q : ℝ × ℝ => φ q.1 q.2 * (q.1)⁻¹)
        (Work.Cyl.radial x, Work.Cyl.axial x) := hnum.mul hinv
    convert hmain using 1
    funext q
    simp [div_eq_mul_inv]
  have hfield : (fun y : R3 => φ (Work.Cyl.radial y) (Work.Cyl.axial y) • Work.Cyl.eTheta y)
      = swirlField (fun r z : ℝ => φ r z / r) := by
    funext y
    show φ (Work.Cyl.radial y) (Work.Cyl.axial y) • Work.Cyl.eTheta y
      = (φ (Work.Cyl.radial y) (Work.Cyl.axial y) / Work.Cyl.radial y) • Work.Cyl.angularVec y
    rw [Work.Cyl.eTheta, smul_smul]
    congr 1
    simp [div_eq_mul_inv]
  rw [hfield]
  exact div_swirlField x hred hr

/-! ## Differentiability of the cut-off profile `Φ(r,z) = χ(ρP/L)·F(ρP^p, θP)` -/

private theorem diffAt2_cutProfile {p : ℝ} {g : ℝ → ℝ → ℝ} {L : ℝ} {x : R3}
    (hg : ContDiffAt ℝ 1 (Function.uncurry (profile p g)) ((Work.Cyl.rho x) ^ p, Work.Cyl.theta x))
    (hr : 0 < Work.Cyl.radial x) :
    Work.Cyl.DiffAt2
      (fun r z : ℝ =>
        Work.Stability.chi (Work.Cyl.rhoP r z / L) *
          profile p g (Work.Cyl.rhoP r z ^ p) (Work.Cyl.thetaP r z))
      (Work.Cyl.radial x) (Work.Cyl.axial x) := by
  have hρ0 : DifferentiableAt ℝ (fun q : ℝ × ℝ => Work.Cyl.rhoP q.1 q.2)
      (Work.Cyl.radial x, Work.Cyl.axial x) := by
    have h : (fun q : ℝ × ℝ => Work.Cyl.rhoP q.1 q.2)
        = fun q : ℝ × ℝ => Real.sqrt (q.1 ^ 2 + q.2 ^ 2) := by
      funext q; rw [Work.Cyl.rhoP]
    rw [h]
    apply DifferentiableAt.sqrt
    · fun_prop
    · exact ne_of_gt (by positivity)
  have hρ : DifferentiableAt ℝ (fun q : ℝ × ℝ => Work.Cyl.rhoP q.1 q.2 ^ p)
      (Work.Cyl.radial x, Work.Cyl.axial x) :=
    hρ0.rpow_const (Or.inl (ne_of_gt (Work.Cyl.rhoP_pos hr (Work.Cyl.axial x))))
  have hθ : DifferentiableAt ℝ (fun q : ℝ × ℝ => Work.Cyl.thetaP q.1 q.2)
      (Work.Cyl.radial x, Work.Cyl.axial x) := by
    have h : (fun q : ℝ × ℝ => Work.Cyl.thetaP q.1 q.2)
        = fun q : ℝ × ℝ => Real.arctan (q.2 * (q.1)⁻¹) := by
      funext q; rw [Work.Cyl.thetaP, div_eq_mul_inv]
    rw [h]
    apply DifferentiableAt.arctan
    have h1 : DifferentiableAt ℝ (fun q : ℝ × ℝ => q.2)
        (Work.Cyl.radial x, Work.Cyl.axial x) := by fun_prop
    have h2 : DifferentiableAt ℝ (fun q : ℝ × ℝ => (q.1)⁻¹)
        (Work.Cyl.radial x, Work.Cyl.axial x) :=
      (by fun_prop : DifferentiableAt ℝ (fun q : ℝ × ℝ => q.1)
        (Work.Cyl.radial x, Work.Cyl.axial x)).inv (by simpa using ne_of_gt hr)
    exact h1.mul h2
  have hpair : DifferentiableAt ℝ
      (fun q : ℝ × ℝ => (Work.Cyl.rhoP q.1 q.2 ^ p, Work.Cyl.thetaP q.1 q.2))
      (Work.Cyl.radial x, Work.Cyl.axial x) := hρ.prodMk hθ
  -- the profile is differentiable at the image point `(ρ(x)^p, θ(x))`
  have hprof : DifferentiableAt ℝ (Function.uncurry (profile p g))
      ((Work.Cyl.rho x) ^ p, Work.Cyl.theta x) := hg.differentiableAt (by simp)
  rw [rho_eq_rhoP' x, theta_eq_thetaP' x] at hprof
  have hcomp := hprof.comp (Work.Cyl.radial x, Work.Cyl.axial x) hpair
  -- the smooth cut-off factor `χ(·/L)` costs nothing
  have hcut : DifferentiableAt ℝ
      ((fun s : ℝ => Work.Stability.chi (s / L)) ∘ (fun q : ℝ × ℝ => Work.Cyl.rhoP q.1 q.2))
      (Work.Cyl.radial x, Work.Cyl.axial x) := by
    have h1 : DifferentiableAt ℝ (fun s : ℝ => Work.Stability.chi (s / L))
        (Work.Cyl.rhoP (Work.Cyl.radial x) (Work.Cyl.axial x)) :=
      ((Work.Stability.chi_contDiff.differentiable (by simp)).differentiableAt).comp _
        (by fun_prop : DifferentiableAt ℝ (fun s : ℝ => s / L)
          (Work.Cyl.rhoP (Work.Cyl.radial x) (Work.Cyl.axial x)))
    exact h1.comp (Work.Cyl.radial x, Work.Cyl.axial x) hρ0
  have hprod := hcut.mul hcomp
  convert hprod using 1
  · funext q
    simp [Function.uncurry, Function.comp_def, Pi.mul_apply]

/-! ## The main theorem -/

theorem div_cutDatum {p : ℝ} {g : ℝ → ℝ → ℝ} {L : ℝ} {x : Work.ConstructionInstance.R3}
    (hg : ContDiffAt ℝ 1 (Function.uncurry (Work.ConstructionInstance.profile p g))
      ((Work.Cyl.rho x) ^ p, Work.Cyl.theta x))
    (hr : 0 < Work.Cyl.radial x) :
    FiniteTimeSingularity.div (Work.ConstructionInstance.omega₀ p g L) x = 0 := by
  -- the cut-off profile as a function of `(r, x₃)`
  have hΦ : Work.Cyl.DiffAt2
      (fun r z : ℝ =>
        Work.Stability.chi (Work.Cyl.rhoP r z / L) *
          profile p g (Work.Cyl.rhoP r z ^ p) (Work.Cyl.thetaP r z))
      (Work.Cyl.radial x) (Work.Cyl.axial x) := diffAt2_cutProfile hg hr
  -- `omega₀ p g L = Φ(radial, axial) • e_θ`
  have hfield : omega₀ p g L
      = fun y : R3 =>
          (Work.Stability.chi (Work.Cyl.rhoP (Work.Cyl.radial y) (Work.Cyl.axial y) / L) *
            profile p g (Work.Cyl.rhoP (Work.Cyl.radial y) (Work.Cyl.axial y) ^ p)
              (Work.Cyl.thetaP (Work.Cyl.radial y) (Work.Cyl.axial y))) • Work.Cyl.eTheta y := by
    funext y
    have h1 : Work.Stability.chi (Work.Cyl.rho y / L) * profile p g (Work.Cyl.rho y ^ p)
          (Work.Cyl.theta y)
        = Work.Stability.chi (Work.Cyl.rhoP (Work.Cyl.radial y) (Work.Cyl.axial y) / L) *
          profile p g (Work.Cyl.rhoP (Work.Cyl.radial y) (Work.Cyl.axial y) ^ p)
            (Work.Cyl.thetaP (Work.Cyl.radial y) (Work.Cyl.axial y)) := by
      rw [rho_eq_rhoP' y, theta_eq_thetaP' y]
    rw [omega₀_apply, omegaS_apply', smul_smul, h1]
  rw [hfield]
  exact div_smul_eTheta_of_diffAt2 x hΦ hr

end Work.ConstructionInstance
