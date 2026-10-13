/-
# Parity of the Biot–Savart field of the constructed self-similar vorticity

The constructed vorticity (`Reduced.solVort`) is the cut self-similar field

  `ω(x,t) = λ̄(t)⁻¹·χ(ρ(x)/L)·F(ρ(x)^p/λ̄(t), θ(x))·e_θ(x)`,

so every slice `ω(·,t)` is a *swirl* field: an angular scalar (odd in `θ`, because the profile
`F = F_* + g` is odd in `θ`) times the frame vector `e_θ`.  Two dictionary facts about such a
field, both already available in the workspace, deliver the oddness of its Biot–Savart field:

* **parity** — `IsOddVorticity` (`ω ∘ reflZ = -flipZ ∘ ω`): under the reflection `x ↦ (x₀,x₁,-x₃)`
  one has `ρ ↦ ρ`, `θ ↦ -θ`, `e_θ ↦ e_θ` and `flipZ (a • e_θ) = a • e_θ`, so the parity of the
  field is the parity of its scalar, which is `profile_odd`;
* **axisymmetry without swirl** — the slice is of the shape `f(radial x)(axial x) • e_θ(x)`, to
  which `isAxiNoSwirl_biotSavart` applies (Biot–Savart of a swirl vorticity has no swirl).

`Work.SolutionDelivery.isOdd_biotSavart_of_axiNoSwirl` (reflection equivariance of the
Biot–Savart integral `Work.LWP.biotSavart_reflZ`, plus `Work.Cyl.isOdd_of_reflZ_invariant`)
turns exactly these two facts into `IsOdd (biotSavart ω(·,t))`, which is the lemma proved here.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.ConstructionInstance.Reduced
import Submission.Work.ConstructionInstance.isOddVorticity_omegaS
import Submission.Work.ConstructionInstance.isAxiNoSwirl_biotSavart
import Submission.Work.SolutionDelivery.DatumOdd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-! ## The `Cyl` dictionary under the reflection `reflZ` -/

/-- The three dimensional radius is invariant under the reflection in the plane `x₃ = 0`. -/
private lemma rho_reflZL (x : R3) : Work.Cyl.rho (Work.LWP.reflZ x) = Work.Cyl.rho x := by
  have h1 : Work.Cyl.radSq (Work.LWP.reflZ x) = Work.Cyl.radSq x := by
    simp [Work.Cyl.radSq, Work.LWP.reflZ]
  have h2 : Work.Cyl.axial (Work.LWP.reflZ x) = -Work.Cyl.axial x := by
    simp [Work.Cyl.axial, Work.LWP.reflZ]
  rw [Work.Cyl.rho, Work.Cyl.rho, h1, h2, neg_sq]

/-- The polar angle changes sign under the reflection in the plane `x₃ = 0`. -/
private lemma theta_reflZL (x : R3) :
    Work.Cyl.theta (Work.LWP.reflZ x) = - Work.Cyl.theta x := by
  simp [Work.Cyl.theta, Work.Cyl.radial, Work.Cyl.radSq, Work.Cyl.axial, Work.LWP.reflZ,
    neg_div, Real.arctan_neg]

/-- The angular frame vector `e_θ` is invariant under the reflection in the plane `x₃ = 0`. -/
private lemma eTheta_reflZL (x : R3) :
    Work.Cyl.eTheta (Work.LWP.reflZ x) = Work.Cyl.eTheta x := by
  simp [Work.Cyl.eTheta, Work.Cyl.radial, Work.Cyl.radSq, Work.Cyl.angularVec, Work.LWP.reflZ]

/-- The flip of the third component is real-linear. -/
private lemma flipZ_smulL (c : ℝ) (v : R3) :
    Work.LWP.flipZ (c • v) = c • Work.LWP.flipZ v := by
  ext i
  fin_cases i <;> simp [Work.LWP.flipZ]

/-- The flip of the third component fixes `e_θ` (which lies in the plane `x₃ = 0`). -/
private lemma flipZ_eThetaL (x : R3) : Work.LWP.flipZ (Work.Cyl.eTheta x) = Work.Cyl.eTheta x := by
  ext i
  fin_cases i <;> simp [Work.LWP.flipZ, Work.Cyl.eTheta]

/-! ## The parity dictionary for `(ρ,θ)`-swirl fields -/

/-- **A field `x ↦ W(ρ(x),θ(x)) • e_θ(x)` whose scalar is odd in the angular variable is in the
parity class `IsOddVorticity`.**  (The cut-off and the modulation only enter through the scalar
`W`, so this covers `omegaS`, the cut datum and every slice `solVort P · t` at once.) -/
theorem isOddVorticity_smul_eTheta {W : ℝ → ℝ → ℝ} (hW : ∀ ρ θ, W ρ (-θ) = - W ρ θ) :
    Work.LWP.IsOddVorticity
      (fun x : R3 => W (Work.Cyl.rho x) (Work.Cyl.theta x) • Work.Cyl.eTheta x) := by
  intro x
  show W (Work.Cyl.rho (Work.LWP.reflZ x)) (Work.Cyl.theta (Work.LWP.reflZ x))
        • Work.Cyl.eTheta (Work.LWP.reflZ x)
      = - Work.LWP.flipZ (W (Work.Cyl.rho x) (Work.Cyl.theta x) • Work.Cyl.eTheta x)
  rw [rho_reflZL, theta_reflZL, eTheta_reflZL, hW, neg_smul, flipZ_smulL, flipZ_eThetaL]

/-! ## The slice of the constructed vorticity as a swirl field -/

/-- The scalar profile of the slice `t` of the constructed vorticity: the field is
`x ↦ scalarProfile P t (ρ x) (θ x) • e_θ(x)`. -/
private noncomputable def scalarProfile {α : NNReal} (P : ProfileData α) (t : ℝ)
    (ρ θ : ℝ) : ℝ :=
  (P.lam t)⁻¹ * Work.Stability.chi (ρ / P.L)
    * profile (profExp α) P.g (ρ ^ profExp α / P.lam t) θ

/-- `solVort P · t` is a `(ρ,θ)`-swirl field, pointwise. -/
private lemma solVort_apply_scalarProfile {α : NNReal} (P : ProfileData α) (t : ℝ) (y : R3) :
    solVort P y t
      = scalarProfile P t (Work.Cyl.rho y) (Work.Cyl.theta y) • Work.Cyl.eTheta y := by
  rw [solVort_apply, omegaSz_apply]
  simp only [scalarProfile, smul_smul]
  ring_nf

/-- The same, as an identity of functions. -/
private lemma solVort_eq_smul_eTheta {α : NNReal} (P : ProfileData α) (t : ℝ) :
    (fun y : R3 => solVort P y t)
      = fun y => scalarProfile P t (Work.Cyl.rho y) (Work.Cyl.theta y) • Work.Cyl.eTheta y :=
  funext (solVort_apply_scalarProfile P t)

/-- The scalar profile of the slice is odd in the angular variable: this is `profile_odd` for the
odd extension `profile (profExp α) P.g`, the perturbation vanishing at `θ = 0`. -/
private lemma scalarProfile_odd {α : NNReal} (P : ProfileData α) (t : ℝ) :
    ∀ ρ θ : ℝ, scalarProfile P t ρ (-θ) = - scalarProfile P t ρ θ := by
  have hp : profExp α ≠ 0 := ne_of_gt (profExp_pos P.hα)
  have hg0 : ∀ z : ℝ, P.g z 0 = 0 := P.hvt.1
  intro ρ θ
  rw [scalarProfile, scalarProfile, profile_odd hp hg0]
  ring

/-- **The parity of every slice of the constructed vorticity.** -/
theorem isOddVorticity_solVort {α : NNReal} (P : ProfileData α) (t : ℝ) :
    Work.LWP.IsOddVorticity (fun y => solVort P y t) := by
  have h := isOddVorticity_smul_eTheta (scalarProfile_odd P t)
  rwa [← solVort_eq_smul_eTheta P t] at h

/-! ## The slice as a function of `(radial, axial)` -/

/-- **The `(radial, axial)` form of the slice**: `ρ` and `θ` are functions of `(radial x, axial x)`,
so the slice is `f(radial x)(axial x) • e_θ(x)`, the shape consumed by
`isAxiNoSwirl_biotSavart`. -/
private lemma solVort_eq_radialAxial {α : NNReal} (P : ProfileData α) (t : ℝ) (y : R3) :
    solVort P y t
      = scalarProfile P t (Work.Cyl.rhoP (Work.Cyl.radial y) (Work.Cyl.axial y))
          (Work.Cyl.thetaP (Work.Cyl.radial y) (Work.Cyl.axial y)) • Work.Cyl.eTheta y := by
  rw [solVort_apply_scalarProfile]
  have hρ : Work.Cyl.rho y = Work.Cyl.rhoP (Work.Cyl.radial y) (Work.Cyl.axial y) := by
    rw [Work.Cyl.rho, Work.Cyl.rhoP, Work.Cyl.radial_sq]
  have hθ : Work.Cyl.theta y = Work.Cyl.thetaP (Work.Cyl.radial y) (Work.Cyl.axial y) := rfl
  rw [hρ, hθ]

/-- **The Biot–Savart field of every slice of the constructed vorticity is axisymmetric without
swirl**: the slice is a swirl field of the shape `f(radial, axial) • e_θ`, so
`isAxiNoSwirl_biotSavart` (equivariance of the Boole integral under the rotations about the
`x₃`-axis and under the reflection `x₁ ↦ -x₁`) applies. -/
theorem isAxiNoSwirl_biotSavart_solVort {α : NNReal} (P : ProfileData α) (t : ℝ) :
    Work.Cyl.IsAxiNoSwirl (Work.LWP.biotSavart (fun y => solVort P y t)) :=
  isAxiNoSwirl_biotSavart (f := fun r a =>
      scalarProfile P t (Work.Cyl.rhoP r a) (Work.Cyl.thetaP r a))
    (fun y => solVort_eq_radialAxial P t y)

/-! ## The target -/

theorem isOdd_biotSavart_solVort {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) :
    ∀ t ∈ Work.ConstructionInstance.preWindow P.T,
      FiniteTimeSingularity.IsOdd
        (Work.LWP.biotSavart (fun y => Work.ConstructionInstance.solVort P y t)) := by
  intro t _
  exact Work.SolutionDelivery.isOdd_biotSavart_of_axiNoSwirl (isOddVorticity_solVort P t)
    (isAxiNoSwirl_biotSavart_solVort P t)

end Work.ConstructionInstance
