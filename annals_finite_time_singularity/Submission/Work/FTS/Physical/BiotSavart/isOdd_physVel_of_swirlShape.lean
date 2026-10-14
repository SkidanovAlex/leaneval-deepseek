import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS_MuLamOK.Rows.rl0_final
import Submission.Work.SolutionDelivery.DatumEuler
import Submission.Work.SolutionDelivery.DatumOdd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Physical.BiotSavart

/-- **Oddness of the physical velocity of a swirl vorticity.**  If the slice `ω(·,t)` of the
vorticity is a swirl field `x ↦ W(ρ(x), θ(x)) • e_θ(x)` whose angular scalar is odd in the angle,
then its Biot–Savart velocity `physVel ω · t` is odd in the sense of `IsOdd` (componentwise:
component `i` odd in coordinate `i`, even in the other two).

The three dictionary facts used are exactly the ones available in the workspace:

* `Work.ConstructionInstance.isOddVorticity_smul_eTheta`: under `x ↦ reflZ x = (x₀,x₁,-x₃)` one
  has `ρ ↦ ρ`, `θ ↦ -θ`, `e_θ ↦ e_θ`, so the parity of the swirl field is that of its scalar,
  which is `hW`; hence the slice lies in the class `IsOddVorticity`;
* `Work.ConstructionInstance.isAxiNoSwirl_biotSavart`: a vorticity of the shape
  `f(radial x)(axial x) • e_θ(x)` (here `f r a = W(ρ(r,a), θ(r,a))` since `ρ = rhoP(radial,axial)`
  and `θ = thetaP(radial,axial)` definitionally) has axisymmetric no-swirl Biot–Savart field;
* `Work.SolutionDelivery.isOdd_biotSavart_of_axiNoSwirl`: reflection equivariance of the
  Biot–Savart integral plus axisymmetry no-swirl upgrades to the full `IsOdd`
  (`Work.Cyl.isOdd_of_reflZ_invariant`). -/
theorem isOdd_physVel_of_swirlShape {W : ℝ → ℝ → ℝ} {ω : Work.FTS.Physical.R3 → ℝ → Work.FTS.Physical.R3} {t : ℝ} (hshape : ∀ x : Work.FTS.Physical.R3, ω x t = W (Work.Cyl.rho x) (Work.Cyl.theta x) • Work.Cyl.eTheta x) (hW : ∀ ρ θ : ℝ, W ρ (-θ) = - W ρ θ) : FiniteTimeSingularity.IsOdd ((Work.FTS.Physical.physVel ω) · t) := by
  -- The slice as a function is the `(ρ,θ)`-swirl field of the hypothesis.
  have hfun : (fun y : Work.FTS.Physical.R3 => ω y t)
      = fun x : Work.FTS.Physical.R3 =>
          W (Work.Cyl.rho x) (Work.Cyl.theta x) • Work.Cyl.eTheta x :=
    funext hshape
  -- Parity dictionary: the slice lies in the class `IsOddVorticity`.
  have hωv : Work.LWP.IsOddVorticity (fun y => ω y t) := by
    rw [hfun]
    exact Work.ConstructionInstance.isOddVorticity_smul_eTheta hW
  -- The slice is a swirl field in the `(radial, axial)` profiles.
  have hshape2 : ∀ x, ω x t = (fun r a => W (Work.Cyl.rhoP r a) (Work.Cyl.thetaP r a))
        (Work.Cyl.radial x) (Work.Cyl.axial x) • Work.Cyl.eTheta x := by
    intro x
    rw [hshape x]
    have hρ : Work.Cyl.rhoP (Work.Cyl.radial x) (Work.Cyl.axial x) = Work.Cyl.rho x := by
      rw [Work.Cyl.rhoP, Work.Cyl.rho, Work.Cyl.radial_sq]
    have hθ : Work.Cyl.thetaP (Work.Cyl.radial x) (Work.Cyl.axial x) = Work.Cyl.theta x := rfl
    simp only [hρ, hθ]
  -- Biot–Savart of a swirl field is axisymmetric without swirl.
  have hax : Work.Cyl.IsAxiNoSwirl (Work.LWP.biotSavart (fun y => ω y t)) :=
    Work.ConstructionInstance.isAxiNoSwirl_biotSavart (ω := fun y => ω y t)
      (f := fun r a => W (Work.Cyl.rhoP r a) (Work.Cyl.thetaP r a)) hshape2
  rw [Work.FTS.Physical.physVel_slice]
  exact Work.SolutionDelivery.isOdd_biotSavart_of_axiNoSwirl hωv hax

end Work.FTS.Physical.BiotSavart
