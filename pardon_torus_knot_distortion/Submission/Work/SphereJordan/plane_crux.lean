import Mathlib
import Submission.Work.SphereJordan.ladder_approx

/-!
# The plane crux: loops in an open set with connected complement-in-the-sphere

This file assembles the classical "plane crux" — every loop in an open `U ⊆ ℂ` whose complement
in the Riemann sphere is preconnected is null-homotopic in `U` — from

* the lattice approximation `Work.SphereJordan.exists_lwalk_freeHomotopic` (a loop in `U` is freely
  homotopic, inside `↥U`, to the realization `W.loopNat hval` of a lattice walk with trace in `U`),
  and
* `Work.SphereJordan.lwalk_nullhomotopic` (the peel, already proved in this workspace).
-/

namespace Work.SphereJordan

open Set
open Work.Smooth.JordanSeparation

noncomputable section

/-- **The approximation interface.**  Every loop in an open `U ⊆ ℂ` is freely homotopic, inside
`↥U`, to the realization of a closed lattice walk whose trace lies in `U`. -/
def LWalkApprox : Prop :=
  ∀ {U : Set ℂ}, IsOpen U → ∀ {x : ℂ} (hx : x ∈ U),
    ∀ (γ : Path (⟨x, hx⟩ : ↥U) (⟨x, hx⟩ : ↥U)),
      ∃ (W : LWalk) (hval : ∀ t, W.path t ∈ U),
        FreeHomotopic γ (W.loopNat hval)

theorem LWalkApprox_proof : LWalkApprox := by
  intro U hUo x hx γ
  exact exists_lwalk_freeHomotopic hUo hx γ

/-- **The plane crux at the level of loops.**  From the approximation interface: every loop in an
open `U ⊆ ℂ` with preconnected complement in the Riemann sphere is null-homotopic in `U`. -/
theorem plane_loops_nullhomotopic_of_approx (happrox : LWalkApprox)
    {U : Set ℂ} (hUo : IsOpen U)
    (hpre : IsPreconnected (((↑) : ℂ → OnePoint ℂ) '' Uᶜ ∪ {OnePoint.infty}))
    {x : ℂ} (hx : x ∈ U) (γ : Path (⟨x, hx⟩ : ↥U) (⟨x, hx⟩ : ↥U)) :
    Path.Homotopic γ (Path.refl _) := by
  obtain ⟨W, hval, hfree⟩ := happrox hUo hx γ
  exact nullhomotopic_of_freeHomotopic hfree (lwalk_nullhomotopic hUo hpre hval)

/-- **The plane crux.**  An open preconnected subset of `ℂ` whose complement in the Riemann
sphere is preconnected is simply connected. -/
theorem plane_crux_of_approx (happrox : LWalkApprox) {U : Set ℂ} (hUo : IsOpen U)
    (hUne : U.Nonempty) (hUpre : IsPreconnected U)
    (hpre : IsPreconnected (((↑) : ℂ → OnePoint ℂ) '' Uᶜ ∪ {OnePoint.infty})) :
    IsSimplyConnected U := by
  rw [IsSimplyConnected, simply_connected_iff_loops_nullhomotopic]
  refine ⟨?_, fun x γ => ?_⟩
  · exact isPathConnected_iff_pathConnectedSpace.mp
      ((hUo.isConnected_iff_isPathConnected).mp ⟨hUne, hUpre⟩)
  · exact plane_loops_nullhomotopic_of_approx happrox hUo hpre x.2 γ

end

end Work.SphereJordan
