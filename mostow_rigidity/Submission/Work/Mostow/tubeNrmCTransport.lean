import Mathlib
import Submission.Work.Mostow.fermi_inv
import Submission.Work.Mostow.cosh_hdist_fermi
import Submission.Work.Mostow.blkMap_linBlk
import Submission.Work.Mostow.fermiFootDist

/-!
# Transport of the normal coordinate through a bounded perturbation

`tubeNrmCTransport` (GAP-A / thin-tube chapter): if a point `u` lies in the Fermi tube
`tube j m ρ` about the standard stratum, i.e. `‖nrmC j m u‖ ≤ sinh ρ`, and `x` is at
hyperbolic distance at most `1` from `u`, then the normal coordinate of `x` is still
bounded by `sinh (ρ + 1)`.

Mathematically this is the statement that `u ↦ arsinh ‖nrmC j m u‖` — the hyperbolic
distance to the standard stratum `stdTG j m` — is `1`-Lipschitz, combined with
`arsinh (sinh ρ) = ρ` and the monotonicity of `sinh`.  The two distance-to-stratum facts
(`hdist u (coordEmb _ (fermiInv u).1) = arsinh ‖nrmC u‖` and
`arsinh ‖nrmC u‖ ≤ hdist u (coordEmb _ v')`) are the content of `fermiFootDist`.
-/

namespace Work.Mostow

open Submission.Mostow in
theorem tubeNrmCTransport {j m : ℕ} (hI : HypIsometryProp (j + m)) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {u x : E (j + m)} (hu : u ∈ tube j m ρ) (hux : hdist u x ≤ 1) :
    ‖nrmC j m x‖ ≤ Real.sinh (ρ + 1) := by
  -- symmetry and triangle inequality for `hdist`
  have hsym : ∀ a b : E (j + m), hdist a b = hdist b a := hI.2.1
  have htri : ∀ a b c : E (j + m), hdist a c ≤ hdist a b + hdist b c := hI.2.2.2.1
  -- the two "distance to the standard stratum" identities
  obtain ⟨-, -, hfoot, hlow⟩ := fermiFootDist j m
  -- the foot of `u` in the stratum, and the three comparisons
  have hA : Real.arsinh ‖nrmC j m x‖ ≤ hdist x (coordEmb j m (fermiInv j m u).1) :=
    hlow x (fermiInv j m u).1
  have hB : hdist x (coordEmb j m (fermiInv j m u).1)
      ≤ hdist x u + Real.arsinh ‖nrmC j m u‖ := by
    rw [← hfoot u]
    exact htri x u _
  have hD : Real.arsinh ‖nrmC j m u‖ ≤ ρ := by
    have h : Real.arsinh ‖nrmC j m u‖ ≤ Real.arsinh (Real.sinh ρ) :=
      Real.arsinh_le_arsinh.mpr (show ‖nrmC j m u‖ ≤ Real.sinh ρ from hu)
    rwa [Real.arsinh_sinh ρ] at h
  have hF : hdist x u ≤ 1 := by
    rw [hsym x u]
    exact hux
  have hE : Real.arsinh ‖nrmC j m x‖ ≤ ρ + 1 := by linarith
  calc ‖nrmC j m x‖ = Real.sinh (Real.arsinh ‖nrmC j m x‖) := (Real.sinh_arsinh _).symm
    _ ≤ Real.sinh (ρ + 1) := Real.sinh_le_sinh.mpr hE

end Work.Mostow
