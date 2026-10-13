/-
  WilE9 / Sharp / AE — the analytic core of the component locality of a `Good` stratum.

  This is the statement that was originally requested as a separate lemma; it is now proved
  inside `Sharp/AE/component_locality.lean` as `zero_set_component_locality_aux` (the implicit
  function theorem applied to a `C^∞` map `F` whose fibre Jacobian is invertible makes the zero
  set of `F` near `u` a graph over a ball of the base, hence connected).  The present file only
  re-exports it under the public name.
-/
import Mathlib
import Submission.Work.WilE9.Sharp.AE.component_locality

namespace Work.WilE9.Sharp.AE

/-- **The zero set of `F` near `u` stays in the component of `T` through `u`.**  If `F` is `C^∞`
at `u`, `F u = 0`, the fibre Jacobian of `F` at `u` is invertible, and the zero set of `F`
germ-wise lies in `T`, then every near-by zero of `F` lies in the connected component of `T`
through `u`. -/
theorem zero_set_component_locality {n q : ℕ}
    (F : ((Fin n → ℝ) × (Fin q → ℝ)) → (Fin q → ℝ))
    (u : (Fin n → ℝ) × (Fin q → ℝ))
    (hcdf : ContDiffAt ℝ ⊤ F u) (hF0 : F u = 0)
    (hif : ((fderiv ℝ F u) ∘SL ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin q → ℝ)).IsInvertible)
    (T : Set ((Fin n → ℝ) × (Fin q → ℝ)))
    (hT : ∀ᶠ v in nhds u, F v = 0 → v ∈ T) :
    ∀ᶠ v in nhds u, F v = 0 → v ∈ connectedComponentIn T u :=
  zero_set_component_locality_aux F u hcdf hF0 hif T hT

end Work.WilE9.Sharp.AE
