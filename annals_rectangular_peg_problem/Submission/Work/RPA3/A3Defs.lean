import Submission.Work.RPA3.TubularDefs

/-!
# RPA3: packaged data for block A3

Two structures collect the intermediate data of the flux primitive (D1) and of the tubular
extension (D2), so that the statements of the individual lemmas stay short.
-/

open scoped ContDiff
open Real

set_option autoImplicit false
noncomputable section

namespace Work.RPA3

/-- The flux primitive of a Lagrangian family: a function `h` whose differential is minus the
flux form `ω(∂_τℓ, ·)` along the family, `2π`-periodic in `t` and vanishing for `|x| ≥ X₀`. -/
structure FluxPrimitive (L : LagFamilyAll) where
  h : ℝ → ℝ × ℝ → ℝ
  smooth : ContDiff ℝ 7 (fun z : ℝ × (ℝ × ℝ) => h z.1 z.2)
  per : ∀ τ x t, h τ (x, t + 2 * π) = h τ (x, t)
  van : ∀ τ x t, L.X0 ≤ |x| → h τ (x, t) = 0
  dx : ∀ τ x t, deriv (fun y => h τ (y, t)) x =
    -symp (deriv (fun σ => L.ℓ σ (x, t)) τ) (deriv (fun y => L.ℓ τ (y, t)) x)
  dt : ∀ τ x t, deriv (fun s => h τ (x, s)) t =
    -symp (deriv (fun σ => L.ℓ σ (x, t)) τ) (deriv (fun s => L.ℓ τ (x, s)) t)

/-- The two analytic facts about the tubular map `theta` that the construction of the Hamiltonian
needs: a uniform injectivity radius on the compact part of the strip, and the local smooth inverse
charts (from the inverse function theorem). -/
structure TubularData (L : LagFamilyAll) where
  ε : ℝ
  εpos : 0 < ε
  inj : ∀ τ ∈ Set.Icc (-1 : ℝ) 2, ∀ x t x' t' (ξ ξ' : ℝ × ℝ),
    t ∈ Set.Icc 0 (2 * π) → t' ∈ Set.Icc 0 (2 * π) →
    ‖ξ‖ < ε → ‖ξ'‖ < ε → ∀ k : ℤ, theta L τ x t ξ = Tk k (theta L τ x' t' ξ') →
      x = x' ∧ ξ = ξ' ∧ ∃ m : ℤ, t' = t + 2 * π * m
  chart : ∀ w : ℝ × PS, w.1 ∈ Set.Icc (-1 : ℝ) 2 → |w.2.1.1| ≤ L.X0 + 1 → ‖w.2.2‖ < ε →
    ∃ (U : Set (ℝ × PS)) (σ : ℝ × PS → PS), IsOpen U ∧ thetaP L w ∈ U ∧ σ (thetaP L w) = w.2 ∧
      ContDiffOn ℝ 7 σ U ∧ ∀ p ∈ U, thetaP L (p.1, σ p) = p

end Work.RPA3
