/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# Injectivity of `ℂ[G] → N(G)`

The linear (indeed algebra-) map `D.lift : ℂ[G] → N(G)`, `g ↦ ρ(g)`, is injective.  This is
the algebraic shadow of the fact that the group von Neumann algebra trace `τ` is faithful.

The proof extracts coefficients: for `f : ℂ[G]` and `h : G`,

  `τ (ρ h * lift f) = f.coeff (h⁻¹)`,

because `τ (ρ h * ρ g) = τ (ρ (h * g)) = δ_{h*g,1}`.  Letting `h` range over `G` recovers
all coefficients of `f`, so `lift` is injective.
-/
import Mathlib
import Submission.Work.ORVonNeumann.VonNeumannAlgebra

set_option autoImplicit false

open Classical

namespace Work.ORVonNeumann.VonNeumannAlgebra

open Work.ORVonNeumann

/-- **Coefficient extraction.**  Pairing `lift f` against `ρ h` with the trace picks out
the coefficient of `h⁻¹` in `f`. -/
theorem tau_rho_mul_lift {G : Type*} [Group G] (D : GroupVonNeumannAlgebra G)
    (f : MonoidAlgebra ℂ G) (h : G) : D.τ (D.ρ h * D.lift f) = f.coeff h⁻¹ := by
  -- The summand of `ρ h * lift f` in terms of the trace.
  have hsum : ∀ a : G, D.τ (D.ρ h * f.coeff a • D.ρ a)
      = f.coeff a * (if a = h⁻¹ then (1 : ℂ) else 0) := by
    intro a
    have h1 : D.ρ h * f.coeff a • D.ρ a = f.coeff a • D.ρ (h * a) := by
      rw [Algebra.mul_smul_comm, map_mul]
    rw [h1, map_smul, smul_eq_mul]
    congr 1
    by_cases ha : h * a = 1
    · rw [if_pos (eq_inv_of_mul_eq_one_right ha), ha, D.τ_ρ_one]
    · rw [if_neg (fun hc => ha (by rw [hc, mul_inv_cancel])), D.τ_ρ_ne_one (h * a) ha]
  -- Collapsing a `Finsupp` sum against the indicator of a single index.
  have hcoeff : f.coeff.sum (fun a b => b * (if a = h⁻¹ then (1 : ℂ) else 0))
      = f.coeff h⁻¹ := by
    have h1 : (fun a (b : ℂ) => b * (if a = h⁻¹ then (1 : ℂ) else 0))
        = (fun a (b : ℂ) => if a = h⁻¹ then b else 0) := by
      funext a b
      by_cases ha : a = h⁻¹ <;> simp [ha]
    rw [h1, Finsupp.sum_ite_eq' f.coeff h⁻¹ (fun x v => v)]
    by_cases hs : h⁻¹ ∈ f.coeff.support
    · rw [if_pos hs]
    · rw [if_neg hs, Finsupp.notMem_support_iff.mp hs]
  have key : f.coeff.sum (fun a b => D.τ (D.ρ h * b • D.ρ a)) = f.coeff h⁻¹ := by
    rw [Finsupp.sum_congr (f := f.coeff) (g1 := fun a b => D.τ (D.ρ h * b • D.ρ a))
      (g2 := fun a b => b * (if a = h⁻¹ then (1 : ℂ) else 0)) (by intro a _; exact hsum a)]
    exact hcoeff
  rw [GroupVonNeumannAlgebra.lift, Finsupp.mul_sum, map_finsuppSum]
  exact key

theorem lift_injective {G : Type*} [Group G] (D : Work.ORVonNeumann.GroupVonNeumannAlgebra G) : Function.Injective D.lift := by
  intro f f' hff'
  refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
  have h1 := tau_rho_mul_lift D f g⁻¹
  have h2 := tau_rho_mul_lift D f' g⁻¹
  rw [inv_inv] at h1 h2
  rw [hff'] at h1
  rw [← h1, h2]

end Work.ORVonNeumann.VonNeumannAlgebra
