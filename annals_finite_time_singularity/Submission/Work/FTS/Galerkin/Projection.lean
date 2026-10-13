/-
# The GALERKIN area: the formal Galerkin reduction (audit §4 N6, steps 2–4)

This module contains the *purely formal* core of the Galerkin scheme: the projected evolution
equation `IsGalerkinCoeff` is an ODE in the finite-dimensional space `Fin n → ℝ`
(`isGalerkinCoeff_iff_coord`), and, when the test sequence is `IP`-orthonormal
(`IsIPOrthonormal`, derived from the raw orthonormality by
`Submission/Work/FTS/Galerkin/Projection/ip_galFun_pair.lean`), it is *equivalent* to the tested
(weak) form of the fake-time equation:

  `d/dτ IP (gₙ(τ)) (φ k) = IP (-𝓛_Γ^T gₙ + gRHS(μ̄,λ,F_*+gₙ,Ψ(gₙ),gₙ)) (φ k)` for all `k < n`.

Two further consequences are recorded, both of which are the formal content of the audit's step 4
("the energy identity is exact, because `Pₙ` is `IP`-orthogonal"):

* `galFam_energy`: at each `τ`, `IP gₙ(τ) gₙ(τ) = ∑ₖ cₖ(τ)²`;
* `hasDerivWithinAt_galFam_energy`: hence
  `d/dτ ∑ₖ cₖ(τ)² = 2 ∑ₖ cₖ(τ) ċₖ(τ)`, i.e. the pairing `IP ġₙ gₙ` is exactly the Euclidean
  pairing of the coefficient curve with its projected vector field.  This is why the a-priori
  estimate of §Modulation applies to the Galerkin families *without* any loss.

Everything here is child-independent: the pairing property is taken as an explicit hypothesis
(`IsIPOrthonormal IP φ`), the derivation of which from the raw orthonormality lives in
`Submission/Work/FTS/Galerkin/OrdBridge.lean`.
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.Galerkin.Hilbert

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Galerkin

set_option autoImplicit false

/-! ## The projected equation is a finite-dimensional ODE -/

theorem galField_apply (α : ℝ) (IP : Fn → Fn → ℝ) (φ : ℕ → Fn) (n : ℕ) (Psi : Fam → Fam)
    (τ : ℝ) (c : Fin n → ℝ) (k : Fin n) :
    galField α IP φ n Psi τ c k = IP (galRHS α φ n Psi τ c) (φ (k : ℕ)) := rfl

/-- The projected equation, coordinate by coordinate. -/
theorem isGalerkinCoeff_iff_coord {α : ℝ} {IP : Fn → Fn → ℝ} {φ : ℕ → Fn} {n : ℕ}
    {Psi : Fam → Fam} {c : ℝ → Fin n → ℝ} :
    IsGalerkinCoeff α IP φ n Psi c ↔
      ∀ k : Fin n, ∀ τ, 0 ≤ τ → HasDerivWithinAt (fun s => c s k)
        (galField α IP φ n Psi τ (c τ) k) (Set.Ici 0) τ := by
  constructor
  · intro h k τ hτ
    exact hasDerivWithinAt_pi.mp (h τ hτ) k
  · intro h τ hτ
    exact hasDerivWithinAt_pi.mpr (fun k => h k τ hτ)

/-- **The tested (weak) form of the Galerkin equation.**  If the coefficient curve solves the
projected ODE and the test sequence is `IP`-orthonormal, then for each `k < n` the scalar function
`τ ↦ IP (gₙ(τ)) (φ k) = cₖ(τ)` has derivative the `IP`-pairing of the projected right hand side
with `φ k`. -/
theorem isGalerkinCoeff_weak {α : ℝ} {IP : Fn → Fn → ℝ} {φ : ℕ → Fn} {n : ℕ} {Psi : Fam → Fam}
    {c : ℝ → Fin n → ℝ} (hpair : IsIPOrthonormal IP φ)
    (hc : IsGalerkinCoeff α IP φ n Psi c) (k : Fin n) :
    ∀ τ, 0 ≤ τ → HasDerivWithinAt (fun s => IP (galFun φ (c s)) (φ (k : ℕ)))
      (IP (galRHS α φ n Psi τ (c τ)) (φ (k : ℕ))) (Set.Ici 0) τ := by
  intro τ hτ
  have hfun : (fun s => IP (galFun φ (c s)) (φ (k : ℕ))) = fun s => c s k := by
    funext s
    exact hpair.coeff n (c s) k
  rw [hfun]
  exact (isGalerkinCoeff_iff_coord.mp hc) k τ hτ

/-- The tested form, written on the Galerkin family: `gₙ(τ) = ∑ cₖ(τ) φ k` and its stream function
is `Ψ(gₙ)`. -/
theorem isGalerkinCoeff_weak_fam {α : ℝ} {IP : Fn → Fn → ℝ} {φ : ℕ → Fn} {n : ℕ}
    {Psi : Fam → Fam} {c : ℝ → Fin n → ℝ} (hpair : IsIPOrthonormal IP φ)
    (hc : IsGalerkinCoeff α IP φ n Psi c) (k : Fin n) (τ : ℝ) (hτ : 0 ≤ τ) :
    HasDerivWithinAt (fun s => IP (slice (galFam φ n c) s) (φ (k : ℕ)))
      (IP (dynLin α (galFam φ n (fun _ => c τ)) τ
        + dynRHS α (Psi (galFam φ n (fun _ => c τ)))
            (galFam φ n (fun _ => c τ)) τ) (φ (k : ℕ))) (Set.Ici 0) τ := by
  have h := isGalerkinCoeff_weak hpair hc k τ hτ
  have hslice : (fun s => IP (slice (galFam φ n c) s) (φ (k : ℕ)))
      = fun s => IP (galFun φ (c s)) (φ (k : ℕ)) := by
    funext s; simp
  rw [hslice]
  simpa [galRHS] using h

theorem galFun_eq_zero_of_coeff_eq_zero {φ : ℕ → Fn} {n : ℕ} {c : Fin n → ℝ}
    (hc : ∀ k : Fin n, c k = 0) : galFun φ c = 0 := by
  funext z θ
  simpa [galFun, hc] using (Finset.sum_eq_zero fun k _ => by simp [hc k])

/-- **The Galerkin pairing separates points of the span.**  If a Galerkin combination pairs trivially
with every test function, then it vanishes identically.  This is the algebraic half of the
fundamental lemma `Work.FTS.Galerkin.WeakDetermines` of the passage to the limit. -/
theorem galFun_eq_zero_of_pairing_eq_zero {IP : Fn → Fn → ℝ} {φ : ℕ → Fn}
    (hpair : IsIPOrthonormal IP φ) {n : ℕ} {c : Fin n → ℝ}
    (h : ∀ k : Fin n, IP (galFun φ c) (φ (k : ℕ)) = 0) : galFun φ c = 0 :=
  galFun_eq_zero_of_coeff_eq_zero fun k => by
    rw [← hpair.coeff n c k]
    exact h k

/-! ## The exact energy identity -/

/-- **The energy identity is exact** (audit step 4): for an `IP`-orthonormal Galerkin basis the
`IP`-energy of the Galerkin profile at fake time `τ` is the Euclidean norm squared of the
coefficient vector. -/
theorem galFam_energy {IP : Fn → Fn → ℝ} {φ : ℕ → Fn} (hpair : IsIPOrthonormal IP φ)
    (n : ℕ) (c : ℝ → Fin n → ℝ) (τ : ℝ) :
    IP (slice (galFam φ n c) τ) (slice (galFam φ n c) τ) = ∑ k : Fin n, (c τ k) ^ 2 := by
  simpa using hpair.self n (c τ)

/-- The fake-time derivative of a Galerkin predicate is the Galerkin combination of the projected
vector field. -/
theorem hasDerivWithinAt_galFun {α : ℝ} {IP : Fn → Fn → ℝ} {φ : ℕ → Fn} {n : ℕ} {Psi : Fam → Fam}
    {c : ℝ → Fin n → ℝ} (hc : IsGalerkinCoeff α IP φ n Psi c) (z θ τ : ℝ) (hτ : 0 ≤ τ) :
    HasDerivWithinAt (fun s => galFun φ (c s) z θ)
      (galFun φ (galField α IP φ n Psi τ (c τ)) z θ) (Set.Ici 0) τ := by
  have hcoord := (isGalerkinCoeff_iff_coord.mp hc)
  have h : HasDerivWithinAt (fun s => ∑ k : Fin n, c s k * φ (k : ℕ) z θ)
      (∑ k : Fin n, galField α IP φ n Psi τ (c τ) k * φ (k : ℕ) z θ) (Set.Ici 0) τ := by
    have h0 := HasDerivWithinAt.sum (u := (Finset.univ : Finset (Fin n)))
      (fun k _ => (hcoord k τ hτ).mul_const (φ (k : ℕ) z θ))
    have hfun : (∑ k : Fin n, fun y => c y k * φ (k : ℕ) z θ)
        = fun s => ∑ k : Fin n, c s k * φ (k : ℕ) z θ := by
      funext s
      simp [Finset.sum_apply]
    rw [hfun] at h0
    exact h0
  simpa [galFun] using h

/-- The energy of the Galerkin family, as a function of fake time, is the squared Euclidean norm of
the coefficient curve. -/
theorem energy_eq_sq_sum {IP : Fn → Fn → ℝ} {φ : ℕ → Fn} (hpair : IsIPOrthonormal IP φ)
    (n : ℕ) (c : ℝ → Fin n → ℝ) :
    (fun τ => IP (slice (galFam φ n c) τ) (slice (galFam φ n c) τ))
      = fun τ => ∑ k : Fin n, (c τ k) ^ 2 :=
  funext fun τ => galFam_energy hpair n c τ

/-- **The differentiated energy identity**: along a Galerkin solution, the fake-time derivative of
`∑ₖ cₖ²` is twice the Euclidean pairing of the coefficients with the projected vector field — i.e.
`d/dτ|gₙ|²_{IP} = 2 IP (ġₙ) gₙ`, with no error term. -/
theorem hasDerivWithinAt_galFam_energy {α : ℝ} {IP : Fn → Fn → ℝ} {φ : ℕ → Fn} {n : ℕ}
    {Psi : Fam → Fam} {c : ℝ → Fin n → ℝ} (hc : IsGalerkinCoeff α IP φ n Psi c) (τ : ℝ)
    (hτ : 0 ≤ τ) :
    HasDerivWithinAt (fun s => ∑ k : Fin n, (c s k) ^ 2)
      (2 * ∑ k : Fin n, c τ k * galField α IP φ n Psi τ (c τ) k) (Set.Ici 0) τ := by
  have hcoord := (isGalerkinCoeff_iff_coord.mp hc)
  have h : HasDerivWithinAt (fun s => ∑ k : Fin n, (c s k) ^ 2)
      (∑ k : Fin n, 2 * (c τ k) ^ (2 - 1) * galField α IP φ n Psi τ (c τ) k)
      (Set.Ici 0) τ := by
    have h0 := HasDerivWithinAt.sum (u := (Finset.univ : Finset (Fin n)))
      (fun k _ => (hcoord k τ hτ).pow 2)
    have hfun : (∑ k : Fin n, (fun s => c s k) ^ 2) = fun s => ∑ k : Fin n, (c s k) ^ 2 := by
      funext s
      simp [Finset.sum_apply, Pi.pow_apply]
    rw [hfun] at h0
    exact h0
  have h2 : (∑ k : Fin n, 2 * (c τ k) ^ (2 - 1) * galField α IP φ n Psi τ (c τ) k)
      = 2 * ∑ k : Fin n, c τ k * galField α IP φ n Psi τ (c τ) k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    norm_num
    ring
  rw [h2] at h
  exact h

/-- The pairing with the derivative, in the form used by the a-priori estimate:
`IP (ġₙ) gₙ = ∑ₖ cₖ ċₖ`. -/
theorem galFam_pairing {α : ℝ} {IP : Fn → Fn → ℝ} {φ : ℕ → Fn} (hpair : IsIPOrthonormal IP φ)
    (n : ℕ) (Psi : Fam → Fam) (c : ℝ → Fin n → ℝ) (τ : ℝ) :
    IP (fun z θ => ∑ k : Fin n, galField α IP φ n Psi τ (c τ) k * φ (k : ℕ) z θ)
        (slice (galFam φ n c) τ)
      = ∑ k : Fin n, c τ k * galField α IP φ n Psi τ (c τ) k := by
  have h1 : (fun z θ => ∑ k : Fin n, galField α IP φ n Psi τ (c τ) k * φ (k : ℕ) z θ)
      = galFun φ (galField α IP φ n Psi τ (c τ)) := rfl
  have h2 : slice (galFam φ n c) τ = galFun φ (c τ) := rfl
  rw [h1, h2, hpair n (galField α IP φ n Psi τ (c τ)) (c τ)]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

end Work.FTS.Galerkin
