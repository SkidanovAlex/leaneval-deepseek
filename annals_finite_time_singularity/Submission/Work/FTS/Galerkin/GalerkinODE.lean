/-
# The GALERKIN area: the Galerkin system has global solutions (audit §4 N6, step 3)

This module reduces the existence of the Galerkin families to the abstract global-existence theorem
for ODEs on a ball (`Work.FTS.Galerkin.exists_global_solution_of_bound`, in
`Submission/Work/FTS/Galerkin/exists_global_solution_of_bound.lean`), via the a-priori bundle
`DynInputs`:

* `GlobalODEExistence` is that abstract theorem, packaged as a `Prop` so that this module is
  independent of how it is proved;
* `galerkin_coeff_exists` turns the bundle's fields (`hField_lip`, `hField_bound`, `hField_cont`,
  `hInit`, `hCoeffBound`) plus the abstract theorem into the existence of a global solution of the
  projected Galerkin ODE `ċ = galField(τ,c)` in the a-priori ball of radius `R`.

The plugging of the proved ODE theorem into `GlobalODEExistence` is `Work.FTS.Galerkin.globalODEExistence`
(`Submission/Work/FTS/Galerkin/ODEApply.lean`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.Galerkin.Projection
import Submission.Work.FTS.Galerkin.Hilbert.galFun_adm
import Submission.Work.FTS.GalerkinFix.Defs

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

/-- The sup-norm ball membership from a bound on the squared Euclidean norm of the coefficients. -/
theorem mem_closedBall_of_sum_sq_le {n : ℕ} {c : Fin n → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (h : ∑ k : Fin n, (c k) ^ 2 ≤ R ^ 2) : c ∈ Metric.closedBall 0 R := by
  rw [Metric.mem_closedBall, dist_pi_le_iff hR]
  intro k
  have h1 : (c k) ^ 2 ≤ ∑ j : Fin n, (c j) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ k)
  have h2 : (c k) ^ 2 ≤ R ^ 2 := le_trans h1 h
  have h3 : |c k| ≤ R := by
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq hR]
    exact Real.sqrt_le_sqrt h2
  simpa using h3

/-- The abstract global-existence theorem for an ODE with an a-priori (trajectory) bound: a vector
field which is Lipschitz, bounded and time-continuous on the ball of radius `R'` admits a solution
on all of `[0,∞)` starting from any `x₀` in the ball of radius `R < R'`, provided every solution
stays in the ball of radius `R`.  This is the interface through which the ODE chapter is used. -/
def GlobalODEExistence : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E → E) (x₀ : E) (R R' L K : ℝ) (hR : 0 < R) (hR' : R < R') (hL : 0 < L)
    (hK : 0 ≤ K),
    x₀ ∈ Metric.closedBall (0 : E) R →
    (∀ t : ℝ, 0 ≤ t → LipschitzOnWith ⟨K, hK⟩ (f t) (Metric.closedBall (0 : E) R')) →
    (∀ (t : ℝ), 0 ≤ t → ∀ x ∈ Metric.closedBall (0 : E) R', ‖f t x‖ ≤ L) →
    (∀ x ∈ Metric.closedBall (0 : E) R', ContinuousOn (fun t : ℝ => f t x) (Set.Ici 0)) →
    (∀ (T : ℝ), 0 ≤ T → ∀ α : ℝ → E, IsSolOn f x₀ T α →
      ∀ t ∈ Set.Icc 0 T, α t ∈ Metric.closedBall (0 : E) R) →
    ∃ α : ℝ → E, IsSolGlob f x₀ α ∧ ∀ t, 0 ≤ t → α t ∈ Metric.closedBall (0 : E) R

/-- **The Galerkin approximations exist globally** (audit steps 3–4): for every truncation `n` the
projected ODE admits a solution on all of `[0,∞)` with the projected datum as initial value, and the
coefficient curve stays in the a-priori ball of radius `R` (this last fact is the bundle's a-priori
estimate `hCoeffBound`).  The Lipschitz and bound constants `K n`, `L n` of the projected field
depend on the truncation (interface fix of 2026-10-03: they cannot be uniform in `n`, because
`𝓛_Γ^T` is unbounded on `ℋ⁴`). -/
theorem galerkin_coeff_exists (hODE : GlobalODEExistence) {Law : Fn → Fn → Prop} {α C₀ : ℝ}
    {g₀ : Fn} (hin : DynInputs Law α g₀ C₀) (n : ℕ) :
    ∃ c : ℝ → Fin n → ℝ, c 0 = coeffOf (hin.IP α) g₀ hin.φ n ∧
      IsGalerkinCoeff α (hin.IP α) hin.φ n hin.Psi c ∧
      (∀ τ, 0 ≤ τ → ∑ k : Fin n, (c τ k) ^ 2 ≤ hin.R ^ 2) ∧
      ∀ τ, 0 ≤ τ → c τ ∈ Metric.closedBall 0 hin.R := by
  have hRlt : hin.R < 2 * hin.R := by linarith [hin.hR]
  have hx₀ : coeffOf (hin.IP α) g₀ hin.φ n ∈ Metric.closedBall (0 : Fin n → ℝ) hin.R :=
    mem_closedBall_of_sum_sq_le hin.hR.le (hin.hInit n)
  obtain ⟨c, hc, hball⟩ := hODE (Fin n → ℝ) (f := galField α (hin.IP α) hin.φ n hin.Psi)
    (x₀ := coeffOf (hin.IP α) g₀ hin.φ n) (R := hin.R) (R' := 2 * hin.R)
    (L := hin.L n) (K := hin.K n)
    hin.hR hRlt (hin.hL n) (hin.hK n) hx₀
    (fun t ht => hin.hField_lip n t ht)
    (fun t ht x hx => hin.hField_bound n t x ht hx)
    (fun x hx => hin.hField_cont n x hx)
    (fun T hT α' hα' τ hτ => mem_closedBall_of_sum_sq_le hin.hR.le (hin.hCoeffBound n T hT α' hα' τ hτ))
  refine ⟨c, hc.1, hc.2, ?_, hball⟩
  intro τ hτ
  exact hin.hCoeffBound n τ hτ c (hc.isSolOn τ) τ ⟨hτ, le_rfl⟩

/-! ## From the `ℋ⁴`-bound on the Galerkin profiles to the coefficient ball

The bundle's a-priori field `hCoeffBound` is a statement about the *coefficients*; the paper's
a-priori estimate is a statement about the `ℋ⁴`-norm of the Galerkin *profile*.  The two are related
by the exact energy identity `IP (∑ cₖφₖ) (∑ cₖφₖ) = ∑ cₖ²` and the upper bound
`IP f f ≤ C|f|²_{ℋ⁴}` of the admissible inner product: this is how N5 is expected to discharge
`hCoeffBound`. -/

/-- **The coefficient ball from the profile bound**: if the Galerkin profiles satisfy
`|gₙ(τ)|_{ℋ⁴} ≤ C₀α²` and the Galerkin combinations are admissible, then the coefficient vectors lie
in the sup-norm ball of radius `R`, provided `R² ≥ C(C₀α²)²` where `C` is the upper bound of `IP`
against the `ℋ⁴`-norm. -/
theorem coeffBall_of_profileBound {α : ℝ} {IP : Fn → Fn → ℝ} {φ : ℕ → Fn}
    (hpair : IsIPOrthonormal IP φ) {C C₀ R : ℝ} (hR : 0 ≤ R) (hCnn : 0 ≤ C)
    (hBnn : 0 ≤ C₀ * α ^ 2)
    (hC : ∀ f : Fn, Coercivity.HkAdm α 4 f → IP f f ≤ C * Spaces.HkSq α 4 f)
    {n : ℕ} {c : ℝ → Fin n → ℝ}
    (hadm : ∀ τ, Coercivity.HkAdm α 4 (galFun φ (c τ)))
    (hb : ∀ τ, Spaces.HkNorm α 4 (galFun φ (c τ)) ≤ C₀ * α ^ 2)
    (hR2 : C * (C₀ * α ^ 2) ^ 2 ≤ R ^ 2) :
    ∀ τ, c τ ∈ Metric.closedBall 0 R := by
  intro τ
  refine mem_closedBall_of_sum_sq_le hR ?_
  have h1 := hpair.sq_sum_le (hC := hC) (c τ) (hadm τ)
  have h2 : Spaces.HkNorm α 4 (galFun φ (c τ)) ^ 2 ≤ (C₀ * α ^ 2) ^ 2 :=
    sq_le_sq' (by linarith [Spaces.HkNorm_nonneg α 4 (galFun φ (c τ)), hBnn]) (hb τ)
  have h3 : C * Spaces.HkNorm α 4 (galFun φ (c τ)) ^ 2 ≤ C * (C₀ * α ^ 2) ^ 2 :=
    mul_le_mul_of_nonneg_left h2 hCnn
  linarith

/-- **The paper's cubic barrier applied to the coefficient energy** (tex 1569–1572).  The scalar
step of the a-priori estimate is `Work.Construction.le_of_deriv_le_of_cubic`, applied to the energy
`e(τ) = ∑ₖ cₖ(τ)²` (which is `IP gₙ(τ) gₙ(τ)` by `galFam_energy`, with fake-time derivative
`2 ∑ₖ cₖċₖ` by `hasDerivWithinAt_galFam_energy`).  Once the barrier is available, the coefficient
ball membership is the following conversion: -/
theorem coeffBall_of_energyBound {n : ℕ} {c : Fin n → ℝ} {y1 : ℝ} (hy1 : 0 ≤ y1)
    (he : (∑ k : Fin n, (c k) ^ 2) ≤ y1) : c ∈ Metric.closedBall 0 (Real.sqrt y1) := by
  refine mem_closedBall_of_sum_sq_le (Real.sqrt_nonneg y1) ?_
  rw [Real.sq_sqrt hy1]
  exact he

/-- **The bundle's a-priori field `hCoeffBound` from the paper's `ℋ⁴`-bound on the Galerkin
profiles.**  With the test functions admissible (`hφ`, i.e. the bundle's `hφ_adm`), the admissibility
of the Galerkin combinations is automatic (`Work.FTS.Galerkin.Hilbert.galFun_adm`), so a uniform
`ℋ⁴`-bound `|gₙ(τ)|_{ℋ⁴} ≤ C₀α²` on the Galerkin profiles — the conclusion of the paper's §Modulation
estimate — yields the coefficient ball of radius `R`.  This is the bridge by which N5 is expected to
discharge `DynInputs.hCoeffBound`. -/
theorem coeffBall_of_profileBound_of_adm {α : ℝ} {IP : Fn → Fn → ℝ} {φ : ℕ → Fn}
    (hpair : IsIPOrthonormal IP φ) {C C₀ R : ℝ} (hR : 0 ≤ R) (hCnn : 0 ≤ C)
    (hBnn : 0 ≤ C₀ * α ^ 2)
    (hC : ∀ f : Fn, Coercivity.HkAdm α 4 f → IP f f ≤ C * Spaces.HkSq α 4 f)
    (hφ : ∀ k : ℕ, Coercivity.HkAdm α 4 (φ k))
    {n : ℕ} {c : ℝ → Fin n → ℝ}
    (hb : ∀ τ, Spaces.HkNorm α 4 (galFun φ (c τ)) ≤ C₀ * α ^ 2)
    (hR2 : C * (C₀ * α ^ 2) ^ 2 ≤ R ^ 2) :
    ∀ τ, c τ ∈ Metric.closedBall 0 R :=
  coeffBall_of_profileBound hpair hR hCnn hBnn hC
    (fun τ => Hilbert.galFun_adm hφ n (c τ)) hb hR2

/-- **The `ℋ⁴`-bound of a Galerkin profile from the energy form of the a-priori estimate.**  By the
exact energy identity (`IsIPOrthonormal.self`) and the dominance of the inner product
(`IsH4Inner.dominates`), the `ℋ⁴`-norm of a Galerkin combination is bounded by the `ℓ²`-norm of its
coefficients: `∑ₖ cₖ² ≤ R²` gives `|∑ₖ cₖφₖ|_{ℋ⁴} ≤ R`.  This is the first half of the derivation of
the bundle's field `hProfileBdd` from the a-priori bound `hCoeffBound`. -/
theorem HkNorm_galFun_le {α : ℝ} {IP : Fn → Fn → ℝ} {φ : ℕ → Fn}
    (hIP : IsH4Inner α IP) (hpair : IsIPOrthonormal IP φ) {R : ℝ} {n : ℕ} {c : Fin n → ℝ}
    (hadm : Coercivity.HkAdm α 4 (galFun φ c))
    (h : ∑ k : Fin n, (c k) ^ 2 ≤ R ^ 2) (hR : 0 ≤ R) :
    Spaces.HkNorm α 4 (galFun φ c) ≤ R := by
  have h1 : Spaces.HkSq α 4 (galFun φ c) ≤ IP (galFun φ c) (galFun φ c) := hIP.dominates hadm
  have h2 : IP (galFun φ c) (galFun φ c) = ∑ k : Fin n, (c k) ^ 2 := hpair.self n c
  have h3 : Spaces.HkSq α 4 (galFun φ c) ≤ R ^ 2 := by rw [h2] at h1; linarith
  have h4 : Spaces.HkNorm α 4 (galFun φ c) = Real.sqrt (Spaces.HkSq α 4 (galFun φ c)) := rfl
  rw [h4]
  calc Real.sqrt (Spaces.HkSq α 4 (galFun φ c)) ≤ Real.sqrt (R ^ 2) := Real.sqrt_le_sqrt h3
    _ = R := Real.sqrt_sq hR

end Work.FTS.Galerkin
