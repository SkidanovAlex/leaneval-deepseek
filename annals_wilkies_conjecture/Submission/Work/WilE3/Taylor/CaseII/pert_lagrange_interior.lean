import Mathlib
import Submission.Work.WilE3.Taylor.Grad.lagrangeOfInteriorMin
import Submission.Work.WilE3.Taylor.Polar.Lagrange
import Submission.Work.WilE3.Taylor.CaseII.grad_sqGrad_mul_exp
import Submission.Work.WilE3.Taylor.CaseII.hasStrictFDerivAt_sqGrad_mul_exp

/-!
  annals_wilkies_conjecture, AREA E3 / Taylor / CaseII: **the Lagrange condition at an *interior*
  minimum of the perturbed squared gradient norm** (the node feeding the solution count of the
  perturbed polar system in the CaseII branch of `cbc/wilkies_e3_caseII.md`).

  Write `G z = ∑ l (∂ₗ Φ z)²` for the squared gradient norm and
  `H z = G z · exp (∑ i, v i · (z i - y i))` for its perturbation by the exponential weight of the
  parameter `v`.  The hypothesis `hloc` says that `u` is a local minimiser of `H` on the level set
  `{z | Φ z = Φ u}` (the "interior" case, where the constraint `Φ` is regular at `u`), and the
  conclusion is the Lagrange multiplier condition:

      `∇G u + G u · v  =  c · ∇Φ u`.

  The proof is the standard one.  `∇H u = exp(∑ i, v i (u i - y i)) · (∇G u + G u · v)`
  (`grad_sqGrad_mul_exp`), and `H` is strictly differentiable at `u`
  (`hasStrictFDerivAt_sqGrad_mul_exp`), so applying the Lagrange multiplier theorem
  `Work.WilE3.Taylor.grad_parallel_of_isLocalExtrOn` to the objective `H` on the level set of `Φ`
  (whose gradient does not vanish at `u`, `hgu`) gives `∇H u = c' · ∇Φ u`.  Dividing by the strictly
  positive factor `exp (∑ i, v i (u i - y i))` yields the claim with `c = c' / exp (∑ i, v i (u i - y i))`.
-/

namespace Work.WilE3.Taylor.CaseII

open Classical Topology Filter

set_option autoImplicit false

theorem pert_lagrange_interior {k : ℕ} {Φ : (Fin k → ℝ) → ℝ} {v y u : Fin k → ℝ}
    (hΦ : ∀ z, AnalyticAt ℝ Φ z) (hgu : Work.WilE3.Taylor.grad Φ u ≠ 0)
    (hloc : ∀ᶠ z in nhds u, Φ z = Φ u →
      (∑ l, (Work.WilE3.Taylor.grad Φ u l) ^ 2) * Real.exp (∑ i, v i * (u i - y i))
        ≤ (∑ l, (Work.WilE3.Taylor.grad Φ z l) ^ 2) * Real.exp (∑ i, v i * (z i - y i))) :
    ∃ c : ℝ, ∀ i : Fin k,
      Work.WilE3.Taylor.grad (fun z => ∑ l, (Work.WilE3.Taylor.grad Φ z l) ^ 2) u i
        + (∑ l, (Work.WilE3.Taylor.grad Φ u l) ^ 2) * v i
        = c * Work.WilE3.Taylor.grad Φ u i := by
  -- Step 1: `u` locally minimises the perturbed squared gradient norm `H` on the level set of `Φ`.
  -- Step 2: Lagrange's multiplier theorem then gives `∇H u ∥ ∇Φ u`.
  obtain ⟨c', hc'⟩ : ∃ c' : ℝ,
      Work.WilE3.Taylor.grad
          (fun z => (∑ l, (Work.WilE3.Taylor.grad Φ z l) ^ 2) * Real.exp (∑ i, v i * (z i - y i))) u
        = c' • Work.WilE3.Taylor.grad Φ u := by
    refine Work.WilE3.Taylor.grad_parallel_of_isLocalExtrOn ?_
      (hasStrictFDerivAt_sqGrad_mul_exp (v := v) (y := y) (u := u) hΦ) ?_ hgu
    · refine Or.inl ?_
      show ∀ᶠ z in 𝓝[{z : Fin k → ℝ | Φ z = Φ u}] u,
        (∑ l, (Work.WilE3.Taylor.grad Φ u l) ^ 2) * Real.exp (∑ i, v i * (u i - y i))
          ≤ (∑ l, (Work.WilE3.Taylor.grad Φ z l) ^ 2) * Real.exp (∑ i, v i * (z i - y i))
      rw [eventually_nhdsWithin_iff]
      filter_upwards [hloc] with z hz hmem
      exact hz hmem
    · exact (hΦ u).contDiffAt.hasStrictFDerivAt (n := 1) (by norm_num)
  -- Step 3: evaluate the product rule `∇(G · exp) u = exp · (∇G u + G u · v)` and divide by `exp`.
  refine ⟨c' / Real.exp (∑ i, v i * (u i - y i)), fun i => ?_⟩
  have hB := grad_sqGrad_mul_exp (v := v) (y := y) (u := u) hΦ i
  have h1 : Work.WilE3.Taylor.grad
      (fun z => (∑ l, (Work.WilE3.Taylor.grad Φ z l) ^ 2) * Real.exp (∑ i, v i * (z i - y i))) u i
      = c' * Work.WilE3.Taylor.grad Φ u i := by
    have := congrFun hc' i
    simpa [Pi.smul_apply, smul_eq_mul] using this
  rw [hB] at h1
  rw [div_mul_eq_mul_div, eq_div_iff (Real.exp_ne_zero _)]
  linear_combination h1

end Work.WilE3.Taylor.CaseII
