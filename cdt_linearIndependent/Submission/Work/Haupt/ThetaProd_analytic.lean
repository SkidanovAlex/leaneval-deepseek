import Mathlib
import Submission.Work.Haupt.thetaCore
import Submission.Work.Haupt.jtpLHS_differentiableAt

/-!
# Holomorphy of the theta product `ThetaProd x`

For `‖x‖ < 1` the two-sided infinite product
`ThetaProd x z = ∏' n, (1 + x ^ (2n+1) * z) * (1 + x ^ (2n+1) / z)`
is holomorphic on `ℂ \ {0}`.

The proof splits the product into the two convergent factors
* `∏' n, (1 + x ^ (2n+1) * z)` (entire), and
* `∏' n, (1 + x ^ (2n+1) / z)` (holomorphic on `{0}ᶜ`),
each of which is a locally uniform limit of holomorphic partial products
(`tprod_one_add_mul_differentiable`, `tprod_one_add_div_differentiableOn`),
and then recombines them with `Multipliable.tprod_mul`.
-/

namespace Work.Haupt

open Filter
open scoped BigOperators

noncomputable section

/-- `∑_n ‖x ^ (2n+1)‖` converges for `‖x‖ < 1`. -/
lemma summable_norm_x_pow_odd (x : ℂ) (hx : ‖x‖ < 1) :
    Summable (fun n : ℕ => ‖x ^ (2 * n + 1)‖) := by
  have hx2 : ‖x‖ ^ 2 < 1 := by nlinarith [norm_nonneg x]
  have h : Summable (fun n : ℕ => ‖x‖ * (‖x‖ ^ 2) ^ n) :=
    (summable_geometric_of_lt_one (sq_nonneg ‖x‖) hx2).mul_left ‖x‖
  refine h.congr fun n => ?_
  rw [norm_pow, ← pow_mul, ← pow_succ']

/-- `z ↦ ∏' n, (1 + x^(2n+1) * z)` is holomorphic on `{0}ᶜ` (indeed entire). -/
lemma thetaProd_factorA_differentiableOn (x : ℂ) (hx : ‖x‖ < 1) :
    DifferentiableOn ℂ (fun z : ℂ => ∏' n : ℕ, (1 + x ^ (2 * n + 1) * z))
      {z : ℂ | z ≠ 0} :=
  (tprod_one_add_mul_differentiable (fun n : ℕ => x ^ (2 * n + 1))
    (summable_norm_x_pow_odd x hx)).differentiableOn

/-- `z ↦ ∏' n, (1 + x^(2n+1) / z)` is holomorphic on `{0}ᶜ`. -/
lemma thetaProd_factorB_differentiableOn (x : ℂ) (hx : ‖x‖ < 1) :
    DifferentiableOn ℂ (fun z : ℂ => ∏' n : ℕ, (1 + x ^ (2 * n + 1) / z))
      {z : ℂ | z ≠ 0} :=
  tprod_one_add_div_differentiableOn (fun n : ℕ => x ^ (2 * n + 1))
    (summable_norm_x_pow_odd x hx)

/-- On `{0}ᶜ` the product `ThetaProd x` is the product of the two factors above. -/
lemma thetaProd_eq_mul_factors (x : ℂ) (hx : ‖x‖ < 1) :
    Set.EqOn (ThetaProd x)
      (fun z : ℂ => (∏' n : ℕ, (1 + x ^ (2 * n + 1) * z)) *
        (∏' n : ℕ, (1 + x ^ (2 * n + 1) / z))) {z : ℂ | z ≠ 0} := by
  intro z hz
  have hgeom := summable_norm_x_pow_odd x hx
  have hm1 : Multipliable (fun n : ℕ => (1 + x ^ (2 * n + 1) * z : ℂ)) := by
    refine multipliable_one_add_of_summable ((hgeom.mul_left ‖z‖).congr fun n => ?_)
    rw [norm_mul, mul_comm]
  have hm2 : Multipliable (fun n : ℕ => (1 + x ^ (2 * n + 1) / z : ℂ)) := by
    refine multipliable_one_add_of_summable ((hgeom.div_const ‖z‖).congr fun n => ?_)
    rw [norm_div]
  show ThetaProd x z = _
  rw [ThetaProd]
  exact hm1.tprod_mul hm2

theorem ThetaProd_analytic (x : ℂ) (hx : ‖x‖ < 1) :
    DifferentiableOn ℂ (ThetaProd x) {z : ℂ | z ≠ 0} := by
  have hprod : DifferentiableOn ℂ
      (fun z : ℂ => (∏' n : ℕ, (1 + x ^ (2 * n + 1) * z)) *
        (∏' n : ℕ, (1 + x ^ (2 * n + 1) / z))) {z : ℂ | z ≠ 0} :=
    (thetaProd_factorA_differentiableOn x hx).mul (thetaProd_factorB_differentiableOn x hx)
  exact hprod.congr fun z hz => thetaProd_eq_mul_factors x hx hz

end

end Work.Haupt
