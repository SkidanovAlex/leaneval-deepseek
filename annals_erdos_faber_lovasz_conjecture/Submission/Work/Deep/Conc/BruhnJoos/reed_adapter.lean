/-
# `Work.Deep.Conc.BruhnJoos.reed_adapter`

Bridge from the parallel subproject `Deep/Reed`'s weighted finite-probability layer
(`Work.Deep.Reed.FinProb`, product space `FinProb.pi`) to this development's uniform measure
on a finite type.

* `uniform_prob_eq`, `uniform_expect_eq`: the uniform `FinProb` on `Ω` computes the same
  probability / expectation as `Work.Deep.Conc.prob` / `Work.Deep.Conc.expect`.
* `pi_uniform_prob_eq`, `pi_uniform_expect_eq`: on the product `∀ i, π i`, `FinProb.pi` of the
  uniform factors is again the uniform measure, so the two layers agree there as well.
-/
import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Conc.Basic
import Submission.Work.Deep.Conc.Pi
import Submission.Work.Deep.Reed.Prob.hoeffding_bounded_differences

set_option autoImplicit false
open scoped BigOperators
open Finset

namespace Work.Deep.Conc.BruhnJoos

open Work.Deep.Conc

/-- The uniform `FinProb` computes the same probabilities as `Work.Deep.Conc.prob`. -/
theorem uniform_prob_eq {Ω : Type*} [Fintype Ω] [Nonempty Ω] (A : Set Ω) :
    (Work.Deep.Reed.FinProb.uniform Ω).prob A = Work.Deep.Conc.prob A := by
  classical
  rw [Work.Deep.Reed.FinProb.prob, Work.Deep.Conc.prob_eq_sum]
  simp only [Work.Deep.Reed.FinProb.uniform]
  have hterm : ∀ ω : Ω, (if ω ∈ A then ((Fintype.card Ω : ℝ))⁻¹ else 0)
      = Set.indicator A (fun _ => (1 : ℝ)) ω * ((Fintype.card Ω : ℝ))⁻¹ := by
    intro ω
    rw [Set.indicator_apply]
    by_cases h : ω ∈ A <;> simp [h]
  calc (∑ ω : Ω, (if ω ∈ A then ((Fintype.card Ω : ℝ))⁻¹ else 0))
      = ∑ ω : Ω, Set.indicator A (fun _ => (1 : ℝ)) ω * ((Fintype.card Ω : ℝ))⁻¹ :=
        Finset.sum_congr rfl fun ω _ => hterm ω
    _ = (∑ ω : Ω, Set.indicator A (fun _ => (1 : ℝ)) ω) * ((Fintype.card Ω : ℝ))⁻¹ := by
        rw [Finset.sum_mul]
    _ = (∑ ω : Ω, Set.indicator A (fun _ => (1 : ℝ)) ω) / (Fintype.card Ω : ℝ) := by
        rw [div_eq_mul_inv]

/-- The uniform `FinProb` computes the same expectations as `Work.Deep.Conc.expect`. -/
theorem uniform_expect_eq {Ω : Type*} [Fintype Ω] [Nonempty Ω] (X : Ω → ℝ) :
    (Work.Deep.Reed.FinProb.uniform Ω).exp X = Work.Deep.Conc.expect X := by
  rw [Work.Deep.Reed.FinProb.exp, Work.Deep.Conc.expect]
  simp only [Work.Deep.Reed.FinProb.uniform]
  rw [← Finset.mul_sum, div_eq_mul_inv, mul_comm]

/-- On the product space, `FinProb.pi` of the uniform factors is the uniform measure. -/
theorem pi_uniform_prob_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {π : ι → Type*}
    [∀ i, Fintype (π i)] (hne : ∀ i, Nonempty (π i)) (A : Set (∀ i, π i)) :
    (Work.Deep.Reed.FinProb.pi (fun i => Work.Deep.Reed.FinProb.uniform (π i))).prob A
      = Work.Deep.Conc.prob A := by
  classical
  haveI : ∀ i, Nonempty (π i) := hne
  rw [Work.Deep.Reed.FinProb.prob, Work.Deep.Conc.prob_eq_sum]
  simp only [Work.Deep.Reed.FinProb.pi_wt, Work.Deep.Reed.FinProb.uniform]
  have hterm : ∀ f : ∀ i, π i,
      (if f ∈ A then (∏ i, ((Fintype.card (π i) : ℝ))⁻¹) else 0)
        = Set.indicator A (fun _ => (1 : ℝ)) f * (∏ i, ((Fintype.card (π i) : ℝ))⁻¹) := by
    intro f
    rw [Set.indicator_apply]
    by_cases h : f ∈ A <;> simp [h]
  rw [Finset.sum_congr rfl (fun f _ => hterm f), ← Finset.sum_mul, div_eq_mul_inv,
    Finset.prod_inv_distrib, ← Nat.cast_prod, ← Fintype.card_pi]

/-- On the product space, `FinProb.pi` of the uniform factors is the uniform measure. -/
theorem pi_uniform_expect_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {π : ι → Type*}
    [∀ i, Fintype (π i)] (hne : ∀ i, Nonempty (π i)) (X : (∀ i, π i) → ℝ) :
    (Work.Deep.Reed.FinProb.pi (fun i => Work.Deep.Reed.FinProb.uniform (π i))).exp X
      = Work.Deep.Conc.expect X := by
  classical
  haveI : ∀ i, Nonempty (π i) := hne
  rw [Work.Deep.Reed.FinProb.exp, Work.Deep.Conc.expect]
  simp only [Work.Deep.Reed.FinProb.pi_wt, Work.Deep.Reed.FinProb.uniform]
  rw [← Finset.mul_sum, div_eq_mul_inv, Finset.prod_inv_distrib, ← Nat.cast_prod,
    ← Fintype.card_pi, mul_comm]

end Work.Deep.Conc.BruhnJoos
