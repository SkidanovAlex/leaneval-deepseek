import Mathlib.Data.Fintype.BigOperators
import Submission.Work.Deep.Reed.Prob.Product

/-!
# Disintegration of a product measure in the coordinate `none`

For a family of finite probability spaces `μ o` indexed by `Option α`, the
product measure on `∀ o, Ω o` disintegrates over the value of the coordinate
`none`:  summing the weights over the fibre over a fixed value `ω` of that
coordinate gives the product measure of the remaining (i.e. `some a`) family,
applied to the corresponding section of the event.

This is the "probability" companion of `pi_exp_option`, and is the shape in
which the product measure over `Option α` is used in the certification layer
(a quantity defined on the full product is decomposed into the `none`
coordinate and the remaining coordinates).
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Deep.Reed.Prob.Certified

theorem pi_prob_option {α : Type*} [Fintype α] [DecidableEq α] {Ω : Option α → Type*}
    [∀ o, Fintype (Ω o)] (μ : ∀ o, Work.Deep.Reed.FinProb (Ω o)) (A : Set (∀ o, Ω o)) :
    (Work.Deep.Reed.FinProb.pi μ).prob A
      = ∑ ω : Ω none, (μ none).wt ω *
          (Work.Deep.Reed.FinProb.pi (fun a => μ (some a))).prob
            {x : ∀ a, Ω (some a) | (fun o => o.casesOn ω x) ∈ A} := by
  classical
  -- reassembling a function out of its `none`- and `some`-parts
  have hfun : ∀ f : ∀ o, Ω o,
      (fun o => o.casesOn (f none) (fun a => f (some a))) = f :=
    fun f => funext fun o => by cases o <;> rfl
  -- the weight of the product measure splits at the coordinate `none`
  have hwtsplit : ∀ f : ∀ o, Ω o,
      ∏ o, (μ o).wt (f o) = (μ none).wt (f none) * ∏ a, (μ (some a)).wt (f (some a)) :=
    fun f => Fintype.prod_option (fun o => (μ o).wt (f o))
  -- rewriting the probability at a fixed `none`-value:
  -- independent of the value of the `none`-coordinate (the extra factor is
  -- exactly the missing weight `(μ none).wt (f none)`)
  have hpt : ∀ f : ∀ o, Ω o,
      (if f ∈ A then ∏ o, (μ o).wt (f o) else 0)
      = (if (fun o => o.casesOn (f none) (fun a => f (some a))) ∈ A
          then (μ none).wt (f none) * ∏ a, (μ (some a)).wt (f (some a)) else 0) := by
    intro f
    by_cases hf : f ∈ A
    · rw [if_pos hf, if_pos (by rw [hfun f]; exact hf), hwtsplit f]
    · rw [if_neg hf, if_neg (by rw [hfun f]; exact hf)]
  calc (Work.Deep.Reed.FinProb.pi μ).prob A
      = ∑ f : ∀ o, Ω o, (if f ∈ A then ∏ o, (μ o).wt (f o) else 0) := by
        simp only [FinProb.prob, FinProb.pi_wt]
      -- reindex the sum along the bijection `f ↦ (f none, f ∘ some)`
    _ = ∑ f : ∀ o, Ω o, (if (fun o => o.casesOn (f none) (fun a => f (some a))) ∈ A
          then (μ none).wt (f none) * ∏ a, (μ (some a)).wt (f (some a)) else 0) :=
        Finset.sum_congr rfl fun f _ => hpt f
    _ = ∑ p : Ω none × ∀ a, Ω (some a),
          (if (fun o => o.casesOn p.1 p.2) ∈ A
            then (μ none).wt p.1 * ∏ a, (μ (some a)).wt (p.2 a) else 0) :=
        Equiv.sum_comp (Equiv.piOptionEquivProd (β := Ω))
          (fun p : Ω none × ∀ a, Ω (some a) =>
            if (fun o => o.casesOn p.1 p.2) ∈ A
              then (μ none).wt p.1 * ∏ a, (μ (some a)).wt (p.2 a) else 0)
      -- split the double sum and pull out the weight of the `none`-coordinate
    _ = ∑ ω : Ω none, (μ none).wt ω *
          (Work.Deep.Reed.FinProb.pi (fun a => μ (some a))).prob
            {x : ∀ a, Ω (some a) | (fun o => o.casesOn ω x) ∈ A} := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun ω _ => ?_
        simp only [FinProb.prob, FinProb.pi_wt]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [mul_ite, mul_zero, Set.mem_ofPred_eq]

end Work.Deep.Reed.Prob.Certified
