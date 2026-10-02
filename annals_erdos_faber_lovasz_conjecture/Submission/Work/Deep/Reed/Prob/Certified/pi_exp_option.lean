import Mathlib.Data.Fintype.BigOperators
import Submission.Work.Deep.Reed.Prob.Product
import Submission.Work.Deep.Reed.Prob.Expectation

/-!
# Integrating out one coordinate of a product measure (`Option`-indexed)

For a product space indexed by `Option α` and a real-valued function `Φ` on the
full product, the expectation under the product measure `FinProb.pi μ` can be
computed by first integrating over the coordinates in `α` and then over the
extra coordinate `none`:

`E_μ[Φ] = ∑_{ω : Ω none} μ none .wt ω · E_{pi (fun a => μ (some a))}[x ↦ Φ (ω,x)]`.

This is the `Option`-indexed case of the tower rule / Fubini for product
measures, in the shape in which the induction steps of the concentration
arguments use it.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Deep.Reed.Prob.Certified

/-- **Fubini/tower rule for a product over `Option α`.**  The expectation of a
function of the whole product equals the average over the `none`-coordinate of
the conditional expectation over the remaining coordinates. -/
theorem pi_exp_option {α : Type*} [Fintype α] [DecidableEq α] {Ω : Option α → Type*}
    [∀ o, Fintype (Ω o)] (μ : ∀ o, Work.Deep.Reed.FinProb (Ω o)) (Φ : (∀ o, Ω o) → ℝ) :
    (Work.Deep.Reed.FinProb.pi μ).exp Φ
      = ∑ ω : Ω none, (μ none).wt ω *
          (Work.Deep.Reed.FinProb.pi (fun a => μ (some a))).exp
            (fun x : ∀ a, Ω (some a) => Φ (fun o => o.casesOn ω x)) := by
  classical
  -- The product over `Option α` is (via the splitting `none` / `some`) the
  -- product of `Ω none` and the product over `α`.
  have hbij : Function.Bijective (fun f : ∀ o, Ω o => (f none, fun a => f (some a))) := by
    refine ⟨?_, ?_⟩
    · intro f g h
      have h1 : f none = g none := congrArg Prod.fst h
      have h2 : (fun a => f (some a)) = (fun a => g (some a)) := congrArg Prod.snd h
      funext o
      cases o with
      | none => exact h1
      | some a => exact congrFun h2 a
    · rintro ⟨ω, x⟩
      exact ⟨fun o => o.casesOn ω x, rfl⟩
  -- Pointwise identification of the two summands under that splitting.
  have hpt : ∀ f : ∀ o, Ω o,
      (∏ o : Option α, (μ o).wt (f o)) * Φ f
        = ((μ none).wt (f none) * ∏ a : α, (μ (some a)).wt (f (some a)))
            * Φ (fun o => o.casesOn (f none) (fun a => f (some a))) := by
    intro f
    have h1 : ∏ o : Option α, (μ o).wt (f o)
        = (μ none).wt (f none) * ∏ a : α, (μ (some a)).wt (f (some a)) :=
      Fintype.prod_option (fun o => (μ o).wt (f o))
    have h2 : (fun o => o.casesOn (f none) (fun a => f (some a))) = f := by
      funext o
      cases o <;> rfl
    rw [h1, h2]
  -- Reindex the sum by the bijection, split the product type, factor out the
  -- `none`-weight, and recognise the inner sum as an expectation.
  calc (Work.Deep.Reed.FinProb.pi μ).exp Φ
      = ∑ f : ∀ o, Ω o, (∏ o : Option α, (μ o).wt (f o)) * Φ f := rfl
    _ = ∑ p : (Ω none) × (∀ a, Ω (some a)),
        ((μ none).wt p.1 * ∏ a : α, (μ (some a)).wt (p.2 a))
          * Φ (fun o => o.casesOn p.1 p.2) := by
          exact Fintype.sum_bijective (fun f : ∀ o, Ω o => (f none, fun a => f (some a))) hbij
            (fun f => (∏ o : Option α, (μ o).wt (f o)) * Φ f)
            (fun p => ((μ none).wt p.1 * ∏ a : α, (μ (some a)).wt (p.2 a))
              * Φ (fun o => o.casesOn p.1 p.2)) hpt
    _ = ∑ ω : Ω none, ∑ x : ∀ a, Ω (some a),
        ((μ none).wt ω * ∏ a : α, (μ (some a)).wt (x a))
          * Φ (fun o => o.casesOn ω x) := by
          simp only [Fintype.sum_prod_type]
    _ = ∑ ω : Ω none, (μ none).wt ω * (∑ x : ∀ a, Ω (some a),
        (∏ a : α, (μ (some a)).wt (x a)) * Φ (fun o => o.casesOn ω x)) := by
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl fun ω _ =>
            Finset.sum_congr rfl fun x _ => by ring
    _ = ∑ ω : Ω none, (μ none).wt ω *
        (Work.Deep.Reed.FinProb.pi (fun a => μ (some a))).exp
          (fun x : ∀ a, Ω (some a) => Φ (fun o => o.casesOn ω x)) := rfl

end Work.Deep.Reed.Prob.Certified
