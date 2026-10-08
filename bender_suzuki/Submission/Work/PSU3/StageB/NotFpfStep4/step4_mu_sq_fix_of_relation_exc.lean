import Mathlib
import Submission.Work.PSU3.StageB.NotFpfStep4.step4_mu_sq_fix_of_relation
import Submission.Work.PSU3.StageB.NotFpfStep4.odd_iterate_fixes_all_but_two

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB.NotFpfStep4

/-- **Exception-tolerant form of `step4_mu_sq_fix_of_relation`.**

The source's relation (10) is produced by the assembly of §4 only for `X` in the fixed field
`F` of `σE` *away from two values*: the excluded class of the source's proviso on relation (4)
and the value where the identity is trivial.  Concretely, `(c + X^μ) X = (c + X^{μ²}) X^μ` is
available for every `σE`-fixed `X` with `X ≠ x₀` and `X + 1 ≠ x₀`, i.e. for every fixed point
outside the two exceptional values `x₀` and `x₀ + 1`.

This lemma shows that the conclusion `μ (μ X) = X` for all `σE`-fixed `X` still follows.
For fixed `X` off the two exceptions the instances of the relation at `X` and at `X + 1` add up
to `X + μ (μ X) = 0` in characteristic two (this is `step4_mu_sq_fix_of_relation`).  Thus the
permutation `τ = μ²` of `F` fixes every point except possibly `x₀` and `x₀ + 1`.  Since
`orderOf τ` divides the odd number `orderOf μ`, `τ` has odd order, and a permutation of odd order
moving at most two points is the identity: a nontrivial odd-order permutation moves at least three
points, or equivalently its only conceivable non-identity restriction to a two-element set would
be a transposition, of order `2`.  A ring automorphism fixing `x₀` also fixes `x₀ + 1`, so all of
`F` is fixed and the conclusion follows. -/
theorem step4_mu_sq_fix_of_relation_exc {n : ℕ} (hn : 2 ≤ n)
    (μ : Work.PSU3.E n ≃+* Work.PSU3.E n) (c x₀ : Work.PSU3.E n)
    (hodd : Odd (orderOf μ))
    (hμF : ∀ x : Work.PSU3.E n, Work.PSU3.σE x = x → Work.PSU3.σE (μ x) = μ x)
    (hrel : ∀ X : Work.PSU3.E n, Work.PSU3.σE X = X → X ≠ x₀ → X + 1 ≠ x₀ →
      (c + μ X) * X = (c + μ (μ X)) * μ X) :
    ∀ X : Work.PSU3.E n, Work.PSU3.σE X = X → μ (μ X) = X := by
  have _ : 1 ≤ n := by omega
  -- Adding the relation at `X` and at `X + 1` (both instances available off the two exceptions)
  -- yields `X + μ (μ X) = 0`, i.e. `μ (μ X) = X`, in characteristic two.
  have pair : ∀ X : Work.PSU3.E n, Work.PSU3.σE X = X → X ≠ x₀ → X + 1 ≠ x₀ →
      μ (μ X) = X := by
    intro X hX h1 h2
    have hX1 : Work.PSU3.σE (X + 1) = X + 1 := by rw [map_add, map_one, hX]
    have e1 : (c + μ X) * X = (c + μ (μ X)) * μ X := hrel X hX h1 h2
    have e2 : (c + μ (X + 1)) * (X + 1) = (c + μ (μ (X + 1))) * μ (X + 1) :=
      hrel (X + 1) hX1 h2 (by
        have hxx : X + 1 + 1 = X := by
          have h2' : (2 : Work.PSU3.E n) = 0 := CharTwo.two_eq_zero
          linear_combination h2'
        rw [hxx]; exact h1)
    rw [map_add, map_one, map_add, map_one] at e2
    have hkey : (c + (μ X + 1)) * (X + 1) + (c + μ X) * X
        = (c + (μ (μ X) + 1)) * (μ X + 1) + (c + μ (μ X)) * μ X := by rw [e1, e2]
    have h2zero : X + μ (μ X) = 0 := by
      linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hkey
    exact (CharTwo.add_eq_zero.mp h2zero).symm
  intro X hX
  by_cases hfix : Work.PSU3.σE x₀ = x₀
  · -- `x₀` is fixed: `τ = μ²` fixes all of `F`, being an odd-order permutation fixing all but
    -- at most `x₀` and `x₀ + 1`.
    have hx0p1 : Work.PSU3.σE (x₀ + 1) = x₀ + 1 := by rw [map_add, map_one, hfix]
    let F := {x : Work.PSU3.E n // Work.PSU3.σE x = x}
    have hμF2 : ∀ x : Work.PSU3.E n,
        Work.PSU3.σE x = x → Work.PSU3.σE (μ (μ x)) = μ (μ x) :=
      fun x hx => hμF (μ x) (hμF x hx)
    let f : F → F := fun p => ⟨μ (μ p.1), hμF2 p.1 p.2⟩
    -- `τ^[orderOf μ] = id` because `(μ * μ) ^ orderOf μ = 1`.
    have hτm : ∀ x : Work.PSU3.E n, (fun y => μ (μ y))^[orderOf μ] x = x := by
      intro x
      have hgm : (μ * μ) ^ orderOf μ = 1 := by
        have h1 : (μ * μ) ^ orderOf μ = μ ^ (2 * orderOf μ) := by
          rw [← pow_two, ← pow_mul]
        rw [h1, show (2 : ℕ) * orderOf μ = orderOf μ + orderOf μ by ring, pow_add]
        simp [pow_orderOf_eq_one μ]
      have h2 : ∀ k (z : Work.PSU3.E n), (⇑(μ * μ))^[k] z = ((μ * μ) ^ k) z := by
        intro k
        induction k with
        | zero => intro z; rfl
        | succ k ih =>
          intro z
          rw [Function.iterate_succ_apply, ih, pow_succ]
          rfl
      have h1 : (fun y => μ (μ y)) = (⇑(μ * μ) : Work.PSU3.E n → Work.PSU3.E n) := rfl
      rw [h1, h2, hgm]
      rfl
    -- the restriction `f` computes `τ` on the subtype.
    have happly : ∀ (k : ℕ) (p : F), (f^[k] p).1 = (fun x => μ (μ x))^[k] p.1 := by
      intro k
      induction k with
      | zero => intro p; rfl
      | succ k ih =>
        intro p
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        show μ (μ (f^[k] p).1) = μ (μ ((fun x => μ (μ x))^[k] p.1))
        rw [ih p]
    have hfm : ∀ p : F, f^[orderOf μ] p = p := by
      intro p
      apply Subtype.ext
      rw [happly]
      exact hτm p.1
    have hgood : ∀ p : F, p ≠ ⟨x₀, hfix⟩ → p ≠ ⟨x₀ + 1, hx0p1⟩ → f p = p := by
      intro p hp1 hp2
      have h1 : p.1 ≠ x₀ := fun h => hp1 (Subtype.ext h)
      have h2 : p.1 + 1 ≠ x₀ := by
        intro h
        apply hp2
        apply Subtype.ext
        show p.1 = x₀ + 1
        have hc : p.1 + 1 + 1 = x₀ + 1 := congrArg (fun t => t + 1) h
        have hcc : p.1 + 1 + 1 = p.1 := by
          have h2' : (2 : Work.PSU3.E n) = 0 := CharTwo.two_eq_zero
          linear_combination h2'
        rwa [hcc] at hc
      exact Subtype.ext (pair p.1 p.2 h1 h2)
    have hftriv := odd_iterate_fixes_all_but_two f (orderOf μ) hodd hfm hgood
    exact congrArg Subtype.val (hftriv ⟨X, hX⟩)
  · -- `x₀` is not fixed: the two exceptions are not `σE`-fixed, so the relation holds at every
    -- fixed point and `step4_mu_sq_fix_of_relation` applies directly.
    have hrel' : ∀ Y : Work.PSU3.E n, Work.PSU3.σE Y = Y →
        (c + μ Y) * Y = (c + μ (μ Y)) * μ Y := by
      intro Y hY
      refine hrel Y hY ?_ ?_
      · intro h; exact hfix (h ▸ hY)
      · intro h; exact hfix (by rw [← h, map_add, map_one, hY])
    exact step4_mu_sq_fix_of_relation μ c hrel' X hX

end Work.PSU3.StageB.NotFpfStep4
