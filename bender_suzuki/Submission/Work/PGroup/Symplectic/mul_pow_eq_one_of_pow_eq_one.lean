import Mathlib
import Submission.Work.PGroup.Symplectic.centralProduct_of_structure

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Powers of products in a class-two group with an order-`p` central subgroup

Let `K ≤ Z(G)` be a central subgroup of order a prime `p ≠ 2`, and assume every commutator
`y * x * y⁻¹ * x⁻¹` lies in `K`.  Then `⁅G, G⁆ ≤ Z(G)`: the group has nilpotency class at
most two, and the `p`-th power map is multiplicative (the correction term
`⁅y, x⁆ ^ (p.choose 2)` vanishes because `p` is odd and `⁅y, x⁆ ^ p = 1`).  Consequently
`g ↦ g ^ (p ^ i)` is a homomorphism, so elements whose `p ^ i`-th power is trivial form a
subgroup.  This is the elementary "`Ω₁` is a subgroup" fact used for the symplectic-type
classification.
-/

set_option linter.unusedVariables false

open scoped commutatorElement

namespace Work.PGroup.Symplectic

theorem mul_pow_eq_one_of_pow_eq_one {G : Type*} [Group G] {p i : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hi : 1 ≤ i) {K : Subgroup G} (hKZ : K ≤ Subgroup.center G) (hKcard : Nat.card ↥K = p)
    (hcomm : ∀ x y : G, y * x * y⁻¹ * x⁻¹ ∈ K) {x y : G}
    (hx : x ^ p ^ i = 1) (hy : y ^ p ^ i = 1) : (x * y) ^ p ^ i = 1 := by
  -- Every element of `K` has order dividing `p`, hence its `p`-th power is trivial.
  have hKexp : ∀ k ∈ K, k ^ p = 1 := by
    intro k hk
    rw [← orderOf_dvd_iff_pow_eq_one, ← hKcard]
    exact K.orderOf_dvd_natCard hk
  -- All commutators lie in `K`, hence in the centre.
  have hclass : (⁅(⊤ : Subgroup G), ⊤⁆ : Subgroup G) ≤ Subgroup.center G := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [commutatorElement_def]
    exact hKZ (hcomm b a)
  have hcommK : ∀ a b : G, ⁅a, b⁆ ^ p = 1 := by
    intro a b
    rw [commutatorElement_def]
    exact hKexp _ (hcomm b a)
  -- The `p`-th power map is multiplicative on a class-two group with commutators of order `p`.
  have hpm : ∀ u v : G, (u * v) ^ p = u ^ p * v ^ p :=
    pow_mul_eq_of_class_two hp hodd hclass hcommK
  -- Hence so is `g ↦ g ^ (p ^ i)`, by induction on `i`.
  have key : ∀ n : ℕ, (x * y) ^ p ^ n = x ^ (p ^ n) * y ^ (p ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
      simp only [Nat.pow_succ, pow_mul, ih, hpm]
  have h := key i
  rw [hx, hy, mul_one] at h
  exact h

end Work.PGroup.Symplectic
