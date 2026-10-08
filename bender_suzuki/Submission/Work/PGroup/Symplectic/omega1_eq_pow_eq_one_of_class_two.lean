import Mathlib
import Submission.Work.PGroup.Omega1
import Submission.Work.PGroup.Symplectic.centralProduct_of_structure

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Ω₁` of a group of class at most two with all `p`-th powers central

If `H` has nilpotency class at most `2` (i.e. `⁅⊤,⊤⁆ ≤ Z(H)`) and every `p`-th power is central,
with `p` an odd prime, then the set of elements whose `p`-th power is trivial is a subgroup:
for `a^p = b^p = 1` one has
`(a*b)^p = a^p * b^p * ⁅b,a⁆^(p.choose 2)`,
and `⁅b,a⁆` is central of order dividing `p`, so `⁅b,a⁆^(p.choose 2) = (⁅b,a⁆^p)^((p-1)/2) = 1`.
Consequently `Ω₁(H) = {x | x^p = 1}`.
-/

open scoped commutatorElement Pointwise
open Subgroup

namespace Work.PGroup.Symplectic

/-- Power formula in a group in which `⁅b,a⁆` is central:
`(a*b)^n = a^n * b^n * ⁅b,a⁆^(n.choose 2)`. -/
theorem mul_pow_eq_of_commutator_mem_center {G : Type*} [Group G] {a b : G}
    (hc : ∀ g : G, Commute (⁅b,a⁆) g) (n : ℕ) :
    (a*b)^n = a^n * b^n * ⁅b,a⁆^(n.choose 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hcm : ∀ (k : ℕ) (g : G), ⁅b,a⁆^k * g = g * ⁅b,a⁆^k :=
      fun k g => ((hc g).pow_left k).eq
    have move_left : ∀ (k : ℕ) (u v : G), ⁅b,a⁆^k * u * v = u * v * ⁅b,a⁆^k :=
      fun k u v => by rw [mul_assoc, hcm k (u*v)]
    have hbna : b^n * a = ⁅b,a⁆^n * a * b^n := by
      rw [(hc b).symm.commutatorElement_pow_left n]; group
    have hchoose : (n+1).choose 2 = n.choose 2 + n := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_comm]
    calc (a*b)^(n+1)
        = a^n * b^n * ⁅b,a⁆^(n.choose 2) * (a*b) := by rw [pow_succ, ih]
      _ = a^n * b^n * (a*b) * ⁅b,a⁆^(n.choose 2) := by
            rw [mul_assoc (a^n * b^n), hcm (n.choose 2) (a*b), ← mul_assoc]
      _ = a^n * (b^n * a) * b * ⁅b,a⁆^(n.choose 2) := by group
      _ = a^n * (⁅b,a⁆^n * a * b^n) * b * ⁅b,a⁆^(n.choose 2) := by rw [hbna]
      _ = a^n * ⁅b,a⁆^n * a * b^n * b * ⁅b,a⁆^(n.choose 2) := by group
      _ = ⁅b,a⁆^n * a^n * a * b^n * b * ⁅b,a⁆^(n.choose 2) := by
            rw [← hcm n (a^n)]
      _ = ⁅b,a⁆^n * a^(n+1) * b^(n+1) * ⁅b,a⁆^(n.choose 2) := by group
      _ = a^(n+1) * b^(n+1) * (⁅b,a⁆^n * ⁅b,a⁆^(n.choose 2)) := by
            rw [move_left n (a^(n+1)) (b^(n+1)), mul_assoc]
      _ = a^(n+1) * b^(n+1) * ⁅b,a⁆^((n+1).choose 2) := by
            rw [← pow_add, Nat.add_comm n (n.choose 2), ← hchoose]

/-- In a group of class at most two all of whose `p`-th powers are central (`p` an odd prime),
`Ω₁` is exactly the set of elements whose `p`-th power is trivial. -/
theorem omega1_eq_pow_eq_one_of_class_two {H : Type*} [Group H] {p : ℕ}
    (hp : p.Prime) (hodd : p ≠ 2)
    (hclass : ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ ≤ Subgroup.center H)
    (hquot : ∀ x : H, x ^ p ∈ Subgroup.center H) :
    ∀ x : H, x ∈ Work.PGroup.omega1 H p ⊤ ↔ x ^ p = 1 := by
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two hodd
  have hchoose : p.choose 2 = p * m := by
    rw [Nat.choose_two_right, hm, show 2*m+1-1 = 2*m by omega]
    rw [show (2*m+1)*(2*m) = ((2*m+1)*m)*2 by ring,
        Nat.mul_div_left ((2*m+1)*m) (by norm_num : 0 < 2)]
  intro x
  constructor
  · intro hx
    rw [Work.PGroup.omega1] at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact hy.2
    | one => exact one_pow p
    | mul a b _ _ iha ihb =>
        have hcab : ∀ g : H, Commute ⁅b,a⁆ g := fun g =>
          (Subgroup.mem_center_iff.mp
            (hclass (Subgroup.commutator_mem_commutator (Subgroup.mem_top b)
              (Subgroup.mem_top a))) g).symm
        rw [mul_pow_eq_of_commutator_mem_center hcab p, iha, ihb, one_mul, one_mul]
        have hcp : ⁅b,a⁆ ^ p = 1 := by
          rw [(hcab b).symm.commutatorElement_pow_left p, commutatorElement_eq_one_iff_commute]
          exact (Subgroup.mem_center_iff.mp (hquot b) a).symm
        rw [hchoose, pow_mul, hcp, one_pow]
    | inv a _ iha => rw [inv_pow, iha, inv_one]
  · intro hx
    exact Work.PGroup.omega1_subset p (Subgroup.mem_top x) hx

end Work.PGroup.Symplectic
