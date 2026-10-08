import Mathlib
import Submission.Work.Higman.Interface
import Submission.Work.ZassenhausSuzuki.pow_four_of_mulEquiv
import Submission.Work.ZassenhausSuzuki.szA_of_isSuzukiTwoGroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# No inverting pair in a Suzuki `2`-group of order `q²`

A *Suzuki `2`-group* `P` (Higman's notion: a finite `2`-group whose involutions all lie in the
centre, with more than one involution and a cyclic automorphism transitive on them) of order
`|P| = |Z(P)|² = q²` is Higman's group `A(n,θ) = A(GF(2ⁿ), θ)` with `θ` of **odd** order
(`Work.ZassenhausSuzuki.szA_of_isSuzukiTwoGroup`, from Higman's Theorem 1).

In `A(K,θ)` the law is `(a,b) * (c,d) = (a+c, b+d+a·θ c)`, so `x * x = (0, a·θ a)` for
`x = (a,b)`; hence `x * x = 1 ↔ a = 0`.  Conjugation is `y * x * y⁻¹ = (a, b + c·θ a - a·θ c)`
for `y = (c,d)`, so the equation `y * x * y⁻¹ = x⁻¹` is, in characteristic two,

`c·θ a + a·θ c = a·θ a`,   i.e.   `t + θ t = 1`   for `t = c / a`   (`a ≠ 0`).

Iterating `θ t = t + 1` gives `θ ^ k t = t + k`, and since `orderOf θ` is odd, `k = orderOf θ`
gives the contradiction `t = θ ^ (orderOf θ) t = t + (orderOf θ : K) = t + 1`.  So `a = 0` and
`x` is an involution.

The main theorem is this statement transported back along the isomorphism `P ≃* A(n,θ)`.
-/

set_option autoImplicit false

namespace Work.ZassenhausSuzuki.Odd

open LeanEval.GroupTheory.Defs

/-- Conjugation in Higman's group `A(K,θ)`: the second coordinate of `y * x * y⁻¹` is
`x.b + y.a * θ x.a - x.a * θ y.a`. -/
theorem SzA_conj_b {K : Type*} [Field K] (θ : K ≃+* K) (x y : SzA K θ) :
    (y * x * y⁻¹).b = x.b + y.a * θ x.a - x.a * θ y.a := by
  simp only [SzA.mul_b, SzA.mul_a, SzA.inv_a, SzA.inv_b, map_neg]
  ring

/-- In characteristic two, the equation `θ t = t + 1` has no solution when `θ` has odd order:
the hypothesis gives `θ ^ k t = t + k`, hence `t = t + (orderOf θ : K)` and a contradiction
with `Odd (orderOf θ)` through `CharP`. -/
theorem theta_ne_add_one_of_odd_order {K : Type*} [Field K] [CharP K 2] (θ : K ≃+* K)
    (hodd : Odd (orderOf θ)) (t : K) : θ t ≠ t + 1 := by
  intro h
  have hiter : ∀ k : ℕ, (θ ^ k) t = t + (k : K) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', show (θ * θ ^ k) t = θ ((θ ^ k) t) from rfl, ih, map_add, h, map_natCast]
      push_cast
      ring
  have h1 : t = t + (orderOf θ : K) := by
    have h3 := hiter (orderOf θ)
    rw [pow_orderOf_eq_one] at h3
    simpa using h3
  have hm0 : (orderOf θ : K) = 0 := by
    have hh : t + 0 = t + (orderOf θ : K) := by rw [add_zero]; exact h1
    exact (add_left_cancel hh).symm
  exact (Nat.not_even_iff_odd.mpr hodd)
    (even_iff_two_dvd.mpr ((CharP.cast_eq_zero_iff K 2 (orderOf θ)).mp hm0))

/-- In `A(K,θ)` over a field of characteristic two with `θ` of odd order, an element that is
conjugated to its inverse by some element is an involution. -/
theorem SzA_mul_self_eq_one_of_conj_eq_inv {K : Type*} [Field K] [CharP K 2]
    (θ : K ≃+* K) (hodd : Odd (orderOf θ)) (x y : SzA K θ)
    (h : y * x * y⁻¹ = x⁻¹) : x * x = 1 := by
  have hkey : y.a * θ x.a + x.a * θ y.a + x.a * θ x.a = 0 := by
    have hb : x.b + y.a * θ x.a - x.a * θ y.a = -x.b + x.a * θ x.a := by
      have h1 := congrArg SzA.b h
      rw [SzA.inv_b, SzA_conj_b] at h1
      exact h1
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    linear_combination hb + (x.a * θ y.a + x.a * θ x.a - x.b) * h2
  have hfin : x.a * θ x.a = 0 := by
    by_cases ha : x.a = 0
    · simp [ha]
    · exfalso
      have hθa : θ x.a ≠ 0 := fun hz => ha (θ.injective (by rw [hz, map_zero]))
      have h4 : x.a * θ x.a * (x.a⁻¹ * y.a + θ (x.a⁻¹ * y.a) + 1) = 0 := by
        rw [← hkey, map_mul, map_inv₀]
        field_simp
      have h5 : x.a⁻¹ * y.a + θ (x.a⁻¹ * y.a) + 1 = 0 :=
        (mul_eq_zero.mp h4).resolve_left (mul_ne_zero ha hθa)
      have ht : θ (x.a⁻¹ * y.a) = x.a⁻¹ * y.a + 1 := by
        have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
        linear_combination h5 - (x.a⁻¹ * y.a + 1) * h2
      exact theta_ne_add_one_of_odd_order θ hodd _ ht
  calc x * x = (⟨0, x.a * θ x.a⟩ : SzA K θ) := SzA.mul_self_eq θ x
    _ = 1 := by ext <;> simp [hfin]

theorem no_inverting_pair_of_suzuki2_q2 {P : Type} [Group P] [Finite P]
    (h : Submission.Blueprint.IsSuzukiTwoGroup P)
    (hcard : Nat.card P = Nat.card ↥(Subgroup.center P) ^ 2) :
    ∀ x y : P, y * x * y⁻¹ = x⁻¹ → x * x = 1 := by
  intro x y hxy
  obtain ⟨n, θ, _hne, hodd, _hc, ⟨e⟩⟩ :=
    Work.ZassenhausSuzuki.szA_of_isSuzukiTwoGroup Work.Higman.higmanProp h hcard
  have h' : e y * e x * (e y)⁻¹ = (e x)⁻¹ := by
    have hh := congrArg e hxy
    simpa using hh
  have hsq : e x * e x = 1 := SzA_mul_self_eq_one_of_conj_eq_inv θ hodd (e x) (e y) h'
  exact e.injective (by rw [map_mul, hsq, map_one])

end Work.ZassenhausSuzuki.Odd
