import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.AppXIDickson

/-- Arithmetic helper: a divisor of `8` that is neither `4` nor `8` divides `2`. -/
private lemma order_dvd_two_of_dvd_eight {n : ℕ} (h : n ∣ 8) (h4 : n ≠ 4) (h8 : n ≠ 8) :
    n ∣ 2 := by
  have hpos : 0 < n := Nat.pos_of_dvd_of_pos h (by norm_num)
  have hle : n ≤ 8 := Nat.le_of_dvd (by norm_num) h
  interval_cases n <;> simp_all

/-- A non-abelian group of order `8` contains an element `x` of order `4` together with an
element `y` that inverts it (`y * x * y⁻¹ = x⁻¹`).  (The conclusion already holds without the
`huniq` hypothesis; it is retained verbatim from the request.)

Route.  If every element had order dividing `2` the group would be abelian (for a group all of
whose elements are involutions, `(a*b)^2 = 1` gives `a*b = b*a`), so some element has order
not dividing `2`; since the order divides `8` it is `4` or `8`, and a square of an order-`8`
element has order `4`.  Thus there is `x` with `orderOf x = 4`.  Then `H = ⟨x⟩` has order `4`
and index `2`, hence is normal.  The subgroup `H` is not contained in the centre: if `H ≤ Z(P)`
the quotient by `H` has order `2`, so it is cyclic and
`commutative_of_cyclic_center_quotient` would make `P` abelian.  Hence some `y` satisfies
`y * x * y⁻¹ ≠ x`; by normality `y * x * y⁻¹ ∈ H`, and its order is again `4`, so
`y * x * y⁻¹ ∈ {x, x⁻¹}` — and it is not `x`. -/
theorem exists_order_four_and_conj_inv {P : Type} [Group P] [Finite P] (hcard : Nat.card P = 8)
    (hnab : ¬ IsMulCommutative P) (huniq : ∀ x y : P, orderOf x = 2 → orderOf y = 2 → x = y) :
    ∃ x y : P, orderOf x = 4 ∧ y * x * y⁻¹ = x⁻¹ := by
  classical
  -- If every element squares to `1`, then `P` is commutative.
  have comm_of_sq_one : (∀ z : P, z ^ 2 = 1) → IsMulCommutative P := by
    intro h
    rw [isMulCommutative_iff]
    intro a b
    have inv_eq : ∀ c : P, c⁻¹ = c := by
      intro c
      exact inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact h c)
    have hab : (a * b)⁻¹ = a * b :=
      inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact h (a * b))
    rw [mul_inv_rev, inv_eq a, inv_eq b] at hab
    exact hab.symm
  -- There is an element of order `4`.
  have h4exists : ∃ x : P, orderOf x = 4 := by
    by_contra hc
    push Not at hc
    apply hnab
    apply comm_of_sq_one
    intro z
    rw [← orderOf_dvd_iff_pow_eq_one]
    have hdvd : orderOf z ∣ 8 := by rw [← hcard]; exact orderOf_dvd_natCard z
    have h8 : orderOf z ≠ 8 := by
      intro hz
      exact hc (z ^ 2) (by rw [orderOf_pow, hz]; norm_num)
    exact order_dvd_two_of_dvd_eight hdvd (hc z) h8
  obtain ⟨x, hx4⟩ := h4exists
  -- `H = ⟨x⟩` has order `4` and index `2`, hence is normal.
  have hHidx : (Subgroup.zpowers x).index = 2 := by
    rw [Subgroup.index_eq_card_div, Nat.card_zpowers, hx4, hcard]
  have hHnormal : (Subgroup.zpowers x).Normal := Subgroup.normal_of_index_eq_two hHidx
  -- Some `y` fails to commute with `x`.
  have hnotcentral : ∃ y : P, y * x * y⁻¹ ≠ x := by
    by_contra hc
    push Not at hc
    apply hnab
    have hxcenter : x ∈ Subgroup.center P := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg := hc g
      rw [mul_inv_eq_iff_eq_mul] at hg
      exact hg
    have hHcenter : Subgroup.zpowers x ≤ Subgroup.center P := by
      rw [Subgroup.zpowers_le]
      exact hxcenter
    haveI : (Subgroup.zpowers x).Normal := hHnormal
    have hcyc : IsCyclic (P ⧸ Subgroup.zpowers x) :=
      isCyclic_of_prime_card (p := 2) (by rw [← Subgroup.index_eq_card, hHidx])
    haveI := hcyc
    exact (QuotientGroup.mk' (Subgroup.zpowers x)).isMulCommutative_of_isCyclic_of_ker_le_center
      (by rw [QuotientGroup.ker_mk']; exact hHcenter)
  obtain ⟨y, hy⟩ := hnotcentral
  refine ⟨x, y, hx4, ?_⟩
  have hwH : y * x * y⁻¹ ∈ Subgroup.zpowers x := hHnormal.conj_mem x (Subgroup.mem_zpowers x) y
  have hword : orderOf (y * x * y⁻¹) = 4 := by
    rw [← hx4]
    simpa only [MulAut.conj_apply] using MulEquiv.orderOf_eq (MulAut.conj y) x
  -- `y * x * y⁻¹` lies in `⟨x⟩ = {1, x, x^2, x^3}` and has order `4`, so it is `x` or `x⁻¹`.
  have hcases : y * x * y⁻¹ = x ∨ y * x * y⁻¹ = x⁻¹ := by
    rw [mem_zpowers_iff_mem_range_orderOf, hx4, Finset.mem_image] at hwH
    obtain ⟨k, hk, hkw⟩ := hwH
    rw [Finset.mem_range] at hk
    interval_cases k
    · exfalso
      have : orderOf (y * x * y⁻¹) = 1 := by rw [← hkw, pow_zero]; simp
      omega
    · left; rw [← hkw, pow_one]
    · exfalso
      have : orderOf (y * x * y⁻¹) = 2 := by rw [← hkw, orderOf_pow, hx4]; norm_num
      omega
    · right
      rw [← hkw]
      have hx4pow : x ^ 4 = 1 := by rw [← hx4]; exact pow_orderOf_eq_one x
      have h3 : x * x ^ 3 = 1 := by rw [← pow_succ' x 3]; exact hx4pow
      exact (inv_eq_of_mul_eq_one_right h3).symm
  rcases hcases with h | h
  · exact absurd h hy
  · exact h

end Work.AppXIDickson
