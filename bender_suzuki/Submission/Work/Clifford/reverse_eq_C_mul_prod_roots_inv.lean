import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Clifford

open Polynomial

/-- `reverse` is multiplicative on the product of a multiset of polynomials over a field. -/
lemma reverse_multiset_prod {K : Type*} [Field K] (s : Multiset K[X]) :
    (s.prod).reverse = (s.map (fun f => f.reverse)).prod := by
  induction s using Multiset.induction with
  | empty => simpa using (reverse_C (1 : K))
  | cons a s ih =>
      rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons, reverse_mul_of_domain, ih]

/-- Reversing `X - C a` gives `C (-a) * (X - C a⁻¹)`, for `a ≠ 0`. -/
lemma reverse_X_sub_C {K : Type*} [Field K] (a : K) (ha : a ≠ 0) :
    (X - C a).reverse = C (-a) * (X - C a⁻¹) := by
  have hX : (X : K[X]).reverse = 1 := by
    have h : (X : K[X]) = 1 * X := by ring
    rw [h, reverse_mul_X]
    simpa using (reverse_C (1 : K))
  have hca : C (-a) * C (a⁻¹) = (-1 : K[X]) := by
    rw [← map_mul, neg_mul, mul_inv_cancel₀ ha, map_neg, map_one]
  rw [sub_eq_add_neg, ← map_neg C a, reverse_add_C, hX, natDegree_X, pow_one]
  rw [mul_sub, hca]
  ring

theorem reverse_eq_C_mul_prod_roots_inv {K : Type*} [Field K] (p : Polynomial K)
    (hp : p.Monic) (hsp : p.Splits) (h0 : p.coeff 0 ≠ 0) :
    p.reverse = Polynomial.C (p.coeff 0) *
      (p.roots.map (fun a => Polynomial.X - Polynomial.C a⁻¹)).prod := by
  have hp0 : p ≠ 0 := hp.ne_zero
  -- no root of `p` is zero, since `p 0 = p.coeff 0 ≠ 0`
  have hroot : ∀ a ∈ p.roots, a ≠ 0 := by
    intro a ha h
    subst h
    rw [mem_roots hp0, IsRoot.def, ← coeff_zero_eq_eval_zero] at ha
    exact h0 ha
  -- `p` is the product of `X - C a` over its roots
  have h_eq : p = (p.roots.map (fun a => X - C a)).prod := hsp.eq_prod_roots_of_monic hp
  have hmap : (p.roots.map (fun a => X - C a)).map (fun f => f.reverse)
      = p.roots.map (fun a => C (-a) * (X - C a⁻¹)) := by
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl ?_
    intro a ha
    exact reverse_X_sub_C a (hroot a ha)
  -- the scalar product `∏ (-a)` equals `p.coeff 0`
  have hC : (p.roots.map (fun a => C (-a))).prod = C (p.coeff 0) := by
    have h1 : (p.roots.map (fun a => C (-a))).prod
        = C ((p.roots.map (fun a => -a)).prod) := by
      simpa only [Multiset.map_map, Function.comp_def] using
        (map_multiset_prod (Polynomial.C) (p.roots.map (fun a => -a))).symm
    rw [h1, Multiset.prod_map_neg, ← hsp.natDegree_eq_card_roots,
      hsp.coeff_zero_eq_prod_roots_of_monic hp]
  conv_lhs => rw [h_eq]
  rw [reverse_multiset_prod, hmap, Multiset.prod_map_mul, hC]

end Work.Clifford
