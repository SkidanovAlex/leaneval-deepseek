import Submission.ZagierHoffmanProof.ThakurDeg1

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Polynomial RatFunc
open scoped BigOperators WithZero
open WithZero

/-!
# Step M2: coercions into the completion and the truncated binomial expansion

This file sets up the language used by Thakur's degree formula for the depth-one power
sums: the constant map `cst : F →+* F((1/t))`, its interplay with the valuation at
infinity, and the *truncated* binomial expansion of `∑_c (z + c)^{-k}` for an element
`z` of the completion whose translates `z + c` all have the same valuation as `z`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

section Coercions

/-- The canonical ring hom `F(t) → F((1/t))`. -/
noncomputable def toK : RatFunc F →+* RatFunc.CompletionAtInfty F :=
  algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)

/-- The constant map `F →+* F((1/t))`. -/
noncomputable def cstHom : F →+* RatFunc.CompletionAtInfty F :=
  (toK F).comp (algebraMap F (RatFunc F))

/-- The image of the constant `a : F` in the completion. -/
noncomputable def cst (a : F) : RatFunc.CompletionAtInfty F := cstHom F a

lemma cst_add (a b : F) : cst F (a + b) = cst F a + cst F b := map_add _ _ _
lemma cst_mul (a b : F) : cst F (a * b) = cst F a * cst F b := map_mul _ _ _
lemma cst_one : cst F 1 = 1 := map_one _
lemma cst_zero : cst F 0 = 0 := map_zero _
lemma cst_pow (a : F) (n : ℕ) : cst F (a ^ n) = cst F a ^ n := map_pow _ _ _

lemma v_toK (x : RatFunc F) (hx : x ≠ 0) :
    Valued.v (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) x) = exp x.intDegree :=
  inftyValued_v_ratFunc F x hx

lemma v_cst_le_one (a : F) : Valued.v (cst F a) ≤ 1 := by
  by_cases ha : a = 0
  · subst ha; rw [cst_zero]; simp
  · rw [cst, cstHom, RingHom.comp_apply, toK, v_toK F _ (by simpa using ha)]
    have h3 : (algebraMap F (RatFunc F) a).intDegree = 0 := by
      rw [RatFunc.algebraMap_eq_C, RatFunc.intDegree_C]
    rw [h3, WithZero.exp_zero]

lemma v_toK_X : Valued.v (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) RatFunc.X)
    = exp (1 : ℤ) := by
  rw [v_toK F _ RatFunc.X_ne_zero, RatFunc.intDegree_X]

/-- A polynomial with coefficients in `F`, evaluated at an element of valuation `≤ 1`, has
valuation `≤ 1`. -/
lemma v_eval_poly_le_one (p : F[X]) (u : RatFunc.CompletionAtInfty F)
    (hu : Valued.v u ≤ 1) :
    Valued.v (p.eval₂ (cstHom F) u) ≤ 1 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.eval₂_add]
      exact Valuation.map_add_le (v := Valued.v) hp hq
  | monomial n a =>
      rw [Polynomial.eval₂_monomial, map_mul, map_pow]
      exact mul_le_one₀ (v_cst_le_one F a) (zero_le) (pow_le_one₀ (zero_le) hu)

end Coercions

section Truncation

/-- The truncated binomial series `∑_{j ≤ N} binF k j · X^j` (a polynomial over `F`). -/
noncomputable def tTrunc (k N : ℕ) : F[X] :=
  ∑ j ∈ Finset.range (N + 1), Polynomial.C (binF F k j) * Polynomial.X ^ j

/-- The binomial coefficients of `tTrunc` are the cast of the corresponding integers. -/
lemma intCast_binCoeff (k j : ℕ) :
    (Int.castRingHom F) ((-1 : ℤ) ^ j * (Nat.choose (k + j - 1) j : ℤ)) = binF F k j := by
  show (((-1 : ℤ) ^ j * (Nat.choose (k + j - 1) j : ℤ) : ℤ) : F) = binF F k j
  rw [binF]
  push_cast
  ring

/-- The algebraic truncation identity: `(1+X)^k · tTrunc k N ≡ 1` modulo `X^{N+1}`. -/
lemma tTrunc_mul (k N : ℕ) (hk : 1 ≤ k) : ∃ R : F[X],
    (1 + Polynomial.X : F[X]) ^ k * tTrunc F k N = 1 + Polynomial.X ^ (N + 1) * R := by
  obtain ⟨R₀, hR₀⟩ := Commons.Algebra.Binomial.trunc_inv_add_one k N hk
  refine ⟨Polynomial.map (Int.castRingHom F) R₀, ?_⟩
  have hsum : (Polynomial.map (Int.castRingHom F))
      (∑ j ∈ Finset.range (N + 1),
        Polynomial.C (((-1 : ℤ) ^ j * (Nat.choose (k + j - 1) j : ℤ))) * Polynomial.X ^ j)
      = tTrunc F k N := by
    rw [tTrunc, Polynomial.map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      intCast_binCoeff F k j]
  have h := congrArg (Polynomial.map (Int.castRingHom F)) hR₀
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_one, Polynomial.map_pow,
    Polynomial.map_X, hsum] at h
  exact h

/-- Evaluation of the truncation identity at an element `u` of the completion. -/
lemma tTrunc_eval (k N : ℕ) (hk : 1 ≤ k) (R : F[X])
    (hR : (1 + Polynomial.X : F[X]) ^ k * tTrunc F k N = 1 + Polynomial.X ^ (N + 1) * R)
    (u : RatFunc.CompletionAtInfty F) :
    (1 + u) ^ k * (∑ j ∈ Finset.range (N + 1), cst F (binF F k j) * u ^ j)
      = 1 + u ^ (N + 1) * (R.eval₂ (cstHom F) u) := by
  have h := congrArg (Polynomial.eval₂ (cstHom F) u) hR
  simp only [tTrunc, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_add,
    Polynomial.eval₂_one, Polynomial.eval₂_X, Polynomial.eval₂_finsetSum, Polynomial.eval₂_C] at h
  exact h

/-- The generic truncated expansion of `((1+u)^k)^{-1}`. -/
lemma trunc_generic (k N : ℕ) (hk : 1 ≤ k) (R : F[X])
    (hR : (1 + Polynomial.X : F[X]) ^ k * tTrunc F k N = 1 + Polynomial.X ^ (N + 1) * R)
    (u : RatFunc.CompletionAtInfty F) (hu : 1 + u ≠ 0) :
    ((1 + u) ^ k)⁻¹
      = (∑ j ∈ Finset.range (N + 1), cst F (binF F k j) * u ^ j)
        - u ^ (N + 1) * (R.eval₂ (cstHom F) u) * ((1 + u) ^ k)⁻¹ := by
  have h := tTrunc_eval F k N hk R hR u
  have hp : (1 + u) ^ k ≠ 0 := pow_ne_zero _ hu
  have h1 : (∑ j ∈ Finset.range (N + 1), cst F (binF F k j) * u ^ j) =
      ((1 + u) ^ k)⁻¹ * (1 + u ^ (N + 1) * (R.eval₂ (cstHom F) u)) := by
    rw [← h, ← mul_assoc, inv_mul_cancel₀ hp, one_mul]
  rw [h1, mul_add, mul_one]
  ring

end Truncation

section Expansion

/-- `(z^m)⁻¹ · (z^n)⁻¹ = (z^(m+n))⁻¹` in a field. -/
lemma inv_pow_mul_inv_pow (z : RatFunc.CompletionAtInfty F) (m n : ℕ) :
    (z ^ m)⁻¹ * (z ^ n)⁻¹ = (z ^ (m + n))⁻¹ := by
  rw [← mul_inv_rev, ← pow_add, Nat.add_comm]

/-- `∑_{c : F} ((z + c)^k)^{-1}` : the depth-one power sum at the level of an arbitrary
element `z` of the completion. -/
noncomputable def zetaSum (k : ℕ) (z : RatFunc.CompletionAtInfty F) :
    RatFunc.CompletionAtInfty F :=
  letI : Fintype F := Fintype.ofFinite F
  ∑ c : F, ((z + cst F c) ^ k)⁻¹

/-- The truncated first part of the expansion of `zetaSum F k z`. -/
noncomputable def trExp (k N : ℕ) (z : RatFunc.CompletionAtInfty F) :
    RatFunc.CompletionAtInfty F :=
  ∑ j ∈ Finset.range (N + 1), cst F (binF F k j * psumF F j) * (z ^ (k + j))⁻¹

/-- The per-`c` identity: the truncated expansion of a single summand. -/
lemma per_c (k N : ℕ) (hk : 1 ≤ k) (R : F[X])
    (hR : (1 + Polynomial.X : F[X]) ^ k * tTrunc F k N = 1 + Polynomial.X ^ (N + 1) * R)
    (z : RatFunc.CompletionAtInfty F) (hz : z ≠ 0) (c : F) (hzc : z + cst F c ≠ 0) :
    ((z + cst F c) ^ k)⁻¹
      = (∑ j ∈ Finset.range (N + 1), cst F (binF F k j * c ^ j) * (z ^ (k + j))⁻¹)
        - cst F (c ^ (N + 1)) * (z ^ (N + 1))⁻¹
            * (R.eval₂ (cstHom F) (cst F c * z⁻¹)) * ((z + cst F c) ^ k)⁻¹ := by
  set u : RatFunc.CompletionAtInfty F := cst F c * z⁻¹ with hu
  have hzeq : z + cst F c = (1 + u) * z := by
    rw [hu, add_mul, one_mul, mul_assoc, inv_mul_cancel₀ hz, mul_one, add_comm]
  have h1u : 1 + u ≠ 0 := by
    intro h
    exact hzc (by rw [hzeq, h, zero_mul])
  have hshift : ((z + cst F c) ^ k)⁻¹ = (z⁻¹) ^ k * ((1 + u) ^ k)⁻¹ := by
    rw [hzeq, mul_pow, mul_inv_rev, inv_pow]
  have hshift' : ((1 + u) ^ k)⁻¹ = z ^ k * ((z + cst F c) ^ k)⁻¹ := by
    rw [hshift, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hz, one_pow, one_mul]
  have hgen := trunc_generic F k N hk R hR u h1u
  have hfirst : (z⁻¹) ^ k * (∑ j ∈ Finset.range (N + 1), cst F (binF F k j) * u ^ j)
      = (∑ j ∈ Finset.range (N + 1), cst F (binF F k j * c ^ j) * (z ^ (k + j))⁻¹) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hu, mul_pow, cst_mul, cst_pow, inv_pow]
    rw [← inv_pow_mul_inv_pow F z k j]
    ring
  have hsecond : (z⁻¹) ^ k * (u ^ (N + 1)
        * (R.eval₂ (cstHom F) u) * ((1 + u) ^ k)⁻¹)
      = cst F (c ^ (N + 1)) * (z ^ (N + 1))⁻¹
          * (R.eval₂ (cstHom F) (cst F c * z⁻¹)) * ((z + cst F c) ^ k)⁻¹ := by
    rw [hshift', hu, mul_pow, cst_pow, inv_pow, inv_pow]
    field_simp
  have hmul := congrArg (fun w => (z⁻¹) ^ k * w) hgen
  rw [mul_sub] at hmul
  conv_lhs => rw [hshift, hmul, hfirst, hsecond]

section ExpArith

/-- `(exp m)^n = exp (m * n)`. -/
lemma exp_pow (m : ℤ) (n : ℕ) : (WithZero.exp m : ℤᵐ⁰) ^ n = WithZero.exp (m * n) := by
  rw [← WithZero.exp_nsmul]
  congr 1
  ring

end ExpArith

section Expansion1

/-- `cst` commutes with finite sums. -/
lemma cst_sum {ι : Type*} (s : Finset ι) (f : ι → F) :
    cst F (∑ i ∈ s, f i) = ∑ i ∈ s, cst F (f i) :=
  map_sum (cstHom F) f s

lemma v_per_c_le (k N : ℕ) (z : RatFunc.CompletionAtInfty F) (m : ℤ) (c : F) (R : F[X])
    (hz : z ≠ 0) (hzv : Valued.v z = WithZero.exp m) (hm : 0 ≤ m)
    (hzc : Valued.v (z + cst F c) = Valued.v z) :
    Valued.v (cst F (c ^ (N + 1)) * (z ^ (N + 1))⁻¹
        * (R.eval₂ (cstHom F) (cst F c * z⁻¹)) * ((z + cst F c) ^ k)⁻¹)
      ≤ WithZero.exp (-(m * ((k : ℤ) + N + 1))) := by
  have hu1 : Valued.v (cst F c * z⁻¹) ≤ 1 := by
    rw [Valuation.map_mul, Valuation.map_inv, hzv, ← WithZero.exp_neg]
    refine mul_le_one₀ (v_cst_le_one F c) zero_le ?_
    rw [← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (neg_nonpos.mpr hm)
  have hQ : Valued.v (R.eval₂ (cstHom F) (cst F c * z⁻¹)) ≤ 1 :=
    v_eval_poly_le_one F R _ hu1
  have h2 : Valued.v ((z ^ (N + 1))⁻¹) = WithZero.exp (-(m * ((N : ℤ) + 1))) := by
    rw [Valuation.map_inv, Valuation.map_pow, hzv, exp_pow, ← WithZero.exp_neg]
    norm_num
  have h4 : Valued.v (((z + cst F c) ^ k)⁻¹) = WithZero.exp (-(m * (k : ℤ))) := by
    rw [Valuation.map_inv, Valuation.map_pow, hzc, hzv, exp_pow, ← WithZero.exp_neg]
  rw [Valuation.map_mul, Valuation.map_mul, Valuation.map_mul, h2, h4]
  have hab : Valued.v (cst F (c ^ (N + 1))) * WithZero.exp (-(m * ((N : ℤ) + 1)))
      ≤ 1 * WithZero.exp (-(m * ((N : ℤ) + 1))) :=
    mul_le_mul (v_cst_le_one F _) le_rfl zero_le zero_le
  have hcd : Valued.v (R.eval₂ (cstHom F) (cst F c * z⁻¹)) * WithZero.exp (-(m * (k : ℤ)))
      ≤ 1 * WithZero.exp (-(m * (k : ℤ))) :=
    mul_le_mul hQ le_rfl zero_le zero_le
  calc Valued.v (cst F (c ^ (N + 1))) * WithZero.exp (-(m * ((N : ℤ) + 1)))
        * Valued.v (R.eval₂ (cstHom F) (cst F c * z⁻¹)) * WithZero.exp (-(m * (k : ℤ)))
      = (Valued.v (cst F (c ^ (N + 1))) * WithZero.exp (-(m * ((N : ℤ) + 1))))
        * (Valued.v (R.eval₂ (cstHom F) (cst F c * z⁻¹)) * WithZero.exp (-(m * (k : ℤ)))) := by
        rw [mul_assoc]
    _ ≤ (1 * WithZero.exp (-(m * ((N : ℤ) + 1)))) * (1 * WithZero.exp (-(m * (k : ℤ)))) :=
        mul_le_mul hab hcd zero_le zero_le
    _ = WithZero.exp (-(m * ((k : ℤ) + N + 1))) := by
        rw [one_mul, one_mul, ← WithZero.exp_add]
        congr 1
        ring

/-- ★ The truncated expansion of `zetaSum F k z`: the main computational engine.  It
expresses the depth-one power sum as the truncated binomial series plus a remainder whose
valuation is at most `v z ^ (-(k + N + 1))`. -/
theorem trunc_expansion (k N : ℕ) (hk : 1 ≤ k) (z : RatFunc.CompletionAtInfty F) (m : ℤ)
    (hz : z ≠ 0) (hzv : Valued.v z = WithZero.exp m) (hm : 0 ≤ m)
    (hzc : ∀ c : F, Valued.v (z + cst F c) = Valued.v z) :
    ∃ W : RatFunc.CompletionAtInfty F, zetaSum F k z = trExp F k N z + W ∧
      Valued.v W ≤ WithZero.exp (-(m * ((k : ℤ) + N + 1))) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨R, hR⟩ := tTrunc_mul F k N hk
  have hzcn : ∀ c : F, z + cst F c ≠ 0 := by
    intro c h
    have h1 := hzc c
    rw [h, hzv, map_zero] at h1
    exact WithZero.exp_ne_zero h1.symm
  refine ⟨-∑ c : F, cst F (c ^ (N + 1)) * (z ^ (N + 1))⁻¹
      * (R.eval₂ (cstHom F) (cst F c * z⁻¹)) * ((z + cst F c) ^ k)⁻¹, ?_, ?_⟩
  · rw [zetaSum, trExp]
    have hper : ∀ c : F, ((z + cst F c) ^ k)⁻¹ =
        (∑ j ∈ Finset.range (N + 1), cst F (binF F k j * c ^ j) * (z ^ (k + j))⁻¹)
          - cst F (c ^ (N + 1)) * (z ^ (N + 1))⁻¹
              * (R.eval₂ (cstHom F) (cst F c * z⁻¹)) * ((z + cst F c) ^ k)⁻¹ :=
      fun c => per_c F k N hk R hR z hz c (hzcn c)
    rw [Finset.sum_congr rfl (fun c _ => hper c), Finset.sum_sub_distrib, sub_eq_add_neg]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Finset.sum_mul, ← cst_sum]
    congr 1
    rw [← Finset.mul_sum]
    rfl
  · rw [Valuation.map_neg]
    exact le_trans (Valuation.map_sum_le (v := Valued.v)
        (g := WithZero.exp (-(m * ((k : ℤ) + N + 1))))
        (fun c _ => v_per_c_le F k N z m c R hz hzv hm (hzc c))) le_rfl


end Expansion1

end Expansion

end ZagierHoffmanPositiveChar
