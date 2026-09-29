import Mathlib
import Submission.Commons.FieldTheory.RatFunc.ordDegT_def
import Submission.Commons.FieldTheory.RatFunc.ordInfT_def
import Submission.Commons.FieldTheory.RatFunc.ordInfT_mul
import Submission.Commons.FieldTheory.RatFunc.ordInfT_add_le_max
import Submission.Commons.FieldTheory.RatFunc.ordInfT_neg
import Submission.Commons.FieldTheory.RatFunc.ordInfT_eq_top_iff
import Submission.Commons.FieldTheory.RatFunc.ordInfT_div
import Submission.Commons.FieldTheory.RatFunc.ordInfT_inv
import Submission.Commons.FieldTheory.RatFunc.ordAtT_adjoint_eq_of_indicial

namespace Commons.FieldTheory.RatFunc

open Classical
open Commons.Algebra.Polynomial
open Commons.FieldTheory.RatFunc

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable {K : Type*} [Field K]

/-! ## Basic properties of `ordDegT = -ordInfT` -/

private theorem ordDegT_eq_neg_ordInfT (x : RatFunc K) : ordDegT x = -ordInfT x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [ordDegT, ordInfT]
  · rw [ordDegT_def hx, ordInfT_def hx, neg_sub]

private theorem ordDegT_eq_top_iff {x : RatFunc K} : ordDegT x = ⊤ ↔ x = 0 := by
  rw [ordDegT_eq_neg_ordInfT]
  constructor
  · intro h
    by_contra hx
    rw [ordInfT_def hx] at h
    exact WithTop.coe_ne_top h
  · rintro rfl
    simp [ordInfT]

private theorem ordDegT_eq_neg_intDegree {x : RatFunc K} (hx : x ≠ 0) :
    ordDegT x = -((RatFunc.intDegree x : ℤ) : WithTop ℤ) := by
  rw [ordDegT_eq_neg_ordInfT, ordInfT_eq_coe_intDegree hx]

private theorem ordDegT_mul {x y : RatFunc K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordDegT (x * y) = ordDegT x + ordDegT y := by
  rw [ordDegT_eq_neg_ordInfT, ordDegT_eq_neg_ordInfT, ordDegT_eq_neg_ordInfT,
    ordInfT_mul hx hy, neg_add_rev, add_comm]

private theorem ordDegT_neg (x : RatFunc K) : ordDegT (-x) = ordDegT x := by
  rw [ordDegT_eq_neg_ordInfT, ordDegT_eq_neg_ordInfT, ordInfT_neg]

private theorem ordDegT_inv {x : RatFunc K} (hx : x ≠ 0) : ordDegT x⁻¹ = -ordDegT x := by
  rw [ordDegT_eq_neg_ordInfT, ordDegT_eq_neg_ordInfT, ordInfT_inv hx]

private theorem ordDegT_div {x y : RatFunc K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordDegT (x / y) = ordDegT x - ordDegT y := by
  rw [ordDegT_eq_neg_ordInfT, ordDegT_eq_neg_ordInfT, ordDegT_eq_neg_ordInfT,
    ordInfT_div hx hy]
  rw [sub_eq_add_neg, sub_eq_add_neg, neg_add_rev, neg_neg, add_comm]

private theorem ordDegT_add_ge (x y : RatFunc K) :
    min (ordDegT x) (ordDegT y) ≤ ordDegT (x + y) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [zero_add]
    have : ordDegT (0 : RatFunc K) = ⊤ := by simp [ordDegT]
    rw [this]; exact min_le_right _ _
  rcases eq_or_ne y 0 with rfl | hy
  · rw [add_zero]; exact min_le_left _ _
  rcases eq_or_ne (x + y) 0 with hxy | hxy
  · rw [hxy]
    have : ordDegT (0 : RatFunc K) = ⊤ := by simp [ordDegT]
    rw [this]; exact le_top
  · rw [ordDegT_eq_neg_intDegree hx, ordDegT_eq_neg_intDegree hy, ordDegT_eq_neg_intDegree hxy,
      ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.LinearOrderedAddCommGroup.coe_neg,
      ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_min, WithTop.coe_le_coe,
      min_neg_neg, neg_le_neg_iff]
    exact RatFunc.intDegree_add_le hy hxy

private theorem ordDegT_add_eq_of_lt {x y : RatFunc K} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : ordDegT x < ordDegT y) : ordDegT (x + y) = ordDegT x := by
  rcases eq_or_ne (x + y) 0 with hxy | hxy
  · have hy_eq : y = -x := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hxy
    rw [hy_eq, ordDegT_neg] at h
    exact absurd h (lt_irrefl _)
  · have h1 : ordDegT x ≤ ordDegT (x + y) := by
      have := ordDegT_add_ge x y
      rwa [min_eq_left (le_of_lt h)] at this
    have h2 : min (ordDegT (x + y)) (ordDegT y) ≤ ordDegT x := by
      have h2 := ordDegT_add_ge (x + y) (-y)
      simpa only [add_assoc, add_neg_cancel, add_zero, ordDegT_neg] using h2
    have h3 : ordDegT (x + y) ≤ ordDegT x := by
      rcases le_total (ordDegT (x + y)) (ordDegT y) with hh | hh
      · rwa [min_eq_left hh] at h2
      · rw [min_eq_right hh] at h2
        exact absurd h2 (not_le.mpr h)
    exact le_antisymm h3 h1

private theorem ordDegT_mul_ge (x y : RatFunc K) : ordDegT x + ordDegT y ≤ ordDegT (x * y) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [zero_mul]; simp [ordDegT]
  rcases eq_or_ne y 0 with rfl | hy
  · rw [mul_zero]; simp [ordDegT]
  · rw [ordDegT_mul hx hy]

private theorem ordDegT_algebraMap {p : Polynomial K} (hp : p ≠ 0) :
    ordDegT (algebraMap (Polynomial K) (RatFunc K) p)
      = -((Polynomial.natDegree p : ℤ) : WithTop ℤ) := by
  rw [ordDegT_eq_neg_ordInfT, ordInfT_eq_coe_intDegree (RatFunc.algebraMap_ne_zero hp),
    RatFunc.intDegree_polynomial]

private theorem zero_le_ordDegT_algebraMap_C (a : K) :
    (0 : WithTop ℤ) ≤ ordDegT (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C a)) := by
  by_cases ha : a = 0
  · rw [ha, Polynomial.C_0, map_zero]; simp [ordDegT]
  · rw [ordDegT_algebraMap (by rwa [Polynomial.C_ne_zero]), Polynomial.natDegree_C]
    simp

private theorem zero_le_ordDegT_intCast (n : ℤ) :
    (0 : WithTop ℤ) ≤ ordDegT ((n : ℤ) : RatFunc K) := by
  rw [intCast_eq_algebraMap_C n]
  exact zero_le_ordDegT_algebraMap_C _

private theorem le_ordDegT_mul_intCast (n : ℤ) (y : RatFunc K) :
    ordDegT y ≤ ordDegT (((n : ℤ) : RatFunc K) * y) := by
  have h0 : (0 : WithTop ℤ) ≤ ordDegT (((n : ℤ) : RatFunc K)) := zero_le_ordDegT_intCast n
  calc ordDegT y = (0 : WithTop ℤ) + ordDegT y := (zero_add _).symm
    _ ≤ ordDegT (((n : ℤ) : RatFunc K)) + ordDegT y := add_le_add h0 le_rfl
    _ ≤ ordDegT (((n : ℤ) : RatFunc K) * y) := ordDegT_mul_ge _ _

private theorem le_ordDegT_finset_sum {ι : Type*} {s : Finset ι} {f : ι → RatFunc K} {N : ℤ}
    (h : ∀ i ∈ s, (N : WithTop ℤ) ≤ ordDegT (f i)) :
    (N : WithTop ℤ) ≤ ordDegT (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; simp [ordDegT]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      have ha' : (N : WithTop ℤ) ≤ ordDegT (f a) := h a (Finset.mem_insert_self a s)
      have hs' : (N : WithTop ℤ) ≤ ordDegT (∑ i ∈ s, f i) :=
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      calc (N : WithTop ℤ) = min (N : WithTop ℤ) N := by simp
        _ ≤ min (ordDegT (f a)) (ordDegT (∑ i ∈ s, f i)) := min_le_min ha' hs'
        _ ≤ ordDegT (f a + ∑ i ∈ s, f i) := ordDegT_add_ge _ _

private theorem ordDegT_add_eq_of_le_succ {x y : RatFunc K} {N : ℤ}
    (hx : ordDegT x = (N : WithTop ℤ)) (hy : ((N + 1 : ℤ) : WithTop ℤ) ≤ ordDegT y) :
    ordDegT (x + y) = (N : WithTop ℤ) := by
  have hxne : x ≠ 0 := by intro h; rw [h] at hx; simp [ordDegT] at hx
  rcases eq_or_ne y 0 with hy0 | hyne
  · rw [hy0, add_zero]; exact hx
  · have hlt : ordDegT x < ordDegT y := by
      rw [hx]
      exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by omega)) hy
    rw [ordDegT_add_eq_of_lt hxne hyne hlt, hx]


/-! ## The standard derivation and powers of `X` -/

private theorem deriv_X (D : Derivation K (RatFunc K) (RatFunc K))
    (hd : ∀ p : Polynomial K, D (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative) :
    D (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) = 1 := by
  rw [hd Polynomial.X, Polynomial.derivative_X, map_one]

private theorem deriv_X_zpow (D : Derivation K (RatFunc K) (RatFunc K))
    (hd : ∀ p : Polynomial K, D (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative) (k : ℤ) :
    D ((algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ^ k)
      = (k : ℤ) • (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ^ (k - 1) := by
  rw [Derivation.leibniz_zpow, deriv_X D hd]
  simp

private theorem iterate_deriv_X_zpow (D : Derivation K (RatFunc K) (RatFunc K))
    (hd : ∀ p : Polynomial K, D (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative) (e : ℤ) (j : ℕ) :
    ((fun x : RatFunc K => D x)^[j]) ((algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ^ e)
      = (((fallFact e j : ℤ)) : RatFunc K)
        * (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ^ (e - j) := by
  induction j with
  | zero => simp [fallFact]
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
        Derivation.map_intCast, mul_zero, add_zero]
      rw [deriv_X_zpow D hd, zsmul_eq_mul, fallFact_succ]
      push_cast
      ring_nf

private theorem ordDegT_X_zpow (e : ℤ) :
    ordDegT ((algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ^ e)
      = ((-e : ℤ) : WithTop ℤ) := by
  have hX : (algebraMap (Polynomial K) (RatFunc K) Polynomial.X : RatFunc K) ≠ 0 :=
    RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg e
  · rw [zpow_natCast, ← map_pow, ordDegT_algebraMap (pow_ne_zero n Polynomial.X_ne_zero),
      Polynomial.natDegree_X_pow]
    simp
  · rw [zpow_neg, zpow_natCast, ordDegT_inv (pow_ne_zero n hX), ← map_pow,
      ordDegT_algebraMap (pow_ne_zero n Polynomial.X_ne_zero), Polynomial.natDegree_X_pow]
    simp

private theorem le_ordDegT_C_mul_X_zpow (a : K) (e : ℤ) :
    ((-e : ℤ) : WithTop ℤ) ≤ ordDegT
      (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C a)
        * (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ^ e) := by
  by_cases ha : a = 0
  · rw [ha, Polynomial.C_0, map_zero, zero_mul]; simp [ordDegT]
  · have hC0 : (Polynomial.C a : Polynomial K) ≠ 0 := by rwa [Polynomial.C_ne_zero]
    have hC : algebraMap (Polynomial K) (RatFunc K) (Polynomial.C a) ≠ 0 :=
      RatFunc.algebraMap_ne_zero hC0
    have hXe : (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ^ e ≠ 0 :=
      zpow_ne_zero e (RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero)
    calc ((-e : ℤ) : WithTop ℤ)
        = ordDegT (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C a))
            + ordDegT ((algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ^ e) := by
          rw [ordDegT_algebraMap hC0, Polynomial.natDegree_C, ordDegT_X_zpow]
          simp
      _ ≤ _ := ordDegT_mul_ge _ _

/-! ## The derivative raises the order at infinity -/

private theorem one_le_ordDegT_logDeriv (p : Polynomial K) :
    (1 : WithTop ℤ) ≤ ordDegT (algebraMap (Polynomial K) (RatFunc K) p.derivative
        / algebraMap (Polynomial K) (RatFunc K) p) := by
  rcases eq_or_ne p.derivative 0 with h | h
  · rw [h, map_zero, zero_div]; simp [ordDegT]
  · have hp : p ≠ 0 := by intro hp0; exact h (by rw [hp0]; simp)
    have hp' : algebraMap (Polynomial K) (RatFunc K) p.derivative ≠ 0 :=
      RatFunc.algebraMap_ne_zero h
    have hp0 : algebraMap (Polynomial K) (RatFunc K) p ≠ 0 := RatFunc.algebraMap_ne_zero hp
    rw [ordDegT_div hp' hp0, ordDegT_algebraMap h, ordDegT_algebraMap hp,
      ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.LinearOrderedAddCommGroup.coe_neg,
      ← WithTop.LinearOrderedAddCommGroup.coe_sub]
    change ((1 : ℤ) : WithTop ℤ) ≤
      ((-((Polynomial.derivative p).natDegree : ℤ) - -(p.natDegree : ℤ) : ℤ) : WithTop ℤ)
    rw [WithTop.coe_le_coe]
    have hle := Polynomial.natDegree_derivative_le p
    have hp0 : p.natDegree ≠ 0 := fun hc => h (Polynomial.derivative_of_natDegree_zero hc)
    omega

private theorem one_le_ordDegT_logDeriv_sub (h : RatFunc K) :
    (1 : WithTop ℤ) ≤ ordDegT (algebraMap (Polynomial K) (RatFunc K) h.num.derivative
          / algebraMap (Polynomial K) (RatFunc K) h.num
        - algebraMap (Polynomial K) (RatFunc K) h.denom.derivative
          / algebraMap (Polynomial K) (RatFunc K) h.denom) := by
  set A : RatFunc K := algebraMap (Polynomial K) (RatFunc K) h.num.derivative
      / algebraMap (Polynomial K) (RatFunc K) h.num with hA
  set B : RatFunc K := algebraMap (Polynomial K) (RatFunc K) h.denom.derivative
      / algebraMap (Polynomial K) (RatFunc K) h.denom with hB
  have hA1 : (1 : WithTop ℤ) ≤ ordDegT A := one_le_ordDegT_logDeriv h.num
  have hB1 : (1 : WithTop ℤ) ≤ ordDegT B := one_le_ordDegT_logDeriv h.denom
  have := ordDegT_add_ge A (-B)
  rw [ordDegT_neg] at this
  refine le_trans (le_min hA1 hB1) ?_
  rwa [sub_eq_add_neg]

private theorem ordDegT_deriv_lower_bound (D : Derivation K (RatFunc K) (RatFunc K))
    (hd : ∀ p : Polynomial K, D (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative) {h : RatFunc K} (hh : h ≠ 0) :
    ordDegT h + 1 ≤ ordDegT (D h) := by
  rcases eq_or_ne (D h) 0 with h0 | h0
  · rw [h0]; simp [ordDegT]
  · set A : RatFunc K := algebraMap (Polynomial K) (RatFunc K) h.num.derivative
        / algebraMap (Polynomial K) (RatFunc K) h.num with hA
    set B : RatFunc K := algebraMap (Polynomial K) (RatFunc K) h.denom.derivative
        / algebraMap (Polynomial K) (RatFunc K) h.denom with hB
    have hAB : D h = h * (A - B) := by
      rw [deriv_eq_mul_sub_logDeriv D hd hh, ← hA, ← hB]; ring
    have hne : A - B ≠ 0 := by
      intro hz; exact h0 (by rw [hAB, hz, mul_zero])
    rw [hAB, ordDegT_mul hh hne]
    exact add_le_add le_rfl (one_le_ordDegT_logDeriv_sub h)

private theorem ordDegT_iterate_deriv_lower_bound (D : Derivation K (RatFunc K) (RatFunc K))
    (hd : ∀ p : Polynomial K, D (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative) {h : RatFunc K} (hh : h ≠ 0)
    (j : ℕ) :
    ordDegT h + ((j : ℤ) : WithTop ℤ) ≤ ordDegT (((fun x : RatFunc K => D x)^[j]) h) := by
  induction j with
  | zero => rw [Function.iterate_zero, id_eq]; simp
  | succ j ih =>
      rcases eq_or_ne (((fun x : RatFunc K => D x)^[j]) h) 0 with hw | hw
      · rw [Function.iterate_succ_apply', hw]; simp [ordDegT]
      · have hstep := ordDegT_deriv_lower_bound D hd hw
        calc ordDegT h + (((j + 1 : ℕ) : ℤ) : WithTop ℤ)
            = (ordDegT h + ((j : ℤ) : WithTop ℤ)) + 1 := by
                have hX : (((j + 1 : ℕ) : ℤ) : WithTop ℤ) = ((j : ℤ) : WithTop ℤ) + 1 := by
                  rw [Nat.cast_succ, ← WithTop.coe_one, ← WithTop.coe_add]
                rw [hX, add_assoc]
          _ ≤ ordDegT (((fun x : RatFunc K => D x)^[j]) h) + 1 := add_le_add ih le_rfl
          _ ≤ ordDegT (D (((fun x : RatFunc K => D x)^[j]) h)) := hstep
          _ = ordDegT (((fun x : RatFunc K => D x)^[j + 1]) h) := by
              rw [Function.iterate_succ_apply']

/-! ## Indicial exactness: leading-term analysis at infinity -/

private theorem ordDegT_iterate_deriv_leading (D : Derivation K (RatFunc K) (RatFunc K))
    (hd : ∀ p : Polynomial K, D (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative)
    {c : K} {f : RatFunc K} {k : ℤ}
    (hres : ((k + 1 : ℤ) : WithTop ℤ) ≤ ordDegT
      (f - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C c)
        * (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ^ (-k)))
    (j : ℕ) :
    (((k + (j : ℤ) + 1 : ℤ)) : WithTop ℤ) ≤ ordDegT
      (((fun x : RatFunc K => D x)^[j]) f
        - algebraMap (Polynomial K) (RatFunc K)
            (Polynomial.C (c * ((fallFact (-k) j : ℤ) : K)))
          * (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ^ (-k - (j : ℤ))) := by
  set g : RatFunc K := f - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C c)
      * (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ^ (-k) with hg
  have key : ((fun x : RatFunc K => D x)^[j]) g
      = ((fun x : RatFunc K => D x)^[j]) f
        - algebraMap (Polynomial K) (RatFunc K)
            (Polynomial.C (c * ((fallFact (-k) j : ℤ) : K)))
          * (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ^ (-k - (j : ℤ)) := by
    rw [hg, iterate_map_sub, iterate_deriv_C_mul hd, iterate_deriv_X_zpow D hd,
      intCast_eq_algebraMap_C, ← mul_assoc, ← map_mul, ← Polynomial.C_mul]
  rw [← key]
  rcases eq_or_ne g 0 with hg0 | hg0
  · rw [hg0, Function.iterate_fixed (map_zero D)]; simp [ordDegT]
  · have hg1 : ((k + 1 : ℤ) : WithTop ℤ) ≤ ordDegT g := by rw [hg]; exact hres
    have hiter := ordDegT_iterate_deriv_lower_bound D hd hg0 j
    refine le_trans ?_ hiter
    calc (((k + (j : ℤ) + 1 : ℤ)) : WithTop ℤ)
        = ((k + 1 : ℤ) : WithTop ℤ) + ((j : ℤ) : WithTop ℤ) := by
            rw [← WithTop.coe_add]; congr 1; ring
      _ ≤ ordDegT g + ((j : ℤ) : WithTop ℤ) := add_le_add hg1 le_rfl

private theorem ordDegT_leading_residual_mul {γ f : RatFunc K} {e N : ℤ} {lam r : K}
    (hγ : ((e + 1 : ℤ) : WithTop ℤ) ≤ ordDegT
      (γ - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C lam)
        * (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ^ (-e)))
    (hf : ordDegT f = (N : WithTop ℤ))
    (hfr : ((N + 1 : ℤ) : WithTop ℤ) ≤ ordDegT
      (f - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C r)
        * (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ^ (-N))) :
    ((N + e + 1 : ℤ) : WithTop ℤ) ≤ ordDegT
      (γ * f - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (lam * r))
        * (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ^ (-(N + e))) := by
  have hZ : (algebraMap (Polynomial K) (RatFunc K) Polynomial.X : RatFunc K) ≠ 0 :=
    RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero
  have hsplit : γ * f - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (lam * r))
        * (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ^ (-(N + e))
      = (γ - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C lam)
            * (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ^ (-e)) * f
        + algebraMap (Polynomial K) (RatFunc K) (Polynomial.C lam)
            * (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ^ (-e)
          * (f - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C r)
              * (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ^ (-N)) := by
    rw [show -(N + e) = (-e) + (-N) by ring, zpow_add₀ hZ (-e) (-N), Polynomial.C_mul, map_mul]
    ring
  rw [hsplit]
  refine le_trans (le_min ?_ ?_) (ordDegT_add_ge _ _)
  · have heq : ((N + e + 1 : ℤ) : WithTop ℤ)
        = ((e + 1 : ℤ) : WithTop ℤ) + (N : WithTop ℤ) := by
      rw [← WithTop.coe_add]; congr 1; ring
    refine le_trans (le_of_eq heq) ?_
    exact le_trans (add_le_add hγ (le_of_eq hf.symm)) (ordDegT_mul_ge _ f)
  · have heq : ((N + e + 1 : ℤ) : WithTop ℤ)
        = (e : WithTop ℤ) + ((N + 1 : ℤ) : WithTop ℤ) := by
      rw [← WithTop.coe_add]; congr 1; ring
    refine le_trans (le_of_eq heq) ?_
    have hle := le_ordDegT_C_mul_X_zpow lam (-e)
    simp only [neg_neg] at hle
    exact le_trans (add_le_add hle hfr) (ordDegT_mul_ge _ _)

private theorem ordDegT_iterate_deriv_mul_leading (D : Derivation K (RatFunc K) (RatFunc K))
    (hd : ∀ p : Polynomial K, D (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative)
    {γ f : RatFunc K} {e N : ℤ} {lam r : K}
    (hγ : ((e + 1 : ℤ) : WithTop ℤ) ≤ ordDegT
      (γ - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C lam)
        * (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ^ (-e)))
    (hf : ordDegT f = (N : WithTop ℤ))
    (hfr : ((N + 1 : ℤ) : WithTop ℤ) ≤ ordDegT
      (f - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C r)
        * (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ^ (-N)))
    (j : ℕ) :
    (((N + e + (j : ℤ) + 1 : ℤ)) : WithTop ℤ) ≤ ordDegT
      (((fun x : RatFunc K => D x)^[j]) (γ * f)
        - algebraMap (Polynomial K) (RatFunc K)
            (Polynomial.C (lam * r * ((fallFact (-(N + e)) j : ℤ) : K)))
          * (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ^ (-(N + e) - (j : ℤ))) := by
  have h1 := ordDegT_leading_residual_mul (γ := γ) (f := f) (e := e) (N := N)
    (lam := lam) (r := r) hγ hf hfr
  exact ordDegT_iterate_deriv_leading (D := D) hd (c := lam * r) (f := γ * f) (k := N + e) h1 j

private theorem ordDegT_iterate_deriv_mul_ge (D : Derivation K (RatFunc K) (RatFunc K))
    (hd : ∀ p : Polynomial K, D (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative)
    (γ f : RatFunc K) (hf : f ≠ 0) (j : ℕ) :
    ordDegT γ + ordDegT f + ((j : ℤ) : WithTop ℤ)
      ≤ ordDegT (((fun x : RatFunc K => D x)^[j]) (γ * f)) := by
  rcases eq_or_ne γ 0 with hγ | hγ
  · subst hγ
    rw [zero_mul, Function.iterate_fixed (map_zero D)]
    simp [ordDegT]
  · have hh : γ * f ≠ 0 := mul_ne_zero hγ hf
    have hiter := ordDegT_iterate_deriv_lower_bound D hd hh j
    rw [ordDegT_mul hγ hf] at hiter
    exact hiter


/-- **Indicial exactness at the point `∞` of the projective line.** -/
theorem ordDegT_adjoint_eq_of_indicial {K : Type*} [Field K]
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hd : ∀ p : Polynomial K, D (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative)
    (b : RatFunc K) (hb : b ≠ 0) (N : ℤ) (hN : ordDegT b = (N : WithTop ℤ)) (r : K) (hr : r ≠ 0)
    (hb' : ((N + 1 : ℤ) : WithTop ℤ) ≤ ordDegT
      (b - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C r)
        * (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ^ (-N)))
    (γ : Fin 5 → RatFunc K) (e : Fin 5 → ℤ) (lam : Fin 5 → K) (m : ℤ)
    (he : ∀ i : Fin 5, e i + ((i : ℕ) : ℤ) ≠ m → ((e i : ℤ) : WithTop ℤ) ≤ ordDegT (γ i))
    (hm : ∀ i : Fin 5, m ≤ e i + ((i : ℕ) : ℤ))
    (hlam : ∀ i : Fin 5, e i + ((i : ℕ) : ℤ) = m → (((e i + 1 : ℤ)) : WithTop ℤ) ≤ ordDegT
      (γ i - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (lam i))
        * (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ^ (-(e i))))
    (hP : (∑ i ∈ Finset.univ.filter (fun i : Fin 5 => e i + ((i : ℕ) : ℤ) = m),
        (-1 : ℤ) ^ (i : ℕ) • (lam i * ∏ j ∈ Finset.range (i : ℕ),
          ((-(N + e i + (j : ℤ)) : ℤ) : K))) ≠ 0) :
    ordDegT (∑ i : Fin 5, (-1 : ℤ) ^ (i : ℕ) •
      ((fun x : RatFunc K => D x)^[i] (γ i * b)))
      = ((N + m : ℤ) : WithTop ℤ) := by
  classical
  have hXne : (algebraMap (Polynomial K) (RatFunc K) Polynomial.X : RatFunc K) ≠ 0 :=
    RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero
  have hprod : ∀ i : Fin 5, (∏ j ∈ Finset.range (i : ℕ), ((-(N + e i + (j : ℤ)) : ℤ) : K))
      = ((fallFact (-(N + e i)) ((i : ℕ)) : ℤ) : K) := by
    intro i
    rw [fallFact, Int.cast_prod]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [show (-(N + e i) - (j : ℤ) : ℤ) = -(N + e i + (j : ℤ)) from by ring]
  have hPne : (∑ i ∈ Finset.univ.filter (fun i : Fin 5 => e i + ((i : ℕ) : ℤ) = m),
      (-1 : ℤ) ^ (i : ℕ) • (lam i * ((fallFact (-(N + e i)) ((i : ℕ)) : ℤ) : K))) ≠ 0 := by
    simpa only [hprod] using hP
  let FF : Fin 5 → K := fun i => ((fallFact (-(N + e i)) ((i : ℕ)) : ℤ) : K)
  let F : Finset (Fin 5) := Finset.univ.filter (fun i : Fin 5 => e i + ((i : ℕ) : ℤ) = m)
  let V : K := ∑ i ∈ F, (-1 : ℤ) ^ (i : ℕ) • (lam i * FF i)
  have hVne : V ≠ 0 := hPne
  let c : Fin 5 → K := fun i => (-1 : ℤ) ^ (i : ℕ) • (lam i * r * FF i)
  let T : Fin 5 → RatFunc K := fun i =>
      (-1 : ℤ) ^ (i : ℕ) • ((fun x : RatFunc K => D x)^[i] (γ i * b))
  let W : RatFunc K := algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (r * V))
      * (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ^ (-(N + m))
  let g : Fin 5 → RatFunc K := fun i => if e i + ((i : ℕ) : ℤ) = m then
      T i - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (c i))
        * (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ^ (-(N + m)) else T i
  have hExp : ∀ i : Fin 5, e i + ((i : ℕ) : ℤ) = m → ((N + m + 1 : ℤ) : WithTop ℤ) ≤ ordDegT
      (((fun x : RatFunc K => D x)^[i]) (γ i * b)
        - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (lam i * r * FF i))
          * (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ^ (-(N + m))) := by
    intro i hcond
    have h := ordDegT_iterate_deriv_mul_leading (D := D) hd (γ := γ i) (f := b)
      (e := e i) (N := N) (lam := lam i) (r := r) (hlam i hcond) hN hb' (i : ℕ)
    have heq : (N + e i + ((i : ℕ) : ℤ) + 1 : ℤ) = N + m + 1 := by omega
    have heq2 : (-(N + e i) - ((i : ℕ) : ℤ) : ℤ) = -(N + m) := by omega
    rw [heq, heq2] at h
    exact h
  have hgle : ∀ i : Fin 5, ((N + m + 1 : ℤ) : WithTop ℤ) ≤ ordDegT (g i) := by
    intro i
    by_cases hcond : e i + ((i : ℕ) : ℤ) = m
    · have hexp : ((N + m + 1 : ℤ) : WithTop ℤ) ≤ ordDegT
          (((fun x : RatFunc K => D x)^[i]) (γ i * b)
            - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (lam i * r * FF i))
              * (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ^ (-(N + m))) :=
        hExp i hcond
      have hgi : g i = (((-1 : ℤ) ^ (i : ℕ) : ℤ) : RatFunc K)
          * ((((fun x : RatFunc K => D x)^[i]) (γ i * b)
            - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (lam i * r * FF i))
              * (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ^ (-(N + m)))) := by
        have hgu : g i = T i - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (c i))
            * (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ^ (-(N + m)) := by
          simp only [g]; exact if_pos hcond
        rw [hgu, show c i = (-1 : ℤ) ^ (i : ℕ) • (lam i * r * FF i) from rfl,
          algebraMap_C_zsmul]
        simp only [T, zsmul_eq_mul]
        ring
      rw [hgi]
      have h0 : (0 : WithTop ℤ) ≤ ordDegT (((-1 : ℤ) ^ (i : ℕ) : ℤ) : RatFunc K) :=
        zero_le_ordDegT_intCast _
      refine le_trans (le_of_eq ?_)
        (le_trans (add_le_add h0 hexp) (ordDegT_mul_ge _ _))
      rw [zero_add]
    · have hexp : ((N + m + 1 : ℤ) : WithTop ℤ) ≤ ordDegT
          (((fun x : RatFunc K => D x)^[i]) (γ i * b)) := by
        have hge := ordDegT_iterate_deriv_mul_ge (D := D) hd (γ i) b hb (i : ℕ)
        rw [hN] at hge
        have hei : ((e i : ℤ) : WithTop ℤ) ≤ ordDegT (γ i) := he i hcond
        have hlt : m + 1 ≤ e i + ((i : ℕ) : ℤ) := by
          rcases lt_trichotomy (e i + ((i : ℕ) : ℤ)) m with h | h | h
          · exact absurd (le_antisymm (le_of_lt h) (hm i)) hcond
          · exact absurd h hcond
          · linarith
        have hle1 : ((N + m + 1 : ℤ) : WithTop ℤ)
            ≤ ((e i : ℤ) : WithTop ℤ) + (N : WithTop ℤ) + (((i : ℕ) : ℤ) : WithTop ℤ) := by
          rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
          linarith
        have hle2 : ((e i : ℤ) : WithTop ℤ) + (N : WithTop ℤ) + (((i : ℕ) : ℤ) : WithTop ℤ)
            ≤ ordDegT (γ i) + (N : WithTop ℤ) + (((i : ℕ) : ℤ) : WithTop ℤ) :=
          add_le_add (add_le_add hei le_rfl) le_rfl
        exact le_trans (le_trans hle1 hle2) hge
      have h2 : ordDegT (((fun x : RatFunc K => D x)^[i]) (γ i * b)) ≤ ordDegT (T i) := by
        have hTi : T i = (((-1 : ℤ) ^ (i : ℕ) : ℤ) : RatFunc K)
            * (((fun x : RatFunc K => D x)^[i]) (γ i * b)) := by
          simp only [T, zsmul_eq_mul]
        rw [hTi]
        exact le_ordDegT_mul_intCast _ _
      rw [show g i = T i from by simp only [g]; exact if_neg hcond]
      exact le_trans hexp h2
  have hcV : (∑ i ∈ F, c i) = r * V := by
    show (∑ i ∈ F, (-1 : ℤ) ^ (i : ℕ) • (lam i * r * FF i))
      = r * (∑ i ∈ F, (-1 : ℤ) ^ (i : ℕ) • (lam i * FF i))
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [zsmul_eq_mul]
    ring
  have hsum : (∑ i : Fin 5, g i) = (∑ i : Fin 5, T i) - W := by
    have hg' : ∀ i : Fin 5, g i = T i - (if e i + ((i : ℕ) : ℤ) = m then
        algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (c i))
          * (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ^ (-(N + m)) else 0) := by
      intro i
      by_cases h : e i + ((i : ℕ) : ℤ) = m <;> simp [g, h]
    rw [Finset.sum_congr rfl (fun i _ => hg' i), Finset.sum_sub_distrib]
    congr 1
    show (∑ i : Fin 5, (if e i + ((i : ℕ) : ℤ) = m then
        algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (c i))
          * (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ^ (-(N + m)) else 0)) = W
    show _ = algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (r * V))
        * (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ^ (-(N + m))
    rw [← Finset.sum_filter, ← Finset.sum_mul]
    congr 1
    rw [← map_sum (algebraMap (Polynomial K) (RatFunc K)) (fun i => Polynomial.C (c i)) _]
    congr 1
    simp only [Polynomial.C_eq_algebraMap]
    rw [← map_sum (algebraMap K (Polynomial K)) (fun i => c i) _, hcV]
  have hW : ordDegT W = ((N + m : ℤ) : WithTop ℤ) := by
    show ordDegT (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (r * V))
        * (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ^ (-(N + m))) = _
    have hC0 : (Polynomial.C (r * V) : Polynomial K) ≠ 0 := by
      rw [Polynomial.C_ne_zero]; exact mul_ne_zero hr hVne
    have hC : algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (r * V)) ≠ 0 :=
      RatFunc.algebraMap_ne_zero hC0
    rw [ordDegT_mul hC (zpow_ne_zero _ hXne), ordDegT_algebraMap hC0,
      Polynomial.natDegree_C, ordDegT_X_zpow]
    simp
  have hgl : ((N + m + 1 : ℤ) : WithTop ℤ) ≤ ordDegT (∑ i : Fin 5, g i) :=
    le_ordDegT_finset_sum (fun i _ => hgle i)
  have hsum' : (∑ i : Fin 5, T i) = W + ∑ i : Fin 5, g i := by
    rw [hsum]; abel
  change ordDegT (∑ i : Fin 5, T i) = ((N + m : ℤ) : WithTop ℤ)
  rw [hsum']
  exact ordDegT_add_eq_of_le_succ hW hgl

end Commons.FieldTheory.RatFunc
