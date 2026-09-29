import Mathlib
import Submission.Work.ConvR.basic
import Submission.Work.SynFFT.yMulFacts
import Submission.Work.ConvR.negaMulLin

/-!
# `y^e · (a·b) = (y^e·a)·b` in `R = ℂ[y]/(y^r+1)`

`HvdH.yMul r e` is multiplication by `y^e` in `R = ℂ[y]/(y^r+1)` and `HvdH.negaMul` is the
product.  This file proves `yMulNegMulAlt` (`y^e·(a·b) = (y^e·a)·b`), the ring-theoretic
statement needed to move powers of `y` through products in the synthetic
DFT/convolution computation (`Work.ConvR.convIdentity`).

The proof avoids any explicit formula for `yMul` by working with the *antiperiodic lift*
`alift x m = (y^{-m} x) 0` (`= (-1)^⌊m/r⌋ x_{m mod r}`), a coefficient vector extended to
integers so that `y` acts by the shift `m ↦ m+1`:

* `alift_nat`: for `0 ≤ n < r` the lift is the original coefficient;
* `alift_flip`, `alift_period`, `alift_period'`, `alift_mod`: antiperiodicity (`m ↦ m+r`
  changes the sign) and periodicity (`2r`);
* `alift_yMul`: shifting the exponent shifts the argument (pure composition law for `yMul`);
* `negaMul_eq_alift`, `alift_negaMul`: the product is the convolution of the lifts.

With these, both sides of `y^e·(a·b) = a·(y^e·b)` are `∑ i, a i · alift b (k - e - i)`, and the
stated form follows by commutativity of `negaMul` (`Work.ConvR.negaMulLin`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.ConvR

open HvdH

/-- The antiperiodic lift of a coefficient vector: `alift x m` is the coefficient of `y^0` in
`y^{-m} x`, i.e. `(-1)^⌊m/r⌋ x_{m mod r}`. -/
noncomputable def alift (r : ℕ) (hr : 0 < r) (x : Fin r → ℂ) (m : ℤ) : ℂ :=
  HvdH.yMul r (-m) x ⟨0, hr⟩

/-- Value of the lift at `0 ≤ n < r`. -/
theorem alift_nat (r : ℕ) (hr : 0 < r) (x : Fin r → ℂ) (n : ℕ) (hn : n < r) :
    alift r hr x (n : ℤ) = x ⟨n, hn⟩ := by
  dsimp only [alift, HvdH.yMul]
  simp only [Nat.cast_zero]
  have hmod : (((0 : ℤ) - (-(n : ℤ))) % (r : ℤ)) = (n : ℤ) := by
    rw [show (0 : ℤ) - (-(n : ℤ)) = (n : ℤ) by ring]
    exact Int.emod_eq_of_lt (Int.natCast_nonneg n) (by exact_mod_cast hn)
  rw [hmod]
  have hq : (((n : ℤ)) + (-(n : ℤ)) - 0) / (r : ℤ) = 0 := by simp
  rw [hq]
  simp only [Int.toNat_natCast, HvdH.vget, hn, dite_eq_left, Even.zero, ↓reduceIte]
  rw [one_mul]

/-- `yMul r e (-x) = -(yMul r e x)`. -/
theorem yMul_neg (r : ℕ) (hr : 0 < r) (e : ℤ) (x : Fin r → ℂ) :
    HvdH.yMul r e (-x) = -HvdH.yMul r e x := by
  have h := (Work.SynFFT.yMulFacts r hr).2.2.2.1 e (-1 : ℂ) x
  simpa using h

/-- `yMul r (-r) = -id`. -/
theorem yMul_neg_r (r : ℕ) (hr : 0 < r) (x : Fin r → ℂ) :
    HvdH.yMul r (-(r : ℤ)) x = -x := by
  have h := (Work.SynFFT.yMulFacts r hr).1 (r : ℤ) (-(r : ℤ)) x
  rw [show (r : ℤ) + (-(r : ℤ)) = 0 by ring, (Work.SynFFT.yMulFacts r hr).2.1] at h
  rw [(Work.SynFFT.yMulFacts r hr).2.2.2.2.2.2.2] at h
  simpa only [neg_neg] using (congrArg Neg.neg h).symm

/-- `alift` is antiperiodic with antiperiod `r`. -/
theorem alift_flip (r : ℕ) (hr : 0 < r) (x : Fin r → ℂ) (m : ℤ) :
    alift r hr x (m + (r : ℤ)) = -alift r hr x m := by
  simp only [alift]
  rw [show -(m + (r : ℤ)) = (-m) + (-(r : ℤ)) by ring,
    (Work.SynFFT.yMulFacts r hr).1 (-m) (-(r : ℤ)) x, yMul_neg_r r hr x, yMul_neg r hr (-m) x]
  simp only [Pi.neg_apply]

/-- `alift x (m - r) = - alift x m`. -/
theorem alift_sub_r (r : ℕ) (hr : 0 < r) (x : Fin r → ℂ) (m : ℤ) :
    alift r hr x (m - (r : ℤ)) = -alift r hr x m := by
  have h := alift_flip r hr x (m - (r : ℤ))
  rw [show m - (r : ℤ) + (r : ℤ) = m by ring] at h
  have h2 := congrArg Neg.neg h
  simp only [neg_neg] at h2
  exact h2.symm

/-- `alift` has period `2r`. -/
theorem alift_period (r : ℕ) (hr : 0 < r) (x : Fin r → ℂ) (m : ℤ) :
    alift r hr x (m + 2 * (r : ℤ)) = alift r hr x m := by
  rw [show m + 2 * (r : ℤ) = (m + (r : ℤ)) + (r : ℤ) by ring, alift_flip, alift_flip, neg_neg]

/-- Period `2r·n` for any integer `n`. -/
theorem alift_period' (r : ℕ) (hr : 0 < r) (x : Fin r → ℂ) (m n : ℤ) :
    alift r hr x (m + 2 * (r : ℤ) * n) = alift r hr x m := by
  induction n using Int.induction_on with
  | zero => rw [mul_zero, add_zero]
  | succ i ih =>
      rw [show m + 2 * (r : ℤ) * ((i : ℤ) + 1) = (m + 2 * (r : ℤ) * (i : ℤ)) + 2 * (r : ℤ)
        by ring, alift_period, ih]
  | pred i ih =>
      rw [show m + 2 * (r : ℤ) * (-(i : ℤ) - 1)
        = (m + 2 * (r : ℤ) * (-(i : ℤ))) - 2 * (r : ℤ) by ring]
      have h := alift_period r hr x ((m + 2 * (r : ℤ) * (-(i : ℤ))) - 2 * (r : ℤ))
      rw [show (m + 2 * (r : ℤ) * (-(i : ℤ))) - 2 * (r : ℤ) + 2 * (r : ℤ)
        = m + 2 * (r : ℤ) * (-(i : ℤ)) by ring] at h
      rw [← h, ih]

/-- `alift` depends only on `m % 2r`. -/
theorem alift_mod (r : ℕ) (hr : 0 < r) (x : Fin r → ℂ) (m : ℤ) :
    alift r hr x m = alift r hr x (m % (2 * (r : ℤ))) := by
  have h := alift_period' r hr x (m % (2 * (r : ℤ))) (m / (2 * (r : ℤ)))
  have key : m % (2 * (r : ℤ)) + 2 * (r : ℤ) * (m / (2 * (r : ℤ))) = m := by
    have := Int.emod_add_mul_ediv m (2 * (r : ℤ)); omega
  rw [key] at h
  exact h

/-- Shifting the argument shifts the lift. -/
theorem alift_yMul (r : ℕ) (hr : 0 < r) (e : ℤ) (x : Fin r → ℂ) (m : ℤ) :
    alift r hr (HvdH.yMul r e x) m = alift r hr x (m - e) := by
  simp only [alift]
  rw [← (Work.SynFFT.yMulFacts r hr).1 (-m) e x]
  congr 1
  ring

/-- The product in `R`, written as a convolution against the lift of the second factor. -/
theorem negaMul_eq_alift (r : ℕ) (hr : 0 < r) (a b : Fin r → ℂ) (k : Fin r) :
    HvdH.negaMul r a b k = ∑ i : Fin r, a i * alift r hr b ((k : ℤ) - (i : ℤ)) := by
  simp only [HvdH.negaMul]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hle : (i : ℕ) ≤ (k : ℕ)
  · have hjlt : (k : ℕ) - (i : ℕ) < r := by omega
    rw [Finset.sum_eq_single (⟨(k : ℕ) - (i : ℕ), hjlt⟩ : Fin r)]
    · have h1 : (i : ℕ) + ((⟨(k : ℕ) - (i : ℕ), hjlt⟩ : Fin r) : ℕ) = (k : ℕ) := by
        simp only [Fin.val_mk]; omega
      rw [ite_eq_left h1]
      congr 1
      rw [show (k : ℤ) - (i : ℤ) = (((k : ℕ) - (i : ℕ) : ℕ) : ℤ) by omega,
        alift_nat r hr b ((k : ℕ) - (i : ℕ)) hjlt]
    · intro j _ hj
      have hne : ((j : ℕ)) ≠ (k : ℕ) - (i : ℕ) := fun h => hj (Fin.ext h)
      have hc1 : ¬ ((i : ℕ) + (j : ℕ) = (k : ℕ)) := fun h => hne (by omega)
      have hc2 : ¬ ((i : ℕ) + (j : ℕ) = (k : ℕ) + r) := fun h => by omega
      rw [ite_eq_right hc1, ite_eq_right hc2]
    · intro h; exact absurd (Finset.mem_univ _) h
  · have hlt : (k : ℕ) < (i : ℕ) := not_le.mp hle
    have hjlt : (k : ℕ) + r - (i : ℕ) < r := by omega
    rw [Finset.sum_eq_single (⟨(k : ℕ) + r - (i : ℕ), hjlt⟩ : Fin r)]
    · have hc1 : ¬ ((i : ℕ) + ((⟨(k : ℕ) + r - (i : ℕ), hjlt⟩ : Fin r) : ℕ) = (k : ℕ)) := by
        simp only [Fin.val_mk]; omega
      have h2 : (i : ℕ) + ((⟨(k : ℕ) + r - (i : ℕ), hjlt⟩ : Fin r) : ℕ) = (k : ℕ) + r := by
        simp only [Fin.val_mk]; omega
      rw [ite_eq_right hc1, ite_eq_left h2]
      rw [show (k : ℤ) - (i : ℤ)
          = (((k : ℕ) + r - (i : ℕ) : ℕ) : ℤ) - (r : ℤ) by omega,
        alift_sub_r r hr b ((((k : ℕ) + r - (i : ℕ) : ℕ) : ℤ)),
        alift_nat r hr b ((k : ℕ) + r - (i : ℕ)) hjlt]
      ring
    · intro j _ hj
      have hne : ((j : ℕ)) ≠ (k : ℕ) + r - (i : ℕ) := fun h => hj (Fin.ext h)
      have hc1 : ¬ ((i : ℕ) + (j : ℕ) = (k : ℕ)) := fun h => by omega
      have hc2 : ¬ ((i : ℕ) + (j : ℕ) = (k : ℕ) + r) := fun h => hne (by omega)
      rw [ite_eq_right hc1, ite_eq_right hc2]
    · intro h; exact absurd (Finset.mem_univ _) h

/-- The convolution formula for the lift of a product, for every integer index. -/
theorem alift_negaMul (r : ℕ) (hr : 0 < r) (a b : Fin r → ℂ) (m : ℤ) :
    alift r hr (HvdH.negaMul r a b) m = ∑ i : Fin r, a i * alift r hr b (m - (i : ℤ)) := by
  set m' := m % (2 * (r : ℤ)) with hm'
  have h0 : 0 ≤ m' := Int.emod_nonneg m (by positivity)
  have h2r : m' < 2 * (r : ℤ) := Int.emod_lt_of_pos m (by positivity)
  have hL : alift r hr (HvdH.negaMul r a b) m = alift r hr (HvdH.negaMul r a b) m' := by
    rw [alift_mod]
  have hR : (∑ i : Fin r, a i * alift r hr b (m - (i : ℤ)))
      = ∑ i : Fin r, a i * alift r hr b (m' - (i : ℤ)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    have key : m - (i : ℤ) = (m' - (i : ℤ)) + 2 * (r : ℤ) * (m / (2 * (r : ℤ))) := by
      have h := Int.emod_add_mul_ediv m (2 * (r : ℤ))
      rw [← hm'] at h
      omega
    rw [key, alift_period']
  rw [hL, hR]
  rcases lt_or_ge m' (r : ℤ) with hm | hm
  · have hlt : m'.toNat < r := by
      rw [Int.toNat_lt h0]; exact hm
    have hcast : ((m'.toNat : ℕ) : ℤ) = m' := Int.toNat_of_nonneg h0
    rw [← hcast, alift_nat r hr (HvdH.negaMul r a b) m'.toNat hlt,
      negaMul_eq_alift r hr a b ⟨m'.toNat, hlt⟩]
  · set q := m' - (r : ℤ) with hq
    have hq0 : 0 ≤ q := by omega
    have hqlt : q < (r : ℤ) := by omega
    have hqnat : q.toNat < r := by rw [Int.toNat_lt hq0]; exact hqlt
    have hcast : ((q.toNat : ℕ) : ℤ) = q := Int.toNat_of_nonneg hq0
    have hsplit : m' = q + (r : ℤ) := by omega
    rw [hsplit, alift_flip r hr (HvdH.negaMul r a b) q, ← hcast,
      alift_nat r hr (HvdH.negaMul r a b) q.toNat hqnat,
      negaMul_eq_alift r hr a b ⟨q.toNat, hqnat⟩]
    have hstep : (∑ i : Fin r, a i * alift r hr b (((q.toNat : ℕ) : ℤ) + (r : ℤ) - (i : ℤ)))
        = -∑ i : Fin r, a i * alift r hr b (((q.toNat : ℕ) : ℤ) - (i : ℤ)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show ((q.toNat : ℕ) : ℤ) + (r : ℤ) - (i : ℤ)
          = (((q.toNat : ℕ) : ℤ) - (i : ℤ)) + (r : ℤ) by ring, alift_flip]
      ring
    rw [hstep]

/-- `y^e · (a·b) = a · (y^e·b)` in `R = ℂ[y]/(y^r+1)`. -/
theorem yMul_negaMul_symm (r : ℕ) (hr : 0 < r) (e : ℤ) (a b : Fin r → ℂ) :
    HvdH.yMul r e (HvdH.negaMul r a b) = HvdH.negaMul r a (HvdH.yMul r e b) := by
  funext k
  rw [← alift_nat r hr (HvdH.yMul r e (HvdH.negaMul r a b)) (k : ℕ) k.isLt,
    alift_yMul, alift_negaMul r hr a b ((k : ℤ) - e),
    negaMul_eq_alift r hr a (HvdH.yMul r e b) k]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [alift_yMul]
  ring

/-- Multiplication by `y^e` in `R = ℂ[y]/(y^r+1)` commutes with the product. -/
theorem yMulNegMulAlt (r : ℕ) (hr : 0 < r) (e : ℤ) (a b : Fin r → ℂ) :
    HvdH.yMul r e (HvdH.negaMul r a b) = HvdH.negaMul r (HvdH.yMul r e a) b := by
  calc HvdH.yMul r e (HvdH.negaMul r a b)
      = HvdH.yMul r e (HvdH.negaMul r b a) := by rw [negaMulLin.1 r a b]
    _ = HvdH.negaMul r b (HvdH.yMul r e a) := yMul_negaMul_symm r hr e b a
    _ = HvdH.negaMul r (HvdH.yMul r e a) b := negaMulLin.1 r b (HvdH.yMul r e a)

end Work.ConvR
