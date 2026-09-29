import Mathlib
import Submission.Work.SynFFT.defs
import Submission.Work.SynFFT.yMulExpAdd

/-!
# `multiCons`: the multivariate synthetic transform splits along the first axis

The synthetic transform `dftMultiN r (t :: ts) sgn` of a flat lexicographic array of shape
`t × B` (`B = ts.prod`) is the one-dimensional synthetic transform of length `t` along the first
axis of the array of `B`-blocks, each block being transformed by `dftMultiN r ts sgn`.

This is the `synExp`-additivity statement behind the multivariate (tensor) factorisation of the
synthetic DFT: for `p < t * B` the mixed-radix digits of `p` split as
`digits (t :: ts) p = (p / B) :: digits ts (p % B)`, the index `u * B + w` splits as
`u :: digits ts w`, and

`synExp r (t :: ts) (j₁ :: js) (k₁ :: ks)`
  `= (2 * r / t * j₁ * k₁) + synExp r ts js ks`

is a sum of the one-dimensional phase and the phase of the remaining coordinates.  The whole
statement is therefore a single application of `yMul`-additivity in the exponent
(`Work.SynFFT.yMulExpAdd`) plus a rearrangement of the double sum over `range (t * B)` into
blocks `range t × range B`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.SynFFT

open HvdH
open scoped BigOperators

/-! ## Pointwise form of `yMul` and its linearity in the vector argument -/

/-- Unfolded (pointwise) form of `yMul`: the sign and the source index depend only on `k` and `e`,
not on the vector `a`. -/
lemma yMulPt (r : ℕ) (e : ℤ) (a : Fin r → ℂ) (k : Fin r) :
    yMul r e a k =
      (if Even ((((k : ℤ) - e) % (r : ℤ) + e - (k : ℤ)) / (r : ℤ)) then (1 : ℂ) else -1) *
        vget a ((((k : ℤ) - e) % (r : ℤ)).toNat) := rfl

lemma vgetSmul {n : ℕ} (u : Fin n → ℂ) (c : ℂ) (i : ℕ) :
    vget (c • u) i = c * vget u i := by
  by_cases h : i < n <;> simp [vget, h, Pi.smul_apply, smul_eq_mul]

lemma vgetSum {n : ℕ} (s : Finset ℕ) (f : ℕ → Fin n → ℂ) (i : ℕ) :
    vget (∑ i' ∈ s, f i') i = ∑ i' ∈ s, vget (f i') i := by
  by_cases h : i < n
  · simp only [vget, h, dite_eq_left]
    rw [Finset.sum_apply]
  · simp [vget, h]

lemma yMulSmulLoc (r : ℕ) (e : ℤ) (c : ℂ) (a : Fin r → ℂ) :
    yMul r e (c • a) = c • yMul r e a := by
  funext k
  simp only [yMulPt, Pi.smul_apply, smul_eq_mul, vgetSmul]
  ring

lemma yMulSumLoc (r : ℕ) (e : ℤ) (s : Finset ℕ) (f : ℕ → Fin r → ℂ) :
    yMul r e (∑ i ∈ s, f i) = ∑ i ∈ s, yMul r e (f i) := by
  funext k
  simp only [yMulPt, Finset.sum_apply, vgetSum, Finset.mul_sum]

/-! ## Elementary unfolding lemmas -/

lemma digits_cons (t : ℕ) (ts : List ℕ) (m : ℕ) :
    digits (t :: ts) m = (m / ts.prod) % t :: digits ts (m % ts.prod) := rfl

lemma synExp_cons (r t : ℕ) (ts js ks : List ℕ) (j k : ℕ) :
    synExp r (t :: ts) (j :: js) (k :: ks) =
      ((2 * r / t * j * k : ℕ) : ℤ) + synExp r ts js ks := rfl

/-- `dftMultiN` as a scalar multiple of a `yMul`-weighted sum of the input entries. -/
lemma dftMultiN_eq_smul_sum (r : ℕ) (ts : List ℕ) (sgn : ℤ) (g : ℕ → Fin r → ℂ) (m : ℕ) :
    (fun c => dftMultiN r ts sgn g m c) = (1 / (ts.prod : ℂ)) •
      (∑ w ∈ Finset.range ts.prod,
        yMul r (sgn * synExp r ts (digits ts m) (digits ts w)) (g w)) := by
  funext c
  simp only [dftMultiN, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]

/-- Splitting a sum over `range (t * B)` into blocks of size `B`. -/
lemma sum_range_mul {M : Type*} [AddCommMonoid M] (t B : ℕ) (f : ℕ → M) :
    ∑ k ∈ Finset.range (t * B), f k =
      ∑ u ∈ Finset.range t, ∑ w ∈ Finset.range B, f (u * B + w) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-! ## The main statement -/

set_option linter.unusedVariables false in
theorem multiCons (r t : ℕ) (ts : List ℕ) (sgn : ℤ) (a : Arr r)
    (ht : 0 < t) (hpos : ∀ u ∈ ts, 0 < u) :
    ∀ p : ℕ, p < t * ts.prod →
      dftMultiN r (t :: ts) sgn a p =
        axisT r t ts.prod sgn
          (fun q c => dftMultiN r ts sgn (fun k => a (q / ts.prod * ts.prod + k)) (q % ts.prod) c) p := by
  intro p hp
  rcases Nat.eq_zero_or_pos r with h0 | hr
  · subst h0
    funext c
    exact c.elim0
  have hB : 0 < ts.prod := List.prod_pos hpos
  have hpdiv : p / ts.prod < t := by rw [Nat.div_lt_iff_lt_mul hB]; exact hp
  have hpmod : (p / ts.prod) % t = p / ts.prod := Nat.mod_eq_of_lt hpdiv
  have hpm : p - p / ts.prod * ts.prod = p % ts.prod := by
    have h := Nat.div_add_mod p ts.prod
    rw [mul_comm ts.prod (p / ts.prod)] at h
    omega
  have hscalar : (1 / (t : ℂ)) * (1 / (ts.prod : ℂ)) = 1 / ((t * ts.prod : ℕ) : ℂ) := by
    rw [div_mul_div_comm, one_mul, Nat.cast_mul]
  set X : Fin r → ℂ := fun c => (1 / ((t * ts.prod : ℕ) : ℂ)) *
      ∑ u ∈ Finset.range t, ∑ w ∈ Finset.range ts.prod,
        yMul r (sgn * ((2 * r / t * (p / ts.prod) * u : ℕ) : ℤ))
          (yMul r (sgn * synExp r ts (digits ts (p % ts.prod)) (digits ts w))
            (a (u * ts.prod + w))) c with hX
  have hL : dftMultiN r (t :: ts) sgn a p = X := by
    rw [hX]
    funext c
    simp only [dftMultiN, List.prod_cons]
    rw [show digits (t :: ts) p = p / ts.prod :: digits ts (p % ts.prod) from by
      rw [digits_cons, hpmod]]
    rw [sum_range_mul]
    apply congrArg (fun z => (1 / ((t * ts.prod : ℕ) : ℂ)) * z)
    refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun w hw => ?_
    have hu' : u < t := Finset.mem_range.mp hu
    have hw' : w < ts.prod := Finset.mem_range.mp hw
    have hduw : digits (t :: ts) (u * ts.prod + w) = u :: digits ts w := by
      rw [digits_cons]
      have h1 : (u * ts.prod + w) / ts.prod = u := by
        rw [Nat.add_comm, mul_comm u ts.prod, Nat.add_mul_div_left _ _ hB,
          Nat.div_eq_of_lt hw', Nat.zero_add]
      have h2 : (u * ts.prod + w) % ts.prod = w := by
        rw [Nat.add_comm, mul_comm u ts.prod, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hw']
      have h3 : u % t = u := Nat.mod_eq_of_lt hu'
      rw [h1, h2, h3]
    rw [hduw, synExp_cons, mul_add, yMulExpAdd r hr]
  have hR : axisT r t ts.prod sgn
        (fun q c => dftMultiN r ts sgn (fun k => a (q / ts.prod * ts.prod + k)) (q % ts.prod) c) p = X := by
    rw [hX]
    funext c
    simp only [axisT]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    have hu' : u < t := Finset.mem_range.mp hu
    have hdiv2 : (p % ts.prod + u * ts.prod) / ts.prod = u := by
      rw [mul_comm u ts.prod, Nat.add_mul_div_left _ _ hB,
        Nat.div_eq_of_lt (Nat.mod_lt p hB), Nat.zero_add]
    have hmod2 : (p % ts.prod + u * ts.prod) % ts.prod = p % ts.prod := by
      rw [mul_comm u ts.prod, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Nat.mod_lt p hB)]
    rw [hpmod, hpm, hdiv2, hmod2]
    rw [dftMultiN_eq_smul_sum]
    rw [yMulSmulLoc, yMulSumLoc]
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [← mul_assoc, hscalar]
  rw [hL, hR]

end Work.SynFFT
