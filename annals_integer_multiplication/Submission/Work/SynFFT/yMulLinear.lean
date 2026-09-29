import Mathlib
import Submission.Work.SynFFT.defs

/-!
# Linearity of multiplication by `y^e` in `ℂ[y]/(y^r+1)`

`HvdH.yMul r e a` acts on the coefficient vector `a` of an element of `R = ℂ[y]/(y^r+1)` by the
fixed data

`(yMul r e a) k = σ_k · vget a i_k`

where the sign `σ_k ∈ {1,-1}` and the index `i_k` depend only on `r`, `e` and `k` — never on `a`.
Hence the operator is `ℂ`-linear (and, more generally, additive over any `Finset` sum), for every
`r` including `r = 0` (where `Fin r` is empty and both identities are vacuous).

This is the `ℂ`-linearity needed to move `yMul` through the sums appearing in the DFT/FFT
definitions, in particular in `dftN`, `levels` and `synDFT`.
-/

set_option autoImplicit false

namespace Work.SynFFT

open HvdH

/-- The value of `yMul` is a constant (independent of the vector) times a read-off of the vector;
this is the explicit pointwise form used to prove linearity. -/
private lemma yMul_apply (r : ℕ) (e : ℤ) (a : Fin r → ℂ) (k : Fin r) :
    HvdH.yMul r e a k =
      (if Even ((((k : ℤ) - e) % (r : ℤ) + e - (k : ℤ)) / (r : ℤ)) then (1 : ℂ) else -1) *
        HvdH.vget a ((((k : ℤ) - e) % (r : ℤ)).toNat) := rfl

/-- `vget` is `ℂ`-homogeneous. -/
lemma vget_smul {n : ℕ} (u : Fin n → ℂ) (c : ℂ) (i : ℕ) :
    HvdH.vget (c • u) i = c * HvdH.vget u i := by
  by_cases h : i < n <;> simp [HvdH.vget, h, Pi.smul_apply, smul_eq_mul]

/-- `vget` commutes with finite sums. -/
lemma vget_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Fin n → ℂ) (i : ℕ) :
    HvdH.vget (∑ i' ∈ s, f i') i = ∑ i' ∈ s, HvdH.vget (f i') i := by
  by_cases h : i < n
  · simp only [HvdH.vget, h, dite_eq_left]
    rw [Finset.sum_apply]
  · simp [HvdH.vget, h]

theorem yMulLinear (r : ℕ) {ι : Type*} :
    (∀ (e : ℤ) (c : ℂ) (a : Fin r → ℂ), HvdH.yMul r e (c • a) = c • HvdH.yMul r e a) ∧
    (∀ (e : ℤ) (s : Finset ι) (f : ι → Fin r → ℂ),
      HvdH.yMul r e (∑ i ∈ s, f i) = ∑ i ∈ s, HvdH.yMul r e (f i)) := by
  constructor
  · intro e c a
    funext k
    simp only [yMul_apply, Pi.smul_apply, smul_eq_mul, vget_smul]
    ring
  · intro e s f
    funext k
    simp only [yMul_apply, Finset.sum_apply, vget_sum, Finset.mul_sum]

end Work.SynFFT
