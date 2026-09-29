import Mathlib
import Submission.Work.SynFFT.defs
import Submission.Work.SynFFT.yMulFacts

/-!
# The `ℤ`-action laws of `yMul`

`HvdH.yMul r e a` is multiplication by `y^e` on coefficient vectors of `R = ℂ[y]/(y^r+1)`.
`Submission/Work/SynFFT/yMulFacts.lean` establishes, for `r > 0`, the conjunction of the
laws of this `ℤ`-action on `R`: composition, unit, `ℂ`-bilinearity, the one-step period
`y^{e+2r} = y^e` (which specialises the action to an action of `ℤ/2r`), and the two
relations `y^{2r} = 1`, `y^r = -1`.

Here we extract the seven conjuncts requested by `yMulAlg`.  The seventh conjunct (the
period with an arbitrary integer multiplier, `y^{e+2rn} = y^e`) is not among the conjuncts
of `yMulFacts`, so we derive it from the one-step period by induction on `n : ℤ`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.SynFFT

open HvdH

private lemma yMulAlg_comp (r : ℕ) (hr : 0 < r) (e e' : ℤ) (a : Fin r → ℂ) :
    HvdH.yMul r (e + e') a = HvdH.yMul r e (HvdH.yMul r e' a) :=
  (yMulFacts r hr).1 e e' a

private lemma yMulAlg_zero (r : ℕ) (hr : 0 < r) (a : Fin r → ℂ) :
    HvdH.yMul r 0 a = a :=
  (yMulFacts r hr).2.1 a

private lemma yMulAlg_add (r : ℕ) (hr : 0 < r) (e : ℤ) (a b : Fin r → ℂ) :
    HvdH.yMul r e (a + b) = HvdH.yMul r e a + HvdH.yMul r e b :=
  (yMulFacts r hr).2.2.1 e a b

private lemma yMulAlg_smul (r : ℕ) (hr : 0 < r) (e : ℤ) (c : ℂ) (a : Fin r → ℂ) :
    HvdH.yMul r e (c • a) = c • HvdH.yMul r e a :=
  (yMulFacts r hr).2.2.2.1 e c a

/-- One-step period: `y^{e+2r} = y^e`. -/
private lemma yMulAlg_per1 (r : ℕ) (hr : 0 < r) (e : ℤ) (a : Fin r → ℂ) :
    HvdH.yMul r (e + 2 * (r : ℤ)) a = HvdH.yMul r e a :=
  (yMulFacts r hr).2.2.2.2.2.1 e a

private lemma yMulAlg_twoR (r : ℕ) (hr : 0 < r) (a : Fin r → ℂ) :
    HvdH.yMul r (2 * (r : ℤ)) a = a :=
  (yMulFacts r hr).2.2.2.2.2.2.1 a

private lemma yMulAlg_half (r : ℕ) (hr : 0 < r) (a : Fin r → ℂ) :
    HvdH.yMul r (r : ℤ) a = -a :=
  (yMulFacts r hr).2.2.2.2.2.2.2 a

/-- Period with an arbitrary integer multiplier: `y^{e+2rn} = y^e` for every `n : ℤ`. -/
private lemma yMulAlg_per (r : ℕ) (hr : 0 < r) (e n : ℤ) (a : Fin r → ℂ) :
    HvdH.yMul r (e + 2 * (r : ℤ) * n) a = HvdH.yMul r e a := by
  have hper := yMulAlg_per1 r hr
  have hper' : ∀ (x : ℤ) (a : Fin r → ℂ),
      HvdH.yMul r (x - 2 * (r : ℤ)) a = HvdH.yMul r x a := by
    intro x b
    have h := hper (x - 2 * (r : ℤ)) b
    rw [show x - 2 * (r : ℤ) + 2 * (r : ℤ) = x by ring] at h
    exact h.symm
  induction n using Int.induction_on with
  | zero => rw [mul_zero, add_zero]
  | succ i ih =>
      rw [show e + 2 * (r : ℤ) * ((i : ℤ) + 1)
            = (e + 2 * (r : ℤ) * (i : ℤ)) + 2 * (r : ℤ) by ring]
      exact (hper (e + 2 * (r : ℤ) * (i : ℤ)) a).trans ih
  | pred i ih =>
      rw [show e + 2 * (r : ℤ) * (-(i : ℤ) - 1)
            = (e + 2 * (r : ℤ) * (-(i : ℤ))) - 2 * (r : ℤ) by ring]
      exact (hper' (e + 2 * (r : ℤ) * (-(i : ℤ))) a).trans ih

theorem yMulAlg (r : ℕ) (hr : 0 < r) :
    (∀ (e e' : ℤ) (a : Fin r → ℂ), HvdH.yMul r (e + e') a = HvdH.yMul r e (HvdH.yMul r e' a)) ∧
    (∀ a : Fin r → ℂ, HvdH.yMul r 0 a = a) ∧
    (∀ (e : ℤ) (a b : Fin r → ℂ), HvdH.yMul r e (a + b) = HvdH.yMul r e a + HvdH.yMul r e b) ∧
    (∀ (e : ℤ) (c : ℂ) (a : Fin r → ℂ), HvdH.yMul r e (c • a) = c • HvdH.yMul r e a) ∧
    (∀ (e n : ℤ) (a : Fin r → ℂ), HvdH.yMul r (e + 2 * (r : ℤ) * n) a = HvdH.yMul r e a) ∧
    (∀ a : Fin r → ℂ, HvdH.yMul r (2 * (r : ℤ)) a = a) ∧
    (∀ a : Fin r → ℂ, HvdH.yMul r (r : ℤ) a = -a) :=
  ⟨yMulAlg_comp r hr, yMulAlg_zero r hr, yMulAlg_add r hr, yMulAlg_smul r hr,
    yMulAlg_per r hr, yMulAlg_twoR r hr, yMulAlg_half r hr⟩

end Work.SynFFT
