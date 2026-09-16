import Submission.ZagierHoffmanProof.StepK21

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial
open scoped BigOperators

/-!
# Step K22: the general one-step stage factorisation (`St_s`, `St_step`)

The collapse-native form of the stage machinery (PLAN SESSION 152): for a degree-`d`
coefficient tuple `a` (extended by `a_d = 1`), the stage-`s` collapse denominator is
`St_s(a) := Σ_{m=0}^{d−s} a_{m+s}·hh 0 (s+1) m`.  Removing the next coefficient `a_s`
(`St_minus_head`) leaves exactly `stage_step`'s `E_s`-sum, so the GENERAL one-step
factorisation

    (St_s − a_s) − (St_s − a_s)^q = (X − X^{q^{s+1}})·Σ_{m<d−s} a_{m+s+1}·hh 0 (s+2) m

is `St_step` (repackaging of StepK18's `stage_step`); `St_step_one` is its s=1
specialisation.  This is the uniform lemma that the nested `EvalU d` iteration applies
at every stage (the shrinking tuple spaces change only the data `a`), completing the
`stage_step` → `stageE0_eq_Z0` → `stage0_factor` chain of StepK18/21.  All lemmas here
are sorry-free.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]




/-- the stage-`s` collapse denominator of the degree-`d` polynomial with coefficients
`a` (a_d = 1): `St_s(a) := Σ_{m=0}^{d−s} a_{m+s}·hh 0 (s+1) m`.  (PLAN SESSION 152:
after `s` coefficient-collapses of `U_d` the remaining inner denominator is `St_s`.) -/
noncomputable def St (d s : ℕ) (a : Fin d → F) : F[X] :=
  ∑ m ∈ Finset.range (d - s + 1), C (coeffSeq F d a (m + s)) * hh F 0 (s + 1) m

/-- removing the head coefficient (`a_s`, the next to collapse) from `St_s` leaves the
`E_s`-sum of `stage_step`: `St_s − a_s = Σ_{m<d−s} a_{m+s+1}·hh 0 (s+1) (m+1)`. -/
lemma St_minus_head (d s : ℕ) (a : Fin d → F) (hs : s < d) :
    St F d s a - C (coeffSeq F d a s) =
      ∑ m ∈ Finset.range (d - s), C (coeffSeq F d a (m + s + 1)) * hh F 0 (s + 1) (m + 1) := by
  classical
  dsimp [St]
  rw [Finset.sum_range_succ']
  have hf0 : C (coeffSeq F d a (0 + s)) * hh F 0 (s + 1) 0 = C (coeffSeq F d a s) := by
    rw [hh_zero F 0 (s + 1)]
    simp
  rw [hf0]
  have hcancel : ((∑ k ∈ Finset.range (d - s), C (coeffSeq F d a ((k + 1) + s)) * hh F 0 (s + 1) (k + 1)) + C (coeffSeq F d a s)) - C (coeffSeq F d a s) =
      ∑ k ∈ Finset.range (d - s), C (coeffSeq F d a ((k + 1) + s)) * hh F 0 (s + 1) (k + 1) := by
    ring
  rw [hcancel]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : (k + 1) + s = k + s + 1 := by omega
  rw [hk']

/-- ★ the GENERAL one-step stage factorisation (stage-`s` form of `stage_step`, in the
collapse-native language `St`): with the next coefficient `a_s` removed,
`(St_s − a_s) − (St_s − a_s)^q = (X − X^{q^{s+1}})·D_{s+1}`, where
`D_{s+1} := Σ_{m<d−s} a_{m+s+1}·hh 0 (s+2) m`. -/
lemma St_step (d s : ℕ) (a : Fin d → F) (hs : s < d) :
    (St F d s a - C (coeffSeq F d a s)) - (St F d s a - C (coeffSeq F d a s)) ^ (Nat.card F) =
      (X - X ^ ((Nat.card F) ^ (s + 1))) *
        (∑ m ∈ Finset.range (d - s), C (coeffSeq F d a (m + s + 1)) * hh F 0 (s + 2) m) := by
  classical
  have hs' := stage_step F d s a
  rw [← St_minus_head F d s a hs] at hs'
  exact hs'

/-- s = 1 specialisation of the general one-step factorisation. -/
lemma St_step_one (d : ℕ) (a : Fin d → F) (hs : 1 < d) :
    (St F d 1 a - C (coeffSeq F d a 1)) - (St F d 1 a - C (coeffSeq F d a 1)) ^ (Nat.card F) =
      (X - X ^ ((Nat.card F) ^ 2)) *
        (∑ m ∈ Finset.range (d - 1), C (coeffSeq F d a (m + 2)) * hh F 0 3 m) := by
  classical
  -- exactly St_step at s = 1 (the exponent (s+1) = 2)
  have h := St_step F d 1 a hs
  simpa using h


end ZagierHoffmanPositiveChar
