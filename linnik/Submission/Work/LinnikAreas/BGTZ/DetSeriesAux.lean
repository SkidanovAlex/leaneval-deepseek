/-
# Auxiliary lemmas for `DetSeriesIdentity`

Elementary manipulation lemmas used in the evaluation of the pair series `pairSer` (see
`DetSeriesDefs`): the multiplicative rewritings of `rProd T = ∏_{p ∈ T} p` and of the complex
power `(ab)^{-s}`, and the two re-indexing lemmas (pulling a finite sum out of an infinite sum,
and transferring between `ℕ+`- and `ℕ`-indexed absolutely convergent series).

The definitions of `cfun`/`multSer` and the basic facts about them live in
`Work.LinnikAreas.BGTZ.DetectorSeries` (shared vocabulary).
-/
import Mathlib
import Submission.Work.LinnikAreas.BGTZSetup
import Submission.Work.LinnikAreas.BGTZ.DetectorDefs
import Submission.Work.LinnikAreas.BGTZ.DetSeriesDefs
import Submission.Work.LinnikAreas.BGTZ.DetectorSeries

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.BGTZ

variable {q : ℕ} [NeZero q]

/-- `(∏_{p ∈ T} p)^{-s} = ∏_{p ∈ T} p^{-s}`. -/
lemma rProd_cpow (T : Finset ℕ) (s : ℂ) :
    ((rProd T : ℕ) : ℂ) ^ (-s) = ∏ p ∈ T, ((p : ℂ) ^ (-s)) := by
  have h : ∀ x y : ℕ, ((x : ℂ) * (y : ℂ)) ^ (-s) = (x : ℂ) ^ (-s) * (y : ℂ) ^ (-s) := by
    intro x y
    rw [← Complex.ofReal_natCast x, ← Complex.ofReal_natCast y]
    exact Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity) (-s)
  induction T using Finset.induction with
  | empty => simp [rProd]
  | insert a T ha ih =>
    have hars : rProd (insert a T) = a * rProd T := by
      rw [rProd, rProd, Finset.prod_insert ha]
    rw [hars, Finset.prod_insert ha]
    push_cast
    rw [h, ih]

/-- The value of a Dirichlet character at `rProd T` is the product of its values on `T`. -/
lemma chi_rProd (χ : DirichletCharacter ℂ q) (T : Finset ℕ) :
    χ (((rProd T : ℕ) : ZMod q)) = ∏ p ∈ T, χ ((p : ℕ) : ZMod q) := by
  rw [rProd, Nat.cast_prod]
  induction T using Finset.induction with
  | empty => simp
  | insert a T ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, map_mul, ih]

/-- `(a * b)^{-s} = a^{-s} * b^{-s}` for natural numbers. -/
lemma natCast_mul_cpow (a b : ℕ) (s : ℂ) :
    (((a * b : ℕ)) : ℂ) ^ (-s) = ((a : ℂ) ^ (-s)) * ((b : ℂ) ^ (-s)) := by
  rw [Nat.cast_mul, ← Complex.ofReal_natCast a, ← Complex.ofReal_natCast b]
  exact Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity) (-s)

/-- A finite sum may be pulled out of an infinite sum of complex numbers. -/
lemma tsum_sum_finset {ι α : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → α → ℂ)
    (hf : ∀ i ∈ s, Summable (f i)) :
    (∑' a, ∑ i ∈ s, f i a) = ∑ i ∈ s, ∑' a, f i a := by
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    have hfi : Summable (f i) := hf i (Finset.mem_insert_self i s)
    have hfs : ∀ j ∈ s, Summable (f j) := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hsum : Summable (fun a => ∑ j ∈ s, f j a) := summable_sum hfs
    have hstep : (fun a => ∑ j ∈ insert i s, f j a) = (fun a => f i a + ∑ j ∈ s, f j a) := by
      funext a
      exact Finset.sum_insert hi
    rw [hstep, Summable.tsum_add hfi hsum, ih hfs, Finset.sum_insert hi]

/-- An `ℕ+`-indexed series whose summand vanishes at `0` equals the `ℕ`-indexed one. -/
lemma tsum_pnat_eq_tsum_nat {f : ℕ → ℂ} (h0 : f 0 = 0) (hf : Summable f) :
    (∑' n : ℕ+, f (n : ℕ)) = ∑' n : ℕ, f n := by
  have h := tsum_zero_pnat_eq_tsum_nat (f := f) hf
  rw [h0, zero_add] at h
  exact h

/-- The multiples-series summand is summable for `1 < Re s` (the indicator is bounded by `1`). -/
lemma summable_indicator_cfun_div (χ₁ χ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1) (m : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => (if m ∣ n then cfun χ₁ χ n else 0) / (n : ℂ) ^ s) := by
  refine (summable_cfun χ₁ χ hχ₁ hs).norm.of_norm_bounded fun n => ?_
  by_cases h : m ∣ n
  · rw [if_pos h]
  · rw [if_neg h, zero_div, norm_zero]
    positivity

end Work.LinnikAreas.BGTZ
