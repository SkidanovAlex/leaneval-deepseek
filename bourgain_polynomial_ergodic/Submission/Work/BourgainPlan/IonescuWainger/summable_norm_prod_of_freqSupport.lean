import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.FourierL2Defs

/-!
# A finite product of band-limited `ℓ²(ℤ)`-sequences is `ℓ¹`

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066, §4 —
the "band-limited / `ℓ²(ℤ)`-with-arcs" lane (`ARC_ARITH_STATUS.md`, `PLAN.md`).

The `ℓ²`-layer of Tao's `ortho`(ii)/(iii) needs the fact that the pointwise product of finitely
many band-limited `ℓ²(ℤ)`-sequences is absolutely summable: this is the hypothesis under which
Fubini/Tonelli may be applied to the coefficient formula, and under which the pairing
`Σ_m ∏_i f_i(m)·conj(∏_i g_i(m))` is absolutely convergent.

We prove the sharper (and frequency-support-free) statement

`g i ∈ ℓ²(ℤ) for all i : Fin (n + 2) → Summable (fun m => ∏ i, ‖g i m‖)`,

i.e. **any finite product of at least two `ℓ²`-sequences is `ℓ¹`**.  The frequency support
hypothesis `HasFreqSupport` is consequently not needed here at all; the statement is included
for the reader's convenience of matching the call site.

The mathematics is the elementary Hölder/AM-GM argument: for nonnegative reals
`2·a·b ≤ a² + b²`, so a factor `b ∈ ℓ²` may be absorbed into a summable `H ∈ ℓ¹` at the cost of
replacing `H` by `(H² + b²)/2`, which is again summable because `ℓ¹ ⊂ ℓ²` and a product of two
summable nonnegative sequences is summable (`Summable.mul_of_nonneg`).  Iterating over the finite
set of factors gives the result.

## Main declarations

* `summable_sq_of_summable_nonneg` — `ℓ¹ ⊂ ℓ²` for nonnegative real sequences;
* `summable_mul_finset_prod` — `H ∈ ℓ¹`, `b_i ∈ ℓ²` ⟹ `H · ∏_i b_i ∈ ℓ¹` (finite product);
* `summable_norm_prod_of_freqSupport` — the requested statement.
-/

open MeasureTheory
open scoped lp BigOperators ENNReal

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-- **`ℓ¹ ⊂ ℓ²` for nonnegative real sequences.**  A summable nonnegative sequence has summable
square.  (Equivalently, `Memℓp H 1` implies `Memℓp H 2`, via `Memℓp.of_exponent_ge`.) -/
theorem summable_sq_of_summable_nonneg {H : ℤ → ℝ} (h0 : ∀ m, 0 ≤ H m) (hh : Summable H) :
    Summable fun m => H m ^ 2 := by
  have hm1 : Memℓp H (1 : ℝ≥0∞) := by
    refine memℓp_gen ?_
    simpa [Real.norm_of_nonneg (h0 _)] using hh
  have hm2 : Memℓp H (2 : ℝ≥0∞) := hm1.of_exponent_ge (by norm_num)
  have := (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mp hm2
  simpa [Real.norm_of_nonneg (h0 _)] using this

/-- **Absorbing one `ℓ²` factor into a summable sequence.**  If `H ∈ ℓ¹` is nonnegative and
`b i ∈ ℓ²` for every `i ∈ s`, then `H · ∏_{i ∈ s} b i ∈ ℓ¹`.

The induction (on the finite set `s`) replaces `H` by `(H² + (b a)²)/2 ⊇ H·b a` when inserting a
new factor `a`; the new `H` is summable because `ℓ¹ ⊂ ℓ²`
(`summable_sq_of_summable_nonneg`) and `ℓ¹` is closed under pointwise sums and products. -/
theorem summable_mul_finset_prod {ι : Type*} (H : ℤ → ℝ) (hH0 : ∀ m, 0 ≤ H m)
    (hH : Summable H) (b : ι → ℤ → ℝ) (hb0 : ∀ i m, 0 ≤ b i m)
    (hb : ∀ i, Summable fun m => (b i m) ^ 2) (s : Finset ι) :
    Summable fun m => H m * ∏ i ∈ s, b i m := by
  classical
  induction s using Finset.induction_on generalizing H hH0 hH with
  | empty => simpa using hH
  | insert a s ha ih =>
    have hH2 : Summable fun m => H m ^ 2 := summable_sq_of_summable_nonneg hH0 hH
    have ha2 : Summable fun m => (b a m) ^ 2 := hb a
    have hH' : Summable fun m => (H m ^ 2 + (b a m) ^ 2) / 2 := (hH2.add ha2).div_const 2
    have ih' := ih (fun m => (H m ^ 2 + (b a m) ^ 2) / 2) (fun m => by positivity) hH'
    refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) ih'
    · rw [Finset.prod_insert ha]
      exact mul_nonneg (hH0 m) (mul_nonneg (hb0 a m) (Finset.prod_nonneg fun i _ => hb0 i m))
    · rw [Finset.prod_insert ha]
      have hle : H m * b a m ≤ (H m ^ 2 + (b a m) ^ 2) / 2 := by
        nlinarith [sq_nonneg (H m - b a m)]
      have hnn : 0 ≤ ∏ i ∈ s, b i m := Finset.prod_nonneg fun i _ => hb0 i m
      calc H m * (b a m * ∏ i ∈ s, b i m)
          = (H m * b a m) * ∏ i ∈ s, b i m := by ring
        _ ≤ (H m ^ 2 + (b a m) ^ 2) / 2 * ∏ i ∈ s, b i m :=
            mul_le_mul_of_nonneg_right hle hnn

/-- **A finite product of band-limited `ℓ²(ℤ)`-sequences is `ℓ¹`.**

For `g i ∈ ℓ²(ℤ)`, `i : Fin (n + 2)` (so at least two factors), the product of the absolute values
is summable.  The band-limitation hypothesis `HasFreqSupport` is not needed for this conclusion —
any finite product of `≥ 2` square-summable sequences is summable — but the statement is stated in
the form the band-limited major-arc lane consumes it.

Proof: split off the first two factors, bound `‖g 0 m‖·‖g 1 m‖ ≤ (‖g 0 m‖² + ‖g 1 m‖²)/2`, and
apply `summable_mul_finset_prod` to the (summable) weight `(‖g 0 m‖² + ‖g 1 m‖²)/2` and the
remaining `n` factors. -/
theorem summable_norm_prod_of_freqSupport {n : ℕ} (g : Fin (n + 2) → ℤ → ℂ)
    (hg : ∀ i, Memℓp (g i) 2) (D : Fin (n + 2) → Set Circle)
    (hD : ∀ i, HasFreqSupport (g i) (hg i) (D i)) :
    Summable fun m => ∏ i, ‖g i m‖ := by
  classical
  -- each factor is square summable
  have hsq : ∀ i : Fin (n + 2), Summable fun m => ‖g i m‖ ^ 2 := by
    intro i
    have h := (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mp (hg i)
    simpa [Real.rpow_natCast] using h
  -- the weight `(‖g 0‖² + ‖g 1‖²)/2`, summable, dominating `‖g 0‖·‖g 1‖`
  have hmain := summable_mul_finset_prod
    (fun m : ℤ => (‖g (0 : Fin (n + 2)) m‖ ^ 2 + ‖g (1 : Fin (n + 2)) m‖ ^ 2) / 2)
    (fun m => by positivity)
    (((hsq (0 : Fin (n + 2))).add (hsq (1 : Fin (n + 2)))).div_const 2)
    (fun i : Fin (n + 2) => fun m => ‖g i m‖)
    (fun i m => norm_nonneg _) hsq
    ((Finset.univ.erase (0 : Fin (n + 2))).erase (1 : Fin (n + 2)))
  refine Summable.of_nonneg_of_le (fun m => Finset.prod_nonneg fun i _ => norm_nonneg _)
    (fun m => ?_) hmain
  -- `∏ i, ‖g i m‖ = (∏_{i ≠ 0,1} ‖g i m‖ · ‖g 1 m‖) · ‖g 0 m‖`
  have key0 : (∏ i ∈ Finset.univ.erase (0 : Fin (n + 2)), ‖g i m‖) * ‖g 0 m‖ = ∏ i, ‖g i m‖ :=
    Finset.prod_erase_mul Finset.univ (fun i => ‖g i m‖) (Finset.mem_univ _)
  have key1 : (∏ i ∈ (Finset.univ.erase (0 : Fin (n + 2))).erase (1 : Fin (n + 2)), ‖g i m‖)
        * ‖g 1 m‖ = ∏ i ∈ Finset.univ.erase (0 : Fin (n + 2)), ‖g i m‖ :=
    Finset.prod_erase_mul _ (fun i => ‖g i m‖) (by simp)
  rw [← key0, ← key1]
  have hle : ‖g 0 m‖ * ‖g 1 m‖ ≤ (‖g 0 m‖ ^ 2 + ‖g 1 m‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖g 0 m‖ - ‖g 1 m‖)]
  have hR : 0 ≤ ∏ i ∈ (Finset.univ.erase (0 : Fin (n + 2))).erase (1 : Fin (n + 2)), ‖g i m‖ :=
    Finset.prod_nonneg fun i _ => norm_nonneg _
  calc ((∏ i ∈ (Finset.univ.erase (0 : Fin (n + 2))).erase (1 : Fin (n + 2)), ‖g i m‖)
        * ‖g 1 m‖) * ‖g 0 m‖
      = (∏ i ∈ (Finset.univ.erase (0 : Fin (n + 2))).erase (1 : Fin (n + 2)), ‖g i m‖)
          * (‖g 0 m‖ * ‖g 1 m‖) := by ring
    _ ≤ (∏ i ∈ (Finset.univ.erase (0 : Fin (n + 2))).erase (1 : Fin (n + 2)), ‖g i m‖)
          * ((‖g 0 m‖ ^ 2 + ‖g 1 m‖ ^ 2) / 2) := mul_le_mul_of_nonneg_left hle hR
    _ = ((‖g 0 m‖ ^ 2 + ‖g 1 m‖ ^ 2) / 2)
          * ∏ i ∈ (Finset.univ.erase (0 : Fin (n + 2))).erase (1 : Fin (n + 2)), ‖g i m‖ := by
        ring

end Work.BourgainPlan.IonescuWainger
