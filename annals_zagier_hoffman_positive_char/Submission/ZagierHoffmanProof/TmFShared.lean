import Submission.ZagierHoffmanProof.Step3H

/-!
# The evaluation of `tmF` at a SHARED prefix

`Step3General.evalSeriesGen_tmF_gen` evaluates `evalSeriesGen (tmF … (s₀.take k)) θ` under the
hypothesis `huniq` (the prefix `s₀.take k` is uniquely extendable in `S`).  For Dac's Theorem 6.2 the
prefix may be **shared** by several tuples, and then the evaluation is the *sum* over the extenders:

  `evalSeriesGen (tmF q ω w S cf t) θ = ∑_{s ∈ S, s.take |t| = t} (cf s).eval θ · 𝓛(s.drop |t|)(θ)`.

This is the algebraic input of the shared-prefix case of Step 3(a): combined with the bridge
`π̃^{w-w(t)}·𝓛(tail_s)(θ) = (∏_j Γ_j)·ambInfHom (ζ_A tail_s)` it turns `f_𝔱(θ) = 0` into a
`K`-linear relation among the `ζ_A(tail_s)`, which the induction hypothesis `TupleIndP (w - w(𝔱))`
kills — hence `f_𝔱(θ) ≠ 0`, and then `dvd_pred_of_piTilde_pow_mul_mem_ambK` (in `PiTildeDvd.lean`)
gives `(q-1) ∣ (w - w(𝔱))` with **no** `huniq` hypothesis at all.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
open Polynomial PowerSeries Finset
open scoped WithZero Topology Classical

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- `GSuperEntire` of the zero series (via `GSuperEntire.sum` on the empty finset). -/
lemma gSuperEntire_zero : GSuperEntire ambGamma (0 : PowerSeries (Ambient F)) := by
  have h := GSuperEntire.sum (K := Ambient F) (ambGamma_lt_one.le) (∅ :
    Finset (PowerSeries (Ambient F))) (fun x => x)
    (fun i hi => absurd hi (by simp))
  simpa using h

/-- ★★★ **The evaluation of `tmF` at a shared prefix.**  No uniqueness hypothesis. -/
theorem evalSeriesGen_tmF_shared {w : ℕ}
    {S : Finset (List (ℕ × Polynomial (Ambient F)))}
    {cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F)}
    {t : List (ℕ × Polynomial (Ambient F))}
    (hse : ∀ s ∈ S, GSuperEntire ambGamma
      (tmL (Nat.card F) (ambOmega F) (s.drop t.length))) :
    evalSeriesGen (tmF (Nat.card F) (ambOmega F) w S cf t) (ambTheta F)
      = ∑ s ∈ S, if s.take t.length = t then (cf s).eval (ambTheta F)
          * evalSeriesGen (tmL (Nat.card F) (ambOmega F) (s.drop t.length)) (ambTheta F)
        else 0 := by
  classical
  rw [tmF]
  refine (evalSeriesGen_finset_sum (K := Ambient F) (ambGamma_lt_one) gammaArchimedean_rat S
    (fun s => if s.take t.length = t then
      (cf s : PowerSeries (Ambient F)) * tmL (Nat.card F) (ambOmega F) (s.drop t.length)
      else 0) ?_ (ambTheta F)).trans ?_
  · intro s hs
    by_cases h : s.take t.length = t
    · rw [if_pos h]
      exact (GSuperEntire.polynomial (K := Ambient F) (ambGamma_pos) (ambGamma_lt_one.le)
        (cf s)).mul (ambGamma_lt_one.le) (hse s hs)
    · rw [if_neg h]
      exact gSuperEntire_zero F
  · refine Finset.sum_congr rfl fun s hs => ?_
    by_cases h : s.take t.length = t
    · rw [if_pos h, if_pos h,
        evalSeriesGen_mul (K := Ambient F) (ambGamma_lt_one) gammaArchimedean_rat
          (GSuperEntire.polynomial (K := Ambient F) (ambGamma_pos) (ambGamma_lt_one.le) (cf s))
          (hse s hs),
        evalSeriesGen_polynomial]
    · rw [if_neg h, if_neg h, evalSeriesGen_zero]

end ZagierHoffmanPositiveChar
