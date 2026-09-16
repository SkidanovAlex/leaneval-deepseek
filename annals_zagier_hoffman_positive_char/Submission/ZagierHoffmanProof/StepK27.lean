import Submission.ZagierHoffmanProof.StepK26

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial
open scoped BigOperators

/-!
# Step K27: the s=1 collapse — first two steps (split + head-affineness)

The s=1 instance of the general stage-s collapse (StepK25 statement; Session 159
recipe, mirroring Hsum_collapse0's assembly with `D1` in place of `monicPd`):
`Σ_{t : Fin(m+1)→F} inv(cast(D1 (m+1) t))` should equal `(X−X^{q²})⁻¹·Σ_{u : Fin m→F}
inv(cast(D2 m u))`.  This module proves the first two steps:

  collapse1_split : Σ_t inv(cast(D1 (m+1) t)) = Σ_c Σ_u inv(cast(D1 (m+1)(cons c u)))
      [sum_cons_split + Fintype.sum_prod_type]
  collapse1_csum : Σ_c Σ_u inv(cast(D1 (m+1)(cons c u)))
      = Σ_u Σ_c inv(cast(C c + D1 (m+1)(cons 0 u)))   [Finset.sum_comm + per-summand
      congrArg of Inv.inv over congrArg of the cast over D1_cons_add_zero]

Remaining (next pass): the inner `c`-sum is the `Hsum_one_subst` collapse at
`Z := D1 (m+1)(cons 0 u)` — requires `D1 (m+1)(cons 0 u).natDegree ≠ 0` (needs the
`hh 0 2 k` degree lemmas: natDegree (hh 0 2 k) = q·k since hh 0 2 k = Σ_{i≤k} X^{k+(q−1)i}
has unique top monomial `X^{qk}` at `i = k`) — then `Σ_c inv(C c + Z) = inv(Z − Z^q)`,
and the `D1 ↔ D2` glue `Z − Z^q = (X−X^{q²})·D2 m u` (St_step at stage-1 data, as in
stage0_factor) finishes the s=1 instance.  All lemmas here are sorry-free.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]




/-- (s=1, step 1) splitting the stage-1 state-sum by the next head coefficient:
`Σ_{t : Fin(m+1)→F} inv(D1 (m+1) t) = Σ_c Σ_u inv(D1 (m+1)(cons c u))`. -/
lemma collapse1_split (m : ℕ) :
    letI : Fintype F := Fintype.ofFinite F
    (∑ t : Fin (m + 1) → F, ((((D1 F (m + 1) t : F[X]) : F[X]) : RatFunc F)⁻¹)) =
      ∑ c : F, ∑ u : Fin m → F, ((((D1 F (m + 1) (Fin.cons c u) : F[X]) : F[X]) : RatFunc F)⁻¹) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  letI : DecidableEq F := Classical.decEq F
  rw [sum_cons_split F m (fun t : Fin (m + 1) → F =>
    ((((D1 F (m + 1) t : F[X]) : F[X]) : RatFunc F)⁻¹))]
  rw [Fintype.sum_prod_type]

/-- (s=1, step 2) rewriting the summand through the head-affineness:
`Σ_c Σ_u inv(D1 (m+1)(cons c u)) = Σ_u Σ_c inv(C c + D1 (m+1)(cons 0 u))`. -/
lemma collapse1_csum (m : ℕ) :
    letI : Fintype F := Fintype.ofFinite F
    (∑ c : F, ∑ u : Fin m → F, ((((D1 F (m + 1) (Fin.cons c u) : F[X]) : F[X]) : RatFunc F)⁻¹)) =
      ∑ u : Fin m → F, ∑ c : F, ((((C c + D1 F (m + 1) (Fin.cons 0 u) : F[X]) : F[X]) : RatFunc F)⁻¹) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro c hc
  apply congrArg (fun x : RatFunc F => x⁻¹)
  have hm := congrArg (fun p : F[X] => (((p : F[X]) : F[X]) : RatFunc F)) (D1_cons_add_zero F m c u)
  simpa using hm


end ZagierHoffmanPositiveChar
