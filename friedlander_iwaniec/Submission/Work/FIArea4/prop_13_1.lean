import Mathlib
import Submission.Work.FIArea4.A4varbounds
import Submission.Work.FIArea4.jacobi_congruence_count
import Submission.Work.FIArea4.Evar_le_trivial
import Submission.Work.FIArea4.P13Defs
import Submission.Work.FIArea4.P13basic
import Submission.Work.FIArea4.P13Scale
import Submission.Work.FIArea4.P13_tau_bound
import Submission.Work.FIArea4.P13_num_large
import Submission.Work.FIArea4.P13_num_small
import Submission.Work.FIArea4.P13_EvarA_le
import Submission.Work.FIArea4.P13_EvarB_sum
import Submission.Work.FIArea4.P13_prime_divisor_count
import Submission.Work.FIArea4.P13_Ener_le
import Submission.Work.FIArea4.P13_arith_facts
import Submission.Work.FIArea4.P13Assembly
import Submission.Work.FIArea4.P13_caseB2
import Submission.Work.FIArea4.P13Final

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- FI Proposition 13.1 ("enlarging moduli", (13.4)–(13.5)), stated as the implication
"Proposition 12.1 (for every `ε > 0`) implies Proposition 13.1 (for every `ε > 0`)" between the
`Prop`s defined in the module `Submission.Work.FIArea4.A4varbounds`, which this file imports.

WHY THE "FOR EVERY `ε`" FORM (and not the same-`ε` form `p14Prop121 ε → p14Prop131 ε`, which is
NOT derivable and was already declared false once): the §13 argument applies Proposition 12.1 to
`V(D⁺)`, whose right-hand side carries the `τ`-weighted energy `p14Ener = Σ τ(r)‖α r s‖²`; the
conclusion `p14Prop131` carries the *unweighted* `p14L2 = Σ‖α r s‖²`, and converting costs
`(RS)^{ε'}` for any `ε' > 0` (`τ(r) ≤ C_{ε'} r^{ε'}`).  Likewise the `log`-powers of (12.4) and of
the enlarging principle (13.4) must be absorbed, again at the price of a small power of `RS`.
Both fit inside the conclusion's `(RS)^ε` as long as the hypothesis is used at an exponent
`ε' ≤ ε/3` say — which is exactly what the paper's convention "for any `ε > 0`" allows, and what
`p14Prop121All` provides.  Since `p14T12` is *increasing* in its exponent (all its `ε`-occurrences
are powers `(RS)^ε` with `RS ≥ 1`), the same-`ε` form is strictly weaker information and is not
enough.

README for the proof (paper §13, all at exponent `ε' := ε/3`):
* (13.1) `E(d) ≤ 2(E_p(d) + E'_p(d))` (`p ∤ r` resp. `p ∣ r`); `Σ_d E'_p(d)` is estimated
  trivially by `(D + p^{-1}(RS)^{1+ε'})Σ_{r,s}‖α pr s‖²`;
* multiply by `p^{-1} log p`, sum over `P < p ≤ 2P`: `V(D) ≪ Σ_{P<p≤2P}(log p/p)Σ_{d∼D}E_p(d) +
  (DP^{-1} + P^{-2}RS)(RS)^{ε'}·p14L2`;
* the monotonicity of the local variance `A(d) ≤ mA(dm)` with `m = p²` gives (13.3)
  `E_p(d) ≤ p²E(dp²)` (the Jacobi identity `(d p²/r) = (d/r)` for `p ∤ r`), hence (13.4): for
  all `D, P > 1` there is `D⁺` with `DP² ≤ D⁺ ≤ 4DP²` and
  `V(D) ≪ V(D⁺)·P·log(2DP) + (DP^{-1} + P^{-2}RS)(RS)^{ε'}p14L2`;
* apply `p14Prop121All` at `ε'` to `V(D⁺)`, bound `p14Ener ≤ C_{ε'}(RS)^{ε'}·p14L2`, and choose
  `P = D^{-1/2}(R+S)^{-1/8}(RS)^{3/8}`: then `P·T12(D⁺) ≪ p14T13(RS)^{ε'}` (the two bracketed
  terms of (12.4) reproduce the second term of (13.5) exactly at this `P`, up to a bounded
  constant, and `P·D⁺ ≪ p14T13`), so
  `V(D) ≪ (RS)^{2ε'}·p14T13·p14L2 ≤ (RS)^ε·p14T13·p14L2` because `2ε' = 2ε/3 ≤ ε`;
* outside the paper's range (13.6) `(R+S)^{1/4}(RS)^{1/4} ≪ D ≪ (R+S)^{-1/4}(RS)^{3/4}` (i.e.
  `P ≤ 1` resp. the lower end) use the *sharp* elementary bound
  `E(d) ≪ (d^{-1}RS + √(RS))·p14L2` (FI (11.8) + Lemma 11.2 — the asymmetric
  `Evar_le_trivial` bound `4RS/d+4R+4` is too weak, e.g. `R = n², S = 1, D = n`, and it assumes
  `gcd(r,d) = 1` for every supported `r`, which the hypothesis only gives for odd `r` coprime to
  `s`).  The support hypothesis (12.1) gives `(r,s) = 1`, which is what makes the diagonal
  `r₁s₂ = r₂s₁` collapse to `(r₁,s₁) = (r₂,s₂)`; note that the formalized
  `Work.FIArea4.jacobi_congruence_count` assumes `a, b` both coprime to `d`, so a small
  generalisation to `(a,b,d) = 1` is needed.  FI's remark after (11.14) also gives directly
  `V(D) ≪ (RS + D√(RS))p14L2`, which is already `≪ p14T13` at both ends of (13.6).
The statement is *true* (it is the paper's §13 argument); the previous declaration of falsity was
about the same-`ε` form, which is a different (and indeed unprovable) statement. 
FORMALISED ROUTE (this file).  The proof is assembled in `Submission/Work/FIArea4/P13Final.lean`
from the pieces below (all `sorry`-free in the workspace):
* `P13_EvarA_le` (13.3), `P13_EvarB_sum` (13.2), `p13_enlarged_sum_le` (the window/multiplicity
  step of (13.4)), `P13_prime_count`, `P13_prime_divisor_count`, `P13_sum_L2p`, `P13_tau_bound`,
  `P13_Ener_le`, `P13_num_large` / `P13_num_small` (the two bracket comparisons with
  `P = p13P D R S = D^{-1/2}(R+S)^{-1/8}(RS)^{3/8}`) and `P13_arith_facts` (the elementary
  consequences of that choice of `P`);
* `P13Assembly.p13_caseA` (`P ≤ 1`: Proposition 12.1 at `D` itself),
  `P13_caseB2` (`P > 1`: average (13.1)+(13.3) over the primes of `(⌈P⌉₊, 2⌈P⌉₊]`, which turns the
  enlargement cost `P²` into `P log(4P)`, and apply Proposition 12.1 at the enlarged moduli
  `≍ D P²`), and `P13Assembly.p13_combine`.
The conclusion is stated with exponent `ε/8` for the hypothesis and absorbs the logarithms and the
`τ`-weight into the available `(RS)^ε`.
-/
theorem prop_13_1 : p14Prop121All → p14Prop131All :=
  p13_final_aux
    (fun ε hε => P13_Ener_le ε hε)
    (fun ε hε => P13_num_large ε hε)
    (fun ε hε => P13_num_small ε hε)
    P13_prime_count
    (fun ε hε => P13_prime_divisor_count ε hε)
    (fun ε hε => P13_arith_facts ε hε)
    (fun ε hε => P13_tau_bound ε hε)
    (fun D R S p α B hp hB hsup => P13_EvarB_sum D R S p α B hB hsup)
    (fun R S α W K hK hK2 => P13_sum_L2p R S α W K hK hK2)
    (fun R S d p α hd hp => P13_EvarA_le R S d p α hp hd)
    (fun D R S W α e₁ e₂ he₁ hp hlo hhi => p13_enlarged_sum_le D R S W α e₁ e₂ he₁ hp hlo hhi)

end

end Work.FIArea4
