import Mathlib
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotAS.ASRul.kernel_basis
import Submission.Work.MotC5N3.RulingX2.NotMemRadicalOfShift
import Submission.Work.MotC5N3.RulingX2.ZiasSliceNeTop

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC5N3.RulingX2

/-
The AS residual curve `V(ZIAS a b g) ⊂ A³_{X0,X1,X2}` (the five cubics `zcubAS a b g k`, chart
`(1,X₀,X₁,X₂,0)` of the AS-twisted Klein curve) is NOT contained in the plane `{X 2 = 0}`.
TRUE (exhaustively swept over 𝔽₅ and 𝔽₂₅).

## The route implemented here (route R1 of the recorded alternatives)

The load-bearing step is that the plane `{X₂ = 1}` is *not* contained in the residual curve, i.e.

  `ZIAS a b g ⊔ (X 2 - 1) ≠ ⊤`   (`Work.MotC5N3.RulingX2.ZiasSliceNeTop`, a separate piece);

from a proper ideal `Z ⊔ (X 2 - 1)` the conclusion `X 2 ∉ √Z` follows with *no* further geometry:
if `X 2` were nilpotent modulo `Z` then `X 2 - 1` would be a unit of `K[X] ⧸ Z`, so
`Z ⊔ (X 2 - 1)` would be the unit ideal.  This implication is the (already proved, sorry-free)
`Work.MotC5N3.RulingX2.notMem_radical_of_shift_ne_top` with `c = 1` — a local fork of
`Work.MotAS.ASRulV2.notMem_radical_of_shift_ne_top`, so that this route does not drag in the
transitive imports of that `MotAS` module (the `MotAS/ZiasNe*` family, a work in progress).

## What was tried and does not work (recorded for the next session)

* The route through the *degree-3 parts* `H_k` of `zcubAS a b g k` is **invalid**:
  `X 2 ∈ √(ZIAS) ⟹ X 2 ∈ √(H_0,…,H_4)` is FALSE.  Concrete counterexample: for
  `(a,b,g) = (1,1,1)` over `𝔽₂₅` the point `(X₀,X₁,X₂) = (4,2,1)` is a common zero of
  `H_0,…,H_4` (verified) while the values of the full cubics `zcubAS 1 1 1 k` there are
  `4,3,4,3,3 ≠ 0` (verified).  Hence `V(H_k) ⊄ V(ZIAS)`, so `√(ZIAS) ⊄ √(H_k)`, and the
  reduction recorded in the original docstring is unavailable.  (A certificate
  `E ∣ A³ h_k(-C/A, X₁)` for the dehomogenised degree-3 system *does* hold — `E` the quintic
  eliminant, `A = δ(abX₁+gε)`, `C = gδεX₁² + 2ab(a²+ab-b²)X₁ - gδ²` — but it yields only
  `X 2 ∉ √(H_k)`, which does not suffice.)

* `Work.MotAS.ASRulV2.CertData`'s `X₂ = 1` slice certificate `Ptilde ∣ Ac³ · f_k(Ccert/Ac, X₁)`
  does **not** hold where `Ac ≠ 0` (checked numerically over `𝔽₅` at
  `(a,b,g) = (1,1,1), (2,1,1), (1,1,2), (1,3,1), (1,4,1), (2,3,1)`: the division leaves a nonzero
  remainder in every case), so that file's docstring overstates its status.

* The full `X₂ = 1` slice ideal `J₁ = (f_k) ⊆ K[X₀,X₁]` **is** (verified over `𝔽₅` for all
  admissible `(a,b,g)` with `g ≠ 0`) described by a *graph* `J₁ = (X₀ - P(X₁), Q(X₁))` for an
  explicit low-degree `P` and a quintic `Q`; e.g. `(1,1,1)`: `P = X₁⁴+X₁³+X₁+1`,
  `Q = X₁⁵+X₁⁴+2X₁³+X₁²+X₁+1`.  A *uniform* symbolic `P, Q` was not obtained here, and in the few
  cases `(2,3,4), (3,2,4), (3,4,2), (4,2,2), (4,1,4)` the graph has a non-constant denominator.
-/
theorem X2_notMem_radical_generic (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) (hab : a * b ≠ 0) (hg : ¬ ∃ c : K, c ^ 5 - c = g) :
    (MvPolynomial.X 2 : MvPolynomial (Fin 3) K) ∉ Ideal.radical (Work.MotAS.ZIAS a b g) :=
  Work.MotC5N3.RulingX2.notMem_radical_of_shift_ne_top (Work.MotAS.ZIAS a b g) 1 one_ne_zero
    (by simpa using ZiasSliceNeTop K a b g ha hab hg)

end Work.MotC5N3.RulingX2
