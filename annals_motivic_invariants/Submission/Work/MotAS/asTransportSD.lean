import Mathlib
import Submission.Work.MotAS.ASData
import Submission.Work.MotAS.ASEntries
import Submission.Work.MotAS.ASRed
import Submission.Work.MotK.KleinData
import Submission.Work.MotAS.AsSDDefs
import Submission.Work.MotAS.AsTransportSDstage

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# AS transport of the dual secant quintic `s'`: reduction machinery

Part of `Submission/Work/MotAS` (`Work.MotAS`), the characteristic-5 (Artin--Schreier) branch of the
Crauder--Katz chart of H.-Y. Lin and E. Shinder, *Motivic invariants of birational maps*,
Ann. of Math. **199** (2024).

The target `asTransportSD` states `s'(asN w · ẑ) = s'^AS(ẑ)` in a ring `R` with `5 = 0` and
`w^5 = w + g`.  The reduction machinery lives in `Submission/Work/MotAS/AsSDDefs.lean`:

* `AsSDzv i` is the *reduced* coordinate vector of `z_i = Σ_j asN w i j ẑ_j` in the basis
  `1, w, …, w⁴` of `A = R[w]/(w⁵ - w - g)`, with `AsSDzv{i}_spec`;
* `asSDsq/cube/4/5` and `asSDt3/t5` reduce powers and products of these vectors through
  `Work.MotAS.redMul_spec` (multiplication in `A`), never leaving `w`-degree 4.

That reduction is *staged* (2-fold products at a time) in `Submission/Work/MotAS/AsSDVecs.lean`,
which defines the 63 intermediate coefficient vectors `W0, …, W62` (each with its five
components `Wk_0, …, Wk_4`), and in `AsSDStages*.lean`, which proves
`redMul g A B = Wk g z` for every stage (`A`, `B` one of the `AsSDzv i z` or `Wj g z`).
`AsSDRuns*.lean` collects the per-(run, component) reduction of the 48 monomials of
`kleinSecDual`, grouped by their `(a,b)`-coefficient.

The remaining work is the *main assembly*: rewrite the 48 monomials of `kleinSecDual` with
`asSDt3/t5` (building the nested `redMul` expressions), rewrite those with the stage lemmas,
expand the `Fin 5` sums, rearrange the resulting sum into the `(run, component)` blocks
(a `ring` identity in the vector atoms), rewrite those with `AsSDRuns*`, and close with
`linear_combination … * h5`.

That assembly is carried out in the sibling chapter `Submission/Work/MotAS/SD*.lean`
(namespace `Work.MotAS.SDStage`, entry point `Submission.Work.MotAS.AsTransportSDstage`): the
coefficient vectors `Xk` are rewritten monomial-by-monomial (`sdmon*`), the sums are collected
per `z`-monomial (`split_*`, `reord`, `Lm_agg`), each of the 126 `z`-monomial pieces is reduced
modulo `w^5 - w - g` and `5` (`piece_*`), and the result is reassembled into
`kleinSecDualAS` (`kleinSecDualAS_collect`).  The theorem below is the target name, obtained
from that development.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Work.MotAS
variable {R : Type*} [CommRing R]

/-- **`s'(asN w · ẑ) = s'^AS(ẑ)`** in characteristic `5`. -/
theorem asTransportSD {R : Type*} [CommRing R] (a b g w : R) (h5 : (5 : R) = 0)
    (hw : w ^ 5 = w + g) (z : Fin 5 → R) :
    Work.MotK.kleinSecDual a b (fun i => ∑ j, Work.MotAS.asN w i j * z j)
      = Work.MotAS.kleinSecDualAS a b g z := by
  exact Work.MotAS.AsTransportSDstage a b g w h5 hw z

end Work.MotAS
