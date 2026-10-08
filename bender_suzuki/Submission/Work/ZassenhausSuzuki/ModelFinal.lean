import Submission.Work.ZassenhausSuzuki.SzModelCoords
import Submission.Work.ZassenhausSuzuki.szFrelProp

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Area `ZassenhausSuzuki`: the model half is proved

The two inputs of the model half of the Suzuki recognition are now theorems of this area:

* D1, uniqueness of the Tits endomorphism: `titsThetaUniqueProp` (`ModelDatum.lean`);
* D2, the matrix identity `w u(a,b) w ∈ B w u(τ(a,b))` of `SzModel n`: `szFrelProp`
  (`szFrelProp.lean`, using `SzAux/sz_e_eq` and the delivered
  `Commons.GroupTheory.Suzuki.szW_conj_szU_matrix`).

Hence `SzModelDatumTitsProp` and `SzModelDatumProp` hold unconditionally:
`szModelDatumProp` below is the model half of `recognize_szModel` with no further hypotheses.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

/-- **D2.**  The model datum of `SzModel n` at the canonical Tits endomorphism. -/
theorem szModelDatumTitsProp : SzModelDatumTitsProp :=
  szModelDatumTitsProp_of szFrelProp

/-- **The model half of the Suzuki recognition, proved.** -/
theorem szModelDatumProp : SzModelDatumProp :=
  szModelDatumProp_of titsThetaUniqueProp szModelDatumTitsProp

end Work.ZassenhausSuzuki
