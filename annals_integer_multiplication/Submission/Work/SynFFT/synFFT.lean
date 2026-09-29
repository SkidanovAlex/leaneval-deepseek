import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.top
import Submission.Work.SynFFT.reorderWord
import Submission.Work.SynFFT.dropParams
import Submission.Work.SynFFT.yMulTwiddle
import Submission.Work.SynFFT.hasYMulShift
import Submission.Work.SynFFT.hasPair
import Submission.Work.SynFFT.hasBlkLvl
import Submission.Work.SynFFT.lvlAllGetD
import Submission.Work.SynFFT.hasLvlPass
import Submission.Work.SynFFT.hasMrgBlk
import Submission.Work.SynFFT.hasMrgPass
import Submission.Work.SynFFT.mrgIterN_bitrev
import Submission.Work.SynFFT.hasFFT1
import Submission.Work.SynFFT.axisTSlices
import Submission.Work.SynFFT.hasAxis
import Submission.Work.SynFFT.axisIterEq
import Submission.Work.SynFFT.synDFTProp
import Submission.Work.SynFFT.arrSize
import Submission.Work.SynFFT.costArith
import Submission.Work.SynFFT.hasAxesFold

/-!
# SynFFT: the area's statement (paper Lemma 3.2 + Proposition 3.3)

The program and its proof of correctness are assembled in `top.lean` (`Work.SynFFT.hasTop`) from
the pieces of `kit2.lean`, each proved at its own path:

* `hasYMulShift`, `hasPair`           — the butterfly (Lemma 3.2);
* `hasBlkLvl`, `hasLvlPass`, `hasFFT1` — one radix-two level / the whole slice word;
* `hasMrgBlk`, `hasMrgPass`            — the interleave passes undoing the bit reversal;
* `hasAxis`, `hasAxesFold`             — the tensor factorisation (Prop 3.3);
* `reorderWord`, `dropParams`          — the parameter shuffling of the top level;
* pure math: `yMulTwiddle`, `lvlAllGetD`, `mrgIterN_bitrev`, `axisTSlices`, `axisIterEq`,
  `synDFTProp`, `arrSize`, `costArith`, plus the earlier `dft1Math`, `multiCons`, `logBound`,
  `yMulListOK`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.SynFFT

/-- Paper Lem. 3.2 and Proposition 3.3: synthetic multivariate FFT over C[y]/(y^r+1). -/
theorem synFFT : HvdH.KernelLib → HvdH.IntLib → HvdH.LayoutLib → HvdH.FxLib → HvdH.SynFFTProp := by
  intro hk hi hl hf
  have hK : Work.SynFFT.KLib := kLibOf hk
  have hy : HasYMulShift := hasYMulShift hK hi hl hf
  have hp : HasPair := hasPair hK hi hl hf hy yMulTwiddle
  have hb : HasBlkLvl := hasBlkLvl hK hi hl hf hp
  have hlvl : HasLvlPass := hasLvlPass hK hi hl hf hb lvlAllGetD
  have hmrg : HasMrgBlk := hasMrgBlk hK hi hl hf
  have hmp : HasMrgPass := hasMrgPass hK hi hl hf hmrg
  have hf1 : HasFFT1 := hasFFT1 hK hi hl hf hlvl hmp mrgIterN_bitrev
  have hax : HasAxis := hasAxis hK hi hl hf hf1 axisTSlices
  have hfold : HasAxesFold := hasAxesFold hK hi hl hf hax
  have hre : ReorderProp := reorderWord hK
  have hdp : DropParamsProp := dropParams hK
  have hcost : CostArithProp := fun Kr Kd Kf p r ts sgn us ws' n1 n2 n3 hlen hr hM h1 h2 h3
      hus hw' hts hsz hpisz hrisz hsisz =>
    costArith Kr Kd Kf p r ts sgn us ws' n1 n2 n3 hlen hr hM h1 h2 h3 hus hw' hts hsz
      hpisz hrisz hsisz
  exact hasTop hK hi hl hf hre hdp hfold axisIterEq synDFTProp arrSize hcost

end Work.SynFFT
