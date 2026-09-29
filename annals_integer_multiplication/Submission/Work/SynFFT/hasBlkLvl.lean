import Mathlib
import Submission.Work.SynFFT.hasBlkLvlAux2
import Submission.Work.SynFFT.blkLvlPrefix
import Submission.Work.SynFFT.blkLvlSuffix
import Submission.Work.SynFFT.blkLvlRead

/-!
# `Work.SynFFT.hasBlkLvl`

The block level pass (`HasBlkLvl`, `kit2.lean`): the word that applies one radix-two butterfly
level (block size `m`) to a block of `m` coefficient vectors.

Its proof is assembled in `Submission/Work/SynFFT/hasBlkLvlAux2.lean` from

* the per-pair word (`pairWordBlk`) and the `zipWith` pass (`blkLvlZip`, `hasBlkLvlAux.lean`),
* the prefix and suffix list words (`blkLvlPrefix`, `blkLvlSuffix`),
* the list-level reading of the result (`blkLvlRead`).
-/

set_option autoImplicit false

namespace Work.SynFFT

theorem hasBlkLvl (hk : Work.SynFFT.KLib) (hi : HvdH.IntLib) (hl : HvdH.LayoutLib) (hf : HvdH.FxLib) (hp : Work.SynFFT.HasPair) : Work.SynFFT.HasBlkLvl :=
  hasBlkLvl_aux hk hi hl hf hp (blkLvlPrefix hk hi hl) (blkLvlSuffix hk hi hl)
    (fun p r m sh sgn u e lows highs h2 hmul hp2 hlow hhigh hlowapp hhighapp =>
      blkLvlRead p r m sh sgn u e lows highs h2 hmul hp2 hlow hhigh hlowapp hhighapp)

end Work.SynFFT
