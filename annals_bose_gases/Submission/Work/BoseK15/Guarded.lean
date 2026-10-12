import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseK15.Derive
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseK15.Guarded` — the guarded form of `hasKernel`

`Work.BoseK15.Obstruction` proves that the **global** `Q3Kernel.hasKernel` has no
honest instance: on a finite mode system the identity forces the (unguarded)
label additivity `kmom (i - j) = kmom i - kmom j` for *all* `i, j`, which makes
`kmom ≡ 0` and empties `P_H^q`.  The repair is the one the design already applied
to `Q3Kernel.kmom_sub`: ask the identity only on the pairs §10 sums over,
`i ∈ supp f_L ⊆ P_L` and `j ∈ P_H`.

This module proves that **guarded** identity for the box model, from the three
definitional facts that `Work.BoseB4.boxFockData`/`Work.BoseB4.Q3Env.ofSect4`
supply (`hF` is `Work.BoseB4.boxFockData_ccrK` unpacked, `hE`/`hE1` are the
`chiHatSqMode`/`chiHatMode` definitions), together with the guarded additivity.
It is the statement `Work.BoseB7A.Q3Kernel.hasKernel` *should* have.
-/

noncomputable section

open scoped BigOperators Pointwise
open MeasureTheory Classical

namespace Work.BoseK15

open Work.BoseB7 Work.BoseB7A

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **The guarded `hasKernel`.**  For a box mode system whose commutator kernel is
the box kernel at the momentum difference (`hF`), whose `χ̂`/`χ̂²` are read off the
corpus χ at `ℓ·kmom` (`hE`, `hE1`), and whose labels are additive on the summed
pairs (`hadd` — the unguarded version is impossible, see `Obstruction`), the
`Q3Kernel` identity holds on those pairs. -/
theorem hasKernel_guarded {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (ℓ : ℝ) (kmom : Mode → ℝ³)
    (F : FockData Mode) (E : Q3Env Mode)
    (hF : ∀ i j : Mode, F.ccrK i j
      = corpusBox.hatChiSq (ℓ • (kmom i - kmom j))
        - corpusBox.hatChi (ℓ • kmom i) * corpusBox.hatChi (ℓ • kmom j))
    (hE : ∀ k : Mode, E.hatChiSq k = corpusBox.hatChiSq (ℓ • kmom k))
    (hE1 : ∀ k : Mode, E.hatChi k = corpusBox.hatChi (ℓ • kmom k))
    (hadd : ∀ i j : Mode, E.fL i ≠ 0 → j ∈ F.PHset E → kmom (i - j) = kmom i - kmom j) :
    ∀ i j : Mode, E.fL i ≠ 0 → j ∈ F.PHset E →
      F.ccrK i j = E.hatChiSq (i - j) - E.hatChi i * E.hatChi j := by
  intro i j hi hj
  rw [hF i j, hE (i - j), hE1 i, hE1 j, hadd i j hi hj]

end Work.BoseK15
