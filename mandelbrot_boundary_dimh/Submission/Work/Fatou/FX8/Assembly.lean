import Submission.Work.Fatou.FX8.Main
import Submission.Work.Fatou.Analysis.fatouDerivEstimate
import Submission.Work.Fatou.Analysis.fatouUniqueOfConstructed
import Submission.Work.Fatou.Analysis.fatouContinuityOf

/-!
# FX8, step 7: the FATOU contract from the constructed coordinate

The existence conjunct is `Work.Fatou.FX8.fatouExists` (FX8).  The remaining conjuncts of
`MandelDim.FatouStatement` are assembled here from

* the orbit relation (`FatouOrbit`), which follows from `FatouConstructed` and uniqueness,
* uniqueness (`FatouUnique`),
* continuity (`FatouContinuity`),
* the derivative estimate (`FatouDerivEstimate`, already proved),
* the end asymptotics (`FatouEnds`).
-/

namespace Work.Fatou.FX8

open MandelDim

noncomputable section

/-- The orbit relation for arbitrary Fatou coordinates, in the form of the contract. -/
theorem fatouOrbit (hU : UniformizationHyp) (hUnique : MandelDim.FatouUnique) :
    MandelDim.FatouOrbit :=
  fatouOrbit_of_constructed (fatouConstructed hU) hUnique

/-- Uniqueness of the Fatou coordinate, from the constructed coordinate. -/
theorem fatouUnique (hU : UniformizationHyp) : MandelDim.FatouUnique :=
  Work.Fatou.Analysis.fatouUniqueOfConstructed (fatouConstructed hU)

/-- Continuity of the Fatou coordinate, from the contract's inputs. -/
theorem fatouContinuity (hU : UniformizationHyp) : MandelDim.FatouContinuity :=
  Work.Fatou.Analysis.fatouContinuityOf (fatouExists hU) (fatouUnique hU)
    Work.Fatou.Analysis.fatouDerivEstimate

/-- **The FATOU contract**, from the end asymptotics. -/
theorem fatouStatement_of (hU : UniformizationHyp) (hEnds : MandelDim.FatouEnds) :
    MandelDim.FatouStatement :=
  ⟨fatouExists hU, fatouOrbit hU (fatouUnique hU), fatouUnique hU, fatouContinuity hU,
    Work.Fatou.Analysis.fatouDerivEstimate, hEnds⟩

end

end Work.Fatou.FX8
