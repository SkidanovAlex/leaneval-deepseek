/-
A thin import-bridge so that lemma requests under `Submission/Work/` can declare both the
`Commons` `L²`-multiplier machinery (`Commons.Analysis.Fourier.BoundaryLayer.multiplier`, via
`BLRepro`) and the a.e. identification of the Plancherel inverse transform with the pointwise
inverse Fourier integral (`fourierInv_toLp_ae_eq_fourierInv`) as dependencies.  Nothing is proved
here.
-/
import Submission.Work.BourgainPlan.Maximal.BLRepro
import Submission.Commons.Analysis.Fourier.fourierInv_toLp_ae_eq_fourierInv
