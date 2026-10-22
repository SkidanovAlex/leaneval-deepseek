import Mathlib
import Submission.Work.ANALYTIC.CechPt.DualComplex
import Submission.Work.ANALYTIC.CechPt.DualCechSetup
import Submission.Work.ANALYTIC.CechPt.dualCech_exact
import Submission.Work.ANALYTIC.CechPt.dualCech_free
import Submission.Work.ANALYTIC.CechPt.contraction_of_exact
import Submission.Work.ANALYTIC.CechPt.DualCechBridge
import Submission.Work.ANALYTIC.CechPt.free_submodule_of_free
import Submission.Work.ANALYTIC.CechPt.sdBridge_natural
import Submission.Work.ANALYTIC.CechPt.DualCechContract
import Submission.Work.ANALYTIC.CechPt.DualCechRho

/-!
# Contractibility of the augmented dual Čech complex of the Cantor cover

`Work.ANALYTIC.CechPt.DualAugContractible` (in `CechPt/DualComplex.lean`) asserts that the
augmented complex

`𝟙 ⟶ sd (ℤ[C_0]) ⟶ sd (ℤ[C_1]) ⟶ ⋯`

of the dual of the free Čech complex of the Cantor cover (`sd X = (X ⟹ 𝟙)`, `C_p = cechTerm p`) is
contractible, i.e. that there are maps `t₀ : sd (ℤ[C_0]) ⟶ 𝟙` and `t_q : sd (ℤ[C_{q+1}]) ⟶
sd (ℤ[C_q])` with

`rho ≫ t₀ = 𝟙`, `dE 0 ≫ t 0 + t₀ ≫ rho = 𝟙`, `dE (q+1) ≫ t (q+1) + t q ≫ dE q = 𝟙`.

## Route

The abelian-group model `DualC p = C(C_p, ℤ)` of `DualCechSetup.lean` carries the transposed Čech
complex, which is exact (`dualCech_exact`) with augmentation `dualAug`; its terms are free
(`dualCech_free`) and so are its kernels (`free_submodule_of_free`).  An exact bounded-below
complex of free `ℤ`-modules is contractible (`contraction_of_exact`), producing maps `h, h₀`
satisfying the three corresponding identities over `ℤ`.

The contraction of the *condensed* complex is the transport of `(h, h₀)` across the bridge
`sdBridge T : sd (ℤ[T]) ≅ C(T,ℤ)_disc` (`DualCechBridge.lean`), which is compatible with the
transposes of the face maps (`sdBridge_natural`, giving compatibility with the differential) and
with the augmentation (`sdBridgeRho` in `DualCechRho.lean`).  The transport and the two
compatibility computations are carried out in `DualCechContract.final_assembly`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

namespace Work.ANALYTIC.CechPt

set_option linter.style.haveILetI false in
theorem dualCech_contractible : Work.ANALYTIC.CechPt.DualAugContractible :=
  final_assembly sdBridge_natural sdBridgeRho (fun p => by
    haveI := dualCech_free p
    exact free_submodule_of_free (DualC p) (LinearMap.ker (dualD p)))

end Work.ANALYTIC.CechPt
