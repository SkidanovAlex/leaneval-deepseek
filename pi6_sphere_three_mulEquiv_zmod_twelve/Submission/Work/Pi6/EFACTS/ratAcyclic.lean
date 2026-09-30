import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.EFACTS.Basic
import Submission.Work.Pi6.EFACTS.p3Model
import Submission.Work.Rat.oddCoverAcyclicFull
import Submission.Work.Serre.serreE3b
import Submission.Work.Serre.serreE4
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6.EFACTS

/-- **`E = S³⟨3⟩` is rationally acyclic through degree `8`.**

`E` is the homotopy fibre of the Postnikov section `g₃ : S³ → P₃`, whose target `P₃` is a range
model of `K(ℤ,3)` through degree `12` (`Work.Pi6.EFACTS.p3Model`) and `g₃` is a `π₃`-bijection
(`PostnikovData 3 12`).  The odd case `n = 3` of `Work.Serre.SerreE3b` (the Gysin/Euler-class
statement for a rational spherical fibration, proved as `Work.Serre.serreE3b`) applied through
`Work.Rat.oddCoverAcyclicFull` (the cover of `Sⁿ` by a `K(ℤ,n)`-model is rationally `S^{2n-1}`
through degree `M`) gives `RatAcyclicBelow E 11`, i.e. `H_t(E;ℚ) = 0` for `0 < t ≤ 11`. -/
theorem ratAcyclic {P3 : Type} [TopologicalSpace P3] (g3 : C(Work.Pi6.S3, P3)) (hP3 : Work.Pi6.PostnikovData 3 12 g3 Work.Pi6.s3) : ∀ i : ℕ, 1 ≤ i → i ≤ 8 → Subsingleton (Work.Pi6.HR ℚ (Work.Pi6.Ecov g3) i) := by
  intro i hi1 hi8
  -- `P₃` is a `K(ℤ,3)`-model through degree `12`
  have hmodel : Work.Serre.IsEMSpaceUpTo ℤ 3 (by norm_num) 12 P3 (g3 Work.Pi6.s3) :=
    p3Model g3 hP3
  -- `g₃` is a `π₃`-bijection
  have hbij : Function.Bijective (Work.Serre.piMapN g3 3 Work.Pi6.s3) :=
    hP3.1 3 (by norm_num) Work.Pi6.s3
  -- the cover `E = hofib g₃` is rationally acyclic through degree `11`
  have hacyc : Work.Serre.RatAcyclicBelow (Work.RatHurewicz.homotopyFibre g3 Work.Pi6.s3) 11 :=
    Work.Rat.oddCoverAcyclicFull Work.Serre.serreE3b Work.Serre.serreE3a 1 (by norm_num) 12
      P3 (g3 Work.Pi6.s3) hmodel Work.Pi6.s3 g3 hbij
  have hzero : IsZero (Work.Serre.ratH (TopCat.of (Work.Pi6.Ecov g3)) i) :=
    hacyc.1 i (by omega) (by omega)
  exact ModuleCat.isZero_iff_subsingleton.mp hzero

end Work.Pi6.EFACTS
