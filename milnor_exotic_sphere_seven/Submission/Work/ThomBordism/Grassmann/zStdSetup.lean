import Mathlib
import Submission.Work.ThomBordism.Grassmann.p1RatAux
import Submission.Work.Thom.Gysin
import Submission.Work.Thom.chernClass
import Submission.Work.Thom.complexification
import Submission.Work.Thom.realification_homeo
import Submission.Work.Thom.pontryaginClass_one

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-!
# The rank-`2` real bundle `zStd` over `ℂP²`, its complexification, and the two pieces

This module fixes the vocabulary of the crux `Work.Thom.pontryagin1 zStd ≠ 0` of
`Submission/Work/ThomBordism/Grassmann/P1_CRUX_PLAN.md`:

* `zStd` — `RealBundle.mapFibre equivC1R2 (realification (tautDual 2))`, the rank-`2` real bundle
  over `ℂP²` in the standard fibre `ℝ²` (`Submission/Work/ThomBordism/Grassmann/p1RatAux.lean`);
* `E₂` — its complexification `ℂ ⊗_ℝ zStd`, a complex rank-`2` bundle (fibre `ℂ²`);
* `W` — the underlying real bundle of `E₂`, real rank `4`; its Thom class is `Tthom`
  (`Work.Thom.thomClassRank 2 _ E₂`), whose Euler class is `c₂(E₂) = -p₁(zStd)`;
* `UR`, `VR` — the two pieces of the punctured total space `X = zeroComplement W` on which the
  real part (resp. the imaginary part) of the fibre coordinate does not vanish.  These are the two
  sets of the Mayer–Vietoris cover of `X` used in the proof of the crux: the transition functions of
  `E₂` are `Work.Thom.cxTrans g = g ⊕ g` on `Re ⊕ Im`, so both conditions are well posed and
  `UR ∪ VR = univ`.
-/

namespace Work.ThomBordism.Grassmann

open Work.TangentClasses

noncomputable section

/-- The complexification of `zStd`: a complex rank-`2` bundle over `ℂP²` with fibre `ℂ²`. -/
def E₂ : VectorBundleCore ℂ (Work.Projective.CP 2) (EuclideanSpace ℂ (Fin 2)) (Fin 3) :=
  Work.Thom.complexificationCore zStd

/-- The underlying real bundle of `E₂`, of real rank `4`. -/
def W : RealBundle (Work.Projective.CP 2) (EuclideanSpace ℂ (Fin 2)) (Fin 3) :=
  Work.Thom.realification E₂

/-- **The canonical Thom class of `W`**, of rank `4 = 2 · 2`. -/
noncomputable def Tthom : Work.Thom.ThomClass W 4 :=
  Work.Thom.thomClassRank 2 (Nat.succ_le_succ (Nat.zero_le 1)) E₂

/-- The defining property: `Tthom` is the canonical Thom class of the complex rank-`2` bundle
`E₂`, so its Euler class is the top Chern class `c₂(E₂)`. -/
theorem chernClass_E₂_eq_euler : Work.Thom.chernClass 2 2 E₂ = Tthom.eulerClass :=
  Work.Thom.chernClass_succ_top' E₂

/-- **`p₁(zStd)` is minus the Euler class of the rank-`4` real bundle `W`.** -/
theorem pontryagin1_zStd_eq : Work.Thom.pontryagin1 zStd = - Tthom.eulerClass := by
  rw [← chernClass_E₂_eq_euler]
  rfl

/-- **The "real part" piece of the punctured total space `X = zeroComplement W`.** -/
def UR : Set ↥(Work.Thom.zeroComplement W) := {p | Work.Thom.cxRePart p.1.2 ≠ 0}

/-- **The "imaginary part" piece of the punctured total space `X = zeroComplement W`.** -/
def VR : Set ↥(Work.Thom.zeroComplement W) := {p | Work.Thom.cxImPart p.1.2 ≠ 0}

end

end Work.ThomBordism.Grassmann
