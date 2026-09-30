import Mathlib
import Submission.Work.SSSR.transportTransAux
import Submission.Work.SSSR.TransHalf.halfLeft_eq
import Submission.Work.SSSR.TransHalf.halfRight_eq
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits
/-- The canonical fibre transport of a Serre fibration is compatible with concatenation of paths.
The two pullbacks `Pullback p γ`, `Pullback p δ` and the pullback `Pullback p (γ.trans δ)` over the
concatenation are compared through the homeomorphisms induced by the reparametrisation
`I ≅ [0,1/2]`, `I ≅ [1/2,1]` and the identification of the fibre over the junction point. -/
theorem transportIsoPath_trans {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.SSSR.StemsB.IsSerreFibration p) (j : ℕ)
    {b b' b'' : B} (γ : Path b b') (δ : Path b' b'') :
    Work.SSSR.transportIsoPath p hp (γ.trans δ) j =
      Work.SSSR.transportIsoPath (R := R) p hp γ j ≪≫ Work.SSSR.transportIsoPath p hp δ j := by
  have hL : halfLeft p hp γ δ j =
      (HZHomeoIso (phiZeroHomeo p γ δ) j).symm ≪≫ pathTrans (R := R) p hp γ j ≪≫
        HZHomeoIso (phiTwelfthHomeo p γ δ) j :=
    Work.SSSR.TransHalf.halfLeft_eq p hp γ δ j
  have hR : halfRight p hp γ δ j =
      (HZHomeoIso (psiTwelfthHomeo p γ δ) j).symm ≪≫ pathTrans (R := R) p hp δ j ≪≫
        HZHomeoIso (psiOneHomeo p γ δ) j :=
    Work.SSSR.TransHalf.halfRight_eq p hp γ δ j
  rw [transportIsoPath_eq p hp (γ.trans δ) j, transportIsoPath_eq p hp γ j,
    transportIsoPath_eq p hp δ j]
  rw [pathSrc_trans p γ δ j, pathTgt_trans p γ δ j]
  rw [pathCore, pathCore, pathCore]
  rw [pathTrans_trans_eq p hp γ δ j, hL, hR]
  simp only [Iso.trans_assoc]
  rw [pathTgt_pathSrc_tail]
  rw [leaf_zero_tail, leaf_mid_tail, leaf_one_tail]

end Work.SSSR
