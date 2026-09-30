import Mathlib
import Submission.Work.FoldInst.FoldInvDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Continuity of the Klein-coordinate inverse of a fold chart

The chart map of the class `i` and the sign index `r` is

  `foldTheta i r = coordPerm i ∘ mobiusKlein (N_F · D_r)`

(`FoldPiece.lean`), where `M := N_F · D_r` is a Lorentz matrix preserving the upper sheet
(`foldInst_foldNr_mul_foldDrR_isLorentz`).  Its Klein-coordinate inverse

  `foldInv i r z = kleinOfHyp (M⁻¹ · hypOfUHS (coordPermInv i z))`

is continuous on the image `foldTheta i r '' ball`, because that image is the
`coordPerm i`-image of the upper half space (`mobiusKlein_image_ball`), on which
`q ↦ kleinOfHyp (M⁻¹ · hypOfUHS q)` is continuous: `hypOfUHS` is smooth on the upper half space
and `kleinOfHyp` is smooth off the hyperplane `P 4 = 0`, and `M⁻¹` carries the upper sheet into
itself so that `M⁻¹ · hypOfUHS q` never meets that hyperplane.
-/

open scoped Matrix

namespace Work.FoldInst

theorem continuousOn_foldInv (i : Fin 98) (r : Fin (foldCodim i) → Bool) :
    ContinuousOn (foldInv i r) (foldTheta i r '' HypModel.ball) := by
  have hM : HypModel.IsLorentzMat (foldNr i * foldDrR i r) :=
    foldInst_foldNr_mul_foldDrR_isLorentz i r
  have hMinv : HypModel.IsLorentzMat (foldNr i * foldDrR i r)⁻¹ := isLorentzMat_inv hM
  -- The inverse map is continuous on the upper half space.
  have hg : ContinuousOn
      (fun q : E4 =>
        HypModel.kleinOfHyp ((foldNr i * foldDrR i r)⁻¹ *ᵥ HypModel.hypOfUHS q))
      HypModel.upperHalfSpace := by
    have hA : ContinuousOn HypModel.hypOfUHS HypModel.upperHalfSpace :=
      HypModel.contDiffOn_hypOfUHS.continuousOn
    have hC : ContinuousOn HypModel.kleinOfHyp {P : HypModel.V5 | P 4 ≠ 0} :=
      contDiffOn_kleinOfHyp.continuousOn
    have hB : Continuous (fun P : HypModel.V5 => (foldNr i * foldDrR i r)⁻¹ *ᵥ P) :=
      (HypModel.contDiff_mulVec (foldNr i * foldDrR i r)⁻¹).continuous
    refine hC.comp (hB.comp_continuousOn hA) ?_
    intro q hq
    have hP : HypModel.hypOfUHS q ∈ HypModel.upperSheet :=
      ⟨HypModel.lorentz_hypOfUHS_self (ne_of_gt hq), HypModel.hypOfUHS_four_pos hq⟩
    exact ne_of_gt (HypModel.isLorentzMat_mem_upperSheet hMinv hP).2
  -- The chart image is contained in the domain of the inverse map.
  have hmap : Set.MapsTo (coordPermInv i) (foldTheta i r '' HypModel.ball)
      HypModel.upperHalfSpace := by
    rintro z ⟨y, hy, rfl⟩
    show coordPermInv i (foldTheta i r y) ∈ HypModel.upperHalfSpace
    rw [foldTheta, coordPermInv_comp_coordPerm]
    exact HypModel.mobiusKlein_mem hM hy
  have hcomp : ContinuousOn (foldInv i r) (foldTheta i r '' HypModel.ball) :=
    hg.comp (continuous_coordPermInv i).continuousOn hmap
  exact hcomp

end Work.FoldInst
