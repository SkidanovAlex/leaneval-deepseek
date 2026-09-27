import Mathlib
import Submission.Work.KT.Fund.kappa_hopf_defs

namespace Work.KT.Fund

open _root_.Matrix

noncomputable section

private theorem rr_A (X : Type) [TopologicalSpace X] :
    star (gFun X) * gFun X = (1 - cHeight X) * cHeightInv X := by
  rw [star_gFun X, gFun]
  rw [show star (cCoord X) * cHeightInv X * (cCoord X * cHeightInv X)
      = (star (cCoord X) * cCoord X) * (cHeightInv X * cHeightInv X) from by ring]
  rw [star_cCoord_mul_cCoord X]
  rw [show (1 : C(X × Ball ℂ, ℂ)) - cHeight X * cHeight X
      = (1 - cHeight X) * (1 + cHeight X) from by ring]
  calc (1 - cHeight X) * (1 + cHeight X) * (cHeightInv X * cHeightInv X)
      = (1 - cHeight X) * ((1 + cHeight X) * cHeightInv X) * cHeightInv X := by ring
    _ = (1 - cHeight X) * 1 * cHeightInv X := by rw [hUnit_mul X]
    _ = (1 - cHeight X) * cHeightInv X := by ring

private theorem rr_B (X : Type) [TopologicalSpace X] :
    star (gFun X) * ((1 + cHeight X) * halfC X) = star (cCoord X) * halfC X := by
  rw [star_gFun X]
  calc star (cCoord X) * cHeightInv X * ((1 + cHeight X) * halfC X)
      = star (cCoord X) * (cHeightInv X * (1 + cHeight X)) * halfC X := by ring
    _ = star (cCoord X) * 1 * halfC X := by rw [hUnit_inv_mul X]
    _ = star (cCoord X) * halfC X := by ring

private theorem rr_C (X : Type) [TopologicalSpace X] :
    ((1 + cHeight X) * halfC X) * gFun X = cCoord X * halfC X := by
  rw [gFun]
  calc (1 + cHeight X) * halfC X * (cCoord X * cHeightInv X)
      = cCoord X * ((1 + cHeight X) * cHeightInv X) * halfC X := by ring
    _ = cCoord X * 1 * halfC X := by rw [hUnit_mul X]
    _ = cCoord X * halfC X := by ring

theorem kappa_hopf_reciproj (X : Type) [TopologicalSpace X] :
    Matrix.reindex finSumFinEquiv finSumFinEquiv (recipProj C(X × Ball ℂ, ℂ) (G0 X))
      = !![(1 - cHeight X) * halfC X, star (cCoord X) * halfC X;
           cCoord X * halfC X, (1 + cHeight X) * halfC X] := by
  have hgram : (1 + star (star (gFun X)) * star (gFun X) : C(X × Ball ℂ, ℂ))
      = 2 * cHeightInv X := by
    rw [star_star, mul_comm (gFun X) (star (gFun X))]
    exact F0_gram X
  have hw1 : (1 + star (star (gFun X)) * star (gFun X) : C(X × Ball ℂ, ℂ)) *
      ((1 + cHeight X) * halfC X) = 1 := by
    rw [hgram]
    calc (2 * cHeightInv X) * ((1 + cHeight X) * halfC X)
        = 2 * (cHeightInv X * (1 + cHeight X)) * halfC X := by ring
      _ = 2 * 1 * halfC X := by rw [hUnit_inv_mul X]
      _ = 2 * halfC X := by ring
      _ = 1 := two_mul_halfC X
  have hw2 : ((1 + cHeight X) * halfC X) *
      (1 + star (star (gFun X)) * star (gFun X) : C(X × Ball ℂ, ℂ)) = 1 := by
    rw [hgram]
    calc ((1 + cHeight X) * halfC X) * (2 * cHeightInv X)
        = 2 * ((1 + cHeight X) * cHeightInv X) * halfC X := by ring
      _ = 2 * 1 * halfC X := by rw [hUnit_mul X]
      _ = 2 * halfC X := by ring
      _ = 1 := two_mul_halfC X
  have h00 : star (gFun X) * ((1 + cHeight X) * halfC X) * star (star (gFun X))
      = (1 - cHeight X) * halfC X := by
    rw [star_star]
    calc star (gFun X) * ((1 + cHeight X) * halfC X) * gFun X
        = (star (gFun X) * gFun X) * ((1 + cHeight X) * halfC X) := by ring
      _ = ((1 - cHeight X) * cHeightInv X) * ((1 + cHeight X) * halfC X) := by rw [rr_A X]
      _ = (1 - cHeight X) * (cHeightInv X * (1 + cHeight X)) * halfC X := by ring
      _ = (1 - cHeight X) * 1 * halfC X := by rw [hUnit_inv_mul X]
      _ = (1 - cHeight X) * halfC X := by ring
  have h10 : ((1 + cHeight X) * halfC X) * star (star (gFun X)) = cCoord X * halfC X := by
    rw [star_star]; exact rr_C X
  rw [show G0 X = !![star (gFun X)] from rfl]
  rw [recipProj_one (star (gFun X)) ((1 + cHeight X) * halfC X) hw1 hw2]
  rw [h00, rr_B X, h10]

end

end Work.KT.Fund
