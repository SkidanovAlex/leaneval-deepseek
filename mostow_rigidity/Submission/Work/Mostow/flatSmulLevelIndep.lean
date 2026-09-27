import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.hptOf_level
import Submission.Work.Mostow.hptOf_hdist
import Submission.Work.Mostow.levYcFormula
import Submission.Work.Mostow.flatActBasic

namespace Work.Mostow

open Submission.Mostow

theorem flatSmulLevelIndep {n : ℕ} (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    {ξ : Submission.Mostow.E n} (hξ : ξ ∈ Submission.Mostow.Sph n)
    (g : LeanEval.Geometry.MostowRigidity.PO n 1) (hg : Submission.Mostow.bd g ξ = ξ)
    (y : Submission.Mostow.E n) (hy : inner ℝ y ξ = 0)
    (E₁ E₂ : ℝ) (h₁ : 0 < E₁) (h₂ : 0 < E₂) :
    Work.Mostow.yc ξ (g • Work.Mostow.hptOf ξ y E₁) = Work.Mostow.yc ξ (g • Work.Mostow.hptOf ξ y E₂) := by
  have hA' : POBasic n := POBasic.ofProp hA
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  have hcpos : 0 < lev ξ (g • (0 : E n)) := lev_pos ξ hξ _
  have hlev₁ : lev ξ (g • hptOf ξ y E₁) = E₁ * lev ξ (g • (0 : E n)) := by
    rw [lev_smul_self hI' hA' ξ hξ g (hptOf ξ y E₁) hg, (hptOf_level ξ hξ E₁ h₁ y hy).1]
  have hlev₂ : lev ξ (g • hptOf ξ y E₂) = E₂ * lev ξ (g • (0 : E n)) := by
    rw [lev_smul_self hI' hA' ξ hξ g (hptOf ξ y E₂) hg, (hptOf_level ξ hξ E₂ h₂ y hy).1]
  have hratio : E₁ * lev ξ (g • (0 : E n)) / (E₂ * lev ξ (g • (0 : E n))) = E₁ / E₂ :=
    mul_div_mul_right _ _ (ne_of_gt hcpos)
  have hdist_g : hdist (g • hptOf ξ y E₁) (g • hptOf ξ y E₂)
      = hdist (hptOf ξ y E₁) (hptOf ξ y E₂) := hI'.isom_smul g _ _
  have hform₁ := levYcFormula hξ (g • hptOf ξ y E₁) (g • hptOf ξ y E₂)
  rw [hlev₁, hlev₂, hratio] at hform₁
  have hform₂ := levYcFormula hξ (hptOf ξ y E₁) (hptOf ξ y E₂)
  rw [(hptOf_level ξ hξ E₁ h₁ y hy).1, (hptOf_level ξ hξ E₂ h₂ y hy).1,
    (hptOf_level ξ hξ E₁ h₁ y hy).2, (hptOf_level ξ hξ E₂ h₂ y hy).2] at hform₂
  have hform₂' : Real.cosh (hdist (hptOf ξ y E₁) (hptOf ξ y E₂))
      = Real.cosh (Real.log (E₁ / E₂)) := by
    rw [hform₂]; simp
  rw [hdist_g, hform₂'] at hform₁
  have hcoef : 0 < E₁ * lev ξ (g • (0 : E n)) * (E₂ * lev ξ (g • (0 : E n))) / 2 := by
    positivity
  have hkey : ‖yc ξ (g • hptOf ξ y E₁) - yc ξ (g • hptOf ξ y E₂)‖ = 0 := by
    by_contra hne
    have hZ : 0 < ‖yc ξ (g • hptOf ξ y E₁) - yc ξ (g • hptOf ξ y E₂)‖ ^ 2 :=
      pow_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)) 2
    have hprod : 0 < (E₁ * lev ξ (g • (0 : E n)) * (E₂ * lev ξ (g • (0 : E n))) / 2)
        * ‖yc ξ (g • hptOf ξ y E₁) - yc ξ (g • hptOf ξ y E₂)‖ ^ 2 :=
      mul_pos hcoef hZ
    linarith [hform₁, hprod]
  exact sub_eq_zero.mp (norm_eq_zero.mp hkey)

end Work.Mostow
