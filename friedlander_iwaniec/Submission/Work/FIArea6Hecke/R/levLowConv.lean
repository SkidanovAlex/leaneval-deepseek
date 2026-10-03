import Mathlib
import Submission.Work.FIArea6Hecke.R.levelHeckeDefs

namespace Work.FIArea6Hecke.R

open MeasureTheory Set
open scoped ComplexConjugate

/-- `MellinConvergent` depends only on the values of `f` on `(0,∞)`. -/
private lemma mellinConvergent_congr_Ioi {f g : ℝ → ℂ} {s : ℂ}
    (h : ∀ u : ℝ, 0 < u → f u = g u) : MellinConvergent f s ↔ MellinConvergent g s := by
  unfold MellinConvergent
  refine integrableOn_congr_fun (fun u hu => ?_) measurableSet_Ioi
  rw [h u hu]

/-- The convergence of the lower cutoff at `t` follows from the convergence of the upper
conjugate cutoff at `m + 1 - t`, by the change of variables `u ↦ 1/(B u)` combined with the
theta law.  This is the level-`R` form of
`Work.FIArea5.S16Hecke.mellinConvergent_thetaCutLow`. -/
theorem levLowConv (B : ℝ) (hB : 0 < B) (f : ℝ → ℂ) (m : ℕ) (A : ℂ)
    (hlaw : ∀ u : ℝ, 0 < u → f u = A * ((u : ℂ) ^ (-(m : ℤ) - 1)) * star (f (1 / (B * u))))
    (t : ℂ) (ht : MellinConvergent (thetaCutHiStar B f) ((m : ℂ) + 1 - t)) :
    MellinConvergent (thetaCutLo B f) t := by
  have hcast : ((-1 : ℝ) : ℂ) = -1 := by norm_num
  have h1 : MellinConvergent (fun v : ℝ => thetaCutHiStar B f (v ^ (-1 : ℝ)))
      (t - ((m : ℂ) + 1)) := by
    refine (MellinConvergent.comp_rpow (f := thetaCutHiStar B f) (a := (-1 : ℝ)) (by norm_num)
      (s := t - ((m : ℂ) + 1))).mpr ?_
    rw [show (t - ((m : ℂ) + 1)) / ((-1 : ℝ) : ℂ) = ((m : ℂ) + 1 - t) by rw [hcast]; ring]
    exact ht
  have h2 : MellinConvergent (fun u : ℝ => thetaCutHiStar B f ((B * u) ^ (-1 : ℝ)))
      (t - ((m : ℂ) + 1)) :=
    (MellinConvergent.comp_mul_left (f := fun v : ℝ => thetaCutHiStar B f (v ^ (-1 : ℝ)))
      (a := B) hB (s := t - ((m : ℂ) + 1))).mpr h1
  have h3 : MellinConvergent
      (fun u : ℝ => ((u : ℂ) ^ (-((m : ℂ) + 1))) • thetaCutHiStar B f ((B * u) ^ (-1 : ℝ)))
      t := by
    refine (MellinConvergent.cpow_smul
      (f := fun u : ℝ => thetaCutHiStar B f ((B * u) ^ (-1 : ℝ)))
      (a := -((m : ℂ) + 1)) (s := t)).mpr ?_
    rw [show t + (-((m : ℂ) + 1)) = t - ((m : ℂ) + 1) by ring]
    exact h2
  have h4 : MellinConvergent
      (fun u : ℝ => A •
        (((u : ℂ) ^ (-((m : ℂ) + 1))) • thetaCutHiStar B f ((B * u) ^ (-1 : ℝ)))) t :=
    h3.const_smul A
  have h5 : MellinConvergent
      (fun u : ℝ => A •
        (((u : ℂ) ^ (-((m : ℂ) + 1))) • thetaCutHiStar B f (1 / (B * u)))) t := by
    refine (mellinConvergent_congr_Ioi
      (f := fun u : ℝ => A •
        (((u : ℂ) ^ (-((m : ℂ) + 1))) • thetaCutHiStar B f ((B * u) ^ (-1 : ℝ))))
      (g := fun u : ℝ => A •
        (((u : ℂ) ^ (-((m : ℂ) + 1))) • thetaCutHiStar B f (1 / (B * u)))) ?_).mp h4
    intro u _
    rw [Real.rpow_neg_one, one_div]
  refine (mellinConvergent_congr_Ioi
    (f := fun u : ℝ => A •
      (((u : ℂ) ^ (-((m : ℂ) + 1))) • thetaCutHiStar B f (1 / (B * u))))
    (g := thetaCutLo B f) ?_).mp h5
  intro u hu
  exact (thetaCutLo_eq_smul B hB f m A hlaw u hu).symm

end Work.FIArea6Hecke.R
