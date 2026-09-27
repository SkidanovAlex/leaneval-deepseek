import Mathlib
import Submission.Work.KT.EG.KLG.kappa_bott_defs
import Submission.Work.KT.Fund.kappa_hopf_pullup
import Submission.Work.KT.Fund.kappa_hopf_pulldn

namespace Work.KT.EG.KLG

open _root_.Matrix
open Work.KT.Fund.KL

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

/-! ## Generic `2 × 2` matrix algebra for the chart identities -/

section Generic

variable {R : Type} [CommRing R]

/-- `R₁ * A = A` with `R₁ = !![1,0;uw,0]`, `A = !![1+s,v;u,1-s]`. -/
lemma chart_R1_mul (s u v w : R) (huv : u * v = 1 - s * s) (h : (1 + s) * w = 1) :
    !![1, 0; u * w, 0] * !![1 + s, v; u, 1 - s] = !![1 + s, v; u, 1 - s] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  · linear_combination u * h
  · linear_combination w * huv + (1 - s) * h

/-- `A * R₁ = 2 • R₁`. -/
lemma chart_mul_R1 (s u v w : R) (huv : u * v = 1 - s * s)
    (h : (1 + s) * w = 1) (h3 : w * (1 + s) = 1) :
    !![1 + s, v; u, 1 - s] * !![1, 0; u * w, 0] = (2 : R) • !![1, 0; u * w, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  · linear_combination w * huv + (1 - s) * h
  · linear_combination (-u) * h3

/-- `R₂ * B = B` with `R₂ = !![uv, v(s s)w; (1+s)u, s s]`, `B = !![1-s,v;u,1+s]`. -/
lemma chart_R2_mul (s u v w : R) (huv : u * v = 1 - s * s) (h : (1 + s) * w = 1) :
    !![u * v, v * (s * s) * w; (1 + s) * u, s * s] * !![1 - s, v; u, 1 + s]
      = !![1 - s, v; u, 1 + s] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  · linear_combination (1 - s + s * s * w) * huv + (s * s * (1 - s)) * h
  · linear_combination v * huv + v * s * s * h
  · ring
  · linear_combination (1 + s) * huv

/-- `B * R₂ = 2 • R₂`. -/
lemma chart_mul_R2 (s u v w : R) (huv : u * v = 1 - s * s)
    (h : (1 + s) * w = 1) (h3 : w * (1 + s) = 1) :
    !![1 - s, v; u, 1 + s] * !![u * v, v * (s * s) * w; (1 + s) * u, s * s]
      = (2 : R) • !![u * v, v * (s * s) * w; (1 + s) * u, s * s] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  · ring
  · linear_combination (-(v * s * s)) * h3
  · linear_combination u * huv
  · linear_combination (s * s * w) * huv + (s * s) * h3 + (-(s * s * s)) * h3

end Generic

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-! ## Identifications of the chart data -/

lemma halfC_eq_algebraMap :
    Work.KT.Fund.halfC X = algebraMap ℂ C(X × Ball ℂ, ℂ) (1 / 2) := by
  ext p
  rfl

lemma two_mul_algebraMap_half :
    (2 : C(X × Ball ℂ, ℂ)) * algebraMap ℂ C(X × Ball ℂ, ℂ) (1 / 2) = 1 := by
  rw [← halfC_eq_algebraMap X, Work.KT.Fund.two_mul_halfC X]

lemma algebraMap_half_mul_two :
    algebraMap ℂ C(X × Ball ℂ, ℂ) (1 / 2) * (2 : C(X × Ball ℂ, ℂ)) = 1 := by
  rw [mul_comm, two_mul_algebraMap_half X]

lemma RhopUp_eq_pull :
    RhopUp X = (Work.KT.Fund.hopfMat.map
        (Work.KT.pullAlg (ContinuousMap.snd : C(X × S2, S2))).toRingHom).map
          (Work.KT.Fund.pullUp X) := rfl

lemma RhopDn_eq_pull :
    RhopDn X = (Work.KT.Fund.hopfMat.map
        (Work.KT.pullAlg (ContinuousMap.snd : C(X × S2, S2))).toRingHom).map
          (Work.KT.Fund.pullDn X) := rfl

/-! ## The chart formulas -/

lemma RhopUp_chart :
    RhopUp X = algebraMap ℂ C(X × Ball ℂ, ℂ) (1 / 2) •
      !![1 + zs X, zcb X; zc X, 1 - zs X] := by
  rw [RhopUp_eq_pull X, Work.KT.Fund.kappa_hopf_pullup X, ← halfC_eq_algebraMap X]
  ext i j p
  fin_cases i <;> fin_cases j <;>
    simp [Work.KT.Fund.cHeight, Work.KT.Fund.cCoord, Work.KT.Fund.halfC, zs, zc, zcb,
      Matrix.smul_apply, smul_eq_mul, ContinuousMap.star_apply]
  all_goals ring

lemma RhopDn_chart :
    RhopDn X = algebraMap ℂ C(X × Ball ℂ, ℂ) (1 / 2) •
      !![1 - zs X, zcb X; zc X, 1 + zs X] := by
  rw [RhopDn_eq_pull X, Work.KT.Fund.kappa_hopf_pulldn X, ← halfC_eq_algebraMap X]
  ext i j p
  fin_cases i <;> fin_cases j <;>
    simp [Work.KT.Fund.cHeight, Work.KT.Fund.cCoord, Work.KT.Fund.halfC, zs, zc, zcb,
      Matrix.smul_apply, smul_eq_mul, ContinuousMap.star_apply]
  all_goals ring

/-! ## The multiplication identities -/

lemma R1_mul_Aup :
    R1 X * !![1 + zs X, zcb X; zc X, 1 - zs X] = !![1 + zs X, zcb X; zc X, 1 - zs X] :=
  chart_R1_mul (zs X) (zc X) (zcb X) (zsinv X) (zc_mul_zcb_eq X) (one_add_zs_mul_zsinv X)

lemma Aup_mul_R1 :
    !![1 + zs X, zcb X; zc X, 1 - zs X] * R1 X =
      (2 : C(X × Ball ℂ, ℂ)) • R1 X :=
  chart_mul_R1 (zs X) (zc X) (zcb X) (zsinv X) (zc_mul_zcb_eq X)
    (one_add_zs_mul_zsinv X) (zsinv_mul_one_add_zs X)

lemma R2_mul_Adn :
    R2 X * !![1 - zs X, zcb X; zc X, 1 + zs X] = !![1 - zs X, zcb X; zc X, 1 + zs X] :=
  chart_R2_mul (zs X) (zc X) (zcb X) (zsinv X) (zc_mul_zcb_eq X) (one_add_zs_mul_zsinv X)

lemma Adn_mul_R2 :
    !![1 - zs X, zcb X; zc X, 1 + zs X] * R2 X =
      (2 : C(X × Ball ℂ, ℂ)) • R2 X :=
  chart_mul_R2 (zs X) (zc X) (zcb X) (zsinv X) (zc_mul_zcb_eq X)
    (one_add_zs_mul_zsinv X) (zsinv_mul_one_add_zs X)

theorem Rhop_chart (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    (Work.KT.Fund.KL.RhopUp X = (algebraMap ℂ C(X × Work.KT.Ball ℂ, ℂ) (1 / 2)) •
      !![1 + Work.KT.Fund.KL.zs X, Work.KT.Fund.KL.zcb X;
        Work.KT.Fund.KL.zc X, 1 - Work.KT.Fund.KL.zs X]) ∧
    (Work.KT.Fund.KL.RhopDn X = (algebraMap ℂ C(X × Work.KT.Ball ℂ, ℂ) (1 / 2)) •
      !![1 - Work.KT.Fund.KL.zs X, Work.KT.Fund.KL.zcb X;
        Work.KT.Fund.KL.zc X, 1 + Work.KT.Fund.KL.zs X]) ∧
    (Work.KT.EG.KLG.R1 X * Work.KT.Fund.KL.RhopUp X = Work.KT.Fund.KL.RhopUp X) ∧
    (Work.KT.Fund.KL.RhopUp X * Work.KT.EG.KLG.R1 X = Work.KT.EG.KLG.R1 X) ∧
    (Work.KT.EG.KLG.R2 X * Work.KT.Fund.KL.RhopDn X = Work.KT.Fund.KL.RhopDn X) ∧
    (Work.KT.Fund.KL.RhopDn X * Work.KT.EG.KLG.R2 X = Work.KT.EG.KLG.R2 X) := by
  refine ⟨RhopUp_chart X, RhopDn_chart X, ?_, ?_, ?_, ?_⟩
  · rw [RhopUp_chart X, Matrix.mul_smul, R1_mul_Aup X]
  · rw [RhopUp_chart X, Matrix.smul_mul, Aup_mul_R1 X, smul_smul, algebraMap_half_mul_two X,
      one_smul]
  · rw [RhopDn_chart X, Matrix.mul_smul, R2_mul_Adn X]
  · rw [RhopDn_chart X, Matrix.smul_mul, Adn_mul_R2 X, smul_smul, algebraMap_half_mul_two X,
      one_smul]

end

end Work.KT.EG.KLG
