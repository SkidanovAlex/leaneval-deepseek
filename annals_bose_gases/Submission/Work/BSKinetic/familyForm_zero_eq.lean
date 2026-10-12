import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BSKinetic.integrable_bsJoint_J1
import Submission.Work.BSKinetic.integrable_bsJoint_J2
import Submission.Work.BSKinetic.integrable_bsJoint_J3
import Submission.Work.BSKinetic.integral_bsWin_deriv_sq
import Submission.Work.BSKinetic.sum_integral_mul_fderiv_fderiv
import Submission.Work.BSKinetic.winForm_sq_hasCompactSupport
import Submission.Work.BSKinetic.windowedMul_dirichlet_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BSKinetic

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ## helper definitions of the three blocks -/

private noncomputable def ffz_ffA (ℓ : ℝ) (ψ : ℝ³ → ℝ) (u : ℝ³) : ℝ :=
  ∫ x : ℝ³, ∑ k : Fin 3,
    (fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * bsQ ℓ u ψ y) x (kcStdBasis k)) ^ 2

private noncomputable def ffz_ffP (ℓ : ℝ) (ψ : ℝ³ → ℝ) (u : ℝ³) : ℝ :=
  ∫ x : ℝ³, ∑ k : Fin 3,
    (bsQ ℓ u ψ x) ^ 2 * (fderiv ℝ (bsWin ℓ u) x (kcStdBasis k)) ^ 2

private noncomputable def ffz_ffZ (ℓ : ℝ) (ψ : ℝ³ → ℝ) (u : ℝ³) : ℝ :=
  ∫ x : ℝ³, ∑ k : Fin 3,
    (bsWin ℓ u x) ^ 2 * (bsQ ℓ u ψ x) *
      (fderiv ℝ (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) x (kcStdBasis k))

private noncomputable def ffz_ffZ2 (ℓ : ℝ) (ψ : ℝ³ → ℝ) (u : ℝ³) : ℝ :=
  ∫ x : ℝ³, ∑ k : Fin 3,
    (bsWin ℓ u x) ^ 2 * ψ x *
      (fderiv ℝ (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) x (kcStdBasis k))

private noncomputable def ffz_ffZ3 (ℓ : ℝ) (ψ : ℝ³ → ℝ) (u : ℝ³) : ℝ :=
  ∫ x : ℝ³, ∑ k : Fin 3,
    bsMean ℓ u ψ * (bsWin ℓ u x) ^ 2 *
      (fderiv ℝ (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) x (kcStdBasis k))

private noncomputable def ffz_ffJ1 (k : Fin 3) (ℓ : ℝ) (ψ : ℝ³ → ℝ) (x u : ℝ³) : ℝ :=
  (bsQ ℓ u ψ x) ^ 2 * (fderiv ℝ (bsWin ℓ u) x (kcStdBasis k)) ^ 2

private noncomputable def ffz_ffJ2 (k : Fin 3) (ℓ : ℝ) (ψ : ℝ³ → ℝ) (x u : ℝ³) : ℝ :=
  (bsWin ℓ u x) ^ 2 * ψ x *
    (fderiv ℝ (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) x (kcStdBasis k))

private noncomputable def ffz_ffJ3 (k : Fin 3) (ℓ : ℝ) (ψ : ℝ³ → ℝ) (x u : ℝ³) : ℝ :=
  bsMean ℓ u ψ * (bsWin ℓ u x) ^ 2 *
    (fderiv ℝ (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) x (kcStdBasis k))

/-! ## elementary helpers -/

private lemma ffz_bsWin_contDiff {ℓ : ℝ} (hℓ : ℓ ≠ 0) (u : ℝ³) :
    ContDiff ℝ (⊤ : ENat) (bsWin ℓ u) := by
  unfold bsWin
  exact (chiScale_contDiff hℓ).comp (contDiff_id.sub contDiff_const)

private lemma ffz_bsWin_hasCompactSupport {ℓ : ℝ} (hℓ : ℓ ≠ 0) (u : ℝ³) :
    HasCompactSupport (bsWin ℓ u) := by
  unfold bsWin
  have h := (chiScale_hasCompactSupport hℓ).comp_homeomorph (Homeomorph.subRight (ℓ • u))
  simpa [Function.comp_def, Homeomorph.coe_subRight] using h

private lemma ffz_bsQ_contDiff {ℓ : ℝ} (u : ℝ³) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) : ContDiff ℝ (⊤ : ENat) (bsQ ℓ u ψ) := by
  unfold bsQ
  exact hψ.sub contDiff_const

private lemma ffz_fderiv_fderiv_bsQ {ℓ : ℝ} (u : ℝ³) (ψ : ℝ³ → ℝ) (k : Fin 3) (x : ℝ³) :
    fderiv ℝ (fun y : ℝ³ => fderiv ℝ (bsQ ℓ u ψ) y (kcStdBasis k)) x (kcStdBasis k)
      = fderiv ℝ (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) x (kcStdBasis k) := by
  have hfun : (fun y : ℝ³ => fderiv ℝ (bsQ ℓ u ψ) y (kcStdBasis k))
      = (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) := by
    funext y
    congr 1
    show fderiv ℝ (fun z : ℝ³ => ψ z - bsMean ℓ u ψ) y = fderiv ℝ ψ y
    rw [fderiv_sub_const]
  rw [hfun]

private lemma ffz_integral_bsWin_sq {ℓ : ℝ} (hℓ : 0 < ℓ) (x : ℝ³) :
    (∫ u : ℝ³, (bsWin ℓ u x) ^ 2) = 1 := by
  have h : (fun u : ℝ³ => (bsWin ℓ u x) ^ 2)
      = (fun u : ℝ³ => (chiScale ℓ (x - ℓ • u)) ^ 2) := rfl
  rw [h]
  exact Work.UBBInputs9.B.integral_chiScale_sub_smul_sq ℓ hℓ x

private lemma ffz_hasCompactSupport_fderiv_bsWin {ℓ : ℝ} (hℓ : ℓ ≠ 0) (u : ℝ³) (k : Fin 3) :
    HasCompactSupport (fun x : ℝ³ => fderiv ℝ (bsWin ℓ u) x (kcStdBasis k)) := by
  have hbase : HasCompactSupport (fun z : ℝ³ => fderiv ℝ (chiScale ℓ) z (kcStdBasis k)) :=
    (chiScale_hasCompactSupport hℓ).fderiv_apply ℝ (kcStdBasis k)
  have h := hbase.comp_homeomorph (Homeomorph.subRight (ℓ • u))
  have heq : (fun x : ℝ³ => fderiv ℝ (bsWin ℓ u) x (kcStdBasis k))
      = (fun x : ℝ³ => fderiv ℝ (chiScale ℓ) (x - ℓ • u) (kcStdBasis k)) := by
    funext x
    rw [show bsWin ℓ u = fun y : ℝ³ => chiScale ℓ (y - ℓ • u) from rfl]
    exact fderiv_comp_sub_const_apply (chiScale ℓ) (ℓ • u) x (kcStdBasis k)
      ((chiScale_contDiff hℓ).differentiable (by simp) _)
  rw [heq]
  simpa [Function.comp_def, Homeomorph.coe_subRight] using h

private lemma ffz_continuous_fderiv_bsWin {ℓ : ℝ} (hℓ : ℓ ≠ 0) (u : ℝ³) (k : Fin 3) :
    Continuous (fun x : ℝ³ => fderiv ℝ (bsWin ℓ u) x (kcStdBasis k)) :=
  (ffz_bsWin_contDiff hℓ u).continuous_fderiv (by simp) |>.clm_apply continuous_const

private lemma ffz_cs_bsWin_sq {ℓ : ℝ} (hℓ : ℓ ≠ 0) (u : ℝ³) :
    HasCompactSupport (fun x : ℝ³ => (bsWin ℓ u x) ^ 2) :=
  (ffz_bsWin_hasCompactSupport hℓ u).comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)

private lemma ffz_continuous_bsWin_sq {ℓ : ℝ} (hℓ : ℓ ≠ 0) (u : ℝ³) :
    Continuous (fun x : ℝ³ => (bsWin ℓ u x) ^ 2) :=
  ((ffz_bsWin_contDiff hℓ u).continuous).pow 2

private lemma ffz_contDiff_fderiv_apply_apply {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (k : Fin 3) :
    ContDiff ℝ (⊤ : ENat) (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) := by
  have h1 : ContDiff ℝ (⊤ : ENat) (fderiv ℝ ψ) :=
    (hψ.fderiv_right (m := (⊤ : ENat))) (by simp)
  exact h1.clm_apply contDiff_const

private lemma ffz_continuous_fderiv_fderiv {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (k : Fin 3) :
    Continuous (fun x : ℝ³ =>
      fderiv ℝ (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) x (kcStdBasis k)) :=
  ((ffz_contDiff_fderiv_apply_apply hψ k).continuous_fderiv (by simp)).clm_apply continuous_const

private lemma ffz_integrable_ffJ1_x {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (u : ℝ³) (k : Fin 3) :
    Integrable (fun x : ℝ³ => (bsQ ℓ u ψ x) ^ 2 *
        (fderiv ℝ (bsWin ℓ u) x (kcStdBasis k)) ^ 2) (volume : Measure ℝ³) := by
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  have hcont : Continuous (fun x : ℝ³ => (bsQ ℓ u ψ x) ^ 2 *
      (fderiv ℝ (bsWin ℓ u) x (kcStdBasis k)) ^ 2) := by
    exact (((hψ.continuous.sub continuous_const).pow 2).mul
      ((ffz_continuous_fderiv_bsWin hℓne u k).pow 2))
  have hcs : HasCompactSupport (fun x : ℝ³ => (bsQ ℓ u ψ x) ^ 2 *
      (fderiv ℝ (bsWin ℓ u) x (kcStdBasis k)) ^ 2) :=
    ((ffz_hasCompactSupport_fderiv_bsWin hℓne u k).comp_left
      (g := fun t : ℝ => t ^ 2) (by norm_num)).mul_left
  exact hcont.integrable_of_hasCompactSupport hcs

private lemma ffz_integrable_ffJ2_x {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (u : ℝ³) (k : Fin 3) :
    Integrable (fun x : ℝ³ => (bsWin ℓ u x) ^ 2 * ψ x *
        (fderiv ℝ (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) x (kcStdBasis k)))
      (volume : Measure ℝ³) := by
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  have hcont : Continuous (fun x : ℝ³ => (bsWin ℓ u x) ^ 2 * ψ x *
      (fderiv ℝ (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) x (kcStdBasis k))) := by
    exact ((ffz_continuous_bsWin_sq hℓne u).mul hψ.continuous).mul
      (ffz_continuous_fderiv_fderiv hψ k)
  have hcs : HasCompactSupport (fun x : ℝ³ => (bsWin ℓ u x) ^ 2 * ψ x *
      (fderiv ℝ (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) x (kcStdBasis k))) :=
    ((ffz_cs_bsWin_sq hℓne u).mul_right).mul_right
  exact hcont.integrable_of_hasCompactSupport hcs

private lemma ffz_integrable_win_sq_fderiv2_x {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (u : ℝ³) (k : Fin 3) :
    Integrable (fun x : ℝ³ => (bsWin ℓ u x) ^ 2 *
        (fderiv ℝ (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) x (kcStdBasis k)))
      (volume : Measure ℝ³) := by
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  have hcont : Continuous (fun x : ℝ³ => (bsWin ℓ u x) ^ 2 *
      (fderiv ℝ (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) x (kcStdBasis k))) :=
    (ffz_continuous_bsWin_sq hℓne u).mul (ffz_continuous_fderiv_fderiv hψ k)
  have hcs : HasCompactSupport (fun x : ℝ³ => (bsWin ℓ u x) ^ 2 *
      (fderiv ℝ (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) x (kcStdBasis k))) :=
    (ffz_cs_bsWin_sq hℓne u).mul_right
  exact hcont.integrable_of_hasCompactSupport hcs

private lemma ffz_integrable_ffJ3_x {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (u : ℝ³) (k : Fin 3) :
    Integrable (fun x : ℝ³ => bsMean ℓ u ψ * (bsWin ℓ u x) ^ 2 *
        (fderiv ℝ (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) x (kcStdBasis k)))
      (volume : Measure ℝ³) := by
  have hbase := ffz_integrable_win_sq_fderiv2_x hℓ hψ u k
  have hconst : Integrable (fun x : ℝ³ => bsMean ℓ u ψ *
      ((bsWin ℓ u x) ^ 2 *
        (fderiv ℝ (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) x (kcStdBasis k)))) :=
    hbase.const_mul _
  refine hconst.congr (Eventually.of_forall (fun x => ?_))
  ring


/-! ## the assembly -/

theorem familyForm_zero_eq {ℓ : ℝ} (hℓ : 0 < ℓ) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    Work.BSKinetic.bsFamilyForm ℓ (fun r => r ^ 2) ψ
      = Work.BSKinetic.dSpace ψ
        + (∑ k : Fin 3, ∫ u : EuclideanSpace ℝ (Fin 3),
            Work.BSKinetic.bsMean ℓ u ψ *
              ∫ x : EuclideanSpace ℝ (Fin 3), (Work.BSKinetic.bsWin ℓ u x) ^ 2 *
                (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) =>
                    fderiv ℝ ψ y (Submission.BoseGases.kcStdBasis k)) x
                  (Submission.BoseGases.kcStdBasis k)))
        + (∑ k : Fin 3, ∫ u : EuclideanSpace ℝ (Fin 3),
            ∫ x : EuclideanSpace ℝ (Fin 3), (Work.BSKinetic.bsQ ℓ u ψ x) ^ 2 *
              (fderiv ℝ (Work.BSKinetic.bsWin ℓ u) x
                (Submission.BoseGases.kcStdBasis k)) ^ 2) := by
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  have h1 : bsFamilyForm ℓ (fun r => r ^ 2) ψ = ∫ u : ℝ³, ffz_ffA ℓ ψ u := by
    simp only [bsFamilyForm, ffz_ffA]
    apply integral_congr_ae
    filter_upwards with u
    rw [show bsOneBody ℓ (fun r => r ^ 2) u ψ
        = Submission.BoseGases.winModeForm (bsWin ℓ u) (fun r => r ^ 2) (bsQ ℓ u ψ) from rfl]
    exact winForm_sq_hasCompactSupport (ffz_bsWin_contDiff hℓne u) (ffz_bsQ_contDiff u hψ)
      (ffz_bsWin_hasCompactSupport hℓne u)
  have hperP : ∀ u : ℝ³, ffz_ffP ℓ ψ u = ∑ k : Fin 3, ∫ x : ℝ³, ffz_ffJ1 k ℓ ψ x u := by
    intro u
    exact integral_finsetSum Finset.univ (f := fun (k : Fin 3) (x : ℝ³) => ffz_ffJ1 k ℓ ψ x u)
      (fun k _ => ffz_integrable_ffJ1_x hℓ hψ u k)
  have hperZ2 : ∀ u : ℝ³, ffz_ffZ2 ℓ ψ u = ∑ k : Fin 3, ∫ x : ℝ³, ffz_ffJ2 k ℓ ψ x u := by
    intro u
    exact integral_finsetSum Finset.univ (f := fun (k : Fin 3) (x : ℝ³) => ffz_ffJ2 k ℓ ψ x u)
      (fun k _ => ffz_integrable_ffJ2_x hℓ hψ u k)
  have hperZ3 : ∀ u : ℝ³, ffz_ffZ3 ℓ ψ u = ∑ k : Fin 3, ∫ x : ℝ³, ffz_ffJ3 k ℓ ψ x u := by
    intro u
    exact integral_finsetSum Finset.univ (f := fun (k : Fin 3) (x : ℝ³) => ffz_ffJ3 k ℓ ψ x u)
      (fun k _ => ffz_integrable_ffJ3_x hℓ hψ u k)
  have hZspl : ∀ u : ℝ³, ffz_ffZ ℓ ψ u = ffz_ffZ2 ℓ ψ u - ffz_ffZ3 ℓ ψ u := by
    intro u
    change (∫ x : ℝ³, ∑ k : Fin 3, (bsWin ℓ u x) ^ 2 * (bsQ ℓ u ψ x) *
        (fderiv ℝ (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) x (kcStdBasis k)))
      = (∫ x : ℝ³, ∑ k : Fin 3, (bsWin ℓ u x) ^ 2 * ψ x *
            (fderiv ℝ (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) x (kcStdBasis k)))
        - (∫ x : ℝ³, ∑ k : Fin 3, bsMean ℓ u ψ * (bsWin ℓ u x) ^ 2 *
            (fderiv ℝ (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) x (kcStdBasis k)))
    rw [integral_congr_ae (Eventually.of_forall (fun x : ℝ³ => ?_))]
    · exact integral_sub
        (integrable_finsetSum Finset.univ (fun k _ => ffz_integrable_ffJ2_x hℓ hψ u k))
        (integrable_finsetSum Finset.univ (fun k _ => ffz_integrable_ffJ3_x hℓ hψ u k))
    · rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun k _ => by simp only [bsQ]; ring)
  have hIntP : Integrable (ffz_ffP ℓ ψ) (volume : Measure ℝ³) := by
    rw [show ffz_ffP ℓ ψ = fun u : ℝ³ => ∑ k : Fin 3, ∫ x : ℝ³, ffz_ffJ1 k ℓ ψ x u
        from funext hperP]
    exact integrable_finsetSum Finset.univ
      (fun k _ => (integrable_bsJoint_J1 hℓ hψ hcs k).integral_prod_right)
  have hIntZ2 : Integrable (ffz_ffZ2 ℓ ψ) (volume : Measure ℝ³) := by
    rw [show ffz_ffZ2 ℓ ψ = fun u : ℝ³ => ∑ k : Fin 3, ∫ x : ℝ³, ffz_ffJ2 k ℓ ψ x u
        from funext hperZ2]
    exact integrable_finsetSum Finset.univ
      (fun k _ => (integrable_bsJoint_J2 hℓ hψ hcs k).integral_prod_right)
  have hIntZ3 : Integrable (ffz_ffZ3 ℓ ψ) (volume : Measure ℝ³) := by
    rw [show ffz_ffZ3 ℓ ψ = fun u : ℝ³ => ∑ k : Fin 3, ∫ x : ℝ³, ffz_ffJ3 k ℓ ψ x u
        from funext hperZ3]
    exact integrable_finsetSum Finset.univ
      (fun k _ => (integrable_bsJoint_J3 hℓ hψ hcs k).integral_prod_right)
  have hIntZ : Integrable (ffz_ffZ ℓ ψ) (volume : Measure ℝ³) := by
    rw [show ffz_ffZ ℓ ψ = fun u : ℝ³ => ffz_ffZ2 ℓ ψ u - ffz_ffZ3 ℓ ψ u from funext hZspl]
    exact hIntZ2.sub hIntZ3
  have h2 : ∀ u : ℝ³, ffz_ffA ℓ ψ u = ffz_ffP ℓ ψ u - ffz_ffZ ℓ ψ u := by
    intro u
    have hD2 := windowedMul_dirichlet_eq (χ := bsWin ℓ u) (F := bsQ ℓ u ψ)
      (ffz_bsWin_contDiff hℓne u) (ffz_bsWin_hasCompactSupport hℓne u) (ffz_bsQ_contDiff u hψ)
    have hkey : (∫ x : ℝ³, ∑ k : Fin 3, (bsWin ℓ u x) ^ 2 * (bsQ ℓ u ψ x) *
          (fderiv ℝ (fun y : ℝ³ => fderiv ℝ (bsQ ℓ u ψ) y (kcStdBasis k)) x
            (kcStdBasis k)))
        = (∫ x : ℝ³, ∑ k : Fin 3, (bsWin ℓ u x) ^ 2 * (bsQ ℓ u ψ x) *
          (fderiv ℝ (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) x (kcStdBasis k))) := by
      apply integral_congr_ae
      filter_upwards with x
      exact Finset.sum_congr rfl (fun k _ => by rw [ffz_fderiv_fderiv_bsQ u ψ k x])
    have hswap : (∫ x : ℝ³, ∑ k : Fin 3, (fderiv ℝ (bsWin ℓ u) x) (kcStdBasis k) ^ 2 *
          (bsQ ℓ u ψ x) ^ 2)
        = ∫ x : ℝ³, ∑ k : Fin 3, (bsQ ℓ u ψ x) ^ 2 *
          (fderiv ℝ (bsWin ℓ u) x) (kcStdBasis k) ^ 2 := by
      apply integral_congr_ae
      filter_upwards with x
      exact Finset.sum_congr rfl (fun k _ => by ring)
    simp only [ffz_ffA, ffz_ffP, ffz_ffZ]
    rw [hD2, hkey, hswap]
  have h3 : (∫ u : ℝ³, ffz_ffP ℓ ψ u)
      = ∑ k : Fin 3, ∫ u : ℝ³, ∫ x : ℝ³, ffz_ffJ1 k ℓ ψ x u := by
    rw [show (∫ u : ℝ³, ffz_ffP ℓ ψ u)
        = ∫ u : ℝ³, ∑ k : Fin 3, ∫ x : ℝ³, ffz_ffJ1 k ℓ ψ x u
        from integral_congr_ae (Eventually.of_forall hperP)]
    rw [integral_finsetSum Finset.univ
      (f := fun (k : Fin 3) (u : ℝ³) => ∫ x : ℝ³, ffz_ffJ1 k ℓ ψ x u)
      (fun k _ => (integrable_bsJoint_J1 hℓ hψ hcs k).integral_prod_right)]
  have h4 : (∫ u : ℝ³, ffz_ffZ ℓ ψ u)
      = (∫ u : ℝ³, ffz_ffZ2 ℓ ψ u) - (∫ u : ℝ³, ffz_ffZ3 ℓ ψ u) := by
    rw [show (∫ u : ℝ³, ffz_ffZ ℓ ψ u) = ∫ u : ℝ³, (ffz_ffZ2 ℓ ψ u - ffz_ffZ3 ℓ ψ u)
        from integral_congr_ae (Eventually.of_forall hZspl)]
    exact integral_sub hIntZ2 hIntZ3
  have h5 : (∫ u : ℝ³, ffz_ffZ2 ℓ ψ u) = - dSpace ψ := by
    have hswap : ∀ k : Fin 3, (∫ u : ℝ³, ∫ x : ℝ³, ffz_ffJ2 k ℓ ψ x u)
        = ∫ x : ℝ³, ∫ u : ℝ³, ffz_ffJ2 k ℓ ψ x u := by
      intro k
      exact (MeasureTheory.integral_integral_swap
        (f := fun (x : ℝ³) (u : ℝ³) => ffz_ffJ2 k ℓ ψ x u)
        (integrable_bsJoint_J2 hℓ hψ hcs k)).symm
    have hinner : ∀ k : Fin 3, ∀ x : ℝ³, (∫ u : ℝ³, ffz_ffJ2 k ℓ ψ x u)
        = ψ x * (fderiv ℝ (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) x
            (kcStdBasis k)) := by
      intro k x
      simp only [ffz_ffJ2]
      rw [show (fun u : ℝ³ => (bsWin ℓ u x) ^ 2 * ψ x *
            (fderiv ℝ (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) x (kcStdBasis k)))
          = (fun u : ℝ³ => ((bsWin ℓ u x) ^ 2) *
            (ψ x * (fderiv ℝ (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) x
              (kcStdBasis k)))) from by funext u; ring]
      rw [integral_mul_const, ffz_integral_bsWin_sq hℓ x, one_mul]
    calc (∫ u : ℝ³, ffz_ffZ2 ℓ ψ u)
        = ∫ u : ℝ³, ∑ k : Fin 3, ∫ x : ℝ³, ffz_ffJ2 k ℓ ψ x u :=
          integral_congr_ae (Eventually.of_forall hperZ2)
      _ = ∑ k : Fin 3, ∫ u : ℝ³, ∫ x : ℝ³, ffz_ffJ2 k ℓ ψ x u := by
          rw [integral_finsetSum Finset.univ
            (f := fun (k : Fin 3) (u : ℝ³) => ∫ x : ℝ³, ffz_ffJ2 k ℓ ψ x u)
            (fun k _ => (integrable_bsJoint_J2 hℓ hψ hcs k).integral_prod_right)]
      _ = ∑ k : Fin 3, ∫ x : ℝ³, ∫ u : ℝ³, ffz_ffJ2 k ℓ ψ x u :=
          Finset.sum_congr rfl (fun k _ => hswap k)
      _ = ∑ k : Fin 3, ∫ x : ℝ³, ψ x *
            (fderiv ℝ (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) x (kcStdBasis k)) := by
          apply Finset.sum_congr rfl
          intro k _
          apply integral_congr_ae
          filter_upwards with x
          exact hinner k x
      _ = - dSpace ψ := sum_integral_mul_fderiv_fderiv hψ hcs
  have h6 : (∫ u : ℝ³, ffz_ffZ3 ℓ ψ u)
      = ∑ k : Fin 3, ∫ u : ℝ³, bsMean ℓ u ψ *
          ∫ x : ℝ³, (bsWin ℓ u x) ^ 2 *
            (fderiv ℝ (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) x (kcStdBasis k)) := by
    calc (∫ u : ℝ³, ffz_ffZ3 ℓ ψ u)
        = ∫ u : ℝ³, ∑ k : Fin 3, ∫ x : ℝ³, ffz_ffJ3 k ℓ ψ x u :=
          integral_congr_ae (Eventually.of_forall hperZ3)
      _ = ∑ k : Fin 3, ∫ u : ℝ³, ∫ x : ℝ³, ffz_ffJ3 k ℓ ψ x u := by
          rw [integral_finsetSum Finset.univ
            (f := fun (k : Fin 3) (u : ℝ³) => ∫ x : ℝ³, ffz_ffJ3 k ℓ ψ x u)
            (fun k _ => (integrable_bsJoint_J3 hℓ hψ hcs k).integral_prod_right)]
      _ = ∑ k : Fin 3, ∫ u : ℝ³, bsMean ℓ u ψ *
            ∫ x : ℝ³, (bsWin ℓ u x) ^ 2 *
              (fderiv ℝ (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) x (kcStdBasis k)) := by
          apply Finset.sum_congr rfl
          intro k _
          apply integral_congr_ae
          filter_upwards with u
          simp only [ffz_ffJ3]
          rw [show (fun x : ℝ³ => bsMean ℓ u ψ * (bsWin ℓ u x) ^ 2 *
                (fderiv ℝ (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) x (kcStdBasis k)))
              = (fun x : ℝ³ => bsMean ℓ u ψ * ((bsWin ℓ u x) ^ 2 *
                (fderiv ℝ (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) x (kcStdBasis k)))) from by
              funext x; ring]
          rw [integral_const_mul]
  rw [h1]
  rw [show (∫ u : ℝ³, ffz_ffA ℓ ψ u) = ∫ u : ℝ³, (ffz_ffP ℓ ψ u - ffz_ffZ ℓ ψ u) from
    integral_congr_ae (Eventually.of_forall h2)]
  rw [integral_sub hIntP hIntZ, h4, h5, h6, h3]
  simp only [ffz_ffJ1]
  ring

end Work.BSKinetic
