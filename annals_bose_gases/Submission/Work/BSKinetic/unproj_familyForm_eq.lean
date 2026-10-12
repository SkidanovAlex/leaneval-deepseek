import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BSKinetic.integrable_uncurry_bsWin_deriv_sq
import Submission.Work.BSKinetic.integral_bsWin_deriv_sq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BSKinetic.unproj_familyForm_eq`

The **unprojected** one-body moving-box family form of FS's `lem:LocKinEn` telescopes exactly to
the full-space Dirichlet word plus the window excess:

    `∫_u ⟨ψ, χ_u (√−Δ)² χ_u ψ⟩ du
       = ∫_{ℝ³} Σ_k (∂_k ψ)² + ((Σ_k ∫_z (∂_k χ_ℓ)(z)²) / ℓ³) · ∫_{ℝ³} ψ²`.

Here `χ_u(x) = bsWin ℓ u x = chiScale ℓ (x − ℓ•u)` is the big-box window family (an exact `L²`
partition, `∫_u χ_u(x)² du = 1`), and the one-body family form is written in the corpus's
`p`-convention Fourier form (`bsFamilyFormUnproj`, whose integrand `F = (·)²` is the Dirichlet
symbol).  This is the unprojected counterpart of `Work.UBBInputs9.B.integral_dirichlet_chiBig_eq`
(which integrates `x` only over the analysis box `abox 1 ℓ`), and the machine-checked bookkeeping
behind FS's big-box localisation: the *projection* is what has to pay for the positive window
excess on the right.

## Proof

1. For each `u`, `bsOneBodyUnproj ℓ (·)² u ψ = ∫_x Σ_k (∂_k(χ_u·ψ))²` by the windowed
   Plancherel/`p`-convention Fourier identity
   (`Work.SmallBoxBridge.Resolve.winModeForm_sq_eq_dirichlet`);
2. Fubini over `(x,u)` — the joint integrand is compactly supported, since `ψ` is
   (`Work.BSKinetic.integrable_uncurry_bsWin_deriv_sq`);
3. for each fixed `x`, the `u`-integral is the exact partition telescoping
   (`Work.BSKinetic.integral_bsWin_deriv_sq`): `∫_u χ_u(x)² = 1`,
   `∫_u χ_u(x)(∂_kχ_u)(x) = 0` (oddness) and `∫_u (∂_kχ_u)(x)² = (∫_z (∂_kχ_ℓ)²)/ℓ³`;
4. integrate in `x` and exchange the finite sums.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BSKinetic

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
open Submission.BoseGases

set_option maxHeartbeats 2000000

lemma bsOneBodyUnproj_sq {ℓ : ℝ} (hℓ : 0 < ℓ) (ψ : ℝ³ → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) (u : ℝ³) :
    bsOneBodyUnproj ℓ (fun r => r ^ 2) u ψ
      = ∫ x : ℝ³, ∑ k : Fin 3,
          (fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * ψ y) x (kcStdBasis k)) ^ 2 := by
  rw [show bsOneBodyUnproj ℓ (fun r => r ^ 2) u ψ
      = Submission.BoseGases.winModeForm (bsWin ℓ u) (fun r => r ^ 2) ψ from rfl]
  refine Work.SmallBoxBridge.Resolve.winModeForm_sq_eq_dirichlet (bsWin ℓ u) ψ ?_ ?_ hcs
  · have h : ContDiff ℝ ∞ (fun y : ℝ³ => y - ℓ • u) := by fun_prop
    exact (chiScale_contDiff (ne_of_gt hℓ)).comp h
  · simpa using hψ

lemma fderiv_bsWin_mul {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ³ → ℝ} (u x : ℝ³) (k : Fin 3)
    (hψd : DifferentiableAt ℝ ψ x) :
    fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * ψ y) x (kcStdBasis k)
      = bsWin ℓ u x * fderiv ℝ ψ x (kcStdBasis k)
        + ψ x * fderiv ℝ (chiScale ℓ) (x - ℓ • u) (kcStdBasis k) := by
  have hχd : Differentiable ℝ (chiScale ℓ) :=
    (chiScale_contDiff (ne_of_gt hℓ)).differentiable (by norm_num)
  have hkey : fderiv ℝ (fun y : ℝ³ => chiScale ℓ (y - ℓ • u)) x (kcStdBasis k)
      = fderiv ℝ (chiScale ℓ) (x - ℓ • u) (kcStdBasis k) := by
    have h1 : DifferentiableAt ℝ (fun y : ℝ³ => y - ℓ • u) x :=
      ((hasFDerivAt_id x).sub_const (ℓ • u)).differentiableAt
    have h3 : fderiv ℝ (fun y : ℝ³ => y - ℓ • u) x = ContinuousLinearMap.id ℝ ℝ³ :=
      ((hasFDerivAt_id x).sub_const (ℓ • u)).fderiv
    have h2 : fderiv ℝ (fun y : ℝ³ => chiScale ℓ (y - ℓ • u)) x
        = (fderiv ℝ (chiScale ℓ) (x - ℓ • u)).comp
            (fderiv ℝ (fun y : ℝ³ => y - ℓ • u) x) :=
      fderiv_comp (x := x) (f := fun y : ℝ³ => y - ℓ • u) (g := chiScale ℓ)
        (hχd (x - ℓ • u)) h1
    rw [h2, h3, ContinuousLinearMap.comp_id]
  have hχud : DifferentiableAt ℝ (fun y : ℝ³ => chiScale ℓ (y - ℓ • u)) x :=
    ((chiScale_contDiff (ne_of_gt hℓ)).comp
      (by fun_prop : ContDiff ℝ ∞ (fun y : ℝ³ => y - ℓ • u)))
      |>.differentiable (by norm_num) x
  have hfun : (fun y : ℝ³ => bsWin ℓ u y * ψ y)
      = (fun y : ℝ³ => chiScale ℓ (y - ℓ • u)) * ψ := rfl
  rw [hfun, fderiv_mul hχud hψd, add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul]
  rw [hkey]
  rfl

lemma integrable_bsWin_deriv_sq_u {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (x : ℝ³) (k : Fin 3) :
    Integrable (fun u : ℝ³ =>
      (fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * ψ y) x (kcStdBasis k)) ^ 2)
      (volume : Measure ℝ³) := by
  set A : ℝ := fderiv ℝ ψ x (kcStdBasis k) with hA
  set B : ℝ := ψ x with hB
  have h1 : Integrable (fun u : ℝ³ => (chiScale ℓ (x - ℓ • u)) ^ 2) :=
    Work.UBBInputs9.B.integrable_chiScale_sub_smul_sq ℓ hℓ x
  have h2 : Integrable (fun u : ℝ³ =>
      chiScale ℓ (x - ℓ • u) * fderiv ℝ (chiScale ℓ) (x - ℓ • u) (kcStdBasis k)) :=
    Work.UBBInputs9.B.integrable_chiScale_sub_smul_mul_fderiv ℓ hℓ x (kcStdBasis k)
  have h3 : Integrable (fun u : ℝ³ =>
      (fderiv ℝ (chiScale ℓ) (x - ℓ • u) (kcStdBasis k)) ^ 2) :=
    Work.UBBInputs9.C.integrable_partialDeriv_chiScale_sub_smul ℓ hℓ x k
  have hsum : Integrable (fun u : ℝ³ => A ^ 2 * (chiScale ℓ (x - ℓ • u)) ^ 2
      + (2 * A * B) * (chiScale ℓ (x - ℓ • u) * fderiv ℝ (chiScale ℓ) (x - ℓ • u) (kcStdBasis k))
      + B ^ 2 * (fderiv ℝ (chiScale ℓ) (x - ℓ • u) (kcStdBasis k)) ^ 2) :=
    ((h1.const_mul _).add (h2.const_mul _)).add (h3.const_mul _)
  refine hsum.congr (Filter.Eventually.of_forall (fun u => ?_))
  simp only
  rw [fderiv_bsWin_mul hℓ u x k (hψ.differentiable (by norm_num) x)]
  simp only [bsWin, hA, hB]
  ring

theorem unproj_familyForm_eq {ℓ : ℝ} (hℓ : 0 < ℓ) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    Work.BSKinetic.bsFamilyFormUnproj ℓ (fun r => r ^ 2) ψ
      = Work.BSKinetic.dSpace ψ
        + ((∑ k : Fin 3,
              ∫ z : EuclideanSpace ℝ (Fin 3),
                (fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
                  (Submission.BoseGases.kcStdBasis k)) ^ 2) / ℓ ^ 3)
          * (∫ z : EuclideanSpace ℝ (Fin 3), (ψ z) ^ 2) := by
  have stepI : bsFamilyFormUnproj ℓ (fun r => r ^ 2) ψ
      = ∫ u : ℝ³, ∫ x : ℝ³, ∑ k : Fin 3,
          (fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * ψ y) x (kcStdBasis k)) ^ 2 := by
    rw [bsFamilyFormUnproj]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun u => bsOneBodyUnproj_sq hℓ ψ hψ hcs u)
  have hInt : Integrable
      (Function.uncurry (fun (x u : ℝ³) => ∑ k : Fin 3,
        (fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * ψ y) x (kcStdBasis k)) ^ 2))
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := by
    have hfun : Function.uncurry (fun (x u : ℝ³) => ∑ k : Fin 3,
        (fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * ψ y) x (kcStdBasis k)) ^ 2)
        = fun p : ℝ³ × ℝ³ => ∑ k : Fin 3,
        (fderiv ℝ (fun y : ℝ³ => bsWin ℓ p.2 y * ψ y) p.1 (kcStdBasis k)) ^ 2 := rfl
    rw [hfun]
    exact integrable_finset_sum Finset.univ
      (f := fun (k : Fin 3) (p : ℝ³ × ℝ³) =>
        (fderiv ℝ (fun y : ℝ³ => bsWin ℓ p.2 y * ψ y) p.1 (kcStdBasis k)) ^ 2)
      (fun k _ => integrable_uncurry_bsWin_deriv_sq hℓ hψ hcs k)
  have stepII : (∫ u : ℝ³, ∫ x : ℝ³, ∑ k : Fin 3,
          (fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * ψ y) x (kcStdBasis k)) ^ 2)
      = ∫ x : ℝ³, ∫ u : ℝ³, ∑ k : Fin 3,
          (fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * ψ y) x (kcStdBasis k)) ^ 2 :=
    (MeasureTheory.integral_integral_swap (f := fun (x u : ℝ³) => ∑ k : Fin 3,
        (fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * ψ y) x (kcStdBasis k)) ^ 2) hInt).symm
  have stepIII : (∫ x : ℝ³, ∫ u : ℝ³, ∑ k : Fin 3,
          (fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * ψ y) x (kcStdBasis k)) ^ 2)
      = ∫ x : ℝ³, ∑ k : Fin 3,
          ((fderiv ℝ ψ x (kcStdBasis k)) ^ 2
            + ((∫ z : ℝ³, (fderiv ℝ (chiScale ℓ) z (kcStdBasis k)) ^ 2) / ℓ ^ 3)
              * (ψ x) ^ 2) := by
    apply integral_congr_ae
    refine Filter.Eventually.of_forall (fun x => ?_)
    simp only []
    have h := integral_finset_sum (Finset.univ)
        (f := fun (k : Fin 3) (u : ℝ³) =>
          (fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * ψ y) x (kcStdBasis k)) ^ 2)
        (fun k _ => integrable_bsWin_deriv_sq_u hℓ hψ x k)
    rw [h]
    apply Finset.sum_congr rfl
    intro k _
    exact integral_bsWin_deriv_sq hℓ ψ hψ x k
  have hWcs : HasCompactSupport (fun x : ℝ³ => (ψ x) ^ 2) :=
    hcs.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  have hW : Integrable (fun x : ℝ³ => (ψ x) ^ 2) (volume : Measure ℝ³) :=
    (hψ.continuous.pow 2).integrable_of_hasCompactSupport hWcs
  have hAcon : ∀ k : Fin 3, Continuous (fun x : ℝ³ => fderiv ℝ ψ x (kcStdBasis k)) :=
    fun k => (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hAcs : ∀ k : Fin 3, HasCompactSupport (fun x : ℝ³ => fderiv ℝ ψ x (kcStdBasis k)) :=
    fun k => hcs.fderiv_apply ℝ (kcStdBasis k)
  have hAkcs : ∀ k : Fin 3,
      HasCompactSupport (fun x : ℝ³ => (fderiv ℝ ψ x (kcStdBasis k)) ^ 2) :=
    fun k => (hAcs k).comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  have hAk : ∀ k : Fin 3, Integrable (fun x : ℝ³ => (fderiv ℝ ψ x (kcStdBasis k)) ^ 2) :=
    fun k => ((hAcon k).pow 2).integrable_of_hasCompactSupport (hAkcs k)
  have stepIV : (∫ x : ℝ³, ∑ k : Fin 3,
          ((fderiv ℝ ψ x (kcStdBasis k)) ^ 2
            + ((∫ z : ℝ³, (fderiv ℝ (chiScale ℓ) z (kcStdBasis k)) ^ 2) / ℓ ^ 3)
              * (ψ x) ^ 2))
      = dSpace ψ
        + ((∑ k : Fin 3, ∫ z : ℝ³,
              (fderiv ℝ (chiScale ℓ) z (kcStdBasis k)) ^ 2) / ℓ ^ 3)
          * (∫ z : ℝ³, (ψ z) ^ 2) := by
    calc (∫ x : ℝ³, ∑ k : Fin 3,
            ((fderiv ℝ ψ x (kcStdBasis k)) ^ 2
              + ((∫ z : ℝ³, (fderiv ℝ (chiScale ℓ) z (kcStdBasis k)) ^ 2) / ℓ ^ 3)
                * (ψ x) ^ 2))
        = ∑ k : Fin 3, ∫ x : ℝ³,
            ((fderiv ℝ ψ x (kcStdBasis k)) ^ 2
              + ((∫ z : ℝ³, (fderiv ℝ (chiScale ℓ) z (kcStdBasis k)) ^ 2) / ℓ ^ 3)
                * (ψ x) ^ 2) :=
          integral_finset_sum Finset.univ (fun k _ => (hAk k).add (hW.const_mul _))
      _ = ∑ k : Fin 3, ((∫ x : ℝ³, (fderiv ℝ ψ x (kcStdBasis k)) ^ 2)
            + ((∫ z : ℝ³, (fderiv ℝ (chiScale ℓ) z (kcStdBasis k)) ^ 2) / ℓ ^ 3)
              * (∫ x : ℝ³, (ψ x) ^ 2)) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [integral_add (hAk k) (hW.const_mul _), integral_const_mul]
      _ = (∑ k : Fin 3, ∫ x : ℝ³, (fderiv ℝ ψ x (kcStdBasis k)) ^ 2)
            + (∑ k : Fin 3,
                ((∫ z : ℝ³, (fderiv ℝ (chiScale ℓ) z (kcStdBasis k)) ^ 2) / ℓ ^ 3))
              * (∫ x : ℝ³, (ψ x) ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.sum_mul]
      _ = dSpace ψ
            + ((∑ k : Fin 3, ∫ z : ℝ³,
                (fderiv ℝ (chiScale ℓ) z (kcStdBasis k)) ^ 2) / ℓ ^ 3)
              * (∫ z : ℝ³, (ψ z) ^ 2) := by
          rw [show (∑ k : Fin 3,
                ((∫ z : ℝ³, (fderiv ℝ (chiScale ℓ) z (kcStdBasis k)) ^ 2) / ℓ ^ 3))
              = (∑ k : Fin 3,
                ∫ z : ℝ³, (fderiv ℝ (chiScale ℓ) z (kcStdBasis k)) ^ 2) / ℓ ^ 3
              from (Finset.sum_div _ _ _).symm]
          simp only [dSpace]
  rw [stepI, stepII, stepIII, stepIV]

end Work.BSKinetic
