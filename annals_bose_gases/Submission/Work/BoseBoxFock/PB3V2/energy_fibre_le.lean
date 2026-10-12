import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PB3V2.energyKinPlancherelOnBox
import Submission.Work.BoseBoxFock.PB3V2.windowMulPointwiseBound
import Submission.Work.BoseBoxFock.chiMf_contDiff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PB3V2.energy_fibre_le`

The kinetic energy of the windowed mean-free *fibre* of a smooth `n`-body state is bounded by the
windowed Dirichlet energy of the state plus the "window mass" row.

For `Ψ : Xn n → ℂ` of class `C^∞`, a slot `i : Fin n` and a frozen configuration `x'` of the
remaining `n − 1` slots, put

    φ := sect i x' Ψ            (the slot-`i` fibre of `Ψ`),
    g := (χ_ℓ : ℂ) · mf ℓ φ    (the windowed mean-free part of the fibre),

where `mf ℓ φ = φ − (ℓ³)⁻¹∫_{boxL ℓ} φ` and `χ_ℓ = chiScale ℓ`.  The theorem states

    (2π)⁻³ ∫_p ‖p‖²‖kinFT g p‖²
      ≤ 6 D² ∫_{boxL ℓ} ‖mf ℓ φ‖²
        + 2 ∫_{boxL ℓ} χ_ℓ² Σ_m ‖∂_{i,m}Ψ(insertCoord i w x')‖² ,

i.e. the momentum second moment of `g` is dominated by `D²`-times the box mass of the fibre plus
the *windowed slot-`i` Dirichlet energy of the state itself*, `D` being a bound on the gradient of
the window (`hD`).

## Proof (three steps)

1. **Derivative Plancherel** (`PB3V2.energyKinPlancherelOnBox`, delegated): since `tsupport g ⊆
   boxL ℓ` and `g` is `C¹`, the momentum second moment of `g` equals the Dirichlet energy
   `∫_{boxL ℓ} Σ_j ‖∂_j g‖²` (derivative Plancherel on the box).

2. **Product rule** (`PB3V2.windowMulPointwiseBound`, delegated): on the box,
   `Σ_j ‖∂_j(χ_ℓ·f)‖² ≤ 2χ_ℓ²Σ_j‖∂_jf‖² + 6D²‖f‖²` for `f = mf ℓ φ`.  Integrating and splitting
   gives `2∫_{boxL ℓ}χ_ℓ²Σ_j‖∂_j(mf ℓ φ)‖² + 6D²∫_{boxL ℓ}‖mf ℓ φ‖²`.

3. **The fibre dictionary** (both one-line calculus facts proved below): `∂_j (mf ℓ φ) = ∂_j φ`
   (the subtracted box mean is a constant) and `∂_j (sect i x' Ψ)(w) = ∂_{i,j}Ψ(insertCoord i w x')`
   (chain rule for the affine insertion `z ↦ insertCoord i z x'`), which turns the first piece of
   step 2 into the "state derivative" term of the statement.

All integrability inputs come from continuity on the compact box `boxL ℓ`.
-/

namespace Work.BoseBoxFock.PB3V2

noncomputable section

open MeasureTheory
open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

set_option maxHeartbeats 800000

/-- The mean-free part `mf ℓ h = h − const` has the same derivative as `h`. -/
private lemma fderiv_mf_apply {ℓ : ℝ} (h : E3 → ℂ) (w v : E3) :
    fderiv ℝ (Work.BoseBoxFock.mf ℓ h) w v = fderiv ℝ h w v := by
  have hc : Work.BoseBoxFock.mf ℓ h
      = fun x => h x - (((ℓ ^ 3)⁻¹ : ℝ) : ℂ) * (∫ y in boxL ℓ, h y) := rfl
  rw [hc, fderiv_sub_const]

/-- **Chain rule for the slot-`j` fibre**: the derivative of `z ↦ Ψ (insertCoord j z x')` at `z`
in the direction `kcStdBasis k` is the slot-`j`, coordinate-`k` derivative of `Ψ` at the inserted
configuration. -/
private lemma fderiv_sect_apply {n : ℕ} {Ψ : Xn n → ℂ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (j : Fin n) (x' : {k : Fin n // k ≠ j} → E3) (w : E3) (k : Fin 3) :
    fderiv ℝ (Work.BoseBoxFock.sect j x' Ψ) w (Submission.BoseGases.kcStdBasis k)
      = fderiv ℝ Ψ (Work.BoseBoxFock.insertCoord j w x') (Work.BoseBoxFock.slotDirVec j k) := by
  show fderiv ℝ (fun z : E3 => Ψ (Work.BoseBoxFock.insertCoord j z x')) w
      (Submission.BoseGases.kcStdBasis k) = _
  have heq : (fun z : E3 => Work.BoseBoxFock.insertCoord j z x')
      = (fun z : E3 => Function.update (Work.BoseBoxFock.insertCoord j 0 x') j z) := by
    funext z k
    by_cases hk : k = j <;> simp [Work.BoseBoxFock.insertCoord, hk]
  have hder : HasFDerivAt (fun z : E3 => Work.BoseBoxFock.insertCoord j z x')
      (ContinuousLinearMap.pi (Pi.single j (ContinuousLinearMap.id ℝ E3))) w := by
    rw [heq]
    exact hasFDerivAt_update (Work.BoseBoxFock.insertCoord j 0 x') w
  have hdΨ : HasFDerivAt Ψ (fderiv ℝ Ψ (Work.BoseBoxFock.insertCoord j w x'))
      (Work.BoseBoxFock.insertCoord j w x') :=
    ((hΨ.differentiable (by simp)) (Work.BoseBoxFock.insertCoord j w x')).hasFDerivAt
  have hfun : (fun z : E3 => Ψ (Work.BoseBoxFock.insertCoord j z x'))
      = Ψ ∘ (fun z : E3 => Work.BoseBoxFock.insertCoord j z x') := rfl
  rw [hfun, (hdΨ.comp w hder).fderiv, ContinuousLinearMap.comp_apply]
  congr 1
  funext k
  by_cases hk : k = j
  · subst hk
    simp [ContinuousLinearMap.pi_apply, Pi.single_eq_same, Work.BoseBoxFock.slotDirVec,
      Submission.BoseGases.kcStdBasis, Function.update_self]
  · simp [ContinuousLinearMap.pi_apply, Pi.single_eq_of_ne hk, Work.BoseBoxFock.slotDirVec,
      Submission.BoseGases.kcStdBasis, Function.update_of_ne hk]

theorem energy_fibre_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n)
    {Ψ : Work.BoseDict.Xn n → ℂ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ x v : EuclideanSpace ℝ (Fin 3),
        |fderiv ℝ (Submission.BoseGases.chiScale ℓ) x v| ≤ D * ‖v‖)
    (x' : {k : Fin n // k ≠ i} → EuclideanSpace ℝ (Fin 3)) :
    ((2 * Real.pi) ^ 3)⁻¹ *
        ∫ p : EuclideanSpace ℝ (Fin 3), ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT
          (fun w : EuclideanSpace ℝ (Fin 3) =>
            ((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)
              * Work.BoseBoxFock.mf ℓ (Work.BoseBoxFock.sect i x' Ψ) w) p‖ ^ 2
      ≤ 6 * D ^ 2 * (∫ w in Work.BoseK15.corpusBox.boxL ℓ,
            ‖Work.BoseBoxFock.mf ℓ (Work.BoseBoxFock.sect i x' Ψ) w‖ ^ 2)
        + 2 * ∫ w in Work.BoseK15.corpusBox.boxL ℓ,
            (Submission.BoseGases.chiScale ℓ w) ^ 2 *
              ∑ m : Fin 3, ‖fderiv ℝ Ψ (Work.BoseBoxFock.insertCoord i w x')
                (Work.BoseBoxFock.slotDirVec i m)‖ ^ 2 := by
  classical
  set φ : E3 → ℂ := Work.BoseBoxFock.sect i x' Ψ with hφdef
  set g : E3 → ℂ := fun z => ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ)
      * Work.BoseBoxFock.mf ℓ φ z with hgdef
  set Ef : E3 → ℝ := fun z => ∑ m : Fin 3,
      ‖fderiv ℝ Ψ (Work.BoseBoxFock.insertCoord i z x') (Work.BoseBoxFock.slotDirVec i m)‖ ^ 2
    with hEfdef
  -- 1. smoothness of the fibre and of the windowed fibre
  have hins : ContDiff ℝ 1 (fun z : E3 => Work.BoseBoxFock.insertCoord i z x') := by
    have heq : (fun z : E3 => Work.BoseBoxFock.insertCoord i z x')
        = (fun z : E3 => Function.update (Work.BoseBoxFock.insertCoord i 0 x') i z) := by
      funext z k
      by_cases hk : k = i <;> simp [Work.BoseBoxFock.insertCoord, hk]
    rw [heq]
    exact contDiff_update (1 : WithTop ℕ∞) (Work.BoseBoxFock.insertCoord i 0 x') i
  have hsect : ContDiff ℝ 1 φ := by
    rw [hφdef]
    exact (hΨ.of_le (by simp)).comp hins
  have hg1 : ContDiff ℝ 1 g := by
    rw [hgdef]
    exact Work.BoseBoxFock.chiMf_contDiff hℓ hsect
  have hgts : tsupport g ⊆ boxL ℓ := by
    rw [hgdef]
    exact Work.BoseBoxFock.chiMf_tsupport_subset hℓ φ
  -- 2. derivative Plancherel: the momentum second moment is the Dirichlet energy on the box
  have hplan := energyKinPlancherelOnBox hℓ hg1 hgts
  -- 3. the pointwise product-rule bound
  have hmfdiff : Differentiable ℝ (Work.BoseBoxFock.mf ℓ φ) := by
    have hφd : Differentiable ℝ φ := hsect.differentiable (by norm_num)
    have hc : Work.BoseBoxFock.mf ℓ φ
        = fun x => φ x - (((ℓ ^ 3)⁻¹ : ℝ) : ℂ) * (∫ y in boxL ℓ, φ y) := rfl
    rw [hc]
    exact hφd.sub_const _
  have hpw : ∀ z : E3, (∑ j : Fin 3, ‖fderiv ℝ g z (Submission.BoseGases.kcStdBasis j)‖ ^ 2)
      ≤ 2 * ((Submission.BoseGases.chiScale ℓ z) ^ 2 * Ef z)
        + 6 * D ^ 2 * ‖Work.BoseBoxFock.mf ℓ φ z‖ ^ 2 := by
    intro z
    have h1 := windowMulPointwiseBound (ℓ := ℓ) (D := D) hD (f := Work.BoseBoxFock.mf ℓ φ)
      hmfdiff z
    have hmid : (∑ j : Fin 3, ‖fderiv ℝ (Work.BoseBoxFock.mf ℓ φ) z
        (Submission.BoseGases.kcStdBasis j)‖ ^ 2) = Ef z := by
      rw [hEfdef]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [fderiv_mf_apply, fderiv_sect_apply hΨ i x' z j]
    rw [hmid] at h1
    rw [hgdef]
    refine le_trans h1 (le_of_eq ?_)
    ring
  -- 4. integrability on the box (everything is continuous, the box is compact)
  have hcont_g : ∀ j : Fin 3,
      Continuous (fun z : E3 => fderiv ℝ g z (Submission.BoseGases.kcStdBasis j)) :=
    fun j => (hg1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcontFA : Continuous (fun z : E3 =>
      ∑ j : Fin 3, ‖fderiv ℝ g z (Submission.BoseGases.kcStdBasis j)‖ ^ 2) :=
    continuous_finsetSum _ (fun j _ => (hcont_g j).norm.pow 2)
  have hcontEf : Continuous Ef := by
    rw [hEfdef]
    refine continuous_finsetSum _ (fun j _ => ?_)
    exact ((((hΨ.continuous_fderiv (by simp)).comp hins.continuous).clm_apply
      continuous_const).norm.pow 2)
  have hcont_mf : Continuous (Work.BoseBoxFock.mf ℓ φ) := by
    have hc : Work.BoseBoxFock.mf ℓ φ
        = fun x => φ x - (((ℓ ^ 3)⁻¹ : ℝ) : ℂ) * (∫ y in boxL ℓ, φ y) := rfl
    rw [hc]
    exact hsect.continuous.sub continuous_const
  have hcontFR : Continuous (fun z : E3 => 2 * ((Submission.BoseGases.chiScale ℓ z) ^ 2 * Ef z)
      + 6 * D ^ 2 * ‖Work.BoseBoxFock.mf ℓ φ z‖ ^ 2) := by
    have hchi : Continuous (Submission.BoseGases.chiScale ℓ) :=
      (Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).continuous
    exact (continuous_const.mul ((hchi.pow 2).mul hcontEf)).add
      (continuous_const.mul (hcont_mf.norm.pow 2))
  have hIntFA : IntegrableOn (fun z : E3 =>
      ∑ j : Fin 3, ‖fderiv ℝ g z (Submission.BoseGases.kcStdBasis j)‖ ^ 2) (boxL ℓ) volume :=
    hcontFA.continuousOn.integrableOn_compact (Work.BoseBoxFock.isCompact_boxL hℓ)
  have hIntFR : IntegrableOn (fun z : E3 =>
      2 * ((Submission.BoseGases.chiScale ℓ z) ^ 2 * Ef z)
        + 6 * D ^ 2 * ‖Work.BoseBoxFock.mf ℓ φ z‖ ^ 2) (boxL ℓ) volume :=
    hcontFR.continuousOn.integrableOn_compact (Work.BoseBoxFock.isCompact_boxL hℓ)
  -- 5. monotonicity of the integral
  have hmono := setIntegral_mono hIntFA hIntFR hpw
  -- 6. splitting the right-hand side
  have hInt1 : Integrable (fun z : E3 =>
      2 * ((Submission.BoseGases.chiScale ℓ z) ^ 2 * Ef z)) (volume.restrict (boxL ℓ)) :=
    ((continuous_const.mul
      (((Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).continuous.pow 2).mul
        hcontEf)).continuousOn.integrableOn_compact (Work.BoseBoxFock.isCompact_boxL hℓ))
  have hInt2 : Integrable (fun z : E3 =>
      6 * D ^ 2 * ‖Work.BoseBoxFock.mf ℓ φ z‖ ^ 2) (volume.restrict (boxL ℓ)) :=
    ((continuous_const.mul (hcont_mf.norm.pow 2)).continuousOn.integrableOn_compact
      (Work.BoseBoxFock.isCompact_boxL hℓ))
  have hsplit : (∫ z in boxL ℓ, (2 * ((Submission.BoseGases.chiScale ℓ z) ^ 2 * Ef z)
        + 6 * D ^ 2 * ‖Work.BoseBoxFock.mf ℓ φ z‖ ^ 2))
      = 2 * (∫ z in boxL ℓ, (Submission.BoseGases.chiScale ℓ z) ^ 2 * Ef z)
        + 6 * D ^ 2 * (∫ z in boxL ℓ, ‖Work.BoseBoxFock.mf ℓ φ z‖ ^ 2) := by
    rw [MeasureTheory.integral_add hInt1 hInt2, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
  rw [hplan]
  refine le_trans hmono ?_
  rw [hsplit]
  linarith

end

end Work.BoseBoxFock.PB3V2
