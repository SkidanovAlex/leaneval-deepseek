import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.L3Aux.HkIntegrand_sep_le
import Submission.Work.FTS.StrongPersist.L3Aux.GamJetBounds
import Submission.Work.FTS.StrongPersist.L6Aux.ZslotSupBound6
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.NfkDefs
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.Basic
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.AngProfAll
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.HKerRadialMul
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.contHkAngRad
import Submission.Work.FTS.NonlinRows.AngRad.HkMem_ang_rad_le
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.StrongLWP.Basic
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row21

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L3Rhs.NfkAux

open Work.FTS.Galerkin (Fn)
open MeasureTheory

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# The block `N₄^{g*} + N₅^{g*}` of the level-three right-hand side

`N₄^{g*}` (row 21) and `N₅^{g*}` (row 25a) are the two rows of the nonlinear right-hand side in
which the angular moment `FK f` of the perturbation `f` multiplies the *star* profile `F_*`.
Since `F_* α z θ = α (Γ(θ)/c α)·2 hKer z` with `hKer z = z/(1+z)²`, their sum factors as

  `N₄^{g*} α f z θ + N₅^{g*} α f z θ = aProf α θ · rProf f z`

(`N4gs_add_N5gs_factor`), with the *single* angular profile `aProf` and the *single* radial
factor `r f z = FK f z · hKer z`.  Everything therefore reduces to the `θ`/`z`-separation
estimate for an angular `×` radial product:

* the angular profile `aProf` and its `D_θ`-iterates up to order `4` are `O(α)` with an explicit
  majorant whose square times `sin(2θ)^{-γ}` is integrable with an `O(1/α)` bound (`AngProfAll`);
* the radial factor `r = FK f · hKer` is honest in `ℋ⁴` with an `α`-independent bound by the
  `ℋ⁴`-norm of `FK f` (`HKerRadialMul`), because `hKer` is a fixed bounded `C^∞` radial
  multiplier (`ZslotSupBound6`);
* `Xₙ α (aProf · r) ≤ K · Xₙ α r` (`XN_ang_rad_le_gen`, via `AngProfAll`);
* the descent from level `4` to level `3` uses the pointwise monotonicity of the integrand plus
  the open-quadrant continuity of the level-`3` integrand (`contHkAngRad`).

The `C^{m}`-smoothness (`m ≤ 5`) of `z ↦ FK f z` on `(0,∞)` needed for the Leibniz rules is
`contDiffOn_FK` of `NfkAux.Basic` (`SmoothOpen f` + `HkMem α 6 f`, i.e. the `HQo α 6` field of
`H6Adm`).
-/

/-! ## The factorisation of the block -/

/-- **`N₄^{g*} + N₅^{g*}` is a product of an angular profile and a radial function.**

`∂_θF_* = (α/c)·F_*'(z)·Γ'(θ)` with `F_*'(z) = 2 hKer z` (so that `FK f · ∂_θF_*` carries the
radial factor `FK f · hKer`), and `F_* = α(Γ/c)·2 hKer`; with `D_θΓ = sin(2θ)·Γ'` this gives

`N₄^{g*} = -(α/c)·D_θΓ(θ) · (FK f z · hKer z)`,
`N₅^{g*} = -(2α/c)·sin²θ·Γ(θ) · (FK f z · hKer z)`,

whence the sum.  The identity is unconditional (no regularity hypothesis is used). -/
theorem N4gs_add_N5gs_factor (α : ℝ) (g : Fn) :
    (fun z θ => Work.FTS.Nonlin.N4gs α g z θ + Work.FTS.Nonlin.N5gs α g z θ)
      = fun z θ => aProf α θ * rProf g z := by
  funext z θ
  have hF : Work.FM.Fstar z = 2 * Work.Spaces.hKer z := by
    rw [Work.FM.Fstar, Work.Spaces.hKer_apply]; ring
  rw [Work.FTS.Nonlinear.Pieces.RNP.N4gs_factor]
  simp only [Work.FTS.Nonlin.N5gs, Work.FTS.StrongPersist.L3Rhs.NfkAux.aProf,
    Work.FTS.StrongPersist.L3Rhs.NfkAux.rProf, Work.Construction.Fstar, hF]
  ring

/-! ## The target -/

theorem NfkFstarBlock : ∃ C Cpow : ℝ, 0 < C ∧ 0 ≤ Cpow ∧
    ∀ (α : ℝ) (f : Work.FTS.Galerkin.Fn) (MK : ℝ),
      0 < α → α ≤ 1 →
      Work.FTS.StrongPersist.H6Adm α f →
      Work.Spaces.HkMem α 4 (fun z _ => Work.Construction.FK f z) →
      Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK f z) ≤ MK →
      Work.Spaces.HkMem α 3
          (fun z θ => Work.FTS.Nonlin.N4gs α f z θ + Work.FTS.Nonlin.N5gs α f z θ) ∧
      Work.Spaces.HkSq α 3
          (fun z θ => Work.FTS.Nonlin.N4gs α f z θ + Work.FTS.Nonlin.N5gs α f z θ)
        ≤ C * α ^ (-Cpow) * (1 + MK) ^ 2 := by
  obtain ⟨K₀, K₁, K₂, KA, hK₀, hK₁, hK₂, hKA, hang⟩ := AngProfAll
  obtain ⟨KR, hKR, hrad⟩ := HKerRadialMul
  refine ⟨(KA * (Real.sqrt KR + 1)) ^ 2 + 1, 0, by positivity, le_refl 0, ?_⟩
  intro α f MK hα hα1 hadm hmemFK hXnFK
  -- ### the smoothness of the datum, and of the angular moment `FK f`
  have hsmO : Work.FTS.EllipticEst.SmoothOpen f := hadm.reg.1
  have hmem6 : Work.Spaces.HkMem α 6 f := hadm.reg.2
  have hFK4 : ContDiffOn ℝ 4 (fun z => Work.Construction.FK f z) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.StrongPersist.L3Rhs.NfkAux.contDiffOn_FK hα hα1 hsmO hmem6 4 (by norm_num)
  -- ### the two separation children
  obtain ⟨hcontR, hmemr, hSqr⟩ := hrad α hα hα1 (fun z => Work.Construction.FK f z) hFK4 hmemFK
  obtain ⟨hcontA, ha0, ha1, hGnn, hGint, _hMint, hXnSep⟩ := hang α hα hα1
  -- ### level-four membership of `aProf · rProf`
  have hmem4 : Work.Spaces.HkMem α 4 (fun z θ => aProf α θ * rProf f z) :=
    Work.FTS.NonlinRows.AngRad.HkMem_ang_rad_le (α := α) (a := aProf α) (r := rProf f)
      (B0 := K₀ * α) (B1 := K₁ * α) (G := Gprof α)
      (by positivity) (by positivity) hGnn ha0 ha1 hGint
      Work.FTS.NonlinRows.AuxAngRad.integrableOn_smE hmemr hcontA hcontR
  -- ### level-three membership of `aProf · rProf`
  have hcont3 : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 3 (fun z θ => aProf α θ * rProf f z) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    contHkAngRad 3 α (aProf α) (rProf f)
      (fun i hi => hcontA i (le_trans hi (by norm_num)))
      (fun b hb => hcontR b (le_trans hb (by norm_num)))
  have hmem3 : Work.Spaces.HkMem α 3 (fun z θ => aProf α θ * rProf f z) :=
    Work.FTS.LocData.HkMem_of_majorant α 3 (f := fun z θ => aProf α θ * rProf f z)
      (M := fun z θ => Work.Spaces.HkIntegrand α 4 (fun z θ => aProf α θ * rProf f z) z θ)
      hcont3 hmem4.1 hmem4.2
      (fun z _ θ _ => Work.FTS.StrongLWP.HkIntegrand_mono α _ (by norm_num) z θ)
  -- ### the norm bound
  have hMKnn : 0 ≤ MK := le_trans (Work.Spaces.HkNorm_nonneg α 4 _) hXnFK
  have hsqFK : Work.Spaces.HkSq α 4 (fun z _ => Work.Construction.FK f z) ≤ MK ^ 2 := by
    have hnn : 0 ≤ Work.Spaces.HkSq α 4 (fun z _ => Work.Construction.FK f z) :=
      Work.Spaces.HkSq_nonneg α 4 _
    calc Work.Spaces.HkSq α 4 (fun z _ => Work.Construction.FK f z)
        = (Real.sqrt (Work.Spaces.HkSq α 4 (fun z _ => Work.Construction.FK f z))) ^ 2 :=
          (Real.sq_sqrt hnn).symm
      _ ≤ MK ^ 2 := by
          refine pow_le_pow_left₀ (Real.sqrt_nonneg _) ?_ 2
          simpa only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm] using hXnFK
  have hXn_r : Work.FTS.Nonlin.Xn α (fun z θ => rProf f z) ≤ Real.sqrt KR * MK := by
    have h1 : Work.Spaces.HkSq α 4 (fun z _ => rProf f z)
        ≤ KR * Work.Spaces.HkSq α 4 (fun z _ => Work.Construction.FK f z) := hSqr
    have h2 : Work.FTS.Nonlin.Xn α (fun z θ => rProf f z)
        = Real.sqrt (Work.Spaces.HkSq α 4 (fun z _ => rProf f z)) := rfl
    rw [h2]
    calc Real.sqrt (Work.Spaces.HkSq α 4 (fun z _ => rProf f z))
        ≤ Real.sqrt (KR * Work.Spaces.HkSq α 4 (fun z _ => Work.Construction.FK f z)) :=
          Real.sqrt_le_sqrt h1
      _ ≤ Real.sqrt (KR * MK ^ 2) := by
          refine Real.sqrt_le_sqrt ?_
          exact mul_le_mul_of_nonneg_left hsqFK hKR.le
      _ = Real.sqrt KR * |MK| := by
          rw [Real.sqrt_mul hKR.le, Real.sqrt_sq_eq_abs]
      _ = Real.sqrt KR * MK := by rw [abs_of_nonneg hMKnn]
  have hXn_ar : Work.FTS.Nonlin.Xn α (fun z θ => aProf α θ * rProf f z)
      ≤ KA * (Real.sqrt KR * MK) := by
    have h5 := hXnSep (fun z => rProf f z) hmemr
    have h6 : KA * Work.FTS.Nonlin.Xn α (fun z θ => rProf f z)
        ≤ KA * (Real.sqrt KR * MK) :=
      mul_le_mul_of_nonneg_left hXn_r hKA.le
    linarith
  -- ### the value bound
  have hSq4ar : Work.Spaces.HkSq α 4 (fun z θ => aProf α θ * rProf f z)
      = (Work.FTS.Nonlin.Xn α (fun z θ => aProf α θ * rProf f z)) ^ 2 := by
    rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm]
    exact (Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 _)).symm
  have hSq3 : Work.Spaces.HkSq α 3 (fun z θ => aProf α θ * rProf f z)
      ≤ (KA * (Real.sqrt KR * MK)) ^ 2 := by
    refine le_trans (Work.FTS.StrongLWP.HkSq_mono_of_mem (α := α) (k := 4) (k' := 3)
      (by norm_num) hmem4) ?_
    rw [hSq4ar]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hXn_ar 2
  rw [N4gs_add_N5gs_factor α f]
  refine ⟨hmem3, ?_⟩
  have hfin : (KA * (Real.sqrt KR * MK)) ^ 2
      ≤ ((KA * (Real.sqrt KR + 1)) ^ 2 + 1) * α ^ (-(0 : ℝ)) * (1 + MK) ^ 2 := by
    rw [neg_zero, Real.rpow_zero, mul_one]
    have h1 : Real.sqrt KR * MK ≤ (Real.sqrt KR + 1) * (1 + MK) := by
      nlinarith [Real.sqrt_nonneg KR, hMKnn]
    have h2 : KA * (Real.sqrt KR * MK) ≤ KA * (Real.sqrt KR + 1) * (1 + MK) := by
      have h2' : KA * (Real.sqrt KR * MK) ≤ KA * ((Real.sqrt KR + 1) * (1 + MK)) :=
        mul_le_mul_of_nonneg_left h1 hKA.le
      linarith [h2']
    have h3 : (KA * (Real.sqrt KR * MK)) ^ 2
        ≤ (KA * (Real.sqrt KR + 1) * (1 + MK)) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hKA.le (mul_nonneg (Real.sqrt_nonneg KR) hMKnn)) h2 2
    have h4 : (KA * (Real.sqrt KR + 1) * (1 + MK)) ^ 2
        = (KA * (Real.sqrt KR + 1)) ^ 2 * (1 + MK) ^ 2 := by ring
    have h5 : (KA * (Real.sqrt KR + 1)) ^ 2 * (1 + MK) ^ 2
        ≤ ((KA * (Real.sqrt KR + 1)) ^ 2 + 1) * (1 + MK) ^ 2 := by
      nlinarith [sq_nonneg (1 + MK), sq_nonneg (KA * (Real.sqrt KR + 1))]
    rw [h4] at h3
    linarith [h3, h5]
  exact le_trans hSq3 hfin

end Work.FTS.StrongPersist.L3Rhs.NfkAux
