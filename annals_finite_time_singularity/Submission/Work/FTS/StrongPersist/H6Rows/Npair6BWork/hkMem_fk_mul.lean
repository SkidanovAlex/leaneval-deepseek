/-
# `hkMem_fk_mul` — the `ℋ⁶`-membership of the seven `FK f ×` fields of the level-six `N`-row

The term `N α F Ψ` of §Modulation contains the `FK F ×`-fields `-(1/2) sin(2θ) FK F ∂_θF` and
`-sin²θ FK F F` (`Work.Construction.N`), and the splitting of the level-six `N`-row pairs the
coefficient `Kf = FK f` against the datum `f` and against the star profile `F_*` (and its
`D_θ`-derivative), with the extra angular factor `sin²θ` in two of the pieces.  This module
records the membership of those seven fields in `ℋ⁶`.

The route is

* `FK f` is a **radial** function: it is `C⁶` on `(0,∞)` (from `SmoothOpen f` + `HkMem α 7 f`,
  via `NfkAux.contDiffOn_FK` and `FK f = 3 F_*(f)`), and it is `ℋ⁶` (`fk_hkMem`, from
  `QangSq6Full` + `QangAe6`);
* a radial factor whose `D_z`-iterates are bounded (a.e. in `z`) multiplies `ℋ⁶` into itself
  (`Npair6SupAux.radialSupMul_cd6`); the bounds are supplied by `fk_dzd_bound` below, the one
  analytically non-trivial step: for a.e. `z`,
  `|D_z^b (FK f)(z)| = |FK (D_z^b f)(z)| ≤ ∫_θ K(θ)|D_z^b f(z,θ)| dθ`, the angular slice being
  controlled by the radial Hardy/Agmon inequality `N6Trans.SixAux.zslice6_hardy` (through
  `pure_slice_agmon`) and the resulting `θ`-integral by the Tonelli swap `hkSqSwapOpenK` at
  level `7`;
* the `F_*`-fields are priced by `𝒲^{6,∞}` (`FKstarSlotPiece`, `Fstar_W6`), and the extra
  `sin²θ` factor is `𝒲^{6,∞}`-priced too (`WlInf_sinSq`), so those pieces go through the
  `𝒲^{6,∞}`-product rule `hknorm_mul_WlInf6_cd6'`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.fk_hkMem
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.pure_slice_agmon
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.radialSupMul_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.FKstarSlotPiece
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.DzIter_FK_eq_ae
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.hkSqSwapOpenK
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.NfkSmooth
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.FkSlots
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.Cd6Basic
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.FTS.GalBasis.exists_cc_of_honClass
import Submission.Work.FTS.StrongPersist.Fstar_W6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0
import Submission.Work.FTS.H2.QangAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Elementary properties of the angular kernel `K(θ) = 3 sin θ cos²θ` -/

private theorem K_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Spaces.K θ := by
  have h1 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have h2 : 0 ≤ Real.cos θ ^ 2 := sq_nonneg _
  rw [Work.Spaces.K]
  positivity

private theorem K_le_three_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : Work.Spaces.K θ ≤ 3 := by
  have h1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have h2 : Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [Real.neg_one_le_cos θ, Real.cos_le_one θ]
  have h1' : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  rw [Work.Spaces.K]
  nlinarith

/-- The squared radial weight vanishes at the origin (Lean's totalised division). -/
private theorem w_zero : Work.Spaces.w 0 = 0 := by
  rw [Work.Spaces.w]
  norm_num

/-! ## The uniform bound on the radial derivatives of `FK f` -/

/-- **The radial `D_z`-iterates of the angular moment `FK f` are bounded on `(0,∞)`.**

For a datum `f` of the open-quadrant class which is `C^∞` on the quadrant and honestly in `ℋ⁶`
and `ℋ⁷`, there is `K` with `|D_z^b (FK f)(z)| ≤ K` for a.e. `z ∈ Iz` and every `b ≤ 6`. -/
theorem fk_dzd_bound : ∀ α ∈ Set.Ioc 0 1, ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ),
    Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
    ∃ K : ℝ, 0 < K ∧ ∀ b : ℕ, b ≤ 6 →
      ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        |Work.Elliptic.DzdIter b (fun z => Work.Construction.FK f z) z| ≤ K := by
  intro α hα f M hD
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hD.sm
  have hmem6 : Work.Spaces.HkMem α 6 f := hD.h6
  have hmem7 : Work.Spaces.HkMem α 7 f := hD.h7
  -- the level-`7` Tonelli swap and the conull set of good angles
  obtain ⟨hswap7, hAint7, hAslice7⟩ :=
    Work.FTS.StrongPersist.H6Pair6Aux.hkSqSwapOpenK α 7 f hsm hmem7
  have haeθ : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      σ ∈ Set.Ioo 0 (Real.pi / 2) := by
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
    filter_upwards [MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := Real.pi / 2)] with σ h
    exact fun hmem' => h.mpr hmem'
  -- the pointwise (in `θ`) radial Hardy/Agmon bound on the slices
  have hHardy : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), ∀ b : ℕ, b ≤ 6 →
      ∀ z : ℝ, 0 < z → (Work.Spaces.DzIter b f z σ) ^ 2
        ≤ 2 * ∫ s in Work.Spaces.Iz,
            (Work.Spaces.DzIter (b + 1) f s σ) ^ 2 * (Work.Spaces.w s) ^ 2 := by
    filter_upwards [hAslice7, haeθ] with σ hslice hσ
    intro b hb z hz
    exact pure_slice_agmon α f σ hα0 hα1 hsm hσ hslice b hb z hz
  -- the radial moments are dominated by the level-`7` slice integral
  have hBA : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), ∀ j : ℕ, j ≤ 7 →
      (∫ s in Work.Spaces.Iz, (Work.Spaces.DzIter j f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
        ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 7 f s σ := by
    filter_upwards [hAslice7, haeθ] with σ hslice hσ
    intro j hj
    refine MeasureTheory.integral_mono_of_nonneg (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (f := fun s => (Work.Spaces.DzIter j f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
      (g := fun s => Work.Spaces.HkIntegrand α 7 f s σ) ?_ hslice ?_
    · filter_upwards with s
      exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with s hs
      rcases eq_or_lt_of_le (Set.mem_Ici.mp hs) with h0 | hpos
      · subst h0
        rw [w_zero]
        simpa using Work.Spaces.HkIntegrand_nonneg α 7 f 0 σ
      · have h1 := Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq α 7 f j hj hpos hσ
        have hw : 0 < (Work.Spaces.w s) ^ 2 := pow_pos (Work.FTS.H2.w_pos hpos) 2
        rw [le_div_iff₀ hw] at h1
        exact h1
  -- the total mass of the angular interval is finite
  have hIθvol : MeasureTheory.volume Work.Spaces.Iθ ≠ ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  -- integrability of the dominating angular function
  have hAint7' : MeasureTheory.Integrable
      (fun σ : ℝ => 3 * (1 + ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 7 f s σ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h : MeasureTheory.Integrable
        (fun σ : ℝ => 3 * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 7 f s σ)
          + (3 : ℝ)) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (hAint7.const_mul 3).add
        (MeasureTheory.integrableOn_const (s := Work.Spaces.Iθ) (C := (3 : ℝ)) hIθvol)
    refine h.congr ?_
    filter_upwards with σ
    ring
  -- the value of the `θ`-integral of the dominating function
  have hfinal : (∫ σ in Work.Spaces.Iθ,
        3 * (1 + ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 7 f s σ))
      ≤ 3 * ((MeasureTheory.volume Work.Spaces.Iθ).toReal + Work.Spaces.HkSq α 7 f) := by
    have hcongr : (fun σ : ℝ => 3 * (1 + ∫ s in Work.Spaces.Iz,
          Work.Spaces.HkIntegrand α 7 f s σ))
        = fun σ : ℝ => (3 : ℝ) + 3 * (∫ s in Work.Spaces.Iz,
            Work.Spaces.HkIntegrand α 7 f s σ) := by
      funext σ; ring
    rw [hcongr]
    have hsplit : (∫ σ in Work.Spaces.Iθ, ((3 : ℝ) + 3 * (∫ s in Work.Spaces.Iz,
          Work.Spaces.HkIntegrand α 7 f s σ)))
        = (∫ σ in Work.Spaces.Iθ, (3 : ℝ))
          + ∫ σ in Work.Spaces.Iθ, 3 * (∫ s in Work.Spaces.Iz,
              Work.Spaces.HkIntegrand α 7 f s σ) :=
      MeasureTheory.integral_add
        (MeasureTheory.integrableOn_const (s := Work.Spaces.Iθ) (C := (3 : ℝ)) hIθvol)
        (hAint7.const_mul 3)
    rw [hsplit, MeasureTheory.setIntegral_const, MeasureTheory.integral_const_mul, hswap7,
      smul_eq_mul, MeasureTheory.Measure.real]
    linarith [ENNReal.toReal_nonneg (a := (MeasureTheory.volume Work.Spaces.Iθ)),
      Work.Spaces.HkSq_nonneg α 7 f]
  -- the constant
  set Kc : ℝ := 3 * ((MeasureTheory.volume Work.Spaces.Iθ).toReal + Work.Spaces.HkSq α 7 f) + 1
    with hKcdef
  have hKcpos : 0 < Kc := by
    rw [hKcdef]
    have h1 : 0 ≤ (MeasureTheory.volume Work.Spaces.Iθ).toReal := ENNReal.toReal_nonneg
    have h2 : 0 ≤ Work.Spaces.HkSq α 7 f := Work.Spaces.HkSq_nonneg α 7 f
    linarith
  refine ⟨Kc, hKcpos, fun b hb => ?_⟩
  -- the a.e. identification of `D_z^b (FK f)` with `FK (D_z^b f)`
  have hid := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.DzIter_FK_eq_ae hsm hmem6 b hb
  have haepos : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
    filter_upwards [MeasureTheory.Measure.ae_ne (MeasureTheory.volume) (0 : ℝ)] with z hz hzI
    exact lt_of_le_of_ne hzI (Ne.symm hz)
  filter_upwards [hid, haepos] with z hzid hzpos
  have hval : Work.Elliptic.DzdIter b (fun z => Work.Construction.FK f z) z
      = Work.Construction.FK (Work.Spaces.DzIter b f) z := by
    have h0 := hzid 0
    rwa [Work.Elliptic.DzIter_rad] at h0
  rw [hval]
  -- the chain of inequalities
  have h1 : |Work.Construction.FK (Work.Spaces.DzIter b f) z|
      ≤ ∫ σ in Work.Spaces.Iθ, Work.Spaces.K σ * |Work.Spaces.DzIter b f z σ| := by
    rw [show Work.Construction.FK (Work.Spaces.DzIter b f) z
        = ∫ σ in Work.Spaces.Iθ, Work.Spaces.DzIter b f z σ * Work.Spaces.K σ from rfl]
    have hnorm := norm_integral_le_integral_norm
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (fun σ : ℝ => Work.Spaces.DzIter b f z σ * Work.Spaces.K σ)
    rw [Real.norm_eq_abs] at hnorm
    refine le_trans hnorm ?_
    refine le_of_eq (MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun σ hσ => ?_))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (K_nonneg_Iθ hσ)]
    ring
  have h2 : (∫ σ in Work.Spaces.Iθ, Work.Spaces.K σ * |Work.Spaces.DzIter b f z σ|)
      ≤ ∫ σ in Work.Spaces.Iθ,
          3 * (1 + ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 7 f s σ) := by
    refine MeasureTheory.integral_mono_of_nonneg (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      ?_ hAint7' ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with σ hσ
      exact mul_nonneg (K_nonneg_Iθ hσ) (abs_nonneg _)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc, hHardy, hBA]
        with σ hσ hH hB
      have hKnn : 0 ≤ Work.Spaces.K σ := K_nonneg_Iθ hσ
      have hK3 : Work.Spaces.K σ ≤ 3 := K_le_three_Iθ hσ
      have hH' : |Work.Spaces.DzIter b f z σ| ≤ 1 + ∫ s in Work.Spaces.Iz,
          (Work.Spaces.DzIter (b + 1) f s σ) ^ 2 * (Work.Spaces.w s) ^ 2 := by
        have hsq := hH b hb z hzpos
        have hnn : 0 ≤ ∫ s in Work.Spaces.Iz,
            (Work.Spaces.DzIter (b + 1) f s σ) ^ 2 * (Work.Spaces.w s) ^ 2 :=
          MeasureTheory.setIntegral_nonneg measurableSet_Ici
            (fun s _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
        have hsq' : (Work.Spaces.DzIter b f z σ) ^ 2
            ≤ (1 + ∫ s in Work.Spaces.Iz,
                (Work.Spaces.DzIter (b + 1) f s σ) ^ 2 * (Work.Spaces.w s) ^ 2) ^ 2 := by
          nlinarith
        have h1B : (0 : ℝ) ≤ 1 + ∫ s in Work.Spaces.Iz,
            (Work.Spaces.DzIter (b + 1) f s σ) ^ 2 * (Work.Spaces.w s) ^ 2 := by linarith
        have h2' := sq_le_sq.mp hsq'
        rwa [abs_of_nonneg h1B] at h2'
      have hB' := hB (b + 1) (by omega)
      calc Work.Spaces.K σ * |Work.Spaces.DzIter b f z σ|
          ≤ Work.Spaces.K σ * (1 + ∫ s in Work.Spaces.Iz,
              (Work.Spaces.DzIter (b + 1) f s σ) ^ 2 * (Work.Spaces.w s) ^ 2) :=
            mul_le_mul_of_nonneg_left hH' hKnn
        _ ≤ 3 * (1 + ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 7 f s σ) := by
            refine mul_le_mul hK3 (by linarith [hB']) (by positivity) (by norm_num)
  calc |Work.Construction.FK (Work.Spaces.DzIter b f) z|
      ≤ ∫ σ in Work.Spaces.Iθ, Work.Spaces.K σ * |Work.Spaces.DzIter b f z σ| := h1
    _ ≤ ∫ σ in Work.Spaces.Iθ,
          3 * (1 + ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 7 f s σ) := h2
    _ ≤ 3 * ((MeasureTheory.volume Work.Spaces.Iθ).toReal + Work.Spaces.HkSq α 7 f) := hfinal
    _ ≤ Kc := by rw [hKcdef]; linarith

/-! ## The seven membership statements -/

theorem hkMem_fk_mul : ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      (Work.Spaces.HkMem α 6 (fun z θ => Work.Construction.FK f z * f z θ) ∧
       Work.Spaces.HkMem α 6 (fun z θ => Work.Construction.FK f z * Work.Spaces.Dth f z θ) ∧
       Work.Spaces.HkMem α 6 (fun z θ => Work.Construction.FK f z * Work.Construction.Fstar α z θ) ∧
       Work.Spaces.HkMem α 6 (fun z θ =>
          Work.Construction.FK f z * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ∧
       Work.Spaces.HkMem α 6 (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z * f z θ) ∧
       Work.Spaces.HkMem α 6 (fun z θ =>
          Real.sin θ ^ 2 * Work.Construction.FK f z * Work.Spaces.Dth f z θ) ∧
       Work.Spaces.HkMem α 6 (fun z θ =>
          Real.sin θ ^ 2 * Work.Construction.FK f z * Work.Construction.Fstar α z θ)) := by
  intro α hα f M hD
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hD.sm
  have hmem6 : Work.Spaces.HkMem α 6 f := hD.h6
  have hmem7 : Work.Spaces.HkMem α 7 f := hD.h7
  -- `FK f` is `C⁶` on the open quadrant and `ℋ⁶`
  have hFKcd : ContDiffOn ℝ 6
      (Function.uncurry (fun z (_ : ℝ) => Work.Construction.FK f z))
      Work.FTS.EllipticEst.Q0 := by
    have h6 : ContDiffOn ℝ 6 (fun z => Work.Construction.FK f z) (Set.Ioi (0 : ℝ)) := by
      have hF : ContDiffOn ℝ 6 (Work.Elliptic.Fstar f) (Set.Ioi (0 : ℝ)) :=
        Work.FTS.EllipticEst.UopHk.contDiffOn_Fstar_of_smoothOpen_Hk α 7 f hsm hmem7
          (by norm_num)
      rw [Work.FTS.StrongPersist.L3Rhs.NfkAux.fk_eq_three_Fstar f]
      have h3 : ContDiffOn ℝ 6 (fun z => (3 : ℝ) • Work.Elliptic.Fstar f z)
          (Set.Ioi (0 : ℝ)) := hF.const_smul (3 : ℝ)
      simpa only [Pi.smul_apply, smul_eq_mul] using h3
    exact Work.FTS.StrongPersist.L3Rhs.NfkAux.contDiffOn_radial h6
  have hFKmem : Work.Spaces.HkMem α 6 (fun z (_ : ℝ) => Work.Construction.FK f z) :=
    fk_hkMem α hα f hsm hmem6
  -- the a.e. slot bounds for the radial factor
  obtain ⟨K, hKpos, hKb⟩ := fk_dzd_bound α hα f M hD
  have hslots : ∀ j : ℕ, j ≤ 6 → ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ∀ θ : ℝ, |Work.Spaces.DzIter j (fun z (_ : ℝ) => Work.Construction.FK f z) z θ| ≤ K := by
    intro j hj
    filter_upwards [hKb j hj] with z hz θ
    rwa [Work.Elliptic.DzIter_rad]
  -- smoothness of the two datum fields and of the angular factor `sin²θ`
  have hfcd : ContDiffOn ℝ 6 (Function.uncurry f) Work.FTS.EllipticEst.Q0 := hsm.forall 6
  have hdthcd : ContDiffOn ℝ 6 (Function.uncurry (Work.Spaces.Dth f))
      Work.FTS.EllipticEst.Q0 := hsm.Dth.forall 6
  have hdthmem : Work.Spaces.HkMem α 6 (Work.Spaces.Dth f) :=
    Work.FTS.IPGen.HkMem_Dth_le (k := 6) (by linarith) hsm hmem7
  have hsinsqcd : ContDiffOn ℝ 6 (Function.uncurry (fun z θ => Real.sin θ ^ 2))
      Work.FTS.EllipticEst.Q0 := by
    have hAsm : ContDiff ℝ (6 : WithTop ℕ∞) (fun p : ℝ × ℝ => Real.sin p.2 ^ 2) := by fun_prop
    convert hAsm.contDiffOn using 1
    funext p
    rcases p with ⟨z, θ⟩
    rfl
  -- the radial-multiplier rows
  obtain ⟨Crad, hCrad, hRadial⟩ :=
    Work.FTS.StrongPersist.H6Rows.Npair6SupAux.radialSupMul_cd6
  have hprod1 : ContDiffOn ℝ 6
      (Function.uncurry (fun z θ => Work.Construction.FK f z * f z θ))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.contDiffOn_uncurry_mul_cd6 hFKcd hfcd
  have hprod2 : ContDiffOn ℝ 6
      (Function.uncurry (fun z θ => Work.Construction.FK f z * Work.Spaces.Dth f z θ))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.contDiffOn_uncurry_mul_cd6 hFKcd hdthcd
  have hmem1 : Work.Spaces.HkMem α 6 (fun z θ => Work.Construction.FK f z * f z θ) :=
    (hRadial (α := α) (a := fun z => Work.Construction.FK f z) (g := f) (K := K)
      hα0 hα1 hKpos.le hFKcd hfcd hslots hmem6).2.1
  have hmem2 : Work.Spaces.HkMem α 6
      (fun z θ => Work.Construction.FK f z * Work.Spaces.Dth f z θ) :=
    (hRadial (α := α) (a := fun z => Work.Construction.FK f z) (g := Work.Spaces.Dth f) (K := K)
      hα0 hα1 hKpos.le hFKcd hdthcd hslots hdthmem).2.1
  -- the `𝒲^{6,∞}`-priced product rule and the star-field rows
  obtain ⟨Cw, hCw, hmulW⟩ :=
    Work.FTS.StrongPersist.H6Rows.Npair6SupAux.hknorm_mul_WlInf6_cd6'
  obtain ⟨Csinsq, hCsinsq, hSinsqW⟩ := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.WlInf_sinSq
  obtain ⟨CFs, hCFs, hFstarW⟩ := Work.FTS.StrongPersist.Fstar_W6
  have hFstarcd : ContDiffOn ℝ 6 (Function.uncurry (Work.Construction.Fstar α))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α).forall 6
  -- conjunct 3: `FK f · F_*`
  have hmem3 : Work.Spaces.HkMem α 6
      (fun z θ => Work.Construction.FK f z * Work.Construction.Fstar α z θ) := by
    have h := (hmulW α (Work.Construction.Fstar α)
      (fun z (_ : ℝ) => Work.Construction.FK f z) hα0 hα1 hFstarcd
      (hFstarW α hα0 hα1).1 hFKcd hFKmem).1
    exact Work.FTS.GalBasis.HkMem_congr_all (fun z θ => mul_comm _ _) α 6 h
  obtain ⟨Cstar, hCstar, hFKstar⟩ :=
    Work.FTS.StrongPersist.H6Rows.Npair6SupAux.FKstarSlotPiece
  -- conjuncts 4 and 7: the two `FK f ×`-star-slot pieces
  obtain ⟨⟨-, hmem4, -⟩, ⟨-, hmem7', -⟩⟩ :=
    hFKstar (α := α)
      (Kf := Work.Spaces.HkNorm α 6 (fun z (_ : ℝ) => Work.Construction.FK f z))
      hα0 hα1 (Work.Spaces.HkNorm_nonneg α 6 _) hsm hmem6 hFKcd hFKmem le_rfl
  -- conjuncts 5 and 6: the extra angular factor `sin²θ`
  have hmem5 : Work.Spaces.HkMem α 6
      (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z * f z θ) := by
    have h := (hmulW α (fun z θ => Real.sin θ ^ 2)
      (fun z θ => Work.Construction.FK f z * f z θ) hα0 hα1 hsinsqcd
      (hSinsqW α hα0 hα1).1 hprod1 hmem1).1
    exact Work.FTS.GalBasis.HkMem_congr_all (fun z θ => by ring) α 6 h
  have hmem6' : Work.Spaces.HkMem α 6
      (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z * Work.Spaces.Dth f z θ) := by
    have h := (hmulW α (fun z θ => Real.sin θ ^ 2)
      (fun z θ => Work.Construction.FK f z * Work.Spaces.Dth f z θ) hα0 hα1 hsinsqcd
      (hSinsqW α hα0 hα1).1 hprod2 hmem2).1
    exact Work.FTS.GalBasis.HkMem_congr_all (fun z θ => by ring) α 6 h
  exact ⟨hmem1, hmem2, hmem3, hmem4, hmem5, hmem6', hmem7'⟩

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
