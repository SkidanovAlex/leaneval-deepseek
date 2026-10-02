/-
Copyright: Work.MRMT (mandelbar) subproject.

# The principal solution of the Beltrami equation for a smooth coefficient

Let `μ : ℂ → ℂ` be smooth (`C^∞`) with compact support and `‖μ z‖ ≤ k < 1` for all `z`.  Then there
is a `C¹` homeomorphism `F` of `ℂ` (both `F` and `F⁻¹` are `C¹`) with

* `∂̄F = μ ∂F` pointwise everywhere, and
* the principal normalisation `F z = z + O(1/‖z‖)`.

This is the smooth case of the measurable Riemann mapping theorem (Ahlfors–Bers).  The proof
follows the classical construction: `F = z + C h`, where `h ∈ L²` is the solution of the
Ahlfors–Bers equation `h = μ (1 + S h)` (`S` the Beurling transform) and `C` the Cauchy transform.
For a smooth coefficient this `L²` solution is `C²` (a difference-quotient/Fourier argument,
`Found/translateL2_sub_pow_le` + `Found/memLp_fourier_weight` +
`Found/contDiff_two_of_memLp_fourier_weight`).  Ahlfors' exponential trick shows `∂F` has no
zeros, so `F` is a local diffeomorphism; the normalisation `F z = z + O(1/‖z‖)` makes it a proper
local homeomorphism of degree one, hence a homeomorphism.
-/
import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.PrincipalAux
import Submission.Work.MRMT.Found.hsolA_spec
import Submission.Work.MRMT.Found.qsol_spec
import Submission.Work.MRMT.Found.beurlingL2_eq_cauchyTransform_dz
import Submission.Work.MRMT.Found.cauchyTransform_contDiff_one
import Submission.Work.MRMT.Found.memLp_cauchyTransform_dz
import Submission.Work.MRMT.Found.contDiff_invFun_of_contDiff
import Submission.Work.MRMT.Found.exists_continuousLinearEquiv_of_dz_dzbar
import Submission.Work.MRMT.Found.translateL2_sub_pow_le
import Submission.Work.MRMT.Found.memLp_fourier_weight
import Submission.Work.MRMT.Found.contDiff_two_of_memLp_fourier_weight
import Submission.Work.MRMT.Found.cauchyTransform_decay_of_contDiff_one
import Submission.Work.MRMT.Found.cauchyTransform_sub_le
import Submission.Work.MRMT.Found.exists_homeomorph_of_localInj_proper
import Submission.Work.MRMT.Found.DecayAux
import Submission.Work.MRMT.QC.WirtingerCalc
import Submission.Work.MRMT.QC.isQCOn_of_isOpen_cover
import Submission.Work.MRMT.QC.smooth_approx_w12
import Submission.Work.MRMT.AhlforsBers.Affine
import Submission.Work.MRMT.Wirtinger.dz_comp
import Submission.Work.MRMT.Wirtinger.dzbar_comp
import Submission.Work.MRMT.Weyl.Defs
import Submission.Work.MRMT.Weyl.isDzDeriv_moll_gen
import Submission.Work.MRMT.Beltrami.cauchyTransform_dz_memLp
import Submission.Work.MRMT.Cauchy.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Filter Topology Complex Function
open scoped Distributions Topology ENNReal

namespace Work.MRMT.Found

/-! ## Elementary glue -/

theorem support_subset_tsupport'_ec {f : ℂ → ℂ} : Function.support f ⊆ tsupport f := subset_closure

/-- The real Fréchet derivative of a map `ℂ → ℂ` in terms of the Wirtinger derivatives. -/
theorem fderiv_apply_eq_dz_add_dzbar_star_ec (f : ℂ → ℂ) (z w : ℂ) :
    fderiv ℝ f z w = dz f z * w + dzbar f z * star w := by
  have h := Work.MRMT.Wirtinger.realLinearMap_apply_eq (fderiv ℝ f z) w
  rw [h]
  unfold dz dzbar
  ring

/-- The real Fréchet derivative of the complex exponential. -/
theorem hasFDerivAt_exp_ec (z : ℂ) :
    HasFDerivAt (fun w : ℂ => Complex.exp w) ((ContinuousLinearMap.mul ℝ ℂ) (Complex.exp z)) z := by
  have h2 := ((Complex.hasStrictDerivAt_exp z).hasStrictFDerivAt.hasFDerivAt).restrictScalars ℝ
  have h3 : ContinuousLinearMap.restrictScalars ℝ
      (ContinuousLinearMap.toSpanSingleton ℂ (Complex.exp z))
      = (ContinuousLinearMap.mul ℝ ℂ) (Complex.exp z) := by
    ext w
    rw [show (ContinuousLinearMap.restrictScalars ℝ
        (ContinuousLinearMap.toSpanSingleton ℂ (Complex.exp z))) w
        = (ContinuousLinearMap.toSpanSingleton ℂ (Complex.exp z)) w from rfl]
    simp [ContinuousLinearMap.toSpanSingleton_apply, mul_comm]
  rwa [h3] at h2

/-- `∂̄` of the complex exponential. -/
theorem dzbar_exp_ec (z : ℂ) : dzbar (fun w : ℂ => Complex.exp w) z = 0 := by
  rw [dzbar, (hasFDerivAt_exp_ec z).fderiv]
  have h1 : (ContinuousLinearMap.mul ℝ ℂ (Complex.exp z)) 1 = Complex.exp z := by simp
  have hI : (ContinuousLinearMap.mul ℝ ℂ (Complex.exp z)) Complex.I
      = Complex.exp z * Complex.I := rfl
  rw [h1, hI]
  rw [show Complex.I * (Complex.exp z * Complex.I) = Complex.exp z * (Complex.I * Complex.I) by ring,
    Complex.I_mul_I]
  ring

/-- `∂` of the complex exponential. -/
theorem dz_exp_ec (z : ℂ) : dz (fun w : ℂ => Complex.exp w) z = Complex.exp z := by
  rw [dz, (hasFDerivAt_exp_ec z).fderiv]
  have h1 : (ContinuousLinearMap.mul ℝ ℂ (Complex.exp z)) 1 = Complex.exp z := by simp
  have hI : (ContinuousLinearMap.mul ℝ ℂ (Complex.exp z)) Complex.I
      = Complex.exp z * Complex.I := rfl
  rw [h1, hI]
  rw [show Complex.I * (Complex.exp z * Complex.I) = Complex.exp z * (Complex.I * Complex.I) by ring,
    Complex.I_mul_I]
  ring

/-- `∂` of a `C^∞` function is `C^∞`. -/
theorem contDiff_dz_top_ec {f : ℂ → ℂ} (h : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) :
    ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (dz f) := by
  have htop : (↑(⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by simp
  have hfd : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ f) := h.fderiv_right htop
  have h1 : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun z => fderiv ℝ f z 1) :=
    hfd.clm_apply contDiff_const
  have hI : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun z => fderiv ℝ f z Complex.I) :=
    hfd.clm_apply contDiff_const
  have hmain : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => ((fderiv ℝ f z) 1 - Complex.I * (fderiv ℝ f z) Complex.I) / 2) :=
    (h1.sub (contDiff_const.mul hI)).div_const 2
  rwa [show (fun z => ((fderiv ℝ f z) 1 - Complex.I * (fderiv ℝ f z) Complex.I) / 2) = dz f
    from rfl] at hmain

/-- `∂` of a `C²` function is `C¹`. -/
theorem contDiff_one_dz_ec {f : ℂ → ℂ} (h : ContDiff ℝ 2 f) : ContDiff ℝ 1 (dz f) := by
  have htwo : (1 : WithTop ℕ∞) + 1 ≤ 2 := by norm_num
  have hfd : ContDiff ℝ 1 (fderiv ℝ f) := h.fderiv_right htwo
  have h1 : ContDiff ℝ 1 (fun z => fderiv ℝ f z 1) := hfd.clm_apply contDiff_const
  have hI : ContDiff ℝ 1 (fun z => fderiv ℝ f z Complex.I) := hfd.clm_apply contDiff_const
  have hmain : ContDiff ℝ 1
      (fun z => ((fderiv ℝ f z) 1 - Complex.I * (fderiv ℝ f z) Complex.I) / 2) :=
    (h1.sub (contDiff_const.mul hI)).div_const 2
  rwa [show (fun z => ((fderiv ℝ f z) 1 - Complex.I * (fderiv ℝ f z) Complex.I) / 2) = dz f
    from rfl] at hmain

/-- `∂̄` of a `C²` function is `C¹`. -/
theorem contDiff_one_dzbar_ec {f : ℂ → ℂ} (h : ContDiff ℝ 2 f) : ContDiff ℝ 1 (dzbar f) := by
  have htwo : (1 : WithTop ℕ∞) + 1 ≤ 2 := by norm_num
  have hfd : ContDiff ℝ 1 (fderiv ℝ f) := h.fderiv_right htwo
  have h1 : ContDiff ℝ 1 (fun z => fderiv ℝ f z 1) := hfd.clm_apply contDiff_const
  have hI : ContDiff ℝ 1 (fun z => fderiv ℝ f z Complex.I) := hfd.clm_apply contDiff_const
  have hmain : ContDiff ℝ 1
      (fun z => ((fderiv ℝ f z) 1 + Complex.I * (fderiv ℝ f z) Complex.I) / 2) :=
    (h1.add (contDiff_const.mul hI)).div_const 2
  rwa [show (fun z => ((fderiv ℝ f z) 1 + Complex.I * (fderiv ℝ f z) Complex.I) / 2) = dzbar f
    from rfl] at hmain

/-- `∂` of a negation (it is `-1` times the function). -/
theorem dz_neg'_ec (f : ℂ → ℂ) (z : ℂ) : dz (fun w => -f w) z = - dz f z := by
  have h := Work.MRMT.AhlforsBers.dz_const_mul_add (-1) 0 f z
  simpa using h

/-- `∂̄` of a negation (it is `-1` times the function). -/
theorem dzbar_neg'_ec (f : ℂ → ℂ) (z : ℂ) : dzbar (fun w => -f w) z = - dzbar f z := by
  have h := Work.MRMT.AhlforsBers.dzbar_const_mul_add (-1) 0 f z
  simpa using h

/-- `∂` of a constant. -/
theorem dz_const''_ec (c : ℂ) (z : ℂ) : dz (fun _ : ℂ => c) z = 0 := by simp [dz]

/-- `∂̄` of a constant. -/
theorem dzbar_const'_ec (c : ℂ) (z : ℂ) : dzbar (fun _ : ℂ => c) z = 0 := by simp [dzbar]

/-- `∂` of a function minus a constant. -/
theorem dz_sub_const'_ec (c : ℂ) (f : ℂ → ℂ) (z : ℂ) : dz (fun w => f w - c) z = dz f z := by
  have hfun : (fun w : ℂ => f w - c) = (fun w => 1 * f w + (-c)) := by funext w; ring
  rw [hfun, Work.MRMT.AhlforsBers.dz_const_mul_add 1 (-c) f z]
  ring

/-- `∂̄` of a function minus a constant. -/
theorem dzbar_sub_const'_ec (c : ℂ) (f : ℂ → ℂ) (z : ℂ) : dzbar (fun w => f w - c) z = dzbar f z := by
  have hfun : (fun w : ℂ => f w - c) = (fun w => 1 * f w + (-c)) := by funext w; ring
  rw [hfun, Work.MRMT.AhlforsBers.dzbar_const_mul_add 1 (-c) f z]
  ring

/-- Local square integrability of a continuous function. -/
theorem memL2LocOn_univ_of_continuous_ec {f : ℂ → ℂ} (hf : Continuous f) :
    MemL2LocOn f Set.univ := by
  intro K hK
  have hcont : ContinuousOn (fun z : ℂ => ‖f z‖ ^ 2) K := (hf.norm.pow 2).continuousOn
  simpa [Set.inter_univ] using ContinuousOn.integrableOn_compact hK hcont

theorem isDzDerivOn_univ_iff_ec {f g : ℂ → ℂ} : IsDzDerivOn f g Set.univ ↔ IsDzDeriv f g := by
  constructor
  · rintro ⟨hl, hlg, hmain⟩
    exact ⟨locallyIntegrableOn_univ.mp hl, locallyIntegrableOn_univ.mp hlg,
      fun φ => hmain φ (Set.subset_univ _)⟩
  · rintro ⟨hl, hlg, hmain⟩
    exact ⟨locallyIntegrableOn_univ.mpr hl, locallyIntegrableOn_univ.mpr hlg,
      fun φ _ => hmain φ⟩

theorem isDbarDerivOn_univ_iff_ec {f g : ℂ → ℂ} : IsDbarDerivOn f g Set.univ ↔ IsDbarDeriv f g := by
  constructor
  · rintro ⟨hl, hlg, hmain⟩
    exact ⟨locallyIntegrableOn_univ.mp hl, locallyIntegrableOn_univ.mp hlg,
      fun φ => hmain φ (Set.subset_univ _)⟩
  · rintro ⟨hl, hlg, hmain⟩
    exact ⟨locallyIntegrableOn_univ.mpr hl, locallyIntegrableOn_univ.mpr hlg,
      fun φ _ => hmain φ⟩

/-- A `C¹` function is locally of class `W^{1,2}` on `ℂ`. -/
theorem hasW12LocOn_univ_of_contDiff_one_ec {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) :
    HasW12LocOn f Set.univ := by
  have hone : (1 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hdz : IsDzDeriv f (dz f) := Work.MRMT.Weyl.isDzDeriv_dz hf hone
  have hdzbar : IsDbarDeriv f (dzbar f) := Work.MRMT.Weyl.isDbarDeriv_dzbar hf hone
  exact ⟨memL2LocOn_univ_of_continuous_ec hf.continuous, dz f, dzbar f,
    isDzDerivOn_univ_iff_ec.mpr hdz, isDbarDerivOn_univ_iff_ec.mpr hdzbar,
    memL2LocOn_univ_of_continuous_ec (Work.MRMT.Beltrami.continuous_dz_of_contDiff f hone hf),
    memL2LocOn_univ_of_continuous_ec (Work.MRMT.Weyl.continuous_dzbar_of_contDiff hf hone),
    Eventually.of_forall fun _ => rfl, Eventually.of_forall fun _ => rfl⟩

/-- A continuous map with linear growth at infinity is proper. -/
theorem isProperMap_of_growth_ec {f : ℂ → ℂ} (hf : Continuous f)
    (hgr : ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖z‖ / 2 ≤ ‖f z‖) : IsProperMap f := by
  obtain ⟨R, hR⟩ := hgr
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨hf, fun K hK => ?_⟩
  rw [Metric.isCompact_iff_isClosed_bounded]
  obtain ⟨M, hM⟩ := hK.isBounded.exists_norm_le
  refine ⟨hK.isClosed.preimage hf, ?_⟩
  rw [isBounded_iff_forall_norm_le]
  refine ⟨max (max R 1) (2 * max M 0), fun z hz => ?_⟩
  by_cases hzR : R ≤ ‖z‖
  · have h1 := hR z hzR
    have h2 : ‖f z‖ ≤ M := hM (f z) hz
    have h3 : M ≤ max M 0 := le_max_left M 0
    have h4 : ‖z‖ ≤ 2 * max M 0 := by linarith
    exact h4.trans (le_max_right _ _)
  · rw [not_le] at hzR
    exact hzR.le.trans ((le_max_left R 1).trans (le_max_left _ _))

/-- **The principal solution of the Beltrami equation for a smooth compactly supported
coefficient.** -/
theorem exists_contDiff_principal_of_contDiff_ec {μ : ℂ → ℂ} (hμ : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) μ)
    (hs : HasCompactSupport μ) {k : ℝ} (hk : k < 1) (hb : ∀ z : ℂ, ‖μ z‖ ≤ k) :
    ∃ F : ℂ ≃ₜ ℂ, ContDiff ℝ 1 (F : ℂ → ℂ) ∧ ContDiff ℝ 1 ((F.symm : ℂ → ℂ)) ∧
      (∀ z : ℂ, dzbar (F : ℂ → ℂ) z = μ z * dz (F : ℂ → ℂ) z) ∧
      ∃ C R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖F z - z‖ ≤ C / ‖z‖ := by
  -- ## Step 0: basic data about `μ`
  have hμc : Continuous μ := hμ.continuous
  have hbae : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k := ae_of_all _ hb
  have hμLp : MemLp μ 2 (volume : Measure ℂ) := hμc.memLp_of_hasCompactSupport hs
  have hμad : Admissible μ := ⟨hμc.aestronglyMeasurable, ⟨k, hk, hbae⟩,
    hs.isBounded.subset support_subset_tsupport'_ec⟩
  have hdμcd : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (dz μ) := contDiff_dz_top_ec hμ
  have hdμcs : HasCompactSupport (dz μ) := hasCompactSupport_dz hs
  have hdμLp : MemLp (dz μ) 2 (volume : Measure ℂ) := hdμcd.continuous.memLp_of_hasCompactSupport hdμcs
  -- ## Step 1: `C²` representatives of the two `L²` solutions
  -- (1a) the principal solution `h = (1 - μS)⁻¹ μ`
  set hL : Lp ℂ 2 (volume : Measure ℂ) := hsolA μ hμad hμLp with hhL
  obtain ⟨hhL_eq, hhL_norm, hhL_supp⟩ := hsolA_spec hμad hμLp hk hbae
  obtain ⟨H, hH2, hHcs, hHae⟩ : ∃ H : ℂ → ℂ, ContDiff ℝ 2 H ∧ HasCompactSupport H ∧
      H =ᵐ[(volume : Measure ℂ)] (hL : ℂ → ℂ) := by
    have hsupp₁ : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ tsupport μ → (hL : ℂ → ℂ) z = 0 := by
      filter_upwards [hhL_supp] with z hz hzt
      exact hz (fun hmem => hzt (support_subset_tsupport'_ec hmem))
    have heq₁ : (hL : ℂ → ℂ) =ᵐ[(volume : Measure ℂ)] fun z => μ z + μ z *
        ((beurlingL2 ((Lp.memLp hL).toLp (hL : ℂ → ℂ)) : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) z := by
      rw [Lp.toLp_coeFn]
      filter_upwards [hhL_eq] with z hz
      rw [hz]; ring
    obtain ⟨C₁, hC₁0, hC₁⟩ := translateL2_sub_pow_le hμ hμ hs hs hk hb (Lp.memLp hL) heq₁ 4
    exact contDiff_two_of_memLp_fourier_weight hs (Lp.memLp hL) hsupp₁
      (memLp_fourier_weight (Lp.memLp hL) ⟨C₁, hC₁0, hC₁⟩)
  -- (1b) the solution with source `∂μ` (for Ahlfors' trick)
  set qL : Lp ℂ 2 (volume : Measure ℂ) := qsol μ (dz μ) hdμLp with hqL
  obtain ⟨hqL_eq, hqL_norm, hqL_supp⟩ := qsol_spec hμad hk hbae hdμLp
  obtain ⟨Q, hQ2, hQcs, hQae⟩ : ∃ Q : ℂ → ℂ, ContDiff ℝ 2 Q ∧ HasCompactSupport Q ∧
      Q =ᵐ[(volume : Measure ℂ)] (qL : ℂ → ℂ) := by
    have hqsupp : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ tsupport μ → (qL : ℂ → ℂ) z = 0 := by
      filter_upwards [hqL_supp] with z hz hzt
      refine hz (fun hmem => hzt (support_subset_tsupport'_ec hmem))
        (fun hmem => hzt (Work.MRMT.QC.tsupport_dz_subset μ (support_subset_tsupport'_ec hmem)))
    have heq₂ : (qL : ℂ → ℂ) =ᵐ[(volume : Measure ℂ)] fun z => dz μ z + μ z *
        ((beurlingL2 ((Lp.memLp qL).toLp (qL : ℂ → ℂ)) : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) z := by
      rw [hqL]
      rw [Lp.toLp_coeFn]
      exact hqL_eq
    obtain ⟨C₂, hC₂0, hC₂⟩ := translateL2_sub_pow_le hμ hdμcd hs hdμcs hk hb (Lp.memLp qL) heq₂ 4
    exact contDiff_two_of_memLp_fourier_weight hs (Lp.memLp qL) hqsupp
      (memLp_fourier_weight (Lp.memLp qL) ⟨C₂, hC₂0, hC₂⟩)
  -- ## Step 2: the map `F = z + C H` and its Wirtinger derivatives
  have hH1 : ContDiff ℝ 1 H := hH2.of_le (by norm_num)
  obtain ⟨hCH1, hdzbar_CH, hdz_CH⟩ := cauchyTransform_contDiff_one hH1 hHcs
  have hdzH1 : ContDiff ℝ 1 (dz H) := contDiff_one_dz_ec hH2
  have hdzHcs : HasCompactSupport (dz H) := hasCompactSupport_dz hHcs
  obtain ⟨hCdH1, hdzbar_CdH, hdz_CdH⟩ := cauchyTransform_contDiff_one hdzH1 hdzHcs
  have hHmem : MemLp H 2 (volume : Measure ℂ) := hH1.continuous.memLp_of_hasCompactSupport hHcs
  have htoLp : hHmem.toLp H = hL := by
    rw [MemLp.toLp_congr hHmem (Lp.memLp hL) hHae]
    exact Lp.toLp_coeFn hL (Lp.memLp hL)
  have hber := beurlingL2_eq_cauchyTransform_dz hH1 hHcs hHmem
  rw [htoLp] at hber
  have hH_eq_ae : H =ᵐ[(volume : Measure ℂ)] fun z => μ z * (1 + cauchyTransform (dz H) z) := by
    filter_upwards [hHae, hhL_eq, hber] with z h1 h2 h3
    rw [h1, h2, h3]
  have hH_eq : H = fun z => μ z * (1 + cauchyTransform (dz H) z) :=
    Measure.eq_of_ae_eq hH_eq_ae hH1.continuous
      (hμc.mul (continuous_const.add hCdH1.continuous))
  let F : ℂ → ℂ := fun z => z + cauchyTransform H z
  have hF1 : ContDiff ℝ 1 F := contDiff_id.add hCH1
  have hFcont : Continuous F := hF1.continuous
  have hdzF : ∀ z, dz F z = 1 + cauchyTransform (dz H) z := by
    intro z
    have h1 : DifferentiableAt ℝ (fun w : ℂ => w) z := differentiableAt_id
    have h2 : DifferentiableAt ℝ (cauchyTransform H) z := hCH1.differentiable (by norm_num) z
    have h3 : dz (fun w : ℂ => w + cauchyTransform H w) z
        = dz (fun w : ℂ => w) z + cauchyTransform (dz H) z := by
      rw [Work.MRMT.QC.dz_add_of_diff h1 h2, hdz_CH z]
    rw [show dz F z = dz (fun w : ℂ => w + cauchyTransform H w) z from rfl, h3]
    rw [show (fun w : ℂ => w) = (id : ℂ → ℂ) from rfl, dz_id]
  have hdzbarF : ∀ z, dzbar F z = H z := by
    intro z
    have h1 : DifferentiableAt ℝ (fun w : ℂ => w) z := differentiableAt_id
    have h2 : DifferentiableAt ℝ (cauchyTransform H) z := hCH1.differentiable (by norm_num) z
    have h3 : dzbar (fun w : ℂ => w + cauchyTransform H w) z
        = dzbar (fun w : ℂ => w) z + H z := by
      rw [Work.MRMT.QC.dzbar_add_of_diff h1 h2, hdzbar_CH z]
    rw [show dzbar F z = dzbar (fun w : ℂ => w + cauchyTransform H w) z from rfl, h3]
    rw [show (fun w : ℂ => w) = (id : ℂ → ℂ) from rfl, dzbar_id]
    ring
  -- ## Step 3: the Beltrami equation, pointwise everywhere
  have hbelt : ∀ z, dzbar F z = μ z * dz F z := by
    intro z
    rw [hdzbarF z, hdzF z, congrFun hH_eq z]

  -- ## Step 4: Ahlfors' trick — `∂F` has no zero
  have hQ1 : ContDiff ℝ 1 Q := hQ2.of_le (by norm_num)
  have hμdiff : Differentiable ℝ μ := hμ.differentiable (by simp)
  have hCQ1 : ContDiff ℝ 1 (cauchyTransform Q) := (cauchyTransform_contDiff_one hQ1 hQcs).1
  have hdzbar_CQ : ∀ z, dzbar (cauchyTransform Q) z = Q z := (cauchyTransform_contDiff_one hQ1 hQcs).2.1
  have hdz_CQ : ∀ z, dz (cauchyTransform Q) z = cauchyTransform (dz Q) z :=
    (cauchyTransform_contDiff_one hQ1 hQcs).2.2
  have hCdQ1 : ContDiff ℝ 1 (cauchyTransform (dz Q)) :=
    (cauchyTransform_contDiff_one (contDiff_one_dz_ec hQ2) (hasCompactSupport_dz hQcs)).1
  have hQmem : MemLp Q 2 (volume : Measure ℂ) := hQ1.continuous.memLp_of_hasCompactSupport hQcs
  have hQ_eq_ae : Q =ᵐ[(volume : Measure ℂ)] fun z => dz μ z + μ z * cauchyTransform (dz Q) z := by
    have htoLpQ : hQmem.toLp Q = qL := by
      rw [MemLp.toLp_congr hQmem (Lp.memLp qL) hQae]
      exact Lp.toLp_coeFn qL (Lp.memLp qL)
    have hberQ := beurlingL2_eq_cauchyTransform_dz hQ1 hQcs hQmem
    rw [htoLpQ] at hberQ
    filter_upwards [hQae, hqL_eq, hberQ] with z h1 h2 h3
    rw [h1, h2, h3]
  have hQ_eq : Q = fun z => dz μ z + μ z * cauchyTransform (dz Q) z :=
    Measure.eq_of_ae_eq hQ_eq_ae hQ1.continuous
      (hdμcd.continuous.add (hμc.mul hCdQ1.continuous))
  -- (4a) `G = 1 + C(∂H)` and its Wirtinger derivatives
  have hG1 : ContDiff ℝ 1 (fun z => 1 + cauchyTransform (dz H) z) := contDiff_const.add hCdH1
  have hGd : ∀ z, DifferentiableAt ℝ (fun z => 1 + cauchyTransform (dz H) z) z :=
    fun z => hG1.differentiable (by norm_num) z
  have hdzG : ∀ z, dz (fun z => 1 + cauchyTransform (dz H) z) z = cauchyTransform (dz (dz H)) z := by
    intro z
    have h1 : DifferentiableAt ℝ (fun _ : ℂ => (1 : ℂ)) z := differentiableAt_const _
    have h2 : DifferentiableAt ℝ (cauchyTransform (dz H)) z := hCdH1.differentiable (by norm_num) z
    have h3 : dz (fun w : ℂ => (1 : ℂ) + cauchyTransform (dz H) w) z
        = cauchyTransform (fun w => dz (dz H) w) z := by
      rw [Work.MRMT.QC.dz_add_of_diff h1 h2, hdz_CdH z, dz_const''_ec]
      rw [zero_add]
    have h4 : (fun w : ℂ => dz (dz H) w) = dz (dz H) := rfl
    rw [show dz (fun z => 1 + cauchyTransform (dz H) z) z
      = dz (fun w : ℂ => (1 : ℂ) + cauchyTransform (dz H) w) z from rfl, h3, h4]
  have hdzbarG : ∀ z, dzbar (fun z => 1 + cauchyTransform (dz H) z) z = dz H z := by
    intro z
    have h1 : DifferentiableAt ℝ (fun _ : ℂ => (1 : ℂ)) z := differentiableAt_const _
    have h2 : DifferentiableAt ℝ (cauchyTransform (dz H)) z := hCdH1.differentiable (by norm_num) z
    have h3 : dzbar (fun w : ℂ => (1 : ℂ) + cauchyTransform (dz H) w) z = dz H z := by
      rw [Work.MRMT.QC.dzbar_add_of_diff h1 h2, hdzbar_CdH z, dzbar_const'_ec]
      rw [zero_add]
    rw [show dzbar (fun z => 1 + cauchyTransform (dz H) z) z
      = dzbar (fun w : ℂ => (1 : ℂ) + cauchyTransform (dz H) w) z from rfl, h3]
  -- (4b) `∂H = ∂μ · G + μ · ∂G` (from `H = μ G`)
  have hGH : ∀ z, dz H z = dz μ z * (1 + cauchyTransform (dz H) z)
      + μ z * cauchyTransform (dz (dz H)) z := by
    intro z
    have h1 : DifferentiableAt ℝ μ z := hμdiff.differentiableAt
    have h2 : DifferentiableAt ℝ (fun z => 1 + cauchyTransform (dz H) z) z := hGd z
    have h4 : dz H = dz (fun z => μ z * (1 + cauchyTransform (dz H) z)) := congrArg dz hH_eq
    rw [congrFun h4 z, Work.MRMT.QC.dz_mul h1 h2, hdzG z]
  -- (4c) the exponential `E = e^{-σ}` with `σ = C Q`
  have hsigma_eq : ∀ z, dzbar (cauchyTransform Q) z = dz μ z + μ z * dz (cauchyTransform Q) z := by
    intro z
    rw [hdzbar_CQ z, hdz_CQ z, congrFun hQ_eq z]
  have hE1 : ContDiff ℝ 1 (fun z => Complex.exp (-(cauchyTransform Q z))) := by
    have hneg : ContDiff ℝ 1 (fun z : ℂ => -(cauchyTransform Q z)) := hCQ1.neg
    exact hneg.cexp
  have hEd : ∀ z, DifferentiableAt ℝ (fun z => Complex.exp (-(cauchyTransform Q z))) z :=
    fun z => hE1.differentiable (by norm_num) z
  have hnegd : ∀ z, DifferentiableAt ℝ (fun z : ℂ => -(cauchyTransform Q z)) z :=
    fun z => (hCQ1.differentiable (by norm_num) z).neg
  have hE_dz : ∀ z, dz (fun z => Complex.exp (-(cauchyTransform Q z))) z
      = Complex.exp (-(cauchyTransform Q z)) * (-(cauchyTransform (dz Q) z)) := by
    intro z
    have hg : DifferentiableAt ℝ (fun w : ℂ => Complex.exp w) (-(cauchyTransform Q z)) :=
      (hasFDerivAt_exp_ec _).differentiableAt
    have hcomp := Work.MRMT.Wirtinger.dz_comp (f := fun z : ℂ => -(cauchyTransform Q z))
      (g := fun w : ℂ => Complex.exp w) hg (hnegd z)
    rw [show ((fun w : ℂ => Complex.exp w) ∘ (fun z : ℂ => -(cauchyTransform Q z)))
      = (fun z : ℂ => Complex.exp (-(cauchyTransform Q z))) from rfl] at hcomp
    rw [hcomp, dz_exp_ec, dzbar_exp_ec, dz_neg'_ec, dzbar_neg'_ec, hdz_CQ z, hdzbar_CQ z]
    ring
  have hE_dzbar : ∀ z, dzbar (fun z => Complex.exp (-(cauchyTransform Q z))) z
      = Complex.exp (-(cauchyTransform Q z)) * (-(dzbar (cauchyTransform Q) z)) := by
    intro z
    have hg : DifferentiableAt ℝ (fun w : ℂ => Complex.exp w) (-(cauchyTransform Q z)) :=
      (hasFDerivAt_exp_ec _).differentiableAt
    have hcomp := Work.MRMT.Wirtinger.dzbar_comp (f := fun z : ℂ => -(cauchyTransform Q z))
      (g := fun w : ℂ => Complex.exp w) hg (hnegd z)
    rw [show ((fun w : ℂ => Complex.exp w) ∘ (fun z : ℂ => -(cauchyTransform Q z)))
      = (fun z : ℂ => Complex.exp (-(cauchyTransform Q z))) from rfl] at hcomp
    rw [hcomp, dz_exp_ec, dzbar_exp_ec, dz_neg'_ec, dzbar_neg'_ec, hdz_CQ z, hdzbar_CQ z]
    ring
  -- (4d) `W = G · E` solves the homogeneous Beltrami equation
  let W : ℂ → ℂ := fun z => (1 + cauchyTransform (dz H) z) * Complex.exp (-(cauchyTransform Q z))
  have hWrel : ∀ z, dzbar W z = μ z * dz W z := by
    intro z
    have h1 := Work.MRMT.QC.dzbar_mul (hGd z) (hEd z)
    have h2 := Work.MRMT.QC.dz_mul (hGd z) (hEd z)
    have h1' : dzbar W z = dzbar (fun z => (1 + cauchyTransform (dz H) z)
        * Complex.exp (-(cauchyTransform Q z))) z := rfl
    have h2' : dz W z = dz (fun z => (1 + cauchyTransform (dz H) z)
        * Complex.exp (-(cauchyTransform Q z))) z := rfl
    rw [h1', h1, h2', h2, hdzbarG z, hdzG z, hE_dzbar z, hE_dz z, hGH z,
      hdzbar_CQ z, congrFun hQ_eq z]
    ring
  -- (4e) decay of `W - 1`
  have hWdecay : ∃ C R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖W z - 1‖ ≤ C / ‖z‖ := by
    obtain ⟨C₁, R₁, hC₁0, hCR₁⟩ := cauchyTransform_decay_of_contDiff_one hdzH1 hdzHcs
    obtain ⟨C₂, R₂, hC₂0, hCR₂⟩ := cauchyTransform_decay_of_contDiff_one hQ1 hQcs
    refine ⟨3 * C₁ + 2 * C₂ + 1, max R₁ (max R₂ (max (2 * C₂ + 1) 1)), fun z hz => ?_⟩
    have hz1 : R₁ ≤ ‖z‖ := (le_max_left _ _).trans hz
    have hz2 : R₂ ≤ ‖z‖ := (le_max_left _ _).trans ((le_max_right _ _).trans hz)
    have hz3 : 2 * C₂ + 1 ≤ ‖z‖ :=
      (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hz))
    have hz4 : (1 : ℝ) ≤ ‖z‖ :=
      (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hz))
    have hzpos : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one hz4
    have hGz : ‖1 + cauchyTransform (dz H) z - 1‖ ≤ C₁ / ‖z‖ := by
      simpa using (hCR₁ z hz1).1
    have hsig : ‖cauchyTransform Q z‖ ≤ C₂ / ‖z‖ := (hCR₂ z hz2).1
    have hsig1 : ‖-(cauchyTransform Q z)‖ ≤ 1 := by
      rw [norm_neg]
      refine hsig.trans ?_
      rw [div_le_one hzpos]
      linarith
    have hE1 : ‖Complex.exp (-(cauchyTransform Q z))‖ ≤ 3 := by
      rw [Complex.norm_exp]
      have h1 : (-(cauchyTransform Q z)).re ≤ ‖-(cauchyTransform Q z)‖ := Complex.re_le_norm _
      have h2 : Real.exp ((-(cauchyTransform Q z)).re) ≤ Real.exp 1 :=
        Real.exp_le_exp.mpr (h1.trans hsig1)
      linarith [Real.exp_one_lt_three]
    have hE2 : ‖Complex.exp (-(cauchyTransform Q z)) - 1‖ ≤ 2 * (C₂ / ‖z‖) := by
      refine (Complex.norm_exp_sub_one_le hsig1).trans ?_
      have h3 : 2 * ‖cauchyTransform Q z‖ ≤ 2 * (C₂ / ‖z‖) :=
        mul_le_mul_of_nonneg_left hsig (by norm_num)
      simpa using h3
    have hkey : (1 + cauchyTransform (dz H) z) * Complex.exp (-(cauchyTransform Q z)) - 1
        = ((1 + cauchyTransform (dz H) z) - 1) * Complex.exp (-(cauchyTransform Q z))
          + (Complex.exp (-(cauchyTransform Q z)) - 1) := by ring
    calc ‖W z - 1‖
        = ‖(1 + cauchyTransform (dz H) z) * Complex.exp (-(cauchyTransform Q z)) - 1‖ := rfl
      _ = ‖((1 + cauchyTransform (dz H) z) - 1) * Complex.exp (-(cauchyTransform Q z))
            + (Complex.exp (-(cauchyTransform Q z)) - 1)‖ := by rw [hkey]
      _ ≤ ‖((1 + cauchyTransform (dz H) z) - 1) * Complex.exp (-(cauchyTransform Q z))‖
            + ‖Complex.exp (-(cauchyTransform Q z)) - 1‖ := norm_add_le _ _
      _ = ‖(1 + cauchyTransform (dz H) z) - 1‖ * ‖Complex.exp (-(cauchyTransform Q z))‖
            + ‖Complex.exp (-(cauchyTransform Q z)) - 1‖ := by rw [norm_mul]
      _ ≤ (C₁ / ‖z‖) * 3 + 2 * (C₂ / ‖z‖) :=
          add_le_add (mul_le_mul hGz hE1 (norm_nonneg _) (by positivity)) hE2
      _ ≤ (3 * C₁ + 2 * C₂ + 1) / ‖z‖ := by
          rw [le_div_iff₀ hzpos]
          field_simp
          nlinarith [hz4, hC₁0, hC₂0]
  have hWzero : W = fun _ => 1 := by
    have hW1 : ContDiff ℝ 1 W := hG1.mul hE1
    have hsub : ContDiff ℝ 1 (fun z => W z - 1) := hW1.sub contDiff_const
    have hmain := Work.MRMT.QC.eq_zero_of_beltrami_of_decay_aux (h := fun z => W z - 1)
      (μ := μ) (k := k) hsub.continuous (hasW12LocOn_univ_of_contDiff_one_ec hsub) hk hbae
      (by filter_upwards with z
          rw [dz_sub_const'_ec, dzbar_sub_const'_ec]
          exact hWrel z)
      (by obtain ⟨C, R, hCR⟩ := hWdecay; exact ⟨C, R, fun z hz => by simpa using hCR z hz⟩)
    funext z
    exact sub_eq_zero.mp (congrFun hmain z)
  have hGne : ∀ z, 1 + cauchyTransform (dz H) z ≠ 0 := by
    intro z hz
    have h1 : W z = 1 := by rw [hWzero]
    have h2 : W z = 0 := by simp [W, hz]
    rw [h2] at h1
    exact one_ne_zero h1.symm
  have hdzFne : ∀ z, dz F z ≠ 0 := by
    intro z hz
    have h := hdzF z
    rw [hz] at h
    have := hGne z
    exact this h.symm

  -- ## Step 5: `F` is a homeomorphism and its inverse is `C¹`
  have hderiv : ∀ z : ℂ, ∃ f' : ℂ ≃L[ℝ] ℂ, (f' : ℂ →L[ℝ] ℂ) = fderiv ℝ F z := by
    intro z
    have hlt : ‖dzbar F z‖ < ‖dz F z‖ := by
      have hz : 0 < ‖dz F z‖ := norm_pos_iff.mpr (hdzFne z)
      calc ‖dzbar F z‖ = ‖μ z * dz F z‖ := by rw [← hbelt z]
        _ = ‖μ z‖ * ‖dz F z‖ := norm_mul _ _
        _ ≤ k * ‖dz F z‖ := mul_le_mul_of_nonneg_right (hb z) (norm_nonneg _)
        _ < 1 * ‖dz F z‖ := by
            exact mul_lt_mul_of_pos_right hk hz
        _ = ‖dz F z‖ := one_mul _
    exact exists_continuousLinearEquiv_of_dz_dzbar hlt (fderiv ℝ F z)
      (fun w => fderiv_apply_eq_dz_add_dzbar_star_ec F z w)
  have hd : ∀ z : ℂ, ∃ f' : ℂ ≃L[ℝ] ℂ, HasFDerivAt F (f' : ℂ →L[ℝ] ℂ) z := by
    intro z
    obtain ⟨f', hf'⟩ := hderiv z
    exact ⟨f', by rw [hf']; exact (hF1.differentiable one_ne_zero z).hasFDerivAt⟩
  have hli : ∀ z : ℂ, ∃ U : Set ℂ, U ∈ nhds z ∧ Set.InjOn F U := by
    intro z
    obtain ⟨f', hf'⟩ := hderiv z
    have hstrict : HasStrictFDerivAt F (f' : ℂ →L[ℝ] ℂ) z := by
      have h0 : HasStrictFDerivAt F (fderiv ℝ F z) z :=
        (hF1.contDiffAt).hasStrictFDerivAt (by norm_num)
      rw [hf']
      exact h0
    refine ⟨{x | HasStrictFDerivAt.localInverse F f' z hstrict (F x) = x},
      hstrict.eventually_left_inverse, ?_⟩
    intro x hx y hy hxy
    have hxy' : HasStrictFDerivAt.localInverse F f' z hstrict (F x)
        = HasStrictFDerivAt.localInverse F f' z hstrict (F y) := by rw [hxy]
    rw [hx] at hxy'
    rw [hy] at hxy'
    exact hxy'
  -- decay of `F - id = C H`
  have hCHdec : ∃ C R : ℝ, 0 ≤ C ∧ ∀ z : ℂ, R ≤ ‖z‖ →
      ‖cauchyTransform H z‖ ≤ C / ‖z‖ ∧ ‖fderiv ℝ (cauchyTransform H) z‖ ≤ C / ‖z‖ ^ 2 :=
    cauchyTransform_decay_of_contDiff_one hH1 hHcs
  have hFeq : ∀ z : ℂ, F z - z = cauchyTransform H z := fun z => by simp [F]
  have hFdec : ∃ C R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖F z - z‖ ≤ C / ‖z‖ := by
    obtain ⟨C, R, hC0, hCR⟩ := hCHdec
    exact ⟨C, R, fun z hz => by rw [hFeq z]; exact (hCR z hz).1⟩
  have hproper : IsProperMap F := by
    obtain ⟨C, R, hCR⟩ := hFdec
    refine isProperMap_of_growth_ec hFcont ⟨max (max R 1) (Real.sqrt (2 * C) + 1), fun z hz => ?_⟩
    have hR : R ≤ ‖z‖ := (le_max_left R 1).trans ((le_max_left _ _).trans hz)
    have h1 : ‖F z - z‖ ≤ C / ‖z‖ := hCR z hR
    have h2 : (1 : ℝ) ≤ ‖z‖ := (le_max_right R 1).trans ((le_max_left _ _).trans hz)
    have h3 : Real.sqrt (2 * C) + 1 ≤ ‖z‖ := (le_max_right _ _).trans hz
    have hpos : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one h2
    have key : C / ‖z‖ ≤ ‖z‖ / 2 := by
      by_cases hC : 0 ≤ C
      · have hsq : (Real.sqrt (2 * C)) ^ 2 = 2 * C := Real.sq_sqrt (by linarith)
        rw [div_le_div_iff₀ hpos (by norm_num : (0 : ℝ) < 2)]
        nlinarith [hsq, Real.sqrt_nonneg (2 * C), h3, sq_nonneg (‖z‖ - Real.sqrt (2 * C))]
      · have h4 : C / ‖z‖ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (le_of_lt (not_le.mp hC)) (norm_nonneg z)
        have h5 : (0 : ℝ) ≤ ‖z‖ / 2 := by positivity
        linarith
    have htri : ‖z‖ - ‖F z - z‖ ≤ ‖F z‖ := by
      have h := norm_sub_le (F z) (F z - z)
      have hz' : F z - (F z - z) = z := by ring
      rw [hz'] at h
      linarith
    linarith
  have hlip : ∃ R : ℝ, ∀ z₁ z₂ : ℂ, R ≤ ‖z₁‖ → R ≤ ‖z₂‖ →
      ‖(F z₁ - z₁) - (F z₂ - z₂)‖ ≤ (1 / 2) * ‖z₁ - z₂‖ := by
    obtain ⟨C, R, hC0, hCR⟩ := cauchyTransform_sub_le hH1 hHcs
    refine ⟨max (max R 1) (Real.sqrt (2 * C) + 1), fun z₁ z₂ h1 h2 => ?_⟩
    have hR1 : R ≤ ‖z₁‖ := (le_max_left R 1).trans ((le_max_left _ _).trans h1)
    have hR2 : R ≤ ‖z₂‖ := (le_max_left R 1).trans ((le_max_left _ _).trans h2)
    have hz1 : (1 : ℝ) ≤ ‖z₁‖ := (le_max_right R 1).trans ((le_max_left _ _).trans h1)
    have hz2 : (1 : ℝ) ≤ ‖z₂‖ := (le_max_right R 1).trans ((le_max_left _ _).trans h2)
    have hs1 : Real.sqrt (2 * C) + 1 ≤ ‖z₁‖ := (le_max_right _ _).trans h1
    have hs2 : Real.sqrt (2 * C) + 1 ≤ ‖z₂‖ := (le_max_right _ _).trans h2
    have hpos1 : 0 < ‖z₁‖ := lt_of_lt_of_le zero_lt_one hz1
    have hpos2 : 0 < ‖z₂‖ := lt_of_lt_of_le zero_lt_one hz2
    have hbound : 2 * C ≤ ‖z₁‖ * ‖z₂‖ := by
      by_cases hC : 0 ≤ C
      · have hsq : (Real.sqrt (2 * C)) ^ 2 = 2 * C := Real.sq_sqrt (by linarith)
        have hs1' : Real.sqrt (2 * C) ≤ ‖z₁‖ := by linarith
        have hs2' : Real.sqrt (2 * C) ≤ ‖z₂‖ := by linarith
        have hsq1 : 2 * C ≤ ‖z₁‖ ^ 2 := by
          rw [← hsq]
          exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hs1' 2
        have hsq2 : 2 * C ≤ ‖z₂‖ ^ 2 := by
          rw [← hsq]
          exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hs2' 2
        nlinarith [sq_nonneg (‖z₁‖ - ‖z₂‖), norm_nonneg z₁, norm_nonneg z₂]
      · have h2C : 2 * C ≤ 0 := by linarith [not_le.mp hC]
        nlinarith [norm_nonneg z₁, norm_nonneg z₂]
    have hkey : C * ‖z₁ - z₂‖ / (‖z₁‖ * ‖z₂‖) ≤ (1 / 2) * ‖z₁ - z₂‖ := by
      have hden : 0 < ‖z₁‖ * ‖z₂‖ := mul_pos hpos1 hpos2
      rw [div_le_iff₀ hden]
      nlinarith [norm_nonneg (z₁ - z₂), hbound]
    rw [hFeq z₁, hFeq z₂]
    exact (hCR z₁ z₂ hR1 hR2).trans hkey
  obtain ⟨φ, hφ⟩ : ∃ φ : ℂ ≃ₜ ℂ, (φ : ℂ → ℂ) = F :=
    exists_homeomorph_of_localInj_proper hFcont hli hproper hFdec hlip
  have hbij : Function.Bijective F := by
    rw [← hφ]; exact φ.bijective
  have hinv : ContDiff ℝ 1 (Function.invFun F) := contDiff_invFun_of_contDiff hF1 hbij hd
  have hsymm : ContDiff ℝ 1 ((φ.symm : ℂ → ℂ)) := by
    have hinv_eq : (φ.symm : ℂ → ℂ) = Function.invFun F := by
      funext b
      have h1 : F (Function.invFun F b) = b := Function.rightInverse_invFun hbij.2 b
      have h2 : F ((φ.symm : ℂ → ℂ) b) = b := by
        rw [← congrFun hφ ((φ.symm : ℂ → ℂ) b)]
        exact φ.apply_symm_apply b
      exact hbij.1 (h2.trans h1.symm)
    rw [hinv_eq]
    exact hinv
  exact ⟨φ, by rw [hφ]; exact hF1, hsymm, by rw [hφ]; exact hbelt, by rw [hφ]; exact hFdec⟩
end Work.MRMT.Found
