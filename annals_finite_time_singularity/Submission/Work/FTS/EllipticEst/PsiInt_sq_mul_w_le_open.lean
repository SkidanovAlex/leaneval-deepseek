/-
Copyright: work module for the Elgindi finite-time singularity project.

# Cauchy--Schwarz for the radial moment, open-quadrant version

This is the open-quadrant (`SmoothOpen`) analogue of
`Work.FTS.EllipticEst.PsiInt_sq_mul_w_le` of `Fstar_Hk_le`:

`(PsiInt u j z)² w(z)² ≤ (π/2) ∫_θ (D_z^j u(z,θ)·w(z)/sin(2θ)^{η/2})² dθ`

where `PsiInt u j z = ∫_θ D_z^j u(z,θ) sinθcos²θ dθ` is the `j`-th radial moment.

The only place where the smoothness hypothesis enters is the a.e. strong measurability of
the weighted angular slice of `D_z^j u`; the open-quadrant version of that fact is
`SmoothOpen.aesm_slice_summand`, which needs only continuity on the *open* quadrant (the
endpoints of `Iθ` are null).  Everything else is the closed-quadrant argument:
Cauchy--Schwarz against the weight
`V(θ) = sinθcos²θ·sin(2θ)^{η/2}/w(z)`, which is bounded by `1/w(z)` on `Iθ`, so that
`∫_θ V² ≤ (π/2)/w(z)²`.

The elementary angular facts used here are the same as those of `Fstar_Hk_le`, reproduced
locally (with private names) because importing `Fstar_Hk_le` alongside `OpenQDefs` is
impossible: both define `Work.FTS.EllipticEst.integrableOn_zSummand`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## The elementary angular facts (local copies) -/

/-- `sin(2θ) ≥ 0` on `Iθ = [0,π/2]`. -/
private theorem sin_two_nonneg_loc {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `sin(2θ) ≤ 1`. -/
private theorem sin_two_le_one_loc (θ : ℝ) : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _

/-- `|sinθ cos²θ| ≤ 1` on `Iθ`. -/
private theorem abs_sinCos2_le_one_loc {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Elliptic.sinCos2 θ| ≤ 1 := by
  have hsin : |Real.sin θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
  have hcos : |Real.cos θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  have hcos2 : Real.cos θ ^ 2 ≤ 1 := by
    have h := pow_le_pow_left₀ (abs_nonneg (Real.cos θ)) hcos 2
    rw [sq_abs] at h
    simpa using h
  have hcos2nn : 0 ≤ Real.cos θ ^ 2 := sq_nonneg _
  calc |Work.Elliptic.sinCos2 θ| = |Real.sin θ| * Real.cos θ ^ 2 := by
        rw [Work.Elliptic.sinCos2, abs_mul, abs_of_nonneg hcos2nn]
    _ ≤ 1 := by nlinarith [hsin, hcos2, abs_nonneg (Real.sin θ)]

/-- `sinθ cos²θ` vanishes wherever `sin 2θ` does. -/
private theorem sinCos2_eq_zero_of_sin_two_eq_zero_loc {θ : ℝ} (h : Real.sin (2 * θ) = 0) :
    Work.Elliptic.sinCos2 θ = 0 := by
  have h2 : Real.sin θ * Real.cos θ = 0 := by
    have h3 : 2 * (Real.sin θ * Real.cos θ) = 0 := by
      rw [← h, Real.sin_two_mul]; ring
    exact (mul_eq_zero.mp h3).resolve_left (by norm_num)
  rcases mul_eq_zero.mp h2 with h3 | h3
  · simp [Work.Elliptic.sinCos2, h3]
  · simp [Work.Elliptic.sinCos2, h3]

/-- A function on `Iθ` bounded by a constant is integrable there. -/
private theorem integrableOn_Iθ_of_abs_le_loc {f : ℝ → ℝ}
    (hm : AEStronglyMeasurable f (volume.restrict Work.Spaces.Iθ)) {C : ℝ}
    (h : ∀ θ ∈ Work.Spaces.Iθ, |f θ| ≤ C) : IntegrableOn f Work.Spaces.Iθ := by
  refine Integrable.mono'
    (MeasureTheory.integrableOn_const (s := Work.Spaces.Iθ) (C := C)
      (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)) hm ?_
  rw [Work.Spaces.Iθ, ae_restrict_iff' measurableSet_Icc]
  exact Eventually.of_forall fun θ hθ => by simpa [Real.norm_eq_abs] using h θ hθ

/-- The cross-term identity of Cauchy--Schwarz for the radial moment. -/
private theorem cs_cross_eq_loc (u : ℝ → ℝ → ℝ) (j : ℕ) {z : ℝ} (hz : 0 < z) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.DzIter j u z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      * (Work.Elliptic.sinCos2 θ * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        / Work.Spaces.w z)
    = Work.Spaces.DzIter j u z θ * Work.Elliptic.sinCos2 θ := by
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_loc hθ
  have hW : Work.Spaces.w z ≠ 0 := by
    rw [Work.Spaces.w]
    exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 hz.ne')
  have he : Work.Spaces.eta / 2 ≠ 0 := by rw [Work.Spaces.eta]; norm_num
  by_cases hs : Real.sin (2 * θ) = 0
  · have hc : Work.Elliptic.sinCos2 θ = 0 := sinCos2_eq_zero_of_sin_two_eq_zero_loc hs
    rw [hs, Real.zero_rpow he, div_zero, hc]
    ring
  · have hspos : 0 < Real.sin (2 * θ) := lt_of_le_of_ne hs0 (Ne.symm hs)
    have hne : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≠ 0 :=
      (Real.rpow_pos_of_pos hspos _).ne'
    field_simp

/-! ## Cauchy--Schwarz for the radial moment -/

/-- **Cauchy--Schwarz for the radial moment** (open-quadrant source).  The mass of the
radial moment `PsiInt u j z` is controlled by the `j`-th `L²`-summand of the `H^k`-integrand
of `u`. -/
theorem PsiInt_sq_mul_w_le_open (u : ℝ → ℝ → ℝ) (hu : Work.FTS.EllipticEst.SmoothOpen u) (j : ℕ) {z : ℝ}
    (hz : 0 < z)
    (hU : MeasureTheory.IntegrableOn (fun θ : ℝ => (Work.Spaces.DzIter j u z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) Work.Spaces.Iθ) :
    (Work.FTS.EllipticEst.PsiInt u j z) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ (Real.pi / 2) * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j u z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  have hz0 : (0 : ℝ) < z := hz
  have hIθ : MeasurableSet Work.Spaces.Iθ := by rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  have hWpos : 0 < Work.Spaces.w z := by
    rw [Work.Spaces.w]
    exact div_pos (pow_pos (by linarith) 2) (pow_pos hz0 2)
  set V : ℝ → ℝ := fun θ => Work.Elliptic.sinCos2 θ
    * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) / Work.Spaces.w z with hVdef
  have hUmem : MemLp (fun θ : ℝ => Work.Spaces.DzIter j u z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) 2
      (volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq
      (hu.aesm_slice_summand j hz0)).mpr hU
  have hVcont : Continuous V := by
    rw [hVdef]
    have h₁ : Continuous fun θ : ℝ => Work.Elliptic.sinCos2 θ := by
      unfold Work.Elliptic.sinCos2; fun_prop
    have h₂ : Continuous fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
      refine Continuous.rpow (by fun_prop) continuous_const (fun θ => Or.inr ?_)
      rw [Work.Spaces.eta]; norm_num
    exact (h₁.mul h₂).div_const _
  have hVabs : ∀ θ ∈ Work.Spaces.Iθ, |V θ| ≤ 1 / Work.Spaces.w z := by
    intro θ hθ
    have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_loc hθ
    have hpow1 : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
      Real.rpow_le_one hs0 (sin_two_le_one_loc θ) (by rw [Work.Spaces.eta]; norm_num)
    have habs : |Work.Elliptic.sinCos2 θ * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0 _)]
      calc |Work.Elliptic.sinCos2 θ| * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
          ≤ 1 * 1 := mul_le_mul (abs_sinCos2_le_one_loc hθ) hpow1
            (Real.rpow_nonneg hs0 _) zero_le_one
        _ = 1 := by ring
    rw [hVdef, abs_div, abs_of_pos hWpos]
    exact div_le_div_of_nonneg_right habs hWpos.le
  have hV2 : IntegrableOn (fun θ : ℝ => (V θ) ^ 2) Work.Spaces.Iθ := by
    refine integrableOn_Iθ_of_abs_le_loc (hVcont.aestronglyMeasurable.pow 2)
      (C := (1 / Work.Spaces.w z) ^ 2) ?_
    intro θ hθ
    rw [abs_of_nonneg (sq_nonneg _)]
    have h := pow_le_pow_left₀ (abs_nonneg (V θ)) (hVabs θ hθ) 2
    rwa [sq_abs] at h
  have hVmem : MemLp V 2 (volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hVcont.aestronglyMeasurable).mpr hV2
  have hcs := Work.Spaces.cs_integral hUmem hVmem
  have hcross : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j u z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) * V θ)
      = PsiInt u j z := by
    rw [PsiInt]
    exact setIntegral_congr_fun hIθ (fun θ hθ => by rw [hVdef]; exact cs_cross_eq_loc u j hz0 hθ)
  have hVb : ∫ θ in Work.Spaces.Iθ, (V θ) ^ 2 ≤ (Real.pi / 2) / (Work.Spaces.w z) ^ 2 := by
    have hconst : ∫ θ in Work.Spaces.Iθ, (1 / Work.Spaces.w z) ^ 2
        = (Real.pi / 2) / (Work.Spaces.w z) ^ 2 := by
      have hvol : volume.real Work.Spaces.Iθ = Real.pi / 2 := by
        rw [MeasureTheory.measureReal_def, Work.Spaces.Iθ, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
        ring
      rw [MeasureTheory.setIntegral_const, smul_eq_mul, hvol]
      ring
    rw [← hconst]
    refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _)
      (integrableOn_const (s := Work.Spaces.Iθ) (C := (1 / Work.Spaces.w z) ^ 2)
        (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)) ?_
    show ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), (V θ) ^ 2 ≤ (1 / Work.Spaces.w z) ^ 2
    rw [ae_restrict_iff' hIθ]
    exact Eventually.of_forall fun θ hθ => by
      have h := pow_le_pow_left₀ (abs_nonneg (V θ)) (hVabs θ hθ) 2
      rwa [sq_abs] at h
  have hA : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j u z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
    integral_nonneg fun θ => sq_nonneg _
  have hstep : (PsiInt u j z) ^ 2 ≤ (∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.DzIter j u z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      * ((Real.pi / 2) / (Work.Spaces.w z) ^ 2) := by
    rw [hcross] at hcs
    exact le_trans hcs (mul_le_mul_of_nonneg_left hVb hA)
  have hw2 : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 hWpos.ne'
  calc (PsiInt u j z) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j u z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          * ((Real.pi / 2) / (Work.Spaces.w z) ^ 2)) * (Work.Spaces.w z) ^ 2 :=
        mul_le_mul_of_nonneg_right hstep (sq_nonneg _)
    _ = (Real.pi / 2) * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j u z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        rw [mul_assoc, div_mul_cancel₀ (Real.pi / 2) hw2, mul_comm]

end Work.FTS.EllipticEst
