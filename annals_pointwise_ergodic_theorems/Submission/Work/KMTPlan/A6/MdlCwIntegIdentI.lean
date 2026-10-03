/-
# The `cw`-level integration-by-parts identity (i) of Krause--Mirek--Tao §6

This module proves `Work.KMTPlan.A6.MdlCwIntegIdentI`, the frequency-coefficient (`cw`) form of
the bump-level identity `Work.KMTPlan.A6.MdlBumpIntegIdentI` for the pair `(k₁, k₂) = (k₁, 0)`
with `k₁ ≥ 1`.

The proof is the (previously `private`) theorem `MdlCwIntegIdentI_aux` of
`Submission/Work/KMTPlan/A6/MdlKerIdentHighLow.lean`, reproduced here verbatim together with its
private auxiliary lemmas (`uph`, `vph`, `ampNeg1`, `ampPos1`, the factorisations
`varphiNt_val`/`varphitildeNt_val`/`ampNeg1_val`/`ampPos1_val`, the integrability lemmas
`integrable_ampNeg1`/`integrable_ampPos1`, and the `t`-integrability of the modified bumps): the
five quantities `E0, E1, E2, E3` of the frequency-level identity `MdlBumpIntegIdentI` are
identified with the five `cw`-products via `CwFubiniWeight` (weights `1` and `mdlW3 P N`) and
`MeasureTheory.integral_prod_mul` (endpoint products), the pointwise identity is applied on the
complement of the null set `{ξ₁ = 0}`, and the resulting double integrals are split using the
integrability supplied by `MarginalModInt` and the amplitude/phase lemmas above.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlBumpIntegIdentI
import Submission.Work.KMTPlan.A6.CwFubiniWeight
import Submission.Work.KMTPlan.A6.MarginalModInt
import Submission.Work.KMTPlan.A6.VarpModAmpInt
import Submission.Work.KMTPlan.A6.MdlWInt
import Submission.Work.KMTPlan.A6.varphiNtj_bounds
import Submission.Work.KMTPlan.A6.varphitildeNtj_bounds

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators Interval
open Work.KMTAreas.A7
open Work.Analysis.EndVar

/-! ## The amplitude/phase vocabulary of the modified bumps of the identity (i) -/

/-- The phase `t ↦ N t`. -/
private noncomputable def uph (N : ℕ) : ℝ → ℝ := fun t => (N : ℝ) * t

/-- The phase `t ↦ P(N t)`. -/
private noncomputable def vph (P : ℤ[X]) (N : ℕ) : ℝ → ℝ :=
  fun t => PevalR P ((N : ℝ) * t)

/-- The amplitude of the modified bump `φ_{N,t,-1}(ξ) = (2^{-k}Nξ)^{-1} φ_{N,t}(ξ)`. -/
private noncomputable def ampNeg1 (N k : ℕ) : ℝ → ℂ :=
  fun ξ => ((((2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * ξ : ℝ)) : ℂ)⁻¹ * varphiN N k ξ

/-- The amplitude of the modified bump `φ̃_{N,t,1}(ξ) = (N^d ξ) φ̃_{N,t}(ξ)` at `k₂ = 0`. -/
private noncomputable def ampPos1 (P : ℤ[X]) (N : ℕ) : ℝ → ℂ :=
  fun ξ => (((N : ℝ) ^ P.natDegree * ξ : ℝ) : ℂ) * varphitildeN P.natDegree N 0 ξ

/-! ## The factorisations of the modified bumps -/

private lemma varphiNt_val (N k : ℕ) (t ξ : ℝ) :
    varphiNt N k t ξ = varphiN N k ξ * ee (uph N t * ξ) := rfl

private lemma varphitildeNt_val (P : ℤ[X]) (d N k : ℕ) (t ξ : ℝ) :
    varphitildeNt P d N k t ξ = varphitildeN d N k ξ * ee (vph P N t * ξ) := rfl

private lemma ampNeg1_val (N k : ℕ) (t ξ : ℝ) :
    varphiNtj N k (-1) t ξ = ampNeg1 N k ξ * ee (uph N t * ξ) := by
  simp only [varphiNtj, varphiNt, ampNeg1, uph, zpow_neg_one]
  ring

private lemma ampPos1_val (P : ℤ[X]) (N : ℕ) (t ξ : ℝ) :
    varphitildeNtj P N 0 1 t ξ = ampPos1 P N ξ * ee (vph P N t * ξ) := by
  simp only [varphitildeNtj, varphitildeNt, ampPos1, vph, zpow_one]
  norm_num
  ring

/-! ## Integrability of the amplitudes -/

private lemma integrable_ee_mul {f : ℝ → ℂ} (hf : Integrable f) (c : ℝ) :
    Integrable (fun ξ : ℝ => ee (c * ξ) * f ξ) :=
  hf.bdd_mul (f := fun ξ : ℝ => ee (c * ξ)) (c := 1)
    (by simp only [ee]; fun_prop)
    (by filter_upwards with ξ; exact le_of_eq (Work.A7.ee_norm_char _))

private lemma integrable_ampPos1 (P : ℤ[X]) (N : ℕ) :
    Integrable (ampPos1 P N) ∧ Measurable (ampPos1 P N) := by
  have hcont : Continuous (ampPos1 P N) := by
    have h1 : Continuous (fun ξ : ℝ => (((N : ℝ) ^ P.natDegree * ξ : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)
    exact h1.mul (contDiff_varphitildeN P.natDegree N 0).continuous
  have hcs : HasCompactSupport (ampPos1 P N) :=
    HasCompactSupport.mul_left (f := fun ξ : ℝ => (((N : ℝ) ^ P.natDegree * ξ : ℝ) : ℂ))
      (hasCompactSupport_varphitildeN P.natDegree N 0)
  exact ⟨hcont.integrable_of_hasCompactSupport hcs, hcont.measurable⟩

private lemma integrable_ampNeg1 (N k : ℕ) (hk : 1 ≤ k) :
    Integrable (ampNeg1 N k) ∧ Measurable (ampNeg1 N k) := by
  classical
  have hk0 : k ≠ 0 := by omega
  rcases Nat.eq_zero_or_pos N with hN0 | hN1
  · subst hN0
    have hzero : ampNeg1 0 k = fun _ : ℝ => (0 : ℂ) := by
      funext ξ
      simp only [ampNeg1]
      have hcast : ((((2 : ℝ) ^ (-(k : ℝ)) * ((0 : ℕ) : ℝ) * ξ : ℝ)) : ℂ) = 0 := by
        norm_num
      rw [hcast, inv_zero, zero_mul]
    rw [hzero]
    refine ⟨?_, measurable_const⟩
    simpa using (integrable_zero : Integrable (fun _ : ℝ => (0 : ℂ)) volume)
  · have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    have hcpos : (0 : ℝ) < (2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) :=
      mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hNpos
    have hmeas : Measurable (ampNeg1 N k) := by
      have h1 : Measurable (fun ξ : ℝ =>
          ((((2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * ξ : ℝ)) : ℂ)⁻¹) :=
        (Complex.continuous_ofReal.measurable.comp (measurable_const.mul measurable_id)).inv
      exact h1.mul (Work.A7.varphiN_integrable_measurable N k).2
    set δ : ℝ := (1 / 4) * (2 : ℝ) ^ ((k : ℝ) - (logN N : ℝ)) with hδ
    have hδpos : 0 < δ := by rw [hδ]; positivity
    have hprod : (2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ))
        * (2 : ℝ) ^ ((k : ℝ) - (logN N : ℝ)) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      have h : (logN N : ℝ) - (k : ℝ) + ((k : ℝ) - (logN N : ℝ)) = 0 := by ring
      rw [h, Real.rpow_zero]
    have hmul : (2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ)) * δ = 1 / 4 := by
      rw [hδ]
      calc (2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ))
              * ((1 / 4) * (2 : ℝ) ^ ((k : ℝ) - (logN N : ℝ)))
          = ((2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ))
              * (2 : ℝ) ^ ((k : ℝ) - (logN N : ℝ))) * (1 / 4) := by ring
        _ = 1 * (1 / 4) := by rw [hprod]
        _ = 1 / 4 := by ring
    -- `φ_N` vanishes on `|ξ| < δ`
    have hφzero : ∀ ξ : ℝ, |ξ| < δ → varphiN N k ξ = 0 := by
      intro ξ hξ
      have hc : (0 : ℝ) < (2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ)) :=
        Real.rpow_pos_of_pos (by norm_num) _
      have h1 : |(2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ)) * ξ| ≤ 1 / 2 := by
        rw [abs_mul, abs_of_pos hc]
        calc (2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ)) * |ξ|
            ≤ (2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ)) * δ :=
              le_of_lt (mul_lt_mul_of_pos_left hξ hc)
          _ = 1 / 4 := hmul
          _ ≤ 1 / 2 := by norm_num
      have h2 : |(2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ) + 1) * ξ| ≤ 1 / 2 := by
        rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)]
        have hsplit : (2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ) + 1)
            = 2 * (2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ)) := by
          rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
          ring
        rw [hsplit]
        calc 2 * (2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ)) * |ξ|
            ≤ 2 * ((2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ)) * δ) := by
              have h := mul_lt_mul_of_pos_left hξ hc
              linarith
          _ = 2 * (1 / 4) := by rw [hmul]
          _ ≤ 1 / 2 := by norm_num
      rw [varphiN, if_neg hk0]
      show Work.KMTContract.kmtEta (((2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ))) * ξ)
          - Work.KMTContract.kmtEta (((2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ) + 1)) * ξ) = 0
      rw [Work.KMTContract.kmtEta_one h1, Work.KMTContract.kmtEta_one h2, sub_self]
    -- the modulus bound `‖φ_N‖ ≤ 2`
    have hφbd : ∀ ξ : ℝ, ‖varphiN N k ξ‖ ≤ 2 := by
      intro ξ
      by_cases hkk : k = 0
      · rw [varphiN, if_pos hkk]
        exact le_trans (Work.KMTContract.norm_kmtEta_le _) (by norm_num)
      · rw [varphiN, if_neg hkk]
        have h1 := Work.KMTContract.norm_kmtEta_le (((2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ))) * ξ)
        have h2 := Work.KMTContract.norm_kmtEta_le
          (((2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ) + 1)) * ξ)
        calc ‖Work.KMTContract.kmtEta (((2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ))) * ξ)
                - Work.KMTContract.kmtEta (((2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ) + 1)) * ξ)‖
              ≤ ‖Work.KMTContract.kmtEta (((2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ))) * ξ)‖
                + ‖Work.KMTContract.kmtEta (((2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ) + 1)) * ξ)‖ :=
              norm_sub_le _ _
          _ ≤ 2 := by linarith
    -- pointwise domination by a constant times `‖φ_N‖`
    have hbd : ∀ ξ : ℝ, ‖ampNeg1 N k ξ‖
        ≤ ((2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * δ)⁻¹ * ‖varphiN N k ξ‖ := by
      intro ξ
      by_cases hsmall : |ξ| < δ
      · have hz : ampNeg1 N k ξ = 0 := by rw [ampNeg1, hφzero ξ hsmall, mul_zero]
        rw [hz, norm_zero]
        exact mul_nonneg (inv_nonneg.mpr (by positivity)) (norm_nonneg _)
      · have hδξ : δ ≤ |ξ| := not_lt.mp hsmall
        have hnorm : ‖ampNeg1 N k ξ‖
            = ((2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * |ξ|)⁻¹ * ‖varphiN N k ξ‖ := by
          rw [ampNeg1, norm_mul, norm_inv]
          have h1 : ‖((((2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * ξ : ℝ)) : ℂ)‖
              = |(((2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * ξ : ℝ))| := Complex.norm_real _
          rw [h1, abs_mul, abs_of_pos hcpos]
        rw [hnorm]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [← one_div, ← one_div]
        refine one_div_le_one_div_of_le
          (mul_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hNpos) hδpos) ?_
        exact mul_le_mul_of_nonneg_left hδξ
          (le_of_lt (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hNpos))
    refine ⟨?_, hmeas⟩
    exact (((Work.A7.varphiN_integrable_measurable N k).1.norm).const_mul _).mono'
      hmeas.aestronglyMeasurable (Eventually.of_forall fun ξ => hbd ξ)

/-! ## The `cw`-level identity and the integrability of the modified bumps -/

private lemma cw_varphiNtj_neg1 (N k : ℕ) (t : ℝ) (j : ℤ) :
    cw (varphiNtj N k (-1) t) j = cw (fun ξ => ampNeg1 N k ξ * ee (uph N t * ξ)) j := by
  congr 1
  funext ξ
  exact ampNeg1_val N k t ξ

private lemma cw_varphitildeNtj_zero_one (P : ℤ[X]) (N : ℕ) (t : ℝ) (j : ℤ) :
    cw (varphitildeNtj P N 0 1 t) j
      = cw (fun ξ => ampPos1 P N ξ * ee (vph P N t * ξ)) j := by
  congr 1
  funext ξ
  exact ampPos1_val P N t ξ

private lemma integrable_varphiNtj_neg1 (N k : ℕ) (hk : 1 ≤ k) (t : ℝ) :
    Integrable (varphiNtj N k (-1) t) :=
  (integrable_ee_mul (integrable_ampNeg1 N k hk).1 (uph N t)).congr
    (Eventually.of_forall fun ξ => by rw [ampNeg1_val]; ring)

private lemma integrable_varphitildeNtj_zero_one (P : ℤ[X]) (N : ℕ) (t : ℝ) :
    Integrable (varphitildeNtj P N 0 1 t) :=
  (integrable_ee_mul (integrable_ampPos1 P N).1 (vph P N t)).congr
    (Eventually.of_forall fun ξ => by rw [ampPos1_val]; ring)

/-- **The `cw`-level form of the integration-by-parts identity (i) at `(k₁ ≥ 1, k₂ = 0)`.** -/
private theorem MdlCwIntegIdentI_aux (P : ℤ[X]) (N k₁ : ℕ) (hN : 1 ≤ N) (hk₁ : 1 ≤ k₁)
    (i₁ i₂ : ℤ) :
    (∫ t in (1 / 2 : ℝ)..1,
        cw (varphiNt N k₁ t) i₁ * cw (varphitildeNt P P.natDegree N 0 t) i₂)
      = (mdlScaleF k₁ : ℂ) * mdlIota
          * (cw (varphiNtj N k₁ (-1) 1) i₁
              * cw (varphitildeNt P P.natDegree N 0 1) i₂
            - cw (varphiNtj N k₁ (-1) (1 / 2)) i₁
              * cw (varphitildeNt P P.natDegree N 0 (1 / 2)) i₂)
        - (mdlScaleFG P k₁ 0 : ℂ)
            * (∫ t in (1 / 2 : ℝ)..1,
                mdlW3 P N t * (cw (varphiNtj N k₁ (-1) t) i₁
                  * cw (varphitildeNtj P N 0 1 t) i₂)) := by
  classical
  set AV : ℝ → ℂ := varphiN N k₁ with hAV
  set AM : ℝ → ℂ := ampNeg1 N k₁ with hAM
  set BV : ℝ → ℂ := varphitildeN P.natDegree N 0 with hBV
  set BM : ℝ → ℂ := ampPos1 P N with hBM
  set U : ℝ → ℝ := uph N with hU
  set V : ℝ → ℝ := vph P N with hV
  set c0 : ℂ := (mdlScaleF k₁ : ℂ) * mdlIota with hc0
  set c1 : ℂ := (mdlScaleFG P k₁ 0 : ℂ) with hc1
  set L0 : ℂ := ∫ t in (1 / 2 : ℝ)..1,
      cw (varphiNt N k₁ t) i₁ * cw (varphitildeNt P P.natDegree N 0 t) i₂ with hL0d
  set L1 : ℂ := cw (varphiNtj N k₁ (-1) 1) i₁
      * cw (varphitildeNt P P.natDegree N 0 1) i₂ with hL1d
  set L2 : ℂ := cw (varphiNtj N k₁ (-1) (1 / 2)) i₁
      * cw (varphitildeNt P P.natDegree N 0 (1 / 2)) i₂ with hL2d
  set L3 : ℂ := ∫ t in (1 / 2 : ℝ)..1,
      mdlW3 P N t * (cw (varphiNtj N k₁ (-1) t) i₁
        * cw (varphitildeNtj P N 0 1 t) i₂) with hL3d
  set E0 : ℝ × ℝ → ℂ := fun z => ee (-(i₁ : ℝ) * z.1 - (i₂ : ℝ) * z.2) *
      ∫ t in (1 / 2 : ℝ)..1, (AV z.1 * ee (U t * z.1)) * (BV z.2 * ee (V t * z.2)) with hEd0
  set E1 : ℝ × ℝ → ℂ := fun z => ee (-(i₁ : ℝ) * z.1 - (i₂ : ℝ) * z.2) *
      (varphiNtj N k₁ (-1) 1 z.1 * varphitildeNt P P.natDegree N 0 1 z.2) with hEd1
  set E2 : ℝ × ℝ → ℂ := fun z => ee (-(i₁ : ℝ) * z.1 - (i₂ : ℝ) * z.2) *
      (varphiNtj N k₁ (-1) (1 / 2) z.1
        * varphitildeNt P P.natDegree N 0 (1 / 2) z.2) with hEd2
  set E3 : ℝ × ℝ → ℂ := fun z => ee (-(i₁ : ℝ) * z.1 - (i₂ : ℝ) * z.2) *
      ∫ t in (1 / 2 : ℝ)..1,
        mdlW3 P N t * ((AM z.1 * ee (U t * z.1)) * (BM z.2 * ee (V t * z.2))) with hEd3
  -- integrability data
  have hAVi : Integrable AV := by
    rw [hAV]; exact (Work.A7.varphiN_integrable_measurable N k₁).1
  have hAVm : Measurable AV := by
    rw [hAV]; exact (Work.A7.varphiN_integrable_measurable N k₁).2
  have hBVi : Integrable BV := by
    rw [hBV]; exact (Work.A7.varphitildeN_integrable_measurable P.natDegree N 0).1
  have hBVm : Measurable BV := by
    rw [hBV]; exact (Work.A7.varphitildeN_integrable_measurable P.natDegree N 0).2
  have hAMi : Integrable AM := by rw [hAM]; exact (integrable_ampNeg1 N k₁ hk₁).1
  have hAMm : Measurable AM := by rw [hAM]; exact (integrable_ampNeg1 N k₁ hk₁).2
  have hBMi : Integrable BM := by rw [hBM]; exact (integrable_ampPos1 P N).1
  have hBMm : Measurable BM := by rw [hBM]; exact (integrable_ampPos1 P N).2
  have hum : Measurable U := by
    have h : U = fun t : ℝ => (N : ℝ) * t := by rw [hU]; rfl
    rw [h]; exact measurable_const.mul measurable_id
  have hvm : Measurable V := by
    have hP : Measurable (PevalR P) := by unfold PevalR; fun_prop
    have h : V = fun t : ℝ => PevalR P ((N : ℝ) * t) := by rw [hV]; rfl
    rw [h]; exact hP.comp (measurable_const.mul measurable_id)
  have h1i : Integrable (fun _ : ℝ => (1 : ℂ)) (volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) := by
    haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) :=
      ⟨by rw [MeasureTheory.Measure.restrict_apply_univ]; simp [Real.volume_Ioc]⟩
    exact MeasureTheory.integrable_const 1
  have hW3i : Integrable (mdlW3 P N) (volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) := by
    have hle : (1 / 2 : ℝ) ≤ 1 := by norm_num
    have hcont : Continuous (mdlW3 P N) := by
      unfold mdlW3
      exact Complex.continuous_ofReal.comp ((continuous_PderivR_comp P (N : ℝ)).div_const _)
    have hw : ContinuousOn (mdlW3 P N) (Set.uIcc (1 / 2 : ℝ) 1) := hcont.continuousOn
    change IntegrableOn (mdlW3 P N) (Set.Ioc (1 / 2 : ℝ) 1) volume
    rw [← Set.uIoc_of_le hle]
    exact intervalIntegrable_iff.mp (hw.intervalIntegrable)
  have hW3m : Measurable (mdlW3 P N) := by
    unfold mdlW3
    exact Complex.continuous_ofReal.measurable.comp
      ((continuous_PderivR_comp P (N : ℝ)).div_const _).measurable
  -- integrability of the four integrands
  have hE0marg : Integrable (fun z : ℝ × ℝ => ∫ t in (1 / 2 : ℝ)..1,
      (fun _ : ℝ => (1 : ℂ)) t * (AV z.1 * ee (U t * z.1))
        * (BV z.2 * ee (V t * z.2))) (volume.prod volume) :=
    MarginalModInt hAVi hBVi hAVm hBVm hum hvm (W := fun _ : ℝ => (1 : ℂ)) h1i measurable_const
  have hE0marg' : Integrable (fun z : ℝ × ℝ => ∫ t in (1 / 2 : ℝ)..1,
      (AV z.1 * ee (U t * z.1)) * (BV z.2 * ee (V t * z.2))) (volume.prod volume) := by
    refine hE0marg.congr (Eventually.of_forall fun z => ?_)
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [Pi.one_apply, one_mul]
  have hE0i : Integrable E0 (volume.prod volume) := by
    simp only [hEd0]
    exact hE0marg'.bdd_mul (f := fun z : ℝ × ℝ => ee (-(i₁ : ℝ) * z.1 - (i₂ : ℝ) * z.2))
      (c := 1) (by simp only [ee]; fun_prop)
      (by filter_upwards with z; exact le_of_eq (Work.A7.ee_norm_char _))
  have hE3marg : Integrable (fun z : ℝ × ℝ => ∫ t in (1 / 2 : ℝ)..1,
      mdlW3 P N t * (AM z.1 * ee (U t * z.1)) * (BM z.2 * ee (V t * z.2)))
      (volume.prod volume) :=
    MarginalModInt hAMi hBMi hAMm hBMm hum hvm hW3i hW3m
  have hE3marg' : Integrable (fun z : ℝ × ℝ => ∫ t in (1 / 2 : ℝ)..1,
      mdlW3 P N t * ((AM z.1 * ee (U t * z.1)) * (BM z.2 * ee (V t * z.2))))
      (volume.prod volume) := by
    refine hE3marg.congr (Eventually.of_forall fun z => ?_)
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring
  have hE3i : Integrable E3 (volume.prod volume) := by
    simp only [hEd3]
    exact hE3marg'.bdd_mul (f := fun z : ℝ × ℝ => ee (-(i₁ : ℝ) * z.1 - (i₂ : ℝ) * z.2))
      (c := 1) (by simp only [ee]; fun_prop)
      (by filter_upwards with z; exact le_of_eq (Work.A7.ee_norm_char _))
  have hE1f : Integrable (fun ξ : ℝ => ee (-(i₁ : ℝ) * ξ) * (varphiNtj N k₁ (-1) 1 ξ)) :=
    integrable_ee_mul (integrable_varphiNtj_neg1 N k₁ hk₁ 1) (-(i₁ : ℝ))
  have hE1g : Integrable (fun ξ : ℝ => ee (-(i₂ : ℝ) * ξ)
      * (varphitildeNt P P.natDegree N 0 1 ξ)) :=
    integrable_ee_mul (integrable_varphitildeNt_aux P P.natDegree N 0 1) (-(i₂ : ℝ))
  have hE2f : Integrable (fun ξ : ℝ => ee (-(i₁ : ℝ) * ξ)
      * (varphiNtj N k₁ (-1) (1 / 2) ξ)) :=
    integrable_ee_mul (integrable_varphiNtj_neg1 N k₁ hk₁ (1 / 2)) (-(i₁ : ℝ))
  have hE2g : Integrable (fun ξ : ℝ => ee (-(i₂ : ℝ) * ξ)
      * (varphitildeNt P P.natDegree N 0 (1 / 2) ξ)) :=
    integrable_ee_mul (integrable_varphitildeNt_aux P P.natDegree N 0 (1 / 2)) (-(i₂ : ℝ))
  have hE1i : Integrable E1 (volume.prod volume) := by
    simp only [hEd1]
    refine (hE1f.mul_prod hE1g).congr (Eventually.of_forall fun z => ?_)
    show ee (-(i₁ : ℝ) * z.1) * varphiNtj N k₁ (-1) 1 z.1
          * (ee (-(i₂ : ℝ) * z.2) * varphitildeNt P P.natDegree N 0 1 z.2)
        = ee (-(i₁ : ℝ) * z.1 - (i₂ : ℝ) * z.2)
          * (varphiNtj N k₁ (-1) 1 z.1 * varphitildeNt P P.natDegree N 0 1 z.2)
    rw [show -(i₁ : ℝ) * z.1 - (i₂ : ℝ) * z.2
          = (-(i₁ : ℝ) * z.1) + (-(i₂ : ℝ) * z.2) from by ring, Work.A7.ee_add_char]
    ring
  have hE2i : Integrable E2 (volume.prod volume) := by
    simp only [hEd2]
    refine (hE2f.mul_prod hE2g).congr (Eventually.of_forall fun z => ?_)
    show ee (-(i₁ : ℝ) * z.1) * varphiNtj N k₁ (-1) (1 / 2) z.1
          * (ee (-(i₂ : ℝ) * z.2) * varphitildeNt P P.natDegree N 0 (1 / 2) z.2)
        = ee (-(i₁ : ℝ) * z.1 - (i₂ : ℝ) * z.2)
          * (varphiNtj N k₁ (-1) (1 / 2) z.1
            * varphitildeNt P P.natDegree N 0 (1 / 2) z.2)
    rw [show -(i₁ : ℝ) * z.1 - (i₂ : ℝ) * z.2
          = (-(i₁ : ℝ) * z.1) + (-(i₂ : ℝ) * z.2) from by ring, Work.A7.ee_add_char]
    ring
  -- the two product formulas of the endpoint terms
  have hprod1 : (∫ z : ℝ × ℝ, (ee (-(i₁ : ℝ) * z.1) * (varphiNtj N k₁ (-1) 1 z.1))
        * (ee (-(i₂ : ℝ) * z.2) * (varphitildeNt P P.natDegree N 0 1 z.2)))
      = cw (varphiNtj N k₁ (-1) 1) i₁ * cw (varphitildeNt P P.natDegree N 0 1) i₂ := by
    have hf : (∫ ξ : ℝ, ee (-(i₁ : ℝ) * ξ) * (varphiNtj N k₁ (-1) 1 ξ))
        = cw (varphiNtj N k₁ (-1) 1) i₁ := by
      simp only [cw]
      congr 1
      funext ξ
      ring
    have hg : (∫ ξ : ℝ, ee (-(i₂ : ℝ) * ξ) * (varphitildeNt P P.natDegree N 0 1 ξ))
        = cw (varphitildeNt P P.natDegree N 0 1) i₂ := by
      simp only [cw]
      congr 1
      funext ξ
      ring
    rw [← hf, ← hg]
    exact MeasureTheory.integral_prod_mul
      (f := fun ξ : ℝ => ee (-(i₁ : ℝ) * ξ) * (varphiNtj N k₁ (-1) 1 ξ))
      (g := fun ξ : ℝ => ee (-(i₂ : ℝ) * ξ) * (varphitildeNt P P.natDegree N 0 1 ξ))
  have hprod2 : (∫ z : ℝ × ℝ, (ee (-(i₁ : ℝ) * z.1) * (varphiNtj N k₁ (-1) (1 / 2) z.1))
        * (ee (-(i₂ : ℝ) * z.2) * (varphitildeNt P P.natDegree N 0 (1 / 2) z.2)))
      = cw (varphiNtj N k₁ (-1) (1 / 2)) i₁
        * cw (varphitildeNt P P.natDegree N 0 (1 / 2)) i₂ := by
    have hf : (∫ ξ : ℝ, ee (-(i₁ : ℝ) * ξ) * (varphiNtj N k₁ (-1) (1 / 2) ξ))
        = cw (varphiNtj N k₁ (-1) (1 / 2)) i₁ := by
      simp only [cw]
      congr 1
      funext ξ
      ring
    have hg : (∫ ξ : ℝ, ee (-(i₂ : ℝ) * ξ) * (varphitildeNt P P.natDegree N 0 (1 / 2) ξ))
        = cw (varphitildeNt P P.natDegree N 0 (1 / 2)) i₂ := by
      simp only [cw]
      congr 1
      funext ξ
      ring
    rw [← hf, ← hg]
    exact MeasureTheory.integral_prod_mul
      (f := fun ξ : ℝ => ee (-(i₁ : ℝ) * ξ) * (varphiNtj N k₁ (-1) (1 / 2) ξ))
      (g := fun ξ : ℝ => ee (-(i₂ : ℝ) * ξ) * (varphitildeNt P P.natDegree N 0 (1 / 2) ξ))
  -- the four double-integral representations
  have hLp0 : L0 = ∫ z : ℝ × ℝ, E0 z ∂(volume.prod volume) := by
    have hFub := CwFubiniWeight (a := AV) (b := BV) hAVi hBVi hAVm hBVm (u := U) (v := V)
      hum hvm (W := fun _ : ℝ => (1 : ℂ)) h1i measurable_const i₁ i₂
    have hset : L0 = ∫ t in (1 / 2 : ℝ)..1, (fun _ : ℝ => (1 : ℂ)) t
        * cw (fun ξ => AV ξ * ee (U t * ξ)) i₁
        * cw (fun ξ => BV ξ * ee (V t * ξ)) i₂ := by
      rw [hL0d]
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [show cw (varphiNt N k₁ t) i₁ = cw (fun ξ => AV ξ * ee (U t * ξ)) i₁ from by
            rw [hAV, hU]; rfl,
          show cw (varphitildeNt P P.natDegree N 0 t) i₂
              = cw (fun ξ => BV ξ * ee (V t * ξ)) i₂ from by rw [hBV, hV]; rfl]
      ring
    have hinner0 : ∀ ξ₁ ξ₂ : ℝ,
        (∫ t in (1 / 2 : ℝ)..1, (AV ξ₁ * ee (U t * ξ₁)) * (BV ξ₂ * ee (V t * ξ₂)))
          = AV ξ₁ * BV ξ₂
            * (∫ t in (1 / 2 : ℝ)..1,
                (fun _ : ℝ => (1 : ℂ)) t * ee (U t * ξ₁ + V t * ξ₂)) := by
      intro ξ₁ ξ₂
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [Pi.one_apply, one_mul]
      rw [Work.A7.ee_add_char]
      ring
    have hpt : ∀ ξ₁ ξ₂ : ℝ, AV ξ₁ * BV ξ₂
        * (∫ t in (1 / 2 : ℝ)..1, (fun _ : ℝ => (1 : ℂ)) t * ee (U t * ξ₁ + V t * ξ₂))
        * ee (-(i₁ : ℝ) * ξ₁ - (i₂ : ℝ) * ξ₂) = E0 (ξ₁, ξ₂) := by
      intro ξ₁ ξ₂
      simp only [hEd0]
      rw [← hinner0 ξ₁ ξ₂]
      ring
    rw [hset, hFub]
    refine Eq.trans ?_ (MeasureTheory.integral_prod E0 hE0i).symm
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun ξ₁ => ?_)
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun ξ₂ => ?_)
    exact hpt ξ₁ ξ₂
  have hLp1 : L1 = ∫ z : ℝ × ℝ, E1 z ∂(volume.prod volume) := by
    have hset : (∫ z : ℝ × ℝ, E1 z) = ∫ z : ℝ × ℝ,
        (ee (-(i₁ : ℝ) * z.1) * (varphiNtj N k₁ (-1) 1 z.1))
          * (ee (-(i₂ : ℝ) * z.2) * (varphitildeNt P P.natDegree N 0 1 z.2)) := by
      refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [hEd1]
      show ee (-(i₁ : ℝ) * z.1 - (i₂ : ℝ) * z.2)
            * (varphiNtj N k₁ (-1) 1 z.1 * varphitildeNt P P.natDegree N 0 1 z.2)
          = (ee (-(i₁ : ℝ) * z.1) * (varphiNtj N k₁ (-1) 1 z.1))
            * (ee (-(i₂ : ℝ) * z.2) * (varphitildeNt P P.natDegree N 0 1 z.2))
      rw [show -(i₁ : ℝ) * z.1 - (i₂ : ℝ) * z.2
            = (-(i₁ : ℝ) * z.1) + (-(i₂ : ℝ) * z.2) from by ring, Work.A7.ee_add_char]
      ring
    rw [hL1d, ← hprod1]
    exact hset.symm
  have hLp2 : L2 = ∫ z : ℝ × ℝ, E2 z ∂(volume.prod volume) := by
    have hset : (∫ z : ℝ × ℝ, E2 z) = ∫ z : ℝ × ℝ,
        (ee (-(i₁ : ℝ) * z.1) * (varphiNtj N k₁ (-1) (1 / 2) z.1))
          * (ee (-(i₂ : ℝ) * z.2) * (varphitildeNt P P.natDegree N 0 (1 / 2) z.2)) := by
      refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [hEd2]
      show ee (-(i₁ : ℝ) * z.1 - (i₂ : ℝ) * z.2)
            * (varphiNtj N k₁ (-1) (1 / 2) z.1
              * varphitildeNt P P.natDegree N 0 (1 / 2) z.2)
          = (ee (-(i₁ : ℝ) * z.1) * (varphiNtj N k₁ (-1) (1 / 2) z.1))
            * (ee (-(i₂ : ℝ) * z.2) * (varphitildeNt P P.natDegree N 0 (1 / 2) z.2))
      rw [show -(i₁ : ℝ) * z.1 - (i₂ : ℝ) * z.2
            = (-(i₁ : ℝ) * z.1) + (-(i₂ : ℝ) * z.2) from by ring, Work.A7.ee_add_char]
      ring
    rw [hL2d, ← hprod2]
    exact hset.symm
  have hLp3 : L3 = ∫ z : ℝ × ℝ, E3 z ∂(volume.prod volume) := by
    have hFub := CwFubiniWeight (a := AM) (b := BM) hAMi hBMi hAMm hBMm (u := U) (v := V)
      hum hvm (W := mdlW3 P N) hW3i hW3m i₁ i₂
    have hset : L3 = ∫ t in (1 / 2 : ℝ)..1, mdlW3 P N t
        * cw (fun ξ => AM ξ * ee (U t * ξ)) i₁
        * cw (fun ξ => BM ξ * ee (V t * ξ)) i₂ := by
      rw [hL3d]
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [cw_varphiNtj_neg1 N k₁ t i₁, cw_varphitildeNtj_zero_one P N t i₂]
      ring
    have hinner3 : ∀ ξ₁ ξ₂ : ℝ,
        (∫ t in (1 / 2 : ℝ)..1,
            mdlW3 P N t * ((AM ξ₁ * ee (U t * ξ₁)) * (BM ξ₂ * ee (V t * ξ₂))))
          = AM ξ₁ * BM ξ₂
            * (∫ t in (1 / 2 : ℝ)..1, mdlW3 P N t * ee (U t * ξ₁ + V t * ξ₂)) := by
      intro ξ₁ ξ₂
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [Work.A7.ee_add_char]
      ring
    have hpt : ∀ ξ₁ ξ₂ : ℝ, AM ξ₁ * BM ξ₂
        * (∫ t in (1 / 2 : ℝ)..1, mdlW3 P N t * ee (U t * ξ₁ + V t * ξ₂))
        * ee (-(i₁ : ℝ) * ξ₁ - (i₂ : ℝ) * ξ₂) = E3 (ξ₁, ξ₂) := by
      intro ξ₁ ξ₂
      simp only [hEd3]
      rw [← hinner3 ξ₁ ξ₂]
      ring
    rw [hset, hFub]
    refine Eq.trans ?_ (MeasureTheory.integral_prod E3 hE3i).symm
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun ξ₁ => ?_)
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun ξ₂ => ?_)
    exact hpt ξ₁ ξ₂
  -- the a.e. pointwise identity
  have hpw : ∀ᵐ z : ℝ × ℝ ∂(volume.prod volume),
      ee (-(i₁ : ℝ) * z.1 - (i₂ : ℝ) * z.2)
        * (∫ t in (1 / 2 : ℝ)..1,
            (AV z.1 * ee (U t * z.1)) * (BV z.2 * ee (V t * z.2)))
      = c0 * (ee (-(i₁ : ℝ) * z.1 - (i₂ : ℝ) * z.2)
            * (varphiNtj N k₁ (-1) 1 z.1 * varphitildeNt P P.natDegree N 0 1 z.2)
          - ee (-(i₁ : ℝ) * z.1 - (i₂ : ℝ) * z.2)
            * (varphiNtj N k₁ (-1) (1 / 2) z.1
              * varphitildeNt P P.natDegree N 0 (1 / 2) z.2))
        - c1 * (ee (-(i₁ : ℝ) * z.1 - (i₂ : ℝ) * z.2)
            * ∫ t in (1 / 2 : ℝ)..1,
                mdlW3 P N t * ((AM z.1 * ee (U t * z.1)) * (BM z.2 * ee (V t * z.2)))) := by
    have hnull : ∀ᵐ z : ℝ × ℝ ∂(volume.prod volume), z.1 ≠ 0 := by
      have h1 : ∀ᵐ a : ℝ ∂(volume : Measure ℝ), a ≠ 0 := by
        rw [MeasureTheory.ae_iff]
        have hset : {a : ℝ | ¬ a ≠ 0} = ({0} : Set ℝ) := by ext a; simp
        rw [hset, Real.volume_singleton]
      rw [MeasureTheory.Measure.ae_prod_iff_ae_ae (p := fun z : ℝ × ℝ => z.1 ≠ 0)
        (measurable_fst (measurableSet_singleton (0 : ℝ))).compl]
      filter_upwards [h1] with a ha
      exact Filter.Eventually.of_forall fun b => ha
    filter_upwards [hnull] with z hz
    have hconv0 : (∫ t in (1 / 2 : ℝ)..1,
            (AV z.1 * ee (U t * z.1)) * (BV z.2 * ee (V t * z.2)))
          = ∫ t in (1 / 2 : ℝ)..1,
              varphiNt N k₁ t z.1 * varphitildeNt P P.natDegree N 0 t z.2 := by
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [hAV, hBV, hU, hV, ← varphiNt_val, ← varphitildeNt_val]
    have hconv1 : (∫ t in (1 / 2 : ℝ)..1,
            varphiNtj N k₁ (-1) t z.1 * varphitildeNtj P N 0 1 t z.2 * mdlW3 P N t)
          = ∫ t in (1 / 2 : ℝ)..1,
              mdlW3 P N t * ((AM z.1 * ee (U t * z.1)) * (BM z.2 * ee (V t * z.2))) := by
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [ampNeg1_val N k₁ t z.1, ampPos1_val P N t z.2]
      simp only [hAM, hBM, hU, hV]
      ring
    rw [hconv0, MdlBumpIntegIdentI P N k₁ 0 hN z.1 z.2 hz, hconv1]
    rw [← hc0, ← hc1]
    simp only [hAM, hBM, hU, hV]
    ring
  -- linearity of the integral
  have hlin : (∫ z : ℝ × ℝ, c0 * (E1 z - E2 z) - c1 * E3 z) = c0 * (L1 - L2) - c1 * L3 := by
    have h1 : Integrable (fun z : ℝ × ℝ => c0 * E1 z) (volume.prod volume) := hE1i.const_mul _
    have h2 : Integrable (fun z : ℝ × ℝ => c0 * E2 z) (volume.prod volume) := hE2i.const_mul _
    have h3 : Integrable (fun z : ℝ × ℝ => c1 * E3 z) (volume.prod volume) := hE3i.const_mul _
    have h12 : Integrable (fun z : ℝ × ℝ => c0 * E1 z - c0 * E2 z) (volume.prod volume) :=
      h1.sub h2
    have hA : (∫ z : ℝ × ℝ, c0 * (E1 z - E2 z) - c1 * E3 z ∂(volume.prod volume))
        = ∫ z : ℝ × ℝ, (c0 * E1 z - c0 * E2 z) - c1 * E3 z ∂(volume.prod volume) := by
      refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun z => ?_)
      ring
    have hB : (∫ z : ℝ × ℝ, (c0 * E1 z - c0 * E2 z) - c1 * E3 z ∂(volume.prod volume))
        = (∫ z : ℝ × ℝ, c0 * E1 z - c0 * E2 z ∂(volume.prod volume))
          - ∫ z : ℝ × ℝ, c1 * E3 z ∂(volume.prod volume) :=
      MeasureTheory.integral_sub h12 h3
    have hC : (∫ z : ℝ × ℝ, c0 * E1 z - c0 * E2 z ∂(volume.prod volume))
        = (∫ z : ℝ × ℝ, c0 * E1 z ∂(volume.prod volume))
          - ∫ z : ℝ × ℝ, c0 * E2 z ∂(volume.prod volume) :=
      MeasureTheory.integral_sub h1 h2
    have hD1 : (∫ z : ℝ × ℝ, c0 * E1 z ∂(volume.prod volume)) = c0 * L1 := by
      have h := MeasureTheory.integral_const_mul (μ := volume.prod volume) c0 E1
      rw [h, ← hLp1]
    have hD2 : (∫ z : ℝ × ℝ, c0 * E2 z ∂(volume.prod volume)) = c0 * L2 := by
      have h := MeasureTheory.integral_const_mul (μ := volume.prod volume) c0 E2
      rw [h, ← hLp2]
    have hD3 : (∫ z : ℝ × ℝ, c1 * E3 z ∂(volume.prod volume)) = c1 * L3 := by
      have h := MeasureTheory.integral_const_mul (μ := volume.prod volume) c1 E3
      rw [h, ← hLp3]
    calc (∫ z : ℝ × ℝ, c0 * (E1 z - E2 z) - c1 * E3 z ∂(volume.prod volume))
        = (∫ z : ℝ × ℝ, (c0 * E1 z - c0 * E2 z) - c1 * E3 z ∂(volume.prod volume)) := hA
      _ = (∫ z : ℝ × ℝ, c0 * E1 z - c0 * E2 z ∂(volume.prod volume))
            - ∫ z : ℝ × ℝ, c1 * E3 z ∂(volume.prod volume) := hB
      _ = ((∫ z : ℝ × ℝ, c0 * E1 z ∂(volume.prod volume))
              - ∫ z : ℝ × ℝ, c0 * E2 z ∂(volume.prod volume))
            - ∫ z : ℝ × ℝ, c1 * E3 z ∂(volume.prod volume) := by rw [hC]
      _ = (c0 * L1 - c0 * L2) - c1 * L3 := by rw [hD1, hD2, hD3]
      _ = c0 * (L1 - L2) - c1 * L3 := by ring
  calc L0 = ∫ z : ℝ × ℝ, E0 z ∂(volume.prod volume) := hLp0
    _ = ∫ z : ℝ × ℝ, c0 * (E1 z - E2 z) - c1 * E3 z ∂(volume.prod volume) :=
        MeasureTheory.integral_congr_ae hpw
    _ = c0 * (L1 - L2) - c1 * L3 := hlin
    _ = (mdlScaleF k₁ : ℂ) * mdlIota
          * (cw (varphiNtj N k₁ (-1) 1) i₁
              * cw (varphitildeNt P P.natDegree N 0 1) i₂
            - cw (varphiNtj N k₁ (-1) (1 / 2)) i₁
              * cw (varphitildeNt P P.natDegree N 0 (1 / 2)) i₂)
        - (mdlScaleFG P k₁ 0 : ℂ)
            * (∫ t in (1 / 2 : ℝ)..1,
                mdlW3 P N t * (cw (varphiNtj N k₁ (-1) t) i₁
                  * cw (varphitildeNtj P N 0 1 t) i₂)) := by
        rw [hL1d, hL2d, hL3d, hc0, hc1]

/-- **The `cw`-level integration-by-parts identity (i)** of Krause--Mirek--Tao §6: the
frequency-coefficient form of `Work.KMTPlan.A6.MdlBumpIntegIdentI`, for the pair
`(k₁, k₂) = (k₁, 0)` with `k₁ ≥ 1`. -/
theorem MdlCwIntegIdentI (P : Polynomial ℤ) (N k₁ : ℕ) (hN : 1 ≤ N) (hk₁ : 1 ≤ k₁) :
    ∀ i₁ i₂ : ℤ,
      (∫ t in (1 / 2 : ℝ)..1,
          Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphiNt N k₁ t) i₁
            * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphitildeNt P P.natDegree N 0 t) i₂)
        = (Work.KMTPlan.A6.mdlScaleF k₁ : ℂ) * Work.KMTPlan.A6.mdlIota
            * (Work.KMTAreas.A7.cw (Work.KMTPlan.A6.varphiNtj N k₁ (-1) 1) i₁
                * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphitildeNt P P.natDegree N 0 1) i₂
              - Work.KMTAreas.A7.cw (Work.KMTPlan.A6.varphiNtj N k₁ (-1) (1 / 2)) i₁
                * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphitildeNt P P.natDegree N 0 (1 / 2)) i₂)
          - (Work.KMTPlan.A6.mdlScaleFG P k₁ 0 : ℂ)
              * (∫ t in (1 / 2 : ℝ)..1, Work.KMTPlan.A6.mdlW3 P N t
                  * (Work.KMTAreas.A7.cw (Work.KMTPlan.A6.varphiNtj N k₁ (-1) t) i₁
                      * Work.KMTAreas.A7.cw (Work.KMTPlan.A6.varphitildeNtj P N 0 1 t) i₂)) :=
  fun i₁ i₂ => MdlCwIntegIdentI_aux P N k₁ hN hk₁ i₁ i₂

end

end Work.KMTPlan.A6
