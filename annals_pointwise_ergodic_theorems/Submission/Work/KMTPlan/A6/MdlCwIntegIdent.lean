/-
# The `cw`-level (Fourier-coefficient) form of the integration-by-parts identity (ii)

`cw m i = ∫ θ, m θ * e(-iθ) dθ` is the `i`-th Fourier coefficient of `periodize m`.  This module
proves `Work.KMTPlan.A6.MdlCwIntegIdent`: the frequency-level integration-by-parts identity
`Work.KMTPlan.A6.MdlBumpIntegIdent` (proved in `Submission/Work/KMTPlan/A6/MdlBumpIntegIdent.lean`)
applied to the bilinear functional `(Φ,Ψ) ↦ (∫ Φ e(-i₁·))·(∫ Ψ e(-i₂·)) = cw Φ i₁ · cw Ψ i₂`.

## Shape of the proof

Write `F_j(ξ₁,ξ₂)`, `j ∈ {0,1,2,3,4}`, for the five quantities of the frequency-level identity:
`F₀ = ∫_{1/2}^1 φ_{N,t}(ξ₁)φ̃_{N,t}(ξ₂) dt`, `F₁`, `F₂` the two endpoint products (at `t = 1` and
`t = 1/2`), `F₃ = ∫_{1/2}^1 φ_{N,t,1}(ξ₁)φ̃_{N,t,-1}(ξ₂)W₁(t) dt`, `F₄ = ∫ ... W₂(t) dt`, so that
`MdlBumpIntegIdent` reads `F₀ = c(F₁ W₁(1) - F₂ W₁(1/2)) - c'F₃ + cF₄` off the hyperplane
`ξ₂ = 0`.  Multiplying by `e(-i₁ξ₁ - i₂ξ₂)` and integrating over `ℝ²` reduces each of the five
terms to the corresponding `cw`-product: for the three `t`-integrals this is the Fubini identity
`Work.KMTPlan.A6.CwFubiniWeight` (with the weight `W ≡ 1`, `mdlW1 P N`, `mdlW2 P N` and the
amplitudes `φ_N`, `φ̃_N`, `2^{-k₁}Nξ φ_N`, `(2^{-dk₂}N^dξ)^{-1}φ̃_N`), for the two endpoint terms
the product formula `∫∫ f(ξ₁)g(ξ₂) = (∫f)(∫g)` (`MeasureTheory.integral_prod_mul`).  The
`ξ₂ = 0` slice is Lebesgue-null, so the pointwise identity may be applied almost everywhere; the
integrability needed to split the resulting sum of four double integrals is
`Work.KMTPlan.A6.MarginalModInt` (the marginals in `(ξ₁,ξ₂)` of the Fubini integrands) together
with the boundedness of `e(·)`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlBumpIntegIdent
import Submission.Work.KMTPlan.A6.CwFubiniWeight
import Submission.Work.KMTPlan.A6.MarginalModInt
import Submission.Work.KMTPlan.A6.VarpModAmpInt
import Submission.Work.KMTPlan.A6.MdlWInt

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators Interval
open Work.KMTAreas.A7

/-! ## The amplitude/phase vocabulary of the modified bumps

The modified bumps `φ_{N,t,j}`, `φ̃_{N,t,j}` of `(pntj)`/`(tpntj)` are products
`(amplitude) · e(phase)`: this section records the amplitudes `ampMod`, `btilMod` and the phases
`uphase`, `vphase`, so that the (weighted) Fubini identity `CwFubiniWeight` and the integrability
lemma `MarginalModInt` can be applied to them. -/

/-- The amplitude of the modified bump `φ_{N,t,1}`: `ξ ↦ 2^{-k₁}Nξ · φ_N(ξ)`. -/
private noncomputable def ampMod (N k₁ : ℕ) : ℝ → ℂ :=
  fun ξ => ((((2 : ℝ) ^ (-(k₁ : ℝ)) * (N : ℝ) * ξ : ℝ)) : ℂ) * varphiN N k₁ ξ

/-- The amplitude of the modified bump `φ̃_{N,t,-1}`: `ξ ↦ (2^{-dk₂}N^dξ)^{-1} · φ̃_N(ξ)`. -/
private noncomputable def btilMod (P : Polynomial ℤ) (N k₂ : ℕ) : ℝ → ℂ :=
  fun ξ => ((((2 : ℝ) ^ (-((P.natDegree : ℝ) * (k₂ : ℝ))) * ((N : ℝ)) ^ P.natDegree * ξ
    : ℝ)) : ℂ)⁻¹ * varphitildeN P.natDegree N k₂ ξ

/-- The phase `t ↦ N t` of the modulated bump `φ_{N,t}`. -/
private noncomputable def uphase (N : ℕ) : ℝ → ℝ := fun t => (N : ℝ) * t

/-- The phase `t ↦ P(Nt)` of the modulated bump `φ̃_{N,t}`. -/
private noncomputable def vphase (P : Polynomial ℤ) (N : ℕ) : ℝ → ℝ :=
  fun t => PevalR P ((N : ℝ) * t)

private lemma measurable_uphase (N : ℕ) : Measurable (uphase N) := by
  unfold uphase; fun_prop

private lemma measurable_vphase (P : Polynomial ℤ) (N : ℕ) : Measurable (vphase P N) := by
  unfold vphase
  exact (continuous_PevalR_comp P (N : ℝ)).measurable

private lemma measurable_mdlW1 (P : Polynomial ℤ) (N : ℕ) : Measurable (mdlW1 P N) := by
  unfold mdlW1
  exact Complex.continuous_ofReal.measurable.comp
    (measurable_const.div ((continuous_PderivR_comp P (N : ℝ)).measurable))

private lemma measurable_mdlW2 (P : Polynomial ℤ) (N : ℕ) : Measurable (mdlW2 P N) := by
  unfold mdlW2
  have hnum : Measurable (fun t : ℝ => (N : ℝ) ^ P.natDegree * Pderiv2R P ((N : ℝ) * t)) :=
    measurable_const.mul ((continuous_PderivR_comp P.derivative (N : ℝ)).measurable)
  have hden : Measurable (fun t : ℝ => (PderivR P ((N : ℝ) * t)) ^ 2) :=
    ((continuous_PderivR_comp P (N : ℝ)).measurable).pow_const 2
  exact Complex.continuous_ofReal.measurable.comp (hnum.div hden)

private lemma varphiNt_val (N k₁ : ℕ) (t ξ : ℝ) :
    varphiNt N k₁ t ξ = varphiN N k₁ ξ * ee (uphase N t * ξ) := rfl

private lemma varphitildeNt_val (P : Polynomial ℤ) (N k₂ : ℕ) (t ξ : ℝ) :
    varphitildeNt P P.natDegree N k₂ t ξ
      = varphitildeN P.natDegree N k₂ ξ * ee (vphase P N t * ξ) := rfl

private lemma ampMod_val (N k₁ : ℕ) (t ξ : ℝ) :
    ampMod N k₁ ξ * ee (uphase N t * ξ) = varphiNtj N k₁ 1 t ξ := by
  simp only [ampMod, varphiNtj, varphiNt, uphase, zpow_one]
  ring

private lemma btilMod_val (P : Polynomial ℤ) (N k₂ : ℕ) (t ξ : ℝ) :
    btilMod P N k₂ ξ * ee (vphase P N t * ξ) = varphitildeNtj P N k₂ (-1) t ξ := by
  simp only [btilMod, varphitildeNtj, varphitildeNt, vphase, zpow_neg_one]
  ring

private lemma varphiNt_funeq (N k₁ : ℕ) (t : ℝ) :
    varphiNt N k₁ t = fun ξ => varphiN N k₁ ξ * ee (uphase N t * ξ) := rfl

private lemma varphitildeNt_funeq (P : Polynomial ℤ) (N k₂ : ℕ) (t : ℝ) :
    varphitildeNt P P.natDegree N k₂ t
      = fun ξ => varphitildeN P.natDegree N k₂ ξ * ee (vphase P N t * ξ) := rfl

private lemma varphiNtj_funeq (N k₁ : ℕ) (t : ℝ) :
    varphiNtj N k₁ 1 t = fun ξ => ampMod N k₁ ξ * ee (uphase N t * ξ) :=
  funext fun ξ => (ampMod_val N k₁ t ξ).symm

private lemma varphitildeNtj_funeq (P : Polynomial ℤ) (N k₂ : ℕ) (t : ℝ) :
    varphitildeNtj P N k₂ (-1) t = fun ξ => btilMod P N k₂ ξ * ee (vphase P N t * ξ) :=
  funext fun ξ => (btilMod_val P N k₂ t ξ).symm

/-- Integrability of an integrable function multiplied by a character. -/
private lemma integrable_mul_ee {f : ℝ → ℂ} (hf : Integrable f) (c : ℝ) :
    Integrable (fun ξ : ℝ => f ξ * ee (c * ξ)) := by
  have h := hf.bdd_mul (f := fun ξ : ℝ => ee (c * ξ)) (c := 1)
    (by simp only [ee]; fun_prop)
    (by filter_upwards with ξ; rw [Work.A7.ee_norm_char])
  exact h.congr (Filter.Eventually.of_forall fun ξ => mul_comm _ _)

/-- The character identity in the subtraction form used by the `(i₁,i₂)`-oscillation factors. -/
private lemma ee_osc (i₁ i₂ : ℤ) (z : ℝ × ℝ) :
    ee (-(i₁ : ℝ) * z.1 - (i₂ : ℝ) * z.2)
      = ee (-(i₁ : ℝ) * z.1) * ee (-(i₂ : ℝ) * z.2) := by
  rw [sub_eq_add_neg, Work.A7.ee_add_char,
    show -((i₂ : ℝ) * z.2) = -(i₂ : ℝ) * z.2 by ring]
theorem MdlCwIntegIdent (P : Polynomial ℤ) (N k₁ k₂ : ℕ) (hN : 1 ≤ N) (hk₂ : 1 ≤ k₂)
    (hP : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, Work.KMTPlan.A6.PderivR P ((N : ℝ) * t) ≠ 0) :
    ∀ i₁ i₂ : ℤ,
      (∫ t in (1 / 2 : ℝ)..1, Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphiNt N k₁ t) i₁
          * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t) i₂)
        = (Work.KMTPlan.A6.mdlScale P k₂ : ℂ) * Work.KMTPlan.A6.mdlIota
            * (Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphiNt N k₁ 1) i₁
                * Work.KMTAreas.A7.cw (Work.KMTPlan.A6.varphitildeNtj P N k₂ (-1) 1) i₂
                * Work.KMTPlan.A6.mdlW1 P N 1
              - Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphiNt N k₁ (1 / 2)) i₁
                * Work.KMTAreas.A7.cw (Work.KMTPlan.A6.varphitildeNtj P N k₂ (-1) (1 / 2)) i₂
                * Work.KMTPlan.A6.mdlW1 P N (1 / 2))
          - (Work.KMTPlan.A6.mdlScaleFe P k₁ k₂ : ℂ)
              * (∫ t in (1 / 2 : ℝ)..1,
                  Work.KMTAreas.A7.cw (Work.KMTPlan.A6.varphiNtj N k₁ 1 t) i₁
                  * Work.KMTAreas.A7.cw (Work.KMTPlan.A6.varphitildeNtj P N k₂ (-1) t) i₂
                  * Work.KMTPlan.A6.mdlW1 P N t)
          + (Work.KMTPlan.A6.mdlScale P k₂ : ℂ) * Work.KMTPlan.A6.mdlIota
              * (∫ t in (1 / 2 : ℝ)..1,
                  Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphiNt N k₁ t) i₁
                  * Work.KMTAreas.A7.cw (Work.KMTPlan.A6.varphitildeNtj P N k₂ (-1) t) i₂
                  * Work.KMTPlan.A6.mdlW2 P N t) := by
  intro i₁ i₂
  -- ### abbreviations
  set AV : ℝ → ℂ := varphiN N k₁ with hAV
  set AM : ℝ → ℂ := ampMod N k₁ with hAM
  set BV : ℝ → ℂ := varphitildeN P.natDegree N k₂ with hBV
  set BM : ℝ → ℂ := btilMod P N k₂ with hBM
  set U : ℝ → ℝ := uphase N with hU
  set V : ℝ → ℝ := vphase P N with hV
  set c0 : ℂ := (mdlScale P k₂ : ℂ) * mdlIota with hc0
  set c1 : ℂ := (mdlScaleFe P k₁ k₂ : ℂ) with hc1
  set L0 : ℂ := ∫ t in (1 / 2 : ℝ)..1, cw (varphiNt N k₁ t) i₁
      * cw (varphitildeNt P P.natDegree N k₂ t) i₂ with hL0eq
  set L1 : ℂ := cw (varphiNt N k₁ 1) i₁ * cw (varphitildeNtj P N k₂ (-1) 1) i₂ with hL1eq
  set L2 : ℂ := cw (varphiNt N k₁ (1 / 2)) i₁ * cw (varphitildeNtj P N k₂ (-1) (1 / 2)) i₂
    with hL2eq
  set L3 : ℂ := ∫ t in (1 / 2 : ℝ)..1, cw (varphiNtj N k₁ 1 t) i₁
      * cw (varphitildeNtj P N k₂ (-1) t) i₂ * mdlW1 P N t with hL3eq
  set L4 : ℂ := ∫ t in (1 / 2 : ℝ)..1, cw (varphiNt N k₁ t) i₁
      * cw (varphitildeNtj P N k₂ (-1) t) i₂ * mdlW2 P N t with hL4eq
  set E0 : ℝ × ℝ → ℂ := fun z => ee (-(i₁ : ℝ) * z.1 - (i₂ : ℝ) * z.2)
    * ∫ t in (1 / 2 : ℝ)..1, varphiNt N k₁ t z.1 * varphitildeNt P P.natDegree N k₂ t z.2
    with hE0
  set E1 : ℝ × ℝ → ℂ := fun z => ee (-(i₁ : ℝ) * z.1 - (i₂ : ℝ) * z.2)
    * (varphiNt N k₁ 1 z.1 * varphitildeNtj P N k₂ (-1) 1 z.2) with hE1
  set E2 : ℝ × ℝ → ℂ := fun z => ee (-(i₁ : ℝ) * z.1 - (i₂ : ℝ) * z.2)
    * (varphiNt N k₁ (1 / 2) z.1 * varphitildeNtj P N k₂ (-1) (1 / 2) z.2) with hE2
  set E3 : ℝ × ℝ → ℂ := fun z => ee (-(i₁ : ℝ) * z.1 - (i₂ : ℝ) * z.2)
    * ∫ t in (1 / 2 : ℝ)..1,
        varphiNtj N k₁ 1 t z.1 * varphitildeNtj P N k₂ (-1) t z.2 * mdlW1 P N t with hE3
  set E4 : ℝ × ℝ → ℂ := fun z => ee (-(i₁ : ℝ) * z.1 - (i₂ : ℝ) * z.2)
    * ∫ t in (1 / 2 : ℝ)..1,
        varphiNt N k₁ t z.1 * varphitildeNtj P N k₂ (-1) t z.2 * mdlW2 P N t with hE4
  -- ### integrability data
  have hAVi : Integrable AV := by
    rw [hAV]; exact (Work.A7.varphiN_integrable_measurable N k₁).1
  have hAVm : Measurable AV := by
    rw [hAV]; exact (Work.A7.varphiN_integrable_measurable N k₁).2
  have hBVi : Integrable BV := by
    rw [hBV]; exact (Work.A7.varphitildeN_integrable_measurable P.natDegree N k₂).1
  have hBVm : Measurable BV := by
    rw [hBV]; exact (Work.A7.varphitildeN_integrable_measurable P.natDegree N k₂).2
  have hAMi : Integrable AM := by
    rw [hAM]; exact (VarpModAmpInt P N k₁ k₂ hN hk₂).1.1
  have hAMm : Measurable AM := by
    rw [hAM]; exact (VarpModAmpInt P N k₁ k₂ hN hk₂).1.2
  have hBMi : Integrable BM := by
    rw [hBM]; exact (VarpModAmpInt P N k₁ k₂ hN hk₂).2.1
  have hBMm : Measurable BM := by
    rw [hBM]; exact (VarpModAmpInt P N k₁ k₂ hN hk₂).2.2
  have hum : Measurable U := by rw [hU]; exact measurable_uphase N
  have hvm : Measurable V := by rw [hV]; exact measurable_vphase P N
  have h1i : Integrable (fun _ : ℝ => (1 : ℂ)) (volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) := by
    haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) :=
      ⟨by rw [MeasureTheory.Measure.restrict_apply_univ]; simp [Real.volume_Ioc]⟩
    exact MeasureTheory.integrable_const 1
  have hW1i : Integrable (mdlW1 P N) (volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) :=
    (MdlWInt P N hP).1
  have hW2i : Integrable (mdlW2 P N) (volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) :=
    (MdlWInt P N hP).2
  have hW1m : Measurable (mdlW1 P N) := measurable_mdlW1 P N
  have hW2m : Measurable (mdlW2 P N) := measurable_mdlW2 P N
  -- ### the two endpoint products as product-measure integrals
  have hprod1 : cw (varphiNt N k₁ 1) i₁ * cw (varphitildeNtj P N k₂ (-1) 1) i₂
      = ∫ z : ℝ × ℝ, (ee (-(i₁ : ℝ) * z.1) * (varphiNt N k₁ 1 z.1))
        * (ee (-(i₂ : ℝ) * z.2) * (varphitildeNtj P N k₂ (-1) 1 z.2))
        ∂(volume.prod volume) := by
    simp only [cw]
    rw [← MeasureTheory.integral_prod_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    ring
  have hprod2 : cw (varphiNt N k₁ (1 / 2)) i₁ * cw (varphitildeNtj P N k₂ (-1) (1 / 2)) i₂
      = ∫ z : ℝ × ℝ, (ee (-(i₁ : ℝ) * z.1) * (varphiNt N k₁ (1 / 2) z.1))
        * (ee (-(i₂ : ℝ) * z.2) * (varphitildeNtj P N k₂ (-1) (1 / 2) z.2))
        ∂(volume.prod volume) := by
    simp only [cw]
    rw [← MeasureTheory.integral_prod_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    ring
  -- ### integrability of the four summands
  have hE1f : Integrable (fun ξ : ℝ => ee (-(i₁ : ℝ) * ξ) * (varphiNt N k₁ 1 ξ)) := by
    have h : Integrable (fun ξ : ℝ => ee (-(i₁ : ℝ) * ξ) * (AV ξ * ee (uphase N 1 * ξ))) :=
      (integrable_mul_ee hAVi (uphase N 1)).bdd_mul
        (f := fun ξ : ℝ => ee (-(i₁ : ℝ) * ξ)) (c := 1)
        (by simp only [ee]; fun_prop)
        (by filter_upwards with ξ; rw [Work.A7.ee_norm_char])
    simpa only [hAV, hU, varphiNt_val] using h
  have hE1g : Integrable (fun ξ : ℝ => ee (-(i₂ : ℝ) * ξ) * (varphitildeNtj P N k₂ (-1) 1 ξ)) := by
    have h : Integrable (fun ξ : ℝ => ee (-(i₂ : ℝ) * ξ) * (BM ξ * ee (vphase P N 1 * ξ))) :=
      (integrable_mul_ee hBMi (vphase P N 1)).bdd_mul
        (f := fun ξ : ℝ => ee (-(i₂ : ℝ) * ξ)) (c := 1)
        (by simp only [ee]; fun_prop)
        (by filter_upwards with ξ; rw [Work.A7.ee_norm_char])
    simpa only [hBM, hV, btilMod_val] using h
  have hE2f : Integrable (fun ξ : ℝ => ee (-(i₁ : ℝ) * ξ) * (varphiNt N k₁ (1 / 2) ξ)) := by
    have h : Integrable (fun ξ : ℝ => ee (-(i₁ : ℝ) * ξ) * (AV ξ * ee (uphase N (1 / 2) * ξ))) :=
      (integrable_mul_ee hAVi (uphase N (1 / 2))).bdd_mul
        (f := fun ξ : ℝ => ee (-(i₁ : ℝ) * ξ)) (c := 1)
        (by simp only [ee]; fun_prop)
        (by filter_upwards with ξ; rw [Work.A7.ee_norm_char])
    simpa only [hAV, hU, varphiNt_val] using h
  have hE2g : Integrable (fun ξ : ℝ =>
      ee (-(i₂ : ℝ) * ξ) * (varphitildeNtj P N k₂ (-1) (1 / 2) ξ)) := by
    have h : Integrable (fun ξ : ℝ => ee (-(i₂ : ℝ) * ξ) * (BM ξ * ee (vphase P N (1 / 2) * ξ))) :=
      (integrable_mul_ee hBMi (vphase P N (1 / 2))).bdd_mul
        (f := fun ξ : ℝ => ee (-(i₂ : ℝ) * ξ)) (c := 1)
        (by simp only [ee]; fun_prop)
        (by filter_upwards with ξ; rw [Work.A7.ee_norm_char])
    simpa only [hBM, hV, btilMod_val] using h
  have hE1i : Integrable E1 (volume.prod volume) := by
    simp only [hE1]
    exact (hE1f.mul_prod hE1g).congr (Filter.Eventually.of_forall fun z => by
      calc (ee (-(i₁ : ℝ) * z.1) * (varphiNt N k₁ 1 z.1))
            * (ee (-(i₂ : ℝ) * z.2) * (varphitildeNtj P N k₂ (-1) 1 z.2))
          = (ee (-(i₁ : ℝ) * z.1) * ee (-(i₂ : ℝ) * z.2))
              * (varphiNt N k₁ 1 z.1 * varphitildeNtj P N k₂ (-1) 1 z.2) := by ring
        _ = ee (-(i₁ : ℝ) * z.1 - (i₂ : ℝ) * z.2)
              * (varphiNt N k₁ 1 z.1 * varphitildeNtj P N k₂ (-1) 1 z.2) := by rw [← ee_osc])
  have hE2i : Integrable E2 (volume.prod volume) := by
    simp only [hE2]
    exact (hE2f.mul_prod hE2g).congr (Filter.Eventually.of_forall fun z => by
      calc (ee (-(i₁ : ℝ) * z.1) * (varphiNt N k₁ (1 / 2) z.1))
            * (ee (-(i₂ : ℝ) * z.2) * (varphitildeNtj P N k₂ (-1) (1 / 2) z.2))
          = (ee (-(i₁ : ℝ) * z.1) * ee (-(i₂ : ℝ) * z.2))
              * (varphiNt N k₁ (1 / 2) z.1 * varphitildeNtj P N k₂ (-1) (1 / 2) z.2) := by ring
        _ = ee (-(i₁ : ℝ) * z.1 - (i₂ : ℝ) * z.2)
              * (varphiNt N k₁ (1 / 2) z.1 * varphitildeNtj P N k₂ (-1) (1 / 2) z.2) := by
              rw [← ee_osc])
  -- the marginal `(ξ₁,ξ₂)`-integrability of the three `t`-integrals
  have hE0b : Integrable (fun z : ℝ × ℝ => ∫ t in (1 / 2 : ℝ)..1,
      (fun _ : ℝ => (1 : ℂ)) t * (AV z.1 * ee (U t * z.1)) * (BV z.2 * ee (V t * z.2)))
      (volume.prod volume) :=
    MarginalModInt hAVi hBVi hAVm hBVm hum hvm (W := fun _ : ℝ => (1 : ℂ)) h1i measurable_const
  have hE0b' : Integrable (fun z : ℝ × ℝ => ∫ t in (1 / 2 : ℝ)..1,
      varphiNt N k₁ t z.1 * varphitildeNt P P.natDegree N k₂ t z.2) (volume.prod volume) :=
    hE0b.congr (Filter.Eventually.of_forall fun z => by
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [Pi.one_apply, one_mul]
      rw [hAV, hBV, hU, hV, varphiNt_val, varphitildeNt_val]
      try ring)
  have hE3b : Integrable (fun z : ℝ × ℝ => ∫ t in (1 / 2 : ℝ)..1,
      mdlW1 P N t * (AM z.1 * ee (U t * z.1)) * (BM z.2 * ee (V t * z.2)))
      (volume.prod volume) :=
    MarginalModInt hAMi hBMi hAMm hBMm hum hvm hW1i hW1m
  have hE3b' : Integrable (fun z : ℝ × ℝ => ∫ t in (1 / 2 : ℝ)..1,
      varphiNtj N k₁ 1 t z.1 * varphitildeNtj P N k₂ (-1) t z.2 * mdlW1 P N t)
      (volume.prod volume) :=
    hE3b.congr (Filter.Eventually.of_forall fun z => by
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [hAM, hBM, hU, hV, ampMod_val, btilMod_val]
      try ring)
  have hE4b : Integrable (fun z : ℝ × ℝ => ∫ t in (1 / 2 : ℝ)..1,
      mdlW2 P N t * (AV z.1 * ee (U t * z.1)) * (BM z.2 * ee (V t * z.2)))
      (volume.prod volume) :=
    MarginalModInt hAVi hBMi hAVm hBMm hum hvm hW2i hW2m
  have hE4b' : Integrable (fun z : ℝ × ℝ => ∫ t in (1 / 2 : ℝ)..1,
      varphiNt N k₁ t z.1 * varphitildeNtj P N k₂ (-1) t z.2 * mdlW2 P N t)
      (volume.prod volume) :=
    hE4b.congr (Filter.Eventually.of_forall fun z => by
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [hAV, hBM, hU, hV, varphiNt_val, btilMod_val]
      try ring)
  have hE0i : Integrable E0 (volume.prod volume) := by
    simp only [hE0]
    exact hE0b'.bdd_mul (f := fun z : ℝ × ℝ => ee (-(i₁ : ℝ) * z.1 - (i₂ : ℝ) * z.2))
      (c := 1) (by simp only [ee]; fun_prop)
      (by filter_upwards with z; rw [Work.A7.ee_norm_char])
  have hE3i : Integrable E3 (volume.prod volume) := by
    simp only [hE3]
    exact hE3b'.bdd_mul (f := fun z : ℝ × ℝ => ee (-(i₁ : ℝ) * z.1 - (i₂ : ℝ) * z.2))
      (c := 1) (by simp only [ee]; fun_prop)
      (by filter_upwards with z; rw [Work.A7.ee_norm_char])
  have hE4i : Integrable E4 (volume.prod volume) := by
    simp only [hE4]
    exact hE4b'.bdd_mul (f := fun z : ℝ × ℝ => ee (-(i₁ : ℝ) * z.1 - (i₂ : ℝ) * z.2))
      (c := 1) (by simp only [ee]; fun_prop)
      (by filter_upwards with z; rw [Work.A7.ee_norm_char])
  -- ### `L0 = ∫ E0`
  have hL0 : L0 = ∫ z : ℝ × ℝ, E0 z ∂(volume.prod volume) := by
    have hFub := CwFubiniWeight (a := AV) (b := BV) hAVi hBVi hAVm hBVm (u := U) (v := V) hum hvm
      (W := fun _ : ℝ => (1 : ℂ)) h1i measurable_const i₁ i₂
    have hset : L0 = ∫ t in (1 / 2 : ℝ)..1, (fun _ : ℝ => (1 : ℂ)) t
        * cw (fun ξ => AV ξ * ee (U t * ξ)) i₁
        * cw (fun ξ => BV ξ * ee (V t * ξ)) i₂ := by
      rw [hL0eq]
      refine intervalIntegral.integral_congr fun t _ => ?_
      have h1 : cw (varphiNt N k₁ t) i₁ = cw (fun ξ => AV ξ * ee (U t * ξ)) i₁ := by
        rw [hAV, hU]; rfl
      have h2 : cw (varphitildeNt P P.natDegree N k₂ t) i₂
          = cw (fun ξ => BV ξ * ee (V t * ξ)) i₂ := by
        rw [hBV, hV]; rfl
      calc cw (varphiNt N k₁ t) i₁ * cw (varphitildeNt P P.natDegree N k₂ t) i₂
          = cw (fun ξ => AV ξ * ee (U t * ξ)) i₁ * cw (fun ξ => BV ξ * ee (V t * ξ)) i₂ := by
            rw [h1, h2]
        _ = (fun _ : ℝ => (1 : ℂ)) t * cw (fun ξ => AV ξ * ee (U t * ξ)) i₁
              * cw (fun ξ => BV ξ * ee (V t * ξ)) i₂ := by ring
    have hpt : ∀ ξ₁ ξ₂ : ℝ, AV ξ₁ * BV ξ₂
        * (∫ t in (1 / 2 : ℝ)..1, (fun _ : ℝ => (1 : ℂ)) t * ee (U t * ξ₁ + V t * ξ₂))
        * ee (-(i₁ : ℝ) * ξ₁ - (i₂ : ℝ) * ξ₂) = E0 (ξ₁, ξ₂) := by
      intro ξ₁ ξ₂
      simp only [hE0]
      have hstep : AV ξ₁ * BV ξ₂
            * (∫ t in (1 / 2 : ℝ)..1, (fun _ : ℝ => (1 : ℂ)) t * ee (U t * ξ₁ + V t * ξ₂))
            * ee (-(i₁ : ℝ) * ξ₁ - (i₂ : ℝ) * ξ₂)
          = ee (-(i₁ : ℝ) * ξ₁ - (i₂ : ℝ) * ξ₂) * ∫ t in (1 / 2 : ℝ)..1,
              AV ξ₁ * BV ξ₂ * ((fun _ : ℝ => (1 : ℂ)) t * ee (U t * ξ₁ + V t * ξ₂)) := by
        rw [show AV ξ₁ * BV ξ₂
              * (∫ t in (1 / 2 : ℝ)..1, (fun _ : ℝ => (1 : ℂ)) t * ee (U t * ξ₁ + V t * ξ₂))
              * ee (-(i₁ : ℝ) * ξ₁ - (i₂ : ℝ) * ξ₂)
            = ee (-(i₁ : ℝ) * ξ₁ - (i₂ : ℝ) * ξ₂) * ((AV ξ₁ * BV ξ₂)
              * ∫ t in (1 / 2 : ℝ)..1, (fun _ : ℝ => (1 : ℂ)) t * ee (U t * ξ₁ + V t * ξ₂)) by
              ring]
        rw [← intervalIntegral.integral_const_mul]
      rw [hstep]
      congr 1
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [Pi.one_apply, one_mul]
      calc AV ξ₁ * BV ξ₂ * ee (U t * ξ₁ + V t * ξ₂)
          = (varphiN N k₁ ξ₁ * ee (uphase N t * ξ₁))
              * (varphitildeN P.natDegree N k₂ ξ₂ * ee (vphase P N t * ξ₂)) := by
            rw [hAV, hBV, hU, hV, Work.A7.ee_add_char]; ring
        _ = varphiNt N k₁ t ξ₁ * varphitildeNt P P.natDegree N k₂ t ξ₂ := by
            rw [← varphiNt_val, ← varphitildeNt_val]
    rw [hset, hFub]
    refine Eq.trans ?_ (MeasureTheory.integral_prod E0 hE0i).symm
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ξ₁ => ?_)
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ξ₂ => ?_)
    exact hpt ξ₁ ξ₂
  -- ### `L1 = ∫ E1`
  have hL1 : L1 = ∫ z : ℝ × ℝ, E1 z ∂(volume.prod volume) :=
    hL1eq.trans (hprod1.trans (by
      have hset : (∫ z : ℝ × ℝ, E1 z ∂(volume.prod volume)) = ∫ z : ℝ × ℝ,
          (ee (-(i₁ : ℝ) * z.1) * (varphiNt N k₁ 1 z.1))
            * (ee (-(i₂ : ℝ) * z.2) * (varphitildeNtj P N k₂ (-1) 1 z.2))
          ∂(volume.prod volume) := by
        simp only [hE1]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only []
        calc ee (-(i₁ : ℝ) * z.1 - (i₂ : ℝ) * z.2)
              * (varphiNt N k₁ 1 z.1 * varphitildeNtj P N k₂ (-1) 1 z.2)
            = (ee (-(i₁ : ℝ) * z.1) * ee (-(i₂ : ℝ) * z.2))
                * (varphiNt N k₁ 1 z.1 * varphitildeNtj P N k₂ (-1) 1 z.2) := by rw [ee_osc]
          _ = (ee (-(i₁ : ℝ) * z.1) * (varphiNt N k₁ 1 z.1))
                * (ee (-(i₂ : ℝ) * z.2) * (varphitildeNtj P N k₂ (-1) 1 z.2)) := by ring
      exact hset.symm))
  -- ### `L2 = ∫ E2`
  have hL2 : L2 = ∫ z : ℝ × ℝ, E2 z ∂(volume.prod volume) :=
    hL2eq.trans (hprod2.trans (by
      have hset : (∫ z : ℝ × ℝ, E2 z ∂(volume.prod volume)) = ∫ z : ℝ × ℝ,
          (ee (-(i₁ : ℝ) * z.1) * (varphiNt N k₁ (1 / 2) z.1))
            * (ee (-(i₂ : ℝ) * z.2) * (varphitildeNtj P N k₂ (-1) (1 / 2) z.2))
          ∂(volume.prod volume) := by
        simp only [hE2]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only []
        calc ee (-(i₁ : ℝ) * z.1 - (i₂ : ℝ) * z.2)
              * (varphiNt N k₁ (1 / 2) z.1 * varphitildeNtj P N k₂ (-1) (1 / 2) z.2)
            = (ee (-(i₁ : ℝ) * z.1) * ee (-(i₂ : ℝ) * z.2))
                * (varphiNt N k₁ (1 / 2) z.1 * varphitildeNtj P N k₂ (-1) (1 / 2) z.2) := by
                rw [ee_osc]
          _ = (ee (-(i₁ : ℝ) * z.1) * (varphiNt N k₁ (1 / 2) z.1))
                * (ee (-(i₂ : ℝ) * z.2)
                    * (varphitildeNtj P N k₂ (-1) (1 / 2) z.2)) := by ring
      exact hset.symm))
  -- ### `L3 = ∫ E3`
  have hL3 : L3 = ∫ z : ℝ × ℝ, E3 z ∂(volume.prod volume) := by
    have hFub := CwFubiniWeight (a := AM) (b := BM) hAMi hBMi hAMm hBMm (u := U) (v := V) hum hvm
      (W := mdlW1 P N) hW1i hW1m i₁ i₂
    have hset : L3 = ∫ t in (1 / 2 : ℝ)..1, mdlW1 P N t
        * cw (fun ξ => AM ξ * ee (U t * ξ)) i₁ * cw (fun ξ => BM ξ * ee (V t * ξ)) i₂ := by
      rw [hL3eq]
      refine intervalIntegral.integral_congr fun t _ => ?_
      have h1 : cw (varphiNtj N k₁ 1 t) i₁ = cw (fun ξ => AM ξ * ee (U t * ξ)) i₁ := by
        rw [hAM, hU, ← varphiNtj_funeq]
      have h2 : cw (varphitildeNtj P N k₂ (-1) t) i₂ = cw (fun ξ => BM ξ * ee (V t * ξ)) i₂ := by
        rw [hBM, hV, ← varphitildeNtj_funeq]
      calc cw (varphiNtj N k₁ 1 t) i₁ * cw (varphitildeNtj P N k₂ (-1) t) i₂ * mdlW1 P N t
          = cw (fun ξ => AM ξ * ee (U t * ξ)) i₁ * cw (fun ξ => BM ξ * ee (V t * ξ)) i₂
              * mdlW1 P N t := by rw [h1, h2]
        _ = mdlW1 P N t * cw (fun ξ => AM ξ * ee (U t * ξ)) i₁
              * cw (fun ξ => BM ξ * ee (V t * ξ)) i₂ := by ring
    have hpt : ∀ ξ₁ ξ₂ : ℝ, AM ξ₁ * BM ξ₂
        * (∫ t in (1 / 2 : ℝ)..1, mdlW1 P N t * ee (U t * ξ₁ + V t * ξ₂))
        * ee (-(i₁ : ℝ) * ξ₁ - (i₂ : ℝ) * ξ₂) = E3 (ξ₁, ξ₂) := by
      intro ξ₁ ξ₂
      simp only [hE3]
      have hstep : AM ξ₁ * BM ξ₂
            * (∫ t in (1 / 2 : ℝ)..1, mdlW1 P N t * ee (U t * ξ₁ + V t * ξ₂))
            * ee (-(i₁ : ℝ) * ξ₁ - (i₂ : ℝ) * ξ₂)
          = ee (-(i₁ : ℝ) * ξ₁ - (i₂ : ℝ) * ξ₂) * ∫ t in (1 / 2 : ℝ)..1,
              AM ξ₁ * BM ξ₂ * (mdlW1 P N t * ee (U t * ξ₁ + V t * ξ₂)) := by
        rw [show AM ξ₁ * BM ξ₂
              * (∫ t in (1 / 2 : ℝ)..1, mdlW1 P N t * ee (U t * ξ₁ + V t * ξ₂))
              * ee (-(i₁ : ℝ) * ξ₁ - (i₂ : ℝ) * ξ₂)
            = ee (-(i₁ : ℝ) * ξ₁ - (i₂ : ℝ) * ξ₂) * ((AM ξ₁ * BM ξ₂)
              * ∫ t in (1 / 2 : ℝ)..1, mdlW1 P N t * ee (U t * ξ₁ + V t * ξ₂)) by
              ring]
        rw [← intervalIntegral.integral_const_mul]
      rw [hstep]
      congr 1
      refine intervalIntegral.integral_congr fun t _ => ?_
      calc AM ξ₁ * BM ξ₂ * (mdlW1 P N t * ee (U t * ξ₁ + V t * ξ₂))
          = (ampMod N k₁ ξ₁ * ee (uphase N t * ξ₁))
              * (btilMod P N k₂ ξ₂ * ee (vphase P N t * ξ₂)) * mdlW1 P N t := by
            rw [hAM, hBM, hU, hV, Work.A7.ee_add_char]; ring
        _ = varphiNtj N k₁ 1 t ξ₁ * varphitildeNtj P N k₂ (-1) t ξ₂ * mdlW1 P N t := by
            rw [ampMod_val, btilMod_val]
    rw [hset, hFub]
    refine Eq.trans ?_ (MeasureTheory.integral_prod E3 hE3i).symm
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ξ₁ => ?_)
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ξ₂ => ?_)
    exact hpt ξ₁ ξ₂
  -- ### `L4 = ∫ E4`
  have hL4 : L4 = ∫ z : ℝ × ℝ, E4 z ∂(volume.prod volume) := by
    have hFub := CwFubiniWeight (a := AV) (b := BM) hAVi hBMi hAVm hBMm (u := U) (v := V) hum hvm
      (W := mdlW2 P N) hW2i hW2m i₁ i₂
    have hset : L4 = ∫ t in (1 / 2 : ℝ)..1, mdlW2 P N t
        * cw (fun ξ => AV ξ * ee (U t * ξ)) i₁ * cw (fun ξ => BM ξ * ee (V t * ξ)) i₂ := by
      rw [hL4eq]
      refine intervalIntegral.integral_congr fun t _ => ?_
      have h1 : cw (varphiNt N k₁ t) i₁ = cw (fun ξ => AV ξ * ee (U t * ξ)) i₁ := by
        rw [hAV, hU]; rfl
      have h2 : cw (varphitildeNtj P N k₂ (-1) t) i₂ = cw (fun ξ => BM ξ * ee (V t * ξ)) i₂ := by
        rw [hBM, hV, ← varphitildeNtj_funeq]
      calc cw (varphiNt N k₁ t) i₁ * cw (varphitildeNtj P N k₂ (-1) t) i₂ * mdlW2 P N t
          = cw (fun ξ => AV ξ * ee (U t * ξ)) i₁ * cw (fun ξ => BM ξ * ee (V t * ξ)) i₂
              * mdlW2 P N t := by rw [h1, h2]
        _ = mdlW2 P N t * cw (fun ξ => AV ξ * ee (U t * ξ)) i₁
              * cw (fun ξ => BM ξ * ee (V t * ξ)) i₂ := by ring
    have hpt : ∀ ξ₁ ξ₂ : ℝ, AV ξ₁ * BM ξ₂
        * (∫ t in (1 / 2 : ℝ)..1, mdlW2 P N t * ee (U t * ξ₁ + V t * ξ₂))
        * ee (-(i₁ : ℝ) * ξ₁ - (i₂ : ℝ) * ξ₂) = E4 (ξ₁, ξ₂) := by
      intro ξ₁ ξ₂
      simp only [hE4]
      have hstep : AV ξ₁ * BM ξ₂
            * (∫ t in (1 / 2 : ℝ)..1, mdlW2 P N t * ee (U t * ξ₁ + V t * ξ₂))
            * ee (-(i₁ : ℝ) * ξ₁ - (i₂ : ℝ) * ξ₂)
          = ee (-(i₁ : ℝ) * ξ₁ - (i₂ : ℝ) * ξ₂) * ∫ t in (1 / 2 : ℝ)..1,
              AV ξ₁ * BM ξ₂ * (mdlW2 P N t * ee (U t * ξ₁ + V t * ξ₂)) := by
        rw [show AV ξ₁ * BM ξ₂
              * (∫ t in (1 / 2 : ℝ)..1, mdlW2 P N t * ee (U t * ξ₁ + V t * ξ₂))
              * ee (-(i₁ : ℝ) * ξ₁ - (i₂ : ℝ) * ξ₂)
            = ee (-(i₁ : ℝ) * ξ₁ - (i₂ : ℝ) * ξ₂) * ((AV ξ₁ * BM ξ₂)
              * ∫ t in (1 / 2 : ℝ)..1, mdlW2 P N t * ee (U t * ξ₁ + V t * ξ₂)) by
              ring]
        rw [← intervalIntegral.integral_const_mul]
      rw [hstep]
      congr 1
      refine intervalIntegral.integral_congr fun t _ => ?_
      calc AV ξ₁ * BM ξ₂ * (mdlW2 P N t * ee (U t * ξ₁ + V t * ξ₂))
          = (varphiN N k₁ ξ₁ * ee (uphase N t * ξ₁))
              * (btilMod P N k₂ ξ₂ * ee (vphase P N t * ξ₂)) * mdlW2 P N t := by
            rw [hAV, hBM, hU, hV, Work.A7.ee_add_char]; ring
        _ = varphiNt N k₁ t ξ₁ * varphitildeNtj P N k₂ (-1) t ξ₂ * mdlW2 P N t := by
            rw [← varphiNt_val, btilMod_val]
    rw [hset, hFub]
    refine Eq.trans ?_ (MeasureTheory.integral_prod E4 hE4i).symm
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ξ₁ => ?_)
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ξ₂ => ?_)
    exact hpt ξ₁ ξ₂
  -- ### the pointwise (a.e.) identity
  have hpt : ∀ᵐ z : ℝ × ℝ ∂(volume.prod volume),
      E0 z = c0 * (E1 z * mdlW1 P N 1 - E2 z * mdlW1 P N (1 / 2)) - c1 * E3 z + c0 * E4 z := by
    have hnull : ∀ᵐ z : ℝ × ℝ ∂(volume.prod volume), z.2 ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      rw [show {z : ℝ × ℝ | ¬ (z.2 ≠ 0)} = Set.univ ×ˢ ({0} : Set ℝ) by ext z; simp]
      rw [MeasureTheory.Measure.prod_prod]
      simp
    filter_upwards [hnull] with z hz
    simp only [hE0, hE1, hE2, hE3, hE4]
    rw [MdlBumpIntegIdent P N k₁ k₂ hN hk₂ hP z.1 z.2 hz, ← hc0, ← hc1]
    ring
  -- ### linearity and conclusion
  have lin : (∫ z : ℝ × ℝ,
        (c0 * (E1 z * mdlW1 P N 1 - E2 z * mdlW1 P N (1 / 2)) - c1 * E3 z + c0 * E4 z)
        ∂(volume.prod volume))
      = c0 * (L1 * mdlW1 P N 1) - c0 * (L2 * mdlW1 P N (1 / 2)) - c1 * L3 + c0 * L4 := by
    have h1 : Integrable (fun z : ℝ × ℝ => c0 * (E1 z * mdlW1 P N 1)) (volume.prod volume) :=
      (hE1i.mul_const _).const_mul _
    have h2 : Integrable (fun z : ℝ × ℝ => c0 * (E2 z * mdlW1 P N (1 / 2)))
        (volume.prod volume) := (hE2i.mul_const _).const_mul _
    have h3 : Integrable (fun z : ℝ × ℝ => c1 * E3 z) (volume.prod volume) := hE3i.const_mul _
    have h4 : Integrable (fun z : ℝ × ℝ => c0 * E4 z) (volume.prod volume) := hE4i.const_mul _
    have h12 : Integrable (fun z : ℝ × ℝ =>
        c0 * (E1 z * mdlW1 P N 1) - c0 * (E2 z * mdlW1 P N (1 / 2))) (volume.prod volume) :=
      h1.sub h2
    have h123 : Integrable (fun z : ℝ × ℝ =>
        c0 * (E1 z * mdlW1 P N 1) - c0 * (E2 z * mdlW1 P N (1 / 2)) - c1 * E3 z)
        (volume.prod volume) := h12.sub h3
    rw [show (fun z : ℝ × ℝ =>
          c0 * (E1 z * mdlW1 P N 1 - E2 z * mdlW1 P N (1 / 2)) - c1 * E3 z + c0 * E4 z)
        = fun z : ℝ × ℝ => c0 * (E1 z * mdlW1 P N 1) - c0 * (E2 z * mdlW1 P N (1 / 2))
            - c1 * E3 z + c0 * E4 z from by funext z; ring]
    rw [MeasureTheory.integral_add h123 h4,
        MeasureTheory.integral_sub h12 h3, MeasureTheory.integral_sub h1 h2,
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_mul_const, MeasureTheory.integral_mul_const,
        ← hL1, ← hL2, ← hL3, ← hL4]
    try ring
  calc L0 = ∫ z : ℝ × ℝ, E0 z ∂(volume.prod volume) := hL0
    _ = ∫ z : ℝ × ℝ,
          (c0 * (E1 z * mdlW1 P N 1 - E2 z * mdlW1 P N (1 / 2)) - c1 * E3 z + c0 * E4 z)
          ∂(volume.prod volume) := MeasureTheory.integral_congr_ae hpt
    _ = c0 * (L1 * mdlW1 P N 1) - c0 * (L2 * mdlW1 P N (1 / 2)) - c1 * L3 + c0 * L4 := lin
    _ = c0 * (L1 * mdlW1 P N 1 - L2 * mdlW1 P N (1 / 2)) - c1 * L3 + c0 * L4 := by ring

end

end Work.KMTPlan.A6
