import Mathlib
import Submission.Work.BoseBoxFock.etaHRow_kinetic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `qVec`-coefficient of an `L²` state is the transform of the windowed mean-free state

The proved sibling `Work.BoseBoxFock.etaHKin_qVec_overlap_eq_kinFT` states

    `∫ conj(qVec ℓ k)·u = kinFT (χ_Λ·cboxQ ℓ u) k`

under the hypotheses that `u` is measurable, *bounded* and *supported in the box* `Λ = boxL ℓ`.
The present file removes the boundedness and the support hypothesis, keeping only `u ∈ L²(ℝ³)`
(`hu : MemLp u 2 volume`), which is what the `Q₂`/`η_H` row actually supplies.

Mathematically nothing changes: `qVec ℓ k` is bounded with support in `Λ`, so the pairing and the
two `Q`-corrections are still ordinary integrals; only the measure-theoretic bookkeeping has to be
redone, since `u ∈ L²` is not integrable on `ℝ³` (it is only integrable on the box, a finite
measure set) and `u` is only a.e.-measurable.

The proof splits the two sides as

* `∫ conj(qVec)·u = ∫ conj(modeVec)·u − χ̂(ℓk)·∫_Λ u`  (`qVec_LHS_expand`), and
* `kinFT (χ_Λ·cboxQ u) k = ∫ (e^{−i⟪k,·⟫}χ_Λ)·u − ℓ⁻³(∫_Λ u)·(ℓ³χ̂(ℓk))`  (`kinFT_RHS_expand`),

and matches the two displays pointwise (`star_modeVec_eq`) and by the scalar identity
`ℓ⁻³(∫_Λ u)·ℓ³χ̂(ℓk) = χ̂(ℓk)·∫_Λ u` (`scalar_key`).  The integrability inputs are supplied by
`integrable_mul_of_memLp_two`, which multiplies `u ∈ L²` with a bounded measurable function
vanishing outside the box via Hölder (`MemLp.mul'` with `2,2 ↦ 1`).
-/

namespace Work.BoseBoxFock

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

noncomputable section

/-! ## 1. A bounded, box-supported factor times an `L²` function is integrable -/

/-- **Hölder bookkeeping.**  If `g` is measurable, bounded and vanishes outside a set `s` of finite
measure and `u ∈ L²`, then `g·u` is integrable: `g ∈ L²` (bounded with support of finite measure)
and `L²·L² ⊆ L¹` by Hölder. -/
private theorem integrable_mul_of_memLp_two {s : Set E3} (hsf : volume s < ⊤) {g u : E3 → ℂ}
    (hg : Measurable g) (hb : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C) (hsup : ∀ x, x ∉ s → g x = 0)
    (hu : MemLp u 2 (volume : Measure E3)) : Integrable (fun x => g x * u x) := by
  have hg2 : MemLp g 2 (volume : Measure E3) :=
    memLp_two_of_bounded_support hsf hg hb fun x hx => by
      by_contra h
      exact hx (hsup x h)
  exact memLp_one_iff_integrable.mp (hg2.mul' hu)

/-! ## 2. The two expansions -/

/-- **Left-hand side expansion.**  Writing `qVec = modeVec − χ̂(ℓk)·θ_Λ` (`θ_Λ = 1_Λ` real),

    `∫ conj(qVec ℓ k)·u = ∫ conj(modeVec ℓ k)·u − χ̂(ℓk)·∫_Λ u`,

which requires no hypothesis on `u` beyond `u ∈ L²`. -/
private lemma qVec_LHS_expand {ℓ : ℝ} (hℓ : 0 < ℓ) (k : E3) {u : E3 → ℂ}
    (hu : MemLp u 2 (volume : Measure E3)) :
    (∫ x, (starRingEnd ℂ) (Work.BoseK15.corpusBox.qVec ℓ k x) * u x)
      = (∫ x, (starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k x) * u x)
        - ((Work.BoseK15.corpusBox.hatChi (ℓ • k) : ℝ) : ℂ)
          * (∫ x in Work.BoseK15.corpusBox.boxL ℓ, u x) := by
  have hBfin : volume (Work.BoseK15.corpusBox.boxL ℓ) < ⊤ := volume_boxL_lt_top ℓ hℓ
  have hIm : Integrable (fun x => (starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k x) * u x) :=
    integrable_mul_of_memLp_two hBfin
      ((Complex.continuous_conj.comp (continuous_modeVec ℓ k)).measurable)
      ⟨(Real.sqrt Submission.BoseGases.chiNormSq)⁻¹, fun x => by
        rw [starRingEnd_apply, norm_star]; exact norm_modeVec_le ℓ k x⟩
      (fun x hx => by
        rw [star_modeVec_eq, chiLam_eq_chiScale,
          chiScale_eq_zero_of_notMem hℓ hx, Complex.ofReal_zero, mul_zero]) hu
  have hIt : Integrable (fun x => (starRingEnd ℂ) (Work.BoseK15.corpusBox.thetaFun ℓ x) * u x) :=
    integrable_mul_of_memLp_two hBfin
      (Complex.continuous_conj.measurable.comp (measurable_thetaFun ℓ))
      ⟨1, fun x => by rw [starRingEnd_apply, norm_star]; exact norm_thetaFun_le ℓ x⟩
      (fun x hx => by
        rw [Work.BoseB4.BoxData.thetaFun_apply, if_neg hx, map_zero]) hu
  rw [show (∫ x, (starRingEnd ℂ) (Work.BoseK15.corpusBox.qVec ℓ k x) * u x)
      = ∫ x, ((starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k x) * u x
          - ((Work.BoseK15.corpusBox.hatChi (ℓ • k) : ℝ) : ℂ)
            * ((starRingEnd ℂ) (Work.BoseK15.corpusBox.thetaFun ℓ x) * u x)) from
    integral_congr_ae (Filter.Eventually.of_forall fun x => by
      beta_reduce
      rw [Work.BoseB4.BoxData.qVec_apply, map_sub, map_mul, Complex.conj_ofReal]; ring)]
  rw [integral_sub hIm (hIt.const_mul _), integral_const_mul,
    integral_star_thetaFun_mul_c u]

/-- **Right-hand side expansion.**  With `cboxQ ℓ u = u − ℓ⁻³(∫_Λ u)·1_Λ` and
`conj(modeVec ℓ k) = e^{−i⟪k,·⟫}χ_Λ`,

    `kinFT (χ_Λ·cboxQ ℓ u) k = ∫ (e^{−i⟪k,·⟫}χ_Λ)·u − ℓ⁻³(∫_Λ u)·∫ conj(modeVec ℓ k)`. -/
private lemma kinFT_RHS_expand {ℓ : ℝ} (hℓ : 0 < ℓ) (k : E3) {u : E3 → ℂ}
    (hu : MemLp u 2 (volume : Measure E3)) :
    Submission.BoseGases.kinFT (fun z => ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ)
        * cboxQ ℓ u z) k
      = (∫ z, (Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
            * ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ)) * u z)
        - (((ℓ : ℂ) ^ 3)⁻¹ * (∫ x in Work.BoseK15.corpusBox.boxL ℓ, u x))
          * ((ℓ ^ 3 * Work.BoseK15.corpusBox.hatChi (ℓ • k) : ℝ) : ℂ) := by
  classical
  have hBfin : volume (Work.BoseK15.corpusBox.boxL ℓ) < ⊤ := volume_boxL_lt_top ℓ hℓ
  have hBmeas : MeasurableSet (Work.BoseK15.corpusBox.boxL ℓ) :=
    Work.BoseK15.corpusBox.boxL_measurableSet ℓ
  have hchi0 : ∀ z, z ∉ Work.BoseK15.corpusBox.boxL ℓ →
      ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ) = 0 := fun z hz => by
    rw [chiScale_eq_zero_of_notMem hℓ hz, Complex.ofReal_zero]
  have hmeasE : Measurable (fun z : E3 => Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))) :=
    (by fun_prop : Continuous (fun z : E3 =>
      Complex.exp (-(Complex.I * (inner ℝ k z : ℂ))))).measurable
  have hmeasChi : Measurable (fun z : E3 =>
      ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.comp (Submission.BoseGases.chiScale_continuous ℓ)).measurable
  have hbound : ∀ z : E3, ‖Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
      * ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ)‖ ≤
      (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ := by
    intro z
    rw [norm_mul, Complex.norm_exp]
    have hre : (-(Complex.I * (inner ℝ k z : ℂ))).re = 0 := by
      rw [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
        Complex.ofReal_re]
      ring
    rw [hre, Real.exp_zero, one_mul]
    simpa using Submission.BoseGases.abs_chiScale_le ℓ z
  have hI1 : Integrable (fun z => (Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
        * ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ)) * u z) :=
    integrable_mul_of_memLp_two hBfin (hmeasE.mul hmeasChi) ⟨_, hbound⟩
      (fun z hz => by rw [hchi0 z hz, mul_zero]) hu
  have hGint : Integrable (fun z => Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
        * ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ)
        * Set.indicator (Work.BoseK15.corpusBox.boxL ℓ) (fun _ : E3 => (1 : ℂ)) z) :=
    integrable_of_bounded_support hBfin
      ((hmeasE.mul hmeasChi).mul (measurable_const.indicator hBmeas))
      ⟨(Real.sqrt Submission.BoseGases.chiNormSq)⁻¹, fun z => by
        have hIle : ‖Set.indicator (Work.BoseK15.corpusBox.boxL ℓ)
            (fun _ : E3 => (1 : ℂ)) z‖ ≤ 1 := by
          rw [Set.indicator_apply]; split <;> simp
        calc ‖Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
              * ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ)
              * Set.indicator (Work.BoseK15.corpusBox.boxL ℓ) (fun _ : E3 => (1 : ℂ)) z‖
            = ‖Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
                * ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ)‖
              * ‖Set.indicator (Work.BoseK15.corpusBox.boxL ℓ) (fun _ : E3 => (1 : ℂ)) z‖ :=
              norm_mul _ _
          _ ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ * 1 :=
              mul_le_mul (hbound z) hIle (norm_nonneg _)
                (inv_nonneg.mpr (Real.sqrt_nonneg _))
          _ = (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ := mul_one _⟩
      (fun z hz => by
        by_contra hzB
        apply hz
        beta_reduce
        rw [hchi0 z hzB]; ring)
  -- The windowed exponential against the box indicator is `conj(modeVec)`.
  have hG_eq : (∫ z, Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
        * ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ)
        * Set.indicator (Work.BoseK15.corpusBox.boxL ℓ) (fun _ : E3 => (1 : ℂ)) z)
      = ∫ z, (starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k z) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    beta_reduce
    rw [star_modeVec_eq, chiLam_eq_chiScale]
    by_cases hz : z ∈ Work.BoseK15.corpusBox.boxL ℓ
    · rw [Set.indicator_of_mem hz, mul_one]
    · rw [Set.indicator_of_notMem hz, mul_zero, hchi0 z hz, mul_zero]
  rw [Submission.BoseGases.kinFT]
  beta_reduce
  rw [show (∫ z, Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
          * (((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ) * cboxQ ℓ u z))
      = ∫ z, ((Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
            * ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ)) * u z
          - (((ℓ : ℂ) ^ 3)⁻¹ * (∫ x in Work.BoseK15.corpusBox.boxL ℓ, u x))
            * (Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
              * ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ)
              * Set.indicator (Work.BoseK15.corpusBox.boxL ℓ) (fun _ : E3 => (1 : ℂ)) z)) from
    integral_congr_ae (Filter.Eventually.of_forall fun z => by
      beta_reduce
      rw [cboxQ]; ring)]
  rw [integral_sub hI1 (hGint.const_mul _), integral_const_mul, hG_eq,
    integral_star_modeVec hℓ k]

/-! ## 3. The scalar identity `ℓ⁻³(∫_Λ u)·ℓ³χ̂(ℓk) = χ̂(ℓk)·∫_Λ u` -/

private lemma scalar_key {ℓ : ℝ} (hℓ : 0 < ℓ) (B H : ℂ) :
    (((ℓ : ℂ) ^ 3)⁻¹ * B) * (((ℓ ^ 3 : ℝ) : ℂ) * H) = H * B := by
  have hL : ((ℓ : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hℓ)
  have h3 : (((ℓ ^ 3 : ℝ)) : ℂ) = ((ℓ : ℂ)) ^ 3 := by push_cast; ring
  rw [h3]
  field_simp

/-! ## 4. The theorem -/

theorem qVec_overlap_eq_kinFT_L2 {ℓ : ℝ} (hℓ : 0 < ℓ) (k : EuclideanSpace ℝ (Fin 3))
    {u : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hu : MeasureTheory.MemLp u 2
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) :
    (∫ x : EuclideanSpace ℝ (Fin 3),
        (starRingEnd ℂ) (Work.BoseK15.corpusBox.qVec ℓ k x) * u x)
      = Submission.BoseGases.kinFT
          (fun z : EuclideanSpace ℝ (Fin 3) =>
            ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ) * Work.BoseBoxFock.cboxQ ℓ u z) k := by
  have hA : (∫ x, (starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k x) * u x)
      = ∫ x, (Complex.exp (-(Complex.I * (inner ℝ k x : ℂ)))
          * ((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ)) * u x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [star_modeVec_eq, chiLam_eq_chiScale]
  have hsc : ((Work.BoseK15.corpusBox.hatChi (ℓ • k) : ℝ) : ℂ)
        * (∫ x in Work.BoseK15.corpusBox.boxL ℓ, u x)
      = (((ℓ : ℂ) ^ 3)⁻¹ * (∫ x in Work.BoseK15.corpusBox.boxL ℓ, u x))
        * ((ℓ ^ 3 * Work.BoseK15.corpusBox.hatChi (ℓ • k) : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul]
    exact (scalar_key hℓ _ _).symm
  rw [qVec_LHS_expand hℓ k hu, kinFT_RHS_expand hℓ k hu, hA, hsc]

end

end Work.BoseBoxFock
