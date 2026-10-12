import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.dictIIDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.dictIIAux.kBoundIntegral`

`kBound ℓ b` is the pointwise dominator of the `Q M Q` kernel `qmqKR ℓ b`
(see `Work.BoseBoxFock.norm_qmqKR_le_kBound`):

  `kBound ℓ b (w,y) = |b w y| + c·∫|b w ·| + c·∫|b · y| + c²·∬|b|`,   `c = |ℓ³|⁻¹`.

Writing `Λ = acube ℓ`, `μ = volume↾Λ` and `vol Λ = ℓ³`, the four rows integrate over
`μ ⊗ μ` to `∬|b|` each: the first by definition, the second and third by Fubini together with
`∫ 1 ∂μ = ℓ³`, the fourth likewise (`∫ 1 ∂μ = ℓ³` twice); and `c·ℓ³ = 1` because `ℓ > 0`.
Hence `kBound ℓ b` is integrable and its integral is *at most* four times `∬ |b|`.

The whole content is the Fubini computation on the product measure; there is no analytic input
beyond `ℓ > 0`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock.dictIIAux

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem kBoundIntegral {ℓ : ℝ} (hℓ : 0 < ℓ) {b : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hb : MeasureTheory.Integrable (Function.uncurry b) (Work.BoseBoxFock.acubePair ℓ)) :
    MeasureTheory.Integrable (Work.BoseBoxFock.kBound ℓ b) (Work.BoseBoxFock.acubePair ℓ) ∧
      ∫ p, Work.BoseBoxFock.kBound ℓ b p ∂(Work.BoseBoxFock.acubePair ℓ)
        ≤ 4 * ∫ p, |b p.1 p.2| ∂(Work.BoseBoxFock.acubePair ℓ) := by
  classical
  -- the measure `μ = volume ↾ Λ`, `Λ = acube ℓ`, and the identification `acubePair ℓ = μ ⊗ μ`
  set μ : Measure E3 := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ) with hμ
  have hpair : Work.BoseBoxFock.acubePair ℓ = μ.prod μ := by
    rw [Work.BoseBoxFock.acubePair, hμ]
  have hℓ3pos : (0 : ℝ) < ℓ ^ 3 := by positivity
  have hℓ3ne : ℓ ^ 3 ≠ 0 := ne_of_gt hℓ3pos
  have hvoluniv : (volume : Measure E3) (Submission.BoseGases.acube ℓ) = ENNReal.ofReal (ℓ ^ 3) :=
    Submission.BoseGases.acube_volume ℓ hℓ.le
  have hμuniv : μ Set.univ = ENNReal.ofReal (ℓ ^ 3) := by
    rw [hμ, Measure.restrict_apply_univ, hvoluniv]
  have hμfin : IsFiniteMeasure μ :=
    MeasureTheory.isFiniteMeasure_restrict.mpr (by rw [hvoluniv]; exact ENNReal.ofReal_ne_top)
  have hμreal : μ.real Set.univ = ℓ ^ 3 := by
    rw [Measure.real_def, hμuniv, ENNReal.toReal_ofReal hℓ3pos.le]
  -- the normalising constant and `c·ℓ³ = 1`
  set c : ℝ := (ℓ ^ 3)⁻¹ with hc
  have hlc : ℓ ^ 3 * c = 1 := by rw [hc, mul_inv_cancel₀ hℓ3ne]
  have hcabsl : |(ℓ ^ 3)⁻¹| = c := by
    rw [hc]; exact abs_of_pos (inv_pos.mpr hℓ3pos)
  -- the four rows of `kBound`, as functions on `Λ × Λ`
  set F1 : E3 × E3 → ℝ := fun p => |b p.1 p.2| with hF1
  set F2 : E3 × E3 → ℝ := fun p => (∫ y, |b p.1 y| ∂μ) * c with hF2
  set F3 : E3 × E3 → ℝ := fun p => c * (∫ w, |b w p.2| ∂μ) with hF3
  set F4 : E3 × E3 → ℝ := fun p => (∫ w, ∫ y, |b w y| ∂μ ∂μ) * (c * c) with hF4
  set I : ℝ := ∫ p : E3 × E3, |b p.1 p.2| ∂(μ.prod μ) with hIdef
  -- integrability of the four rows
  have hI1 : Integrable F1 (μ.prod μ) := by
    have h := hb.norm
    rw [hpair] at h
    simp only [hF1]
    simpa [Function.uncurry, Real.norm_eq_abs] using h
  have hIeq : I = ∫ w, ∫ y, |b w y| ∂μ ∂μ := by
    rw [hIdef]
    exact MeasureTheory.integral_prod (fun p : E3 × E3 => |b p.1 p.2|) hI1
  have hIeq' : I = ∫ y, ∫ w, |b w y| ∂μ ∂μ := by
    rw [hIdef]
    exact MeasureTheory.integral_prod_symm (fun p : E3 × E3 => |b p.1 p.2|) hI1
  have hG2 : Integrable (fun w : E3 => ∫ y, |b w y| ∂μ) μ := by
    have h := MeasureTheory.Integrable.integral_prod_left (ν := μ) hI1
    simpa only [hF1] using h
  have hG3 : Integrable (fun y : E3 => ∫ w, |b w y| ∂μ) μ := by
    have h := MeasureTheory.Integrable.integral_prod_right (μ := μ) hI1
    simpa only [hF1] using h
  have hF2int : Integrable F2 (μ.prod μ) := by
    simp only [hF2]
    exact hG2.mul_prod (integrable_const c)
  have hF3int : Integrable F3 (μ.prod μ) := by
    simp only [hF3]
    exact (integrable_const c).mul_prod hG3
  have hF4int : Integrable F4 (μ.prod μ) := by
    simp only [hF4]
    exact integrable_const _
  -- the pointwise identification of `kBound` with the sum of the four rows
  have hpt : ∀ p : E3 × E3, F1 p + F2 p + F3 p + F4 p = Work.BoseBoxFock.kBound ℓ b p := by
    intro p
    have h1 : (∫ y' in Submission.BoseGases.acube ℓ, |b p.1 y'|) = ∫ y, |b p.1 y| ∂μ := by
      rw [← hμ]
    have h3 : (∫ w' in Submission.BoseGases.acube ℓ, |b w' p.2|) = ∫ w, |b w p.2| ∂μ := by
      rw [← hμ]
    have h4 : (∫ w' in Submission.BoseGases.acube ℓ,
        ∫ y' in Submission.BoseGases.acube ℓ, |b w' y'|) = ∫ w, ∫ y, |b w y| ∂μ ∂μ := by
      rw [← hμ]
    simp only [hF1, hF2, hF3, hF4, Work.BoseBoxFock.kBound, h1, h3, h4, hcabsl]
    ring
  have hAint : Integrable (fun p : E3 × E3 => F1 p + F2 p) (μ.prod μ) := hI1.add hF2int
  have hBint : Integrable (fun p : E3 × E3 => F1 p + F2 p + F3 p) (μ.prod μ) := hAint.add hF3int
  have hCint : Integrable (fun p : E3 × E3 => F1 p + F2 p + F3 p + F4 p) (μ.prod μ) :=
    hBint.add hF4int
  have hkBint : Integrable (Work.BoseBoxFock.kBound ℓ b) (μ.prod μ) :=
    hCint.congr (Filter.Eventually.of_forall hpt)
  -- the value of the integral: each row contributes `I`
  have hval1 : ∫ p, F1 p ∂(μ.prod μ) = I := by
    simp only [hF1]
    exact hIdef.symm
  have hv2 : ∫ p, F2 p ∂(μ.prod μ) = I := by
    have hmul : ∫ p, F2 p ∂(μ.prod μ)
        = (∫ w, ∫ y, |b w y| ∂μ ∂μ) * (∫ y, c ∂μ) :=
      MeasureTheory.integral_prod_mul (fun w : E3 => ∫ y, |b w y| ∂μ) (fun _ : E3 => c)
    rw [hmul, MeasureTheory.integral_const, hμreal, smul_eq_mul, ← hIeq, hlc, mul_one]
  have hv3 : ∫ p, F3 p ∂(μ.prod μ) = I := by
    have hmul : ∫ p, F3 p ∂(μ.prod μ)
        = (∫ _ : E3, c ∂μ) * (∫ y, ∫ w, |b w y| ∂μ ∂μ) :=
      MeasureTheory.integral_prod_mul (fun _ : E3 => c) (fun y : E3 => ∫ w, |b w y| ∂μ)
    rw [hmul, MeasureTheory.integral_const, hμreal, smul_eq_mul, hlc, one_mul, ← hIeq']
  have hv4 : ∫ p, F4 p ∂(μ.prod μ) = I := by
    have hmul : ∫ p, F4 p ∂(μ.prod μ)
        = (∫ _ : E3, (∫ w, ∫ y, |b w y| ∂μ ∂μ) ∂μ) * (∫ _ : E3, c * c ∂μ) :=
      MeasureTheory.integral_prod_mul (fun _ : E3 => (∫ w, ∫ y, |b w y| ∂μ ∂μ))
        (fun _ : E3 => c * c)
    rw [hmul, MeasureTheory.integral_const, MeasureTheory.integral_const, hμreal, smul_eq_mul,
      smul_eq_mul, ← hIeq]
    rw [show (ℓ ^ 3 * I) * (ℓ ^ 3 * (c * c)) = I * ((ℓ ^ 3 * c) * (ℓ ^ 3 * c)) by ring]
    simp only [hlc, mul_one]
  have hval : ∫ p, Work.BoseBoxFock.kBound ℓ b p ∂(μ.prod μ) = 4 * I := by
    have hcongr : ∫ p, Work.BoseBoxFock.kBound ℓ b p ∂(μ.prod μ)
        = ∫ p, F1 p + F2 p + F3 p + F4 p ∂(μ.prod μ) :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => (hpt p).symm)
    rw [hcongr, MeasureTheory.integral_add hBint hF4int, MeasureTheory.integral_add hAint hF3int,
      MeasureTheory.integral_add hI1 hF2int, hval1, hv2, hv3, hv4]
    ring
  refine ⟨?_, ?_⟩
  · rw [hpair]; exact hkBint
  · rw [hpair, hval, ← hIdef]

end Work.BoseBoxFock.dictIIAux
