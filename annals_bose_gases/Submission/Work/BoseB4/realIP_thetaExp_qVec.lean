import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB4.BoxKernel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.realIP_thetaExp_qVec` — the θ-mode/χ-mode cross Gram product

FS's θ-modes `ã_s` and χ-modes `a_k` are not orthogonal: their commutator is the
cross kernel

    `[ã_s, a_k†] = ℓ⁻³⟨Q(e^{isx}θ), Q(e^{ikx}χ_Λ)⟩ = χ̂((k−s)ℓ)`,

which is `Work.BoseB7A.TildeData`'s `ccrX`.  In the unnormalised functions of
`Work.BoseB4.BoxData` this is

    `realIP (thetaExp ℓ s) (qVec ℓ k) = ℓ³ χ̂(ℓ(k−s))`,

*provided* the θ-mode is orthogonal to the condensate,
`realIP (thetaExp ℓ s) (thetaFun ℓ) = 0` — the Fourier orthogonality of the box
satisfied by the lattice momenta `s ∈ (2π/ℓ)ℤ³ ∖ {0}` (`∫_{Λ(ℓ)} e^{isx}dx = 0`).

This is the third block of the joint Gram matrix of the θ- and χ-modes
(`Work.BoseB4.exists_gram_jointKernel`).
-/

noncomputable section

open scoped BigOperators Pointwise
open MeasureTheory Classical

namespace Work.BoseB4

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- `Re(conj z · w) = Re z · Re w + Im z · Im w`. -/
lemma conj_mul_re_eq (z w : ℂ) :
    ((starRingEnd ℂ) z * w).re = z.re * w.re + z.im * w.im := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

namespace BoxData

variable (B : BoxData)

/-- The imaginary part of `conj θ · modeVec k` is `χ_Λ sin⟪k,x⟫`. -/
lemma conj_thetaFun_mul_modeVec_im {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℝ³) (x : ℝ³) :
    ((starRingEnd ℂ) (B.thetaFun ℓ x) * B.modeVec ℓ k x).im
      = B.chiLam ℓ x * Real.sin (inner ℝ k x) := by
  by_cases hx : x ∈ B.boxL ℓ
  · simp only [BoxData.thetaFun_apply, hx, if_true, BoxData.modeVec_apply, map_one, one_mul,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    rw [mul_comm Complex.I ((inner ℝ k x : ℝ) : ℂ), Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im]
    ring
  · have hchi : B.chiLam ℓ x = 0 := by
      by_contra hc
      exact hx (B.chiLam_supp hℓ hc)
    simp only [BoxData.thetaFun_apply, hx, if_false, map_zero, zero_mul, Complex.zero_im, hchi,
      mul_zero]

/-- The integrand of `realIP (thetaExp ℓ s) (modeVec ℓ k)`: it is
`χ_Λ cos⟪k−s,x⟫`. -/
lemma conj_thetaExp_mul_modeVec_re {ℓ : ℝ} (hℓ : 0 < ℓ) (s k : ℝ³) (x : ℝ³) :
    ((starRingEnd ℂ) (B.thetaExp ℓ s x) * B.modeVec ℓ k x).re
      = B.chiLam ℓ x * Real.cos (inner ℝ (k - s) x) := by
  have hconjθ : (starRingEnd ℂ) (B.thetaFun ℓ x) = B.thetaFun ℓ x := by
    by_cases hx : x ∈ B.boxL ℓ <;>
      simp only [BoxData.thetaFun_apply, hx, if_true, if_false, map_one, map_zero]
  have hsplit : (starRingEnd ℂ) (B.thetaExp ℓ s x) * B.modeVec ℓ k x
      = (starRingEnd ℂ) (Complex.exp (Complex.I * ((inner ℝ s x : ℝ) : ℂ)))
        * ((starRingEnd ℂ) (B.thetaFun ℓ x) * B.modeVec ℓ k x) := by
    simp only [BoxData.thetaExp_apply, map_mul]
    rw [hconjθ]
    ring
  rw [hsplit, conj_mul_re_eq,
    mul_comm Complex.I ((inner ℝ s x : ℝ) : ℂ), Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im,
    B.realIP_thetaFun_modeVec_re hℓ k x, B.conj_thetaFun_mul_modeVec_im hℓ k x,
    inner_sub_left, Real.cos_sub]
  ring

/-- The integrand of `realIP (thetaExp ℓ s) (thetaFun ℓ)`: the indicator of the
box times `cos⟪s,x⟫`. -/
lemma conj_thetaExp_mul_thetaFun_re (ℓ : ℝ) (s : ℝ³) (x : ℝ³) :
    ((starRingEnd ℂ) (B.thetaExp ℓ s x) * B.thetaFun ℓ x).re
      = Set.indicator (B.boxL ℓ) (fun x : ℝ³ => Real.cos (inner ℝ s x)) x := by
  by_cases hx : x ∈ B.boxL ℓ
  · rw [Set.indicator_of_mem hx]
    have hconjθ : (starRingEnd ℂ) (B.thetaFun ℓ x) = B.thetaFun ℓ x := by
      simp only [BoxData.thetaFun_apply, hx, if_true, map_one]
    have hsq : (starRingEnd ℂ) (B.thetaFun ℓ x) * B.thetaFun ℓ x = 1 := by
      rw [hconjθ]
      simp only [BoxData.thetaFun_apply, hx, if_true, map_one, one_mul]
    calc ((starRingEnd ℂ) (B.thetaExp ℓ s x) * B.thetaFun ℓ x).re
        = ((starRingEnd ℂ) (Complex.exp (Complex.I * ((inner ℝ s x : ℝ) : ℂ)))
            * ((starRingEnd ℂ) (B.thetaFun ℓ x) * B.thetaFun ℓ x)).re := by
          simp only [BoxData.thetaExp_apply, map_mul]
          rw [hconjθ]
          ring
      _ = Real.cos (inner ℝ s x) := by
          rw [hsq, mul_one, Complex.conj_re,
            mul_comm Complex.I ((inner ℝ s x : ℝ) : ℂ), Complex.exp_ofReal_mul_I_re]
  · rw [Set.indicator_of_notMem hx]
    have hθ : B.thetaFun ℓ x = (0 : ℂ) := by
      simp only [BoxData.thetaFun_apply, hx, if_false]
    simp only [hθ, mul_zero, Complex.zero_re]

/-- The indicator of the box times `cos⟪p,x⟫` is integrable (bounded, compactly
supported, the box of finite measure). -/
lemma integrable_indicator_cos (ℓ : ℝ) (p : ℝ³) :
    Integrable fun x : ℝ³ => (B.boxL ℓ).indicator (fun x : ℝ³ => Real.cos (inner ℝ p x)) x := by
  have hcs : HasCompactSupport
      (Set.indicator (B.boxL ℓ) (fun x : ℝ³ => Real.cos (inner ℝ p x))) :=
    (B.boxL_compact ℓ).of_isClosed_subset (isClosed_tsupport _)
      (closure_minimal (fun x hx => by
        by_contra hx'
        exact hx (by simp [Set.indicator_of_notMem, hx'])) (B.boxL_compact ℓ).isClosed)
  have hmeas : AEStronglyMeasurable
      (Set.indicator (B.boxL ℓ) (fun x : ℝ³ => Real.cos (inner ℝ p x))) volume :=
    AEStronglyMeasurable.indicator
      (Real.continuous_cos.comp (continuous_const.inner continuous_id)).aestronglyMeasurable
      (B.boxL_measurableSet ℓ)
  have hbdd : ∀ᵐ x ∂volume,
      ‖Set.indicator (B.boxL ℓ) (fun x : ℝ³ => Real.cos (inner ℝ p x)) x‖ ≤ 1 :=
    Filter.Eventually.of_forall fun x => by
      by_cases hx : x ∈ B.boxL ℓ
      · rw [Set.indicator_of_mem hx, Real.norm_eq_abs]
        exact Real.abs_cos_le_one _
      · rw [Set.indicator_of_notMem hx, norm_zero]
        norm_num
  exact (memLp_one_iff_integrable).mp (hcs.memLp_of_bound hmeas 1 hbdd)

/-- The integrand of `realIP (thetaExp ℓ s) (thetaFun ℓ)` is integrable. -/
lemma integrable_conj_thetaExp_thetaFun (ℓ : ℝ) (s : ℝ³) :
    Integrable fun x : ℝ³ => ((starRingEnd ℂ) (B.thetaExp ℓ s x) * B.thetaFun ℓ x).re :=
  (B.integrable_indicator_cos ℓ s).congr
    (Filter.Eventually.of_forall fun x => (B.conj_thetaExp_mul_thetaFun_re ℓ s x).symm)

/-- Real-part splitting of a one-sided projection: for `c : ℝ`,
`Re(conj a · (b − c d)) = Re(conj a · b) − c·Re(conj a · d)`. -/
lemma conj_mul_sub_re (a b d : ℂ) (c : ℝ) :
    ((starRingEnd ℂ) a * (b - (c : ℂ) * d)).re
      = ((starRingEnd ℂ) a * b).re - c * ((starRingEnd ℂ) a * d).re := by
  rw [mul_sub, Complex.sub_re,
    show (starRingEnd ℂ) a * ((c : ℂ) * d) = (c : ℂ) * ((starRingEnd ℂ) a * d) by ring,
    Complex.re_ofReal_mul]

/-- **The θ/χ cross Gram product.**  For a θ-mode momentum `s` orthogonal to the
condensate (`∫_{Λ}cos⟪s,x⟫ = 0`, the lattice condition), the cross Gram product of
the θ-mode and the localised plane wave is the (normalised) `χ̂`:
`⟨e^{isx}θ, Q(e^{ikx}χ_Λ)⟩ = ℓ³χ̂(ℓ(k−s))`.  This is `ccrX` of
`Work.BoseB7A.TildeData`. -/
theorem realIP_thetaExp_qVec (B : BoxData) {ℓ : ℝ} (hℓ : 0 < ℓ) (s k : ℝ³)
    (hs : B.realIP (B.thetaExp ℓ s) (B.thetaFun ℓ) = 0) :
    B.realIP (B.thetaExp ℓ s) (B.qVec ℓ k) = ℓ ^ 3 * B.hatChi (ℓ • (k - s)) := by
  have hint1 : Integrable fun x : ℝ³ =>
      ((starRingEnd ℂ) (B.thetaExp ℓ s x) * B.modeVec ℓ k x).re :=
    (B.integrable_chiLam_mul_cos hℓ (k - s)).congr
      (Filter.Eventually.of_forall fun x => (B.conj_thetaExp_mul_modeVec_re hℓ s k x).symm)
  have hint2 := B.integrable_conj_thetaExp_thetaFun ℓ s
  have hexp : B.realIP (B.thetaExp ℓ s) (B.qVec ℓ k)
      = B.realIP (B.thetaExp ℓ s) (B.modeVec ℓ k)
        - B.hatChi (ℓ • k) * B.realIP (B.thetaExp ℓ s) (B.thetaFun ℓ) := by
    rw [BoxData.realIP_apply, BoxData.realIP_apply, BoxData.realIP_apply]
    rw [show (fun x : ℝ³ => ((starRingEnd ℂ) (B.thetaExp ℓ s x) * B.qVec ℓ k x).re)
        = fun x : ℝ³ => ((starRingEnd ℂ) (B.thetaExp ℓ s x) * B.modeVec ℓ k x).re
            - B.hatChi (ℓ • k) * ((starRingEnd ℂ) (B.thetaExp ℓ s x) * B.thetaFun ℓ x).re from
      funext fun x => by rw [BoxData.qVec_apply, conj_mul_sub_re]]
    rw [MeasureTheory.integral_sub hint1 (hint2.const_mul _), MeasureTheory.integral_const_mul]
  rw [hexp, hs, mul_zero, sub_zero, BoxData.realIP_apply]
  rw [show (fun x : ℝ³ => ((starRingEnd ℂ) (B.thetaExp ℓ s x) * B.modeVec ℓ k x).re)
      = fun x : ℝ³ => B.chiLam ℓ x * Real.cos (inner ℝ (k - s) x) from
    funext fun x => B.conj_thetaExp_mul_modeVec_re hℓ s k x]
  exact B.integral_chiLam_mul_cos hℓ (k - s)

end BoxData

end Work.BoseB4
