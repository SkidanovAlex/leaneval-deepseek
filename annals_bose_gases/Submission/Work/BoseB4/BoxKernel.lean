import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Submission.Work.BoseB4.realIP_modeVec_modeVec
import Submission.Work.BoseB4.realIP_modeVec_thetaFun
import Submission.Work.BoseB4.realIP_sub_mul_sub
import Submission.Work.BoseB4.realIP_thetaFun_modeVec
import Submission.Work.BoseB4.realIP_thetaFun_thetaFun
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.BoxKernel` — FS `eq:Commutator_general`, proved

The main identity of the concrete `L²(Λ)` side of node B4: the commutator kernel
of FS's localised modes is the box kernel

    `[a_k, a_{k'}†] = ℓ⁻³ ⟨Q(e^{ikx}χ_Λ), Q(e^{ik'x}χ_Λ)⟩
                    = χ̂²((k−k')ℓ) − χ̂(kℓ) χ̂(k'ℓ)`,
    i.e. `B.realIP (B.qVec ℓ k) (B.qVec ℓ k') = ℓ³ · B.boxKernel ℓ k k'`,

with `B : Work.BoseB4.BoxData`, `qVec ℓ k = e^{ikx}χ_Λ − χ̂(kℓ)·θ` the localised
plane wave with its condensate component removed (`Q` of FS's `def:projections`)
and `boxKernel ℓ k k' = χ̂²(ℓ(k−k')) − χ̂(ℓk)χ̂(ℓk')` the kernel in the exact form of
`Work.BoseB7.ccrKernel`.

The three ingredients are all proved:

* `realIP_modeVec_modeVec`: `⟨e^{ikx}χ_Λ, e^{ik'x}χ_Λ⟩ = ℓ³ χ̂²(ℓ(k'−k))`;
* `realIP_modeVec_thetaFun`, `realIP_thetaFun_modeVec`,
  `realIP_thetaFun_thetaFun`: the condensate overlaps (`ℓ⁻³⟨θ, e^{ikx}χ_Λ⟩ = χ̂(kℓ)`,
  `‖θ‖² = volume Λ = ℓ³`);
* `realIP_sub_mul_sub`: the bilinear expansion of the projection, with
  integrability of the four pieces (proved here).
-/

noncomputable section

open scoped BigOperators Pointwise
open MeasureTheory Classical

namespace Work.BoseB4

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace BoxData

variable (B : BoxData)

/-! ## Supports and integrability of the explicit pieces -/

lemma tsupport_chiLam_subset {ℓ : ℝ} (hℓ : 0 < ℓ) : tsupport (B.chiLam ℓ) ⊆ B.boxL ℓ :=
  closure_minimal (B.chiLam_supp hℓ) (B.boxL_compact ℓ).isClosed

lemma tsupport_chiLam_sq_subset {ℓ : ℝ} (hℓ : 0 < ℓ) :
    tsupport (fun x : ℝ³ => (B.chiLam ℓ x) ^ 2) ⊆ B.boxL ℓ :=
  closure_minimal (fun x hx => by
    have hx' : B.chiLam ℓ x ^ 2 ≠ 0 := hx
    exact B.chiLam_supp hℓ fun h => hx' (by rw [h]; ring))
    (B.boxL_compact ℓ).isClosed

lemma continuous_cos_inner (p : ℝ³) : Continuous fun x : ℝ³ => Real.cos (inner ℝ p x) :=
  Real.continuous_cos.comp (continuous_const.inner continuous_id)

lemma integrable_chiLam_sq_mul_cos {ℓ : ℝ} (hℓ : 0 < ℓ) (p : ℝ³) :
    Integrable fun x : ℝ³ => (B.chiLam ℓ x) ^ 2 * Real.cos (inner ℝ p x) :=
  (((B.chiLam_cont ℓ).pow 2).mul (continuous_cos_inner p)).integrable_of_hasCompactSupport
    (HasCompactSupport.mul_right
      ((B.boxL_compact ℓ).of_isClosed_subset (isClosed_tsupport _)
        (B.tsupport_chiLam_sq_subset hℓ)))

lemma integrable_chiLam_mul_cos {ℓ : ℝ} (hℓ : 0 < ℓ) (p : ℝ³) :
    Integrable fun x : ℝ³ => B.chiLam ℓ x * Real.cos (inner ℝ p x) :=
  ((B.chiLam_cont ℓ).mul (continuous_cos_inner p)).integrable_of_hasCompactSupport
    (HasCompactSupport.mul_right
      ((B.boxL_compact ℓ).of_isClosed_subset (isClosed_tsupport _) (B.tsupport_chiLam_subset hℓ)))

lemma integrable_boxL_indicator (ℓ : ℝ) :
    Integrable fun x : ℝ³ => (B.boxL ℓ).indicator (fun _ => (1 : ℝ)) x := by
  rw [integrable_indicator_iff (B.boxL_measurableSet ℓ)]
  refine integrableOn_const (C := (1 : ℝ)) ?_
  rw [boxL, Measure.addHaar_smul, B.cell_vol, mul_one]
  exact ENNReal.ofReal_ne_top

/-! ## The four integrands of the projection expansion -/

lemma realIP_thetaFun_modeVec_re {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℝ³) (x : ℝ³) :
    ((starRingEnd ℂ) (B.thetaFun ℓ x) * B.modeVec ℓ k x).re
      = B.chiLam ℓ x * Real.cos (inner ℝ k x) := by
  by_cases hx : x ∈ B.boxL ℓ
  · simp only [BoxData.thetaFun_apply, hx, if_true, BoxData.modeVec_apply, map_one, one_mul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    rw [mul_comm Complex.I ((inner ℝ k x : ℝ) : ℂ), Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im]
    ring
  · have hchi : B.chiLam ℓ x = 0 := by
      by_contra hc
      exact hx (B.chiLam_supp hℓ hc)
    simp only [BoxData.thetaFun_apply, hx, if_false, map_zero, zero_mul, Complex.zero_re, hchi]

lemma integrable_conj_modeVec_modeVec {ℓ : ℝ} (hℓ : 0 < ℓ) (k k' : ℝ³) :
    Integrable fun x : ℝ³ =>
      ((starRingEnd ℂ) (B.modeVec ℓ k x) * B.modeVec ℓ k' x).re := by
  rw [modeVec_realIP_integrand B ℓ k k']
  exact B.integrable_chiLam_sq_mul_cos hℓ (k' - k)

lemma integrable_conj_modeVec_thetaFun {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℝ³) :
    Integrable fun x : ℝ³ => ((starRingEnd ℂ) (B.modeVec ℓ k x) * B.thetaFun ℓ x).re := by
  rw [show (fun x : ℝ³ => ((starRingEnd ℂ) (B.modeVec ℓ k x) * B.thetaFun ℓ x).re)
        = fun x : ℝ³ => B.chiLam ℓ x * Real.cos (inner ℝ k x) from
      funext fun x => realIP_modeVec_thetaFun_re B hℓ k x]
  exact B.integrable_chiLam_mul_cos hℓ k

lemma integrable_conj_thetaFun_modeVec {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℝ³) :
    Integrable fun x : ℝ³ => ((starRingEnd ℂ) (B.thetaFun ℓ x) * B.modeVec ℓ k x).re := by
  rw [show (fun x : ℝ³ => ((starRingEnd ℂ) (B.thetaFun ℓ x) * B.modeVec ℓ k x).re)
        = fun x : ℝ³ => B.chiLam ℓ x * Real.cos (inner ℝ k x) from
      funext fun x => B.realIP_thetaFun_modeVec_re hℓ k x]
  exact B.integrable_chiLam_mul_cos hℓ k

lemma integrable_conj_thetaFun_thetaFun (ℓ : ℝ) :
    Integrable fun x : ℝ³ => ((starRingEnd ℂ) (B.thetaFun ℓ x) * B.thetaFun ℓ x).re := by
  rw [B.thetaFun_integrand_eq_indicator ℓ]
  exact B.integrable_boxL_indicator ℓ

end BoxData

/-! ## FS `eq:Commutator_general` -/

/-- **FS `eq:Commutator_general`, proved.**  The Gram product of the localised
plane waves with their condensate component removed is `ℓ³` times the box kernel
`χ̂²((k−k')ℓ) − χ̂(kℓ)χ̂(k'ℓ)`; dividing by `ℓ³` and using
`[a_k, a_{k'}†] = ℓ⁻³⟨Q(e^{ikx}χ_Λ), Q(e^{ik'x}χ_Λ)⟩` this is exactly
`Work.BoseB7.ccrKernel`. -/
theorem realIP_qVec_qVec (B : BoxData) {ℓ : ℝ} (hℓ : 0 < ℓ) (k k' : ℝ³) :
    B.realIP (B.qVec ℓ k) (B.qVec ℓ k') = ℓ ^ 3 * B.boxKernel ℓ k k' := by
  have hq : ∀ j : ℝ³, B.qVec ℓ j
      = fun x : ℝ³ => B.modeVec ℓ j x - ((B.hatChi (ℓ • j) : ℝ) : ℂ) * B.thetaFun ℓ x :=
    fun j => rfl
  rw [hq k, hq k']
  rw [realIP_sub_mul_sub B (B.modeVec ℓ k) (B.thetaFun ℓ) (B.modeVec ℓ k') (B.thetaFun ℓ)
      (B.hatChi (ℓ • k)) (B.hatChi (ℓ • k'))
      (B.integrable_conj_modeVec_modeVec hℓ k k')
      (B.integrable_conj_modeVec_thetaFun hℓ k)
      (B.integrable_conj_thetaFun_modeVec hℓ k')
      (B.integrable_conj_thetaFun_thetaFun ℓ)]
  rw [realIP_modeVec_modeVec B hℓ k k', realIP_modeVec_thetaFun B hℓ k,
      realIP_thetaFun_modeVec B hℓ k', realIP_thetaFun_thetaFun B hℓ]
  have hsym : B.hatChiSq (ℓ • (k' - k)) = B.hatChiSq (ℓ • (k - k')) := by
    rw [← B.hatChiSq_neg (ℓ • (k - k')), ← smul_neg, neg_sub]
  rw [hsym, BoxData.boxKernel]
  ring

end Work.BoseB4
