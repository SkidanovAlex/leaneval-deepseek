import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB4.B7Instance
import Submission.Work.BoseB4.BoxKernel
import Submission.Work.BoseB4.Exists_gram_iff
import Submission.Work.BoseB4.boxKernel_symm
import Submission.Work.BoseB4.realIP_sum_sum_nonneg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.BoxGram` — the box kernel is a Gram kernel (FS `eq:Commutator_general`, PSD form)

`Work.BoseB4.BoxKernel.realIP_qVec_qVec` computes the box kernel as the Gram
product of the localised plane waves:
`realIP (qVec ℓ k) (qVec ℓ k') = ℓ³ (χ̂²((k−k')ℓ) − χ̂(kℓ)χ̂(k'ℓ))`.  Since the
right-hand side is `ℓ³` times a Gram matrix of honest vectors of `L²(Λ)`, the box
kernel is **symmetric and positive semidefinite**, which is exactly the hypothesis
`hgram` of `Work.BoseB4.b7FockDataBox` (via `Work.BoseB4.Exists_gram_iff`, which
turns symmetry + PSD into coordinates `f : Mode → Fin m → ℝ` with
`gram (f i) (f j) = ccrKernel …`).

This module closes that gap: `exists_gram_ccrKernel` discharges `hgram`, so
`Work.BoseB4.b7FockDataBox` — and with it B7's `EstHyp.hasKernel` — carries no
hypothesis beyond the box data `B : BoxData` and the momentum assignment.
-/

noncomputable section

open scoped BigOperators Pointwise
open MeasureTheory Classical

namespace Work.BoseB4

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace BoxData

variable (B : BoxData)

/-- **Complex algebra of the projection expansion.**  For `c, d : ℝ` (so that the
scalars are fixed by conjugation), the real part of
`conj(A − cB)·(C − dD)` splits into the four real parts. -/
lemma re_conj_sub_mul_sub (A B C D : ℂ) (c d : ℝ) :
    ((starRingEnd ℂ) (A - (c : ℂ) * B) * (C - (d : ℂ) * D)).re
      = ((starRingEnd ℂ) A * C).re - d * ((starRingEnd ℂ) A * D).re
        - c * ((starRingEnd ℂ) B * C).re + c * d * ((starRingEnd ℂ) B * D).re := by
  simp only [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im]
  ring

/-- The integrand of `realIP (qVec ℓ k) (qVec ℓ k')`, in closed form: it is the
four-term real expression produced by the projection
`qVec ℓ k = e^{ikx}χ_Λ − χ̂(kℓ)θ`. -/
lemma conj_qVec_mul_qVec_re {ℓ : ℝ} (hℓ : 0 < ℓ) (k k' : ℝ³) (x : ℝ³) :
    ((starRingEnd ℂ) (B.qVec ℓ k x) * B.qVec ℓ k' x).re
      = (B.chiLam ℓ x) ^ 2 * Real.cos (inner ℝ (k' - k) x)
        - B.hatChi (ℓ • k') * (B.chiLam ℓ x * Real.cos (inner ℝ k x))
        - B.hatChi (ℓ • k) * (B.chiLam ℓ x * Real.cos (inner ℝ k' x))
        + B.hatChi (ℓ • k) * B.hatChi (ℓ • k')
            * (if x ∈ B.boxL ℓ then (1 : ℝ) else 0) := by
  rw [BoxData.qVec_apply, BoxData.qVec_apply, re_conj_sub_mul_sub,
    congrFun (modeVec_realIP_integrand B ℓ k k') x,
    realIP_modeVec_thetaFun_re B hℓ k x,
    B.realIP_thetaFun_modeVec_re hℓ k' x,
    congrFun (B.thetaFun_integrand_eq_indicator ℓ) x]
  rfl

/-- The integrand of `realIP (qVec ℓ k) (qVec ℓ k')` is integrable: it is the
four-term combination of the four integrable pieces of `Work.BoseB4.BoxKernel`. -/
lemma integrable_conj_qVec_qVec {ℓ : ℝ} (hℓ : 0 < ℓ) (k k' : ℝ³) :
    Integrable fun x : ℝ³ => ((starRingEnd ℂ) (B.qVec ℓ k x) * B.qVec ℓ k' x).re := by
  have h1 := B.integrable_chiLam_sq_mul_cos hℓ (k' - k)
  have h2 := B.integrable_chiLam_mul_cos hℓ k
  have h3 := B.integrable_chiLam_mul_cos hℓ k'
  have h4 : Integrable fun x : ℝ³ => (if x ∈ B.boxL ℓ then (1 : ℝ) else 0) :=
    B.integrable_boxL_indicator ℓ
  have hcomb : Integrable fun x : ℝ³ =>
      (B.chiLam ℓ x) ^ 2 * Real.cos (inner ℝ (k' - k) x)
        - B.hatChi (ℓ • k') * (B.chiLam ℓ x * Real.cos (inner ℝ k x))
        - B.hatChi (ℓ • k) * (B.chiLam ℓ x * Real.cos (inner ℝ k' x))
        + B.hatChi (ℓ • k) * B.hatChi (ℓ • k')
            * (if x ∈ B.boxL ℓ then (1 : ℝ) else 0) :=
    (((h1.sub (h2.const_mul (B.hatChi (ℓ • k')))).sub
        (h3.const_mul (B.hatChi (ℓ • k)))).add
      (h4.const_mul (B.hatChi (ℓ • k) * B.hatChi (ℓ • k'))))
  refine hcomb.congr (Filter.Eventually.of_forall fun x => ?_)
  exact (B.conj_qVec_mul_qVec_re hℓ k k' x).symm


/-- **The box kernel is positive semidefinite**: `Σ_{ij} c_i c_j K(k_i,k_j) ≥ 0`
(the quadratic form of the Gram matrix of the localised plane waves). -/
theorem boxKernel_quadform_nonneg {ℓ : ℝ} (hℓ : 0 < ℓ) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (k : ι → ℝ³) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * B.boxKernel ℓ (k i) (k j) := by
  have h := realIP_sum_sum_nonneg B (fun i => B.qVec ℓ (k i)) c
    (fun i j => B.integrable_conj_qVec_qVec hℓ (k i) (k j))
  have hident : ∀ i j : ι,
      B.realIP (B.qVec ℓ (k i)) (B.qVec ℓ (k j))
        = ℓ ^ 3 * B.boxKernel ℓ (k i) (k j) :=
    fun i j => realIP_qVec_qVec B hℓ (k i) (k j)
  have hrewrite : ∑ i, ∑ j, c i * c j * B.realIP (B.qVec ℓ (k i)) (B.qVec ℓ (k j))
      = ℓ ^ 3 * ∑ i, ∑ j, c i * c j * B.boxKernel ℓ (k i) (k j) := by
    simp only [hident]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hrewrite] at h
  exact nonneg_of_mul_nonneg_right h (by positivity)

end BoxData

/-- **`hgram` discharged.**  For every box data `B`, side `ℓ > 0` and momentum
assignment `kmom`, there are coordinates `f : Mode → Fin m → ℝ` whose Gram matrix
is FS `eq:Commutator_general`'s kernel `Work.BoseB7.ccrKernel` built from the box
data (`χ̂ = B.hatChi`, `χ̂² = B.hatChiSq`).  In particular the hypothesis `hgram`
of `Work.BoseB4.b7FockDataBox` is a theorem, not an assumption. -/
theorem exists_gram_ccrKernel (B : BoxData) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (kmom : Mode → ℝ³) :
    ∃ m : ℕ, ∃ f : Mode → Fin m → ℝ, ∀ i j : Mode,
      gram (f i) (f j) = BoseB7.ccrKernel ℓ B.hatChiSq B.hatChi (kmom i) (kmom j) := by
  refine (Exists_gram_iff (fun i j => BoseB7.ccrKernel ℓ B.hatChiSq B.hatChi (kmom i) (kmom j))).mpr
    ⟨fun i j => ?_, fun v => ?_⟩
  · simpa only [BoseB7.ccrKernel, BoxData.boxKernel] using
      boxKernel_symm B ℓ (kmom i) (kmom j)
  · have h := B.boxKernel_quadform_nonneg hℓ kmom v
    have heq : ∑ i, ∑ j, v i * v j *
          (BoseB7.ccrKernel ℓ B.hatChiSq B.hatChi (kmom i) (kmom j))
        = ∑ i, ∑ j, v i * (BoseB7.ccrKernel ℓ B.hatChiSq B.hatChi (kmom i) (kmom j)) * v j := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have h' : 0 ≤ ∑ i, ∑ j, v i * v j *
        (BoseB7.ccrKernel ℓ B.hatChiSq B.hatChi (kmom i) (kmom j)) := by
      simpa only [BoseB7.ccrKernel, BoxData.boxKernel] using h
    rwa [heq] at h'

end Work.BoseB4
