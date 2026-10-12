import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Submission.Work.BoseBoxFock.mom2Summable
import Submission.Work.BoseKinLoc.Momentum.memLp_kinFT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The momentum second moment of the box lattice (`S₂ = R₂`)

For `ℓ > 0` and `g : ℝ³ → ℂ` smooth with `tsupport g ⊆ B(0,ℓ/2)`, the second lattice moment of
the `p`-convention Fourier transform agrees with its continuum counterpart:

`Σ_n ℓ⁻³‖k_n‖²‖kinFT g (k_n)‖² = (2π)⁻³ ∫_p ‖p‖²‖kinFT g p‖²`,  `k_n = kmomInt ℓ n = ℓ⁻¹•n`.

The proof trades the weight `‖k_n‖²` for a sum over the three directional derivatives:
the complex-valued chain rule for `kinFT` (`kinFT_fderiv_applyC`, the complex twin of the
corpus's `kinFT_fderiv_apply`) gives the *pointwise* identity

`‖p‖²‖kinFT g p‖² = Σ_i ‖kinFT (∂_i g) p‖²`   (`∂_i g = fderiv ℝ g · e_i`),

so each lattice side is the `j = 0` frame identity `frame_lattice_ball` applied to `∂_i g`
(after exchanging the finite `Fin 3`-sum with the `tsum`, licensed by the summability
`mom2Summable`), and the same pointwise identity converts the right-hand side into the sum of
the corresponding continuum integrals (`integral_finsetSum`, licensed by the integrability
`memLp_kinFT` of the transform of a smooth compactly supported state).
-/

open MeasureTheory
open scoped Pointwise

namespace Work.BoseBoxFock

/-! ## Auxiliary lemmas -/

/-- The ball `B(0,ℓ/2)` is contained in the box `Λ(ℓ) = boxL ℓ = ℓ • [-1/2,1/2]³`.  Coordinates
of an element of the ball are bounded by its norm. -/
lemma ball_subset_corpusBox_boxL {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Metric.ball (0 : ℝ³) (ℓ/2) ⊆ Work.BoseK15.corpusBox.boxL ℓ := by
  intro x hx
  rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hx
  show x ∈ (ℓ : ℝ) • (Work.BoseB4.unitCell : Set ℝ³)
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ (ne_of_gt hℓ)]
  intro i
  rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  have h1 : ‖x.ofLp i‖ ≤ ‖x‖ := by
    rw [EuclideanSpace.norm_eq]
    exact Real.le_sqrt_of_sq_le
      (Finset.single_le_sum (fun j _ => sq_nonneg ‖x.ofLp j‖) (Finset.mem_univ i))
  have h2 : |x.ofLp i| ≤ ‖x‖ := by rwa [Real.norm_eq_abs] at h1
  have h3 : |ℓ⁻¹ * x.ofLp i| < (1:ℝ)/2 := by
    rw [abs_mul, abs_inv, abs_of_pos hℓ]
    have h4 : ℓ⁻¹ * ‖x‖ < ℓ⁻¹ * (ℓ/2) :=
      mul_lt_mul_of_pos_left hx (inv_pos.mpr hℓ)
    have h5 : ℓ⁻¹ * (ℓ/2) = 1/2 := by field_simp
    rw [h5] at h4
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left h2 (le_of_lt (inv_pos.mpr hℓ))) h4
  exact le_of_lt h3

/-- **The chain rule for `kinFT` of a complex-valued state.**  For `g : ℝ³ → ℂ` smooth of compact
support, the `p`-convention Fourier transform of the `i`-th directional derivative is
`i⟪k,e_i⟫` times the transform of `g`.  (Complex twin of `kinFT_fderiv_apply`.) -/
theorem kinFT_fderiv_applyC {g : ℝ³ → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) (k : ℝ³) (i : Fin 3) :
    Submission.BoseGases.kinFT
        (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) k
      = Complex.I * ((inner ℝ k (Submission.BoseGases.kcStdBasis i) : ℝ) : ℂ)
          * Submission.BoseGases.kinFT g k := by
  have hInt : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
  have hDiff : Differentiable ℝ g := hg.differentiable (by simp)
  have hInt' : Integrable (fderiv ℝ g) :=
    (hg.continuous_fderiv (by simp)).integrable_of_hasCompactSupport (hgc.fderiv ℝ)
  have key := Real.fourier_fderiv (f := g) hInt hDiff hInt'
  -- Mathlib's `Real.fourier_fderiv` in the convention of `kinFT`
  have hdir : ∀ v : ℝ³,
      FourierTransform.fourier (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) v
        = (2 * Real.pi * Complex.I * ((inner ℝ v (Submission.BoseGases.kcStdBasis i) : ℝ) : ℂ))
            * FourierTransform.fourier g v := by
    intro v
    have h1 : FourierTransform.fourier
          (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) v
        = (FourierTransform.fourier (fderiv ℝ g) v) (Submission.BoseGases.kcStdBasis i) :=
      (Real.fourier_continuousLinearMap_apply (f := fderiv ℝ g)
        (a := Submission.BoseGases.kcStdBasis i) (v := v) hInt').symm
    have h2 : (FourierTransform.fourier (fderiv ℝ g) v) (Submission.BoseGases.kcStdBasis i)
        = (VectorFourier.fourierSMulRight (-innerSL ℝ)
            (FourierTransform.fourier g) v) (Submission.BoseGases.kcStdBasis i) :=
      congrArg (fun (T : ℝ³ →L[ℝ] ℂ) => T (Submission.BoseGases.kcStdBasis i))
        (congrFun key v)
    rw [h1, h2]
    simp only [VectorFourier.fourierSMulRight_apply, neg_apply, Complex.real_smul]
    rw [innerSL_apply_apply]
    push_cast
    ring
  rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier,
    Work.SmallBoxBridge.Resolve.kinFT_eq_fourier, hdir]
  rw [real_inner_smul_left]
  have hscalar : (2 * (Real.pi : ℂ) * Complex.I
        * ((((2 * Real.pi)⁻¹ * (inner ℝ k (Submission.BoseGases.kcStdBasis i) : ℝ) : ℝ)) : ℂ))
      = Complex.I * ((inner ℝ k (Submission.BoseGases.kcStdBasis i) : ℝ) : ℂ) := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
  rw [hscalar]

/-- **The pointwise second-moment identity.**  For `g : ℝ³ → ℂ` smooth of compact support and
every momentum `k`, the squared momentum times the squared modulus of the transform is the sum
over the three coordinate directions of the squared modulus of the transform of the
corresponding directional derivative. -/
theorem normSq_kinFT_eq_sum_normSq_fderiv {g : ℝ³ → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) (k : ℝ³) :
    ‖k‖ ^ 2 * ‖Submission.BoseGases.kinFT g k‖ ^ 2
      = ∑ i : Fin 3, ‖Submission.BoseGases.kinFT
          (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) k‖ ^ 2 := by
  have hterm : ∀ i : Fin 3,
      Submission.BoseGases.kinFT
          (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) k
        = Complex.I * ((inner ℝ k (Submission.BoseGases.kcStdBasis i) : ℝ) : ℂ)
            * Submission.BoseGases.kinFT g k :=
    fun i => kinFT_fderiv_applyC hg hgc k i
  simp_rw [hterm]
  have h1 : ∀ i : Fin 3,
      ‖Complex.I * ((inner ℝ k (Submission.BoseGases.kcStdBasis i) : ℝ) : ℂ)
          * Submission.BoseGases.kinFT g k‖ ^ 2
        = (inner ℝ k (Submission.BoseGases.kcStdBasis i)) ^ 2
            * ‖Submission.BoseGases.kinFT g k‖ ^ 2 := by
    intro i
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_I,
      one_mul, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq]
    ring
  rw [Finset.sum_congr rfl (fun i _ => h1 i)]
  rw [← Finset.sum_mul, Work.SmallBoxBridge.Resolve.sum_inner_kcStdBasis_sq_local k]

/-! ## The target -/

theorem moment_two_kinFT {ℓ : ℝ} (hℓ : 0 < ℓ) {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgsupp : tsupport g ⊆ Metric.ball 0 (ℓ/2)) :
    (∑' n : Fin 3 → ℤ, (ℓ^3)⁻¹ * ‖Work.BoseBoxFock.kmomInt ℓ n‖^2
        * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖^2)
      = ((2*Real.pi)^3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
          ‖p‖^2 * ‖Submission.BoseGases.kinFT g p‖^2 := by
  have hgc : HasCompactSupport g := by
    rw [HasCompactSupport]
    exact (isCompact_closedBall (0 : ℝ³) (ℓ/2)).of_isClosed_subset (isClosed_tsupport g)
      (hgsupp.trans Metric.ball_subset_closedBall)
  have hsuppL : tsupport g ⊆ Work.BoseK15.corpusBox.boxL ℓ :=
    hgsupp.trans (ball_subset_corpusBox_boxL hℓ)
  -- the directional derivatives `∂_i g`
  have hcd : ∀ i : Fin 3, ContDiff ℝ (⊤ : ENat)
      (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) := by
    intro i
    have hf' : ContDiff ℝ (⊤ : ENat) (fderiv ℝ g) :=
      ContDiff.fderiv_right (f := g) (m := (⊤ : ENat)) (n := (⊤ : ENat)) hg (by simp)
    exact hf'.clm_apply contDiff_const
  have hcs : ∀ i : Fin 3, HasCompactSupport
      (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) :=
    fun i => hgc.fderiv_apply ℝ (Submission.BoseGases.kcStdBasis i)
  have hsupp : ∀ i : Fin 3, tsupport
      (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i))
      ⊆ Work.BoseK15.corpusBox.boxL ℓ :=
    fun i => (tsupport_fderiv_apply_subset ℝ (Submission.BoseGases.kcStdBasis i)).trans hsuppL
  -- the pointwise identity
  have hpoint : ∀ p : ℝ³, ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT g p‖ ^ 2
      = ∑ i : Fin 3, ‖Submission.BoseGases.kinFT
          (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) p‖ ^ 2 :=
    fun p => normSq_kinFT_eq_sum_normSq_fderiv hg hgc p
  -- summability of each differentiated lattice series
  have hsumm : ∀ i : Fin 3, Summable (fun n : Fin 3 → ℤ => (ℓ ^ 3)⁻¹
      * ‖Submission.BoseGases.kinFT
          (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i))
          (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2) :=
    fun i => mom2Summable hℓ (hcd i) (hcs i) (hsupp i)
  -- the frame identity for each differentiated state
  have hframe : ∀ i : Fin 3, (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹
      * ‖Submission.BoseGases.kinFT
          (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i))
          (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p, ‖Submission.BoseGases.kinFT
          (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) p‖ ^ 2 :=
    fun i => frame_lattice_ball hℓ (hcd i) (hcs i) (hsupp i)
  -- integrability of the transformed differentiated states
  have hInt : ∀ i : Fin 3, Integrable (fun p : ℝ³ => ‖Submission.BoseGases.kinFT
      (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) p‖ ^ 2) := by
    intro i
    have h1 : Integrable
        (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) :=
      (hcd i).continuous.integrable_of_hasCompactSupport (hcs i)
    have h2 : MemLp (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) 2 volume :=
      (hcd i).continuous.memLp_of_hasCompactSupport (hcs i)
    exact (memLp_two_iff_integrable_sq_norm (Work.BoseKinLoc.Momentum.continuous_kinFT_of_integrable
      h1).aestronglyMeasurable).mp (Work.BoseKinLoc.Momentum.memLp_kinFT h1 h2)
  calc
    (∑' n : Fin 3 → ℤ, (ℓ^3)⁻¹ * ‖Work.BoseBoxFock.kmomInt ℓ n‖^2
        * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖^2)
        = ∑' n : Fin 3 → ℤ, ∑ i : Fin 3, (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT
            (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i))
            (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2 := by
          refine tsum_congr (fun n => ?_)
          rw [mul_assoc, hpoint (Work.BoseBoxFock.kmomInt ℓ n), Finset.mul_sum]
      _ = ∑ i : Fin 3, ∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT
            (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i))
            (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2 :=
          Summable.tsum_finsetSum (s := Finset.univ)
            (f := fun (i : Fin 3) (n : Fin 3 → ℤ) => (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT
              (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i))
              (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
            (fun i _ => hsumm i)
      _ = ∑ i : Fin 3, ((2 * Real.pi) ^ 3)⁻¹ * ∫ p, ‖Submission.BoseGases.kinFT
            (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) p‖ ^ 2 :=
          Finset.sum_congr rfl (fun i _ => hframe i)
      _ = ((2 * Real.pi) ^ 3)⁻¹ * ∑ i : Fin 3, ∫ p, ‖Submission.BoseGases.kinFT
            (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) p‖ ^ 2 :=
          (Finset.mul_sum (Finset.univ : Finset (Fin 3))
            (fun i => ∫ p, ‖Submission.BoseGases.kinFT
              (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) p‖ ^ 2)
            (((2 * Real.pi) ^ 3)⁻¹)).symm
      _ = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p, ∑ i : Fin 3, ‖Submission.BoseGases.kinFT
            (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) p‖ ^ 2 := by
          rw [(integral_finsetSum (Finset.univ : Finset (Fin 3))
            (f := fun (i : Fin 3) (p : ℝ³) => ‖Submission.BoseGases.kinFT
              (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) p‖ ^ 2)
            (fun i _ => hInt i)).symm]
      _ = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT g p‖ ^ 2 := by
          rw [integral_congr_ae (Filter.Eventually.of_forall (fun p => (hpoint p).symm))]

end Work.BoseBoxFock
