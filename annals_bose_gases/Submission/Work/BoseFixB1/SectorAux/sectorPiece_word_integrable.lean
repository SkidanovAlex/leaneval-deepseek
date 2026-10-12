import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Submission.Work.BoseFixB1.CrossWordsDefs
import Submission.Work.BoseFixB1.boxMass_pos_of_goodSet
import Submission.Work.BoseFixB1.chiSmallB_contDiff_two
import Submission.Work.BoseFixB1.integrable_sbKin
import Submission.Work.BoseFixB1.sectorPieceBoxQIndAmpLe
import Submission.Work.BoseFixB1.tBamp_boxQInd_integrableOn_sq
import Submission.Work.BoseFixB1S.tBamp_rPart_bound
import Submission.Work.BoseFixB2.Polar.fibre_H1_bound
import Submission.Work.BoseFixB2.Polar.fsT_parallelogram
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.SectorAux.sectorPiece_word_integrable`

`p`-integrability of the symbol-weighted squared windowed amplitude of the sector piece of a box
state at the sliding small box, i.e. of

  `p ↦ [‖p‖ − c]₊² ·(ℓ³)⁻¹∫_{abox n ℓ}‖tBamp χ p (Q_{B,i}(1_{n_B=k}·Φ)) i x‖²`,

with `χ = chiSmallB M ℓ d u` the sliding small-box cutoff.

## Route

* the sector piece is dominated pointwise by the state (`sectorPieceBoxQIndAmpLe`);
* on the support of `χ` (⊆ `B(u)`) FS's projection `Q_{B,i}` agrees with the smooth `boxQ`
  (`boxQInd_eq_indicator_mul_boxQ`), so the amplitude is the Fourier transform of the smooth
  fibre `z ↦ χ z·boxQ(x_{i←z})`;
* the Fourier-derivative identity (`kinFT_fderiv_applyC_one`, from Mathlib's `Real.fourier_fderiv`)
  trades `‖p‖²` for the three directional derivatives, giving the pointwise domination
  `[‖p‖−c]₊²‖𝓕F(p)‖² ≤ (1+|c|)²(‖𝓕F(p)‖² + Σ_k‖𝓕(∂_kF)(p)‖²)`;
* each summand is an unweighted windowed amplitude, whose `p`-integral is computed by Plancherel
  (`tBamp_piece_bound`), uniformly in `x`, and the resulting lintegral is finite.
-/

noncomputable section
set_option maxHeartbeats 4000000
open MeasureTheory Filter
open scoped Real Topology FourierTransform ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

namespace Work.BoseFixB1.SectorAux

open Submission.BoseGases

/-! ## 1. Basic helpers -/

/-- The symbol bound `fsKinCoeff c r ≤ (1+|c|)²(1+r²)` for `r ≥ 0`. -/
lemma fsKinCoeff_le_sq_mul {c r : ℝ} (hr : 0 ≤ r) :
    Submission.BoseGases.fsKinCoeff c r ≤ (1 + |c|) ^ 2 * (1 + r ^ 2) := by
  have h1 : Submission.BoseGases.fsKinCoeff c r ≤ (r + |c|) ^ 2 := by
    rw [Submission.BoseGases.fsKinCoeff]
    refine pow_le_pow_left₀ (le_max_right _ 0) (max_le ?_ ?_) 2
    · linarith [neg_le_abs c]
    · linarith [abs_nonneg c, hr]
  have h2 : (r + |c|) ^ 2 ≤ (1 + |c|) ^ 2 * (1 + r ^ 2) := by
    nlinarith [sq_abs c, abs_nonneg c, sq_nonneg (r - 1 / 2), sq_nonneg r, sq_nonneg c,
      mul_nonneg (abs_nonneg c) (by nlinarith [sq_nonneg (r - 1 / 2)] : (0:ℝ) ≤ 1 + r ^ 2 - r)]
  linarith

/-- `tBamp` is the `p`-convention Fourier transform of the windowed substituted fibre. -/
lemma tBamp_eq_kinFT (rr : E3 → ℝ) (p : E3) {n : ℕ} (Ψ : Submission.BoseGases.X n → ℝ)
    (i : Fin n) (x : Submission.BoseGases.X n) :
    Work.SmallBoxTBWord.tBamp rr p Ψ i x
      = Submission.BoseGases.kinFT (fun z : E3 =>
          ((rr z * Ψ (Function.update x i z) : ℝ) : ℂ)) p := by
  rw [Work.SmallBoxTBWord.tBamp, Submission.BoseGases.kinFT]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  push_cast
  ring

/-- C¹ version of the Fourier-derivative identity, from the three integrability hypotheses. -/
theorem kinFT_fderiv_applyC_one {g : E3 → ℂ}
    (hInt : Integrable g) (hDiff : Differentiable ℝ g) (hInt' : Integrable (fderiv ℝ g))
    (k : E3) (i : Fin 3) :
    Submission.BoseGases.kinFT
        (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) k
      = Complex.I * ((inner ℝ k (Submission.BoseGases.kcStdBasis i) : ℝ) : ℂ)
          * Submission.BoseGases.kinFT g k := by
  have key := Real.fourier_fderiv (f := g) hInt hDiff hInt'
  have hdir : ∀ v : E3,
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
      congrArg (fun (T : E3 →L[ℝ] ℂ) => T (Submission.BoseGases.kcStdBasis i))
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

/-- The sum form of the Fourier-derivative identity, for `C¹` compactly supported `g`. -/
theorem normSq_kinFT_eq_sum_normSq_fderiv_one {g : E3 → ℂ}
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (k : E3) :
    ‖k‖ ^ 2 * ‖Submission.BoseGases.kinFT g k‖ ^ 2
      = ∑ i : Fin 3, ‖Submission.BoseGases.kinFT
          (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) k‖ ^ 2 := by
  have hInt : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
  have hDiff : Differentiable ℝ g := hg.differentiable_one
  have hInt' : Integrable (fderiv ℝ g) :=
    (hg.continuous_fderiv (by simp)).integrable_of_hasCompactSupport (hgc.fderiv ℝ)
  have hterm : ∀ i : Fin 3,
      Submission.BoseGases.kinFT
          (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) k
        = Complex.I * ((inner ℝ k (Submission.BoseGases.kcStdBasis i) : ℝ) : ℂ)
            * Submission.BoseGases.kinFT g k :=
    fun i => kinFT_fderiv_applyC_one hInt hDiff hInt' k i
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

/-- The fibre identity: on the support of a window contained in `A`, FS's box projection
`boxQInd` agrees with the (smooth) `boxQ`, so the amplitude is the Fourier transform of the
fibre `χ · (boxQ ∘ update)`. -/
lemma tBamp_boxQInd_eq_kinFT_boxQ {n : ℕ} {V : ℝ} {A : Set E3} {χ : E3 → ℝ}
    (hχA : ∀ z : E3, z ∉ A → χ z = 0) (i : Fin n) (Φ : Submission.BoseGases.X n → ℝ)
    (p : E3) (x : Submission.BoseGases.X n) :
    Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd V A i Φ) i x
      = Submission.BoseGases.kinFT (fun z : E3 =>
          ((χ z * Work.SmallBoxTBWord.boxQ V A i Φ (Function.update x i z) : ℝ) : ℂ)) p := by
  rw [Work.SmallBoxTBWord.tBamp, Submission.BoseGases.kinFT]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  have hQ := congrFun (Work.UBBInputs9.A.boxQInd_eq_indicator_mul_boxQ (volA := V) (A := A) i Φ)
    (Function.update x i z)
  show (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
      * ((Work.UBBInputs8.boxQInd V A i Φ (Function.update x i z) : ℝ) : ℂ)
    = Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
      * (((χ z * Work.SmallBoxTBWord.boxQ V A i Φ (Function.update x i z) : ℝ)) : ℂ)
  rw [hQ]
  simp only [Function.update_self]
  by_cases hz : z ∈ A
  · rw [Set.indicator_of_mem hz, one_mul]
    push_cast
    ring
  · rw [Set.indicator_of_notMem hz, zero_mul, hχA z hz]
    push_cast
    ring

/-- The pointwise `p`-bound: the symbol-weighted squared amplitude of a `C¹` compactly
supported fibre is dominated by the unweighted transform plus the transforms of the three
directional derivatives. -/
lemma fsKinCoeff_mul_normSq_kinFT_le {c : ℝ} {h : E3 → ℂ}
    (hh : ContDiff ℝ 1 h) (hcs : HasCompactSupport h) (p : E3) :
    Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Submission.BoseGases.kinFT h p‖ ^ 2
      ≤ (1 + |c|) ^ 2 * (‖Submission.BoseGases.kinFT h p‖ ^ 2 +
          ∑ k : Fin 3, ‖Submission.BoseGases.kinFT
            (fun z => fderiv ℝ h z (Submission.BoseGases.kcStdBasis k)) p‖ ^ 2) := by
  have hsym : Submission.BoseGases.fsKinCoeff c ‖p‖ ≤ (1 + |c|) ^ 2 * (1 + ‖p‖ ^ 2) :=
    fsKinCoeff_le_sq_mul (norm_nonneg p)
  have hsum := normSq_kinFT_eq_sum_normSq_fderiv_one hh hcs p
  calc Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Submission.BoseGases.kinFT h p‖ ^ 2
      ≤ ((1 + |c|) ^ 2 * (1 + ‖p‖ ^ 2)) * ‖Submission.BoseGases.kinFT h p‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hsym (sq_nonneg _)
    _ = (1 + |c|) ^ 2 * (‖Submission.BoseGases.kinFT h p‖ ^ 2 +
          ∑ k : Fin 3, ‖Submission.BoseGases.kinFT
            (fun z => fderiv ℝ h z (Submission.BoseGases.kcStdBasis k)) p‖ ^ 2) := by
        rw [← hsum]; ring

/-! ## 2. The directional derivative of the smooth fibre -/

/-- The directional derivative of the complexified windowed fibre. -/
lemma fderiv_fib_apply {n : ℕ} {χ : E3 → ℝ} (hχ : Differentiable ℝ χ)
    {G : Submission.BoseGases.X n → ℝ} (hG : ContDiff ℝ (⊤ : ENat) G) (i : Fin n)
    (x : Submission.BoseGases.X n) (z : E3) (k : Fin 3) :
    fderiv ℝ (fun w : E3 => ((χ w * G (Function.update x i w) : ℝ) : ℂ)) z
        (Submission.BoseGases.kcStdBasis k)
      = ((fderiv ℝ χ z (Submission.BoseGases.kcStdBasis k) * G (Function.update x i z)
          + χ z * fderiv ℝ G (Function.update x i z)
              (Function.update 0 i (Submission.BoseGases.kcStdBasis k)) : ℝ) : ℂ) := by
  have hfun : (fun w : E3 => ((χ w * G (Function.update x i w) : ℝ) : ℂ))
      = fun w : E3 => (χ w : ℂ) * ((G (Function.update x i w) : ℝ) : ℂ) := by
    funext w
    push_cast
    ring
  have hGd : DifferentiableAt ℝ (fun w : E3 => G (Function.update x i w)) z :=
    ((hG.differentiable (by simp)).differentiableAt).comp z
      (hasFDerivAt_update x (i := i) z).differentiableAt
  have h1 : HasFDerivAt (fun w : E3 => (χ w : ℂ))
      ((Complex.ofRealCLM : ℝ →L[ℝ] ℂ).comp (fderiv ℝ χ z)) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z (hχ.differentiableAt.hasFDerivAt)
  have h2 : HasFDerivAt (fun w : E3 => ((G (Function.update x i w) : ℝ) : ℂ))
      ((Complex.ofRealCLM : ℝ →L[ℝ] ℂ).comp
        (fderiv ℝ (fun w : E3 => G (Function.update x i w)) z)) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z hGd.hasFDerivAt
  have h3 := h1.mul h2
  rw [hfun]
  rw [show (fun w : E3 => (χ w : ℂ) * ((G (Function.update x i w) : ℝ) : ℂ))
      = (fun w : E3 => (χ w : ℂ)) * (fun w : E3 => ((G (Function.update x i w) : ℝ) : ℂ))
      from rfl]
  rw [h3.fderiv, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  have hfib : fderiv ℝ (fun w : E3 => G (Function.update x i w)) z
        (Submission.BoseGases.kcStdBasis k)
      = fderiv ℝ G (Function.update x i z)
        (Function.update 0 i (Submission.BoseGases.kcStdBasis k)) :=
    Work.BoseFixB2.Polar.fderiv_fibre_apply hG i x z k
  rw [hfib]
  simp only [Complex.ofRealCLM_apply]
  push_cast
  ring

/-! ## 3. Per-`x` Plancherel for the windowed amplitude -/

/-- **Per-`x` Plancherel for the windowed amplitude.** -/
theorem integral_tBamp_normSq_eq {n : ℕ} {rr : E3 → ℝ} (hrc : Continuous rr)
    (hrcs : HasCompactSupport rr) {Ψ : Submission.BoseGases.X n → ℝ} (hΨc : Continuous Ψ)
    (i : Fin n) (x : Submission.BoseGases.X n) :
    Integrable (fun p : E3 => ‖Work.SmallBoxTBWord.tBamp rr p Ψ i x‖ ^ 2) ∧
    (∫ p : E3, ‖Work.SmallBoxTBWord.tBamp rr p Ψ i x‖ ^ 2)
      = (2 * Real.pi) ^ 3 * ∫ z : E3, (rr z * Ψ (Function.update x i z)) ^ 2 := by
  set F : E3 → ℂ := fun z => ((rr z * Ψ (Function.update x i z) : ℝ) : ℂ) with hF
  have hFcont : Continuous F :=
    Complex.continuous_ofReal.comp (hrc.mul (hΨc.comp (by fun_prop)))
  have hFcs : HasCompactSupport F :=
    (hrcs.mul_right (f' := fun z : E3 => Ψ (Function.update x i z))).comp_left
      (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hInt : Integrable F := hFcont.integrable_of_hasCompactSupport hFcs
  have hFcs2 : HasCompactSupport (fun z : E3 => ‖F z‖ ^ 2) :=
    hFcs.comp_left (g := fun r : ℂ => ‖r‖ ^ 2) (by simp)
  have hInt2 : Integrable (fun z : E3 => ‖F z‖ ^ 2) :=
    (hFcont.norm.pow 2).integrable_of_hasCompactSupport hFcs2
  have hm1 : MemLp F 1 volume := memLp_one_iff_integrable.mpr hInt
  have hm2 : MemLp F 2 volume :=
    (memLp_two_iff_integrable_sq_norm hFcont.aestronglyMeasurable).mpr hInt2
  obtain ⟨hint, heq⟩ := Work.BoseFixB1S.integral_kinFT_sq_eq hm1 hm2
  have hpt : (fun p : E3 => ‖Submission.BoseGases.kinFT F p‖ ^ 2)
      = fun p : E3 => ‖Work.SmallBoxTBWord.tBamp rr p Ψ i x‖ ^ 2 := by
    funext p
    rw [tBamp_eq_kinFT rr p Ψ i x]
  refine ⟨hint.congr (Filter.Eventually.of_forall (fun p => congrFun hpt p)), ?_⟩
  rw [← hpt, heq]
  congr 1
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  show ‖(((rr z * Ψ (Function.update x i z)) : ℝ) : ℂ)‖ ^ 2
    = (rr z * Ψ (Function.update x i z)) ^ 2
  rw [Complex.sq_norm, Complex.normSq_ofReal]
  ring

/-- The uniform `z`-bound on the windowed fibre (only the support of the window matters). -/
lemma integral_fibre_sq_le {n : ℕ} {rr : E3 → ℝ} {Ψ : Submission.BoseGases.X n → ℝ} {ρ C : ℝ}
    (x : Submission.BoseGases.X n) (i : Fin n)
    (hrb : ∀ z : E3, |rr z| ≤ ρ)
    (hΨb : ∀ z : E3, rr z ≠ 0 → |Ψ (Function.update x i z)| ≤ C)
    (hcs : HasCompactSupport rr) (hcont : Continuous (fun z : E3 => rr z * Ψ (Function.update x i z))) :
    ∫ z : E3, (rr z * Ψ (Function.update x i z)) ^ 2
      ≤ ρ ^ 2 * C ^ 2 * (volume (tsupport rr)).toReal := by
  have hfibcs : HasCompactSupport (fun z : E3 => rr z * Ψ (Function.update x i z)) := hcs.mul_right
  have hKfin : (volume : Measure E3) (tsupport rr) < ⊤ := hcs.isCompact.measure_lt_top
  have hcs2 : HasCompactSupport (fun z : E3 => (rr z * Ψ (Function.update x i z)) ^ 2) :=
    hfibcs.comp_left (g := fun r : ℝ => r ^ 2) (by simp)
  have h1 : Integrable (fun z : E3 => (rr z * Ψ (Function.update x i z)) ^ 2) :=
    (hcont.pow 2).integrable_of_hasCompactSupport hcs2
  have hg : Integrable (fun z : E3 =>
      ρ ^ 2 * C ^ 2 * (tsupport rr).indicator (fun _ => (1 : ℝ)) z) := by
    have h1 : Integrable ((tsupport rr).indicator (fun _ => (1 : ℝ)) : E3 → ℝ) := by
      rw [MeasureTheory.integrable_indicator_iff (isClosed_tsupport rr).measurableSet]
      exact MeasureTheory.integrableOn_const (C := (1 : ℝ)) (ne_of_lt hKfin) (by simp)
    exact h1.const_mul _
  have hpt : ∀ z : E3, (rr z * Ψ (Function.update x i z)) ^ 2
      ≤ ρ ^ 2 * C ^ 2 * (tsupport rr).indicator (fun _ => (1 : ℝ)) z := by
    intro z
    rw [show (rr z * Ψ (Function.update x i z)) ^ 2
        = rr z ^ 2 * (Ψ (Function.update x i z)) ^ 2 from by ring]
    have h1 : rr z ^ 2 ≤ ρ ^ 2 := by
      rw [← sq_abs (rr z)]; exact pow_le_pow_left₀ (abs_nonneg _) (hrb z) 2
    by_cases hz : rr z = 0
    · rw [hz]
      simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
      exact mul_nonneg (mul_nonneg (sq_nonneg ρ) (sq_nonneg C))
        (Set.indicator_nonneg (fun _ _ => zero_le_one) z)
    · have h2 : (Ψ (Function.update x i z)) ^ 2 ≤ C ^ 2 := by
        rw [← sq_abs (Ψ (Function.update x i z))]
        exact pow_le_pow_left₀ (abs_nonneg _) (hΨb z hz) 2
      by_cases hz' : z ∈ tsupport rr
      · rw [Set.indicator_of_mem hz', mul_one]
        exact mul_le_mul h1 h2 (sq_nonneg _) (sq_nonneg _)
      · exact absurd (subset_tsupport rr (Function.mem_support.mpr hz)) hz'
  have hmono := MeasureTheory.integral_mono h1 hg hpt
  calc ∫ z : E3, (rr z * Ψ (Function.update x i z)) ^ 2
      ≤ ∫ z : E3, ρ ^ 2 * C ^ 2 * (tsupport rr).indicator (fun _ => (1 : ℝ)) z := hmono
    _ = ρ ^ 2 * C ^ 2 * (volume (tsupport rr)).toReal := by
        rw [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_indicator_const (1 : ℝ) (isClosed_tsupport rr).measurableSet,
          smul_eq_mul, mul_one, MeasureTheory.Measure.real_def]

/-- Joint measurability of the squared windowed amplitude in `(p, x)`. -/
theorem measurable_tBamp_pair_gen {n : ℕ} {rr : E3 → ℝ} (hrc : Continuous rr)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨm : Measurable Ψ) (i : Fin n) :
    Measurable (fun q : E3 × Submission.BoseGases.X n =>
      ‖Work.SmallBoxTBWord.tBamp rr q.1 Ψ i q.2‖ ^ 2) := by
  have hmeastB : Measurable (fun q : E3 × Submission.BoseGases.X n =>
      Work.SmallBoxTBWord.tBamp rr q.1 Ψ i q.2) := by
    have hJ : Measurable (fun q : (E3 × Submission.BoseGases.X n) × E3 =>
        ((rr q.2 : ℂ) * Complex.exp (-(Complex.I * (inner ℝ q.1.1 q.2 : ℂ))))
          * (Ψ (Function.update q.1.2 i q.2) : ℂ)) := by
      have hexp : Measurable (fun q : (E3 × Submission.BoseGases.X n) × E3 =>
          Complex.exp (-(Complex.I * (inner ℝ q.1.1 q.2 : ℂ)))) := by
        have hpair : Continuous (fun q : (E3 × Submission.BoseGases.X n) × E3 => (q.1.1, q.2)) := by
          fun_prop
        exact (Complex.continuous_exp.comp ((continuous_const.mul
          (Complex.continuous_ofReal.comp (continuous_inner.comp hpair))).neg)).measurable
      have hupd : Measurable (fun q : (E3 × Submission.BoseGases.X n) × E3 =>
          Function.update q.1.2 i q.2) := by
        have hpair : Measurable (fun q : (E3 × Submission.BoseGases.X n) × E3 =>
            (q.1.2, q.2)) := by fun_prop
        exact (measurable_update' (X := fun _ : Fin n => E3) (a := i)).comp hpair
      exact ((Complex.continuous_ofReal.measurable.comp (hrc.measurable.comp measurable_snd)).mul hexp).mul
        (Complex.continuous_ofReal.measurable.comp (hΨm.comp hupd))
    have hSM := hJ.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure E3))
    simpa only [Work.SmallBoxTBWord.tBamp] using hSM.measurable
  exact hmeastB.norm.pow_const 2

/-- `ofReal` of the squared windowed amplitude is jointly measurable. -/
lemma measurable_ofReal_amp {N : ℕ} {rr : E3 → ℝ} (hrc : Continuous rr)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨm : Measurable Ψ) (i : Fin N) :
    Measurable (fun q : E3 × Submission.BoseGases.X N =>
      ENNReal.ofReal (‖Work.SmallBoxTBWord.tBamp rr q.1 Ψ i q.2‖ ^ 2)) :=
  ENNReal.measurable_ofReal.comp (measurable_tBamp_pair_gen hrc hΨm i)

/-- `ofReal` of a constant multiple of the squared windowed amplitude is jointly measurable. -/
lemma measurable_ofReal_const_mul_amp {N : ℕ} {rr : E3 → ℝ} (hrc : Continuous rr)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨm : Measurable Ψ) (i : Fin N) (c : ℝ) :
    Measurable (fun q : E3 × Submission.BoseGases.X N =>
      ENNReal.ofReal (c * ‖Work.SmallBoxTBWord.tBamp rr q.1 Ψ i q.2‖ ^ 2)) :=
  ENNReal.measurable_ofReal.comp
    (measurable_const.mul (measurable_tBamp_pair_gen hrc hΨm i))

/-- `ofReal` of the squared windowed amplitude, in the `x`-variable at fixed `p`. -/
lemma measurable_ofReal_amp_snd {N : ℕ} {rr : E3 → ℝ} (hrc : Continuous rr)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨm : Measurable Ψ) (i : Fin N) (p : E3) :
    Measurable (fun x : Submission.BoseGases.X N =>
      ENNReal.ofReal (‖Work.SmallBoxTBWord.tBamp rr p Ψ i x‖ ^ 2)) :=
  Measurable.of_uncurry_left
    (f := fun p x => ENNReal.ofReal (‖Work.SmallBoxTBWord.tBamp rr p Ψ i x‖ ^ 2))
    (measurable_ofReal_amp hrc hΨm i) (x := p)

/-- `ofReal` of the squared windowed amplitude, in `p` at fixed `x`. -/
lemma measurable_ofReal_amp_fst {N : ℕ} {rr : E3 → ℝ} (hrc : Continuous rr)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨm : Measurable Ψ) (i : Fin N)
    (x : Submission.BoseGases.X N) :
    Measurable (fun p : E3 => ENNReal.ofReal (‖Work.SmallBoxTBWord.tBamp rr p Ψ i x‖ ^ 2)) :=
  Measurable.of_uncurry_right
    (f := fun p x => ENNReal.ofReal (‖Work.SmallBoxTBWord.tBamp rr p Ψ i x‖ ^ 2))
    (measurable_ofReal_amp hrc hΨm i) (y := x)

/-- `ofReal` of a constant multiple of the squared windowed amplitude, in `p` at fixed `x`. -/
lemma measurable_ofReal_const_mul_amp_fst {N : ℕ} {rr : E3 → ℝ} (hrc : Continuous rr)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨm : Measurable Ψ) (i : Fin N) (c : ℝ)
    (x : Submission.BoseGases.X N) :
    Measurable (fun p : E3 => ENNReal.ofReal (c * ‖Work.SmallBoxTBWord.tBamp rr p Ψ i x‖ ^ 2)) :=
  Measurable.of_uncurry_right
    (f := fun p x => ENNReal.ofReal (c * ‖Work.SmallBoxTBWord.tBamp rr p Ψ i x‖ ^ 2))
    (measurable_ofReal_const_mul_amp hrc hΨm i c) (y := x)

/-! ## 4. Amplitude bounds, `x`-integrability and marginal integrability -/

/-- The `x`-integral of a windowed amplitude is at most `(2π)³ρ²C²V`. -/
theorem tBamp_piece_bound {N : ℕ} {ℓ : ℝ} {rr : E3 → ℝ} {Ψ : Submission.BoseGases.X N → ℝ}
    (hrc : Continuous rr) (hrcs : HasCompactSupport rr) (hℓ : 0 < ℓ) {ρ C S V : ℝ}
    (hρ0 : 0 ≤ ρ) (hC0 : 0 ≤ C) (hrb : ∀ z : E3, |rr z| ≤ ρ)
    (hΨc : Continuous Ψ)
    (hΨb : ∀ y : Submission.BoseGases.X N, (∀ j, ‖y j‖ ≤ S) → |Ψ y| ≤ C)
    (hrS : ∀ z : E3, rr z ≠ 0 → ‖z‖ ≤ S) (hℓS : ℓ ≤ S)
    (hvol : (volume (tsupport rr)).toReal ≤ V) (hV0 : 0 ≤ V) {x : Submission.BoseGases.X N}
    (hx : x ∈ Submission.BoseGases.abox N ℓ) (i : Fin N) :
    Integrable (fun p : E3 => ‖Work.SmallBoxTBWord.tBamp rr p Ψ i x‖ ^ 2) ∧
    (∫ p : E3, ‖Work.SmallBoxTBWord.tBamp rr p Ψ i x‖ ^ 2)
      = (2 * Real.pi) ^ 3 * ∫ z : E3, (rr z * Ψ (Function.update x i z)) ^ 2 ∧
    (∫ p : E3, ‖Work.SmallBoxTBWord.tBamp rr p Ψ i x‖ ^ 2)
      ≤ (2 * Real.pi) ^ 3 * (ρ ^ 2 * C ^ 2 * V) := by
  obtain ⟨hint, heq⟩ := integral_tBamp_normSq_eq hrc hrcs hΨc i x
  refine ⟨hint, heq, ?_⟩
  rw [heq]
  have hcont : Continuous (fun z : E3 => rr z * Ψ (Function.update x i z)) :=
    hrc.mul (hΨc.comp (by fun_prop))
  have hΨb' : ∀ z : E3, rr z ≠ 0 → |Ψ (Function.update x i z)| ≤ C := by
    intro z hz
    refine hΨb _ (fun j => ?_)
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self]
      exact hrS z hz
    · rw [Function.update_of_ne hj]
      exact le_trans (Work.BoseFixB1.norm_le_of_mem_abox hℓ hx j) hℓS
  have h2 := integral_fibre_sq_le x i hrb hΨb' hrcs hcont
  have h3 : (0 : ℝ) ≤ (2 * Real.pi) ^ 3 := by positivity
  calc (2 * Real.pi) ^ 3 * ∫ z : E3, (rr z * Ψ (Function.update x i z)) ^ 2
      ≤ (2 * Real.pi) ^ 3 * (ρ ^ 2 * C ^ 2 * (volume (tsupport rr)).toReal) :=
        mul_le_mul_of_nonneg_left h2 h3
    _ ≤ (2 * Real.pi) ^ 3 * (ρ ^ 2 * C ^ 2 * V) := by
        refine mul_le_mul_of_nonneg_left ?_ h3
        exact mul_le_mul_of_nonneg_left hvol (mul_nonneg (sq_nonneg _) (sq_nonneg _))


/-- `ofReal` of a set integral is at most the lintegral (no integrability needed: the junk value
`∫ = 0` of a non-integrable function makes the non-integrable case trivial). -/
lemma ofReal_integral_le_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases h : Integrable f μ
  · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal h (Filter.Eventually.of_forall hf)]
  · rw [MeasureTheory.integral_undef h, ENNReal.ofReal_zero]
    exact bot_le

/-! ## 5. The smooth-state case -/

/-- The `p`-integrand of the symbol-weighted smooth-case amplitude is integrable. -/
theorem integrable_smooth {N : ℕ} {ℓ V c : ℝ} {A : Set E3} {χ : E3 → ℝ}
    (hℓ : 0 < ℓ) (hχ2 : ContDiff ℝ 2 χ) (hχcs : HasCompactSupport χ)
    (hχA : ∀ z : E3, z ∉ A → χ z = 0) (hAcomp : IsCompact A)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin N) :
    Integrable (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖ *
      ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox N ℓ,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd V A i Φ) i x‖ ^ 2)) := by
  classical
  have hχ1 : ContDiff ℝ 1 χ := hχ2.of_le (by norm_num)
  have hχd : Differentiable ℝ χ := hχ1.differentiable_one
  have hχc : Continuous χ := hχ1.continuous
  have hχdfc : Continuous (fderiv ℝ χ) := hχ1.continuous_fderiv (by simp)
  set G : Submission.BoseGases.X N → ℝ := Work.SmallBoxTBWord.boxQ V A i Φ with hGdef
  have hGcd : ContDiff ℝ (⊤ : ENat) G :=
    Work.SmallBoxTBWord.boxQ_contDiff_of_compact hAcomp V i hΦ
  have hGc : Continuous G := hGcd.continuous
  have hGdfc : Continuous (fderiv ℝ G) := hGcd.continuous_fderiv (by simp)
  -- the directions and the derived data
  have hdirnorm : ∀ k : Fin 3, ‖Submission.BoseGases.kcStdBasis k‖ = 1 := by
    intro k
    rw [show Submission.BoseGases.kcStdBasis k = EuclideanSpace.single k (1 : ℝ) from rfl,
      EuclideanSpace.norm_single]
    norm_num
  have hdirnorm' : ∀ k : Fin 3,
      ‖Function.update (0 : Submission.BoseGases.X N) i (Submission.BoseGases.kcStdBasis k)‖ = 1 := by
    intro k
    rw [Work.BoseFixB2.Polar.norm_update_zero, hdirnorm k]
  -- support radius and the box length of the state side
  obtain ⟨R₀, hR₀χ, hR₀dχ⟩ : ∃ R : ℝ, (∀ z ∈ tsupport χ, ‖z‖ ≤ R)
      ∧ (∀ z ∈ tsupport (fderiv ℝ χ), ‖z‖ ≤ R) := by
    obtain ⟨R₁, hR₁⟩ := hχcs.isCompact.isBounded.subset_closedBall (0 : E3)
    obtain ⟨R₂, hR₂⟩ := (hχcs.fderiv ℝ).isCompact.isBounded.subset_closedBall (0 : E3)
    refine ⟨max R₁ R₂, fun z hz => ?_, fun z hz => ?_⟩
    · refine le_trans (by simpa [Metric.mem_closedBall, dist_eq_norm] using hR₁ hz) (le_max_left _ _)
    · refine le_trans (by simpa [Metric.mem_closedBall, dist_eq_norm] using hR₂ hz) (le_max_right _ _)
  obtain ⟨S, hSpos, hR₀S, hℓS⟩ : ∃ S : ℝ, 0 < S ∧ R₀ ≤ S ∧ ℓ ≤ S := by
    refine ⟨|R₀| + ℓ + 1, ?_, ?_, ?_⟩
    · have h1 := abs_nonneg R₀; linarith
    · have h1 := le_abs_self R₀; linarith
    · have h1 := abs_nonneg R₀; linarith
  -- the volumes
  obtain ⟨Vm, hVm0, hvolχ, hvolP1⟩ : ∃ Vm : ℝ, 0 ≤ Vm ∧ (volume (tsupport χ)).toReal ≤ Vm
      ∧ (∀ k : Fin 3, (volume (tsupport (fun z : E3 =>
          fderiv ℝ χ z (Submission.BoseGases.kcStdBasis k)))).toReal ≤ Vm) := by
    have hfin : (volume : Measure E3) (tsupport (fderiv ℝ χ)) < ⊤ :=
      (hχcs.fderiv ℝ).isCompact.measure_lt_top
    refine ⟨max ((volume (tsupport χ)).toReal)
      ((volume (tsupport (fderiv ℝ χ))).toReal), ?_, le_max_left _ _, ?_⟩
    · exact le_trans ENNReal.toReal_nonneg (le_max_left _ _)
    · intro k
      have hsub : tsupport (fun z : E3 => fderiv ℝ χ z (Submission.BoseGases.kcStdBasis k))
          ⊆ tsupport (fderiv ℝ χ) := by
        refine (IsClosed.closure_subset_iff (isClosed_tsupport (fderiv ℝ χ))).mpr ?_
        intro z hz
        refine subset_tsupport _ (Function.mem_support.mpr ?_)
        intro h0
        refine hz ?_
        show (fderiv ℝ χ z) (Submission.BoseGases.kcStdBasis k) = 0
        rw [h0]
        rfl
      refine le_trans ?_ (le_max_right _ _)
      exact ENNReal.toReal_mono hfin.ne (measure_mono hsub)
  -- sup bounds
  obtain ⟨ρχ, hρχ0, hρχ⟩ : ∃ ρ : ℝ, 0 ≤ ρ ∧ ∀ z : E3, |χ z| ≤ ρ := by
    obtain ⟨M, hM⟩ := hχcs.isCompact.exists_bound_of_continuousOn hχc.continuousOn
    refine ⟨max M 0, le_max_right _ _, fun z => ?_⟩
    by_cases hz : z ∈ tsupport χ
    · exact le_trans (by simpa [Real.norm_eq_abs] using hM z hz) (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hz, abs_zero]
      exact le_max_right _ _
  obtain ⟨ρd, hρd0, hρd⟩ : ∃ ρ : ℝ, 0 ≤ ρ ∧ ∀ (k : Fin 3) (z : E3),
      |fderiv ℝ χ z (Submission.BoseGases.kcStdBasis k)| ≤ ρ := by
    obtain ⟨M, hM⟩ := (hχcs.fderiv ℝ).isCompact.exists_bound_of_continuousOn
      hχdfc.continuousOn
    refine ⟨max M 0, le_max_right _ _, fun k z => ?_⟩
    by_cases hz : fderiv ℝ χ z = 0
    · simp only [hz, ContinuousLinearMap.zero_apply, abs_zero]
      exact le_max_right _ _
    · have h1 : ‖(fderiv ℝ χ z) (Submission.BoseGases.kcStdBasis k)‖ ≤ ‖fderiv ℝ χ z‖ := by
        calc ‖(fderiv ℝ χ z) (Submission.BoseGases.kcStdBasis k)‖
            ≤ ‖fderiv ℝ χ z‖ * ‖Submission.BoseGases.kcStdBasis k‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ = ‖fderiv ℝ χ z‖ := by rw [hdirnorm k, mul_one]
      rw [Real.norm_eq_abs] at h1
      refine le_trans (le_trans h1 (hM z (subset_tsupport _ (Function.mem_support.mpr hz))))
        (le_max_left _ _)
  have hbox2 : ∀ {K : ℝ} {y : Submission.BoseGases.X N}, 0 ≤ K → (∀ j, ‖y j‖ ≤ K) →
      y ∈ Submission.BoseGases.abox N (2 * K) := by
    intro K y hK hy
    rw [Submission.BoseGases.mem_abox_iff]
    intro j
    rw [Submission.BoseGases.mem_acube_iff]
    intro m
    have h1 : |(y j).ofLp m| ≤ ‖y j‖ := by
      simpa using PiLp.norm_apply_le (p := 2) (β := fun _ : Fin 3 => ℝ) (y j) m
    have h3 : |(y j).ofLp m| ≤ K := le_trans h1 (hy j)
    have h4 := abs_le.mp h3
    rw [Set.mem_Icc]
    constructor <;> linarith [h4.1, h4.2]
  obtain ⟨CG, hCG0, hCG⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Submission.BoseGases.X N,
      (∀ j, ‖y j‖ ≤ S) → |G y| ≤ C := by
    obtain ⟨M, hM⟩ := (Submission.BoseGases.abox_compact N (by linarith : (0:ℝ) < 2 * S)).exists_bound_of_continuousOn
      hGc.continuousOn
    exact ⟨max |M| (max M 0), le_trans (abs_nonneg M) (le_max_left _ _), fun y hy =>
      le_trans (by simpa [Real.norm_eq_abs] using hM y (hbox2 hSpos.le hy))
        (le_trans (le_abs_self M) (le_max_left _ _))⟩
  obtain ⟨CdG, hCdG0, hCdG⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : Fin 3) (y : Submission.BoseGases.X N),
      (∀ j, ‖y j‖ ≤ S) → |fderiv ℝ G y (Function.update (0 : Submission.BoseGases.X N) i
        (Submission.BoseGases.kcStdBasis k))| ≤ C := by
    obtain ⟨M, hM⟩ := (Submission.BoseGases.abox_compact N (by linarith : (0:ℝ) < 2 * S)).exists_bound_of_continuousOn
      hGdfc.continuousOn
    refine ⟨max |M| (max M 0), le_trans (abs_nonneg M) (le_max_left _ _), fun k y hy => ?_⟩
    have h1 : ‖(fderiv ℝ G y) (Function.update (0 : Submission.BoseGases.X N) i
          (Submission.BoseGases.kcStdBasis k))‖ ≤ ‖fderiv ℝ G y‖ := by
      calc ‖(fderiv ℝ G y) (Function.update (0 : Submission.BoseGases.X N) i
            (Submission.BoseGases.kcStdBasis k))‖
          ≤ ‖fderiv ℝ G y‖ * ‖Function.update (0 : Submission.BoseGases.X N) i
              (Submission.BoseGases.kcStdBasis k)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = ‖fderiv ℝ G y‖ := by rw [hdirnorm' k, mul_one]
    rw [Real.norm_eq_abs] at h1
    have h3 : ‖fderiv ℝ G y‖ ≤ M := hM y (hbox2 hSpos.le hy)
    have h4 : M ≤ max |M| (max M 0) := le_trans (le_abs_self M) (le_max_left _ _)
    linarith [h1, h3, h4]
  -- the pieces
  let L : E3 → Submission.BoseGases.X N → ℝ := fun p x =>
    ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd V A i Φ) i x‖ ^ 2
  let P1 : Fin 3 → E3 → Submission.BoseGases.X N → ℝ := fun k p x =>
    ‖Work.SmallBoxTBWord.tBamp (fun z : E3 => fderiv ℝ χ z
      (Submission.BoseGases.kcStdBasis k)) p G i x‖ ^ 2
  let P2 : Fin 3 → E3 → Submission.BoseGases.X N → ℝ := fun k p x =>
    ‖Work.SmallBoxTBWord.tBamp χ p (fun y : Submission.BoseGases.X N =>
      fderiv ℝ G y (Function.update 0 i (Submission.BoseGases.kcStdBasis k))) i x‖ ^ 2
  let Rf : E3 → Submission.BoseGases.X N → ℝ := fun p x =>
    L p x + ∑ k : Fin 3, (2 * P1 k p x + 2 * P2 k p x)
  have hL0 : ∀ p x, 0 ≤ L p x := fun p x => sq_nonneg _
  have hR0 : ∀ p x, 0 ≤ Rf p x := by
    intro p x
    refine add_nonneg (hL0 p x) (Finset.sum_nonneg (fun k _ => ?_))
    have h1 : (0:ℝ) ≤ P1 k p x := sq_nonneg _
    have h2 : (0:ℝ) ≤ P2 k p x := sq_nonneg _
    linarith
  -- the derivative identity for the smooth fibre
  have hderiv : ∀ (x : Submission.BoseGases.X N) (k : Fin 3) (p : E3),
      Submission.BoseGases.kinFT (fun z : E3 => fderiv ℝ
        (fun w : E3 => ((χ w * G (Function.update x i w) : ℝ) : ℂ)) z
        (Submission.BoseGases.kcStdBasis k)) p
        = Work.SmallBoxTBWord.tBamp (fun z : E3 => fderiv ℝ χ z
            (Submission.BoseGases.kcStdBasis k)) p G i x
          + Work.SmallBoxTBWord.tBamp χ p (fun y : Submission.BoseGases.X N =>
              fderiv ℝ G y (Function.update 0 i (Submission.BoseGases.kcStdBasis k))) i x := by
    intro x k p
    have hfun : (fun z : E3 => fderiv ℝ
        (fun w : E3 => ((χ w * G (Function.update x i w) : ℝ) : ℂ)) z
        (Submission.BoseGases.kcStdBasis k))
        = (fun z : E3 => ((fderiv ℝ χ z (Submission.BoseGases.kcStdBasis k) * G (Function.update x i z)
            + χ z * fderiv ℝ G (Function.update x i z)
              (Function.update 0 i (Submission.BoseGases.kcStdBasis k)) : ℝ) : ℂ)) := by
      funext z
      rw [fderiv_fib_apply hχd hGcd i x z k]
    rw [hfun]
    have hsplit : (fun z : E3 => ((fderiv ℝ χ z (Submission.BoseGases.kcStdBasis k) * G (Function.update x i z)
          + χ z * fderiv ℝ G (Function.update x i z)
            (Function.update 0 i (Submission.BoseGases.kcStdBasis k)) : ℝ) : ℂ))
        = (fun z : E3 => ((fderiv ℝ χ z (Submission.BoseGases.kcStdBasis k) * G (Function.update x i z) : ℝ) : ℂ)
            + ((χ z * fderiv ℝ G (Function.update x i z)
            (Function.update 0 i (Submission.BoseGases.kcStdBasis k)) : ℝ) : ℂ)) := by
      funext z
      exact Complex.ofReal_add _ _
    rw [hsplit]
    have hcs1 : HasCompactSupport (fun z : E3 =>
        ((fderiv ℝ χ z (Submission.BoseGases.kcStdBasis k) * G (Function.update x i z) : ℝ) : ℂ)) :=
      (((hχcs.fderiv ℝ).comp_left
          (g := fun T : E3 →L[ℝ] ℝ => T (Submission.BoseGases.kcStdBasis k)) (by simp)).mul_right).comp_left
        (g := fun r : ℝ => (r : ℂ)) (by simp)
    have hcs2 : HasCompactSupport (fun z : E3 =>
        ((χ z * fderiv ℝ G (Function.update x i z)
          (Function.update 0 i (Submission.BoseGases.kcStdBasis k)) : ℝ) : ℂ)) :=
      (hχcs.mul_right (f' := fun z : E3 => fderiv ℝ G (Function.update x i z)
          (Function.update 0 i (Submission.BoseGases.kcStdBasis k)))).comp_left
        (g := fun r : ℝ => (r : ℂ)) (by simp)
    rw [Work.BoseFixB2.Polar.FsTAux.kinFT_add]
    · rw [tBamp_eq_kinFT, tBamp_eq_kinFT]
    · exact ((Complex.continuous_ofReal.comp
        ((hχdfc.clm_apply continuous_const).mul (hGc.comp (by fun_prop)))).integrable_of_hasCompactSupport hcs1)
    · exact ((Complex.continuous_ofReal.comp
        (hχc.mul ((hGdfc.clm_apply continuous_const).comp (by fun_prop)))).integrable_of_hasCompactSupport hcs2)
  -- the pointwise bound
  have hmain : ∀ (p : E3) (x : Submission.BoseGases.X N), x ∈ Submission.BoseGases.abox N ℓ →
      Submission.BoseGases.fsKinCoeff c ‖p‖ * L p x ≤ (1 + |c|) ^ 2 * Rf p x := by
    intro p x hx
    have hfib : Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd V A i Φ) i x
        = Submission.BoseGases.kinFT (fun z : E3 =>
            ((χ z * G (Function.update x i z) : ℝ) : ℂ)) p := by
      rw [hGdef]
      exact tBamp_boxQInd_eq_kinFT_boxQ hχA i Φ p x
    have hfibcd : ContDiff ℝ 1 (fun z : E3 => ((χ z * G (Function.update x i z) : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp
        (hχ1.mul ((hGcd.of_le (WithTop.coe_le_coe.mpr le_top)).comp
          (Commons.Analysis.Calculus.contDiff_update_apply 1 x i)))
    have hfibcs : HasCompactSupport (fun z : E3 => ((χ z * G (Function.update x i z) : ℝ) : ℂ)) :=
      (hχcs.mul_right (f' := fun z : E3 => G (Function.update x i z))).comp_left
        (g := fun r : ℝ => (r : ℂ)) (by simp)
    have hkey := fsKinCoeff_mul_normSq_kinFT_le (c := c) hfibcd hfibcs p
    have hkey' : Submission.BoseGases.fsKinCoeff c ‖p‖ * L p x
        ≤ (1 + |c|) ^ 2 * (L p x + ∑ k : Fin 3,
            ‖Submission.BoseGases.kinFT (fun z : E3 => fderiv ℝ
              (fun w : E3 => ((χ w * G (Function.update x i w) : ℝ) : ℂ)) z
              (Submission.BoseGases.kcStdBasis k)) p‖ ^ 2) := by
      have h1 : L p x = ‖Submission.BoseGases.kinFT (fun z : E3 =>
          ((χ z * G (Function.update x i z) : ℝ) : ℂ)) p‖ ^ 2 := by
        rw [← hfib]
      rw [h1]
      exact hkey
    refine le_trans hkey' (mul_le_mul_of_nonneg_left ?_ (by positivity))
    refine add_le_add le_rfl (Finset.sum_le_sum (fun k _ => ?_))
    rw [hderiv x k p]
    have h1 : ‖Work.SmallBoxTBWord.tBamp (fun z : E3 => fderiv ℝ χ z
          (Submission.BoseGases.kcStdBasis k)) p G i x
        + Work.SmallBoxTBWord.tBamp χ p (fun y : Submission.BoseGases.X N =>
            fderiv ℝ G y (Function.update 0 i (Submission.BoseGases.kcStdBasis k))) i x‖ ^ 2
        ≤ 2 * ‖Work.SmallBoxTBWord.tBamp (fun z : E3 => fderiv ℝ χ z
            (Submission.BoseGases.kcStdBasis k)) p G i x‖ ^ 2
          + 2 * ‖Work.SmallBoxTBWord.tBamp χ p (fun y : Submission.BoseGases.X N =>
              fderiv ℝ G y (Function.update 0 i (Submission.BoseGases.kcStdBasis k))) i x‖ ^ 2 := by
      let A : ℝ := ‖Work.SmallBoxTBWord.tBamp (fun z : E3 => fderiv ℝ χ z
          (Submission.BoseGases.kcStdBasis k)) p G i x‖
      let B : ℝ := ‖Work.SmallBoxTBWord.tBamp χ p (fun y : Submission.BoseGases.X N =>
            fderiv ℝ G y (Function.update 0 i (Submission.BoseGases.kcStdBasis k))) i x‖
      change ‖Work.SmallBoxTBWord.tBamp (fun z : E3 => fderiv ℝ χ z
            (Submission.BoseGases.kcStdBasis k)) p G i x
          + Work.SmallBoxTBWord.tBamp χ p (fun y : Submission.BoseGases.X N =>
              fderiv ℝ G y (Function.update 0 i (Submission.BoseGases.kcStdBasis k))) i x‖ ^ 2
        ≤ 2 * A ^ 2 + 2 * B ^ 2
      have h3 : ‖Work.SmallBoxTBWord.tBamp (fun z : E3 => fderiv ℝ χ z
            (Submission.BoseGases.kcStdBasis k)) p G i x
          + Work.SmallBoxTBWord.tBamp χ p (fun y : Submission.BoseGases.X N =>
              fderiv ℝ G y (Function.update 0 i (Submission.BoseGases.kcStdBasis k))) i x‖ ^ 2
          ≤ (A + B) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
      have h4 := sq_nonneg (A - B)
      linarith [h3, h4]
    exact h1
  -- ══ 5a. shape helpers ══
  set KL : ℝ := (2 * Real.pi) ^ 3 * (ρχ ^ 2 * CG ^ 2 * Vm) with hKLdef
  set K1 : ℝ := (2 * Real.pi) ^ 3 * (ρd ^ 2 * CG ^ 2 * Vm) with hK1def
  set K2 : ℝ := (2 * Real.pi) ^ 3 * (ρχ ^ 2 * CdG ^ 2 * Vm) with hK2def
  set CB : ℝ≥0∞ := ENNReal.ofReal KL + ∑ _k : Fin 3,
    (ENNReal.ofReal 2 * ENNReal.ofReal K1 + ENNReal.ofReal 2 * ENNReal.ofReal K2) with hCBdef
  have hdχc : ∀ k : Fin 3, Continuous (fun z : E3 =>
      fderiv ℝ χ z (Submission.BoseGases.kcStdBasis k)) :=
    fun k => hχdfc.clm_apply continuous_const
  have hdiGc : ∀ k : Fin 3, Continuous (fun y : Submission.BoseGases.X N =>
      fderiv ℝ G y (Function.update 0 i (Submission.BoseGases.kcStdBasis k))) :=
    fun k => hGdfc.clm_apply continuous_const
  have hdχcs : ∀ k : Fin 3, HasCompactSupport (fun z : E3 => fderiv ℝ χ z
      (Submission.BoseGases.kcStdBasis k)) :=
    fun k => (hχcs.fderiv ℝ).comp_left
      (g := fun T : E3 →L[ℝ] ℝ => T (Submission.BoseGases.kcStdBasis k)) (by simp)
  have hdχS : ∀ (k : Fin 3) (z : E3),
      fderiv ℝ χ z (Submission.BoseGases.kcStdBasis k) ≠ 0 → ‖z‖ ≤ S := by
    intro k z hz
    have hz' : fderiv ℝ χ z ≠ 0 := fun h0 => hz (by rw [h0]; rfl)
    exact le_trans (hR₀dχ z (subset_tsupport _ (Function.mem_support.mpr hz'))) hR₀S
  have hRRχ : ∀ z : E3, χ z ≠ 0 → ‖z‖ ≤ S := fun z hz =>
    le_trans (hR₀χ z (subset_tsupport χ (Function.mem_support.mpr hz))) hR₀S
  have hmeasΨ : Measurable (Work.UBBInputs8.boxQInd V A i Φ) :=
    Work.SlotWord.measurable_boxQInd V A (hAcomp.isClosed.measurableSet) i hΦ.continuous.measurable
  have hLid : ∀ (p : E3) (x : Submission.BoseGases.X N),
      L p x = ‖Work.SmallBoxTBWord.tBamp χ p G i x‖ ^ 2 := by
    intro p x
    have h := Work.UBBInputs9.A.tBamp_boxQInd (volA := V) (A := A) (χ := χ) hχA Φ i p x
    change ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd V A i Φ) i x‖ ^ 2
      = ‖Work.SmallBoxTBWord.tBamp χ p G i x‖ ^ 2
    rw [h, hGdef]
  have h1nn : ∀ (k : Fin 3) (p : E3) (x : Submission.BoseGases.X N),
      (0:ℝ) ≤ 2 * P1 k p x := fun k p x => mul_nonneg (by norm_num) (sq_nonneg _)
  have h2nn : ∀ (k : Fin 3) (p : E3) (x : Submission.BoseGases.X N),
      (0:ℝ) ≤ 2 * P2 k p x := fun k p x => mul_nonneg (by norm_num) (sq_nonneg _)
  have hSn : ∀ (p : E3) (x : Submission.BoseGases.X N),
      (0:ℝ) ≤ ∑ k : Fin 3, (2 * P1 k p x + 2 * P2 k p x) :=
    fun p x => Finset.sum_nonneg fun k _ => add_nonneg (h1nn k p x) (h2nn k p x)
  -- ══ 5b. the `ℝ≥0∞`-valued refinement of `Rf`, and its measurability ══
  let Rs : E3 → Submission.BoseGases.X N → ℝ≥0∞ := fun p x =>
    ENNReal.ofReal (L p x) + ∑ k : Fin 3,
      (ENNReal.ofReal (2 * P1 k p x) + ENNReal.ofReal (2 * P2 k p x))
  have hRfdec : ∀ (p : E3) (x : Submission.BoseGases.X N), ENNReal.ofReal (Rf p x) = Rs p x := by
    intro p x
    change ENNReal.ofReal (L p x + ∑ k : Fin 3, (2 * P1 k p x + 2 * P2 k p x))
      = ENNReal.ofReal (L p x) + ∑ k : Fin 3,
          (ENNReal.ofReal (2 * P1 k p x) + ENNReal.ofReal (2 * P2 k p x))
    rw [ENNReal.ofReal_add (sq_nonneg _) (hSn p x)]
    congr 1
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => add_nonneg (h1nn k p x) (h2nn k p x))]
    exact Finset.sum_congr rfl (fun k _ => ENNReal.ofReal_add (h1nn k p x) (h2nn k p x))
  have hRsm : Measurable (fun q : E3 × Submission.BoseGases.X N => Rs q.1 q.2) := by
    have hLpart : Measurable (fun q : E3 × Submission.BoseGases.X N =>
        ENNReal.ofReal (L q.1 q.2)) := by
      change Measurable (fun q : E3 × Submission.BoseGases.X N => ENNReal.ofReal
        (‖Work.SmallBoxTBWord.tBamp χ q.1 (Work.UBBInputs8.boxQInd V A i Φ) i q.2‖ ^ 2))
      exact measurable_ofReal_amp hχc hmeasΨ i
    have h1part : ∀ k : Fin 3, Measurable (fun q : E3 × Submission.BoseGases.X N =>
        ENNReal.ofReal (2 * P1 k q.1 q.2)) := by
      intro k
      change Measurable (fun q : E3 × Submission.BoseGases.X N => ENNReal.ofReal
        (2 * ‖Work.SmallBoxTBWord.tBamp (fun z : E3 => fderiv ℝ χ z
          (Submission.BoseGases.kcStdBasis k)) q.1 G i q.2‖ ^ 2))
      exact ENNReal.measurable_ofReal.comp
        (measurable_const.mul (measurable_tBamp_pair_gen (hdχc k) hGc.measurable i))
    have h2part : ∀ k : Fin 3, Measurable (fun q : E3 × Submission.BoseGases.X N =>
        ENNReal.ofReal (2 * P2 k q.1 q.2)) := by
      intro k
      change Measurable (fun q : E3 × Submission.BoseGases.X N => ENNReal.ofReal
        (2 * ‖Work.SmallBoxTBWord.tBamp χ q.1 (fun y : Submission.BoseGases.X N =>
          fderiv ℝ G y (Function.update 0 i (Submission.BoseGases.kcStdBasis k))) i q.2‖ ^ 2))
      exact ENNReal.measurable_ofReal.comp
        (measurable_const.mul (measurable_tBamp_pair_gen hχc (hdiGc k).measurable i))
    have hSpart : Measurable (fun q : E3 × Submission.BoseGases.X N => ∑ k : Fin 3,
        (ENNReal.ofReal (2 * P1 k q.1 q.2) + ENNReal.ofReal (2 * P2 k q.1 q.2))) :=
      Finset.measurable_sum _ (fun k _ => (h1part k).add (h2part k))
    change Measurable (fun q : E3 × Submission.BoseGases.X N =>
      ENNReal.ofReal (L q.1 q.2) + ∑ k : Fin 3,
        (ENNReal.ofReal (2 * P1 k q.1 q.2) + ENNReal.ofReal (2 * P2 k q.1 q.2)))
    exact hLpart.add hSpart
  have hLsm : Measurable (fun q : E3 × Submission.BoseGases.X N =>
      ENNReal.ofReal (L q.1 q.2)) := by
    change Measurable (fun q : E3 × Submission.BoseGases.X N => ENNReal.ofReal
      (‖Work.SmallBoxTBWord.tBamp χ q.1 (Work.UBBInputs8.boxQInd V A i Φ) i q.2‖ ^ 2))
    exact measurable_ofReal_amp hχc hmeasΨ i
  have hLxm : ∀ p : E3, Measurable (fun x : Submission.BoseGases.X N =>
      ENNReal.ofReal (L p x)) := fun p =>
    Measurable.of_uncurry_left (f := fun p x => ENNReal.ofReal (L p x)) hLsm (x := p)
  have hLxf : ∀ x : Submission.BoseGases.X N, Measurable (fun p : E3 =>
      ENNReal.ofReal (L p x)) := fun x =>
    Measurable.of_uncurry_right (f := fun p x => ENNReal.ofReal (L p x)) hLsm (y := x)
  have hP1xm : ∀ (k : Fin 3) (x : Submission.BoseGases.X N),
      Measurable (fun p : E3 => ENNReal.ofReal (2 * P1 k p x)) := fun k x =>
    measurable_ofReal_const_mul_amp_fst (hdχc k) hGc.measurable i 2 x
  have hP2xm : ∀ (k : Fin 3) (x : Submission.BoseGases.X N),
      Measurable (fun p : E3 => ENNReal.ofReal (2 * P2 k p x)) := fun k x =>
    measurable_ofReal_const_mul_amp_fst hχc (hdiGc k).measurable i 2 x
  have hRsxm : ∀ p : E3, Measurable (fun x : Submission.BoseGases.X N => Rs p x) := fun p =>
    Measurable.of_uncurry_left (f := fun p x => Rs p x) hRsm (x := p)
  -- ══ 5c. the per-`x` bound on the `p`-lintegral ══
  have hb0' : ∀ x ∈ Submission.BoseGases.abox N ℓ, (∫⁻ p : E3, ENNReal.ofReal
      (‖Work.SmallBoxTBWord.tBamp χ p G i x‖ ^ 2)) ≤ ENNReal.ofReal KL := by
    intro x hx
    have hb := tBamp_piece_bound hχc hχcs hℓ hρχ0 hCG0 hρχ hGc hCG hRRχ hℓS hvolχ hVm0 hx i
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hb.1
      (Filter.Eventually.of_forall (fun p => sq_nonneg _)), hKLdef]
    exact ENNReal.ofReal_le_ofReal hb.2.2
  have hperx : ∀ᵐ x ∂((volume : Measure (Submission.BoseGases.X N)).restrict
      (Submission.BoseGases.abox N ℓ)), (∫⁻ p : E3, Rs p x) ≤ CB := by
    filter_upwards [MeasureTheory.ae_restrict_mem (Submission.BoseGases.abox_measurable N ℓ)]
      with x hx
    have hb0 : (∫⁻ p : E3, ENNReal.ofReal (L p x)) ≤ ENNReal.ofReal KL :=
      (MeasureTheory.lintegral_congr (f := fun p : E3 => ENNReal.ofReal (L p x))
        (g := fun p : E3 => ENNReal.ofReal (‖Work.SmallBoxTBWord.tBamp χ p G i x‖ ^ 2))
        (fun p => by rw [hLid p x])).trans_le (hb0' x hx)
    have hb1 : ∀ k : Fin 3, (∫⁻ p : E3, ENNReal.ofReal (2 * P1 k p x))
        ≤ ENNReal.ofReal 2 * ENNReal.ofReal K1 := by
      intro k
      have heq : (∫⁻ p : E3, ENNReal.ofReal (2 * P1 k p x))
          = ∫⁻ p : E3, ENNReal.ofReal 2 * ENNReal.ofReal
              (‖Work.SmallBoxTBWord.tBamp (fun z : E3 => fderiv ℝ χ z
                (Submission.BoseGases.kcStdBasis k)) p G i x‖ ^ 2) := by
        refine MeasureTheory.lintegral_congr (fun p => ?_)
        change ENNReal.ofReal (2 * ‖Work.SmallBoxTBWord.tBamp (fun z : E3 => fderiv ℝ χ z
            (Submission.BoseGases.kcStdBasis k)) p G i x‖ ^ 2) = _
        rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      rw [heq, MeasureTheory.lintegral_const_mul _ (measurable_ofReal_amp_fst (hdχc k)
        hGc.measurable i x)]
      refine mul_le_mul_of_nonneg_left ?_ bot_le
      have hb := tBamp_piece_bound (hdχc k) (hdχcs k) hℓ hρd0 hCG0 (fun z => hρd k z) hGc hCG
        (hdχS k) hℓS (hvolP1 k) hVm0 hx i
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hb.1
        (Filter.Eventually.of_forall (fun p => sq_nonneg _)), hK1def]
      exact ENNReal.ofReal_le_ofReal hb.2.2
    have hb2 : ∀ k : Fin 3, (∫⁻ p : E3, ENNReal.ofReal (2 * P2 k p x))
        ≤ ENNReal.ofReal 2 * ENNReal.ofReal K2 := by
      intro k
      have heq : (∫⁻ p : E3, ENNReal.ofReal (2 * P2 k p x))
          = ∫⁻ p : E3, ENNReal.ofReal 2 * ENNReal.ofReal
              (‖Work.SmallBoxTBWord.tBamp χ p (fun y : Submission.BoseGases.X N =>
                fderiv ℝ G y (Function.update 0 i (Submission.BoseGases.kcStdBasis k))) i x‖ ^ 2) := by
        refine MeasureTheory.lintegral_congr (fun p => ?_)
        change ENNReal.ofReal (2 * ‖Work.SmallBoxTBWord.tBamp χ p (fun y : Submission.BoseGases.X N =>
            fderiv ℝ G y (Function.update 0 i (Submission.BoseGases.kcStdBasis k))) i x‖ ^ 2) = _
        rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      rw [heq, MeasureTheory.lintegral_const_mul _ (measurable_ofReal_amp_fst hχc
        (hdiGc k).measurable i x)]
      refine mul_le_mul_of_nonneg_left ?_ bot_le
      have hb := tBamp_piece_bound hχc hχcs hℓ hρχ0 hCdG0 hρχ
        (hdiGc k) (fun y hy => hCdG k y hy) hRRχ hℓS hvolχ hVm0 hx i
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hb.1
        (Filter.Eventually.of_forall (fun p => sq_nonneg _)), hK2def]
      exact ENNReal.ofReal_le_ofReal hb.2.2
    have hdec : ∀ p : E3, Rs p x = ENNReal.ofReal (L p x) + ∑ k : Fin 3,
        (ENNReal.ofReal (2 * P1 k p x) + ENNReal.ofReal (2 * P2 k p x)) := fun p => rfl
    have hsplit0 : (∫⁻ p : E3, (ENNReal.ofReal (L p x) + ∑ k : Fin 3,
          (ENNReal.ofReal (2 * P1 k p x) + ENNReal.ofReal (2 * P2 k p x))))
        = (∫⁻ p : E3, ENNReal.ofReal (L p x))
          + ∑ k : Fin 3, ((∫⁻ p : E3, ENNReal.ofReal (2 * P1 k p x))
              + (∫⁻ p : E3, ENNReal.ofReal (2 * P2 k p x))) := by
      rw [MeasureTheory.lintegral_add_left (hLxf x)]
      congr 1
      have hsummand : ∀ (k : Fin 3) (_ : k ∈ (Finset.univ : Finset (Fin 3))),
          Measurable (fun p : E3 => ENNReal.ofReal (2 * P1 k p x)
            + ENNReal.ofReal (2 * P2 k p x)) := fun k _ => (hP1xm k x).add (hP2xm k x)
      rw [MeasureTheory.lintegral_finsetSum Finset.univ hsummand]
      exact Finset.sum_congr rfl (fun k _ => by
        rw [MeasureTheory.lintegral_add_left (hP1xm k x)])
    calc (∫⁻ p : E3, Rs p x)
        = ∫⁻ p : E3, (ENNReal.ofReal (L p x) + ∑ k : Fin 3,
            (ENNReal.ofReal (2 * P1 k p x) + ENNReal.ofReal (2 * P2 k p x))) :=
          MeasureTheory.lintegral_congr hdec
      _ = (∫⁻ p : E3, ENNReal.ofReal (L p x))
            + ∑ k : Fin 3, ((∫⁻ p : E3, ENNReal.ofReal (2 * P1 k p x))
              + (∫⁻ p : E3, ENNReal.ofReal (2 * P2 k p x))) := hsplit0
      _ ≤ ENNReal.ofReal KL + ∑ _k : Fin 3,
            (ENNReal.ofReal 2 * ENNReal.ofReal K1 + ENNReal.ofReal 2 * ENNReal.ofReal K2) :=
          add_le_add hb0 (Finset.sum_le_sum (fun k _ => add_le_add (hb1 k) (hb2 k)))
      _ = CB := by rw [hCBdef]
  -- ══ 5d. the marginal bound and finiteness ══
  have hKmeas : Measurable (fun p : E3 => ∫⁻ x in Submission.BoseGases.abox N ℓ, Rs p x) :=
    hRsm.lintegral_prod_right (ν := (volume : Measure (Submission.BoseGases.X N)).restrict
      (Submission.BoseGases.abox N ℓ))
  have hCBlt : CB < ⊤ := by
    rw [hCBdef]
    refine ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ?_⟩
    exact ENNReal.sum_lt_top.mpr (fun k _ => ENNReal.add_lt_top.mpr
      ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top,
       ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top⟩)
  have hswap : (∫⁻ p : E3, ∫⁻ x in Submission.BoseGases.abox N ℓ, Rs p x)
      = ∫⁻ x in Submission.BoseGases.abox N ℓ, (∫⁻ p : E3, Rs p x) :=
    MeasureTheory.lintegral_lintegral_swap
      (hRsm.aemeasurable.mono_measure
        (MeasureTheory.Measure.prod_mono le_rfl MeasureTheory.Measure.restrict_le_self))
  have hKle : (∫⁻ p : E3, ∫⁻ x in Submission.BoseGases.abox N ℓ, Rs p x)
      ≤ CB * volume (Submission.BoseGases.abox N ℓ) := by
    rw [hswap]
    calc (∫⁻ x in Submission.BoseGases.abox N ℓ, (∫⁻ p : E3, Rs p x))
        ≤ ∫⁻ _x in Submission.BoseGases.abox N ℓ, CB :=
          MeasureTheory.lintegral_mono_ae hperx
      _ = CB * volume (Submission.BoseGases.abox N ℓ) := by
          rw [MeasureTheory.lintegral_const, MeasureTheory.Measure.restrict_apply_univ]
  have hpt : ∀ p : E3, ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ *
        ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox N ℓ, L p x))
      ≤ ENNReal.ofReal ((ℓ ^ 3)⁻¹) *
          (ENNReal.ofReal ((1 + |c|) ^ 2) *
            (∫⁻ x in Submission.BoseGases.abox N ℓ, Rs p x)) := by
    intro p
    have hB0 : (0:ℝ) ≤ (ℓ ^ 3)⁻¹ := inv_nonneg.mpr (by positivity)
    have hphi0 : (0:ℝ) ≤ Submission.BoseGases.fsKinCoeff c ‖p‖ := sq_nonneg _
    have e1 : ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox N ℓ, L p x))
        = ENNReal.ofReal ((ℓ ^ 3)⁻¹) *
            (ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖) *
              ENNReal.ofReal (∫ x in Submission.BoseGases.abox N ℓ, L p x)) := by
      rw [ENNReal.ofReal_mul hphi0, ENNReal.ofReal_mul hB0]
      ring
    rw [e1]
    refine mul_le_mul_of_nonneg_left ?_ bot_le
    calc ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖) *
            ENNReal.ofReal (∫ x in Submission.BoseGases.abox N ℓ, L p x)
        ≤ ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖) *
            (∫⁻ x in Submission.BoseGases.abox N ℓ, ENNReal.ofReal (L p x)) :=
          mul_le_mul_of_nonneg_left (ofReal_integral_le_lintegral (fun x => sq_nonneg _)) bot_le
      _ = (∫⁻ x in Submission.BoseGases.abox N ℓ,
            ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖) * ENNReal.ofReal (L p x)) := by
          rw [← MeasureTheory.lintegral_const_mul _ (hLxm p)]
      _ ≤ (∫⁻ x in Submission.BoseGases.abox N ℓ,
            ENNReal.ofReal ((1 + |c|) ^ 2) * Rs p x) := by
          refine MeasureTheory.lintegral_mono_ae ?_
          filter_upwards [MeasureTheory.ae_restrict_mem (Submission.BoseGases.abox_measurable N ℓ)]
            with x hx
          have h2 : ENNReal.ofReal ((1 + |c|) ^ 2) * Rs p x
              = ENNReal.ofReal ((1 + |c|) ^ 2 * Rf p x) := by
            rw [← hRfdec p x, ENNReal.ofReal_mul (sq_nonneg _)]
          rw [show ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖) *
                ENNReal.ofReal (L p x)
              = ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ * L p x)
            from (ENNReal.ofReal_mul hphi0).symm, h2]
          exact ENNReal.ofReal_le_ofReal (hmain p x hx)
      _ = ENNReal.ofReal ((1 + |c|) ^ 2) *
            (∫⁻ x in Submission.BoseGases.abox N ℓ, Rs p x) := by
          rw [← MeasureTheory.lintegral_const_mul _ (hRsxm p)]
  have hbound : (∫⁻ p : E3, ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ *
        ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox N ℓ, L p x)))
      ≤ ENNReal.ofReal ((ℓ ^ 3)⁻¹) * (ENNReal.ofReal ((1 + |c|) ^ 2) *
          (CB * volume (Submission.BoseGases.abox N ℓ))) := by
    calc (∫⁻ p : E3, ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox N ℓ, L p x)))
        ≤ ∫⁻ p : E3, ENNReal.ofReal ((ℓ ^ 3)⁻¹) * (ENNReal.ofReal ((1 + |c|) ^ 2) *
            (∫⁻ x in Submission.BoseGases.abox N ℓ, Rs p x)) :=
          MeasureTheory.lintegral_mono hpt
      _ = ENNReal.ofReal ((ℓ ^ 3)⁻¹) * (ENNReal.ofReal ((1 + |c|) ^ 2) *
            (∫⁻ p : E3, ∫⁻ x in Submission.BoseGases.abox N ℓ, Rs p x)) := by
          have hK2meas : Measurable (fun p : E3 => ENNReal.ofReal ((1 + |c|) ^ 2) *
              (∫⁻ x in Submission.BoseGases.abox N ℓ, Rs p x)) :=
            measurable_const.mul hKmeas
          rw [MeasureTheory.lintegral_const_mul _ hK2meas,
            MeasureTheory.lintegral_const_mul _ hKmeas]
      _ ≤ ENNReal.ofReal ((ℓ ^ 3)⁻¹) * (ENNReal.ofReal ((1 + |c|) ^ 2) *
            (CB * volume (Submission.BoseGases.abox N ℓ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hKle bot_le) bot_le
  have haesm : AEStronglyMeasurable (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖ *
      ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox N ℓ, L p x)) volume := by
    have h1 : StronglyMeasurable (fun p : E3 =>
        ∫ x in Submission.BoseGases.abox N ℓ, L p x) :=
      (measurable_tBamp_pair_gen hχc hmeasΨ i).stronglyMeasurable.integral_prod_right'
        (ν := (volume : Measure (Submission.BoseGases.X N)).restrict (Submission.BoseGases.abox N ℓ))
    have h3 : Continuous (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖) := by
      rw [show (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖)
          = (fun r : ℝ => (max (r - c) 0) ^ 2) ∘ fun p : E3 => ‖p‖ from rfl]
      exact (((continuous_id.sub continuous_const).max continuous_const).pow 2).comp continuous_norm
    exact h3.aestronglyMeasurable.mul ((h1.aestronglyMeasurable).const_mul ((ℓ ^ 3)⁻¹))
  refine ⟨haesm, ?_⟩
  have hnonneg : 0 ≤ᵐ[volume] (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖ *
      ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox N ℓ, L p x)) :=
    Filter.Eventually.of_forall fun p => mul_nonneg (sq_nonneg _) (mul_nonneg
      (inv_nonneg.mpr (le_of_lt (pow_pos hℓ 3)))
      (MeasureTheory.integral_nonneg fun x => sq_nonneg _))
  rw [MeasureTheory.hasFiniteIntegral_iff_ofReal hnonneg]
  exact lt_of_le_of_lt hbound
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top hCBlt (Submission.BoseGases.abox_compact N hℓ).measure_lt_top)))

/-! ## 6. The sector piece -/

/-- **The null-box degenerate case.** If the small box `A` is null then the fibre
`Q_{A,i}Ψ(·[i↦z])` vanishes for almost every `z`, hence so does the amplitude, and the whole
`p`-integrand is identically `0`. -/
lemma integrable_of_null_box {N : ℕ} {ℓ V c : ℝ} {A : Set E3} {χ : E3 → ℝ}
    {Ψ : Submission.BoseGases.X N → ℝ} (i : Fin N) (hA : (volume : Measure E3) A = 0) :
    MeasureTheory.Integrable (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖ *
      ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox N ℓ,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd V A i Ψ) i x‖ ^ 2)) := by
  have hAae : ∀ᵐ z ∂(volume : Measure E3), z ∉ A := by
    rw [MeasureTheory.ae_iff]
    have hset : {z : E3 | ¬ z ∉ A} = A := by ext z; simp
    rw [hset]; exact hA
  have htb : ∀ (p : E3) (x : Submission.BoseGases.X N),
      Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd V A i Ψ) i x = 0 := by
    intro p x
    rw [Work.SmallBoxTBWord.tBamp]
    refine MeasureTheory.integral_eq_zero_of_ae ?_
    filter_upwards [hAae] with z hz
    have hQ : Work.UBBInputs8.boxQInd V A i Ψ (Function.update x i z) = 0 := by
      simp only [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd, Function.update_self]
      rw [Set.indicator_of_notMem hz]
      ring
    rw [hQ]
    simp
  have hzero : (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖ *
      ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox N ℓ,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd V A i Ψ) i x‖ ^ 2))
      = fun _ => 0 := by
    funext p
    have hI : (∫ x in Submission.BoseGases.abox N ℓ,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd V A i Ψ) i x‖ ^ 2) = 0 := by
      refine MeasureTheory.integral_eq_zero_of_ae ?_
      exact Filter.Eventually.of_forall (fun x => by simp [htb p x])
    rw [hI]; simp
  rw [hzero]
  exact MeasureTheory.integrable_zero E3 ℝ volume

/-- **The sector-piece companion of `integrable_smooth`.**  The sector piece is pointwise
dominated by the state (`sectorPieceBoxQIndAmpLe`), so its symbol-weighted windowed amplitude is
integrable as soon as the state's is. -/
lemma integrable_sectorPiece {N : ℕ} {ℓ V c : ℝ} {A : Set E3} {χ : E3 → ℝ}
    (hℓ : 0 < ℓ) (hχ2 : ContDiff ℝ 2 χ) (hχcs : HasCompactSupport χ)
    (hAmeas : MeasurableSet A) (hAcsub : A ⊆ Submission.BoseGases.acube ℓ)
    (hχA : ∀ z : E3, z ∉ A → χ z = 0) (hAcomp : IsCompact A)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (k : ℕ) (i : Fin N) :
    MeasureTheory.Integrable (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖ *
      ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox N ℓ,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd V A i
          (Work.FockBridge.sectorPiece A k Φ)) i x‖ ^ 2)) := by
  classical
  have hχ1 : ContDiff ℝ 1 χ := hχ2.of_le (by norm_num)
  have hχc : Continuous χ := hχ1.continuous
  have hg : MeasureTheory.Integrable (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖ *
      ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox N ℓ,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd V A i Φ) i x‖ ^ 2)) :=
    integrable_smooth hℓ hχ2 hχcs hχA hAcomp hΦ i
  have hΨsm : Measurable (Work.FockBridge.sectorPiece A k Φ) :=
    hΦ.continuous.measurable.indicator (Work.FockBridge.sectorSet_measurable A hAmeas k)
  have hΨim : Measurable (Work.UBBInputs8.boxQInd V A i (Work.FockBridge.sectorPiece A k Φ)) :=
    Work.SlotWord.measurable_boxQInd V A hAmeas i hΨsm
  have hf : AEStronglyMeasurable (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖ *
      ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox N ℓ,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd V A i
          (Work.FockBridge.sectorPiece A k Φ)) i x‖ ^ 2)) volume := by
    have hstrong : StronglyMeasurable (fun p : E3 =>
        ∫ x in Submission.BoseGases.abox N ℓ,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd V A i
            (Work.FockBridge.sectorPiece A k Φ)) i x‖ ^ 2) :=
      (measurable_tBamp_pair_gen hχc hΨim i).stronglyMeasurable.integral_prod_right'
        (ν := (volume : Measure (Submission.BoseGases.X N)).restrict
          (Submission.BoseGases.abox N ℓ))
    have h3 : Continuous (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖) := by
      rw [show (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖)
          = (fun r : ℝ => (max (r - c) 0) ^ 2) ∘ fun p : E3 => ‖p‖ from rfl]
      exact (((continuous_id.sub continuous_const).max continuous_const).pow 2).comp continuous_norm
    exact h3.aestronglyMeasurable.mul (hstrong.aestronglyMeasurable.const_mul ((ℓ ^ 3)⁻¹))
  refine MeasureTheory.Integrable.mono' hg hf ?_
  filter_upwards with p
  have hB0 : (0:ℝ) ≤ (ℓ ^ 3)⁻¹ := inv_nonneg.mpr (by positivity)
  have hphi0 : (0:ℝ) ≤ Submission.BoseGases.fsKinCoeff c ‖p‖ := sq_nonneg _
  have hIs : (0:ℝ) ≤ ∫ x in Submission.BoseGases.abox N ℓ,
      ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd V A i
        (Work.FockBridge.sectorPiece A k Φ)) i x‖ ^ 2 :=
    MeasureTheory.integral_nonneg (fun x => sq_nonneg _)
  have hIle : (∫ x in Submission.BoseGases.abox N ℓ,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd V A i
          (Work.FockBridge.sectorPiece A k Φ)) i x‖ ^ 2)
      ≤ ∫ x in Submission.BoseGases.abox N ℓ,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd V A i Φ) i x‖ ^ 2 :=
    MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => sq_nonneg _))
      (Work.BoseFixB1.tBamp_boxQInd_integrableOn_sq hℓ hAmeas hAcsub hχc hχcs hΦ.continuous i p)
      (Filter.Eventually.of_forall (fun x => pow_le_pow_left₀ (norm_nonneg _)
        (Work.BoseFixB1.sectorPieceBoxQIndAmpLe hAmeas i p x) 2))
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hphi0 (mul_nonneg hB0 hIs))]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hIle hB0) hphi0

/-- **`p`-integrability of the symbol-weighted sector-piece amplitude at the sliding small box**:
the window `chiSmallB`, the box projection `boxQInd` over `B(u) = dlBox ℓ d u`, the sector piece
of a box state, and the symbol `fsKinCoeff` at the corpus's `sbCut`. -/
theorem sectorPiece_word_integrable {n : ℕ} {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    (h : Work.UBB.ScatSol v) (u : EuclideanSpace ℝ (Fin 3)) (k : ℕ)
    {Φ : Work.BoseKinLoc.BoxState n (Work.BoseFixB1B.PBℓ v μ)} :
    ∀ i : Fin n, MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (BoseGases.a v)) ‖p‖ *
        (((Work.BoseFixB1B.PBℓ v μ) ^ 3)⁻¹ *
          ∫ x in Submission.BoseGases.abox n (Work.BoseFixB1B.PBℓ v μ),
            ‖Work.SmallBoxTBWord.tBamp
                (Submission.BoseGases.chiSmallB (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u)
                p
                (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u)
                  (Work.BoseFixB1B.PBB v μ u) i
                  (Work.FockBridge.sectorPiece (Work.BoseFixB1B.PBB v μ u) k (Φ : Submission.BoseGases.X n → ℝ)))
                i x‖ ^ 2)) := by
  intro i
  by_cases ht : 0 < μ * (BoseGases.a v) ^ 3
  · -- main case: the box is nondegenerate
    have hμa : 0 < μ * BoseGases.a v := by
      have ha : BoseGases.a v ≠ 0 := by
        intro h0
        rw [h0, zero_pow (by norm_num : (3:ℕ) ≠ 0), mul_zero] at ht
        exact lt_irrefl 0 ht
      have hsq : (0:ℝ) < (BoseGases.a v) ^ 2 * (μ * BoseGases.a v) := by
        rw [mul_comm, show (μ * BoseGases.a v) * (BoseGases.a v) ^ 2
          = μ * (BoseGases.a v) ^ 3 from by ring]
        exact ht
      exact pos_of_mul_pos_right hsq (sq_nonneg _)
    have hEll : 0 < Work.BoseFixB1B.PBℓ v μ := by
      show (0:ℝ) < Work.BoseBox.sideAt μ (BoseGases.a v)
      rw [Work.BoseFixB1.sideAt_eq]
      exact mul_pos (Work.BoseBox.fsXp_pos ht) (Real.rpow_pos_of_pos hμa _)
    have hd : 0 < Work.BoseFixB1B.PBd v μ := by
      show (0:ℝ) < (Work.BoseBox.paramsAt μ (BoseGases.a v)).d
      exact Work.BoseBox.fsXp_pos ht
    have hM3 : 3 ≤ Work.BoseFixB1B.PBM v μ := by
      rw [show Work.BoseFixB1B.PBM v μ = 48 from rfl]; norm_num
    have hM1 : 1 ≤ Work.BoseFixB1B.PBM v μ := le_trans (by norm_num : (1:ℕ) ≤ 3) hM3
    have hAcsub : Work.BoseFixB1B.PBB v μ u ⊆
        Submission.BoseGases.acube (Work.BoseFixB1B.PBℓ v μ) :=
      fun x hx => Work.SmallBoxSliding.dlBox_subset_acube (Work.BoseFixB1B.PBℓ v μ)
        (Work.BoseFixB1B.PBd v μ) u hx
    have hχA : ∀ z : E3, z ∉ Work.BoseFixB1B.PBB v μ u → Submission.BoseGases.chiSmallB
        (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u z = 0 := by
      intro z hz
      by_contra hc
      exact hz (Work.SlotWord.chiSmallB_support_mem_dlBox hM1 hEll hd hc)
    exact integrable_sectorPiece hEll (Work.BoseFixB1.chiSmallB_contDiff_two hM3 u)
      (Submission.BoseGases.chiSmallB_hasCompactSupport hM1 hEll u)
      (Work.SmallBoxSliding.measurableSet_dlBox (Work.BoseFixB1B.PBℓ v μ)
        (Work.BoseFixB1B.PBd v μ) u) hAcsub hχA
      (Work.SmallBoxTBWord.isCompact_dlBox hEll hd u) Φ.contDiff k i
  · -- degenerate case: the box side vanishes
    have ht0 : μ * (BoseGases.a v) ^ 3 ≤ 0 := not_lt.mp ht
    have hμa : μ * BoseGases.a v ≤ 0 := by
      rcases eq_or_ne (BoseGases.a v) 0 with ha | ha
      · rw [ha, mul_zero]
      · have hsq : (BoseGases.a v) ^ 2 * (μ * BoseGases.a v) ≤ 0 := by
          rw [mul_comm, show (μ * BoseGases.a v) * (BoseGases.a v) ^ 2
            = μ * (BoseGases.a v) ^ 3 from by ring]
          exact ht0
        exact nonpos_of_mul_nonpos_right hsq (sq_pos_of_ne_zero ha)
    have hEll : Work.BoseFixB1B.PBℓ v μ = 0 := by
      show Work.BoseBox.sideAt μ (BoseGases.a v) = 0
      rw [Work.BoseFixB1.sideAt_eq]
      have h0 : (μ * BoseGases.a v) ^ (-(1 / 2 : ℝ)) = 0 := by
        rcases lt_or_eq_of_le hμa with hlt | heq
        · rw [Real.rpow_def_of_neg hlt,
            show (-(1 / 2 : ℝ)) * Real.pi = -(Real.pi / 2) by ring, Real.cos_neg,
            Real.cos_pi_div_two, mul_zero]
        · rw [heq, Real.zero_rpow (by norm_num : (-(1 / 2 : ℝ)) ≠ 0)]
      rw [h0, mul_zero]
    have hAnull : (volume : Measure E3) (Work.BoseFixB1B.PBB v μ u) = 0 := by
      refine measure_mono_null ?_ (MeasureTheory.measure_singleton (0 : E3))
      intro y hy
      rw [Set.mem_singleton_iff]
      have h2 : ∀ m : Fin 3, y m ∈ Set.Icc (-(0:ℝ) / 2) (0 / 2) := by
        have h3 := Work.SmallBoxSliding.dlBox_subset_acube (Work.BoseFixB1B.PBℓ v μ)
          (Work.BoseFixB1B.PBd v μ) u hy
        rw [hEll] at h3
        simpa [Submission.BoseGases.acube] using h3
      ext m
      exact le_antisymm (by simpa using (h2 m).2) (by simpa using (h2 m).1)
    exact integrable_of_null_box i hAnull

end Work.BoseFixB1.SectorAux
