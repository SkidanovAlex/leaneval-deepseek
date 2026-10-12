import Mathlib.Order.CompletePartialOrder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.L1Tails.Defs
import Submission.Work.BoseFixB1S.gradient_plancherel_of_contDiff_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.L1Tails.latticeDirichlet` — lattice Parseval for `∇f` (T2 of the `L¹`-tail design)

Design `sources/boseDCF/bose_L1tails.md`, T2.  For `ℓ > 0` and `f : ℝ³ → ℂ` of class `C¹` with
`tsupport f ⊆ boxL ℓ` (the cube of side `ℓ`),

    Σ_n ‖κ_n‖² ‖f̂(κ_n)‖² = ℓ³ (2π)⁻³ ∫_p ‖p‖² ‖f̂(p)‖² ,    κ_n = (2π/ℓ)·n ,

i.e. the lattice sampling sum of `f̂` weighted by `‖κ_n‖²` and the continuum `Ḣ¹`-mass of `f` agree;
both equal `ℓ³ ∫ ‖∇f‖²` (the `ℓℤ³`-translates of the box meet only in measure-zero faces, so the
sampling sum carries no extra aliasing mass).

## Proof

* the **pointwise derivative identity** `kinFT (∂_{e_i}f) p = i⟪p,e_i⟫·kinFT f p` (integration by
  parts; the corpus's `Work.BoseFixB1S.kinFT_fderiv_apply`, whose hypotheses are exactly what
  compactly supported `C¹` functions supply) turns the weight `‖κ_n‖²` into a finite sum over the
  three directional derivatives of `f`:
  `‖p‖²‖kinFT f p‖² = Σ_i ‖kinFT (∂_{e_i}f) p‖²`;
* the **lattice side** is the `L²` frame (aliasing/Poisson) identity
  `Work.BoseBoxFock.hasSum_kinFT_lattice_L2` applied to each `∂_{e_i}f` (continuous, compactly
  supported, supported in the box) and summed over `i`;
* the **continuum side** is Plancherel in the `kinFT` convention
  (`Work.BoseKinLoc.Momentum.kinFT_l1l2_plancherel`) applied to each `∂_{e_i}f`, summed over `i`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Real

namespace Work.BoseBoxFock.L1Tails

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## 1. The directional derivative, and the derivative identity for `kinFT` -/

/-- The `i`-th directional derivative of a `ℂ`-valued function along `kcStdBasis i`. -/
abbrev kcDirC (f : E3 → ℂ) (i : Fin 3) : E3 → ℂ :=
  fun z => fderiv ℝ f z (Submission.BoseGases.kcStdBasis i)

lemma kcDirC_continuous {f : E3 → ℂ} (hf : ContDiff ℝ 1 f) (i : Fin 3) :
    Continuous (kcDirC f i) :=
  (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const

lemma kcDirC_hasCompactSupport {f : E3 → ℂ} (hcs : HasCompactSupport f) (i : Fin 3) :
    HasCompactSupport (kcDirC f i) :=
  hcs.fderiv_apply ℝ (Submission.BoseGases.kcStdBasis i)

lemma kcDirC_tsupport_subset {f : E3 → ℂ} (i : Fin 3) :
    tsupport (kcDirC f i) ⊆ tsupport f :=
  tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := f) (Submission.BoseGases.kcStdBasis i)

/-- **The `kinFT`-transform of a directional derivative** (integration by parts):
`kinFT (∂_{e_i}f) p = i⟪p,e_i⟫·kinFT f p` for `f` of class `C¹` with compact support. -/
lemma kcDirC_kinFT {f : E3 → ℂ} (hf : ContDiff ℝ 1 f) (hcs : HasCompactSupport f)
    (i : Fin 3) (p : E3) :
    Submission.BoseGases.kinFT (kcDirC f i) p
      = Complex.I * ((inner ℝ p (Submission.BoseGases.kcStdBasis i) : ℝ) : ℂ)
          * Submission.BoseGases.kinFT f p :=
  Work.BoseFixB1S.kinFT_fderiv_apply (hf.continuous.integrable_of_hasCompactSupport hcs)
    (hf.differentiable (by norm_num))
    ((hf.continuous_fderiv (by norm_num)).integrable_of_hasCompactSupport (hcs.fderiv ℝ)) i p

/-- **The pointwise second-moment identity**: `‖p‖²‖kinFT f p‖²` is the sum over the three
coordinate directions of `‖kinFT (∂_{e_i}f) p‖²`. -/
theorem normSq_kinFT_eq_sum_kcDirC {f : E3 → ℂ} (hf : ContDiff ℝ 1 f)
    (hcs : HasCompactSupport f) (p : E3) :
    (∑ i : Fin 3, ‖Submission.BoseGases.kinFT (kcDirC f i) p‖ ^ 2)
      = ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT f p‖ ^ 2 := by
  have hkey : ∀ i : Fin 3, Submission.BoseGases.kinFT (kcDirC f i) p
      = Complex.I * ((inner ℝ p (Submission.BoseGases.kcStdBasis i) : ℝ) : ℂ)
          * Submission.BoseGases.kinFT f p := fun i => kcDirC_kinFT hf hcs i p
  simp_rw [hkey]
  have h1 : ∀ i : Fin 3,
      ‖Complex.I * ((inner ℝ p (Submission.BoseGases.kcStdBasis i) : ℝ) : ℂ)
          * Submission.BoseGases.kinFT f p‖ ^ 2
        = (inner ℝ p (Submission.BoseGases.kcStdBasis i)) ^ 2
            * ‖Submission.BoseGases.kinFT f p‖ ^ 2 := by
    intro i
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_I,
      one_mul, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq]
    ring
  rw [Finset.sum_congr rfl (fun i _ => h1 i), ← Finset.sum_mul,
    Work.SmallBoxBridge.Resolve.sum_inner_kcStdBasis_sq_local p]

/-! ## 2. The lattice Dirichlet identity -/

theorem latticeDirichlet {ℓ : ℝ} (hℓ : 0 < ℓ) {f : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hf : ContDiff ℝ 1 f) (hs : tsupport f ⊆ Work.BoseK15.corpusBox.boxL ℓ) :
    HasSum (fun n : Fin 3 → ℤ =>
        ‖Work.BoseBoxFock.kappaL ℓ n‖ ^ 2 *
          ‖Submission.BoseGases.kinFT f (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2)
      (ℓ ^ 3 * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
        ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT f p‖ ^ 2)) := by
  -- the state is compactly supported, hence integrable and `L²`
  have hfcs : HasCompactSupport f :=
    (Work.BoseK15.corpusBox.boxL_compact ℓ).of_isClosed_subset (isClosed_tsupport f) hs
  have hcont : ∀ i : Fin 3, Continuous (kcDirC f i) := fun i => kcDirC_continuous hf i
  have hcs : ∀ i : Fin 3, HasCompactSupport (kcDirC f i) :=
    fun i => kcDirC_hasCompactSupport hfcs i
  have hmlp : ∀ i : Fin 3, MemLp (kcDirC f i) 2 :=
    fun i => (hcont i).memLp_of_hasCompactSupport (hcs i)
  have hintC : ∀ i : Fin 3, Integrable (kcDirC f i) :=
    fun i => (hcont i).integrable_of_hasCompactSupport (hcs i)
  have hsupp : ∀ i : Fin 3, tsupport (kcDirC f i) ⊆ Work.BoseK15.corpusBox.boxL ℓ :=
    fun i => (kcDirC_tsupport_subset i).trans hs
  -- the lattice frame identity for each directional derivative
  have hframe : ∀ i : Fin 3,
      HasSum (fun n : Fin 3 → ℤ => ‖Submission.BoseGases.kinFT (kcDirC f i)
          (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
        (ℓ ^ 3 * ∫ x : E3, ‖kcDirC f i x‖ ^ 2) :=
    fun i => hasSum_kinFT_lattice_L2 hℓ (hmlp i) (hsupp i)
  have hS : ∀ i : Fin 3, Summable (fun n : Fin 3 → ℤ =>
      ‖Submission.BoseGases.kinFT (kcDirC f i) (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2) :=
    fun i => (hframe i).summable
  -- Plancherel, and the integrability of the transformed derivatives
  have hplanch : ∀ i : Fin 3, (∫ p : E3, ‖Submission.BoseGases.kinFT (kcDirC f i) p‖ ^ 2)
      = (2 * Real.pi) ^ 3 * ∫ x : E3, ‖kcDirC f i x‖ ^ 2 :=
    fun i => Work.BoseKinLoc.Momentum.kinFT_l1l2_plancherel (hintC i) (hmlp i)
  have hint2 : ∀ i : Fin 3,
      Integrable (fun p : E3 => ‖Submission.BoseGases.kinFT (kcDirC f i) p‖ ^ 2) := by
    intro i
    exact (MeasureTheory.memLp_two_iff_integrable_sq_norm
      (Work.BoseKinLoc.Momentum.continuous_kinFT_of_integrable (hintC i)).aestronglyMeasurable).mp
      (Work.BoseKinLoc.Momentum.memLp_kinFT (hintC i) (hmlp i))
  -- the pointwise identity
  have hpt : ∀ p : E3, (∑ i : Fin 3, ‖Submission.BoseGases.kinFT (kcDirC f i) p‖ ^ 2)
      = ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT f p‖ ^ 2 :=
    fun p => normSq_kinFT_eq_sum_kcDirC hf hfcs p
  -- the value identity
  have hne : ((2 * Real.pi) ^ 3 : ℝ) ≠ 0 := by positivity
  have hval : (∑ i : Fin 3, ℓ ^ 3 * ∫ x : E3, ‖kcDirC f i x‖ ^ 2)
      = ℓ ^ 3 * (((2 * Real.pi) ^ 3)⁻¹ *
          ∫ p : E3, ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT f p‖ ^ 2) := by
    rw [← Finset.mul_sum]
    congr 1
    have hstep : ∀ i : Fin 3, (∫ x : E3, ‖kcDirC f i x‖ ^ 2)
        = ((2 * Real.pi) ^ 3)⁻¹ *
            ∫ p : E3, ‖Submission.BoseGases.kinFT (kcDirC f i) p‖ ^ 2 := by
      intro i
      rw [hplanch i, inv_mul_cancel_left₀ hne]
    calc (∑ i : Fin 3, ∫ x : E3, ‖kcDirC f i x‖ ^ 2)
        = ∑ i : Fin 3, ((2 * Real.pi) ^ 3)⁻¹ *
            ∫ p : E3, ‖Submission.BoseGases.kinFT (kcDirC f i) p‖ ^ 2 :=
          Finset.sum_congr rfl (fun i _ => hstep i)
      _ = ((2 * Real.pi) ^ 3)⁻¹ * ∑ i : Fin 3,
            ∫ p : E3, ‖Submission.BoseGases.kinFT (kcDirC f i) p‖ ^ 2 :=
          (Finset.mul_sum (Finset.univ : Finset (Fin 3))
            (fun i => ∫ p : E3, ‖Submission.BoseGases.kinFT (kcDirC f i) p‖ ^ 2)
            (((2 * Real.pi) ^ 3)⁻¹)).symm
      _ = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3,
            ∑ i : Fin 3, ‖Submission.BoseGases.kinFT (kcDirC f i) p‖ ^ 2 := by
          rw [(MeasureTheory.integral_finsetSum (Finset.univ : Finset (Fin 3))
            (f := fun (i : Fin 3) (p : E3) =>
              ‖Submission.BoseGases.kinFT (kcDirC f i) p‖ ^ 2)
            (fun i _ => hint2 i)).symm]
      _ = ((2 * Real.pi) ^ 3)⁻¹ *
            ∫ p : E3, ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT f p‖ ^ 2 := by
          rw [integral_congr_ae (Filter.Eventually.of_forall (fun p => hpt p))]
  -- summability of the aggregated family
  have hsum : Summable (fun n : Fin 3 → ℤ =>
      ∑ i : Fin 3, ‖Submission.BoseGases.kinFT (kcDirC f i)
        (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2) :=
    Summable.congr ((hS 0).add ((hS 1).add (hS 2)))
      (fun n => by rw [Fin.sum_univ_three]; ring)
  have htsum : (∑' n : Fin 3 → ℤ,
        ∑ i : Fin 3, ‖Submission.BoseGases.kinFT (kcDirC f i)
          (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
      = ∑ i : Fin 3, ℓ ^ 3 * ∫ x : E3, ‖kcDirC f i x‖ ^ 2 := by
    rw [Summable.tsum_finsetSum (f := fun (i : Fin 3) (n : Fin 3 → ℤ) =>
        ‖Submission.BoseGases.kinFT (kcDirC f i) (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
      (s := Finset.univ) (fun i _ => hS i)]
    exact Finset.sum_congr rfl (fun i _ => (hframe i).tsum_eq)
  have hmain : HasSum (fun n : Fin 3 → ℤ =>
        ∑ i : Fin 3, ‖Submission.BoseGases.kinFT (kcDirC f i)
          (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
      (∑ i : Fin 3, ℓ ^ 3 * ∫ x : E3, ‖kcDirC f i x‖ ^ 2) := by
    rw [← htsum]
    exact hsum.hasSum
  rw [hval] at hmain
  refine hmain.congr_fun (fun n => ?_)
  exact (normSq_kinFT_eq_sum_kcDirC hf hfcs (Work.BoseBoxFock.kmomInt ℓ n)).symm

end Work.BoseBoxFock.L1Tails
