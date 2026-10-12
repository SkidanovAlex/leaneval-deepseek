import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.Work.BoseFixR.ChiR0Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.LatticeW1sqParsevalRe`

The `L¹`-weighted lattice Parseval bound for the *real part* of a finite sum of box-lattice
characters, with the kinetic weight `‖k‖²`:

`∫_{boxL ℓ} ‖∇(Re Σ_k c_k e^{i⟪kmom_lab k, ·⟫})‖² ≤ ℓ³ Σ_k ‖kmom_lab k‖² ‖c_k‖²`.

Route (all in this file):

* `latChar ℓ N k : x ↦ e^{i⟪kmomLab ℓ N k, x⟫}` — the characters of the box lattice;
* `isCompact_boxL`, `integrableOn_boxL_of_continuous` — compactness/finite measure of the box;
* `setIntegral_latChar_mul_star` — the Gram matrix `∫_{boxL} char k · conj(char k') = ℓ³ δ_{k,k'}`
  (the product is the character of the difference momentum, and `box_exp_orthogonal` computes it);
* `setIntegral_normSq_sum_latChar` — complex Parseval on the box:
  `∫_{boxL} ‖Σ_k A k · char k‖² = ℓ³ Σ_k ‖A k‖²` (expand the squared modulus, integrate the
  double sum term by term, collapse with the Gram identity);
* `hasFDerivAt_sum_latChar` — the Fréchet derivative of a finite sum of characters;
* `norm_gradient_sq_eq_sum_fderiv` — `‖∇f x‖² = Σ_i ((fderiv ℝ f x) (single i 1))²`;
* `lattice_re_aux` — the assembly: `∇(Re u)` is bounded pointwise by the complex partial
  derivatives of `u` (via `(Re z)² ≤ ‖z‖²`), whose `L²` norms are computed by Parseval;
* `LatticeW1sqParsevalRe` — the target, the case `K = (univ).erase 0`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseFixR

set_option maxHeartbeats 1600000

/-! ## 1. The lattice characters -/

/-- The box-lattice character `x ↦ e^{i⟪k,x⟫}` at the momentum label `k` of the periodic cube
`Lab N`. -/
def latChar (ℓ : ℝ) (N : ℕ) (k : Work.BoseBoxFock.Lab N) :
    EuclideanSpace ℝ (Fin 3) → ℂ :=
  fun x => Complex.exp (Complex.I * ((inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k) x : ℝ) : ℂ))

lemma latChar_apply (ℓ : ℝ) (N : ℕ) (k : Work.BoseBoxFock.Lab N)
    (x : EuclideanSpace ℝ (Fin 3)) :
    latChar ℓ N k x
      = Complex.exp (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k) x : ℂ)) := rfl

lemma norm_latChar (ℓ : ℝ) (N : ℕ) (k : Work.BoseBoxFock.Lab N)
    (x : EuclideanSpace ℝ (Fin 3)) : ‖latChar ℓ N k x‖ = 1 := by
  rw [latChar_apply, Complex.norm_exp_I_mul_ofReal]

lemma continuous_latChar (ℓ : ℝ) (N : ℕ) (k : Work.BoseBoxFock.Lab N) :
    Continuous (latChar ℓ N k) := by
  refine Complex.continuous_exp.comp (continuous_const.mul ?_)
  exact Complex.ofRealCLM.continuous.comp (innerSL ℝ (Work.BoseBoxFock.kmomLab ℓ N k)).continuous

/-! ## 2. The box is compact and of finite measure -/

lemma isCompact_boxL (ℓ : ℝ) : IsCompact (boxL ℓ) := by
  have h : boxL ℓ = (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)) ⁻¹'
      (Set.Icc (fun _ : Fin 3 => -(ℓ / 2)) (fun _ => ℓ / 2)) := by
    ext y
    simp only [boxL, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Icc, Pi.le_def, abs_le]
    exact ⟨fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩,
      fun h i => ⟨h.1 i, h.2 i⟩⟩
  rw [h]
  exact (Homeomorph.isCompact_preimage _).mpr isCompact_Icc

lemma integrableOn_boxL_of_continuous {F : Type*} [NormedAddCommGroup F] {ℓ : ℝ}
    {g : EuclideanSpace ℝ (Fin 3) → F} (hg : Continuous g) : IntegrableOn g (boxL ℓ) :=
  ContinuousOn.integrableOn_compact (isCompact_boxL ℓ) hg.continuousOn

/-! ## 3. The Gram matrix of the lattice characters -/

lemma setIntegral_latChar_mul_star {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ)
    (k k' : Work.BoseBoxFock.Lab N) :
    ∫ x in boxL ℓ, latChar ℓ N k x * star (latChar ℓ N k' x)
      = if k = k' then ((ℓ : ℂ) ^ 3) else 0 := by
  have hpt : ∀ x : EuclideanSpace ℝ (Fin 3),
      latChar ℓ N k x * star (latChar ℓ N k' x)
        = Complex.exp (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k
            - Work.BoseBoxFock.kmomLab ℓ N k') x : ℂ)) := by
    intro x
    rw [latChar_apply, latChar_apply, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    rw [inner_sub_left]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_sub]
    ring
  rw [setIntegral_congr_fun (measurableSet_boxL ℓ) (fun x _ => hpt x)]
  rw [show boxL ℓ = {y : EuclideanSpace ℝ (Fin 3) | ∀ i, |y i| ≤ ℓ / 2} from rfl]
  rw [Work.BoseFixR.kmomLab_sub ℓ N k k']
  rw [Work.BoseFixR.box_exp_orthogonal hℓ
    (Work.BoseBoxFock.labVec N k - Work.BoseBoxFock.labVec N k')]
  by_cases hkk : k = k'
  · subst hkk; simp
  · rw [if_neg hkk,
      if_neg fun hm => hkk (Work.BoseFixR.labVec_injective N (sub_eq_zero.mp hm))]

/-! ## 4. Complex Parseval for a finite sum of characters -/

lemma norm_sq_eq_re_mul_star (z : ℂ) : ‖z‖ ^ 2 = (z * star z).re := by
  rw [← Complex.normSq_eq_norm_sq, ← starRingEnd_apply, Complex.mul_conj, Complex.ofReal_re]

theorem setIntegral_normSq_sum_latChar {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ)
    (K : Finset (Work.BoseBoxFock.Lab N)) (A : Work.BoseBoxFock.Lab N → ℂ) :
    ∫ x in boxL ℓ, ‖∑ k ∈ K, A k * latChar ℓ N k x‖ ^ 2 = ℓ ^ 3 * ∑ k ∈ K, ‖A k‖ ^ 2 := by
  classical
  set W : EuclideanSpace ℝ (Fin 3) → ℂ := fun x => ∑ k ∈ K, A k * latChar ℓ N k x with hW
  change ∫ x in boxL ℓ, ‖W x‖ ^ 2 = ℓ ^ 3 * ∑ k ∈ K, ‖A k‖ ^ 2
  have hWcont : Continuous W := by
    rw [hW]
    exact continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_latChar ℓ N k)
  have h1 : ∫ x in boxL ℓ, ‖W x‖ ^ 2 = (∫ x in boxL ℓ, W x * star (W x)).re := by
    have hint : Integrable (fun x => W x * star (W x)) (volume.restrict (boxL ℓ)) :=
      integrableOn_boxL_of_continuous (hWcont.mul hWcont.star)
    rw [show (∫ x in boxL ℓ, ‖W x‖ ^ 2)
        = ∫ x in boxL ℓ, (W x * star (W x)).re from
      setIntegral_congr_fun (measurableSet_boxL ℓ) (fun x _ => norm_sq_eq_re_mul_star (W x))]
    simpa using (Complex.reCLM.integral_comp_comm hint)
  have hexpand : ∀ x : EuclideanSpace ℝ (Fin 3), W x * star (W x)
      = ∑ k ∈ K, ∑ k' ∈ K,
          (A k * star (A k')) * (latChar ℓ N k x * star (latChar ℓ N k' x)) := by
    intro x
    rw [hW, Finset.sum_mul, star_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [star_mul]
    ring
  have h2 : ∫ x in boxL ℓ, W x * star (W x)
      = ∑ k ∈ K, ∑ k' ∈ K, (A k * star (A k'))
          * ∫ x in boxL ℓ, latChar ℓ N k x * star (latChar ℓ N k' x) := by
    rw [show (∫ x in boxL ℓ, W x * star (W x))
        = ∫ x in boxL ℓ, ∑ k ∈ K, ∑ k' ∈ K, (A k * star (A k'))
            * (latChar ℓ N k x * star (latChar ℓ N k' x)) from
      setIntegral_congr_fun (measurableSet_boxL ℓ) (fun x _ => hexpand x)]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_finsetSum]
      · refine Finset.sum_congr rfl fun k' _ => ?_
        rw [integral_const_mul]
      · intro k' _
        exact integrableOn_boxL_of_continuous (Continuous.mul continuous_const
          (Continuous.mul (continuous_latChar ℓ N k) (continuous_latChar ℓ N k').star))
    · intro k _
      exact integrableOn_boxL_of_continuous (continuous_finsetSum _ fun k' _ =>
        Continuous.mul continuous_const
          (Continuous.mul (continuous_latChar ℓ N k) (continuous_latChar ℓ N k').star))
  have h3 : ∑ k ∈ K, ∑ k' ∈ K, (A k * star (A k'))
        * ∫ x in boxL ℓ, latChar ℓ N k x * star (latChar ℓ N k' x)
      = ∑ k ∈ K, (A k * star (A k)) * ((ℓ : ℂ) ^ 3) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.sum_eq_single k]
    · rw [setIntegral_latChar_mul_star hℓ N k k, if_pos rfl]
    · intro k' _ hk'
      rw [setIntegral_latChar_mul_star hℓ N k k', if_neg (Ne.symm hk')]
      ring
    · intro hk'; exact absurd hk hk'
  have h4 : (∑ k ∈ K, (A k * star (A k)) * ((ℓ : ℂ) ^ 3)).re
      = ℓ ^ 3 * ∑ k ∈ K, ‖A k‖ ^ 2 := by
    have hpow : ((ℓ : ℂ) ^ 3) = ((ℓ ^ 3 : ℝ) : ℂ) := (Complex.ofReal_pow ℓ 3).symm
    have hterm : ∀ k, (A k * star (A k)) * ((ℓ : ℂ) ^ 3) = ((‖A k‖ ^ 2 * ℓ ^ 3 : ℝ) : ℂ) := by
      intro k
      rw [hpow, ← starRingEnd_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq,
        ← Complex.ofReal_mul]
    rw [Finset.sum_congr rfl fun k _ => hterm k, ← Complex.ofReal_sum, Complex.ofReal_re]
    rw [← Finset.sum_mul]
    ring
  calc ∫ x in boxL ℓ, ‖W x‖ ^ 2
      = (∫ x in boxL ℓ, W x * star (W x)).re := h1
    _ = (∑ k ∈ K, ∑ k' ∈ K, (A k * star (A k'))
          * ∫ x in boxL ℓ, latChar ℓ N k x * star (latChar ℓ N k' x)).re := by rw [h2]
    _ = (∑ k ∈ K, (A k * star (A k)) * ((ℓ : ℂ) ^ 3)).re := by rw [h3]
    _ = ℓ ^ 3 * ∑ k ∈ K, ‖A k‖ ^ 2 := h4

/-! ## 5. The derivative of a finite sum of characters -/

theorem hasFDerivAt_sum_latChar {ℓ : ℝ} (N : ℕ) (K : Finset (Work.BoseBoxFock.Lab N))
    (d : Work.BoseBoxFock.Lab N → ℂ) (x : EuclideanSpace ℝ (Fin 3)) :
    HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 3) => ∑ k ∈ K, d k * latChar ℓ N k z)
      (∑ k ∈ K, (d k * latChar ℓ N k x * Complex.I) •
        (Complex.ofRealCLM.comp (innerSL ℝ (Work.BoseBoxFock.kmomLab ℓ N k)))) x := by
  have hterm : ∀ k ∈ K, HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 3) => d k * latChar ℓ N k z)
      ((d k * latChar ℓ N k x * Complex.I) •
        (Complex.ofRealCLM.comp (innerSL ℝ (Work.BoseBoxFock.kmomLab ℓ N k)))) x := by
    intro k _
    have h1 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 3) =>
        inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k) z)
        (innerSL ℝ (Work.BoseBoxFock.kmomLab ℓ N k)) x :=
      (innerSL ℝ (Work.BoseBoxFock.kmomLab ℓ N k)).hasFDerivAt
    have h2 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 3) =>
        ((inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k) z : ℝ) : ℂ))
        (Complex.ofRealCLM.comp (innerSL ℝ (Work.BoseBoxFock.kmomLab ℓ N k))) x :=
      Complex.ofRealCLM.hasFDerivAt.comp x h1
    have h3 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 3) =>
        Complex.I * ((inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k) z : ℝ) : ℂ))
        (Complex.I • (Complex.ofRealCLM.comp (innerSL ℝ (Work.BoseBoxFock.kmomLab ℓ N k)))) x :=
      h2.const_mul Complex.I
    have h4 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 3) => latChar ℓ N k z)
        (latChar ℓ N k x •
          (Complex.I • (Complex.ofRealCLM.comp (innerSL ℝ (Work.BoseBoxFock.kmomLab ℓ N k))))) x := by
      simpa only [latChar_apply] using h3.cexp
    have h5 := h4.const_mul (d k)
    have hCLM : (d k • (latChar ℓ N k x •
          (Complex.I • (Complex.ofRealCLM.comp (innerSL ℝ (Work.BoseBoxFock.kmomLab ℓ N k))))))
        = (d k * latChar ℓ N k x * Complex.I) •
          (Complex.ofRealCLM.comp (innerSL ℝ (Work.BoseBoxFock.kmomLab ℓ N k))) := by
      rw [smul_smul, smul_smul]
    rw [← hCLM]
    exact h5
  have hsum := HasFDerivAt.sum hterm
  rw [show (∑ k ∈ K, fun z : EuclideanSpace ℝ (Fin 3) => d k * latChar ℓ N k z)
      = (fun z => ∑ k ∈ K, d k * latChar ℓ N k z) from by
    ext z
    simp [Finset.sum_apply]] at hsum
  exact hsum

/-! ## 6. The gradient in coordinates -/

theorem norm_gradient_sq_eq_sum_fderiv {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (x : EuclideanSpace ℝ (Fin 3)) :
    ‖gradient f x‖ ^ 2
      = ∑ i : Fin 3, ((fderiv ℝ f x) (EuclideanSpace.single i 1)) ^ 2 := by
  rw [Submission.BoseGases.shell_sq_norm3]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [← inner_gradient_left]
  rw [EuclideanSpace.inner_single_right]
  simp

/-! ## 7. A scalar computation -/

lemma norm_sq_mul_I (c : ℂ) (r : ℝ) : ‖c * (Complex.I * ((r : ℝ) : ℂ))‖ ^ 2 = ‖c‖ ^ 2 * r ^ 2 := by
  have hr : ‖((r : ℝ) : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    ring
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, mul_pow, hr]

/-! ## 8. The assembly -/

theorem lattice_re_aux {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ)
    (K : Finset (Work.BoseBoxFock.Lab N)) (c : Work.BoseBoxFock.Lab N → ℂ) :
    ∫ x in boxL ℓ, ‖gradient (fun y => (∑ k ∈ K, c k * latChar ℓ N k y).re) x‖ ^ 2
      ≤ ℓ ^ 3 * ∑ k ∈ K, ‖Work.BoseBoxFock.kmomLab ℓ N k‖ ^ 2 * ‖c k‖ ^ 2 := by
  classical
  set u : EuclideanSpace ℝ (Fin 3) → ℂ := fun y => ∑ k ∈ K, c k * latChar ℓ N k y with hu
  set f : EuclideanSpace ℝ (Fin 3) → ℝ := fun y => (u y).re with hf
  -- derivative of the complex sum
  have hB : ∀ x, HasFDerivAt u
      (∑ k ∈ K, (c k * latChar ℓ N k x * Complex.I) •
        (Complex.ofRealCLM.comp (innerSL ℝ (Work.BoseBoxFock.kmomLab ℓ N k)))) x := by
    intro x
    rw [hu]
    exact hasFDerivAt_sum_latChar N K c x
  -- derivative of the real part
  have hfd : ∀ x, fderiv ℝ f x = Complex.reCLM.comp (fderiv ℝ u x) := by
    intro x
    have h1 : HasFDerivAt (fun z : ℂ => z.re) Complex.reCLM (u x) := Complex.reCLM.hasFDerivAt
    have h2 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 3) => (u z).re)
        (Complex.reCLM.comp (∑ k ∈ K, (c k * latChar ℓ N k x * Complex.I) •
          (Complex.ofRealCLM.comp (innerSL ℝ (Work.BoseBoxFock.kmomLab ℓ N k))))) x :=
      h1.comp x (hB x)
    rw [hf, h2.fderiv, (hB x).fderiv]
  -- the coefficients of the partial derivatives
  set AA : Fin 3 → Work.BoseBoxFock.Lab N → ℂ :=
    fun i k => c k * (Complex.I * ((Work.BoseBoxFock.kmomLab ℓ N k i : ℝ) : ℂ)) with hAA
  set w : Fin 3 → EuclideanSpace ℝ (Fin 3) → ℂ :=
    fun i x => ∑ k ∈ K, AA i k * latChar ℓ N k x with hw
  have hcoord : ∀ (x : EuclideanSpace ℝ (Fin 3)) (i : Fin 3),
      (fderiv ℝ f x) (EuclideanSpace.single i 1) = (w i x).re := by
    intro x i
    rw [hfd x]
    rw [show (Complex.reCLM.comp (fderiv ℝ u x)) (EuclideanSpace.single i 1)
        = ((fderiv ℝ u x) (EuclideanSpace.single i 1)).re from rfl]
    rw [(hB x).fderiv]
    have hsum : ((∑ k ∈ K, (c k * latChar ℓ N k x * Complex.I) •
          (Complex.ofRealCLM.comp (innerSL ℝ (Work.BoseBoxFock.kmomLab ℓ N k))))
          (EuclideanSpace.single i 1))
        = ∑ k ∈ K, AA i k * latChar ℓ N k x := by
      simp only [sum_apply, smul_apply,
        ContinuousLinearMap.comp_apply, innerSL_apply_apply, Complex.ofRealCLM_apply,
        smul_eq_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hAA]
      rw [EuclideanSpace.inner_single_right]
      simp
      ring
    have hwx : w i x = ∑ k ∈ K, AA i k * latChar ℓ N k x := by simp only [hw]
    rw [hsum, hwx]
  have hwcont : ∀ i : Fin 3, Continuous (w i) := by
    intro i
    rw [hw]
    exact continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_latChar ℓ N k)
  have hint2 : Integrable (fun x => ∑ i : Fin 3, ‖w i x‖ ^ 2) (volume.restrict (boxL ℓ)) :=
    integrableOn_boxL_of_continuous
      (continuous_finsetSum _ fun i _ => (hwcont i).norm.pow 2)
  have hstep1 : ∫ x in boxL ℓ, ‖gradient f x‖ ^ 2
      = ∫ x in boxL ℓ, ∑ i : Fin 3, ((fderiv ℝ f x) (EuclideanSpace.single i 1)) ^ 2 :=
    setIntegral_congr_fun (measurableSet_boxL ℓ) fun x _ => norm_gradient_sq_eq_sum_fderiv x
  have hstep2 : ∫ x in boxL ℓ, ∑ i : Fin 3, ((fderiv ℝ f x) (EuclideanSpace.single i 1)) ^ 2
      ≤ ∫ x in boxL ℓ, ∑ i : Fin 3, ‖w i x‖ ^ 2 := by
    apply integral_mono_of_nonneg
    · filter_upwards with x
      exact Finset.sum_nonneg fun i _ => sq_nonneg _
    · exact hint2
    · filter_upwards with x
      refine Finset.sum_le_sum fun i _ => ?_
      rw [hcoord x i]
      exact re_sq_le_normSq _
  have hstep3 : ∫ x in boxL ℓ, ∑ i : Fin 3, ‖w i x‖ ^ 2
      = ∑ i : Fin 3, ∫ x in boxL ℓ, ‖w i x‖ ^ 2 := by
    rw [integral_finsetSum]
    intro i _
    exact integrableOn_boxL_of_continuous ((hwcont i).norm.pow 2)
  have hstep4 : ∀ i : Fin 3, ∫ x in boxL ℓ, ‖w i x‖ ^ 2 = ℓ ^ 3 * ∑ k ∈ K, ‖AA i k‖ ^ 2 := by
    intro i
    simpa only [hw] using setIntegral_normSq_sum_latChar hℓ N K (AA i)
  have hfinal : ∑ i : Fin 3, ℓ ^ 3 * ∑ k ∈ K, ‖AA i k‖ ^ 2
      = ℓ ^ 3 * ∑ k ∈ K, ‖Work.BoseBoxFock.kmomLab ℓ N k‖ ^ 2 * ‖c k‖ ^ 2 := by
    have h1 : ∑ i : Fin 3, ℓ ^ 3 * ∑ k ∈ K, ‖AA i k‖ ^ 2
        = ℓ ^ 3 * ∑ i : Fin 3, ∑ k ∈ K, ‖AA i k‖ ^ 2 := by
      rw [Finset.mul_sum]
    rw [h1, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    have hterm : ∀ i : Fin 3, ‖AA i k‖ ^ 2
        = ‖c k‖ ^ 2 * ((Work.BoseBoxFock.kmomLab ℓ N k i) ^ 2) := by
      intro i
      rw [hAA]
      exact norm_sq_mul_I (c k) (Work.BoseBoxFock.kmomLab ℓ N k i)
    rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum]
    rw [show (∑ i : Fin 3, (Work.BoseBoxFock.kmomLab ℓ N k i) ^ 2)
        = ‖Work.BoseBoxFock.kmomLab ℓ N k‖ ^ 2
        from (Submission.BoseGases.shell_sq_norm3 _).symm]
    ring
  calc ∫ x in boxL ℓ, ‖gradient f x‖ ^ 2
      = ∫ x in boxL ℓ, ∑ i : Fin 3, ((fderiv ℝ f x) (EuclideanSpace.single i 1)) ^ 2 := hstep1
    _ ≤ ∫ x in boxL ℓ, ∑ i : Fin 3, ‖w i x‖ ^ 2 := hstep2
    _ = ∑ i : Fin 3, ∫ x in boxL ℓ, ‖w i x‖ ^ 2 := hstep3
    _ = ∑ i : Fin 3, ℓ ^ 3 * ∑ k ∈ K, ‖AA i k‖ ^ 2 :=
        Finset.sum_congr rfl fun i _ => hstep4 i
    _ = ℓ ^ 3 * ∑ k ∈ K, ‖Work.BoseBoxFock.kmomLab ℓ N k‖ ^ 2 * ‖c k‖ ^ 2 := hfinal

theorem LatticeW1sqParsevalRe {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ)
    (c : Work.BoseBoxFock.Lab N → ℂ) :
    ∫ x in boxL ℓ,
        ‖gradient (fun y => (∑ k ∈ (Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0,
            c k * Complex.exp
              (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k) y : ℂ))).re) x‖ ^ 2
      ≤ ℓ ^ 3 * ∑ k ∈ (Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0,
          ‖Work.BoseBoxFock.kmomLab ℓ N k‖ ^ 2 * ‖c k‖ ^ 2 := by
  have h := lattice_re_aux hℓ N ((Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0) c
  simpa only [latChar_apply] using h

end Work.BoseFixR
