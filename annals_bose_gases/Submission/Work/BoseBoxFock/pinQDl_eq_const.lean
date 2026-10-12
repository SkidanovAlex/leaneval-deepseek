import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.FRK.kinFT_conv_mul
import Submission.Work.BoseBoxFock.hatChi_lattice_tail_le
import Submission.Work.BoseBoxFock.integral_tsum_phase
import Submission.Work.BoseBoxFock.latSum_integral_swap
import Submission.Work.BoseBoxFock.pinQLimDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pinQDl_eq_const`

The `θθ` row of the FS §8 pair kernel: the lattice sum
`pinQDl ℓ W = Σ'_n Ŵ(k_n)·χ̂(ℓk_n)²` (`k_n = kmomInt ℓ n = (2π/ℓ)n`) is the
`m`-lattice sum of the double convolution of `W` with the box bump `χ_ℓ = chiScale ℓ`:

    pinQDl ℓ W = ℓ⁻³ · Σ'_m ∫_y ∫_x W(y)·χ_ℓ(x−y)·χ_ℓ(ℓ·latVec m − x) .

## Route

Let `K_ℓ = χ_ℓ ⋆ χ_ℓ` be the self-convolution of the bump: `K_ℓ u = ∫_t χ_ℓ t·χ_ℓ(u−t)dt`.
It is `C^∞` with compact support (it is `convolution (chiScale ℓ) (chiScale ℓ)`, so
Mathlib's convolution smoothness and support lemmas apply), and its Fourier transform is
the square of the bump transform (`convWindow_kinFT` with `W := chiScale ℓ` +
`kinFT_chiScale`):

    kinFT K_ℓ(k_n) = ℓ⁶·χ̂(2πn)²   (since ℓ • kmomInt ℓ n = vec n = 2πn).

The proof of the identity is then the Poisson summation `latticePoisson_kernel` applied to
`K_ℓ` (which is smooth even for a merely bounded `W` — this is the point of using `K_ℓ`
rather than `W ⋆ χ_ℓ`), with the two interchanges `Σ_m/∫_y` and `∫_y/Σ_n` established by
`latSum_integral_swap` (finite in `m`) and `integral_tsum_phase` (absolutely convergent in
`n`).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## The self-convolution of the box bump -/

/-- `K_ℓ = χ_ℓ ⋆ χ_ℓ`, the self-convolution of the box bump `chiScale ℓ`. -/
noncomputable def Kconv (ℓ : ℝ) : E3 → ℝ :=
  MeasureTheory.convolution (Submission.BoseGases.chiScale ℓ)
    (Submission.BoseGases.chiScale ℓ) (ContinuousLinearMap.lsmul ℝ ℝ) volume

/-- The defining integral of `K_ℓ`. -/
lemma Kconv_apply (ℓ : ℝ) (s : E3) :
    Kconv ℓ s = ∫ t : E3,
      Submission.BoseGases.chiScale ℓ t * Submission.BoseGases.chiScale ℓ (s - t) := by
  rw [Kconv, MeasureTheory.convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]

/-- `K_ℓ` is smooth. -/
lemma Kconv_contDiff {ℓ : ℝ} (hℓ : 0 < ℓ) : ContDiff ℝ (⊤ : ℕ∞) (Kconv ℓ) := by
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  have hχcd : ContDiff ℝ (⊤ : ℕ∞) (Submission.BoseGases.chiScale ℓ) :=
    Submission.BoseGases.chiScale_contDiff hℓne
  have hχcs : HasCompactSupport (Submission.BoseGases.chiScale ℓ) :=
    Submission.BoseGases.chiScale_hasCompactSupport hℓne
  rw [Kconv]
  exact hχcs.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    hχcd.continuous.locallyIntegrable hχcd

/-- `K_ℓ` has compact support. -/
lemma Kconv_hasCompactSupport {ℓ : ℝ} (hℓ : 0 < ℓ) : HasCompactSupport (Kconv ℓ) := by
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  have hχcs : HasCompactSupport (Submission.BoseGases.chiScale ℓ) :=
    Submission.BoseGases.chiScale_hasCompactSupport hℓne
  rw [Kconv]
  exact hχcs.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hχcs

/-- The continuous version of `K_ℓ`. -/
lemma Kconv_continuous {ℓ : ℝ} (hℓ : 0 < ℓ) : Continuous (Kconv ℓ) :=
  (Kconv_contDiff hℓ).continuous

/-! ## elementary support facts for the bump -/

/-- The bump `χ_ℓ = χ(·/ℓ)` vanishes outside the ball of radius `ℓ/2`. -/
lemma chiScale_eq_zero_of_half_lt {ℓ : ℝ} (hℓ : 0 < ℓ) {x : E3}
    (hx : ℓ / 2 < ‖x‖) : Submission.BoseGases.chiScale ℓ x = 0 := by
  rw [Submission.BoseGases.chiScale]
  refine Submission.BoseGases.chi_eq_zero_of_norm_gt _ ?_
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hℓ.le), inv_mul_eq_div]
  rw [lt_div_iff₀ hℓ]
  linarith

/-- Contrapositive form: `χ_ℓ x ≠ 0` forces `‖x‖ ≤ ℓ/2`. -/
lemma norm_le_half_of_chiScale_ne_zero {ℓ : ℝ} (hℓ : 0 < ℓ) {x : E3}
    (hx : Submission.BoseGases.chiScale ℓ x ≠ 0) : ‖x‖ ≤ ℓ / 2 := by
  by_contra h
  exact hx (chiScale_eq_zero_of_half_lt hℓ (lt_of_not_ge h))

/-- `K_ℓ` vanishes outside the closed ball of radius `ℓ`. -/
lemma Kconv_eq_zero_of_lt_norm {ℓ : ℝ} (hℓ : 0 < ℓ) {s : E3} (hs : ℓ < ‖s‖) :
    Kconv ℓ s = 0 := by
  rw [Kconv_apply]
  have hpt : ∀ t : E3,
      Submission.BoseGases.chiScale ℓ t * Submission.BoseGases.chiScale ℓ (s - t) = 0 := by
    intro t
    by_cases ht : Submission.BoseGases.chiScale ℓ t = 0
    · simp [ht]
    · have ht' : ‖t‖ ≤ ℓ / 2 := norm_le_half_of_chiScale_ne_zero hℓ ht
      have hst : ℓ / 2 < ‖s - t‖ := by
        have h2 : ‖s‖ = ‖(s - t) + t‖ := by rw [sub_add_cancel]
        have h1 : ‖s‖ ≤ ‖s - t‖ + ‖t‖ := by rw [h2]; exact norm_add_le _ _
        linarith
      rw [chiScale_eq_zero_of_half_lt hℓ hst, mul_zero]
  simp only [hpt]
  simp

/-! ## elementary integrability facts -/

/-- A `L²` function vanishing outside a ball is integrable. -/
lemma integrable_of_memLp_of_supp {f : E3 → ℂ} {ρ : ℝ}
    (hf : MemLp f 2 (volume : Measure E3)) (hs : ∀ x, ρ < ‖x‖ → f x = 0) :
    Integrable f (volume : Measure E3) := by
  have hsupp : Function.support f ⊆ Metric.closedBall (0 : E3) ρ := by
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    by_contra hc
    exact hx (hs x (not_le.mp hc))
  haveI : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : E3) ρ)) :=
    isFiniteMeasure_restrict.mpr (measure_closedBall_lt_top (x := (0 : E3)) (r := ρ)).ne
  exact (integrableOn_iff_integrable_of_support_subset hsupp).mp
    ((hf.restrict _).integrable (q := 2) (by norm_num))

/-- A bounded, compactly supported (radially vanishing) strongly measurable function is
integrable. -/
lemma integrable_of_bdd_of_supp {f : E3 → ℂ} {ρ : ℝ}
    (hmeas : AEStronglyMeasurable f (volume : Measure E3))
    (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) (hs : ∀ x, ρ < ‖x‖ → f x = 0) :
    Integrable f (volume : Measure E3) := by
  obtain ⟨C, hC⟩ := hb
  have hsupp : Function.support f ⊆ Metric.closedBall (0 : E3) ρ := by
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    by_contra hc
    exact hx (hs x (not_le.mp hc))
  have hcomp : HasCompactSupport f :=
    IsCompact.of_isClosed_subset (isCompact_closedBall (0 : E3) ρ) (isClosed_tsupport f)
      (closure_minimal hsupp Metric.isClosed_closedBall)
  refine integrable_of_memLp_of_supp (f := f) ?_ hs
  exact hcomp.memLp_of_bound hmeas (max C 0)
    (Filter.Eventually.of_forall (fun x => le_trans (hC x) (le_max_left C 0)))

/-- A compactly supported function vanishes outside some ball. -/
lemma exists_radius_of_hasCompactSupport {W : E3 → ℝ} (h : HasCompactSupport W) :
    ∃ R : ℝ, ∀ x, R < ‖x‖ → W x = 0 := by
  obtain ⟨R, hR⟩ := h.isCompact.isBounded.subset_closedBall (0 : E3)
  exact ⟨R, fun x hx => by
    by_contra hx0
    have hmem : x ∈ tsupport W := subset_tsupport W hx0
    have h2 := hR hmem
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h2
    exact absurd h2 (not_le.mpr hx)⟩

/-- `‖(r : ℂ)‖ = ‖r‖`. -/
lemma pinQ_norm_ofReal_complex (x : ℝ) : ‖((x : ℝ) : ℂ)‖ = ‖x‖ := by
  have h2 : ‖((x : ℝ) : ℂ)‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, Real.norm_eq_abs, sq_abs, sq]
  nlinarith [norm_nonneg ((x : ℝ) : ℂ), norm_nonneg x]

/-- `‖exp(-(I·x))‖ = 1` for real `x`. -/
lemma norm_exp_neg_I_ofReal (x : ℝ) : ‖Complex.exp (-(Complex.I * (x : ℂ)))‖ = 1 := by
  rw [show -(Complex.I * (x : ℂ)) = ((-x : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I (-x)

/-! ## the Fourier transform of `K_ℓ` -/

/-- The Fourier transform of `K_ℓ` is `ℓ⁶ χ̂(ℓ·)²`. -/
lemma kinFT_Kconv {ℓ : ℝ} (hℓ : 0 < ℓ) (p : E3) :
    Submission.BoseGases.kinFT (fun u : E3 => (Kconv ℓ u : ℂ)) p
      = (ℓ : ℂ) ^ 6 * ((Work.BoseK15.corpusBox.hatChi (ℓ • p) : ℝ) : ℂ) ^ 2 := by
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  have hχcd : ContDiff ℝ (⊤ : ℕ∞) (Submission.BoseGases.chiScale ℓ) :=
    Submission.BoseGases.chiScale_contDiff hℓne
  have hχcs : HasCompactSupport (Submission.BoseGases.chiScale ℓ) :=
    Submission.BoseGases.chiScale_hasCompactSupport hℓne
  have h1 := convWindow_kinFT (ℓ := ℓ) hℓ (W := Submission.BoseGases.chiScale ℓ) hχcd hχcs p
  have h2 : Submission.BoseGases.kinFT
      (fun y : E3 => (Submission.BoseGases.chiScale ℓ y : ℂ)) p
      = (ℓ : ℂ) ^ 3 * ((Work.BoseK15.corpusBox.hatChi (ℓ • p) : ℝ) : ℂ) := by
    have h3 := Work.OneBodyKin.kinFT_chiScale hℓ p
    rwa [show Work.OneBodyKin.profHat (ℓ • p)
        = Work.BoseK15.corpusBox.hatChi (ℓ • p) from rfl] at h3
  show Submission.BoseGases.kinFT
      (fun u : E3 => ((MeasureTheory.convolution (Submission.BoseGases.chiScale ℓ)
        (Submission.BoseGases.chiScale ℓ) (ContinuousLinearMap.lsmul ℝ ℝ) volume u : ℝ) : ℂ)) p
      = (ℓ : ℂ) ^ 6 * _
  rw [← h1, h2]
  ring

/-! ## Poisson summation for `K_ℓ` -/

/-- The Poisson identity for `K_ℓ`, in the form used in the assembly. -/
lemma tsum_Kconv_eq {ℓ : ℝ} (hℓ : 0 < ℓ) (y : E3) :
    (∑' m : Fin 3 → ℤ, ((Kconv ℓ (ℓ • latVec m - y) : ℝ) : ℂ))
      = (((ℓ : ℂ) ^ 3)⁻¹) * ∑' n : Fin 3 → ℤ,
          Submission.BoseGases.kinFT (fun u : E3 => (Kconv ℓ u : ℂ)) (kmomInt ℓ n)
            * Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) y : ℂ))) := by
  have h3 : (ℓ : ℂ) ^ 3 ≠ 0 := pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr (ne_of_gt hℓ))
  have hKcdc : ContDiff ℝ (⊤ : ℕ∞) (fun u : E3 => (Kconv ℓ u : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Kconv_contDiff hℓ)
  have hKcsc : HasCompactSupport (fun u : E3 => (Kconv ℓ u : ℂ)) :=
    (Kconv_hasCompactSupport hℓ).comp_left (g := fun r : ℝ => (r : ℂ)) (by norm_num)
  have h := latticePoisson_kernel ℓ hℓ (fun u : E3 => (Kconv ℓ u : ℂ)) hKcdc hKcsc (-y)
  -- reindex the position lattice: `-y + ℓ•latVec m = ℓ•latVec m - y`
  have hab : (∑' m : Fin 3 → ℤ, ((Kconv ℓ (ℓ • latVec m - y) : ℝ) : ℂ))
      = ∑' m : Fin 3 → ℤ, ((Kconv ℓ (-y + ℓ • latVec m) : ℝ) : ℂ) := by
    refine tsum_congr (fun m => ?_)
    rw [show ℓ • latVec m - y = -y + ℓ • latVec m by abel]
  -- the phase: `exp(I⟪k, -y⟫) = exp(-(I⟪k, y⟫))`
  have hexp : ∀ n : Fin 3 → ℤ,
      Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) y : ℂ)))
        = Complex.exp (Complex.I * (inner ℝ (kmomInt ℓ n) (-y) : ℂ)) := by
    intro n
    rw [show -(Complex.I * (inner ℝ (kmomInt ℓ n) y : ℂ))
        = Complex.I * ((-(inner ℝ (kmomInt ℓ n) y) : ℝ) : ℂ) by push_cast; ring,
      inner_neg_right]
  -- invert the Poisson identity
  have hA : (∑' m : Fin 3 → ℤ, ((Kconv ℓ (-y + ℓ • latVec m) : ℝ) : ℂ))
      = ((ℓ : ℂ) ^ 3)⁻¹ * ∑' n : Fin 3 → ℤ,
          Submission.BoseGases.kinFT (fun u : E3 => (Kconv ℓ u : ℂ)) (kmomInt ℓ n)
            * Complex.exp (Complex.I * (inner ℝ (kmomInt ℓ n) (-y) : ℂ)) := by
    rw [h]
    exact (inv_mul_cancel_left₀ h3 _).symm
  rw [hab]
  rw [show (∑' n : Fin 3 → ℤ, Submission.BoseGases.kinFT (fun u : E3 => (Kconv ℓ u : ℂ))
        (kmomInt ℓ n)
          * Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) y : ℂ))))
      = ∑' n : Fin 3 → ℤ, Submission.BoseGases.kinFT (fun u : E3 => (Kconv ℓ u : ℂ))
        (kmomInt ℓ n)
          * Complex.exp (Complex.I * (inner ℝ (kmomInt ℓ n) (-y) : ℂ)) from
    tsum_congr (fun n => by rw [hexp n])]
  exact hA

/-! ## the inner `x`-integral -/

/-- The inner `x`-integral of the target's right-hand side equals `K_ℓ(ℓ·latVec m − y)`. -/
lemma integral_chiScale_pair {ℓ : ℝ} (hℓ : 0 < ℓ) (m : Fin 3 → ℤ) (y : E3) :
    (∫ x : E3, ((Submission.BoseGases.chiScale ℓ (x - y) : ℝ) : ℂ)
        * ((Submission.BoseGases.chiScale ℓ (ℓ • latVec m - x) : ℝ) : ℂ))
      = ((Kconv ℓ (ℓ • latVec m - y) : ℝ) : ℂ) := by
  rw [Kconv_apply]
  have hptc : (fun x : E3 => ((Submission.BoseGases.chiScale ℓ (x - y) : ℝ) : ℂ)
        * ((Submission.BoseGases.chiScale ℓ (ℓ • latVec m - x) : ℝ) : ℂ))
      = fun x : E3 => ((Submission.BoseGases.chiScale ℓ (x - y)
          * Submission.BoseGases.chiScale ℓ (ℓ • latVec m - x) : ℝ) : ℂ) := by
    funext x
    rw [Complex.ofReal_mul]
  rw [hptc]
  trans (((∫ x : E3, Submission.BoseGases.chiScale ℓ (x - y)
      * Submission.BoseGases.chiScale ℓ (ℓ • latVec m - x) : ℝ)) : ℂ)
  · exact integral_ofReal
  · congr 1
    have hfun : (fun x : E3 => Submission.BoseGases.chiScale ℓ (x - y)
          * Submission.BoseGases.chiScale ℓ (ℓ • latVec m - x))
        = fun x : E3 => (fun t : E3 => Submission.BoseGases.chiScale ℓ t
            * Submission.BoseGases.chiScale ℓ (ℓ • latVec m - y - t)) (x - y) := by
      funext x
      show Submission.BoseGases.chiScale ℓ (x - y)
            * Submission.BoseGases.chiScale ℓ (ℓ • latVec m - x)
          = Submission.BoseGases.chiScale ℓ (x - y)
            * Submission.BoseGases.chiScale ℓ (ℓ • latVec m - y - (x - y))
      rw [show ℓ • latVec m - y - (x - y) = ℓ • latVec m - x by abel]
    rw [hfun]
    exact integral_sub_right_eq_self (μ := volume)
      (f := fun t : E3 => Submission.BoseGases.chiScale ℓ t
        * Submission.BoseGases.chiScale ℓ (ℓ • latVec m - y - t)) y

/-! ## the target -/

theorem pinQDl_eq_const {ℓ : ℝ} (hℓ : 0 < ℓ) {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hWm : MeasureTheory.AEStronglyMeasurable W MeasureTheory.volume)
    (hWb : ∃ C : ℝ, ∀ x, ‖W x‖ ≤ C) (hWs : HasCompactSupport W)
    (hWev : ∀ z, W (-z) = W z) :
    Work.BoseBoxFock.pinQDl ℓ W
      = ((ℓ ^ 3)⁻¹ : ℝ) * ∑' m : Fin 3 → ℤ, ∫ y : EuclideanSpace ℝ (Fin 3),
          ∫ x : EuclideanSpace ℝ (Fin 3),
            ((W y : ℝ) : ℂ) * ((Submission.BoseGases.chiScale ℓ (x - y) : ℝ) : ℂ)
              * ((Submission.BoseGases.chiScale ℓ (ℓ • Work.BoseBoxFock.latVec m - x) : ℝ) : ℂ) := by
  classical
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  have h3 : (ℓ : ℂ) ^ 3 ≠ 0 := pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr hℓne)
  obtain ⟨R, hR⟩ := exists_radius_of_hasCompactSupport hWs
  -- integrability of the weight
  have hWint : Integrable (fun y : E3 => (W y : ℂ)) volume := by
    refine integrable_of_bdd_of_supp (ρ := R) (f := fun y : E3 => (W y : ℂ))
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hWm) ?_ ?_
    · obtain ⟨C, hC⟩ := hWb
      exact ⟨C, fun x => by rw [pinQ_norm_ofReal_complex]; exact hC x⟩
    · intro x hx; rw [hR x hx]; rfl
  -- the Fourier coefficients of `K_ℓ` on the lattice
  set c : (Fin 3 → ℤ) → ℂ :=
    fun n => Submission.BoseGases.kinFT (fun u : E3 => (Kconv ℓ u : ℂ)) (kmomInt ℓ n) with hcdef
  have hcSumm : Summable (fun n : Fin 3 → ℤ => ‖c n‖) := by
    have hKcdc : ContDiff ℝ (⊤ : ℕ∞) (fun u : E3 => (Kconv ℓ u : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (Kconv_contDiff hℓ)
    have hKcsc : HasCompactSupport (fun u : E3 => (Kconv ℓ u : ℂ)) :=
      (Kconv_hasCompactSupport hℓ).comp_left (g := fun r : ℝ => (r : ℂ)) (by norm_num)
    have h := summable_kinFT_lattice_phase (ℓ := ℓ) hℓ hKcdc hKcsc (0 : E3)
    have h2 : Summable (fun n : Fin 3 → ℤ =>
        ‖Submission.BoseGases.kinFT (fun u : E3 => (Kconv ℓ u : ℂ)) (kmomInt ℓ n)
          * Complex.exp (Complex.I * (inner ℝ (kmomInt ℓ n) (0 : E3) : ℂ))‖) := h.norm
    refine h2.congr (fun n => ?_)
    have he : Complex.exp (Complex.I * (inner ℝ (kmomInt ℓ n) (0 : E3) : ℂ)) = 1 := by
      rw [show inner ℝ (kmomInt ℓ n) (0 : E3) = 0 from inner_zero_right _]; simp
    rw [he, mul_one]
  -- the final value of the lattice sum
  set Y : ℂ := ∑' n : Fin 3 → ℤ,
      ((Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec n) : ℝ) : ℂ) ^ 2
        * Submission.BoseGases.kinFT (fun y : E3 => (W y : ℂ)) (kmomInt ℓ n) with hYdef
  -- ### step 1: the inner `x`-integral
  have hstep1 : ∀ m : Fin 3 → ℤ,
      (∫ y : E3, ∫ x : E3, (W y : ℂ) * (Submission.BoseGases.chiScale ℓ (x - y) : ℂ)
          * (Submission.BoseGases.chiScale ℓ (ℓ • latVec m - x) : ℂ))
        = ∫ y : E3, (W y : ℂ) * ((Kconv ℓ (ℓ • latVec m - y) : ℝ) : ℂ) := by
    intro m
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    show (∫ x : E3, (W y : ℂ) * (Submission.BoseGases.chiScale ℓ (x - y) : ℂ)
          * (Submission.BoseGases.chiScale ℓ (ℓ • latVec m - x) : ℂ))
        = (W y : ℂ) * ((Kconv ℓ (ℓ • latVec m - y) : ℝ) : ℂ)
    have hconst : (∫ x : E3, (W y : ℂ) * (Submission.BoseGases.chiScale ℓ (x - y) : ℂ)
          * (Submission.BoseGases.chiScale ℓ (ℓ • latVec m - x) : ℂ))
        = (W y : ℂ) * (∫ x : E3, (Submission.BoseGases.chiScale ℓ (x - y) : ℂ)
            * (Submission.BoseGases.chiScale ℓ (ℓ • latVec m - x) : ℂ)) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))
    rw [hconst, integral_chiScale_pair hℓ m y]
  -- ### step 2: the `m`-sum / `y`-integral interchange
  have hstep2 : (∑' m : Fin 3 → ℤ, ∫ y : E3,
        (W y : ℂ) * ((Kconv ℓ (ℓ • latVec m - y) : ℝ) : ℂ))
      = ∫ y : E3, (W y : ℂ) * (∑' m : Fin 3 → ℤ,
          ((Kconv ℓ (ℓ • latVec m - y) : ℝ) : ℂ)) :=
    latSum_integral_swap (ℓ := ℓ) (R := R) (ρ := ℓ)
      (K := fun u : E3 => ((Kconv ℓ u : ℝ) : ℂ)) hℓ hWm hWb hR
      (Complex.continuous_ofReal.comp (Kconv_continuous hℓ))
      (fun x hx => by rw [Kconv_eq_zero_of_lt_norm hℓ hx]; rfl)
  -- ### step 3a: the Poisson identity, pointwise in `y`
  have hstep3a : (∫ y : E3, (W y : ℂ) * (∑' m : Fin 3 → ℤ,
        ((Kconv ℓ (ℓ • latVec m - y) : ℝ) : ℂ)))
      = ∫ y : E3, (W y : ℂ) * (((ℓ : ℂ) ^ 3)⁻¹ * ∑' n : Fin 3 → ℤ,
          c n * Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) y : ℂ)))) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    show (W y : ℂ) * (∑' m : Fin 3 → ℤ, ((Kconv ℓ (ℓ • latVec m - y) : ℝ) : ℂ))
        = (W y : ℂ) * (((ℓ : ℂ) ^ 3)⁻¹ * ∑' n : Fin 3 → ℤ,
            c n * Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) y : ℂ))))
    rw [tsum_Kconv_eq hℓ y]
  -- ### step 3b: pull out the constant `ℓ⁻³`
  have hstep3b : (∫ y : E3, (W y : ℂ) * (((ℓ : ℂ) ^ 3)⁻¹ * ∑' n : Fin 3 → ℤ,
        c n * Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) y : ℂ)))))
      = ((ℓ : ℂ) ^ 3)⁻¹ * ∫ y : E3, (W y : ℂ) * (∑' n : Fin 3 → ℤ,
          c n * Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) y : ℂ)))) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun y => by ring))
  -- ### step 4: the `n`-sum / `y`-integral interchange
  have hstep4 : (∫ y : E3, (W y : ℂ) * (∑' n : Fin 3 → ℤ,
        c n * Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) y : ℂ)))))
      = ∑' n : Fin 3 → ℤ, c n * ∫ y : E3,
          Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) y : ℂ))) * (W y : ℂ) :=
    integral_tsum_phase (W := W) hWint hcSumm (c := c) (k := kmomInt ℓ)
  -- ### step 5: identify the coefficients
  have hstep5 : (∑' n : Fin 3 → ℤ, c n * ∫ y : E3,
        Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) y : ℂ))) * (W y : ℂ))
      = (ℓ : ℂ) ^ 6 * Y := by
    have hterm : ∀ n : Fin 3 → ℤ, c n * ∫ y : E3,
          Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) y : ℂ))) * (W y : ℂ)
        = (ℓ : ℂ) ^ 6 * (((Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec n) : ℝ) : ℂ) ^ 2
            * Submission.BoseGases.kinFT (fun y : E3 => (W y : ℂ)) (kmomInt ℓ n)) := by
      intro n
      have hcn : c n = (ℓ : ℂ) ^ 6
          * ((Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec n) : ℝ) : ℂ) ^ 2 := by
        show Submission.BoseGases.kinFT (fun u : E3 => (Kconv ℓ u : ℂ)) (kmomInt ℓ n) = _
        rw [kinFT_Kconv hℓ (kmomInt ℓ n)]
        rw [show ℓ • kmomInt ℓ n = Work.BoseB4.vec n from by
          rw [kmomInt, smul_smul, mul_inv_cancel₀ hℓne, one_smul]]
      rw [hcn]
      have hint : (∫ y : E3, Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) y : ℂ)))
            * (W y : ℂ))
          = Submission.BoseGases.kinFT (fun y : E3 => (W y : ℂ)) (kmomInt ℓ n) := rfl
      rw [hint]
      ring
    rw [tsum_congr hterm, hYdef, tsum_mul_left]
  -- ### the lattice sum
  have hDsum : (∑' m : Fin 3 → ℤ, ∫ y : E3, ∫ x : E3, (W y : ℂ)
        * (Submission.BoseGases.chiScale ℓ (x - y) : ℂ)
        * (Submission.BoseGases.chiScale ℓ (ℓ • latVec m - x) : ℂ)) = (ℓ : ℂ) ^ 3 * Y := by
    rw [tsum_congr hstep1, hstep2, hstep3a, hstep3b, hstep4, hstep5]
    rw [show (ℓ : ℂ) ^ 6 = (ℓ : ℂ) ^ 3 * (ℓ : ℂ) ^ 3 by ring]
    rw [mul_assoc, ← mul_assoc, inv_mul_cancel₀ h3, one_mul]
  -- ### conclusion
  rw [hDsum]
  have hscale : (((ℓ ^ 3)⁻¹ : ℝ) : ℂ) * ((ℓ : ℂ) ^ 3 * Y) = Y := by
    rw [show (((ℓ ^ 3)⁻¹ : ℝ) : ℂ) = ((ℓ : ℂ) ^ 3)⁻¹ from by
      rw [Complex.ofReal_inv, Complex.ofReal_pow]]
    rw [← mul_assoc, inv_mul_cancel₀ h3, one_mul]
  rw [hscale, hYdef]
  show (∑' n : Fin 3 → ℤ, ((Work.BoseFixR.chat W (kmomInt ℓ n) : ℝ) : ℂ)
      * (((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ)) : ℂ) ^ 2)
    = ∑' n : Fin 3 → ℤ, ((Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec n) : ℝ) : ℂ) ^ 2
        * Submission.BoseGases.kinFT (fun y : E3 => (W y : ℂ)) (kmomInt ℓ n)
  refine tsum_congr (fun n => ?_)
  rw [show ℓ • kmomInt ℓ n = Work.BoseB4.vec n from by
    rw [kmomInt, smul_smul, mul_inv_cancel₀ hℓne, one_smul]]
  rw [chat_eq_kinFT_of_even hWev (kmomInt ℓ n)]
  ring

end Work.BoseBoxFock
