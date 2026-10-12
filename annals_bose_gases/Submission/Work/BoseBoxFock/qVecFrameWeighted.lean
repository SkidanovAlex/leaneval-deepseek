import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.boxSampling_pair
import Submission.Work.BoseBoxFock.frame_sampling_L2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.qVecFrameWeighted` — the weighted frame identity of the localised `qVec` modes

**The key simplification of the `Q₂` route.**  The localised modes `qVec_k` are the `Q`-projection
of the windowed plane waves `modeVec_k = e^{i⟪k,·⟫}χ_Λ` off the condensate direction `θ_Λ`:

    `qVec ℓ k = modeVec ℓ k − χ̂(ℓk)·θ_Λ`      (`Work.BoseB4.BoxData.qVec`),

i.e. `qVec_k = Q modeVec_k` for the rank-one projection `Q = 1 − ℓ⁻³|θ⟩⟨θ|` onto the mean-free
part of `L²(Λ)`.  Because `Q` is self-adjoint and `qVec_k = Q modeVec_k`, every pairing of a
`qVec` is a pairing of a `modeVec` with the *projected* test function:

    `⟪qVec ℓ k, u⟫ = ⟪modeVec ℓ k, Q u⟫`,     `(Q u)(x) = u(x) − ℓ⁻³(∫_Λ u)·1_Λ(x)`.

Consequently **no separate `θ`-correction lattice sums are needed** — the `θ`-layer is carried
exactly by `Q`.  The weighted frame sum of the `qVec` family is the weighted frame sum of the
`modeVec` family at the projected arguments, and that is the already-proved
`Work.BoseBoxFock.frame_sampling_L2`

    `(ℓ³)⁻¹Σ'_n Ŵ(k_n)⟨modeVec k_n,u⟩conj⟨modeVec k_n,v⟩ = ∬ χu(y)·χv(z)·Σ_m W(z−y+ℓm)`.

This file proves

* `chiLam_exp_integral` — the elementary complex Fourier sample `∫ e^{−i⟪k,x⟫}χ_Λ = ℓ³χ̂(ℓk)`
  (the imaginary part vanishes by evenness);
* `qVec_overlap_eq_modeVec` — the projection identity `⟪qVec ℓ k, u⟫ = ⟪modeVec ℓ k, Q u⟫`;
* **`qVecFrame_weighted`** — the weighted frame identity
  `Σ'_n Ŵ(k_n)⟪qVec k_n,u⟫conj⟪qVec k_n,v⟫ = ℓ³∬ χQu(y)·χQv(z)·Σ_m W(z−y+ℓm)`

for `W` smooth compactly supported and `u, v` integrable real functions.  The remaining error of
the `Q₂` rows is therefore *only* the `m ≠ 0` (periodisation/image) terms
(`Work.BoseBoxFock.chiScale_image_le`) and the `Nmin`-lattice truncation
(`Work.OneBodyKin.kinFT_decay_le`).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The windowed plane wave -/

theorem continuous_modeVec (ℓ : ℝ) (k : E3) :
    Continuous (fun x : E3 => Work.BoseK15.corpusBox.modeVec ℓ k x) := by
  rw [show (fun x : E3 => Work.BoseK15.corpusBox.modeVec ℓ k x)
      = fun x => Complex.exp (Complex.I * (inner ℝ k x : ℂ))
          * ((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ) from by
    funext x; rw [Work.BoseB4.BoxData.modeVec_apply]; rfl]
  refine Continuous.mul (Complex.continuous_exp.comp ?_)
    (Complex.continuous_ofReal.comp (Submission.BoseGases.chiScale_continuous ℓ))
  exact continuous_const.mul (Complex.continuous_ofReal.comp
    (continuous_const.inner continuous_id))

theorem norm_modeVec_le (ℓ : ℝ) (k : E3) (x : E3) :
    ‖Work.BoseK15.corpusBox.modeVec ℓ k x‖ ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ := by
  rw [Work.BoseB4.BoxData.modeVec_apply, norm_mul, Complex.norm_exp]
  have hzero : (Complex.I * (inner ℝ k x : ℂ)).re = 0 := by
    rw [Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.ofReal_re]
    ring
  rw [hzero, Real.exp_zero, one_mul]
  have hnorm : ‖(((Work.BoseK15.corpusBox.chiLam ℓ x : ℝ)) : ℂ)‖
      = |Work.BoseK15.corpusBox.chiLam ℓ x| := by simp
  rw [hnorm]
  exact Submission.BoseGases.abs_chiScale_le ℓ x

/-- `conj (modeVec ℓ k x) = exp(−i⟪k,x⟫)·χ_Λ(x)`. -/
theorem star_modeVec_eq (ℓ : ℝ) (k x : E3) :
    (starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k x)
      = Complex.exp (-(Complex.I * (inner ℝ k x : ℂ)))
        * ((Work.BoseK15.corpusBox.chiLam ℓ x : ℝ) : ℂ) := by
  have h2 : (starRingEnd ℂ) (Complex.I * (inner ℝ k x : ℂ))
      = -(Complex.I * (inner ℝ k x : ℂ)) := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [Work.BoseB4.BoxData.modeVec_apply, map_mul, ← Complex.exp_conj, Complex.conj_ofReal, h2]

/-- **The complex `χ`-sample**: `∫ e^{−i⟪k,x⟫}·χ_Λ(x) dx = ℓ³χ̂(ℓk)` (real by evenness). -/
theorem chiLam_exp_integral {ℓ : ℝ} (hℓ : 0 < ℓ) (k : E3) :
    (∫ x : E3, Complex.exp (-(Complex.I * (inner ℝ k x : ℂ)))
        * ((Work.BoseK15.corpusBox.chiLam ℓ x : ℝ) : ℂ))
      = ((ℓ ^ 3 * Work.BoseK15.corpusBox.hatChi (ℓ • k) : ℝ) : ℂ) := by
  have hcs : HasCompactSupport (Work.BoseK15.corpusBox.chiLam ℓ) :=
    HasCompactSupport.of_support_subset_isCompact (Work.BoseK15.corpusBox.boxL_compact ℓ)
      (Work.BoseK15.corpusBox.chiLam_supp hℓ)
  rw [Work.BoseRowQ2.integral_exp_inner_of_even (F := Work.BoseK15.corpusBox.chiLam ℓ)
    (Work.BoseK15.corpusBox.chiLam_cont ℓ) hcs
    (fun x => Work.BoseK15.corpusBox.chiLam_even ℓ x) k]
  rw [Work.BoseB4.BoxData.integral_chiLam_mul_cos Work.BoseK15.corpusBox hℓ k]

/-- **The `qVec`/`modeVec` dictionary**: `∫ conj (modeVec ℓ k) = ℓ³χ̂(ℓk)`. -/
theorem integral_star_modeVec {ℓ : ℝ} (hℓ : 0 < ℓ) (k : E3) :
    (∫ x : E3, (starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k x))
      = ((ℓ ^ 3 * Work.BoseK15.corpusBox.hatChi (ℓ • k) : ℝ) : ℂ) :=
  calc (∫ x : E3, (starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k x))
      = ∫ x : E3, Complex.exp (-(Complex.I * (inner ℝ k x : ℂ)))
          * ((Work.BoseK15.corpusBox.chiLam ℓ x : ℝ) : ℂ) :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => star_modeVec_eq ℓ k x)
    _ = _ := chiLam_exp_integral hℓ k

theorem star_thetaFun (ℓ : ℝ) (x : E3) :
    (starRingEnd ℂ) (Work.BoseK15.corpusBox.thetaFun ℓ x)
      = Work.BoseK15.corpusBox.thetaFun ℓ x := by
  rw [Work.BoseB4.BoxData.thetaFun_apply]
  by_cases hx : x ∈ Work.BoseK15.corpusBox.boxL ℓ <;> simp [hx]

theorem norm_thetaFun_le (ℓ : ℝ) (x : E3) :
    ‖Work.BoseK15.corpusBox.thetaFun ℓ x‖ ≤ 1 := by
  rw [Work.BoseB4.BoxData.thetaFun_apply]
  by_cases hx : x ∈ Work.BoseK15.corpusBox.boxL ℓ <;> simp [hx]

theorem measurable_thetaFun (ℓ : ℝ) :
    Measurable (fun x : E3 => Work.BoseK15.corpusBox.thetaFun ℓ x) := by
  rw [show (fun x : E3 => Work.BoseK15.corpusBox.thetaFun ℓ x)
      = Set.indicator (Work.BoseK15.corpusBox.boxL ℓ) (fun _ => (1 : ℂ)) from by
    funext x; rw [Work.BoseB4.BoxData.thetaFun_apply]
    by_cases hx : x ∈ Work.BoseK15.corpusBox.boxL ℓ <;> simp [hx]]
  exact measurable_const.indicator (Work.BoseK15.corpusBox.boxL_measurableSet ℓ)

/-- The window vanishes off the box. -/
theorem chiScale_eq_zero_of_notMem {ℓ : ℝ} (hℓ : 0 < ℓ) {x : E3}
    (hx : x ∉ Work.BoseK15.corpusBox.boxL ℓ) : Submission.BoseGases.chiScale ℓ x = 0 :=
  Function.notMem_support.mp (fun h => hx (Work.BoseK15.corpusBox.chiLam_supp hℓ h))

/-- The corpus `BoxData.chiLam` and the corpus `chiScale` are the same function. -/
theorem chiLam_eq_chiScale (ℓ : ℝ) (x : E3) :
    Work.BoseK15.corpusBox.chiLam ℓ x = Submission.BoseGases.chiScale ℓ x := rfl

/-- The real and complex `1`-indicators of the box agree after coercion. -/
theorem ofReal_indicator_boxL (ℓ : ℝ) (x : E3) :
    (((Set.indicator (Work.BoseK15.corpusBox.boxL ℓ) (fun _ : E3 => (1 : ℝ))) x : ℝ) : ℂ)
      = Set.indicator (Work.BoseK15.corpusBox.boxL ℓ) (fun _ : E3 => (1 : ℂ)) x := by
  classical
  by_cases hx : x ∈ Work.BoseK15.corpusBox.boxL ℓ <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]

/-- `latVec` is the concrete lattice vector (definitional unfolding). -/
theorem latVec_eq (m : Fin 3 → ℤ) :
    latVec m = WithLp.toLp 2 (fun i : Fin 3 => ((m i : ℤ) : ℝ)) := rfl

/-! ## 2. The `Q`-projection off the box (real form) -/

/-- `Q u = u − ℓ⁻³(∫_Λ u)·1_Λ`. -/
noncomputable def boxQr (ℓ : ℝ) (u : E3 → ℝ) : E3 → ℝ :=
  fun x => u x - (ℓ ^ 3)⁻¹ * (∫ y in Work.BoseK15.corpusBox.boxL ℓ, u y)
    * Set.indicator (Work.BoseK15.corpusBox.boxL ℓ) (fun _ : E3 => (1 : ℝ)) x

/-- The windowed projection `χ_Λ·(Q u)`. -/
noncomputable def boxQchi (ℓ : ℝ) (u : E3 → ℝ) : E3 → ℝ :=
  fun x => Submission.BoseGases.chiScale ℓ x
    * (u x - (ℓ ^ 3)⁻¹ * (∫ y in Work.BoseK15.corpusBox.boxL ℓ, u y))

/-- `boxQchi ℓ u = χ_Λ · boxQr ℓ u`: the indicator is redundant against the window. -/
theorem boxQchi_eq_mul {ℓ : ℝ} (hℓ : 0 < ℓ) (u : E3 → ℝ) (x : E3) :
    boxQchi ℓ u x = Submission.BoseGases.chiScale ℓ x * boxQr ℓ u x := by
  classical
  rw [boxQchi, boxQr]
  by_cases hx : x ∈ Work.BoseK15.corpusBox.boxL ℓ
  · rw [Set.indicator_of_mem hx, mul_one]
  · rw [chiScale_eq_zero_of_notMem hℓ hx, Set.indicator_of_notMem hx]
    ring

/-! ## 3. Integrability of the projected functions -/

theorem volume_boxL_lt_top (ℓ : ℝ) (hℓ : 0 < ℓ) :
    volume (Work.BoseK15.corpusBox.boxL ℓ) < ⊤ := by
  rw [Work.BoseB4.BoxData.volume_boxL Work.BoseK15.corpusBox hℓ]
  exact ENNReal.ofReal_lt_top

theorem integrable_boxQr {ℓ : ℝ} (hℓ : 0 < ℓ) {u : E3 → ℝ} (hu : Integrable u) :
    Integrable (boxQr ℓ u) := by
  have hind : Integrable (Set.indicator (Work.BoseK15.corpusBox.boxL ℓ)
      (fun _ : E3 => (1 : ℝ))) :=
    (integrable_indicator_iff (Work.BoseK15.corpusBox.boxL_measurableSet ℓ)).mpr
      (MeasureTheory.integrableOn_const (C := (1 : ℝ)) (volume_boxL_lt_top ℓ hℓ).ne (by simp))
  have hconst : Integrable (fun x : E3 =>
      (ℓ ^ 3)⁻¹ * (∫ y in Work.BoseK15.corpusBox.boxL ℓ, u y)
        * Set.indicator (Work.BoseK15.corpusBox.boxL ℓ) (fun _ : E3 => (1 : ℝ)) x) := by
    refine (hind.const_mul ((ℓ ^ 3)⁻¹ * (∫ y in Work.BoseK15.corpusBox.boxL ℓ, u y))).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply]
  exact (hu.sub hconst).congr (Filter.Eventually.of_forall fun x => by simp [boxQr, Pi.sub_apply])

theorem integrable_boxQchi {ℓ : ℝ} (hℓ : 0 < ℓ) {u : E3 → ℝ} (hu : Integrable u) :
    Integrable (boxQchi ℓ u) := by
  refine (Integrable.bdd_mul (integrable_boxQr hℓ hu)
    (Submission.BoseGases.chiScale_continuous ℓ).aestronglyMeasurable
    (Filter.Eventually.of_forall (Submission.BoseGases.abs_chiScale_le ℓ))).congr
    (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.mul_apply, boxQchi_eq_mul hℓ u x]

/-! ## 4. The `θ`-pairing and the `modeVec`-`kinFT` bridge -/

/-- `∫ conj θ_Λ · ↑u = ↑(∫_Λ u)` for integrable real `u`. -/
theorem integral_star_thetaFun_mul {ℓ : ℝ} {u : E3 → ℝ} (hu : Integrable u) :
    (∫ x : E3, (starRingEnd ℂ) (Work.BoseK15.corpusBox.thetaFun ℓ x) * ((u x : ℝ) : ℂ))
      = ((∫ y in Work.BoseK15.corpusBox.boxL ℓ, u y : ℝ) : ℂ) := by
  classical
  have hpt : ∀ x : E3, (starRingEnd ℂ) (Work.BoseK15.corpusBox.thetaFun ℓ x) * ((u x : ℝ) : ℂ)
      = ((Set.indicator (Work.BoseK15.corpusBox.boxL ℓ) u x : ℝ) : ℂ) := by
    intro x
    rw [star_thetaFun, Work.BoseB4.BoxData.thetaFun_apply]
    by_cases hx : x ∈ Work.BoseK15.corpusBox.boxL ℓ
    · rw [if_pos hx, Set.indicator_of_mem hx]; simp
    · rw [if_neg hx, Set.indicator_of_notMem hx]; simp
  rw [show (∫ x : E3, (starRingEnd ℂ) (Work.BoseK15.corpusBox.thetaFun ℓ x) * ((u x : ℝ) : ℂ))
      = ∫ x : E3, ((Set.indicator (Work.BoseK15.corpusBox.boxL ℓ) u x : ℝ) : ℂ) from
    integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [← MeasureTheory.integral_indicator (Work.BoseK15.corpusBox.boxL_measurableSet ℓ) (f := u)]
  exact integral_ofReal

/-- `conj (modeVec ℓ k x) · 1_Λ(x) = conj (modeVec ℓ k x)` (the window is supported in the box). -/
theorem star_modeVec_mul_ind {ℓ : ℝ} (hℓ : 0 < ℓ) (k x : E3) :
    (starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k x)
        * Set.indicator (Work.BoseK15.corpusBox.boxL ℓ) (fun _ : E3 => (1 : ℂ)) x
      = (starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k x) := by
  classical
  by_cases hx : x ∈ Work.BoseK15.corpusBox.boxL ℓ
  · rw [Set.indicator_of_mem hx, mul_one]
  · rw [Set.indicator_of_notMem hx, mul_zero, star_modeVec_eq, chiLam_eq_chiScale,
      chiScale_eq_zero_of_notMem hℓ hx, Complex.ofReal_zero, mul_zero]

/-- `∫ conj (modeVec ℓ k) · 1_Λ = ℓ³χ̂(ℓk)`. -/
theorem integral_star_modeVec_mul_ind {ℓ : ℝ} (hℓ : 0 < ℓ) (k : E3) :
    (∫ x : E3, (starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k x)
        * Set.indicator (Work.BoseK15.corpusBox.boxL ℓ) (fun _ : E3 => (1 : ℂ)) x)
      = ((ℓ ^ 3 * Work.BoseK15.corpusBox.hatChi (ℓ • k) : ℝ) : ℂ) := by
  rw [show (∫ x : E3, (starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k x)
        * Set.indicator (Work.BoseK15.corpusBox.boxL ℓ) (fun _ : E3 => (1 : ℂ)) x)
      = ∫ x : E3, (starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k x) from
    integral_congr_ae (Filter.Eventually.of_forall fun x => star_modeVec_mul_ind hℓ k x)]
  exact integral_star_modeVec hℓ k

/-- The pairing of a windowed plane wave with a real function is its windowed Fourier sample. -/
theorem modeVec_overlap_eq_kinFT (ℓ : ℝ) (k : E3) (w : E3 → ℝ) :
    (∫ x : E3, (starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k x) * ((w x : ℝ) : ℂ))
      = Submission.BoseGases.kinFT
          (fun z => ((Submission.BoseGases.chiScale ℓ z * w z : ℝ) : ℂ)) k := by
  rw [Submission.BoseGases.kinFT]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  beta_reduce
  rw [star_modeVec_eq, chiLam_eq_chiScale]
  push_cast
  ring

/-! ## 5. The projection identity -/

/-- **The `Q`-projection identity**: `⟪qVec ℓ k, u⟫ = ⟪modeVec ℓ k, Q u⟫`. -/
theorem qVec_overlap_eq_modeVec {ℓ : ℝ} (hℓ : 0 < ℓ) (k : E3) {u : E3 → ℝ}
    (hu : Integrable u) :
    (∫ x : E3, (starRingEnd ℂ) (Work.BoseK15.corpusBox.qVec ℓ k x) * ((u x : ℝ) : ℂ))
      = ∫ x : E3, (starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k x)
          * ((boxQr ℓ u x : ℝ) : ℂ) := by
  classical
  have hIu : Integrable (fun x : E3 => ((u x : ℝ) : ℂ)) := hu.ofReal
  have hI1 : Integrable (fun x : E3 =>
      (starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k x) * ((u x : ℝ) : ℂ)) :=
    Integrable.bdd_mul hIu
      ((Complex.continuous_conj.comp (continuous_modeVec ℓ k)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by
        rw [starRingEnd_apply, norm_star]; exact norm_modeVec_le ℓ k x)
  have hboundθ : ∀ x : E3,
      ‖(starRingEnd ℂ) (Work.BoseK15.corpusBox.thetaFun ℓ x)‖ ≤ 1 := by
    intro x; rw [starRingEnd_apply, norm_star]; exact norm_thetaFun_le ℓ x
  have hI2 : Integrable (fun x : E3 =>
      (starRingEnd ℂ) (Work.BoseK15.corpusBox.thetaFun ℓ x) * ((u x : ℝ) : ℂ)) :=
    Integrable.bdd_mul hIu
      ((Complex.continuous_conj.measurable.comp (measurable_thetaFun ℓ)).aestronglyMeasurable)
      (Filter.Eventually.of_forall hboundθ)
  have hI0 : Integrable (fun x : E3 => (starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k x)) := by
    refine integrable_of_bounded_support (volume_boxL_lt_top ℓ hℓ)
      ((Complex.continuous_conj.comp (continuous_modeVec ℓ k)).measurable)
      ⟨(Real.sqrt Submission.BoseGases.chiNormSq)⁻¹, fun x => ?_⟩ ?_
    · rw [starRingEnd_apply, norm_star]; exact norm_modeVec_le ℓ k x
    · intro x hx
      rw [Function.mem_support] at hx
      by_contra hcon
      refine hx ?_
      rw [star_modeVec_eq, chiLam_eq_chiScale, chiScale_eq_zero_of_notMem hℓ hcon,
        Complex.ofReal_zero, mul_zero]
  have hI3 : Integrable (fun x : E3 =>
      (starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k x)
        * Set.indicator (Work.BoseK15.corpusBox.boxL ℓ) (fun _ : E3 => (1 : ℂ)) x) :=
    hI0.congr (Filter.Eventually.of_forall fun x => (star_modeVec_mul_ind hℓ k x).symm)
  have hA : (∫ x : E3, (starRingEnd ℂ) (Work.BoseK15.corpusBox.qVec ℓ k x) * ((u x : ℝ) : ℂ))
      = (∫ x : E3, (starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k x) * ((u x : ℝ) : ℂ))
        - ((Work.BoseK15.corpusBox.hatChi (ℓ • k) : ℝ) : ℂ)
          * ((∫ y in Work.BoseK15.corpusBox.boxL ℓ, u y : ℝ) : ℂ) := by
    rw [show (∫ x : E3, (starRingEnd ℂ) (Work.BoseK15.corpusBox.qVec ℓ k x) * ((u x : ℝ) : ℂ))
        = ∫ x : E3, ((starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k x) * ((u x : ℝ) : ℂ)
            - ((Work.BoseK15.corpusBox.hatChi (ℓ • k) : ℝ) : ℂ)
              * ((starRingEnd ℂ) (Work.BoseK15.corpusBox.thetaFun ℓ x) * ((u x : ℝ) : ℂ))) from
      integral_congr_ae (Filter.Eventually.of_forall fun x => by
        beta_reduce
        rw [Work.BoseB4.BoxData.qVec_apply, map_sub, map_mul, Complex.conj_ofReal]; ring)]
    rw [integral_sub hI1 (hI2.const_mul _), integral_const_mul,
      integral_star_thetaFun_mul hu]
  have hB : (∫ x : E3, (starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k x)
        * ((boxQr ℓ u x : ℝ) : ℂ))
      = (∫ x : E3, (starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k x) * ((u x : ℝ) : ℂ))
        - ((((ℓ ^ 3)⁻¹ * (∫ y in Work.BoseK15.corpusBox.boxL ℓ, u y) : ℝ)) : ℂ)
          * ((ℓ ^ 3 * Work.BoseK15.corpusBox.hatChi (ℓ • k) : ℝ) : ℂ) := by
    rw [show (∫ x : E3, (starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k x)
          * ((boxQr ℓ u x : ℝ) : ℂ))
        = ∫ x : E3, ((starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k x) * ((u x : ℝ) : ℂ)
            - ((((ℓ ^ 3)⁻¹ * (∫ y in Work.BoseK15.corpusBox.boxL ℓ, u y) : ℝ)) : ℂ)
              * ((starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k x)
                  * Set.indicator (Work.BoseK15.corpusBox.boxL ℓ) (fun _ : E3 => (1 : ℂ)) x)) from
      integral_congr_ae (Filter.Eventually.of_forall fun x => by
        beta_reduce
        rw [boxQr]
        push_cast
        rw [ofReal_indicator_boxL]
        ring)]
    rw [integral_sub hI1 (hI3.const_mul _), integral_const_mul,
      integral_star_modeVec_mul_ind hℓ k]
  have hℓ0 : ((ℓ : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hℓ)
  rw [hA, hB]
  push_cast
  field_simp

/-! ## 6. The weighted frame identity -/

/-- **The weighted frame identity of the localised `qVec` modes.**  For `W` smooth with compact
support and integrable real `u, v`,

    `Σ'_n Ŵ(k_n)⟪qVec k_n,u⟫conj⟪qVec k_n,v⟫ = ℓ³∬ χQu(y)·χQv(z)·Σ_m W(z−y+ℓm)`,

where `Q u = u − ℓ⁻³(∫_Λ u)1_Λ` (`Work.BoseBoxFock.boxQr`) and `χQu = boxQchi ℓ u`.

This *is* the "standard calculation" for the `qVec` frame: by the projection identity the two
sides are the `modeVec` frame pairing at `Qu, Qv`, which is `frame_sampling_L2`. -/
theorem qVecFrame_weighted {ℓ : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ}
    (hW : ContDiff ℝ (⊤ : ℕ∞) W) (hWs : HasCompactSupport W)
    {u v : E3 → ℝ} (hu : Integrable u) (hv : Integrable v) :
    (∑' n : Fin 3 → ℤ,
        Submission.BoseGases.kinFT (fun z => (W z : ℂ)) (kmomInt ℓ n)
          * (∫ x : E3, (starRingEnd ℂ) (Work.BoseK15.corpusBox.qVec ℓ (kmomInt ℓ n) x)
              * ((u x : ℝ) : ℂ))
          * (starRingEnd ℂ)
              (∫ x : E3, (starRingEnd ℂ) (Work.BoseK15.corpusBox.qVec ℓ (kmomInt ℓ n) x)
                * ((v x : ℝ) : ℂ)))
      = (((ℓ ^ 3 : ℝ)) : ℂ) * ∫ y : E3, ∫ z : E3,
          ((boxQchi ℓ u y : ℝ) : ℂ) * ((boxQchi ℓ v z : ℝ) : ℂ)
            * (∑' m : Fin 3 → ℤ, (W (z - y + ℓ • latVec m) : ℂ)) := by
  have hu' : Integrable (boxQr ℓ u) := integrable_boxQr hℓ hu
  have hv' : Integrable (boxQr ℓ v) := integrable_boxQr hℓ hv
  rw [tsum_congr (fun n => by
    rw [qVec_overlap_eq_modeVec hℓ _ hu, qVec_overlap_eq_modeVec hℓ _ hv,
      modeVec_overlap_eq_kinFT ℓ _ (boxQr ℓ u), modeVec_overlap_eq_kinFT ℓ _ (boxQr ℓ v)])]
  have hfs := frame_sampling_L2 hℓ hW hWs hu' hv'
  have hS : (∑' n : Fin 3 → ℤ,
        Submission.BoseGases.kinFT (fun z => (W z : ℂ)) (kmomInt ℓ n)
          * Submission.BoseGases.kinFT
              (fun z => ((Submission.BoseGases.chiScale ℓ z * boxQr ℓ u z : ℝ) : ℂ))
              (kmomInt ℓ n)
          * (starRingEnd ℂ) (Submission.BoseGases.kinFT
              (fun z => ((Submission.BoseGases.chiScale ℓ z * boxQr ℓ v z : ℝ) : ℂ))
              (kmomInt ℓ n)))
      = (((ℓ ^ 3 : ℝ)) : ℂ) * ∫ y : E3, ∫ z : E3,
          (((Submission.BoseGases.chiScale ℓ y * boxQr ℓ u y : ℝ)) : ℂ)
            * (((Submission.BoseGases.chiScale ℓ z * boxQr ℓ v z : ℝ)) : ℂ)
            * (∑' m : Fin 3 → ℤ, (W (z - y + ℓ • latVec m) : ℂ)) := by
    simp only [latVec]
    rw [← hfs, ← mul_assoc, ← Complex.ofReal_mul,
      mul_inv_cancel₀ (pow_ne_zero 3 (ne_of_gt hℓ)), Complex.ofReal_one, one_mul]
  have hpt : ∀ y z : E3,
      (((Submission.BoseGases.chiScale ℓ y * boxQr ℓ u y : ℝ)) : ℂ)
        * (((Submission.BoseGases.chiScale ℓ z * boxQr ℓ v z : ℝ)) : ℂ)
        * (∑' m : Fin 3 → ℤ, (W (z - y + ℓ • latVec m) : ℂ))
      = ((boxQchi ℓ u y : ℝ) : ℂ) * ((boxQchi ℓ v z : ℝ) : ℂ)
        * (∑' m : Fin 3 → ℤ, (W (z - y + ℓ • latVec m) : ℂ)) := by
    intro y z
    rw [← boxQchi_eq_mul hℓ u y, ← boxQchi_eq_mul hℓ v z]
  rw [hS]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  exact hpt y z

/-! ## 7. The complex forms of the projection (used by the complex frame identity and by the
lattice-tail bounds: `Q` is not a contraction for the `χ²`-weighted norm, so the projected
function, not `u` itself, is what appears in the Bessel-type estimates). -/

/-- The complex `Q`-projection off the box. -/
noncomputable def cboxQ (ℓ : ℝ) (u : E3 → ℂ) : E3 → ℂ :=
  fun x => u x - ((ℓ : ℂ) ^ 3)⁻¹ * (∫ y in Work.BoseK15.corpusBox.boxL ℓ, u y)
    * Set.indicator (Work.BoseK15.corpusBox.boxL ℓ) (fun _ : E3 => (1 : ℂ)) x

/-- The complex windowed projection `χ_Λ·(Q u)`. -/
noncomputable def cboxQchi (ℓ : ℝ) (u : E3 → ℂ) : E3 → ℂ :=
  fun x => ((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ)
    * (u x - ((ℓ : ℂ) ^ 3)⁻¹ * (∫ y in Work.BoseK15.corpusBox.boxL ℓ, u y))

/-- `cboxQchi ℓ u = χ_Λ · cboxQ ℓ u`. -/
theorem cboxQchi_eq_mul {ℓ : ℝ} (hℓ : 0 < ℓ) (u : E3 → ℂ) (x : E3) :
    cboxQchi ℓ u x = ((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ) * cboxQ ℓ u x := by
  classical
  rw [cboxQchi, cboxQ]
  by_cases hx : x ∈ Work.BoseK15.corpusBox.boxL ℓ
  · rw [Set.indicator_of_mem hx, mul_one]
  · rw [chiScale_eq_zero_of_notMem hℓ hx, Set.indicator_of_notMem hx]
    simp

end Work.BoseBoxFock
