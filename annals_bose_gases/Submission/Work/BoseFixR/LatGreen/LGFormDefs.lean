import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.Defs
import Submission.Work.BoseFixR.LatGreen.PeriodIntegrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.LatGreen.LGFormDefs` — the vocabulary of the lattice-Green form
`latticeSum_eq_latGreen_form`

The target identity

`Σ_{k≠0} ĉ(V,q_k)²/(2‖q_k‖²) = (1/2) ∫_u (∫_x V x V(x+u)) · latGreen u`

is the *torus-Parseval / theta* step of the far-lattice-row programme
(`Submission/Work/BoseFixR/NOTE_lattice_W1sq_Green.md`, §2 step 3).  This module fixes the
vocabulary shared by the proof and its delegated pieces:

* `autoCorr V u = ∫ x, V x * V (x + u)` — the autocorrelation of the charge `V`;
* `q_k = Work.BoseB4.vec k = 2π k` — the dual-lattice momentum of the unit cube, and
  `λ_k = ‖q_k‖² = 4π²‖latVec k‖²`, so that the `latGreen` Fourier series
  `Σ_{k≠0} cos(2π k·u)/(4π²‖k‖²)` is `Σ_{k≠0} cos⟪q_k,u⟫/λ_k`;
* `chat V p = ∫ x, V x cos⟪p,x⟫` (the real `p`-convention Fourier transform of a real `V`);
* the elementary geometry of `vec`/`latVec` and the Gaussian summability over `ℤ³` that
  the Tonelli steps need.
-/

set_option maxHeartbeats 1000000

noncomputable section

open scoped Real BigOperators
open MeasureTheory

namespace Work.BoseFixR.LatGreen

/-! ### 1. The autocorrelation -/

/-- The autocorrelation of a charge `V`: `u ↦ ∫ x, V x * V (x + u)` (also `= (V ⋆ V̌)(u)`).
This is the charge whose Fourier coefficients are the squares `ĉ(V,·)²`. -/
noncomputable def autoCorr (V : ℝ³ → ℝ) (u : ℝ³) : ℝ :=
  ∫ x : ℝ³, V x * V (x + u)

theorem autoCorr_apply (V : ℝ³ → ℝ) (u : ℝ³) :
    autoCorr V u = ∫ x : ℝ³, V x * V (x + u) := rfl

/-! ### 2. `chat` is the cosine transform -/

/-- The corpus's Fourier transform `chat` of a real function in the `p`-convention
`∫ e^{-i⟪p,x⟫} V x dx` has real part the cosine transform `∫ x, V x * cos⟪p,x⟫`. -/
theorem chat_eq_integral_cos {V : ℝ³ → ℝ} (hV : MeasureTheory.Integrable V) (p : ℝ³) :
    Work.BoseFixR.chat V p = ∫ x : ℝ³, V x * Real.cos (inner ℝ p x) := by
  have hg : MeasureTheory.Integrable (fun y : ℝ³ => ((V y : ℝ) : ℂ)) :=
    Complex.ofRealCLM.integrable_comp hV
  have hf : MeasureTheory.Integrable
      (fun y : ℝ³ => Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * ((V y : ℝ) : ℂ)) := by
    refine hg.bdd_mul (c := 1) (by fun_prop : AEStronglyMeasurable
      (fun y : ℝ³ => Complex.exp (-(Complex.I * (inner ℝ p y : ℂ)))) volume) ?_
    filter_upwards with y
    rw [Complex.norm_exp]
    have hre : (-(Complex.I * (inner ℝ p y : ℂ))).re = 0 := by simp [Complex.mul_re]
    rw [hre, Real.exp_zero]
  have h1 : Work.BoseFixR.chat V p
      = (∫ y : ℝ³, Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * ((V y : ℝ) : ℂ)).re := by
    rw [Work.BoseFixR.chat]
    rfl
  rw [h1]
  calc (∫ y : ℝ³, Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * ((V y : ℝ) : ℂ)).re
      = ∫ y : ℝ³,
          (Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * ((V y : ℝ) : ℂ)).re :=
        (integral_re hf).symm
    _ = ∫ y : ℝ³, V y * Real.cos (inner ℝ p y) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        change (Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * ((V y : ℝ) : ℂ)).re
          = V y * Real.cos (inner ℝ p y)
        have hre : (-(Complex.I * (inner ℝ p y : ℂ))).re = 0 := by simp [Complex.mul_re]
        have him : (-(Complex.I * (inner ℝ p y : ℂ))).im = -(inner ℝ p y) := by
          simp [Complex.mul_im]
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
          Complex.exp_re, hre, him, Real.exp_zero, one_mul, Real.cos_neg]
        ring

/-! ### 3. Geometry of the dual-lattice momentum `vec k = 2π k` -/

theorem vec_apply (k : Fin 3 → ℤ) (i : Fin 3) :
    Work.BoseB4.vec k i = 2 * Real.pi * (k i : ℝ) := rfl

theorem latVec_apply' (k : Fin 3 → ℤ) (i : Fin 3) : latVec k i = (k i : ℝ) := rfl

/-- `‖latVec k‖²` in coordinates. -/
theorem norm_sq_latVec (k : Fin 3 → ℤ) : ‖latVec k‖ ^ 2 = ∑ i : Fin 3, (k i : ℝ) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [latVec_apply']

/-- The momenta `q_k = 2π k` have squared norm `4π²‖k‖²`. -/
theorem norm_sq_vec (k : Fin 3 → ℤ) :
    ‖Work.BoseB4.vec k‖ ^ 2 = 4 * Real.pi ^ 2 * ‖latVec k‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, norm_sq_latVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [vec_apply]
  ring

/-- The inner product with a dual-lattice momentum. -/
theorem inner_vec_eq (k : Fin 3 → ℤ) (u : ℝ³) :
    inner ℝ (Work.BoseB4.vec k) u = 2 * Real.pi * ∑ i : Fin 3, (k i : ℝ) * u i := by
  rw [Work.BoseB4.vec, PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- `latVec` is injective. -/
theorem latVec_injective : Function.Injective latVec := by
  intro k l h
  have h' : (fun i : Fin 3 => (k i : ℝ)) = (fun i : Fin 3 => (l i : ℝ)) := by
    have := congrArg WithLp.ofLp h
    simpa [latVec] using this
  funext i
  have h2 := congrFun h' i
  exact_mod_cast h2

/-- `vec` is injective. -/
theorem vec_injective : Function.Injective (Work.BoseB4.vec) := by
  intro k l h
  have h' : (fun i : Fin 3 => 2 * Real.pi * (k i : ℝ)) =
      (fun i : Fin 3 => 2 * Real.pi * (l i : ℝ)) := by
    have := congrArg WithLp.ofLp h
    simpa [Work.BoseB4.vec] using this
  funext i
  have h2 := congrFun h' i
  have h3 : (k i : ℝ) = (l i : ℝ) :=
    mul_left_cancel₀ (show (2 * Real.pi : ℝ) ≠ 0 by positivity) h2
  exact_mod_cast h3

theorem latVec_eq_zero_iff (k : Fin 3 → ℤ) : latVec k = 0 ↔ k = 0 := by
  constructor
  · intro h
    have h' : (fun i : Fin 3 => (k i : ℝ)) = 0 := by
      have := congrArg WithLp.ofLp h
      simpa [latVec] using this
    funext i
    have h2 := congrFun h' i
    simp only [Pi.zero_apply] at h2
    exact_mod_cast h2
  · rintro rfl
    ext i
    simp [latVec]

theorem vec_eq_zero_iff (k : Fin 3 → ℤ) : Work.BoseB4.vec k = 0 ↔ k = 0 := by
  constructor
  · intro h
    have h' : (fun i : Fin 3 => 2 * Real.pi * (k i : ℝ)) = 0 := by
      have := congrArg WithLp.ofLp h
      simpa [Work.BoseB4.vec] using this
    funext i
    have h2 := congrFun h' i
    simp only [Pi.zero_apply] at h2
    have h3 : (k i : ℝ) = 0 := by
      have hπ : (2 * Real.pi : ℝ) ≠ 0 := by positivity
      exact (mul_eq_zero.mp h2).resolve_left hπ
    exact_mod_cast h3
  · rintro rfl
    ext i
    simp [Work.BoseB4.vec]

theorem norm_latVec_pos {k : Fin 3 → ℤ} (hk : k ≠ 0) : 0 < ‖latVec k‖ := by
  rw [norm_pos_iff]
  intro h
  exact hk ((latVec_eq_zero_iff k).mp h)

theorem norm_vec_pos {k : Fin 3 → ℤ} (hk : k ≠ 0) : 0 < ‖Work.BoseB4.vec k‖ := by
  rw [norm_pos_iff]
  intro h
  exact hk ((vec_eq_zero_iff k).mp h)

/-- The Gaussian sum over the dual lattice `2πℤ³`, in the `latVec` normalisation. -/
theorem summable_exp_neg_norm_latVec_sq {c : ℝ} (hc : 0 < c) :
    Summable (fun k : Fin 3 → ℤ => Real.exp (-c * ‖latVec k‖ ^ 2)) := by
  have h1 : ∀ i : Fin 3, Summable fun m : ℤ => Real.exp (-c * (m : ℝ) ^ 2) :=
    fun i => Commons.Analysis.Fourier.summable_exp_neg_mul_sq_int hc
  have hprod : Summable fun n : Fin 3 → ℤ => ∏ i : Fin 3, Real.exp (-c * (n i : ℝ) ^ 2) :=
    SummablePiFin3Prod (F := fun (i : Fin 3) (m : ℤ) => Real.exp (-c * (m : ℝ) ^ 2))
      (fun i m => Real.exp_nonneg _) h1
  refine hprod.congr (fun k => ?_)
  rw [norm_sq_latVec, Finset.mul_sum, Real.exp_sum]

/-- The Gaussian sum over the momenta `q_k = 2πk`: `Σ_k exp(-t ‖q_k‖²) < ∞` for `t > 0`. -/
theorem summable_exp_neg_norm_vec_sq {t : ℝ} (ht : 0 < t) :
    Summable (fun k : Fin 3 → ℤ => Real.exp (-t * ‖Work.BoseB4.vec k‖ ^ 2)) := by
  have hc : 0 < 4 * Real.pi ^ 2 * t := by positivity
  refine (summable_exp_neg_norm_latVec_sq (c := 4 * Real.pi ^ 2 * t) hc).congr (fun k => ?_)
  rw [norm_sq_vec]
  congr 1
  ring

end Work.BoseFixR.LatGreen
