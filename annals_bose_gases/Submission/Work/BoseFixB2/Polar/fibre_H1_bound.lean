import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Polar.fibre_H1_bound` — uniform `H¹` bounds for slot fibres

The one-body localised word `fsT ℓ d s εT b` (FS `eq:DefT`) is `H¹`-bounded on smooth compactly
supported states (`Work.BoseKinLoc.Kinetic.fsT_H1_bound_all`):

`|fsT ℓ d s εT b u ψ| ≤ C·(∫ψ² + Σ_k ∫(∂_kψ)²)`.

For the continuity of the box word along an affine path `t ↦ t·F + G`
(`Polar.boxFormB_continuous_smul`) this estimate has to be applied to the *slot fibres*
`z ↦ (t·F + G)(x with xᵢ = z)`, uniformly in `t`, in the slot `i` and in the configuration
point `x` of the box.  This module provides exactly that uniformity:

* `fibre_H1_bound_of_bounds` — the generic estimate: if a smooth state `Ξ` vanishes beyond the
  ball `B(0,R)`, is bounded by `Mv` there and has differential bounded by `Md` there, then for
  every `x` with `‖x‖ ≤ R` the fibre `z ↦ Ξ(x with xᵢ = z)` satisfies
  `∫ψ² + Σ_k∫(∂_kψ)² ≤ (Mv² + 3 Md²)·|B(0,R)|`;
* `fibre_fsT_uniform_bound_alt` — the consequence for the affine path
  `Ξ_t = t·F + G` (`|t| < 1`, `F, G` smooth compactly supported): there is a single `K` with
  `|fsT ℓ d s εT b 0 (fibreᵢ Ξ_t x)| ≤ K` for all `|t| < 1`, all slots and all `x` in the box.

The auxiliary lemmas are the elementary differential geometry of the insertion map
`z ↦ Function.update x i z`: its norm (`norm_update_zero`, `norm_update_le`), its continuity
(`continuous_update`), and the chain rule for the fibre (`fderiv_fibre_apply`), together with
the fact that a state vanishing beyond a ball propagates that property both to its fibres
(`fibre_eq_zero_of_gt`, `hasCompactSupport_fibre`) and to the fibres' differentials
(`fderiv_fibre_eq_zero_of_gt`).
-/

noncomputable section

open MeasureTheory
open scoped Topology

namespace Work.BoseFixB2.Polar

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- The insertion of a vector in one slot has the same norm. -/
lemma norm_update_zero {n : ℕ} (i : Fin n) (w : EuclideanSpace ℝ (Fin 3)) :
    ‖Function.update (0 : Submission.BoseGases.X n) i w‖ = ‖w‖ := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg w)).mpr fun j => ?_) ?_
  · by_cases hj : j = i
    · subst hj; rw [Function.update_self]
    · rw [Function.update_of_ne hj]; simp
  · have := norm_le_pi_norm (Function.update (0 : Submission.BoseGases.X n) i w) i
    rwa [Function.update_self] at this

/-- The value of `Pi.single` as an insertion. -/
lemma pi_single_apply_eq_update {n : ℕ} (i : Fin n) (w : EuclideanSpace ℝ (Fin 3)) :
    (ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ ℝ³))) w
      = Function.update (0 : Submission.BoseGases.X n) i w := by
  funext j
  rw [ContinuousLinearMap.pi_apply]
  by_cases hj : j = i
  · subst hj; rw [Pi.single_eq_same, ContinuousLinearMap.id_apply, Function.update_self]
  · rw [Pi.single_eq_of_ne hj, Function.update_of_ne hj]
    rfl

/-- The `k`-th partial derivative of a slot fibre. -/
lemma fderiv_fibre_apply {n : ℕ} {Ξ : Submission.BoseGases.X n → ℝ}
    (hΞ : ContDiff ℝ (⊤ : ℕ∞) Ξ) (i : Fin n) (x : Submission.BoseGases.X n)
    (z : EuclideanSpace ℝ (Fin 3)) (k : Fin 3) :
    fderiv ℝ (Work.BoseKinLoc.fibre n i Ξ x) z (Submission.BoseGases.kcStdBasis k)
      = fderiv ℝ Ξ (Function.update x i z)
          (Function.update (0 : Submission.BoseGases.X n) i (Submission.BoseGases.kcStdBasis k)) := by
  have h1 : DifferentiableAt ℝ Ξ (Function.update x i z) := hΞ.differentiable (by simp) _
  have h2 : DifferentiableAt ℝ
      (Function.update x i : EuclideanSpace ℝ (Fin 3) → Submission.BoseGases.X n) z :=
    (hasFDerivAt_update x (i := i) z).differentiableAt
  have hcomp : Work.BoseKinLoc.fibre n i Ξ x
      = Ξ ∘ (Function.update x i : EuclideanSpace ℝ (Fin 3) → Submission.BoseGases.X n) := rfl
  rw [hcomp, fderiv_comp z h1 h2, fderiv_update, ContinuousLinearMap.comp_apply,
    pi_single_apply_eq_update]

/-- The fibre vanishes far away when the state does. -/
lemma fibre_eq_zero_of_gt {n : ℕ} {Ξ : Submission.BoseGases.X n → ℝ} {R : ℝ}
    (hR : ∀ y : Submission.BoseGases.X n, R < ‖y‖ → Ξ y = 0) (i : Fin n)
    (x : Submission.BoseGases.X n) {z : EuclideanSpace ℝ (Fin 3)} (hz : R < ‖z‖) :
    Work.BoseKinLoc.fibre n i Ξ x z = 0 := by
  have h1 : ‖z‖ ≤ ‖Function.update x i z‖ := by
    have := norm_le_pi_norm (Function.update x i z) i
    rwa [Function.update_self] at this
  exact hR _ (lt_of_lt_of_le hz h1)

/-- A state vanishing beyond the ball of radius `R` has fibres vanishing beyond the ball of
radius `R` as well. -/
lemma hasCompactSupport_fibre {n : ℕ} {Ξ : Submission.BoseGases.X n → ℝ}
    (hΞcs : HasCompactSupport Ξ) (i : Fin n) (x : Submission.BoseGases.X n) :
    HasCompactSupport (Work.BoseKinLoc.fibre n i Ξ x) := by
  obtain ⟨R, hR⟩ := hΞcs.isCompact.isBounded.subset_closedBall (0 : Submission.BoseGases.X n)
  have hΞ0 : ∀ y : Submission.BoseGases.X n, R < ‖y‖ → Ξ y = 0 := by
    intro y hy
    refine Function.notMem_support.mp fun h => ?_
    have hy' : y ∉ Metric.closedBall (0 : Submission.BoseGases.X n) R := by
      simp only [Metric.mem_closedBall, dist_zero_right, not_le]; exact hy
    exact hy' (hR (subset_tsupport Ξ h))
  have hfib0 : ∀ z : EuclideanSpace ℝ (Fin 3), R < ‖z‖ →
      Work.BoseKinLoc.fibre n i Ξ x z = 0 := fun z hz => fibre_eq_zero_of_gt hΞ0 i x hz
  refine IsCompact.of_isClosed_subset
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) R) (isClosed_tsupport _) ?_
  refine closure_minimal (fun w hw => ?_) (isCompact_closedBall _ _).isClosed
  by_contra hcon
  rw [Metric.mem_closedBall, dist_zero_right] at hcon
  exact Function.mem_support.mp hw (hfib0 w (lt_of_not_ge hcon))

/-- The norm of a configuration after replacing one slot by `z`. -/
lemma norm_update_le {n : ℕ} (i : Fin n) (x : Submission.BoseGases.X n)
    (z : EuclideanSpace ℝ (Fin 3)) :
    ‖Function.update x i z‖ ≤ max ‖z‖ ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (le_max_of_le_right (norm_nonneg x))).mpr fun j => ?_
  by_cases hj : j = i
  · subst hj; rw [Function.update_self]; exact le_max_left _ _
  · rw [Function.update_of_ne hj]
    exact le_trans (norm_le_pi_norm x j) (le_max_right _ _)

/-- Replacing one slot is continuous. -/
lemma continuous_update {n : ℕ} (x : Submission.BoseGases.X n) (i : Fin n) :
    Continuous (Function.update x i) := by
  refine continuous_pi fun j => ?_
  by_cases hj : j = i
  · have h : (fun z : EuclideanSpace ℝ (Fin 3) => (Function.update x i z) j) = fun z => z := by
      funext z; rw [hj, Function.update_self]
    rw [h]; exact continuous_id
  · have h : (fun z : EuclideanSpace ℝ (Fin 3) => (Function.update x i z) j) = fun _ => x j := by
      funext z; rw [Function.update_of_ne hj]
    rw [h]; exact continuous_const

/-- If a function vanishes beyond the ball of radius `R`, its differential vanishes beyond it
as well. -/
lemma fderiv_fibre_eq_zero_of_gt {n : ℕ} {Ξ : Submission.BoseGases.X n → ℝ} {R : ℝ}
    (hR : ∀ y : Submission.BoseGases.X n, R < ‖y‖ → Ξ y = 0) (i : Fin n)
    (x : Submission.BoseGases.X n) {z : EuclideanSpace ℝ (Fin 3)} (hz : R < ‖z‖) :
    fderiv ℝ (Work.BoseKinLoc.fibre n i Ξ x) z = 0 := by
  have hpos : 0 < ‖z‖ - R := sub_pos.mpr hz
  have hlt : ∀ z' : EuclideanSpace ℝ (Fin 3), ‖z' - z‖ < ‖z‖ - R → R < ‖z'‖ := by
    intro z' hz'
    have h1 : ‖z‖ - ‖z'‖ ≤ ‖z' - z‖ := by
      rw [norm_sub_rev]; exact norm_sub_norm_le z z'
    linarith
  have hev : Work.BoseKinLoc.fibre n i Ξ x =ᶠ[𝓝 z] 0 := by
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds z hpos) fun z' hz' => ?_
    rw [Metric.mem_ball, dist_eq_norm] at hz'
    exact fibre_eq_zero_of_gt hR i x (hlt z' hz')
  have h0 : HasFDerivAt (fun _ : EuclideanSpace ℝ (Fin 3) => (0 : ℝ))
      (0 : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) z := hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) z
  have hf : HasFDerivAt (Work.BoseKinLoc.fibre n i Ξ x)
      (0 : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) z := h0.congr_of_eventuallyEq hev
  exact hf.fderiv

/-- **The `H¹` bound for fibres, from explicit radius and sup-bounds.**  If `Ξ` vanishes beyond the
ball of radius `R`, is bounded by `Mv` there and has differential bounded by `Md` there, then for
every `x` with `‖x‖ ≤ R` the slot-`i` fibre of `Ξ` at `x` has `L²`-plus-`H¹` mass at most
`(Mv² + 3 Md²)·|B(0,R)|`. -/
lemma fibre_H1_bound_of_bounds {n : ℕ} {R Mv Md : ℝ} {Ξ : Submission.BoseGases.X n → ℝ}
    (hΞcd : ContDiff ℝ (⊤ : ℕ∞) Ξ)
    (hΞ0 : ∀ y : Submission.BoseGases.X n, R < ‖y‖ → Ξ y = 0)
    (hbv : ∀ y : Submission.BoseGases.X n, ‖y‖ ≤ R → |Ξ y| ≤ Mv)
    (hbd : ∀ y : Submission.BoseGases.X n, ‖y‖ ≤ R → ‖fderiv ℝ Ξ y‖ ≤ Md)
    (hMv : 0 ≤ Mv) (hMd : 0 ≤ Md)
    (i : Fin n) (x : Submission.BoseGases.X n) (hx : ‖x‖ ≤ R) :
    (∫ z : EuclideanSpace ℝ (Fin 3), (Work.BoseKinLoc.fibre n i Ξ x z) ^ 2)
      + ∑ k : Fin 3, ∫ z : EuclideanSpace ℝ (Fin 3),
          (fderiv ℝ (Work.BoseKinLoc.fibre n i Ξ x) z (Submission.BoseGases.kcStdBasis k)) ^ 2
      ≤ (Mv ^ 2 + 3 * Md ^ 2) *
          (MeasureTheory.volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R)) := by
  have hfib0 : ∀ z : EuclideanSpace ℝ (Fin 3), R < ‖z‖ →
      Work.BoseKinLoc.fibre n i Ξ x z = 0 := fun z hz => fibre_eq_zero_of_gt hΞ0 i x hz
  have hfder0 : ∀ z : EuclideanSpace ℝ (Fin 3), R < ‖z‖ →
      fderiv ℝ (Work.BoseKinLoc.fibre n i Ξ x) z = 0 := fun z hz =>
    fderiv_fibre_eq_zero_of_gt hΞ0 i x hz
  have hvol : MeasureTheory.volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R) < ⊤ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) R).measure_lt_top
  have hmem : ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ R → ‖Function.update x i z‖ ≤ R :=
    fun z hz => le_trans (norm_update_le i x z) (max_le hz hx)
  -- pointwise value bound
  have hval : ∀ z : EuclideanSpace ℝ (Fin 3),
      (Work.BoseKinLoc.fibre n i Ξ x z) ^ 2 ≤ Mv ^ 2 := by
    intro z
    by_cases hz : ‖z‖ ≤ R
    · have h1 : |Work.BoseKinLoc.fibre n i Ξ x z| ≤ Mv := hbv _ (hmem z hz)
      rw [← sq_abs (Work.BoseKinLoc.fibre n i Ξ x z)]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    · rw [hfib0 z (lt_of_not_ge hz)]
      simpa using sq_nonneg Mv
  -- pointwise derivative bound
  have hvald : ∀ (z : EuclideanSpace ℝ (Fin 3)) (k : Fin 3),
      (fderiv ℝ (Work.BoseKinLoc.fibre n i Ξ x) z (Submission.BoseGases.kcStdBasis k)) ^ 2
        ≤ Md ^ 2 := by
    intro z k
    by_cases hz : ‖z‖ ≤ R
    · have h1 : |fderiv ℝ (Work.BoseKinLoc.fibre n i Ξ x) z
          (Submission.BoseGases.kcStdBasis k)| ≤ Md := by
        rw [fderiv_fibre_apply hΞcd i x z k]
        calc |fderiv ℝ Ξ (Function.update x i z)
              (Function.update (0 : Submission.BoseGases.X n) i
                (Submission.BoseGases.kcStdBasis k))|
            = ‖fderiv ℝ Ξ (Function.update x i z)
                (Function.update (0 : Submission.BoseGases.X n) i
                  (Submission.BoseGases.kcStdBasis k))‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖fderiv ℝ Ξ (Function.update x i z)‖ *
                ‖Function.update (0 : Submission.BoseGases.X n) i
                  (Submission.BoseGases.kcStdBasis k)‖ := ContinuousLinearMap.le_opNorm _ _
          _ = ‖fderiv ℝ Ξ (Function.update x i z)‖ * 1 := by
              rw [norm_update_zero, Submission.BoseGases.kcStdBasis, EuclideanSpace.norm_single]
              norm_num
          _ = ‖fderiv ℝ Ξ (Function.update x i z)‖ := mul_one _
          _ ≤ Md := hbd _ (hmem z hz)
      rw [← sq_abs (fderiv ℝ (Work.BoseKinLoc.fibre n i Ξ x) z
        (Submission.BoseGases.kcStdBasis k))]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    · have h1 : fderiv ℝ (Work.BoseKinLoc.fibre n i Ξ x) z
          (Submission.BoseGases.kcStdBasis k) = 0 := by
        rw [hfder0 z (lt_of_not_ge hz)]
        simp
      rw [h1]
      simpa using sq_nonneg Md
  -- the two integral bounds
  have hI1 : ∫ z : EuclideanSpace ℝ (Fin 3), (Work.BoseKinLoc.fibre n i Ξ x z) ^ 2
      ≤ Mv ^ 2 * MeasureTheory.volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R) := by
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
      rw [Metric.mem_closedBall, dist_zero_right, not_le] at hz
      rw [hfib0 z hz]; ring]
    have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const
      (f := fun z : EuclideanSpace ℝ (Fin 3) => (Work.BoseKinLoc.fibre n i Ξ x z) ^ 2)
      (s := Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R) (C := Mv ^ 2) hvol
      (fun z _ => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hval z)
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  have hI2 : ∑ k : Fin 3, ∫ z : EuclideanSpace ℝ (Fin 3),
        (fderiv ℝ (Work.BoseKinLoc.fibre n i Ξ x) z (Submission.BoseGases.kcStdBasis k)) ^ 2
      ≤ 3 * Md ^ 2 * MeasureTheory.volume.real
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R) := by
    have hk : ∀ k : Fin 3, ∫ z : EuclideanSpace ℝ (Fin 3),
          (fderiv ℝ (Work.BoseKinLoc.fibre n i Ξ x) z (Submission.BoseGases.kcStdBasis k)) ^ 2
        ≤ Md ^ 2 * MeasureTheory.volume.real
            (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R) := by
      intro k
      rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
        rw [Metric.mem_closedBall, dist_zero_right, not_le] at hz
        rw [hfder0 z hz]; simp]
      have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const
        (f := fun z : EuclideanSpace ℝ (Fin 3) =>
          (fderiv ℝ (Work.BoseKinLoc.fibre n i Ξ x) z (Submission.BoseGases.kcStdBasis k)) ^ 2)
        (s := Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R) (C := Md ^ 2) hvol
        (fun z _ => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hvald z k)
      rw [Real.norm_eq_abs] at h
      exact (le_abs_self _).trans h
    calc ∑ k : Fin 3, ∫ z : EuclideanSpace ℝ (Fin 3),
          (fderiv ℝ (Work.BoseKinLoc.fibre n i Ξ x) z (Submission.BoseGases.kcStdBasis k)) ^ 2
        ≤ ∑ _k : Fin 3, Md ^ 2 *
            MeasureTheory.volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R) :=
          Finset.sum_le_sum fun k _ => hk k
      _ = 3 * Md ^ 2 * MeasureTheory.volume.real
            (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  calc (∫ z : EuclideanSpace ℝ (Fin 3), (Work.BoseKinLoc.fibre n i Ξ x z) ^ 2)
        + ∑ k : Fin 3, ∫ z : EuclideanSpace ℝ (Fin 3),
            (fderiv ℝ (Work.BoseKinLoc.fibre n i Ξ x) z (Submission.BoseGases.kcStdBasis k)) ^ 2
      ≤ Mv ^ 2 * MeasureTheory.volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R)
        + 3 * Md ^ 2 * MeasureTheory.volume.real
            (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R) := add_le_add hI1 hI2
    _ = (Mv ^ 2 + 3 * Md ^ 2) *
          MeasureTheory.volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R) := by ring

/-- The differential of the affine combination `t·F + G`. -/
lemma fderiv_affine {n : ℕ} {F G : Submission.BoseGases.X n → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (t : ℝ)
    (y : Submission.BoseGases.X n) :
    fderiv ℝ (fun y' => t * F y' + G y') y = t • fderiv ℝ F y + fderiv ℝ G y := by
  have h1 : (fun y' : Submission.BoseGases.X n => t * F y' + G y') = t • F + G := by
    funext y'
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [h1, fderiv_add ((hF.differentiable (by simp) y).const_smul t)
        (hG.differentiable (by simp) y),
    fderiv_const_smul (hF.differentiable (by simp) y) t]

/-- **The one-body word `fsT` is uniformly bounded on the slot fibres of a compactly supported
affine path.**  For smooth compactly supported `F, G` there is `K` with
`|fsT ℓ d s εT b 0 (fibreᵢ (t·F + G) x)| ≤ K` for all `|t| < 1`, all slots `i` and all box
configurations `x ∈ abox n ℓ`. -/
theorem fibre_fsT_uniform_bound_alt {n : ℕ} {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ)
    {F G : Submission.BoseGases.X n → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hFcs : HasCompactSupport F) (hGcs : HasCompactSupport G) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Ioo (-1 : ℝ) 1,
      ∀ (i : Fin n) (x : Submission.BoseGases.X n), x ∈ Submission.BoseGases.abox n ℓ →
        |Work.BoseKinLoc.fsT ℓ d s εT b (0 : EuclideanSpace ℝ (Fin 3))
          (Work.BoseKinLoc.fibre n i (fun y => t * F y + G y) x)| ≤ K := by
  obtain ⟨C, hC0, hfsT⟩ :=
    Work.BoseKinLoc.Kinetic.fsT_H1_bound_all (ℓ := ℓ) (d := d) (s := s) (εT := εT) (b := b) hℓ
  obtain ⟨R, hR⟩ := hFcs.isCompact.isBounded.subset_closedBall (0 : Submission.BoseGases.X n)
  have hF0 : ∀ y : Submission.BoseGases.X n, R < ‖y‖ → F y = 0 := by
    intro y hy
    refine Function.notMem_support.mp fun h => ?_
    have hy' : y ∉ Metric.closedBall (0 : Submission.BoseGases.X n) R := by
      simp only [Metric.mem_closedBall, dist_zero_right, not_le]; exact hy
    exact hy' (hR (subset_tsupport F h))
  obtain ⟨R', hR'⟩ := hGcs.isCompact.isBounded.subset_closedBall (0 : Submission.BoseGases.X n)
  have hG0 : ∀ y : Submission.BoseGases.X n, R' < ‖y‖ → G y = 0 := by
    intro y hy
    refine Function.notMem_support.mp fun h => ?_
    have hy' : y ∉ Metric.closedBall (0 : Submission.BoseGases.X n) R' := by
      simp only [Metric.mem_closedBall, dist_zero_right, not_le]; exact hy
    exact hy' (hR' (subset_tsupport G h))
  obtain ⟨r, hr⟩ := (Submission.BoseGases.abox_compact n hℓ).isBounded.subset_closedBall
    (0 : Submission.BoseGases.X n)
  set S : ℝ := max (max R R') r with hS
  have hS0R : R ≤ S := le_trans (le_max_left R R') (le_max_left _ _)
  have hS0G : R' ≤ S := le_trans (le_max_right R R') (le_max_left _ _)
  have hSr : r ≤ S := le_max_right _ _
  -- sup bounds
  obtain ⟨Mv0, hMv0⟩ := (isCompact_closedBall (0 : Submission.BoseGases.X n) S).bddAbove_image
    ((hF.continuous.abs.add hG.continuous.abs).continuousOn)
  set Mv : ℝ := max Mv0 0 with hMv
  have hMv' : ∀ y ∈ Metric.closedBall (0 : Submission.BoseGases.X n) S,
      |F y| + |G y| ≤ Mv := fun y hy =>
    le_trans (hMv0 (a := |F y| + |G y|) ⟨y, hy, rfl⟩) (le_max_left _ _)
  have hMv0' : 0 ≤ Mv := le_max_right _ _
  obtain ⟨Md0, hMd0⟩ := (isCompact_closedBall (0 : Submission.BoseGases.X n) S).bddAbove_image
    (((hF.continuous_fderiv (by simp)).norm.add
      (hG.continuous_fderiv (by simp)).norm).continuousOn)
  set Md : ℝ := max Md0 0 with hMd
  have hMd' : ∀ y ∈ Metric.closedBall (0 : Submission.BoseGases.X n) S,
      ‖fderiv ℝ F y‖ + ‖fderiv ℝ G y‖ ≤ Md := fun y hy =>
    le_trans (hMd0 (a := ‖fderiv ℝ F y‖ + ‖fderiv ℝ G y‖) ⟨y, hy, rfl⟩) (le_max_left _ _)
  have hMd0' : 0 ≤ Md := le_max_right _ _
  -- the uniform `H¹` bound
  have hH1 : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, ∀ (i : Fin n) (x : Submission.BoseGases.X n),
      x ∈ Submission.BoseGases.abox n ℓ →
      (∫ z : EuclideanSpace ℝ (Fin 3),
          (Work.BoseKinLoc.fibre n i (fun y => t * F y + G y) x z) ^ 2)
        + ∑ k : Fin 3, ∫ z : EuclideanSpace ℝ (Fin 3),
            (fderiv ℝ (Work.BoseKinLoc.fibre n i (fun y => t * F y + G y) x) z
              (Submission.BoseGases.kcStdBasis k)) ^ 2
        ≤ (Mv ^ 2 + 3 * Md ^ 2) *
            (MeasureTheory.volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) S)) := by
    intro t ht i x hx
    have ht1 : |t| ≤ 1 := le_of_lt (abs_lt.mpr ht)
    have hxS : ‖x‖ ≤ S := le_trans (by
      have h1 : x ∈ Metric.closedBall (0 : Submission.BoseGases.X n) r := hr hx
      rwa [Metric.mem_closedBall, dist_zero_right] at h1) hSr
    refine fibre_H1_bound_of_bounds (Ξ := fun y => t * F y + G y) (R := S) (Mv := Mv) (Md := Md)
      (((contDiff_const.mul hF).add hG)) ?_ ?_ ?_ hMv0' hMd0' i x hxS
    · intro y hy
      rw [hF0 y (lt_of_le_of_lt hS0R hy), hG0 y (lt_of_le_of_lt hS0G hy)]
      ring
    · intro y hy
      have h1 : |t * F y + G y| ≤ |t| * |F y| + |G y| := by
        calc |t * F y + G y| ≤ |t * F y| + |G y| := abs_add_le _ _
          _ = |t| * |F y| + |G y| := by rw [abs_mul]
      have h2 : |t| * |F y| ≤ 1 * |F y| := mul_le_mul_of_nonneg_right ht1 (abs_nonneg _)
      have hyb : y ∈ Metric.closedBall (0 : Submission.BoseGases.X n) S := by
        rw [Metric.mem_closedBall, dist_zero_right]; exact hy
      have h3 : |F y| + |G y| ≤ Mv := hMv' y hyb
      linarith
    · intro y hy
      rw [fderiv_affine hF hG t y]
      have h1 : ‖t • fderiv ℝ F y + fderiv ℝ G y‖
          ≤ ‖t • fderiv ℝ F y‖ + ‖fderiv ℝ G y‖ := norm_add_le _ _
      have h2 : ‖t • fderiv ℝ F y‖ = |t| * ‖fderiv ℝ F y‖ := norm_smul t _
      have h3 : |t| * ‖fderiv ℝ F y‖ ≤ 1 * ‖fderiv ℝ F y‖ :=
        mul_le_mul_of_nonneg_right ht1 (norm_nonneg _)
      have hyb : y ∈ Metric.closedBall (0 : Submission.BoseGases.X n) S := by
        rw [Metric.mem_closedBall, dist_zero_right]; exact hy
      have h4 : ‖fderiv ℝ F y‖ + ‖fderiv ℝ G y‖ ≤ Md := hMd' y hyb
      linarith [h1, h4]
  refine ⟨C * ((Mv ^ 2 + 3 * Md ^ 2) *
    (MeasureTheory.volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) S))),
    mul_nonneg hC0 (mul_nonneg (by positivity) MeasureTheory.measureReal_nonneg), ?_⟩
  intro t ht i x hx
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun y => t * F y + G y) := (contDiff_const.mul hF).add hG
  have hcs : HasCompactSupport (fun y : Submission.BoseGases.X n => t * F y + G y) :=
    ((hFcs.smul_left (f := fun _ : Submission.BoseGases.X n => t))).add hGcs
  have h1 : ContDiff ℝ (⊤ : ℕ∞)
      (Work.BoseKinLoc.fibre n i (fun y => t * F y + G y) x) :=
    hcd.comp (contDiff_update (⊤ : ℕ∞) x i)
  have h2 : HasCompactSupport
      (Work.BoseKinLoc.fibre n i (fun y => t * F y + G y) x) := hasCompactSupport_fibre hcs i x
  exact le_trans (hfsT 0 _ h1 h2) (mul_le_mul_of_nonneg_left (hH1 t ht i x hx) hC0)

end Work.BoseFixB2.Polar
