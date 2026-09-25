/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The `C^{1,α}` Schauder estimate for the Bochner–Martinelli potential of Hölder data

The main result of this file is `Work.NN.Core.bmPot_holder_C0a`: for `0 < α < 1`, a centre `c` and
positive multi-radii `r`, there is `C > 0` such that for every `(0,1)`-form
`g : Fin n → (Fin n → ℂ) → ℂ` whose components vanish off the half-polydisc
`polydisc c (r/2)` and whose `C^{0,α}`-norms on `ℂⁿ` are finite, the Bochner–Martinelli potential
`bmPot g` is of class `C^{1,α}` on `polydisc c (r/2)`, with

  `‖bmPot g‖_{C^{1,α}(polydisc c (r/2))} ≤ C · Σ_j ‖g_j‖_{C^{0,α}(ℂⁿ)}`.

Unlike the classical statement (`Work.NN.Core.bmPotential_holder`, which assumes the data to be
`C¹`), the data here are only assumed to be Hölder continuous.  The proof approximates `g` by the
smooth mollifications `G m` of `Work.NN.Core.bmSmoothApprox` (which keep the `C^{0,α}`-norm and
the support), applies the `C¹` Schauder estimate to each `G m`, and passes to the limit.  The
limit is made possible by the explicit formula for the derivative of the potential of smooth data,
`Work.NN.Core.fderiv_bmPot_eq_bmDerivData`, which exhibits `fderiv ℝ (bmPot f) z` as an integral
only involving the *values* of `f`; the corresponding candidate derivative for the Hölder data `g`
is `Work.NN.Core.bmDerivData`, and the convergence of the candidates is `tendsto_bmDerivData`.
-/
import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Cauchy.bmDefs
import Submission.Work.CR.Flat.Cauchy.bmSetup
import Submission.Work.CR.Flat.Cauchy.bmCZDefs
import Submission.Work.CR.Flat.Cauchy.bmPot_dbarCoord
import Submission.Work.CR.Flat.Cauchy.bmCz.bmPot_dCoord
import Submission.Work.CR.Flat.Cauchy.bmCz.integral_bmKernel_mul_dCoord
import Submission.Work.CR.Flat.Cauchy.bmCz.integral_bmKernel_mul_dbarCoord
import Submission.Work.CR.Flat.Cauchy.bmPotential_contDiff_one
import Submission.Work.CR.Flat.Cauchy.bmPotential_tendsto_of_tendsto
import Submission.Work.NN.Core.bmDerivData
import Submission.Work.NN.Core.bmPotential_holder
import Submission.Work.NN.Core.bmSmoothApprox
import Submission.Work.NN.Core.czHolderBound

noncomputable section

open scoped NNReal ENNReal
open MeasureTheory Set Filter

namespace Work.NN.Core

open Work.CR.Flat
open Work.CR.Flat.Cauchy


/-! ## The derivative formula for smooth data -/

/-- `dbarCoord` of a translation: `∂̄_j (y ↦ g (z + y)) x = ∂̄_j g (z + x)`. -/
lemma bmDbarCoord_comp_add {n : ℕ} (j : Fin n) {g : (Fin n → ℂ) → ℂ} {z x : Fin n → ℂ}
    (hg : DifferentiableAt ℝ g (z + x)) :
    dbarCoord j (fun y => g (z + y)) x = dbarCoord j g (z + x) := by
  have hshift : HasFDerivAt (fun y : Fin n → ℂ => z + y)
      (ContinuousLinearMap.id ℝ (Fin n → ℂ)) x :=
    (hasFDerivAt_id x).const_add z
  have h := (hg.hasFDerivAt).comp x hshift
  simp only [Function.comp_def, ContinuousLinearMap.id_comp] at h
  rw [dbarCoord, dbarCoord, h.fderiv, ContinuousLinearMap.comp_id]

/-- The `∂`-Wirtinger derivative of the Bochner–Martinelli potential of `C¹` data is the
singular integral `bmDzPart` (no derivative of the data occurs). -/
lemma dCoord_bmPot_eq_bmDzPart {n : ℕ} (hn : 0 < n)
    {f : Fin n → (Fin n → ℂ) → ℂ} (hf : ∀ k, ContDiff ℝ 1 (f k)) {R : ℝ} (hR : 0 < R)
    (hsupp : ∀ (k : Fin n) (x : Fin n → ℂ), R ≤ ‖x‖ → f k x = 0) {z : Fin n → ℂ}
    (hz : ∀ (k : Fin n) (x : Fin n → ℂ), R ≤ eucNorm x → f k (z + x) = 0) (j : Fin n) :
    dCoord j (bmPot f) z = bmDzPart R f z j := by
  rw [bmCz.bmPot_dCoord hn hf hR hsupp j z, bmDzPart, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h2 := bmCz.integral_bmKernel_mul_dCoord hn j k (fun y => f k (z + y)) R hR
    ((hf k).comp (contDiff_const.add contDiff_id)) (fun x hx => hz k x hx)
  simp only [add_zero] at h2
  rw [← h2]
  refine integral_congr_ae ?_
  filter_upwards with x
  rw [dCoord_comp_add j ((hf k).differentiable (by norm_num)).differentiableAt]

/-- The `∂̄`-Wirtinger derivative of the Bochner–Martinelli potential of `C¹` data is the
singular integral `bmDbarPart` (no derivative of the data occurs). -/
lemma dbarCoord_bmPot_eq_bmDbarPart {n : ℕ} (hn : 0 < n) {cc : Fin n → Fin n → ℂ}
    (hcc : ∀ (j k : Fin n) (h : (Fin n → ℂ) → ℂ) (R : ℝ), 0 < R → ContDiff ℝ 1 h →
      (∀ x : Fin n → ℂ, R ≤ eucNorm x → h x = 0) →
      ∫ x, bmKernel k x * dbarCoord j h x
        = (-∫ x in eucBall (n := n) (4 * R), bmDbarKernel j k x * (h x - h 0)) - cc j k * h 0)
    {f : Fin n → (Fin n → ℂ) → ℂ} (hf : ∀ k, ContDiff ℝ 1 (f k)) {R : ℝ} (hR : 0 < R)
    (hsupp : ∀ (k : Fin n) (x : Fin n → ℂ), R ≤ ‖x‖ → f k x = 0) {z : Fin n → ℂ}
    (hz : ∀ (k : Fin n) (x : Fin n → ℂ), R ≤ eucNorm x → f k (z + x) = 0) (j : Fin n) :
    dbarCoord j (bmPot f) z = bmDbarPart R cc f z j := by
  rw [bmPot_dbarCoord hn hf hR hsupp j z, bmDbarPart]
  have hsplit : (-∑ k, ∫ x in eucBall (n := n) (4 * R),
        bmDbarKernel j k x * (f k (z + x) - f k z)) - ∑ k, cc j k * f k z
      = ∑ k, ((-∫ x in eucBall (n := n) (4 * R),
            bmDbarKernel j k x * (f k (z + x) - f k z)) - cc j k * f k z) := by
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [hsplit]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h2 := hcc j k (fun y => f k (z + y)) R hR ((hf k).comp (contDiff_const.add contDiff_id))
    (fun x hx => hz k x hx)
  simp only [add_zero] at h2
  rw [← h2]
  refine integral_congr_ae ?_
  filter_upwards with x
  rw [bmDbarCoord_comp_add j ((hf k).differentiable (by norm_num)).differentiableAt]

/-- **The derivative of the Bochner–Martinelli potential of `C¹` data, in terms of the values of
the data.**  Under the support conditions on `f` and on the shifted family `f k (z + ·)`, the
Fréchet derivative of `bmPot f` at `z` is the candidate `bmDerivData R cc f z`, which involves no
derivative of `f`. -/
theorem fderiv_bmPot_eq_bmDerivData {n : ℕ} (hn : 0 < n) {cc : Fin n → Fin n → ℂ}
    (hcc : ∀ (j k : Fin n) (h : (Fin n → ℂ) → ℂ) (R : ℝ), 0 < R → ContDiff ℝ 1 h →
      (∀ x : Fin n → ℂ, R ≤ eucNorm x → h x = 0) →
      ∫ x, bmKernel k x * dbarCoord j h x
        = (-∫ x in eucBall (n := n) (4 * R), bmDbarKernel j k x * (h x - h 0)) - cc j k * h 0)
    {f : Fin n → (Fin n → ℂ) → ℂ} (hf : ∀ k, ContDiff ℝ 1 (f k)) {R : ℝ} (hR : 0 < R)
    (hsupp : ∀ (k : Fin n) (x : Fin n → ℂ), R ≤ ‖x‖ → f k x = 0) {z : Fin n → ℂ}
    (hz : ∀ (k : Fin n) (x : Fin n → ℂ), R ≤ eucNorm x → f k (z + x) = 0) :
    fderiv ℝ (bmPot f) z = bmDerivData R cc f z := by
  refine clm_ext_single ?_ ?_
  · intro j
    rw [fderiv_single_one, bmDerivData_single_one,
      dCoord_bmPot_eq_bmDzPart hn hf hR hsupp hz j,
      dbarCoord_bmPot_eq_bmDbarPart hn hcc hf hR hsupp hz j]
  · intro j
    rw [fderiv_single_I, bmDerivData_single_I,
      dCoord_bmPot_eq_bmDzPart hn hf hR hsupp hz j,
      dbarCoord_bmPot_eq_bmDbarPart hn hcc hf hR hsupp hz j]


/-! ## The convergence of the candidate derivative in the data -/

/-- **`bmDerivData` is continuous in the data** (pointwise, in the weak topology): if the data
`G m` converge pointwise to `g` and are uniformly `α`-Hölder with constants `K j`, then the
candidate derivatives converge pointwise. -/
theorem tendsto_bmDerivData_apply {n : ℕ} (hn : 0 < n) {R : ℝ} (hR : 0 < R)
    (cc : Fin n → Fin n → ℂ) {α : ℝ} (hα : 0 < α) {K : Fin n → ℝ} (hK : ∀ j, 0 ≤ K j)
    {g : Fin n → (Fin n → ℂ) → ℂ} {G : ℕ → Fin n → (Fin n → ℂ) → ℂ}
    (hG : ∀ m j x y, ‖G m j x - G m j y‖ ≤ K j * ‖x - y‖ ^ α)
    (hg : ∀ j x y, ‖g j x - g j y‖ ≤ K j * ‖x - y‖ ^ α)
    (hconv : ∀ j z, Tendsto (fun m => G m j z) atTop (nhds (g j z))) :
    ∀ (z v : Fin n → ℂ), Tendsto (fun m => bmDerivData R cc (G m) z v) atTop
      (nhds (bmDerivData R cc g z v)) := by
  intro z v
  obtain ⟨hmeas_dz, hmeas_dbar, Cd, hCdpos, hdec_dz, hdec_dbar⟩ := bmCz.bmKernel_decay_le hn
  have h4R : (0 : ℝ) < 4 * R := by linarith
  have hexp : -(2 * (n : ℝ)) < α - 2 * (n : ℝ) := by linarith
  have hdom_int : ∀ k : Fin n, IntegrableOn
      (fun x : Fin n → ℂ => Cd * K k * eucNorm x ^ (α - 2 * (n : ℝ))) (eucBall (n := n) (4 * R)) :=
    fun k => (integrableOn_eucNorm_rpow_ball hn hexp (4 * R)).const_mul _
  have hscal : ∀ (k : Fin n) (y : Fin n → ℂ), 0 < eucNorm y →
      (Cd / (eucNorm y) ^ (2 * n)) * (K k * eucNorm y ^ α)
        ≤ Cd * K k * eucNorm y ^ (α - 2 * (n : ℝ)) := by
    intro k y hy
    have hE : (eucNorm y) ^ (2 * n) = (eucNorm y) ^ (2 * (n : ℝ)) := by
      rw [← Real.rpow_natCast (eucNorm y) (2 * n)]
      congr 1
      push_cast
      ring
    have key : (Cd / (eucNorm y) ^ (2 * n)) * (K k * eucNorm y ^ α)
        = Cd * K k * (eucNorm y ^ (-(2 * (n : ℝ))) * eucNorm y ^ α) := by
      rw [hE, div_eq_mul_inv, ← Real.rpow_neg (eucNorm_nonneg y)]
      ring
    rw [key, ← Real.rpow_add hy,
      show -(2 * (n : ℝ)) + α = α - 2 * (n : ℝ) from by ring]
  have hbd_dz : ∀ (j k : Fin n) (m : ℕ) (x : Fin n → ℂ),
      ‖bmDzKernel j k x * (G m k (z + x) - G m k z)‖
        ≤ Cd * K k * eucNorm x ^ (α - 2 * (n : ℝ)) := by
    intro j k m x
    rcases eq_or_ne x 0 with rfl | hx
    · simp only [add_zero, sub_self, mul_zero, norm_zero]
      exact mul_nonneg (mul_nonneg hCdpos.le (hK k))
        (Real.rpow_nonneg (eucNorm_nonneg (0 : Fin n → ℂ)) _)
    · have hxpos : 0 < eucNorm x := eucNorm_pos hx
      rw [norm_mul]
      refine (mul_le_mul (hdec_dz j k x hx) ?_ (norm_nonneg _)
        (div_nonneg hCdpos.le (by positivity))).trans (hscal k x hxpos)
      refine (hG m k (z + x) z).trans ?_
      rw [show (z + x) - z = x from by abel]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg x) (pi_norm_le_eucNorm x) hα.le) (hK k)
  have hbd_dbar : ∀ (j k : Fin n) (m : ℕ) (x : Fin n → ℂ),
      ‖bmDbarKernel j k x * (G m k (z + x) - G m k z)‖
        ≤ Cd * K k * eucNorm x ^ (α - 2 * (n : ℝ)) := by
    intro j k m x
    rcases eq_or_ne x 0 with rfl | hx
    · simp only [add_zero, sub_self, mul_zero, norm_zero]
      exact mul_nonneg (mul_nonneg hCdpos.le (hK k))
        (Real.rpow_nonneg (eucNorm_nonneg (0 : Fin n → ℂ)) _)
    · have hxpos : 0 < eucNorm x := eucNorm_pos hx
      rw [norm_mul]
      refine (mul_le_mul (hdec_dbar j k x hx) ?_ (norm_nonneg _)
        (div_nonneg hCdpos.le (by positivity))).trans (hscal k x hxpos)
      refine (hG m k (z + x) z).trans ?_
      rw [show (z + x) - z = x from by abel]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg x) (pi_norm_le_eucNorm x) hα.le) (hK k)
  have hint_dz : ∀ j k : Fin n, Tendsto (fun m => ∫ x in eucBall (n := n) (4 * R),
        bmDzKernel j k x * (G m k (z + x) - G m k z)) atTop
      (nhds (∫ x in eucBall (n := n) (4 * R), bmDzKernel j k x * (g k (z + x) - g k z))) := by
    intro j k
    refine tendsto_integral_of_dominated_convergence
      (fun x : Fin n → ℂ => Cd * K k * eucNorm x ^ (α - 2 * (n : ℝ))) ?_ (hdom_int k) ?_ ?_
    · intro m
      exact ((hmeas_dz j k).mul
        (((continuous_of_holder_bound hα (hK k) (hG m k)).comp
          (continuous_const.add continuous_id)).sub continuous_const).aestronglyMeasurable).mono_measure
        Measure.restrict_le_self
    · intro m
      filter_upwards with x
      exact hbd_dz j k m x
    · filter_upwards with x
      exact ((hconv k (z + x)).sub (hconv k z)).const_mul _
  have hint_dbar : ∀ j k : Fin n, Tendsto (fun m => ∫ x in eucBall (n := n) (4 * R),
        bmDbarKernel j k x * (G m k (z + x) - G m k z)) atTop
      (nhds (∫ x in eucBall (n := n) (4 * R), bmDbarKernel j k x * (g k (z + x) - g k z))) := by
    intro j k
    refine tendsto_integral_of_dominated_convergence
      (fun x : Fin n → ℂ => Cd * K k * eucNorm x ^ (α - 2 * (n : ℝ))) ?_ (hdom_int k) ?_ ?_
    · intro m
      exact ((hmeas_dbar j k).mul
        (((continuous_of_holder_bound hα (hK k) (hG m k)).comp
          (continuous_const.add continuous_id)).sub continuous_const).aestronglyMeasurable).mono_measure
        Measure.restrict_le_self
    · intro m
      filter_upwards with x
      exact hbd_dbar j k m x
    · filter_upwards with x
      exact ((hconv k (z + x)).sub (hconv k z)).const_mul _
  have hDz : ∀ j : Fin n, Tendsto (fun m => bmDzPart R (G m) z j) atTop (nhds (bmDzPart R g z j)) := by
    intro j
    have h : Tendsto (fun m => ∑ k, ∫ x in eucBall (n := n) (4 * R),
          bmDzKernel j k x * (G m k (z + x) - G m k z)) atTop
        (nhds (∑ k, ∫ x in eucBall (n := n) (4 * R),
          bmDzKernel j k x * (g k (z + x) - g k z))) :=
      tendsto_finsetSum _ fun k _ => hint_dz j k
    simpa only [bmDzPart] using h.neg
  have hDbar : ∀ j : Fin n, Tendsto (fun m => bmDbarPart R cc (G m) z j) atTop
      (nhds (bmDbarPart R cc g z j)) := by
    intro j
    have h1 : Tendsto (fun m => ∑ k, ∫ x in eucBall (n := n) (4 * R),
          bmDbarKernel j k x * (G m k (z + x) - G m k z)) atTop
        (nhds (∑ k, ∫ x in eucBall (n := n) (4 * R),
          bmDbarKernel j k x * (g k (z + x) - g k z))) :=
      tendsto_finsetSum _ fun k _ => hint_dbar j k
    have h2 : Tendsto (fun m => ∑ k, cc j k * G m k z) atTop (nhds (∑ k, cc j k * g k z)) :=
      tendsto_finsetSum _ fun k _ => (hconv k z).const_mul _
    simpa only [bmDbarPart] using h1.neg.sub h2
  simp only [bmDerivData_apply]
  refine (tendsto_finsetSum _ fun j _ => ?_).add (tendsto_finsetSum _ fun j _ => ?_)
  · exact ((hDz j).add (hDbar j)).const_smul _
  · exact (((hDz j).sub (hDbar j)).const_mul Complex.I).const_smul _

/-! ## Reading off the pointwise bounds from a `C^{1,α}` bound -/

/-- The norm of `fderivWithin` is bounded by the norm of the `1`-st iterated within-derivative
(the two are linearly isometric). -/
lemma norm_fderivWithin_sub_le_iteratedFDerivWithin_one {n : ℕ} (u : (Fin n → ℂ) → ℂ)
    (Ω : Set (Fin n → ℂ)) (x y : Fin n → ℂ) (hx : UniqueDiffWithinAt ℝ Ω x)
    (hy : UniqueDiffWithinAt ℝ Ω y) :
    ‖fderivWithin ℝ u Ω x - fderivWithin ℝ u Ω y‖
      ≤ ‖iteratedFDerivWithin ℝ 1 u Ω x - iteratedFDerivWithin ℝ 1 u Ω y‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  have hv : (fderivWithin ℝ u Ω x - fderivWithin ℝ u Ω y) v
      = (iteratedFDerivWithin ℝ 1 u Ω x - iteratedFDerivWithin ℝ 1 u Ω y)
          (fun _ : Fin 1 => v) := by
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
      iteratedFDerivWithin_one_apply hx, iteratedFDerivWithin_one_apply hy]
  rw [hv]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  rw [show (∏ i : Fin 1, ‖(fun _ : Fin 1 => v) i‖) = ‖v‖ from by simp]

/-- A `C^{1,α}` bound on `P` gives the four pointwise bounds used in the Schauder estimates. -/
theorem holderNorm_one_bounds {n : ℕ} {α C : ℝ} {u : (Fin n → ℂ) → ℂ} {P : Set (Fin n → ℂ)}
    (hPopen : IsOpen P) (hC : 0 ≤ C)
    (h : holderNorm 1 α u P ≤ ENNReal.ofReal C) :
    (∀ z ∈ P, ‖u z‖ ≤ C) ∧ (∀ x ∈ P, ∀ y ∈ P, ‖u x - u y‖ ≤ C * ‖x - y‖ ^ α) ∧
    (∀ z ∈ P, ‖fderiv ℝ u z‖ ≤ C) ∧
    (∀ x ∈ P, ∀ y ∈ P, ‖fderiv ℝ u x - fderiv ℝ u y‖ ≤ C * ‖x - y‖ ^ α) := by
  have hsum : (iterDerivNorm 0 u P + holderSeminorm 0 α u P)
      + (iterDerivNorm 1 u P + holderSeminorm 1 α u P) ≤ ENNReal.ofReal C := by
    rw [holderNorm_one_eq] at h
    exact h
  have hA : iterDerivNorm 0 u P ≤ ENNReal.ofReal C :=
    calc iterDerivNorm 0 u P ≤ iterDerivNorm 0 u P + holderSeminorm 0 α u P :=
          le_add_of_nonneg_right zero_le
      _ ≤ (iterDerivNorm 0 u P + holderSeminorm 0 α u P)
            + (iterDerivNorm 1 u P + holderSeminorm 1 α u P) := le_add_of_nonneg_right zero_le
      _ ≤ ENNReal.ofReal C := hsum
  have hB : holderSeminorm 0 α u P ≤ ENNReal.ofReal C :=
    calc holderSeminorm 0 α u P ≤ iterDerivNorm 0 u P + holderSeminorm 0 α u P :=
          le_add_of_nonneg_left zero_le
      _ ≤ (iterDerivNorm 0 u P + holderSeminorm 0 α u P)
            + (iterDerivNorm 1 u P + holderSeminorm 1 α u P) := le_add_of_nonneg_right zero_le
      _ ≤ ENNReal.ofReal C := hsum
  have hC' : iterDerivNorm 1 u P ≤ ENNReal.ofReal C :=
    calc iterDerivNorm 1 u P ≤ iterDerivNorm 1 u P + holderSeminorm 1 α u P :=
          le_add_of_nonneg_right zero_le
      _ ≤ (iterDerivNorm 0 u P + holderSeminorm 0 α u P)
            + (iterDerivNorm 1 u P + holderSeminorm 1 α u P) := le_add_of_nonneg_left zero_le
      _ ≤ ENNReal.ofReal C := hsum
  have hD : holderSeminorm 1 α u P ≤ ENNReal.ofReal C :=
    calc holderSeminorm 1 α u P ≤ iterDerivNorm 1 u P + holderSeminorm 1 α u P :=
          le_add_of_nonneg_left zero_le
      _ ≤ (iterDerivNorm 0 u P + holderSeminorm 0 α u P)
            + (iterDerivNorm 1 u P + holderSeminorm 1 α u P) := le_add_of_nonneg_left zero_le
      _ ≤ ENNReal.ofReal C := hsum
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    have h1 : ENNReal.ofReal ‖u z‖ ≤ iterDerivNorm 0 u P := by
      rw [← norm_iteratedFDerivWithin_zero (𝕜 := ℝ) (f := u) (s := P) (x := z)]
      exact le_iterDerivNorm 0 u P hz
    refine (ENNReal.ofReal_le_ofReal_iff hC).mp ?_
    exact le_trans h1 hA
  · intro x hx y hy
    rcases eq_or_ne x y with rfl | hxy
    · rw [sub_self, norm_zero]
      exact mul_nonneg hC (Real.rpow_nonneg (norm_nonneg _) _)
    · have h1 : ENNReal.ofReal (‖u x - u y‖ / ‖x - y‖ ^ α) ≤ holderSeminorm 0 α u P := by
        simpa [Work.NN.Core.norm_iteratedFDerivWithin_zero_sub u P x y] using
          le_holderSeminorm 0 α u P hx hy hxy
      have h2 : ‖u x - u y‖ / ‖x - y‖ ^ α ≤ C :=
        (ENNReal.ofReal_le_ofReal_iff hC).mp (le_trans h1 hB)
      calc ‖u x - u y‖ = (‖u x - u y‖ / ‖x - y‖ ^ α) * ‖x - y‖ ^ α := by
            rw [div_mul_cancel₀]
            exact (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α).ne'
        _ ≤ C * ‖x - y‖ ^ α :=
            mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (norm_nonneg _) α)
  · intro z hz
    have h1 : ENNReal.ofReal ‖iteratedFDerivWithin ℝ 1 u P z‖ ≤ iterDerivNorm 1 u P :=
      le_iterDerivNorm 1 u P hz
    have h2 : ‖iteratedFDerivWithin ℝ 1 u P z‖ ≤ C :=
      (ENNReal.ofReal_le_ofReal_iff hC).mp (le_trans h1 hC')
    rwa [norm_iteratedFDerivWithin_one u (hPopen.uniqueDiffWithinAt hz),
      fderivWithin_of_isOpen hPopen hz] at h2
  · intro x hx y hy
    rcases eq_or_ne x y with rfl | hxy
    · rw [sub_self, norm_zero]
      exact mul_nonneg hC (Real.rpow_nonneg (norm_nonneg _) _)
    · have h1 : ENNReal.ofReal
          (‖iteratedFDerivWithin ℝ 1 u P x - iteratedFDerivWithin ℝ 1 u P y‖ / ‖x - y‖ ^ α)
          ≤ holderSeminorm 1 α u P := le_holderSeminorm 1 α u P hx hy hxy
      have h2 : ‖iteratedFDerivWithin ℝ 1 u P x - iteratedFDerivWithin ℝ 1 u P y‖
          / ‖x - y‖ ^ α ≤ C := (ENNReal.ofReal_le_ofReal_iff hC).mp (le_trans h1 hD)
      have h3 : ‖iteratedFDerivWithin ℝ 1 u P x - iteratedFDerivWithin ℝ 1 u P y‖
          ≤ C * ‖x - y‖ ^ α := by
        calc ‖iteratedFDerivWithin ℝ 1 u P x - iteratedFDerivWithin ℝ 1 u P y‖
            = (‖iteratedFDerivWithin ℝ 1 u P x - iteratedFDerivWithin ℝ 1 u P y‖
                / ‖x - y‖ ^ α) * ‖x - y‖ ^ α := by
              rw [div_mul_cancel₀]
              exact (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α).ne'
          _ ≤ C * ‖x - y‖ ^ α :=
              mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (norm_nonneg _) α)
      rw [← fderivWithin_of_isOpen hPopen hx, ← fderivWithin_of_isOpen hPopen hy]
      exact (norm_fderivWithin_sub_le_iteratedFDerivWithin_one u P x y
        (hPopen.uniqueDiffWithinAt hx) (hPopen.uniqueDiffWithinAt hy)).trans h3


/-! ## Geometry of the polydiscs -/

/-- If every coordinate of `y` is within `r i` of `c i`, then `‖y‖ ≤ Σ r + ‖c‖`. -/
lemma norm_le_sum_add_norm_of_forall_lt {n : ℕ} {c : Fin n → ℂ} {r : Fin n → ℝ}
    (hr : ∀ j, 0 < r j) {y : Fin n → ℂ} (h : ∀ i, ‖y i - c i‖ < r i) :
    ‖y‖ ≤ (∑ j, r j) + ‖c‖ := by
  rw [pi_norm_le_iff_of_nonneg
    (add_nonneg (Finset.sum_nonneg fun j _ => (hr j).le) (norm_nonneg c))]
  intro i
  have hi := h i
  have h1 : ‖y i‖ ≤ ‖y i - c i‖ + ‖c i‖ := by
    simpa using norm_add_le (y i - c i) (c i)
  have h2 : ‖c i‖ ≤ ‖c‖ := norm_le_pi_norm c i
  have h3 : r i ≤ ∑ j, r j := Finset.single_le_sum (fun j _ => (hr j).le) (Finset.mem_univ i)
  linarith

/-- A point outside the sup-norm ball of radius `Σ r + ‖c‖ + 1` is outside the polydisc of
radii `r`. -/
lemma exists_coord_le_of_le_norm {n : ℕ} {c : Fin n → ℂ} {r : Fin n → ℝ} (hr : ∀ j, 0 < r j)
    {x : Fin n → ℂ} (hx : (∑ j, r j) + ‖c‖ + 1 ≤ ‖x‖) : ∃ i, r i ≤ ‖x i - c i‖ := by
  by_contra hcon
  push_neg at hcon
  have := norm_le_sum_add_norm_of_forall_lt hr hcon
  linarith

/-- If `z` lies in the half-size polydisc and `x` is far away in the Euclidean norm then `z + x`
is outside the polydisc of radii `r`. -/
lemma shift_exists_coord_le {n : ℕ} {c : Fin n → ℂ} {r : Fin n → ℝ} (hn : 0 < n)
    (hr : ∀ j, 0 < r j) {z x : Fin n → ℂ} (hz : z ∈ polydisc c (fun j => r j / 2))
    (hx : 2 * Real.sqrt n * ((∑ j, r j) + ‖c‖ + 1) ≤ eucNorm x) :
    ∃ i, r i ≤ ‖(z + x) i - c i‖ := by
  by_contra hcon
  push_neg at hcon
  have hupper : ‖z + x‖ ≤ (∑ j, r j) + ‖c‖ := norm_le_sum_add_norm_of_forall_lt hr hcon
  have hsqrtpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hznorm : ‖z‖ ≤ (∑ j, r j) + ‖c‖ := by
    refine norm_le_sum_add_norm_of_forall_lt hr fun i => ?_
    have h1 := hz i
    linarith [hr i]
  have hzx : eucNorm (z + x) ≤ Real.sqrt n * ‖z + x‖ := bmCz.eucNorm_le_sqrt_mul_norm (z + x)
  have hsplit : eucNorm x ≤ eucNorm (z + x) + eucNorm z := by
    have h := eucNorm_sub_le' (z + x) z
    rwa [show (z + x) - z = x from by abel] at h
  have hzE : eucNorm z ≤ Real.sqrt n * ((∑ j, r j) + ‖c‖) :=
    (bmCz.eucNorm_le_sqrt_mul_norm z).trans
      (mul_le_mul_of_nonneg_left hznorm (Real.sqrt_nonneg n))
  have hlow : (∑ j, r j) + ‖c‖ + 2 ≤ ‖z + x‖ := by
    have h1 : 2 * Real.sqrt n * ((∑ j, r j) + ‖c‖ + 1)
        ≤ eucNorm (z + x) + Real.sqrt n * ((∑ j, r j) + ‖c‖) :=
      hx.trans (hsplit.trans (add_le_add le_rfl hzE))
    have h2 : Real.sqrt n * ((∑ j, r j) + ‖c‖ + 2) ≤ eucNorm (z + x) := by
      nlinarith [h1]
    calc (∑ j, r j) + ‖c‖ + 2
        = (Real.sqrt n * ((∑ j, r j) + ‖c‖ + 2)) / Real.sqrt n := by
          rw [mul_div_cancel_left₀ _ hsqrtpos.ne']
      _ ≤ eucNorm (z + x) / Real.sqrt n := div_le_div_of_nonneg_right h2 hsqrtpos.le
      _ ≤ ‖z + x‖ := by
          rw [div_le_iff₀ hsqrtpos]
          simpa [mul_comm] using hzx
  linarith


/-! ## The `C^{1,α}` Taylor estimate -/

/-- `x ^ (1 + α) = x ^ α * x` for `x ≥ 0`, `α > 0`. -/
lemma rpow_one_add_mul {α : ℝ} (hα : 0 < α) {x : ℝ} (hx : 0 ≤ x) :
    x ^ (1 + α) = x ^ α * x := by
  rcases eq_or_lt_of_le hx with h0 | hpos
  · rw [← h0, Real.zero_rpow (by linarith : (1 : ℝ) + α ≠ 0),
      Real.zero_rpow (ne_of_gt hα), zero_mul]
  · rw [Real.rpow_add hpos, Real.rpow_one, mul_comm]

/-- If the derivative of `f` is `α`-Hölder on the convex set `s`, then `f` is `C^{1,α}` on `s`:
`‖f y - f x - fderiv f x (y - x)‖ ≤ C ‖y - x‖ ^ (1 + α)`. -/
lemma holder_fderiv_taylor' {n : ℕ} {f : (Fin n → ℂ) → ℂ} {s : Set (Fin n → ℂ)}
    {C α : ℝ} (hα : 0 < α) (hC : 0 ≤ C) (hf : ∀ x, DifferentiableAt ℝ f x) (hs : Convex ℝ s)
    (hH : ∀ x ∈ s, ∀ y ∈ s, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ C * ‖x - y‖ ^ α)
    {x y : Fin n → ℂ} (hx : x ∈ s) (hy : y ∈ s) :
    ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ C * ‖y - x‖ ^ (1 + α) := by
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun t : ℝ => f (x + t • (y - x)) - t • (fderiv ℝ f x (y - x)))
        ((fderiv ℝ f (x + t • (y - x)) - fderiv ℝ f x) (y - x)) (Set.Icc (0 : ℝ) 1) t := by
    intro t _
    have hcurve : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) t := by
      simpa using ((hasDerivAt_id t).smul_const (y - x)).const_add x
    have h1 : HasDerivAt (fun t : ℝ => f (x + t • (y - x)))
        ((fderiv ℝ f (x + t • (y - x))) (y - x)) t :=
      ((hf (x + t • (y - x))).hasFDerivAt).comp_hasDerivAt t hcurve
    have h2 : HasDerivAt (fun t : ℝ => t • (fderiv ℝ f x (y - x))) (fderiv ℝ f x (y - x)) t := by
      simpa using (hasDerivAt_id t).smul_const (fderiv ℝ f x (y - x))
    have h3 : HasDerivAt (fun t : ℝ => f (x + t • (y - x)) - t • (fderiv ℝ f x (y - x)))
        ((fderiv ℝ f (x + t • (y - x))) (y - x) - (fderiv ℝ f x) (y - x)) t := h1.sub h2
    rw [sub_apply]
    exact h3.hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ‖((fderiv ℝ f (x + t • (y - x)) - fderiv ℝ f x) (y - x))‖
        ≤ C * ‖y - x‖ ^ (1 + α) := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := le_of_lt ht.2
    have hmem : x + t • (y - x) ∈ s := by
      have h1 : (1 - t) • x + t • y ∈ s := (hs hx) hy (by linarith) ht0 (by ring)
      have h2 : x + t • (y - x) = (1 - t) • x + t • y := by module
      rwa [h2]
    have hHt := hH (x + t • (y - x)) hmem x hx
    rw [show (x + t • (y - x)) - x = t • (y - x) from by abel,
      show ‖t • (y - x)‖ = t * ‖y - x‖ from by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]] at hHt
    calc ‖((fderiv ℝ f (x + t • (y - x)) - fderiv ℝ f x) (y - x))‖
        ≤ ‖fderiv ℝ f (x + t • (y - x)) - fderiv ℝ f x‖ * ‖y - x‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (C * (t * ‖y - x‖) ^ α) * ‖y - x‖ :=
          mul_le_mul_of_nonneg_right hHt (norm_nonneg _)
      _ ≤ (C * ‖y - x‖ ^ α) * ‖y - x‖ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hC) (norm_nonneg _)
          rw [Real.mul_rpow ht0 (norm_nonneg _)]
          exact mul_le_of_le_one_left (Real.rpow_nonneg (norm_nonneg _) _)
            (Real.rpow_le_one ht0 ht1 hα.le)
      _ = C * ‖y - x‖ ^ (1 + α) := by
          rw [rpow_one_add_mul hα (norm_nonneg _)]; ring
  have hseg := norm_image_sub_le_of_norm_deriv_le_segment' (a := (0 : ℝ)) (b := 1)
    (f := fun t : ℝ => f (x + t • (y - x)) - t • (fderiv ℝ f x (y - x))) hderiv hbound 1
    (by norm_num)
  rw [show x + (1 : ℝ) • (y - x) = y from by rw [one_smul]; abel,
    show x + (0 : ℝ) • (y - x) = x from by rw [zero_smul, add_zero],
    show (1 : ℝ) • (fderiv ℝ f x (y - x)) = fderiv ℝ f x (y - x) from by rw [one_smul],
    show (0 : ℝ) • (fderiv ℝ f x (y - x)) = 0 from by rw [zero_smul],
    sub_zero, sub_zero, mul_one] at hseg
  convert hseg using 2
  abel


/-! ## The main theorem -/

theorem bmPot_holder_C0a {n : ℕ} (hn : 0 < n) {c : Fin n → ℂ} {r : Fin n → ℝ}
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (hr : ∀ j, 0 < r j) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : Fin n → (Fin n → ℂ) → ℂ,
      (∀ j z, (∃ i, r i / 2 ≤ ‖z i - c i‖) → g j z = 0) →
      (∀ j, Work.CR.Flat.holderNorm 0 α (g j) Set.univ ≠ ⊤) →
      Work.CR.Flat.holderNorm 1 α (fun z => Work.CR.Flat.Cauchy.bmPot g z)
        (Work.CR.Flat.polydisc c (fun j => r j / 2))
        ≤ ENNReal.ofReal C * ∑ j, Work.CR.Flat.holderNorm 0 α (g j) Set.univ := by
  classical
  obtain ⟨C₁, hC₁pos, hC₁⟩ := bmPotential_holder hn (c := c) (r := fun j => 2 * r j) hα hα1
    (fun j => by linarith [hr j])
  obtain ⟨cc, hcc⟩ := bmCz.integral_bmKernel_mul_dbarCoord hn
  set Rb : ℝ := 2 * Real.sqrt n * ((∑ j, r j) + ‖c‖ + 1) with hRbdef
  have hRbpos : 0 < Rb := by
    rw [hRbdef]
    have h1 : 0 < ∑ j, r j := Finset.sum_pos (fun j _ => hr j) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    have h2 : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    have h3 : 0 ≤ ‖c‖ := norm_nonneg c
    positivity
  refine ⟨4 * C₁, by linarith, ?_⟩
  intro g hgsupp hgfin
  -- ### the constants attached to the data
  set A' : Fin n → ℝ := fun j => (Work.CR.Flat.iterDerivNorm 0 (g j) Set.univ).toReal with hA'def
  set K' : Fin n → ℝ := fun j => (Work.CR.Flat.holderSeminorm 0 α (g j) Set.univ).toReal with hK'def
  have hA'0 : ∀ j, 0 ≤ A' j := fun j => ENNReal.toReal_nonneg
  have hK'0 : ∀ j, 0 ≤ K' j := fun j => ENNReal.toReal_nonneg
  have hA'lt : ∀ j, Work.CR.Flat.iterDerivNorm 0 (g j) Set.univ ≠ ⊤ := fun j =>
    lt_top_iff_ne_top.mp (lt_of_le_of_lt
      (Work.CR.Flat.iterDerivNorm_le_holderNorm 0 α (g j) Set.univ (Nat.zero_le 0))
      (lt_top_iff_ne_top.mpr (hgfin j)))
  have hK'lt : ∀ j, Work.CR.Flat.holderSeminorm 0 α (g j) Set.univ ≠ ⊤ := fun j =>
    lt_top_iff_ne_top.mp (lt_of_le_of_lt
      (Work.CR.Flat.holderSeminorm_le_holderNorm 0 α (g j) Set.univ (Nat.zero_le 0))
      (lt_top_iff_ne_top.mpr (hgfin j)))
  have hA'eq : ∀ j, ENNReal.ofReal (A' j) = Work.CR.Flat.iterDerivNorm 0 (g j) Set.univ :=
    fun j => ENNReal.ofReal_toReal (hA'lt j)
  have hK'eq : ∀ j, ENNReal.ofReal (K' j) = Work.CR.Flat.holderSeminorm 0 α (g j) Set.univ :=
    fun j => ENNReal.ofReal_toReal (hK'lt j)
  have hgA : ∀ j x, ‖g j x‖ ≤ A' j := by
    intro j x
    have h1 : ENNReal.ofReal ‖g j x‖ ≤ Work.CR.Flat.iterDerivNorm 0 (g j) Set.univ := by
      rw [← norm_iteratedFDerivWithin_zero (𝕜 := ℝ) (f := g j) (s := Set.univ) (x := x)]
      exact Work.CR.Flat.le_iterDerivNorm 0 (g j) Set.univ (Set.mem_univ x)
    rw [← hA'eq j] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (hA'0 j)).mp h1
  have hgK : ∀ j x y, ‖g j x - g j y‖ ≤ K' j * ‖x - y‖ ^ α := by
    intro j x y
    rcases eq_or_ne x y with rfl | hxy
    · simp [Real.zero_rpow (ne_of_gt hα)]
    · have h1 : ENNReal.ofReal (‖g j x - g j y‖ / ‖x - y‖ ^ α)
          ≤ Work.CR.Flat.holderSeminorm 0 α (g j) Set.univ := by
        simpa [Work.NN.Core.norm_iteratedFDerivWithin_zero_sub (g j) Set.univ x y] using
          Work.CR.Flat.le_holderSeminorm 0 α (g j) Set.univ (Set.mem_univ x) (Set.mem_univ y) hxy
      rw [← hK'eq j] at h1
      have h2 : ‖g j x - g j y‖ / ‖x - y‖ ^ α ≤ K' j :=
        (ENNReal.ofReal_le_ofReal_iff (hK'0 j)).mp h1
      calc ‖g j x - g j y‖ = (‖g j x - g j y‖ / ‖x - y‖ ^ α) * ‖x - y‖ ^ α := by
            rw [div_mul_cancel₀]
            exact (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α).ne'
        _ ≤ K' j * ‖x - y‖ ^ α :=
            mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (norm_nonneg _) α)
  set S : ℝ := ∑ j, (A' j + K' j) with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => add_nonneg (hA'0 j) (hK'0 j)
  have h0j : ∀ j, Work.CR.Flat.holderNorm 0 α (g j) Set.univ = ENNReal.ofReal (A' j + K' j) := by
    intro j
    rw [Work.NN.Core.holderNorm_zero_eq, ← hA'eq j, ← hK'eq j,
      ENNReal.ofReal_add (hA'0 j) (hK'0 j)]
  have hA'leS : ∀ j, A' j ≤ S := by
    intro j
    calc A' j ≤ A' j + K' j := le_add_of_nonneg_right (hK'0 j)
      _ ≤ S := Finset.single_le_sum (f := fun j => A' j + K' j)
          (fun j _ => add_nonneg (hA'0 j) (hK'0 j)) (Finset.mem_univ j)
  have hAgS : ∀ j x, ‖g j x‖ ≤ S := fun j x => (hgA j x).trans (hA'leS j)
  have hsum_g : (∑ j, Work.CR.Flat.holderNorm 0 α (g j) Set.univ) = ENNReal.ofReal S :=
    (Finset.sum_congr rfl fun j _ => h0j j).trans (by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => add_nonneg (hA'0 j) (hK'0 j)), ← hSdef])
  -- ### the smooth approximations
  have hst : ∀ j, r j / 2 < r j := fun j => by linarith [hr j]
  choose G hGsmooth hGbound hHolder hGsupp hGconv using fun j =>
    bmSmoothApprox (c := c) (s := fun j => r j / 2) (r := r) hα (hK'0 j) hst (hgA j) (hgK j)
      (hgsupp j)
  have hGsmooth1 : ∀ j m, ContDiff ℝ 1 (G j m) := fun j m => (hGsmooth j m).of_le (by norm_num)
  have hGgS : ∀ j m x, ‖G j m x‖ ≤ S := fun j m x => (hGbound j m x).trans (hA'leS j)
  -- ### the `C^{1,α}` bound for each approximation
  have hbound : ∀ m, Work.CR.Flat.holderNorm 1 α (bmPotential (fun j => G j m))
      (polydisc c (fun j => r j / 2)) ≤ ENNReal.ofReal (C₁ * S) := by
    intro m
    have hsupp2 : ∀ j z, (∃ k, (2 * r k) / 2 ≤ ‖z k - c k‖) → G j m z = 0 := by
      intro j z hz
      obtain ⟨k, hk⟩ := hz
      exact hGsupp j m z ⟨k, by rw [show 2 * r k / 2 = r k from by ring] at hk; exact hk⟩
    have hmain := hC₁ (fun j => G j m) (fun j => hGsmooth1 j m) hsupp2
    have hle_j : ∀ j, Work.CR.Flat.holderNorm 0 α (G j m) Set.univ
        ≤ ENNReal.ofReal (A' j + K' j) := by
      intro j
      have h1 : Work.CR.Flat.iterDerivNorm 0 (G j m) Set.univ ≤ ENNReal.ofReal (A' j) := by
        rw [Work.CR.Flat.iterDerivNorm_zero]
        exact iSup₂_le fun z _ => ENNReal.ofReal_le_ofReal (hGbound j m z)
      have h2 : Work.CR.Flat.holderSeminorm 0 α (G j m) Set.univ ≤ ENNReal.ofReal (K' j) := by
        rw [Work.CR.Flat.holderSeminorm]
        refine iSup₂_le fun x _ => iSup₂_le fun y _ => iSup_le fun hxy => ?_
        rw [Work.NN.Core.norm_iteratedFDerivWithin_zero_sub (G j m) Set.univ x y]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_le_iff₀ (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α)]
        exact hHolder j m x y
      calc Work.CR.Flat.holderNorm 0 α (G j m) Set.univ
          = Work.CR.Flat.iterDerivNorm 0 (G j m) Set.univ
            + Work.CR.Flat.holderSeminorm 0 α (G j m) Set.univ :=
            Work.NN.Core.holderNorm_zero_eq α (G j m) Set.univ
        _ ≤ ENNReal.ofReal (A' j) + ENNReal.ofReal (K' j) := add_le_add h1 h2
        _ = ENNReal.ofReal (A' j + K' j) :=
            (ENNReal.ofReal_add (hA'0 j) (hK'0 j)).symm
    have hsum_eq : (∑ j, ENNReal.ofReal (A' j + K' j)) = ENNReal.ofReal S := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => add_nonneg (hA'0 j) (hK'0 j)), ← hSdef]
    have hSbound : (∑ j, Work.CR.Flat.holderNorm 0 α (G j m) Set.univ) ≤ ENNReal.ofReal S :=
      (Finset.sum_le_sum fun j _ => hle_j j).trans (le_of_eq hsum_eq)
    have hPsub : polydisc c (fun j => r j / 2) ⊆ polydisc c r :=
      polydisc_mono fun j => by linarith [hr j]
    have hmono := Work.CR.Flat.holderNorm_mono_set (isOpen_polydisc c _) (isOpen_polydisc c _)
      hPsub 1 α (bmPotential (fun j => G j m))
    calc Work.CR.Flat.holderNorm 1 α (bmPotential (fun j => G j m))
          (polydisc c (fun j => r j / 2))
        ≤ Work.CR.Flat.holderNorm 1 α (bmPotential (fun j => G j m)) (polydisc c r) := hmono
      _ = Work.CR.Flat.holderNorm 1 α (bmPotential (fun j => G j m))
            (polydisc c (fun j => 2 * r j / 2)) := by
          congr 1
          funext j
          ring
      _ ≤ ENNReal.ofReal C₁ * ∑ j, Work.CR.Flat.holderNorm 0 α (G j m) Set.univ := hmain
      _ ≤ ENNReal.ofReal C₁ * ENNReal.ofReal S := mul_le_mul_right hSbound _
      _ = ENNReal.ofReal (C₁ * S) := (ENNReal.ofReal_mul hC₁pos.le).symm
  have hL5 : ∀ m, (∀ z ∈ polydisc c (fun j => r j / 2),
        ‖bmPotential (fun j => G j m) z‖ ≤ C₁ * S) ∧
      (∀ x ∈ polydisc c (fun j => r j / 2), ∀ y ∈ polydisc c (fun j => r j / 2),
        ‖bmPotential (fun j => G j m) x - bmPotential (fun j => G j m) y‖
          ≤ C₁ * S * ‖x - y‖ ^ α) ∧
      (∀ z ∈ polydisc c (fun j => r j / 2),
        ‖fderiv ℝ (bmPotential (fun j => G j m)) z‖ ≤ C₁ * S) ∧
      (∀ x ∈ polydisc c (fun j => r j / 2), ∀ y ∈ polydisc c (fun j => r j / 2),
        ‖fderiv ℝ (bmPotential (fun j => G j m)) x
          - fderiv ℝ (bmPotential (fun j => G j m)) y‖ ≤ C₁ * S * ‖x - y‖ ^ α) :=
    fun m => holderNorm_one_bounds (isOpen_polydisc c _) (mul_nonneg hC₁pos.le hS0) (hbound m)
  -- ### the limits
  have hU : ∀ z, Tendsto (fun m => bmPotential (fun j => G j m) z) atTop
      (nhds (bmPotential g z)) :=
    bmPotential_tendsto_of_tendsto hn hr hS0 (fun m j => (hGsmooth j m).continuous)
      (fun j => continuous_of_holder_bound hα (hK'0 j) (hgK j))
      (fun m j z => hGgS j m z) (fun j z => hAgS j z) (fun m j z hz => hGsupp j m z hz)
      (fun j z hz => hgsupp j z (by obtain ⟨i, hi⟩ := hz; exact ⟨i, by linarith [hr i]⟩))
      (fun j z => hGconv j z)
  have hfsmooth : ∀ m (z : Fin n → ℂ), z ∈ polydisc c (fun j => r j / 2) →
      fderiv ℝ (bmPotential (fun j => G j m)) z = bmDerivData Rb cc (fun j => G j m) z := by
    intro m z hz
    have hbm : bmPotential (fun j => G j m) = fun w => bmPot (fun j => G j m) w :=
      funext fun w => bmPotential_eq_bmPot _ w
    rw [hbm]
    refine fderiv_bmPot_eq_bmDerivData hn hcc (fun j => hGsmooth1 j m) hRbpos
      (fun k x hx => ?_) (fun k x hx => ?_)
    · rw [hRbdef] at hx
      refine hGsupp k m x (exists_coord_le_of_le_norm hr ?_)
      calc (∑ j, r j) + ‖c‖ + 1 = 1 * ((∑ j, r j) + ‖c‖ + 1) := by ring
        _ ≤ 2 * Real.sqrt n * ((∑ j, r j) + ‖c‖ + 1) := by
            refine mul_le_mul_of_nonneg_right ?_ ?_
            · have h1 : (1 : ℝ) ≤ Real.sqrt n :=
                Real.one_le_sqrt.mpr (by exact_mod_cast Nat.succ_le_iff.mpr hn)
              linarith
            · have h1 : 0 < ∑ j, r j :=
                Finset.sum_pos (fun j _ => hr j) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
              have h2 : 0 ≤ ‖c‖ := norm_nonneg c
              linarith
        _ ≤ ‖x‖ := hx
    · rw [hRbdef] at hx
      exact hGsupp k m (z + x) (shift_exists_coord_le hn hr hz hx)
  have hDeriv : ∀ z ∈ polydisc c (fun j => r j / 2), ∀ v : Fin n → ℂ,
      Tendsto (fun m => fderiv ℝ (bmPotential (fun j => G j m)) z v) atTop
        (nhds (bmDerivData Rb cc g z v)) := by
    intro z hz v
    have hconv' := tendsto_bmDerivData_apply hn hRbpos cc hα hK'0
      (fun m j x y => hHolder j m x y) hgK hGconv z v
    refine hconv'.congr' (Filter.Eventually.of_forall fun m => ?_)
    exact congrArg (fun L => L v) (hfsmooth m z hz).symm
  have hTay : ∀ᶠ m in atTop, ∀ z ∈ polydisc c (fun j => r j / 2), ∀ h,
      z + h ∈ polydisc c (fun j => r j / 2) →
      ‖bmPotential (fun j => G j m) (z + h) - bmPotential (fun j => G j m) z
        - fderiv ℝ (bmPotential (fun j => G j m)) z h‖ ≤ C₁ * S * ‖h‖ ^ (1 + α) := by
    filter_upwards with m
    intro z hz h hzh
    have hdiff : ∀ x, DifferentiableAt ℝ (bmPotential (fun j => G j m)) x := fun x =>
      ((bmPotential_contDiff_one (c := c) (r := fun j => 2 * r j) hn
        (fun j => by linarith [hr j]) (fun j => hGsmooth1 j m)
        (fun j z hz' => by
          obtain ⟨k, hk⟩ := hz'
          exact hGsupp j m z ⟨k, by rw [show 2 * r k / 2 = r k from by ring] at hk; exact hk⟩)
        ).differentiable (by norm_num)).differentiableAt
    have hres := holder_fderiv_taylor' hα (mul_nonneg hC₁pos.le hS0) hdiff (convex_polydisc c _)
      (fun x hx y hy => (hL5 m).2.2.2 x hx y hy) hz hzh
    simpa using hres
  have hHasFDeriv : ∀ z ∈ polydisc c (fun j => r j / 2),
      HasFDerivAt (bmPotential g) (bmDerivData Rb cc g z) z := by
    intro z hz
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    refine Asymptotics.IsLittleO.of_bound fun ε hε => ?_
    have hseg : ∀ᶠ h in nhds (0 : Fin n → ℂ), z + h ∈ polydisc c (fun j => r j / 2) := by
      have hmem : polydisc c (fun j => r j / 2) ∈ nhds z :=
        (isOpen_polydisc c (fun j => r j / 2)).mem_nhds hz
      have hz' : Tendsto (fun h : Fin n → ℂ => z + h) (nhds 0) (nhds z) := by
        simpa using (tendsto_const_nhds.add
          (tendsto_id : Tendsto (fun h : Fin n → ℂ => h) (nhds 0) (nhds 0)))
      exact hz'.eventually hmem
    have hcont : Tendsto (fun h : Fin n → ℂ => C₁ * S * ‖h‖ ^ α) (nhds 0) (nhds 0) := by
      have h1 : Tendsto (fun h : Fin n → ℂ => ‖h‖) (nhds 0) (nhds 0) := by
        simpa using (continuous_norm.tendsto (0 : Fin n → ℂ))
      have h2 : Tendsto (fun h : Fin n → ℂ => ‖h‖ ^ α) (nhds 0) (nhds (0 ^ α)) :=
        (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto.comp h1
      rw [Real.zero_rpow (ne_of_gt hα)] at h2
      simpa using h2.const_mul (C₁ * S)
    have hev : ∀ᶠ h in nhds (0 : Fin n → ℂ), C₁ * S * ‖h‖ ^ α < ε :=
      (tendsto_order.1 hcont).2 ε hε
    filter_upwards [hseg, hev] with h hzh hlt
    have hlim : Tendsto (fun m => bmPotential (fun j => G j m) (z + h)
        - bmPotential (fun j => G j m) z - fderiv ℝ (bmPotential (fun j => G j m)) z h)
        atTop (nhds (bmPotential g (z + h) - bmPotential g z - bmDerivData Rb cc g z h)) :=
      ((hU (z + h)).sub (hU z)).sub (hDeriv z hz h)
    have hbl := le_of_tendsto hlim.norm (hTay.mono fun m hm => hm z hz h hzh)
    calc ‖bmPotential g (z + h) - bmPotential g z - bmDerivData Rb cc g z h‖
        ≤ C₁ * S * ‖h‖ ^ (1 + α) := hbl
      _ = (C₁ * S * ‖h‖ ^ α) * ‖h‖ := by rw [rpow_one_add_mul hα (norm_nonneg h)]; ring
      _ ≤ ε * ‖h‖ := mul_le_mul_of_nonneg_right hlt.le (norm_nonneg h)
  have hfderiv_eq : ∀ z ∈ polydisc c (fun j => r j / 2),
      fderiv ℝ (bmPotential g) z = bmDerivData Rb cc g z :=
    fun z hz => (hHasFDeriv z hz).fderiv
  -- ### the four pieces of the `C^{1,α}` norm
  have hE1 : Work.CR.Flat.iterDerivNorm 0 (bmPotential g) (polydisc c (fun j => r j / 2))
      ≤ ENNReal.ofReal (C₁ * S) := by
    rw [Work.CR.Flat.iterDerivNorm_zero]
    refine iSup₂_le fun z hz => ?_
    exact ENNReal.ofReal_le_ofReal (le_of_tendsto (hU z).norm
      (Filter.Eventually.of_forall fun m => (hL5 m).1 z hz))
  have hE2 : Work.CR.Flat.holderSeminorm 0 α (bmPotential g) (polydisc c (fun j => r j / 2))
      ≤ ENNReal.ofReal (C₁ * S) := by
    rw [Work.CR.Flat.holderSeminorm]
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    rw [Work.NN.Core.norm_iteratedFDerivWithin_zero_sub (bmPotential g)
      (polydisc c (fun j => r j / 2)) x y]
    refine ENNReal.ofReal_le_ofReal ?_
    have hb := le_of_tendsto ((hU x).sub (hU y)).norm
      (Filter.Eventually.of_forall fun m => (hL5 m).2.1 x hx y hy)
    calc ‖bmPotential g x - bmPotential g y‖ / ‖x - y‖ ^ α
        ≤ (C₁ * S * ‖x - y‖ ^ α) / ‖x - y‖ ^ α :=
          div_le_div_of_nonneg_right hb (Real.rpow_nonneg (norm_nonneg _) α)
      _ = C₁ * S := by
          rw [mul_div_cancel_right₀ _ (Real.rpow_pos_of_pos
            (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α).ne']
  have hE3 : Work.CR.Flat.iterDerivNorm 1 (bmPotential g) (polydisc c (fun j => r j / 2))
      ≤ ENNReal.ofReal (C₁ * S) := by
    rw [Work.CR.Flat.iterDerivNorm]
    refine iSup₂_le fun z hz => ?_
    rw [norm_iteratedFDerivWithin_one (bmPotential g) ((isOpen_polydisc c _).uniqueDiffWithinAt hz),
      fderivWithin_of_isOpen (isOpen_polydisc c _) hz, hfderiv_eq z hz]
    refine ENNReal.ofReal_le_ofReal ?_
    refine ContinuousLinearMap.opNorm_le_bound (bmDerivData Rb cc g z) (by positivity) fun v => ?_
    have hev : ∀ᶠ m in atTop, ‖bmDerivData Rb cc (fun j => G j m) z v‖ ≤ (C₁ * S) * ‖v‖ := by
      filter_upwards with m
      rw [← hfsmooth m z hz]
      exact le_trans (ContinuousLinearMap.le_opNorm _ v)
        (mul_le_mul_of_nonneg_right ((hL5 m).2.2.1 z hz) (norm_nonneg v))
    exact le_of_tendsto (tendsto_bmDerivData_apply hn hRbpos cc hα hK'0
      (fun m j x y => hHolder j m x y) hgK hGconv z v).norm hev
  have hE4 : Work.CR.Flat.holderSeminorm 1 α (bmPotential g) (polydisc c (fun j => r j / 2))
      ≤ ENNReal.ofReal (C₁ * S) := by
    rw [Work.CR.Flat.holderSeminorm]
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    have hx' : UniqueDiffWithinAt ℝ (polydisc c (fun j => r j / 2)) x :=
      (isOpen_polydisc c (fun j => r j / 2)).uniqueDiffWithinAt hx
    have hy' : UniqueDiffWithinAt ℝ (polydisc c (fun j => r j / 2)) y :=
      (isOpen_polydisc c (fun j => r j / 2)).uniqueDiffWithinAt hy
    have heq : ‖iteratedFDerivWithin ℝ 1 (bmPotential g) (polydisc c (fun j => r j / 2)) x
          - iteratedFDerivWithin ℝ 1 (bmPotential g) (polydisc c (fun j => r j / 2)) y‖
        = ‖fderiv ℝ (bmPotential g) x - fderiv ℝ (bmPotential g) y‖ := by
      rw [le_antisymm
        (Work.NN.Core.iteratedFDerivWithin_one_sub_le (bmPotential g) _ x y hx' hy')
        (norm_fderivWithin_sub_le_iteratedFDerivWithin_one (bmPotential g) _ x y hx' hy'),
        fderivWithin_of_isOpen (isOpen_polydisc c _) hx,
        fderivWithin_of_isOpen (isOpen_polydisc c _) hy]
    rw [heq, hfderiv_eq x hx, hfderiv_eq y hy]
    refine ENNReal.ofReal_le_ofReal ?_
    refine (div_le_iff₀ (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α)).mpr ?_
    refine ContinuousLinearMap.opNorm_le_bound (bmDerivData Rb cc g x - bmDerivData Rb cc g y)
      (by positivity) fun v => ?_
    have hev : ∀ᶠ m in atTop,
        ‖(fderiv ℝ (bmPotential (fun j => G j m)) x
          - fderiv ℝ (bmPotential (fun j => G j m)) y) v‖ ≤ (C₁ * S * ‖x - y‖ ^ α) * ‖v‖ := by
      filter_upwards with m
      exact le_trans (ContinuousLinearMap.le_opNorm _ v)
        (mul_le_mul_of_nonneg_right ((hL5 m).2.2.2 x hx y hy) (norm_nonneg v))
    have hlim : Tendsto (fun m => (fderiv ℝ (bmPotential (fun j => G j m)) x
        - fderiv ℝ (bmPotential (fun j => G j m)) y) v) atTop
        (nhds ((bmDerivData Rb cc g x - bmDerivData Rb cc g y) v)) := by
      have h := (hDeriv x hx v).sub (hDeriv y hy v)
      simpa only [sub_apply] using h
    exact le_of_tendsto hlim.norm hev
  -- ### assembly
  have hfun : (fun z => bmPot g z) = bmPotential g :=
    funext fun z => (bmPotential_eq_bmPot g z).symm
  rw [hfun, Work.NN.Core.holderNorm_one_eq]
  have hC1S : (0 : ℝ) ≤ C₁ * S := mul_nonneg hC₁pos.le hS0
  calc (Work.CR.Flat.iterDerivNorm 0 (bmPotential g) (polydisc c (fun j => r j / 2))
          + Work.CR.Flat.holderSeminorm 0 α (bmPotential g) (polydisc c (fun j => r j / 2)))
        + (Work.CR.Flat.iterDerivNorm 1 (bmPotential g) (polydisc c (fun j => r j / 2))
          + Work.CR.Flat.holderSeminorm 1 α (bmPotential g) (polydisc c (fun j => r j / 2)))
      ≤ (ENNReal.ofReal (C₁ * S) + ENNReal.ofReal (C₁ * S))
        + (ENNReal.ofReal (C₁ * S) + ENNReal.ofReal (C₁ * S)) :=
        add_le_add (add_le_add hE1 hE2) (add_le_add hE3 hE4)
    _ = ENNReal.ofReal (4 * C₁) * ENNReal.ofReal S := by
        rw [← ENNReal.ofReal_add hC1S hC1S,
          ← ENNReal.ofReal_add (add_nonneg hC1S hC1S) (add_nonneg hC1S hC1S),
          ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) hC₁pos.le)]
        congr 1
        ring
    _ = ENNReal.ofReal (4 * C₁) * ∑ j, Work.CR.Flat.holderNorm 0 α (g j) Set.univ := by
        rw [hsum_g]

end Work.NN.Core
