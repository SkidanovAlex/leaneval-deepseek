import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmDefs
import Submission.Work.CR.Flat.Cauchy.bmCZDefs
import Submission.Work.CR.Flat.Cauchy.bmSetup
import Submission.Work.CR.Flat.Cauchy.bmPotential_contDiff_one
import Submission.Work.CR.Flat.Cauchy.bmPot_dbarCoord
import Submission.Work.CR.Flat.Cauchy.bmCz.bmPot_dCoord
import Submission.Work.CR.Flat.Cauchy.bmCz.eucRadialBound
import Submission.Work.CR.Flat.Cauchy.bmCz.czKernel_holderBound
import Submission.Work.CR.Flat.Cauchy.bmCz.bmKernel_decay_le
import Submission.Work.CR.Flat.Cauchy.bmCz.norm_bmDzKernel_sub_le
import Submission.Work.CR.Flat.Cauchy.bmCz.norm_bmDbarKernel_sub_le
import Submission.Work.CR.Flat.Cauchy.bmCz.integral_bmDzKernel_eucShell_eq_zero
import Submission.Work.CR.Flat.Cauchy.bmCz.bmDbarKernel_shell_eq_zero
import Submission.Work.CR.Flat.Cauchy.bmCz.integral_bmKernel_mul_dCoord
import Submission.Work.CR.Flat.Cauchy.bmCz.norm_fderiv_le_sum_wirtinger
import Submission.Work.CR.Flat.Cauchy.bmCz.norm_fderiv_sub_le_sum_wirtinger
import Submission.Work.CR.Flat.Cauchy.bmCz.integral_bmKernel_mul_dbarCoord
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc

noncomputable section

open scoped NNReal ENNReal
open MeasureTheory Set

namespace Work.CR.Flat.Cauchy

/-! ## Lifting pointwise bounds to bounds on the `C^{k,α}` norm -/

private lemma norm_iteratedFDerivWithin_zero_sub_CZ {n : ℕ} (f : (Fin n → ℂ) → ℂ)
    (Ω : Set (Fin n → ℂ)) (x y : Fin n → ℂ) :
    ‖iteratedFDerivWithin ℝ 0 f Ω x - iteratedFDerivWithin ℝ 0 f Ω y‖ = ‖f x - f y‖ := by
  refine le_antisymm ?_ ?_
  · refine ContinuousMultilinearMap.opNorm_le_bound (M := ‖f x - f y‖) (norm_nonneg _) fun m => ?_
    rw [ContinuousMultilinearMap.sub_apply, iteratedFDerivWithin_zero_apply,
      iteratedFDerivWithin_zero_apply]
    rw [show (∏ i : Fin 0, ‖m i‖) = 1 from by simp, mul_one]
  · have h := ContinuousMultilinearMap.le_opNorm
      (iteratedFDerivWithin ℝ 0 f Ω x - iteratedFDerivWithin ℝ 0 f Ω y)
      (fun _ : Fin 0 => (0 : Fin n → ℂ))
    simpa only [ContinuousMultilinearMap.sub_apply, iteratedFDerivWithin_zero_apply,
      Finset.univ_eq_empty, Finset.prod_empty, mul_one] using h

private lemma iterDerivNorm_zero_le_ofReal {n : ℕ} (f : (Fin n → ℂ) → ℂ)
    (Ω : Set (Fin n → ℂ)) {C : ℝ} (h : ∀ x ∈ Ω, ‖f x‖ ≤ C) :
    iterDerivNorm 0 f Ω ≤ ENNReal.ofReal C := by
  refine iSup₂_le fun x hx => ?_
  rw [norm_iteratedFDerivWithin_zero]
  exact ENNReal.ofReal_le_ofReal (h x hx)

private lemma holderSeminorm_zero_le_ofReal {n : ℕ} (f : (Fin n → ℂ) → ℂ)
    (Ω : Set (Fin n → ℂ)) {α C : ℝ}
    (h : ∀ x ∈ Ω, ∀ y ∈ Ω, x ≠ y → ‖f x - f y‖ ≤ C * ‖x - y‖ ^ α) :
    holderSeminorm 0 α f Ω ≤ ENNReal.ofReal C := by
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  rw [norm_iteratedFDerivWithin_zero_sub_CZ]
  have hP : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_iff₀ hP]
  exact h x hx y hy hxy

private lemma norm_iteratedFDeriv_one_eq {n : ℕ} (f : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    ‖iteratedFDeriv ℝ 1 f z‖ = ‖fderiv ℝ f z‖ := by
  refine le_antisymm ?_ ?_
  · refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _) fun m => ?_
    rw [iteratedFDeriv_one_apply, Fin.prod_univ_one]
    exact ContinuousLinearMap.le_opNorm _ _
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
    have h := ContinuousMultilinearMap.le_opNorm (iteratedFDeriv ℝ 1 f z) (fun _ : Fin 1 => v)
    rw [iteratedFDeriv_one_apply, Fin.prod_univ_one] at h
    simpa using h

private lemma norm_iteratedFDeriv_one_sub_eq {n : ℕ} (f : (Fin n → ℂ) → ℂ) (x y : Fin n → ℂ) :
    ‖iteratedFDeriv ℝ 1 f x - iteratedFDeriv ℝ 1 f y‖ = ‖fderiv ℝ f x - fderiv ℝ f y‖ := by
  refine le_antisymm ?_ ?_
  · refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _) fun m => ?_
    rw [ContinuousMultilinearMap.sub_apply, iteratedFDeriv_one_apply, iteratedFDeriv_one_apply,
      ← ContinuousLinearMap.sub_apply, Fin.prod_univ_one]
    exact ContinuousLinearMap.le_opNorm _ _
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
    have h := ContinuousMultilinearMap.le_opNorm
      (iteratedFDeriv ℝ 1 f x - iteratedFDeriv ℝ 1 f y) (fun _ : Fin 1 => v)
    rw [ContinuousMultilinearMap.sub_apply, iteratedFDeriv_one_apply, iteratedFDeriv_one_apply,
      Fin.prod_univ_one] at h
    rw [ContinuousLinearMap.sub_apply]
    exact h

private lemma iterDerivNorm_one_le_ofReal {n : ℕ} (f : (Fin n → ℂ) → ℂ)
    (Ω : Set (Fin n → ℂ)) (hΩ : IsOpen Ω) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ z ∈ Ω, ‖fderiv ℝ f z‖ ≤ C) : iterDerivNorm 1 f Ω ≤ ENNReal.ofReal C := by
  refine iSup₂_le fun z hz => ?_
  rw [(iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := Ω) (f := f) 1 hΩ) hz,
    norm_iteratedFDeriv_one_eq]
  exact ENNReal.ofReal_le_ofReal (h z hz)

private lemma holderSeminorm_one_le_ofReal {n : ℕ} (f : (Fin n → ℂ) → ℂ)
    (Ω : Set (Fin n → ℂ)) (hΩ : IsOpen Ω) {α C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x ∈ Ω, ∀ y ∈ Ω, x ≠ y → ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ C * ‖x - y‖ ^ α) :
    holderSeminorm 1 α f Ω ≤ ENNReal.ofReal C := by
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  rw [(iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := Ω) (f := f) 1 hΩ) hx,
    (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := Ω) (f := f) 1 hΩ) hy,
    norm_iteratedFDeriv_one_sub_eq]
  have hP : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_iff₀ hP]
  exact h x hx y hy hxy

private lemma holderNorm_one_eq_sum {n : ℕ} (α : ℝ) (f : (Fin n → ℂ) → ℂ)
    (Ω : Set (Fin n → ℂ)) :
    holderNorm 1 α f Ω
      = (iterDerivNorm 0 f Ω + holderSeminorm 0 α f Ω)
        + (iterDerivNorm 1 f Ω + holderSeminorm 1 α f Ω) := by
  rw [holderNorm, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

/-! ## Two elementary facts about the kernel and about translates -/

private lemma norm_bmKernel_le_euc {n : ℕ} (j : Fin n) (x : Fin n → ℂ) :
    ‖bmKernel j x‖ ≤ eucNorm x ^ (1 - 2 * (n : ℝ)) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [bmKernel, Pi.zero_apply, map_zero, zero_div, norm_zero]
    exact Real.rpow_nonneg (eucNorm_nonneg _) _
  · have he : 0 < eucNorm x := eucNorm_pos hx
    rw [bmKernel, norm_div, norm_pow, starRingEnd_apply, norm_star, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (eucNorm_nonneg x)]
    calc ‖x j‖ / eucNorm x ^ (2 * n)
        ≤ eucNorm x / eucNorm x ^ (2 * n) :=
          div_le_div_of_nonneg_right (norm_apply_le_eucNorm x j) (pow_nonneg (eucNorm_nonneg x) _)
      _ = eucNorm x ^ (1 - 2 * (n : ℝ)) := by
          rw [show (1 : ℝ) - 2 * (n : ℝ) = 1 - ((2 * n : ℕ) : ℝ) by push_cast; ring]
          rw [Real.rpow_sub he, Real.rpow_one, Real.rpow_natCast]

private lemma hasCompactSupport_of_eucNorm {n : ℕ} {g : (Fin n → ℂ) → ℂ} {R : ℝ}
    (hg : ∀ x, R ≤ eucNorm x → g x = 0) : HasCompactSupport g := by
  refine (isCompact_closedBall (0 : Fin n → ℂ) R).of_isClosed_subset (isClosed_tsupport g) ?_
  rw [tsupport]
  refine closure_minimal ?_ Metric.isClosed_closedBall
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  by_contra hcon
  exact hx (hg x (le_trans (le_of_lt (lt_of_not_ge hcon)) (pi_norm_le_eucNorm x)))

private lemma integrable_bmKernel_mul {n : ℕ} (hn : 0 < n) (j : Fin n)
    {g : (Fin n → ℂ) → ℂ} (hg : Continuous g) (hgs : HasCompactSupport g) :
    Integrable (fun x => bmKernel j x * g x) := by
  have h := (locallyIntegrable_bmKernel hn j).integrable_smul_left_of_hasCompactSupport hg hgs
  simpa only [smul_eq_mul, mul_comm] using h

/-! ## The potential as an integral over a ball -/

private lemma bmPotential_eq_sum_ball {n : ℕ} {f : Fin n → (Fin n → ℂ) → ℂ} {S : ℝ}
    {z : Fin n → ℂ} (h : ∀ j x, S ≤ eucNorm x → f j (z + x) = 0) :
    bmPotential f z = ∑ j, ∫ x in eucBall (n := n) S, bmKernel j x * f j (z + x) := by
  rw [bmPotential_eq_bmPot]
  simp only [bmPot]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := eucBall (n := n) S) (f := fun x => bmKernel j x * f j (z + x)) (fun x hx => ?_)]
  rw [h j x (not_lt.mp hx), mul_zero]

private lemma bmPotential_sub_eq_sum_ball {n : ℕ} (hn : 0 < n) {f : Fin n → (Fin n → ℂ) → ℂ}
    {S : ℝ} {z z' : Fin n → ℂ}
    (h : ∀ j x, S ≤ eucNorm x → f j (z + x) = 0)
    (h' : ∀ j x, S ≤ eucNorm x → f j (z' + x) = 0)
    (hf : ∀ j, ContDiff ℝ 1 (f j)) :
    bmPotential f z - bmPotential f z'
      = ∑ j, ∫ x in eucBall (n := n) S, bmKernel j x * (f j (z + x) - f j (z' + x)) := by
  have hcont : ∀ j, Continuous (fun x => f j (z + x)) := fun j =>
    (hf j).continuous.comp (continuous_const.add continuous_id)
  have hcont' : ∀ j, Continuous (fun x => f j (z' + x)) := fun j =>
    (hf j).continuous.comp (continuous_const.add continuous_id)
  have hint : ∀ j, IntegrableOn (fun x => bmKernel j x * f j (z + x)) (eucBall (n := n) S) := fun j =>
    (integrable_bmKernel_mul hn j (hcont j) (hasCompactSupport_of_eucNorm (h j))).integrableOn
  have hint' : ∀ j, IntegrableOn (fun x => bmKernel j x * f j (z' + x)) (eucBall (n := n) S) := fun j =>
    (integrable_bmKernel_mul hn j (hcont' j) (hasCompactSupport_of_eucNorm (h' j))).integrableOn
  rw [bmPotential_eq_sum_ball h, bmPotential_eq_sum_ball h', ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← integral_sub (hint j) (hint' j)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  ring

/-! ## Differentiating a translate -/

private lemma dCoord_comp_add_CZ {n : ℕ} (k : Fin n) {f : (Fin n → ℂ) → ℂ} {z x : Fin n → ℂ}
    (hf : DifferentiableAt ℝ f (z + x)) :
    Work.CR.Flat.dCoord k (fun y => f (z + y)) x = Work.CR.Flat.dCoord k f (z + x) := by
  have hshift : HasFDerivAt (fun y : Fin n → ℂ => z + y) (ContinuousLinearMap.id ℝ (Fin n → ℂ)) x :=
    (hasFDerivAt_id x).const_add z
  have h := (hf.hasFDerivAt).comp x hshift
  simp only [Function.comp_def, ContinuousLinearMap.id_comp] at h
  rw [Work.CR.Flat.dCoord, Work.CR.Flat.dCoord, h.fderiv, ContinuousLinearMap.comp_id]

private lemma dbarCoord_comp_add_CZ {n : ℕ} (k : Fin n) {f : (Fin n → ℂ) → ℂ} {z x : Fin n → ℂ}
    (hf : DifferentiableAt ℝ f (z + x)) :
    Work.CR.Flat.dbarCoord k (fun y => f (z + y)) x = Work.CR.Flat.dbarCoord k f (z + x) := by
  have hshift : HasFDerivAt (fun y : Fin n → ℂ => z + y) (ContinuousLinearMap.id ℝ (Fin n → ℂ)) x :=
    (hasFDerivAt_id x).const_add z
  have h := (hf.hasFDerivAt).comp x hshift
  simp only [Function.comp_def, ContinuousLinearMap.id_comp] at h
  rw [Work.CR.Flat.dbarCoord, Work.CR.Flat.dbarCoord, h.fderiv, ContinuousLinearMap.comp_id]

private lemma rpow_neg_two_mul_add_one {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    a ^ (-(2 * (n : ℝ) + 1)) = 1 / a ^ (2 * n + 1) := by
  rw [show -(2 * (n : ℝ) + 1) = -(((2 * n + 1 : ℕ)) : ℝ) by push_cast; ring]
  rw [Real.rpow_neg ha, Real.rpow_natCast, one_div]

private lemma integrableOn_eucNorm_rpow {n : ℕ} (hn : 0 < n) {s : ℝ}
    (hs : -(2 * (n : ℝ)) < s) {ρ : ℝ} (hρ : 0 < ρ) :
    IntegrableOn (fun x : Fin n → ℂ => ‖x‖ ^ s) (Metric.ball (0 : Fin n → ℂ) ρ) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hfin : (Module.finrank ℝ (Fin n → ℂ) : ℝ) = 2 * (n : ℝ) := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, Finset.sum_const, nsmul_eq_mul]
    ring
  have hspos : 0 < s + (Module.finrank ℝ (Fin n → ℂ) : ℝ) := by rw [hfin]; linarith
  refine (integrableOn_fun_norm_addHaar (volume : Measure (Fin n → ℂ)) (r := ρ)
    (f := fun y : ℝ => y ^ s)).mpr ?_
  have hDge : ((Module.finrank ℝ (Fin n → ℂ) - 1 : ℕ) : ℝ) + 1
      = (Module.finrank ℝ (Fin n → ℂ) : ℝ) := by
    exact_mod_cast (Nat.sub_add_cancel (Nat.succ_le_of_lt Module.finrank_pos) :
      Module.finrank ℝ (Fin n → ℂ) - 1 + 1 = Module.finrank ℝ (Fin n → ℂ))
  have hr : -1 < s + ((Module.finrank ℝ (Fin n → ℂ) - 1 : ℕ) : ℝ) := by
    linarith only [hDge, hspos]
  refine ((intervalIntegral.integrableOn_Ioo_rpow_iff hρ).2 hr).congr_fun ?_
    measurableSet_Ioo
  intro y hy
  rw [Set.mem_Ioo] at hy
  simp only [smul_eq_mul]
  rw [← Real.rpow_natCast y (Module.finrank ℝ (Fin n → ℂ) - 1), ← Real.rpow_add hy.1, add_comm]

private lemma norm_setIntegral_le_of_norm_leCZ {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} (hs : MeasurableSet s) {F : α → ℂ} {g : α → ℝ}
    (hg : IntegrableOn g s μ) (h : ∀ x ∈ s, ‖F x‖ ≤ g x) :
    ‖∫ x in s, F x ∂μ‖ ≤ ∫ x in s, g x ∂μ := by
  rw [← integral_indicator hs (f := F), ← integral_indicator hs (f := g)]
  refine norm_integral_le_of_norm_le (hg.integrable_indicator hs)
    (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]; exact h x hx
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; simp

set_option maxHeartbeats 1600000

/-- **The Calderón–Zygmund (Bochner–Martinelli Schauder) estimate for the Bochner–Martinelli
potential on a polydisc: a gain of exactly one derivative.**

Let `n ≥ 1`, `0 < α < 1`, and let `polydisc c r` be a polydisc in `ℂⁿ = Fin n → ℂ`.  There is
`C = C(n, c, r, α) > 0` such that for every family `g` of `C¹` functions supported in the open
half-polydisc `{z | ∀ k, ‖z k - c k‖ < r k / 2}` (i.e. vanishing wherever `∃ k, r k / 2 ≤ ‖z k - c k‖`)

`‖bmPotential g‖_{C^{1,α}(polydisc c (r/2))} ≤ C · Σ_j ‖g_j‖_{C^{0,α}(ℂⁿ)}`.

This is the `k = 0` case of the flat `∂̄`-Poincaré estimate with a gain of one derivative; it is
the single remaining input of the bootstrap
`Work.CR.Flat.Cauchy.exists_dbar_solution_polydisc_Ck`.

Sketched proof.  Write the potential as a convolution `bmPotential g = -Σ_j (bmKernel_j ⋆ g_j)`,
cut off the kernel near the origin (`eucCutoff R`): the piece away from the singularity contributes
a smooth compactly supported kernel (`bmPhiCut`, `bmPsiCut`) and is estimated by the mean value
inequality.  For the singular part, `∂_{z_k}` of the kernel is `bmDzKernel k j`, homogeneous of
degree `-2n` with vanishing spherical mean (`integral_bmDzKernel_eucShell_eq_zero`), so
subtracting `g_j(z)` makes the integral absolutely convergent and gives the supremum bound;
the difference of two such integrals at `x, y` is split into the near shell (`|ζ - x| ≤ 2‖x-y‖`,
bounded by `‖g‖_{C^{0,α}} |x-y|^α` using the integrability of `‖·‖^{1-2n}`) and the far region
(bounded via `norm_bmDzKernel_sub_le`, the `(-2n-1)`-homogeneous bound on the kernel's gradient,
giving `|x-y| log(1/|x-y|) ≤ C_α |x-y|^α`).  The `∂̄`-components of the gradient are handled by
`bmPotential_solves_dbar`. -/
theorem bmPotential_holder_CZ {n : ℕ} (hn : 0 < n) {c : Fin n → ℂ} {r : Fin n → ℝ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hr : ∀ j, 0 < r j) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : Fin n → (Fin n → ℂ) → ℂ, (∀ j, ContDiff ℝ 1 (g j)) →
      (∀ j z, (∃ k, r k / 2 ≤ ‖z k - c k‖) → g j z = 0) →
      holderNorm 1 α (bmPotential g) (polydisc c (fun j => r j / 2))
        ≤ ENNReal.ofReal C * ∑ j, holderNorm 0 α (g j) Set.univ := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  -- ### the radius of the window
  set R : ℝ := Real.sqrt (∑ k, (r k + 2 * ‖c k‖) ^ 2) with hRdef
  have hRpos : 0 < R := by
    rw [hRdef]
    refine Real.sqrt_pos.mpr ?_
    refine Finset.sum_pos' (fun k _ => sq_nonneg _) ⟨⟨0, hn⟩, Finset.mem_univ _, ?_⟩
    have h := hr ⟨0, hn⟩
    nlinarith [norm_nonneg (c ⟨0, hn⟩)]
  have hsq_le : ∀ k : Fin n, (r k / 2 + ‖c k‖) ^ 2 ≤ (r k + 2 * ‖c k‖) ^ 2 := by
    intro k
    have h1 : 0 ≤ r k / 2 + ‖c k‖ := by have := hr k; positivity
    have h2 : r k / 2 + ‖c k‖ ≤ r k + 2 * ‖c k‖ := by
      have := hr k; linarith [norm_nonneg (c k)]
    exact pow_le_pow_left₀ h1 h2 2
  -- ### the constants attached to the two families of Calderón-Zygmund kernels
  obtain ⟨hmeasDz, hmeasDbar, Adec, hAdecpos, hAdecDz, hAdecDbar⟩ := bmCz.bmKernel_decay_le hn
  obtain ⟨Cp2, hCp2pos, hCp2⟩ := bmCz.norm_bmDzKernel_sub_le hn
  obtain ⟨Cp3, hCp3pos, hCp3⟩ := bmCz.norm_bmDbarKernel_sub_le hn
  set A : ℝ := max (max Adec Cp2) Cp3 with hAdef
  have hApos : 0 < A := by
    rw [hAdef]; exact lt_max_of_lt_left (lt_max_of_lt_left hAdecpos)
  have hAle : Adec ≤ A := by rw [hAdef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hC2le : Cp2 ≤ A := by rw [hAdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hC3le : Cp3 ≤ A := by rw [hAdef]; exact le_max_right _ _
  have hP1dz : ∀ (k j : Fin n) (x : Fin n → ℂ), x ≠ 0 →
      ‖bmDzKernel k j x‖ ≤ A / (eucNorm x) ^ (2 * n) := by
    intro k j x hx
    exact (hAdecDz k j x hx).trans
      (div_le_div_of_nonneg_right hAle (pow_nonneg (eucNorm_nonneg x) _))
  have hP1dbar : ∀ (j k : Fin n) (x : Fin n → ℂ), x ≠ 0 →
      ‖bmDbarKernel j k x‖ ≤ A / (eucNorm x) ^ (2 * n) := by
    intro j k x hx
    exact (hAdecDbar j k x hx).trans
      (div_le_div_of_nonneg_right hAle (pow_nonneg (eucNorm_nonneg x) _))
  have hP2dz : ∀ (k j : Fin n) (x h : Fin n → ℂ), 2 * eucNorm h ≤ eucNorm x →
      ‖bmDzKernel k j (x - h) - bmDzKernel k j x‖
        ≤ A * eucNorm h / (eucNorm x) ^ (2 * n + 1) := by
    intro k j x h hxh
    have h1 := hCp2 k j x h hxh
    rw [rpow_neg_two_mul_add_one (eucNorm_nonneg x) n] at h1
    refine h1.trans ?_
    calc Cp2 * eucNorm h * (1 / (eucNorm x) ^ (2 * n + 1))
        = Cp2 * eucNorm h / (eucNorm x) ^ (2 * n + 1) := by ring
      _ ≤ A * eucNorm h / (eucNorm x) ^ (2 * n + 1) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC2le (eucNorm_nonneg h))
            (pow_nonneg (eucNorm_nonneg x) _)
  have hP2dbar : ∀ (j k : Fin n) (x h : Fin n → ℂ), 2 * eucNorm h ≤ eucNorm x →
      ‖bmDbarKernel j k (x - h) - bmDbarKernel j k x‖
        ≤ A * eucNorm h / (eucNorm x) ^ (2 * n + 1) := by
    intro j k x h hxh
    exact (hCp3 j k x h hxh).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC3le (eucNorm_nonneg h))
        (pow_nonneg (eucNorm_nonneg x) _))
  have hH2dz : ∀ (k j : Fin n) (a b : ℝ), 0 < a → a < b →
      ∫ x in eucShell a b, bmDzKernel k j x = 0 :=
    fun k j a b ha _ => bmCz.integral_bmDzKernel_eucShell_eq_zero (k := k) (j := j) (ρ := b) ha
  have hH2dbar : ∀ (j k : Fin n) (a b : ℝ), 0 < a → a < b →
      ∫ x in eucShell a b, bmDbarKernel j k x = 0 :=
    fun j k a b ha _ => bmCz.bmDbarKernel_shell_eq_zero hn (j := j) (k := k) (b := b) ha
  -- ### the Calderón-Zygmund estimates, uniformly over the finitely many kernels
  have hCZdz : ∀ p : Fin n × Fin n, ∃ C : ℝ, 0 < C ∧ ∀ (K : ℝ), 0 ≤ K →
      ∀ g : (Fin n → ℂ) → ℂ,
      (∀ x y : Fin n → ℂ, ‖g x - g y‖ ≤ K * ‖x - y‖ ^ α) →
      (∀ x : Fin n → ℂ, R ≤ eucNorm x → g x = 0) →
      (∀ z : Fin n → ℂ,
        ‖∫ x in eucBall (n := n) (4 * R), bmDzKernel p.1 p.2 x * (g (z + x) - g z)‖ ≤ C * K) ∧
      (∀ z z' : Fin n → ℂ,
        ‖(∫ x in eucBall (n := n) (4 * R), bmDzKernel p.1 p.2 x * (g (z + x) - g z))
            - (∫ x in eucBall (n := n) (4 * R), bmDzKernel p.1 p.2 x * (g (z' + x) - g z'))‖
          ≤ C * K * ‖z - z'‖ ^ α) := by
    intro p
    exact bmCz.czKernel_holderBound hn hα hα1 hRpos (hmeasDz p.1 p.2) hApos
      (hP1dz p.1 p.2) (hP2dz p.1 p.2) (hH2dz p.1 p.2)
  have hCZdbar : ∀ p : Fin n × Fin n, ∃ C : ℝ, 0 < C ∧ ∀ (K : ℝ), 0 ≤ K →
      ∀ g : (Fin n → ℂ) → ℂ,
      (∀ x y : Fin n → ℂ, ‖g x - g y‖ ≤ K * ‖x - y‖ ^ α) →
      (∀ x : Fin n → ℂ, R ≤ eucNorm x → g x = 0) →
      (∀ z : Fin n → ℂ,
        ‖∫ x in eucBall (n := n) (4 * R), bmDbarKernel p.1 p.2 x * (g (z + x) - g z)‖ ≤ C * K) ∧
      (∀ z z' : Fin n → ℂ,
        ‖(∫ x in eucBall (n := n) (4 * R), bmDbarKernel p.1 p.2 x * (g (z + x) - g z))
            - (∫ x in eucBall (n := n) (4 * R), bmDbarKernel p.1 p.2 x * (g (z' + x) - g z'))‖
          ≤ C * K * ‖z - z'‖ ^ α) := by
    intro p
    exact bmCz.czKernel_holderBound hn hα hα1 hRpos (hmeasDbar p.1 p.2) hApos
      (hP1dbar p.1 p.2) (hP2dbar p.1 p.2) (hH2dbar p.1 p.2)
  choose Cdz hCdz using hCZdz
  choose Cdbar hCdbar using hCZdbar
  obtain ⟨cc, hcc⟩ := bmCz.integral_bmKernel_mul_dbarCoord hn
  set Cs : ℝ := (∑ p : Fin n × Fin n, Cdz p) + (∑ p : Fin n × Fin n, Cdbar p) with hCsdef
  set Cc : ℝ := ∑ p : Fin n × Fin n, ‖cc p.1 p.2‖ with hCcdef
  have hCs0 : 0 ≤ Cs := by
    rw [hCsdef]
    exact add_nonneg (Finset.sum_nonneg fun p _ => (hCdz p).1.le)
      (Finset.sum_nonneg fun p _ => (hCdbar p).1.le)
  have hCc0 : 0 ≤ Cc := by rw [hCcdef]; exact Finset.sum_nonneg fun p _ => norm_nonneg _
  have hCdzle : ∀ p : Fin n × Fin n, Cdz p ≤ Cs := by
    intro p
    rw [hCsdef]
    exact le_add_of_le_of_nonneg
      (Finset.single_le_sum (fun q _ => (hCdz q).1.le) (Finset.mem_univ p))
      (Finset.sum_nonneg fun q _ => (hCdbar q).1.le)
  have hCdbarle : ∀ p : Fin n × Fin n, Cdbar p ≤ Cs := by
    intro p
    rw [hCsdef]
    exact le_add_of_nonneg_of_le
      (Finset.sum_nonneg fun q _ => (hCdz q).1.le)
      (Finset.single_le_sum (fun q _ => (hCdbar q).1.le) (Finset.mem_univ p))
  have hccle : ∀ k j : Fin n, ‖cc k j‖ ≤ Cc := by
    intro k j
    rw [hCcdef]
    exact Finset.single_le_sum (s := Finset.univ) (f := fun p : Fin n × Fin n => ‖cc p.1 p.2‖)
      (fun p _ => norm_nonneg _) (Finset.mem_univ (k, j))
  set B : ℝ := 2 * (n : ℝ) * (2 * Cs + Cc) with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  -- ### the L¹ mass of the Bochner-Martinelli kernel on the window
  set κ : ℝ := (Module.finrank ℝ (Fin n → ℂ) : ℝ)
      * (volume : Measure (Fin n → ℂ)).real (Metric.ball (0 : Fin n → ℂ) 1) * R with hκdef
  have hκpos : 0 < κ := by
    rw [hκdef]
    refine mul_pos (mul_pos (by exact_mod_cast Module.finrank_pos) ?_) hRpos
    rw [Measure.real_def]
    exact ENNReal.toReal_pos (ne_of_gt (Metric.measure_ball_pos volume 0 one_pos))
      (ne_of_lt MeasureTheory.measure_ball_lt_top)
  have hκbd : ∫ x in eucBall (n := n) R, ‖x‖ ^ (1 - 2 * (n : ℝ)) ≤ κ := by
    refine (MeasureTheory.setIntegral_mono_set
      (integrableOn_eucNorm_rpow hn (by linarith) hRpos)
      (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg x) _)
      (Filter.Eventually.of_forall fun x hx => eucBall_subset_ball hx)).trans (le_of_eq ?_)
    rw [bmCz.integral_norm_rpow_ball hn (by linarith) hRpos, hκdef]
    rw [show (1 - 2 * (n : ℝ)) + (Module.finrank ℝ (Fin n → ℂ) : ℝ) = 1 by
      rw [show (Module.finrank ℝ (Fin n → ℂ) : ℝ) = 2 * (n : ℝ) by
        rw [Module.finrank_pi_fintype]
        simp [Complex.finrank_real_complex, Finset.sum_const, nsmul_eq_mul]
        ring]
      ring]
    rw [Real.rpow_one, div_one]
  have hintE : IntegrableOn (fun x : Fin n → ℂ => ‖x‖ ^ (1 - 2 * (n : ℝ)))
      (eucBall (n := n) R) :=
    (integrableOn_eucNorm_rpow hn (by linarith) hRpos).mono_set eucBall_subset_ball
  refine ⟨κ + 2 * B, by positivity, ?_⟩
  intro f hf hsupp
  set P : Set (Fin n → ℂ) := polydisc c (fun j => r j / 2) with hPdef
  have hPopen : IsOpen P := hPdef ▸ isOpen_polydisc c _
  -- ### the support conditions
  have hPn : ∀ z ∈ P, eucNorm z < R := by
    intro z hz
    have h1 : eucNorm z ^ 2 < R ^ 2 := by
      have hA : ∑ k, ‖z k‖ ^ 2 < ∑ k, (r k / 2 + ‖c k‖) ^ 2 := by
        refine Finset.sum_lt_sum (fun k _ => ?_) ⟨⟨0, hn⟩, Finset.mem_univ _, ?_⟩
        · have htri : ‖z k‖ ≤ ‖z k - c k‖ + ‖c k‖ := by
            simpa [sub_add_cancel] using norm_add_le (z k - c k) (c k)
          have h3 : ‖z k‖ < r k / 2 + ‖c k‖ := by have := hz k; linarith
          nlinarith [norm_nonneg (z k), h3, norm_nonneg (c k), hr k]
        · have htri : ‖z ⟨0, hn⟩‖ ≤ ‖z ⟨0, hn⟩ - c ⟨0, hn⟩‖ + ‖c ⟨0, hn⟩‖ := by
            simpa [sub_add_cancel] using norm_add_le (z ⟨0, hn⟩ - c ⟨0, hn⟩) (c ⟨0, hn⟩)
          have h3 : ‖z ⟨0, hn⟩‖ < r ⟨0, hn⟩ / 2 + ‖c ⟨0, hn⟩‖ := by
            have := hz ⟨0, hn⟩; linarith
          nlinarith [norm_nonneg (z ⟨0, hn⟩), h3, norm_nonneg (c ⟨0, hn⟩), hr ⟨0, hn⟩]
      have hB : ∑ k, (r k / 2 + ‖c k‖) ^ 2 ≤ ∑ k, (r k + 2 * ‖c k‖) ^ 2 :=
        Finset.sum_le_sum fun k _ => hsq_le k
      have hC : ∑ k, (r k + 2 * ‖c k‖) ^ 2 = R ^ 2 :=
        (Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg _)).symm.trans (by rw [hRdef])
      rw [eucNorm_sq, ← hC]
      linarith
    nlinarith [eucNorm_nonneg z, hRpos, h1]
  have hsuppR : ∀ j x, R ≤ eucNorm x → f j x = 0 := by
    intro j x hx
    refine hsupp j x ?_
    by_contra hcon
    push_neg at hcon
    have hlt := hPn x hcon
    linarith
  have hsuppSup : ∀ j x, R ≤ ‖x‖ → f j x = 0 := fun j x hx =>
    hsuppR j x (le_trans hx (pi_norm_le_eucNorm x))
  have hsuppE : ∀ z ∈ P, ∀ j x, R ≤ eucNorm x → f j (z + x) = 0 := by
    intro z hz j x hx
    refine hsupp j (z + x) ?_
    by_contra hcon
    push_neg at hcon
    have hpt : ∀ k, ‖x k‖ < r k := by
      intro k
      have htri : ‖x k‖ ≤ ‖(z + x) k - c k‖ + ‖z k - c k‖ := by
        have h := norm_add_le ((z + x) k - c k) (-(z k - c k))
        have he : ((z + x) k - c k) + (-(z k - c k)) = x k := by
          rw [Pi.add_apply]; ring
        rw [he, norm_neg] at h
        exact h
      have h1 := hcon k
      have h2 := hz k
      linarith
    have hsq : ∑ k, ‖x k‖ ^ 2 < ∑ k, (r k) ^ 2 :=
      Finset.sum_lt_sum (fun k _ => by nlinarith [norm_nonneg (x k), hpt k, hr k])
        ⟨⟨0, hn⟩, Finset.mem_univ _, by
          nlinarith [norm_nonneg (x ⟨0, hn⟩), hpt ⟨0, hn⟩, hr ⟨0, hn⟩]⟩
    have hle : ∑ k, (r k) ^ 2 ≤ R ^ 2 := by
      have hB : ∑ k, (r k) ^ 2 ≤ ∑ k, (r k + 2 * ‖c k‖) ^ 2 := by
        refine Finset.sum_le_sum fun k _ => ?_
        nlinarith [norm_nonneg (c k), hr k, sq_nonneg (r k)]
      have hC : ∑ k, (r k + 2 * ‖c k‖) ^ 2 = R ^ 2 :=
        (Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg _)).symm.trans (by rw [hRdef])
      linarith
    have hlt : eucNorm x < R := by
      have h2 : eucNorm x ^ 2 < R ^ 2 := by rw [eucNorm_sq]; linarith
      nlinarith [eucNorm_nonneg x, hRpos, h2]
    linarith
  -- ### the trivial case where the `C^{0,α}` norm of the data is infinite
  by_cases htop : ∑ j, holderNorm 0 α (f j) Set.univ = ⊤
  · rw [htop, ENNReal.mul_top (by rw [ENNReal.ofReal_ne_zero_iff]; positivity)]
    exact le_top
  · have hfin : ∀ j, holderNorm 0 α (f j) Set.univ ≠ ⊤ := by
      intro j hj
      have hle : holderNorm 0 α (f j) Set.univ ≤ ∑ i, holderNorm 0 α (f i) Set.univ :=
        Finset.single_le_sum (s := Finset.univ) (f := fun i => holderNorm 0 α (f i) Set.univ)
          (fun i _ => bot_le) (Finset.mem_univ j)
      exact htop (top_le_iff.mp (hj ▸ hle))
    set A' : Fin n → ℝ := fun j => (iterDerivNorm 0 (f j) Set.univ).toReal with hA'def
    set K' : Fin n → ℝ := fun j => (holderSeminorm 0 α (f j) Set.univ).toReal with hK'def
    have hA'0 : ∀ j, 0 ≤ A' j := fun j => ENNReal.toReal_nonneg
    have hK'0 : ∀ j, 0 ≤ K' j := fun j => ENNReal.toReal_nonneg
    have hA'lt : ∀ j, iterDerivNorm 0 (f j) Set.univ ≠ ⊤ := fun j => lt_top_iff_ne_top.mp
      (lt_of_le_of_lt (iterDerivNorm_le_holderNorm 0 α (f j) Set.univ (Nat.zero_le 0))
        (lt_top_iff_ne_top.mpr (hfin j)))
    have hK'lt : ∀ j, holderSeminorm 0 α (f j) Set.univ ≠ ⊤ := fun j => lt_top_iff_ne_top.mp
      (lt_of_le_of_lt (holderSeminorm_le_holderNorm 0 α (f j) Set.univ (Nat.zero_le 0))
        (lt_top_iff_ne_top.mpr (hfin j)))
    have hA'eq : ∀ j, ENNReal.ofReal (A' j) = iterDerivNorm 0 (f j) Set.univ := fun j =>
      ENNReal.ofReal_toReal (hA'lt j)
    have hK'eq : ∀ j, ENNReal.ofReal (K' j) = holderSeminorm 0 α (f j) Set.univ := fun j =>
      ENNReal.ofReal_toReal (hK'lt j)
    have hfA : ∀ j x, ‖f j x‖ ≤ A' j := by
      intro j x
      have h1 : ENNReal.ofReal ‖f j x‖ ≤ iterDerivNorm 0 (f j) Set.univ := by
        rw [iterDerivNorm_zero]
        exact le_iSup₂_of_le x (Set.mem_univ x) le_rfl
      rw [← hA'eq j] at h1
      exact (ENNReal.ofReal_le_ofReal_iff (hA'0 j)).mp h1
    have hfK : ∀ j x y, ‖f j x - f j y‖ ≤ K' j * ‖x - y‖ ^ α := by
      intro j x y
      rcases eq_or_ne x y with rfl | hxy
      · simp [Real.zero_rpow (ne_of_gt hα)]
      · have h1 : ENNReal.ofReal (‖f j x - f j y‖ / ‖x - y‖ ^ α)
            ≤ holderSeminorm 0 α (f j) Set.univ := by
          have h := le_holderSeminorm 0 α (f j) Set.univ (Set.mem_univ x) (Set.mem_univ y) hxy
          rwa [norm_iteratedFDerivWithin_zero_sub_CZ] at h
        rw [← hK'eq j] at h1
        have h2 : ‖f j x - f j y‖ / ‖x - y‖ ^ α ≤ K' j :=
          (ENNReal.ofReal_le_ofReal_iff (hK'0 j)).mp h1
        have h3 : 0 < ‖x - y‖ ^ α :=
          Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
        rwa [div_le_iff₀ h3] at h2
    have hsa : 0 ≤ ∑ j, A' j := Finset.sum_nonneg fun j _ => hA'0 j
    have hsk : 0 ≤ ∑ j, K' j := Finset.sum_nonneg fun j _ => hK'0 j
    -- ### (i) the supremum of the potential
    have hT0 : iterDerivNorm 0 (bmPotential f) P ≤ ENNReal.ofReal (κ * ∑ j, A' j) := by
      rw [iterDerivNorm_zero]
      refine iSup₂_le fun p hp => ?_
      have hp' : ∀ k, ‖p k - c k‖ < r k / 2 := hp
      refine ENNReal.ofReal_le_ofReal ?_
      rw [bmPotential_eq_sum_ball (h := fun j x hx => hsuppE p hp' j x hx)]
      refine (norm_sum_le _ _).trans ?_
      have hstep : ∀ j : Fin n,
          ‖∫ x in eucBall (n := n) R, bmKernel j x * f j (p + x)‖ ≤ A' j * κ := by
        intro j
        have hdom : IntegrableOn (fun x : Fin n → ℂ => A' j * ‖x‖ ^ (1 - 2 * (n : ℝ)))
            (eucBall (n := n) R) := hintE.const_mul (A' j)
        refine (norm_setIntegral_le_of_norm_leCZ (measurableSet_eucBall (n := n) R) hdom ?_).trans ?_
        · intro x _
          rw [norm_mul]
          calc ‖bmKernel j x‖ * ‖f j (p + x)‖
              ≤ ‖x‖ ^ (1 - 2 * (n : ℝ)) * A' j :=
                mul_le_mul (norm_bmKernel_le j x) (hfA j (p + x)) (norm_nonneg _)
                  (Real.rpow_nonneg (norm_nonneg x) _)
            _ = A' j * ‖x‖ ^ (1 - 2 * (n : ℝ)) := by ring
        · rw [integral_const_mul]
          exact mul_le_mul_of_nonneg_left hκbd (hA'0 j)
      calc ∑ j, ‖∫ x in eucBall (n := n) R, bmKernel j x * f j (p + x)‖
          ≤ ∑ j, A' j * κ := Finset.sum_le_sum fun j _ => hstep j
        _ = (∑ j, A' j) * κ := by rw [Finset.sum_mul]
        _ = κ * ∑ j, A' j := by ring
    -- ### (ii) the Hölder seminorm of the potential
    have hT1 : holderSeminorm 0 α (bmPotential f) P ≤ ENNReal.ofReal (κ * ∑ j, K' j) := by
      refine holderSeminorm_zero_le_ofReal _ _ ?_
      intro p hp q hq hpq
      have hp' : ∀ k, ‖p k - c k‖ < r k / 2 := hp
      have hq' : ∀ k, ‖q k - c k‖ < r k / 2 := hq
      rw [bmPotential_sub_eq_sum_ball hn (hsuppE p hp') (hsuppE q hq') hf]
      refine (norm_sum_le _ _).trans ?_
      have hstep : ∀ j : Fin n,
          ‖∫ x in eucBall (n := n) R, bmKernel j x * (f j (p + x) - f j (q + x))‖
            ≤ K' j * κ * ‖p - q‖ ^ α := by
        intro j
        have hdom : IntegrableOn (fun x : Fin n → ℂ => K' j * ‖p - q‖ ^ α
            * ‖x‖ ^ (1 - 2 * (n : ℝ))) (eucBall (n := n) R) :=
          hintE.const_mul (K' j * ‖p - q‖ ^ α)
        refine (norm_setIntegral_le_of_norm_leCZ (measurableSet_eucBall (n := n) R) hdom ?_).trans ?_
        · intro x _
          rw [norm_mul]
          have h5 := hfK j (p + x) (q + x)
          rw [show (p + x) - (q + x) = p - q from by ring] at h5
          calc ‖bmKernel j x‖ * ‖f j (p + x) - f j (q + x)‖
              ≤ ‖x‖ ^ (1 - 2 * (n : ℝ)) * (K' j * ‖p - q‖ ^ α) :=
                mul_le_mul (norm_bmKernel_le j x) h5 (norm_nonneg _)
                  (Real.rpow_nonneg (norm_nonneg x) _)
            _ = K' j * ‖p - q‖ ^ α * ‖x‖ ^ (1 - 2 * (n : ℝ)) := by ring
        · rw [integral_const_mul]
          refine (mul_le_mul_of_nonneg_left hκbd
            (mul_nonneg (hK'0 j) (Real.rpow_nonneg (norm_nonneg _) α))).trans (le_of_eq ?_)
          ring
      calc ∑ j, ‖∫ x in eucBall (n := n) R, bmKernel j x * (f j (p + x) - f j (q + x))‖
          ≤ ∑ j, K' j * κ * ‖p - q‖ ^ α := Finset.sum_le_sum fun j _ => hstep j
        _ = (∑ j, K' j) * κ * ‖p - q‖ ^ α := by rw [Finset.sum_mul, Finset.sum_mul]
        _ = κ * (∑ j, K' j) * ‖p - q‖ ^ α := by ring
    -- ### the two Wirtinger derivatives as sums of singular integrals
    have hcont1 : ∀ (j : Fin n) (z : Fin n → ℂ), ContDiff ℝ 1 (fun x => f j (z + x)) :=
      fun j z => (hf j).comp (contDiff_const.add contDiff_id)
    have hdCoord : ∀ (k : Fin n) (p : Fin n → ℂ), (∀ m, ‖p m - c m‖ < r m / 2) →
        Work.CR.Flat.dCoord k (bmPotential f) p
          = -∑ j, ∫ x in eucBall (n := n) (4 * R), bmDzKernel k j x * (f j (p + x) - f j p) := by
      intro k p hp
      have h1 : Work.CR.Flat.dCoord k (bmPotential f) p
          = ∑ j, ∫ x, bmKernel j x * Work.CR.Flat.dCoord k (f j) (p + x) := by
        rw [funext (fun w => bmPotential_eq_bmPot f w)]
        exact bmCz.bmPot_dCoord hn hf hRpos hsuppSup k p
      rw [h1]
      have hper : ∀ j : Fin n, ∫ x, bmKernel j x * Work.CR.Flat.dCoord k (f j) (p + x)
          = -∫ x in eucBall (n := n) (4 * R), bmDzKernel k j x * (f j (p + x) - f j p) := by
        intro j
        have hcongr : (∫ x, bmKernel j x * Work.CR.Flat.dCoord k (f j) (p + x))
            = ∫ x, bmKernel j x * Work.CR.Flat.dCoord k (fun y => f j (p + y)) x := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          exact congrArg (fun t => bmKernel j x * t)
            (dCoord_comp_add_CZ (f := f j) (z := p) (x := x) k
              (((hf j).differentiable (by norm_num)).differentiableAt)).symm
        rw [hcongr]
        have h2 := bmCz.integral_bmKernel_mul_dCoord hn k j (fun y => f j (p + y)) R
          hRpos (hcont1 j p) (hsuppE p hp j)
        simpa using h2
      rw [Finset.sum_congr rfl (fun j _ => hper j), Finset.sum_neg_distrib]
    have hdbarCoord : ∀ (k : Fin n) (p : Fin n → ℂ), (∀ m, ‖p m - c m‖ < r m / 2) →
        Work.CR.Flat.dbarCoord k (bmPotential f) p
          = (-∑ j, ∫ x in eucBall (n := n) (4 * R), bmDbarKernel k j x * (f j (p + x) - f j p))
            - ∑ j, cc k j * f j p := by
      intro k p hp
      have h1 : Work.CR.Flat.dbarCoord k (bmPotential f) p
          = ∑ j, ∫ x, bmKernel j x * Work.CR.Flat.dbarCoord k (f j) (p + x) := by
        rw [funext (fun w => bmPotential_eq_bmPot f w)]
        exact bmPot_dbarCoord hn hf hRpos hsuppSup k p
      rw [h1]
      have hper : ∀ j : Fin n, ∫ x, bmKernel j x * Work.CR.Flat.dbarCoord k (f j) (p + x)
          = (-∫ x in eucBall (n := n) (4 * R), bmDbarKernel k j x * (f j (p + x) - f j p))
            - cc k j * f j p := by
        intro j
        have hcongr : (∫ x, bmKernel j x * Work.CR.Flat.dbarCoord k (f j) (p + x))
            = ∫ x, bmKernel j x * Work.CR.Flat.dbarCoord k (fun y => f j (p + y)) x := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          exact congrArg (fun t => bmKernel j x * t)
            (dbarCoord_comp_add_CZ (f := f j) (z := p) (x := x) k
              (((hf j).differentiable (by norm_num)).differentiableAt)).symm
        rw [hcongr]
        have h2 := hcc k j (fun y => f j (p + y)) R hRpos (hcont1 j p) (hsuppE p hp j)
        simpa using h2
      rw [Finset.sum_congr rfl (fun j _ => hper j), Finset.sum_sub_distrib,
        Finset.sum_neg_distrib]
    -- ### the summed kernel constants
    have hsumDz : ∀ k : Fin n, ∑ j, Cdz (k, j) * K' j ≤ Cs * ∑ j, K' j := by
      intro k
      refine (Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_right (hCdzle (k, j)) (hK'0 j)).trans (le_of_eq ?_)
      rw [Finset.mul_sum]
    have hsumDbar : ∀ k : Fin n, ∑ j, Cdbar (k, j) * K' j ≤ Cs * ∑ j, K' j := by
      intro k
      refine (Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_right (hCdbarle (k, j)) (hK'0 j)).trans (le_of_eq ?_)
      rw [Finset.mul_sum]
    have hdz_le : ∀ (k : Fin n) (p : Fin n → ℂ), (∀ i, ‖p i - c i‖ < r i / 2) →
        ‖Work.CR.Flat.dCoord k (bmPotential f) p‖ ≤ Cs * (∑ j, K' j) := by
      intro k p hp
      rw [hdCoord k p hp, norm_neg]
      refine (norm_sum_le _ _).trans ?_
      have h1 : ∀ j : Fin n,
          ‖∫ x in eucBall (n := n) (4 * R), bmDzKernel k j x * (f j (p + x) - f j p)‖
            ≤ Cdz (k, j) * K' j := fun j =>
        ((hCdz (k, j)).2 (K' j) (hK'0 j) (f j) (hfK j) (hsuppR j)).1 p
      exact (Finset.sum_le_sum fun j _ => h1 j).trans (hsumDz k)
    have hdbar_le : ∀ (k : Fin n) (p : Fin n → ℂ), (∀ i, ‖p i - c i‖ < r i / 2) →
        ‖Work.CR.Flat.dbarCoord k (bmPotential f) p‖
          ≤ Cs * (∑ j, K' j) + Cc * (∑ j, A' j) := by
      intro k p hp
      rw [hdbarCoord k p hp]
      have hA : ‖-∑ j, (∫ x in eucBall (n := n) (4 * R),
            bmDbarKernel k j x * (f j (p + x) - f j p))‖ ≤ Cs * (∑ j, K' j) := by
        rw [norm_neg]
        refine (norm_sum_le _ _).trans ?_
        have h1 : ∀ j : Fin n,
            ‖∫ x in eucBall (n := n) (4 * R), bmDbarKernel k j x * (f j (p + x) - f j p)‖
              ≤ Cdbar (k, j) * K' j := fun j =>
          ((hCdbar (k, j)).2 (K' j) (hK'0 j) (f j) (hfK j) (hsuppR j)).1 p
        exact (Finset.sum_le_sum fun j _ => h1 j).trans (hsumDbar k)
      have hB : ‖∑ j, cc k j * f j p‖ ≤ Cc * (∑ j, A' j) := by
        refine (norm_sum_le _ _).trans ?_
        have h1 : ∀ j : Fin n, ‖cc k j * f j p‖ ≤ Cc * A' j := fun j => by
          rw [norm_mul]
          exact mul_le_mul (hccle k j) (hfA j p) (norm_nonneg _) hCc0
        exact (Finset.sum_le_sum fun j _ => h1 j).trans (le_of_eq (Finset.mul_sum _ _ _).symm)
      calc ‖(-∑ j, (∫ x in eucBall (n := n) (4 * R),
                  bmDbarKernel k j x * (f j (p + x) - f j p))) - ∑ j, cc k j * f j p‖
          ≤ ‖-∑ j, (∫ x in eucBall (n := n) (4 * R),
                  bmDbarKernel k j x * (f j (p + x) - f j p))‖ + ‖∑ j, cc k j * f j p‖ :=
            norm_sub_le _ _
        _ ≤ Cs * (∑ j, K' j) + Cc * (∑ j, A' j) := add_le_add hA hB
    have hdzh : ∀ (k : Fin n) (p q : Fin n → ℂ), (∀ i, ‖p i - c i‖ < r i / 2) →
        (∀ i, ‖q i - c i‖ < r i / 2) →
        ‖Work.CR.Flat.dCoord k (bmPotential f) p
            - Work.CR.Flat.dCoord k (bmPotential f) q‖
          ≤ Cs * (∑ j, K' j) * ‖p - q‖ ^ α := by
      intro k p q hp hq
      rw [hdCoord k p hp, hdCoord k q hq]
      rw [show (-∑ j, (∫ x in eucBall (n := n) (4 * R),
                  bmDzKernel k j x * (f j (p + x) - f j p)))
            - (-∑ j, (∫ x in eucBall (n := n) (4 * R),
                  bmDzKernel k j x * (f j (q + x) - f j q)))
          = ∑ j, ((∫ x in eucBall (n := n) (4 * R),
                  bmDzKernel k j x * (f j (q + x) - f j q))
              - (∫ x in eucBall (n := n) (4 * R),
                  bmDzKernel k j x * (f j (p + x) - f j p))) by
          rw [← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun j _ => by ring]
      refine (norm_sum_le _ _).trans ?_
      have h1 : ∀ j : Fin n,
          ‖(∫ x in eucBall (n := n) (4 * R), bmDzKernel k j x * (f j (q + x) - f j q))
            - (∫ x in eucBall (n := n) (4 * R), bmDzKernel k j x * (f j (p + x) - f j p))‖
          ≤ Cdz (k, j) * K' j * ‖q - p‖ ^ α := fun j =>
        ((hCdz (k, j)).2 (K' j) (hK'0 j) (f j) (hfK j) (hsuppR j)).2 q p
      calc ∑ j, ‖(∫ x in eucBall (n := n) (4 * R),
                  bmDzKernel k j x * (f j (q + x) - f j q))
              - (∫ x in eucBall (n := n) (4 * R),
                  bmDzKernel k j x * (f j (p + x) - f j p))‖
          ≤ ∑ j, Cdz (k, j) * K' j * ‖q - p‖ ^ α := Finset.sum_le_sum fun j _ => h1 j
        _ ≤ ∑ j, Cs * K' j * ‖q - p‖ ^ α := Finset.sum_le_sum fun j _ =>
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (hCdzle (k, j)) (hK'0 j))
                (Real.rpow_nonneg (norm_nonneg (q - p)) α)
        _ = (Cs * (∑ j, K' j)) * ‖q - p‖ ^ α := by rw [Finset.mul_sum, Finset.sum_mul]
        _ = (Cs * (∑ j, K' j)) * ‖p - q‖ ^ α := by rw [norm_sub_rev]
    have hdbarh : ∀ (k : Fin n) (p q : Fin n → ℂ), (∀ i, ‖p i - c i‖ < r i / 2) →
        (∀ i, ‖q i - c i‖ < r i / 2) →
        ‖Work.CR.Flat.dbarCoord k (bmPotential f) p
            - Work.CR.Flat.dbarCoord k (bmPotential f) q‖
          ≤ (Cs + Cc) * (∑ j, K' j) * ‖p - q‖ ^ α := by
      intro k p q hp hq
      rw [hdbarCoord k p hp, hdbarCoord k q hq]
      have e0 : ((-∑ j, (∫ x in eucBall (n := n) (4 * R),
                      bmDbarKernel k j x * (f j (p + x) - f j p)))
                    - (∑ j, cc k j * f j p))
                  - ((-∑ j, (∫ x in eucBall (n := n) (4 * R),
                      bmDbarKernel k j x * (f j (q + x) - f j q)))
                    - (∑ j, cc k j * f j q))
              = ((-∑ j, (∫ x in eucBall (n := n) (4 * R),
                      bmDbarKernel k j x * (f j (p + x) - f j p)))
                    - (-∑ j, (∫ x in eucBall (n := n) (4 * R),
                      bmDbarKernel k j x * (f j (q + x) - f j q))))
                + ((∑ j, cc k j * f j q) - (∑ j, cc k j * f j p)) := by abel
      have e1 : (-∑ j, (∫ x in eucBall (n := n) (4 * R),
                      bmDbarKernel k j x * (f j (p + x) - f j p)))
                  - (-∑ j, (∫ x in eucBall (n := n) (4 * R),
                      bmDbarKernel k j x * (f j (q + x) - f j q)))
              = ∑ j, ((∫ x in eucBall (n := n) (4 * R),
                      bmDbarKernel k j x * (f j (q + x) - f j q))
                  - (∫ x in eucBall (n := n) (4 * R),
                      bmDbarKernel k j x * (f j (p + x) - f j p))) := by
        rw [← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      have e2 : (∑ j, cc k j * f j q) - (∑ j, cc k j * f j p)
              = ∑ j, (cc k j * f j q - cc k j * f j p) := by
        rw [← Finset.sum_sub_distrib]
      rw [e0, e1, e2]
      have hA : ‖∑ j, ((∫ x in eucBall (n := n) (4 * R),
              bmDbarKernel k j x * (f j (q + x) - f j q))
            - (∫ x in eucBall (n := n) (4 * R),
              bmDbarKernel k j x * (f j (p + x) - f j p)))‖
          ≤ Cs * (∑ j, K' j) * ‖q - p‖ ^ α := by
        refine (norm_sum_le _ _).trans ?_
        have h1 : ∀ j : Fin n,
            ‖(∫ x in eucBall (n := n) (4 * R), bmDbarKernel k j x * (f j (q + x) - f j q))
              - (∫ x in eucBall (n := n) (4 * R), bmDbarKernel k j x * (f j (p + x) - f j p))‖
            ≤ Cdbar (k, j) * K' j * ‖q - p‖ ^ α := fun j =>
          ((hCdbar (k, j)).2 (K' j) (hK'0 j) (f j) (hfK j) (hsuppR j)).2 q p
        calc ∑ j, ‖(∫ x in eucBall (n := n) (4 * R),
                    bmDbarKernel k j x * (f j (q + x) - f j q))
                - (∫ x in eucBall (n := n) (4 * R),
                    bmDbarKernel k j x * (f j (p + x) - f j p))‖
            ≤ ∑ j, Cdbar (k, j) * K' j * ‖q - p‖ ^ α := Finset.sum_le_sum fun j _ => h1 j
          _ ≤ ∑ j, Cs * K' j * ‖q - p‖ ^ α := Finset.sum_le_sum fun j _ =>
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right (hCdbarle (k, j)) (hK'0 j))
                  (Real.rpow_nonneg (norm_nonneg (q - p)) α)
          _ = (Cs * (∑ j, K' j)) * ‖q - p‖ ^ α := by rw [Finset.mul_sum, Finset.sum_mul]
      have hB : ‖∑ j, (cc k j * f j q - cc k j * f j p)‖
          ≤ Cc * (∑ j, K' j) * ‖q - p‖ ^ α := by
        refine (norm_sum_le _ _).trans ?_
        have h1 : ∀ j : Fin n, ‖cc k j * f j q - cc k j * f j p‖
            ≤ Cc * (K' j * ‖q - p‖ ^ α) := by
          intro j
          rw [← mul_sub, norm_mul]
          exact mul_le_mul (hccle k j) (hfK j q p) (norm_nonneg _) hCc0
        calc ∑ j, ‖cc k j * f j q - cc k j * f j p‖
            ≤ ∑ j, Cc * (K' j * ‖q - p‖ ^ α) := Finset.sum_le_sum fun j _ => h1 j
          _ = (Cc * (∑ j, K' j)) * ‖q - p‖ ^ α := by
              rw [Finset.mul_sum, Finset.sum_mul]
              exact Finset.sum_congr rfl fun j _ => by ring
      calc ‖(∑ j, ((∫ x in eucBall (n := n) (4 * R),
                  bmDbarKernel k j x * (f j (q + x) - f j q))
                - (∫ x in eucBall (n := n) (4 * R),
                  bmDbarKernel k j x * (f j (p + x) - f j p))))
              + (∑ j, (cc k j * f j q - cc k j * f j p))‖
          ≤ ‖∑ j, ((∫ x in eucBall (n := n) (4 * R),
                  bmDbarKernel k j x * (f j (q + x) - f j q))
                - (∫ x in eucBall (n := n) (4 * R),
                  bmDbarKernel k j x * (f j (p + x) - f j p)))‖
            + ‖∑ j, (cc k j * f j q - cc k j * f j p)‖ := norm_add_le _ _
        _ ≤ Cs * (∑ j, K' j) * ‖q - p‖ ^ α + Cc * (∑ j, K' j) * ‖q - p‖ ^ α :=
            add_le_add hA hB
        _ = (Cs + Cc) * (∑ j, K' j) * ‖q - p‖ ^ α := by ring
        _ = (Cs + Cc) * (∑ j, K' j) * ‖p - q‖ ^ α := by rw [norm_sub_rev]
    -- ### (iii) and (iv) the derivative and its Hölder seminorm
    have hT2 : iterDerivNorm 1 (bmPotential f) P
        ≤ ENNReal.ofReal (B * ((∑ j, A' j) + (∑ j, K' j))) := by
      refine iterDerivNorm_one_le_ofReal _ _ hPopen (mul_nonneg hB0 (add_nonneg hsa hsk)) ?_
      intro p hp
      refine (bmCz.norm_fderiv_le_sum_wirtinger (bmPotential f) p).trans ?_
      have h1 : ∑ k : Fin n, (‖Work.CR.Flat.dCoord k (bmPotential f) p‖
            + ‖Work.CR.Flat.dbarCoord k (bmPotential f) p‖)
          ≤ (n : ℝ) * (2 * Cs * (∑ j, K' j) + Cc * (∑ j, A' j)) := by
        have h2 : ∀ k : Fin n, ‖Work.CR.Flat.dCoord k (bmPotential f) p‖
              + ‖Work.CR.Flat.dbarCoord k (bmPotential f) p‖
            ≤ 2 * Cs * (∑ j, K' j) + Cc * (∑ j, A' j) := by
          intro k
          have h3 := add_le_add (hdz_le k p hp) (hdbar_le k p hp)
          linarith
        refine (Finset.sum_le_sum fun k _ => h2 k).trans (le_of_eq ?_)
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      calc 2 * ∑ k, (‖Work.CR.Flat.dCoord k (bmPotential f) p‖
              + ‖Work.CR.Flat.dbarCoord k (bmPotential f) p‖)
          ≤ 2 * ((n : ℝ) * (2 * Cs * (∑ j, K' j) + Cc * (∑ j, A' j))) :=
            mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ ≤ B * ((∑ j, A' j) + (∑ j, K' j)) := by
            have hle1 : 2 * Cs * (∑ j, K' j) ≤ 2 * Cs * ((∑ j, A' j) + (∑ j, K' j)) :=
              mul_le_mul_of_nonneg_left (by linarith) (by linarith)
            have hle2 : Cc * (∑ j, A' j) ≤ Cc * ((∑ j, A' j) + (∑ j, K' j)) :=
              mul_le_mul_of_nonneg_left (by linarith) hCc0
            have hsum : 2 * Cs * (∑ j, K' j) + Cc * (∑ j, A' j)
                ≤ (2 * Cs + Cc) * ((∑ j, A' j) + (∑ j, K' j)) := by linarith
            calc 2 * ((n : ℝ) * (2 * Cs * (∑ j, K' j) + Cc * (∑ j, A' j)))
                = (2 * (n : ℝ)) * (2 * Cs * (∑ j, K' j) + Cc * (∑ j, A' j)) := by ring
              _ ≤ (2 * (n : ℝ)) * ((2 * Cs + Cc) * ((∑ j, A' j) + (∑ j, K' j))) :=
                  mul_le_mul_of_nonneg_left hsum (by positivity)
              _ = B * ((∑ j, A' j) + (∑ j, K' j)) := by rw [hBdef]; ring
    have hT3 : holderSeminorm 1 α (bmPotential f) P ≤ ENNReal.ofReal (B * ∑ j, K' j) := by
      refine holderSeminorm_one_le_ofReal _ _ hPopen (mul_nonneg hB0 hsk) ?_
      intro p hp q hq hpq
      have hp' : ∀ i, ‖p i - c i‖ < r i / 2 := hp
      have hq' : ∀ i, ‖q i - c i‖ < r i / 2 := hq
      refine (bmCz.norm_fderiv_sub_le_sum_wirtinger (bmPotential f) p q).trans ?_
      have h1 : ∑ k : Fin n, (‖Work.CR.Flat.dCoord k (bmPotential f) p
              - Work.CR.Flat.dCoord k (bmPotential f) q‖
            + ‖Work.CR.Flat.dbarCoord k (bmPotential f) p
              - Work.CR.Flat.dbarCoord k (bmPotential f) q‖)
          ≤ (n : ℝ) * ((2 * Cs + Cc) * (∑ j, K' j) * ‖p - q‖ ^ α) := by
        have h2 : ∀ k : Fin n, ‖Work.CR.Flat.dCoord k (bmPotential f) p
              - Work.CR.Flat.dCoord k (bmPotential f) q‖
            + ‖Work.CR.Flat.dbarCoord k (bmPotential f) p
              - Work.CR.Flat.dbarCoord k (bmPotential f) q‖
            ≤ (2 * Cs + Cc) * (∑ j, K' j) * ‖p - q‖ ^ α := by
          intro k
          have h3 := add_le_add (hdzh k p q hp' hq') (hdbarh k p q hp' hq')
          linarith [hsk, Real.rpow_nonneg (norm_nonneg (p - q)) α]
        refine (Finset.sum_le_sum fun k _ => h2 k).trans (le_of_eq ?_)
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      calc 2 * ∑ k, (‖Work.CR.Flat.dCoord k (bmPotential f) p
              - Work.CR.Flat.dCoord k (bmPotential f) q‖
            + ‖Work.CR.Flat.dbarCoord k (bmPotential f) p
              - Work.CR.Flat.dbarCoord k (bmPotential f) q‖)
          ≤ 2 * ((n : ℝ) * ((2 * Cs + Cc) * (∑ j, K' j) * ‖p - q‖ ^ α)) :=
            mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ = B * (∑ j, K' j) * ‖p - q‖ ^ α := by rw [hBdef]; ring
    -- ### assembly
    have h0j : ∀ j, holderNorm 0 α (f j) Set.univ = ENNReal.ofReal (A' j + K' j) := by
      intro j
      rw [holderNorm, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        ENNReal.ofReal_add (hA'0 j) (hK'0 j), hA'eq j, hK'eq j]
    have h0 : ∑ j, holderNorm 0 α (f j) Set.univ
        = ENNReal.ofReal (∑ j, (A' j + K' j)) := by
      rw [Finset.sum_congr rfl (fun j _ => h0j j),
        ← ENNReal.ofReal_sum_of_nonneg (fun j _ => add_nonneg (hA'0 j) (hK'0 j))]
    have hmain : holderNorm 1 α (bmPotential f) P
        ≤ ENNReal.ofReal ((κ + 2 * B) * ((∑ j, A' j) + (∑ j, K' j))) := by
      rw [holderNorm_one_eq_sum]
      have hb1 : iterDerivNorm 0 (bmPotential f) P + holderSeminorm 0 α (bmPotential f) P
          ≤ ENNReal.ofReal (κ * (∑ j, A' j) + κ * (∑ j, K' j)) := by
        rw [ENNReal.ofReal_add (mul_nonneg hκpos.le hsa) (mul_nonneg hκpos.le hsk)]
        exact add_le_add hT0 hT1
      have hb2 : iterDerivNorm 1 (bmPotential f) P + holderSeminorm 1 α (bmPotential f) P
          ≤ ENNReal.ofReal (B * ((∑ j, A' j) + (∑ j, K' j)) + B * (∑ j, K' j)) := by
        rw [ENNReal.ofReal_add (mul_nonneg hB0 (add_nonneg hsa hsk)) (mul_nonneg hB0 hsk)]
        exact add_le_add hT2 hT3
      refine (add_le_add hb1 hb2).trans ?_
      rw [← ENNReal.ofReal_add (add_nonneg (mul_nonneg hκpos.le hsa) (mul_nonneg hκpos.le hsk))
        (add_nonneg (mul_nonneg hB0 (add_nonneg hsa hsk)) (mul_nonneg hB0 hsk))]
      refine ENNReal.ofReal_le_ofReal ?_
      nlinarith [hκpos.le, hB0, hsa, hsk]
    calc holderNorm 1 α (bmPotential f) P
        ≤ ENNReal.ofReal ((κ + 2 * B) * ((∑ j, A' j) + (∑ j, K' j))) := hmain
      _ = ENNReal.ofReal (κ + 2 * B) * ENNReal.ofReal ((∑ j, A' j) + (∑ j, K' j)) :=
          ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ κ + 2 * B)
      _ = ENNReal.ofReal (κ + 2 * B) * ∑ j, holderNorm 0 α (f j) Set.univ := by
          rw [h0, Finset.sum_add_distrib]

end Work.CR.Flat.Cauchy
