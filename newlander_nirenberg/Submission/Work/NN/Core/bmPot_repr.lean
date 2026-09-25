import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmCZDefs
import Submission.Work.CR.Flat.Cauchy.bmDefs
import Submission.Work.CR.Flat.Cauchy.bmCz.integral_bmKernel_mul_dCoord
import Submission.Work.CR.Flat.Cauchy.bmCz.dCoord_bmKernel
import Submission.Work.CR.Flat.Cauchy.bmKernel_divergence_aux
import Submission.Work.CR.Flat.Cauchy.bmKerEps_dbarCoord_integral
import Submission.Work.CR.Flat.Cauchy.bmKerEpsDivergence
import Submission.Work.CR.Flat.Cauchy.bmCz.eucRadialBound
import Submission.Work.CR.Flat.Cauchy.bmCz.integral_bmKernel_mul_dbarCoord
import Submission.Work.CR.Flat.Cauchy.bmCz.bmDbarKernel_shell_eq_zero
import Submission.Work.CR.Flat.Polydisc.dbarCoord_comm

namespace Work.NN.Core

open MeasureTheory Set
open scoped NNReal ENNReal Topology
open Filter
open Work.CR.Flat
open Work.CR.Flat.Cauchy


/-! ## Auxiliary lemmas for `bmPot_repr`

The main theorem is a representation formula for the Bochner--Martinelli potential: the
`(1,0)`-part of the pairing was already proved (`Work.CR.Flat.Cauchy.bmCz.integral_bmKernel_mul_dCoord`),
and the `(0,1)`-part requires the integration-by-parts identity for `dbarCoord` against the
singular kernel.  Since the kernel is singular at the origin the identity is proved by
regularisation (the `bmKerEps` kernel) and a limiting argument; the constant `c j k` is
defined abstractly with the help of a fixed cutoff, so that no explicit evaluation of a
normalising integral is needed. -/

/-- `eucNorm` is `C¹` away from the origin. -/
lemma contDiffAt_eucNorm {n : ℕ} {x : Fin n → ℂ} (hx : x ≠ 0) :
    ContDiffAt ℝ 1 (fun y : Fin n → ℂ => eucNorm y) x := by
  have hnrmSq : ContDiff ℝ ⊤ (fun y : Fin n → ℂ => nrmSq y) := by
    have h : (fun y : Fin n → ℂ => nrmSq y) = fun y => ∑ j, ‖y j‖ ^ 2 := rfl
    rw [h]
    refine ContDiff.sum (s := Finset.univ) fun j _ => ?_
    exact (contDiff_norm_sq ℝ (E := ℂ) (n := ⊤)).comp
      (((ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ).contDiff)
  have hne : nrmSq x ≠ 0 := fun h => hx (nrmSq_eq_zero.mp h)
  have hsqrt : ContDiffAt ℝ ⊤ (fun y : Fin n → ℂ => Real.sqrt (nrmSq y)) x :=
    ContDiffAt.sqrt hnrmSq.contDiffAt hne
  exact hsqrt.of_le le_top

/-- The smooth radial cutoff `eucCutoffC R` is `C¹` for `R > 0`. -/
lemma contDiff_one_eucCutoffC {n : ℕ} {R : ℝ} (hR : 0 < R) :
    ContDiff ℝ 1 (eucCutoffC (n := n) R) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    refine (contDiffAt_const (c := (1 : ℂ))).congr_of_eventuallyEq ?_
    have hmem : {y : Fin n → ℂ | 2 * eucNorm y < R} ∈ 𝓝 (0 : Fin n → ℂ) :=
      IsOpen.mem_nhds (isOpen_lt (continuous_const.mul continuous_eucNorm) continuous_const)
        (by show 2 * eucNorm (0 : Fin n → ℂ) < R; rw [eucNorm_zero, mul_zero]; exact hR)
    filter_upwards [hmem] with y hy
    simp only [eucCutoffC]
    rw [eucCutoff_eq_one hR (le_of_lt hy)]
    norm_num
  · have hinner : ContDiffAt ℝ 1 (fun y : Fin n → ℂ => eucNorm y / R) x :=
      (contDiffAt_eucNorm hx).div_const R
    have hcomp : ContDiffAt ℝ 1 (fun y : Fin n → ℂ => cutProfile (eucNorm y / R)) x :=
      contDiff_cutProfile.comp_contDiffAt x hinner
    change ContDiffAt ℝ 1 (fun y : Fin n → ℂ => ((cutProfile (eucNorm y / R) : ℝ) : ℂ)) x
    exact Complex.ofRealCLM.contDiff.comp_contDiffAt x hcomp

lemma eucCutoffC_zero {n : ℕ} {R : ℝ} (hR : 0 < R) : eucCutoffC (n := n) R 0 = 1 := by
  simp only [eucCutoffC]
  rw [eucCutoff_eq_one hR (by rw [eucNorm_zero, mul_zero]; exact hR.le)]
  norm_num

/-- The cutoff `eucCutoffC R` is `1` near the origin and `0` outside `eucBall R`, so it is
`1 - eucCutoffC R x` that is bounded by `(2/R)‖x‖`. -/
lemma norm_eucCutoffC_sub_one_le {n : ℕ} {R : ℝ} (hR : 0 < R) (x : Fin n → ℂ) :
    ‖eucCutoffC (n := n) R x - 1‖ ≤ (2 / R) * eucNorm x := by
  by_cases hx : 2 * eucNorm x ≤ R
  · rw [eucCutoffC, eucCutoff_eq_one hR hx, Complex.ofReal_one, sub_self, norm_zero]
    exact mul_nonneg (by positivity) (eucNorm_nonneg x)
  · push_neg at hx
    have h2R : 0 < 2 / R := by positivity
    have h1 : ‖eucCutoffC (n := n) R x - 1‖ ≤ 1 := by
      have hcoe : eucCutoffC (n := n) R x - 1 = (((eucCutoff R x - 1 : ℝ)) : ℂ) := by
        simp only [eucCutoffC]
        rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
      rw [hcoe, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_le]
      constructor
      · have := eucCutoff_nonneg R x; linarith
      · have := eucCutoff_le_one R x; linarith
    have h3 : (1 : ℝ) ≤ (2 / R) * eucNorm x := by
      have : (2 / R) * eucNorm x = (2 * eucNorm x) / R := by ring
      rw [this, le_div_iff₀ hR]
      linarith
    exact h1.trans h3

/-- For `g` of class `C¹` vanishing outside `eucBall R` (`R > 0`), the difference
`g - g 0` is dominated by a multiple of `eucNorm`. -/
lemma exists_norm_sub_le_eucNorm {n : ℕ} {g : (Fin n → ℂ) → ℂ} {R : ℝ} (hR : 0 < R)
    (hg : ContDiff ℝ 1 g) (hsupp : ∀ x, R ≤ eucNorm x → g x = 0) :
    ∃ M, 0 ≤ M ∧ ∀ x, ‖g x - g 0‖ ≤ M * eucNorm x := by
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_closedBall (0 : Fin n → ℂ) R)
    (hg.continuous_fderiv (by norm_num)).continuousOn
  refine ⟨max C (‖g 0‖ / R), le_trans (div_nonneg (norm_nonneg _) hR.le) (le_max_right _ _),
    fun x => ?_⟩
  have hMnn : (0 : ℝ) ≤ max C (‖g 0‖ / R) :=
    le_trans (div_nonneg (norm_nonneg _) hR.le) (le_max_right _ _)
  by_cases hxle : ‖x‖ ≤ R
  · have hxmem : x ∈ Metric.closedBall (0 : Fin n → ℂ) R := by
      rwa [Metric.mem_closedBall, dist_zero_right]
    have h0mem : (0 : Fin n → ℂ) ∈ Metric.closedBall (0 : Fin n → ℂ) R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hR.le
    have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le
      (s := Metric.closedBall (0 : Fin n → ℂ) R)
      (fun y _ => (hg.differentiable (by norm_num)).differentiableAt)
      (fun y hy => le_trans (hC y hy) (le_max_left C (‖g 0‖ / R)))
      (convex_closedBall (0 : Fin n → ℂ) R) h0mem hxmem
    calc ‖g x - g 0‖ ≤ max C (‖g 0‖ / R) * ‖x‖ := by simpa using hmvt
      _ ≤ max C (‖g 0‖ / R) * eucNorm x := mul_le_mul_of_nonneg_left (pi_norm_le_eucNorm x) hMnn
  · push_neg at hxle
    rw [hsupp x (le_trans hxle.le (pi_norm_le_eucNorm x)), zero_sub, norm_neg]
    calc ‖g 0‖ = (‖g 0‖ / R) * R := by field_simp
      _ ≤ max C (‖g 0‖ / R) * R := mul_le_mul_of_nonneg_right (le_max_right _ _) hR.le
      _ ≤ max C (‖g 0‖ / R) * eucNorm x :=
          mul_le_mul_of_nonneg_left (le_trans hxle.le (pi_norm_le_eucNorm x)) hMnn

/-- Integrability of `bmDbarKernel j k * f` on a Euclidean ball, for `f` of class `C¹`
vanishing at the origin and dominated by a multiple of `eucNorm`. -/
lemma integrableOn_bmDbarKernel_mul_of_le {n : ℕ} (hn : 0 < n) (j k : Fin n)
    {f : (Fin n → ℂ) → ℂ} (hf : ContDiff ℝ 1 f) (h0 : f 0 = 0) {M : ℝ}
    (hM : ∀ x, ‖f x‖ ≤ M * eucNorm x) (ρ : ℝ) :
    IntegrableOn (fun x : Fin n → ℂ => bmDbarKernel j k x * f x) (eucBall ρ) volume := by
  have hmeas : AEStronglyMeasurable (fun x : Fin n → ℂ => bmDbarKernel j k x * f x) volume :=
    ((bmCz.measurable_bmDbarKernel j k).mul hf.continuous.measurable).aestronglyMeasurable
  have hfin : Module.finrank ℝ (Fin n → ℂ) = 2 * n := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, Finset.sum_const]
    ring
  have hd : (1 : ℕ) ≤ Module.finrank ℝ (Fin n → ℂ) := by
    rw [hfin]; omega
  have hα : 2 * (n : ℝ) - 1 < (Module.finrank ℝ (Fin n → ℂ) : ℝ) := by
    rw [hfin]; push_cast; linarith
  have hdecay : ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : Fin n → ℂ) (|ρ| + 1))),
      ‖bmDbarKernel j k x * f x‖ ≤ ((n : ℝ) + 1) * |M| * ‖x‖ ^ (-(2 * (n : ℝ) - 1)) := by
    filter_upwards with x
    rcases eq_or_ne x 0 with rfl | hx
    · rw [h0, mul_zero, norm_zero, norm_zero,
        Real.zero_rpow (by
          have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          linarith : -(2 * (n : ℝ) - 1) ≠ 0), mul_zero]
    · have hX : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
      have h1 : ‖bmDbarKernel j k x‖ ≤ ((n : ℝ) + 1) / (eucNorm x) ^ (2 * n) :=
        bmCz.norm_bmDbarKernel_le j k hx
      have h2 : ‖f x‖ ≤ |M| * eucNorm x :=
        (hM x).trans (mul_le_mul_of_nonneg_right (le_abs_self M) (eucNorm_nonneg x))
      have hEx : 0 < eucNorm x := eucNorm_pos hx
      have h3 : ‖bmDbarKernel j k x * f x‖
          ≤ (((n : ℝ) + 1) / (eucNorm x) ^ (2 * n)) * (|M| * eucNorm x) := by
        rw [norm_mul]
        exact mul_le_mul h1 h2 (norm_nonneg _)
          (div_nonneg (by positivity) (by positivity))
      have h4 : (((n : ℝ) + 1) / (eucNorm x) ^ (2 * n)) * (|M| * eucNorm x)
          = ((n : ℝ) + 1) * |M| / (eucNorm x) ^ (2 * n - 1) := by
        have hp : (eucNorm x) ^ (2 * n) = (eucNorm x) ^ (2 * n - 1) * eucNorm x := by
          conv_lhs => rw [show 2 * n = 2 * n - 1 + 1 from by omega]
          rw [pow_succ]
        have hE : eucNorm x ≠ 0 := (eucNorm_pos hx).ne'
        rw [hp]
        field_simp
      have h5 : ((n : ℝ) + 1) * |M| / (eucNorm x) ^ (2 * n - 1)
          ≤ ((n : ℝ) + 1) * |M| * ‖x‖ ^ (-(2 * (n : ℝ) - 1)) := by
        have hcast : (2 * (n : ℝ) - 1) = ((2 * n - 1 : ℕ) : ℝ) := by
          rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]; push_cast; ring
        have hpow : ‖x‖ ^ (2 * n - 1) ≤ (eucNorm x) ^ (2 * n - 1) :=
          pow_le_pow_left₀ (norm_nonneg x) (pi_norm_le_eucNorm x) _
        have hinv : ((eucNorm x) ^ (2 * n - 1))⁻¹ ≤ (‖x‖ ^ (2 * n - 1))⁻¹ :=
          inv_anti₀ (pow_pos hX _) hpow
        have hrw : ‖x‖ ^ (-(2 * (n : ℝ) - 1)) = (‖x‖ ^ (2 * n - 1))⁻¹ := by
          rw [Real.rpow_neg (norm_nonneg x), hcast, Real.rpow_natCast]
        rw [hrw, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hinv (by positivity)
      exact h3.trans (h4.trans_le h5)
  have hint := MeasureTheory.integrableOn_ball_of_norm_le_rpow (μ := volume) hd hα hdecay hmeas
  refine hint.mono_set ?_
  intro x hx
  rw [Metric.mem_ball, dist_zero_right]
  rw [mem_eucBall] at hx
  calc ‖x‖ ≤ eucNorm x := pi_norm_le_eucNorm x
    _ < ρ := hx
    _ ≤ |ρ| + 1 := by linarith [le_abs_self ρ]

/-- Integrability of `bmKernel k * dbarCoord j f` for `f` of class `C¹` with compact support. -/
lemma integrable_bmKernel_mul_dbarCoord' {n : ℕ} (hn : 0 < n) (j k : Fin n)
    {f : (Fin n → ℂ) → ℂ} {a : ℝ} (hf : ContDiff ℝ 1 f)
    (hfs : ∀ x, a ≤ eucNorm x → f x = 0) :
    Integrable (fun x : Fin n → ℂ => bmKernel k x * dbarCoord j f x) :=
  bmCz.integrable_bmKernel_mul_dbarCoord_gen hn j k (continuous_dbarCoord hf j)
    (hasCompactSupport_dbarCoord (fun x hx => hfs x (le_trans hx (pi_norm_le_eucNorm x))) j)


/-- The regularised `∂̄`-derivative of the Bochner--Martinelli kernel is continuous. -/
lemma continuous_dbarCoord_bmKerEps_of {n : ℕ} (j k : Fin n) {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun x : Fin n → ℂ => dbarCoord j (bmKerEps k ε) x) := by
  change Continuous ((Polydisc.dbarCoordPhi j) ∘ (fderiv ℝ (bmKerEps k ε)))
  exact (Polydisc.dbarCoordPhi j).continuous.comp
    ((bmCz.contDiff_one_bmKerEps' k hε).continuous_fderiv (by norm_num))

/-- Domination of the regularised `∂̄`-kernel by the majorant `(n+1)‖h‖/‖·‖^{2n}`. -/
lemma tendsto_ball_dbarKerEps_mul {n : ℕ} (hn : 0 < n) (j k : Fin n) {h : (Fin n → ℂ) → ℂ}
    {ρ : ℝ} (hρ : 0 < ρ) (hh : ContDiff ℝ 1 h) (h0 : h 0 = 0)
    (hsupp : ∀ x, ρ ≤ eucNorm x → h x = 0) :
    Tendsto (fun ε : ℝ => ∫ x in eucBall (n := n) ρ, dbarCoord j (bmKerEps k ε) x * h x)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x in eucBall (n := n) ρ, bmDbarKernel j k x * h x)) := by
  have hsupp' : ∀ x : Fin n → ℂ, ρ ≤ ‖x‖ → h x = 0 :=
    fun x hx => hsupp x (le_trans hx (pi_norm_le_eucNorm x))
  obtain ⟨M, hM0, hM⟩ := bmCz.exists_norm_le_eucNorm_of_contDiff hρ.le hh hsupp' h0
  have hdom : Integrable (fun x : Fin n → ℂ => ((n : ℝ) + 1) * ‖h x‖ / (eucNorm x) ^ (2 * n))
      volume := bmCz.integrable_eucNorm_majorant hn hh hM hsupp'
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (eucBall (n := n) ρ)) (l := 𝓝[>] (0 : ℝ))
    (F := fun ε x => dbarCoord j (bmKerEps k ε) x * h x)
    (f := fun x => bmDbarKernel j k x * h x)
    (fun x => ((n : ℝ) + 1) * ‖h x‖ / (eucNorm x) ^ (2 * n)) ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ((continuous_dbarCoord_bmKerEps_of j k hε).mul hh.continuous).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards with x
    rcases eq_or_ne x 0 with rfl | hx
    · simp [h0]
    · rw [norm_mul]
      calc ‖dbarCoord j (bmKerEps k ε) x‖ * ‖h x‖
          ≤ (((n : ℝ) + 1) / (eucNorm x) ^ (2 * n)) * ‖h x‖ :=
            mul_le_mul_of_nonneg_right (bmCz.norm_dbarCoord_bmKerEps_le hε j k hx) (norm_nonneg _)
        _ = ((n : ℝ) + 1) * ‖h x‖ / (eucNorm x) ^ (2 * n) := by
            rw [div_mul_eq_mul_div]
  · exact hdom.integrableOn
  · refine Filter.Eventually.of_forall (fun x => ?_)
    rcases eq_or_ne x 0 with rfl | hx
    · simp [h0]
    · exact (bmCz.tendsto_dbarCoord_bmKerEps j k hx).mul_const (h x)

/-- **Integration by parts for `∂̄` against the Bochner--Martinelli kernel, for functions
vanishing at the origin.**  If `h` is `C¹`, `h 0 = 0` and `h` vanishes outside `eucBall ρ`,
then `∫ bmKernel k · ∂̄_j h = -∫_{eucBall ρ} bmDbarKernel j k · h`. -/
lemma integral_bmKernel_mul_dbarCoord_of_zero {n : ℕ} (hn : 0 < n) (j k : Fin n)
    {h : (Fin n → ℂ) → ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hh : ContDiff ℝ 1 h) (h0 : h 0 = 0)
    (hsupp : ∀ x, ρ ≤ eucNorm x → h x = 0) :
    (∫ x : Fin n → ℂ, bmKernel k x * dbarCoord j h x)
      = -∫ x in eucBall (n := n) ρ, bmDbarKernel j k x * h x := by
  have hsupp' : ∀ x : Fin n → ℂ, ρ ≤ ‖x‖ → h x = 0 :=
    fun x hx => hsupp x (le_trans hx (pi_norm_le_eucNorm x))
  have hzero : ∀ ε : ℝ, 0 < ε →
      (∫ x : Fin n → ℂ, bmKerEps k ε x * dbarCoord j h x)
        + (∫ x in eucBall (n := n) ρ, dbarCoord j (bmKerEps k ε) x * h x) = 0 := by
    intro ε hε
    have h1 : (∫ x : Fin n → ℂ, bmKerEps k ε x * dbarCoord j h x)
        = -∫ x : Fin n → ℂ, dbarCoord j (bmKerEps k ε) x * h x :=
      bmCz.integral_bmKerEps_mul_dbarCoord_eq_neg (n := n) j k hε hh hsupp'
    have h2 : (∫ x : Fin n → ℂ, dbarCoord j (bmKerEps k ε) x * h x)
        = ∫ x in eucBall (n := n) ρ, dbarCoord j (bmKerEps k ε) x * h x :=
      (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (s := eucBall (n := n) ρ)
        (fun x hx => by
          have hxρ : ρ ≤ eucNorm x :=
            not_lt.mp (fun hc => hx (by simpa [mem_eucBall] using hc))
          rw [hsupp x hxρ, mul_zero])).symm
    rw [h1, h2, neg_add_cancel]
  have hL := bmCz.tendsto_integral_bmKerEps_mul_dbarCoord hn j k hh hsupp'
  have hR := tendsto_ball_dbarKerEps_mul hn j k hρ hh h0 hsupp
  have hsum : Tendsto (fun ε : ℝ => (∫ x : Fin n → ℂ, bmKerEps k ε x * dbarCoord j h x)
      + (∫ x in eucBall (n := n) ρ, dbarCoord j (bmKerEps k ε) x * h x))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((∫ x : Fin n → ℂ, bmKernel k x * dbarCoord j h x)
        + ∫ x in eucBall (n := n) ρ, bmDbarKernel j k x * h x)) := hL.add hR
  have hsum0 : Tendsto (fun ε : ℝ => (∫ x : Fin n → ℂ, bmKerEps k ε x * dbarCoord j h x)
      + (∫ x in eucBall (n := n) ρ, dbarCoord j (bmKerEps k ε) x * h x))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hzero ε hε).symm
  exact eq_neg_of_add_eq_zero_left (tendsto_nhds_unique hsum hsum0)

/-- **Independence of the radius in the `∂̄` integration by parts.**  If `f` vanishes outside
`eucBall a` with `a > 0`, then the ball integral of `bmDbarKernel j k * (f - f 0)` does not
depend on the radius (`≥ a`). -/
lemma setIntegral_bmDbarKernel_sub_eq_of_le {n : ℕ} (hn : 0 < n) (j k : Fin n)
    {f : (Fin n → ℂ) → ℂ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupp : ∀ x, a ≤ eucNorm x → f x = 0)
    (hint : IntegrableOn (fun x : Fin n → ℂ => bmDbarKernel j k x * (f x - f 0))
      (eucBall (n := n) b) volume) :
    ∫ x in eucBall (n := n) b, bmDbarKernel j k x * (f x - f 0)
      = ∫ x in eucBall (n := n) a, bmDbarKernel j k x * (f x - f 0) := by
  have hsub : eucBall (n := n) a ⊆ eucBall (n := n) b := fun x hx => lt_of_lt_of_le hx hab
  have hdiff := MeasureTheory.setIntegral_diff (μ := volume)
    (f := fun x : Fin n → ℂ => bmDbarKernel j k x * (f x - f 0))
    (s := eucBall (n := n) b) (t := eucBall (n := n) a) (measurableSet_eucBall a) hint hsub
  have hset : eucBall (n := n) b \ eucBall (n := n) a = eucShell (n := n) a b := by
    ext x
    simp only [Set.mem_diff, mem_eucBall, mem_eucShell]
    constructor
    · intro h; exact ⟨not_lt.mp (fun hc => h.2 hc), h.1⟩
    · intro h; exact ⟨h.2, fun hc => not_le_of_gt hc h.1⟩
  have hcongr : (fun x : Fin n → ℂ => bmDbarKernel j k x * (f x - f 0))
      =ᵐ[volume.restrict (eucShell (n := n) a b)]
      (fun x => (-(f 0)) * bmDbarKernel j k x) := by
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' (measurableSet_eucShell a b)]
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    rw [hsupp x hx.1]
    ring
  have hzero : ∫ x in eucShell (n := n) a b, bmDbarKernel j k x * (f x - f 0) = 0 := by
    rw [MeasureTheory.integral_congr_ae hcongr, MeasureTheory.integral_const_mul,
      bmCz.bmDbarKernel_shell_eq_zero (n := n) hn ha, mul_zero]
  rw [hset, hzero] at hdiff
  exact sub_eq_zero.mp hdiff.symm

/-- Additivity and homogeneity of `f ↦ ∫ bmKernel k · ∂̄_j f`. -/
lemma bmA_add_smul {n : ℕ} (j k : Fin n) {f f' : (Fin n → ℂ) → ℂ} (c : ℂ)
    (hf : ContDiff ℝ 1 f) (hf' : ContDiff ℝ 1 f')
    (h1 : Integrable (fun x : Fin n → ℂ => bmKernel k x * dbarCoord j f x))
    (h2 : Integrable (fun x : Fin n → ℂ => bmKernel k x * dbarCoord j f' x)) :
    (∫ x : Fin n → ℂ, bmKernel k x * dbarCoord j (fun y => c * f y + f' y) x)
      = c * (∫ x : Fin n → ℂ, bmKernel k x * dbarCoord j f x)
        + (∫ x : Fin n → ℂ, bmKernel k x * dbarCoord j f' x) := by
  have hpt : ∀ x : Fin n → ℂ, bmKernel k x * dbarCoord j (fun y => c * f y + f' y) x
      = c * (bmKernel k x * dbarCoord j f x) + (bmKernel k x * dbarCoord j f' x) := by
    intro x
    have hdiffc : DifferentiableAt ℝ (fun y : Fin n → ℂ => c * f y) x :=
      (hf.differentiable (by norm_num)).differentiableAt.const_mul c
    have hdiff' : DifferentiableAt ℝ f' x := (hf'.differentiable (by norm_num)).differentiableAt
    have hadd : dbarCoord j (fun y : Fin n → ℂ => c * f y + f' y) x
        = dbarCoord j (fun y : Fin n → ℂ => c * f y) x + dbarCoord j f' x := by
      have h := Polydisc.dbarCoord_add j (fun y : Fin n → ℂ => c * f y) f' x hdiffc hdiff'
      simpa using h
    have hmul : dbarCoord j (fun y : Fin n → ℂ => c * f y) x = c * dbarCoord j f x := by
      have hdiff : DifferentiableAt ℝ f x := (hf.differentiable (by norm_num)).differentiableAt
      have h := Polydisc.dbarCoord_mul j (fun _ : Fin n → ℂ => c) f x
        (differentiableAt_const c) hdiff
      rw [BmEpsAux.dbarCoord_const j c x, zero_mul, zero_add] at h
      exact h
    rw [hadd, hmul]
    ring
  rw [funext hpt, MeasureTheory.integral_add (h1.const_mul c) h2,
    MeasureTheory.integral_const_mul]

/-- Additivity and homogeneity of `f ↦ ∫_{eucBall ρ} bmDbarKernel j k · (f - f 0)`. -/
lemma bmBd_add_smul {n : ℕ} (j k : Fin n) {ρ : ℝ} {f f' : (Fin n → ℂ) → ℂ} (c : ℂ)
    (hf : ContDiff ℝ 1 f) (hf' : ContDiff ℝ 1 f')
    (h1 : IntegrableOn (fun x : Fin n → ℂ => bmDbarKernel j k x * (f x - f 0))
      (eucBall (n := n) ρ) volume)
    (h2 : IntegrableOn (fun x : Fin n → ℂ => bmDbarKernel j k x * (f' x - f' 0))
      (eucBall (n := n) ρ) volume) :
    (∫ x in eucBall (n := n) ρ, bmDbarKernel j k x
        * ((fun y => c * f y + f' y) x - (fun y => c * f y + f' y) 0))
      = c * (∫ x in eucBall (n := n) ρ, bmDbarKernel j k x * (f x - f 0))
        + (∫ x in eucBall (n := n) ρ, bmDbarKernel j k x * (f' x - f' 0)) := by
  have hpt : ∀ x : Fin n → ℂ,
      bmDbarKernel j k x * ((fun y => c * f y + f' y) x - (fun y => c * f y + f' y) 0)
      = c * (bmDbarKernel j k x * (f x - f 0)) + (bmDbarKernel j k x * (f' x - f' 0)) := by
    intro x; ring
  rw [MeasureTheory.setIntegral_congr_fun (measurableSet_eucBall ρ) (fun x _ => hpt x)]
  rw [MeasureTheory.integral_add (MeasureTheory.Integrable.const_mul h1 c) h2,
    MeasureTheory.integral_const_mul]

/-- Subtraction rule for `f ↦ ∫ bmKernel k · ∂̄_j f`. -/
lemma bmA_sub {n : ℕ} (j k : Fin n) {f f' : (Fin n → ℂ) → ℂ}
    (hf : ContDiff ℝ 1 f) (hf' : ContDiff ℝ 1 f')
    (h1 : Integrable (fun x : Fin n → ℂ => bmKernel k x * dbarCoord j f x))
    (h2 : Integrable (fun x : Fin n → ℂ => bmKernel k x * dbarCoord j f' x)) :
    (∫ x : Fin n → ℂ, bmKernel k x * dbarCoord j (fun y => f y - f' y) x)
      = (∫ x : Fin n → ℂ, bmKernel k x * dbarCoord j f x)
        - (∫ x : Fin n → ℂ, bmKernel k x * dbarCoord j f' x) := by
  have hpt : ∀ x : Fin n → ℂ, bmKernel k x * dbarCoord j (fun y => f y - f' y) x
      = bmKernel k x * dbarCoord j f x - bmKernel k x * dbarCoord j f' x := by
    intro x
    have hdiff : DifferentiableAt ℝ f x := (hf.differentiable (by norm_num)).differentiableAt
    have hdiff' : DifferentiableAt ℝ f' x := (hf'.differentiable (by norm_num)).differentiableAt
    have hsub : dbarCoord j (fun y : Fin n → ℂ => f y - f' y) x
        = dbarCoord j f x - dbarCoord j f' x := by
      simp only [dbarCoord]
      rw [show (fun y : Fin n → ℂ => f y - f' y) = f - f' from rfl, fderiv_sub hdiff hdiff']
      simp only [ContinuousLinearMap.sub_apply]
      ring
    rw [hsub]; ring
  rw [funext hpt, MeasureTheory.integral_sub h1 h2]

/-- Subtraction rule for `f ↦ ∫_{eucBall ρ} bmDbarKernel j k · (f - f 0)`. -/
lemma bmBd_sub {n : ℕ} (j k : Fin n) {ρ : ℝ} {f f' : (Fin n → ℂ) → ℂ}
    (hf : ContDiff ℝ 1 f) (hf' : ContDiff ℝ 1 f')
    (h1 : IntegrableOn (fun x : Fin n → ℂ => bmDbarKernel j k x * (f x - f 0))
      (eucBall (n := n) ρ) volume)
    (h2 : IntegrableOn (fun x : Fin n → ℂ => bmDbarKernel j k x * (f' x - f' 0))
      (eucBall (n := n) ρ) volume) :
    (∫ x in eucBall (n := n) ρ, bmDbarKernel j k x
        * ((fun y => f y - f' y) x - (fun y => f y - f' y) 0))
      = (∫ x in eucBall (n := n) ρ, bmDbarKernel j k x * (f x - f 0))
        - (∫ x in eucBall (n := n) ρ, bmDbarKernel j k x * (f' x - f' 0)) := by
  have hpt : ∀ x : Fin n → ℂ,
      bmDbarKernel j k x * ((fun y => f y - f' y) x - (fun y => f y - f' y) 0)
      = bmDbarKernel j k x * (f x - f 0) - bmDbarKernel j k x * (f' x - f' 0) := by
    intro x; ring
  rw [MeasureTheory.setIntegral_congr_fun (measurableSet_eucBall ρ) (fun x _ => hpt x),
    MeasureTheory.integral_sub h1 h2]

/-- The constant in the `∂̄`-Bochner--Martinelli integration by parts, defined with the fixed
cutoff `eucCutoffC 1`. -/
noncomputable def bmC0 (n : ℕ) (j k : Fin n) : ℂ :=
  (∫ x : Fin n → ℂ, bmKernel k x * dbarCoord j (eucCutoffC (n := n) 1) x)
    + ∫ x in eucBall (n := n) 4,
        bmDbarKernel j k x * (eucCutoffC (n := n) 1 x - eucCutoffC (n := n) 1 0)

set_option maxHeartbeats 2000000 in
/-- **The `∂̄`-Bochner--Martinelli representation.**  For `g` of class `C¹` vanishing outside
`eucBall R`, `∫ bmKernel k · ∂̄_j g` equals `-∫_{eucBall (4R)} bmDbarKernel j k (g - g 0)` plus
the constant `bmC0 n j k` times `g 0`. -/
lemma bmPot_repr_aux {n : ℕ} (hn : 0 < n) (j k : Fin n) (g : (Fin n → ℂ) → ℂ) (R : ℝ)
    (hR : 0 < R) (hg : ContDiff ℝ 1 g) (hsupp : ∀ x, R ≤ eucNorm x → g x = 0) :
    (∫ x : Fin n → ℂ, bmKernel k x * dbarCoord j g x)
        + (∫ x in eucBall (n := n) (4 * R), bmDbarKernel j k x * (g x - g 0))
      = g 0 * bmC0 n j k := by
  obtain ⟨Mg, hMg0, hMg⟩ := exists_norm_sub_le_eucNorm (n := n) hR hg hsupp
  set χ : (Fin n → ℂ) → ℂ := eucCutoffC (n := n) R with hχdef
  have hχ : ContDiff ℝ 1 χ := by rw [hχdef]; exact contDiff_one_eucCutoffC hR
  have hχ0 : χ 0 = 1 := by rw [hχdef]; exact eucCutoffC_zero hR
  have hχsupp : ∀ x, R ≤ eucNorm x → χ x = 0 := fun x hx => by
    rw [hχdef]; exact eucCutoffC_eq_zero hR hx
  set χ1 : (Fin n → ℂ) → ℂ := eucCutoffC (n := n) 1 with hχ1def
  have hχ1 : ContDiff ℝ 1 χ1 := by rw [hχ1def]; exact contDiff_one_eucCutoffC (by norm_num)
  have hχ10 : χ1 0 = 1 := by rw [hχ1def]; exact eucCutoffC_zero (by norm_num)
  have hχ1supp : ∀ x, (1 : ℝ) ≤ eucNorm x → χ1 x = 0 := fun x hx => by
    rw [hχ1def]; exact eucCutoffC_eq_zero (by norm_num) hx
  set h : (Fin n → ℂ) → ℂ := fun y => g y - g 0 * χ y with hhdef
  have hh : ContDiff ℝ 1 h := by
    rw [hhdef]; exact hg.sub (contDiff_const.mul hχ)
  have hh0 : h 0 = 0 := by rw [hhdef]; simp [hχ0]
  have hhsupp : ∀ x, R ≤ eucNorm x → h x = 0 := fun x hx => by
    rw [hhdef]; simp [hsupp x hx, hχsupp x hx]
  have hMh : ∀ x, ‖h x‖ ≤ (Mg + ‖g 0‖ * (2 / R)) * eucNorm x := by
    intro x
    have hx1 : ‖(1 : ℂ) - χ x‖ ≤ (2 / R) * eucNorm x := by
      rw [norm_sub_rev, hχdef]
      exact norm_eucCutoffC_sub_one_le hR x
    have hdecomp : h x = (g x - g 0) + g 0 * ((1 : ℂ) - χ x) := by rw [hhdef]; ring
    calc ‖h x‖ = ‖(g x - g 0) + g 0 * ((1 : ℂ) - χ x)‖ := by rw [hdecomp]
      _ ≤ ‖g x - g 0‖ + ‖g 0 * ((1 : ℂ) - χ x)‖ := norm_add_le _ _
      _ ≤ Mg * eucNorm x + ‖g 0‖ * ((2 / R) * eucNorm x) := by
          refine add_le_add (hMg x) ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left hx1 (norm_nonneg _)
      _ = (Mg + ‖g 0‖ * (2 / R)) * eucNorm x := by ring
  have intAχ : Integrable (fun x : Fin n → ℂ => bmKernel k x * dbarCoord j χ x) :=
    integrable_bmKernel_mul_dbarCoord' hn j k hχ hχsupp
  have intAh : Integrable (fun x : Fin n → ℂ => bmKernel k x * dbarCoord j h x) :=
    integrable_bmKernel_mul_dbarCoord' hn j k hh hhsupp
  have intAχ1 : Integrable (fun x : Fin n → ℂ => bmKernel k x * dbarCoord j χ1 x) :=
    integrable_bmKernel_mul_dbarCoord' hn j k hχ1 hχ1supp
  have intBdχ : ∀ ρ : ℝ, IntegrableOn (fun x : Fin n → ℂ => bmDbarKernel j k x * (χ x - χ 0))
      (eucBall (n := n) ρ) volume := fun ρ =>
    integrableOn_bmDbarKernel_mul_of_le (f := fun x : Fin n → ℂ => χ x - χ 0) hn j k
      (hχ.sub contDiff_const) (by simp [hχ0]) (fun x => by
        rw [hχ0, hχdef]; exact norm_eucCutoffC_sub_one_le hR x) ρ
  have intBdh : ∀ ρ : ℝ, IntegrableOn (fun x : Fin n → ℂ => bmDbarKernel j k x * (h x - h 0))
      (eucBall (n := n) ρ) volume := fun ρ =>
    integrableOn_bmDbarKernel_mul_of_le (f := fun x : Fin n → ℂ => h x - h 0) hn j k
      (hh.sub contDiff_const) (by simp [hh0]) (fun x => by simpa [hh0] using hMh x) ρ
  have intBdχ1 : ∀ ρ : ℝ,
      IntegrableOn (fun x : Fin n → ℂ => bmDbarKernel j k x * (χ1 x - χ1 0))
        (eucBall (n := n) ρ) volume := fun ρ =>
    integrableOn_bmDbarKernel_mul_of_le (f := fun x : Fin n → ℂ => χ1 x - χ1 0) hn j k
      (hχ1.sub contDiff_const) (by simp [hχ10]) (fun x => by
        rw [hχ10, hχ1def]
        simpa using norm_eucCutoffC_sub_one_le (n := n) (R := 1) (by norm_num) x) ρ
  have hgdecomp : g = fun y => g 0 * χ y + h y := by
    funext y; rw [hhdef]; ring
  have hA : (∫ x : Fin n → ℂ, bmKernel k x * dbarCoord j g x)
      = g 0 * (∫ x : Fin n → ℂ, bmKernel k x * dbarCoord j χ x)
        + (∫ x : Fin n → ℂ, bmKernel k x * dbarCoord j h x) := by
    conv_lhs => rw [hgdecomp]
    exact bmA_add_smul (n := n) j k (g 0) hχ hh intAχ intAh
  have hB : (∫ x in eucBall (n := n) (4 * R), bmDbarKernel j k x * (g x - g 0))
      = g 0 * (∫ x in eucBall (n := n) (4 * R), bmDbarKernel j k x * (χ x - χ 0))
        + (∫ x in eucBall (n := n) (4 * R), bmDbarKernel j k x * (h x - h 0)) := by
    conv_lhs => rw [hgdecomp]
    exact bmBd_add_smul (n := n) j k (ρ := 4 * R) (g 0) hχ hh (intBdχ (4 * R)) (intBdh (4 * R))
  have hEh : (∫ x : Fin n → ℂ, bmKernel k x * dbarCoord j h x)
      + (∫ x in eucBall (n := n) (4 * R), bmDbarKernel j k x * (h x - h 0)) = 0 := by
    have hz := integral_bmKernel_mul_dbarCoord_of_zero hn j k (by linarith : (0 : ℝ) < 4 * R)
      hh hh0 (fun x hx => hhsupp x (le_trans (by linarith : R ≤ 4 * R) hx))
    have hfun : (fun x : Fin n → ℂ => bmDbarKernel j k x * (h x - h 0))
        = fun x : Fin n → ℂ => bmDbarKernel j k x * h x := by
      funext x; simp [hh0]
    rw [hfun, hz]; ring
  have hEχ : (∫ x : Fin n → ℂ, bmKernel k x * dbarCoord j χ x)
        + (∫ x in eucBall (n := n) (4 * R), bmDbarKernel j k x * (χ x - χ 0))
      = (∫ x : Fin n → ℂ, bmKernel k x * dbarCoord j χ1 x)
        + (∫ x in eucBall (n := n) (4 : ℝ), bmDbarKernel j k x * (χ1 x - χ1 0)) := by
    have hR4R : R ≤ 4 * R := by linarith
    have hRmax : R ≤ max (4 * R) 4 := le_trans hR4R (le_max_left (4 * R) 4)
    have h1max : (1 : ℝ) ≤ max (4 * R) 4 := le_trans (by norm_num) (le_max_right (4 * R) 4)
    have hρpos : (0 : ℝ) < max (4 * R) 4 := lt_of_lt_of_le (by norm_num) h1max
    have hχrad : (∫ x in eucBall (n := n) (4 * R), bmDbarKernel j k x * (χ x - χ 0))
        = ∫ x in eucBall (n := n) (max (4 * R) 4), bmDbarKernel j k x * (χ x - χ 0) := by
      rw [setIntegral_bmDbarKernel_sub_eq_of_le (n := n) hn j k (a := R) (b := 4 * R) hR hR4R
            hχsupp (intBdχ (4 * R)),
        setIntegral_bmDbarKernel_sub_eq_of_le (n := n) hn j k (a := R) (b := max (4 * R) 4) hR
            hRmax hχsupp (intBdχ (max (4 * R) 4))]
    have hχ1rad : (∫ x in eucBall (n := n) (4 : ℝ), bmDbarKernel j k x * (χ1 x - χ1 0))
        = ∫ x in eucBall (n := n) (max (4 * R) 4), bmDbarKernel j k x * (χ1 x - χ1 0) := by
      rw [setIntegral_bmDbarKernel_sub_eq_of_le (n := n) hn j k (a := 1) (b := 4) (by norm_num)
            (by norm_num) hχ1supp (intBdχ1 4),
        setIntegral_bmDbarKernel_sub_eq_of_le (n := n) hn j k (a := 1) (b := max (4 * R) 4)
            (by norm_num) h1max hχ1supp (intBdχ1 (max (4 * R) 4))]
    have hsub : ((∫ x : Fin n → ℂ, bmKernel k x * dbarCoord j χ x)
          - (∫ x : Fin n → ℂ, bmKernel k x * dbarCoord j χ1 x))
        + ((∫ x in eucBall (n := n) (max (4 * R) 4), bmDbarKernel j k x * (χ x - χ 0))
          - (∫ x in eucBall (n := n) (max (4 * R) 4),
              bmDbarKernel j k x * (χ1 x - χ1 0))) = 0 := by
      rw [← bmA_sub (n := n) j k hχ hχ1 intAχ intAχ1,
        ← bmBd_sub (n := n) j k (ρ := max (4 * R) 4) hχ hχ1
          (intBdχ (max (4 * R) 4)) (intBdχ1 (max (4 * R) 4))]
      have hz := integral_bmKernel_mul_dbarCoord_of_zero hn j k hρpos (hχ.sub hχ1)
        (by simp [hχ0, hχ10])
        (fun x hx => by
          have hxR : R ≤ eucNorm x := le_trans hRmax hx
          have hx1 : (1 : ℝ) ≤ eucNorm x := le_trans h1max hx
          simp [hχsupp x hxR, hχ1supp x hx1])
      have hfun : (fun x : Fin n → ℂ => bmDbarKernel j k x
            * ((fun y => χ y - χ1 y) x - (fun y => χ y - χ1 y) 0))
          = fun x : Fin n → ℂ => bmDbarKernel j k x * (χ x - χ1 x) := by
        funext x; simp [hχ0, hχ10]
      rw [hfun, hz]; ring
    have key : (∫ x : Fin n → ℂ, bmKernel k x * dbarCoord j χ x)
          + (∫ x in eucBall (n := n) (max (4 * R) 4), bmDbarKernel j k x * (χ x - χ 0))
        = (∫ x : Fin n → ℂ, bmKernel k x * dbarCoord j χ1 x)
          + (∫ x in eucBall (n := n) (max (4 * R) 4),
              bmDbarKernel j k x * (χ1 x - χ1 0)) := by
      have hkey : ((∫ x : Fin n → ℂ, bmKernel k x * dbarCoord j χ x)
            - (∫ x : Fin n → ℂ, bmKernel k x * dbarCoord j χ1 x))
          + ((∫ x in eucBall (n := n) (max (4 * R) 4), bmDbarKernel j k x * (χ x - χ 0))
            - (∫ x in eucBall (n := n) (max (4 * R) 4),
                bmDbarKernel j k x * (χ1 x - χ1 0))) = 0 := hsub
      have hsplit : (∫ x : Fin n → ℂ, bmKernel k x * dbarCoord j χ x)
            + (∫ x in eucBall (n := n) (max (4 * R) 4), bmDbarKernel j k x * (χ x - χ 0))
            - ((∫ x : Fin n → ℂ, bmKernel k x * dbarCoord j χ1 x)
              + (∫ x in eucBall (n := n) (max (4 * R) 4),
                  bmDbarKernel j k x * (χ1 x - χ1 0)))
          = ((∫ x : Fin n → ℂ, bmKernel k x * dbarCoord j χ x)
            - (∫ x : Fin n → ℂ, bmKernel k x * dbarCoord j χ1 x))
          + ((∫ x in eucBall (n := n) (max (4 * R) 4), bmDbarKernel j k x * (χ x - χ 0))
            - (∫ x in eucBall (n := n) (max (4 * R) 4),
                bmDbarKernel j k x * (χ1 x - χ1 0))) := by ring
      exact sub_eq_zero.mp (by rw [hsplit]; exact hkey)
    calc (∫ x : Fin n → ℂ, bmKernel k x * dbarCoord j χ x)
          + (∫ x in eucBall (n := n) (4 * R), bmDbarKernel j k x * (χ x - χ 0))
        = (∫ x : Fin n → ℂ, bmKernel k x * dbarCoord j χ x)
          + (∫ x in eucBall (n := n) (max (4 * R) 4),
              bmDbarKernel j k x * (χ x - χ 0)) := by rw [hχrad]
      _ = (∫ x : Fin n → ℂ, bmKernel k x * dbarCoord j χ1 x)
          + (∫ x in eucBall (n := n) (max (4 * R) 4),
              bmDbarKernel j k x * (χ1 x - χ1 0)) := key
      _ = (∫ x : Fin n → ℂ, bmKernel k x * dbarCoord j χ1 x)
          + (∫ x in eucBall (n := n) (4 : ℝ),
              bmDbarKernel j k x * (χ1 x - χ1 0)) := by rw [← hχ1rad]
  calc (∫ x : Fin n → ℂ, bmKernel k x * dbarCoord j g x)
        + (∫ x in eucBall (n := n) (4 * R), bmDbarKernel j k x * (g x - g 0))
      = (g 0 * (∫ x : Fin n → ℂ, bmKernel k x * dbarCoord j χ x)
          + (∫ x : Fin n → ℂ, bmKernel k x * dbarCoord j h x))
        + (g 0 * (∫ x in eucBall (n := n) (4 * R), bmDbarKernel j k x * (χ x - χ 0))
          + (∫ x in eucBall (n := n) (4 * R), bmDbarKernel j k x * (h x - h 0))) := by
          rw [hA, hB]
    _ = g 0 * ((∫ x : Fin n → ℂ, bmKernel k x * dbarCoord j χ x)
          + (∫ x in eucBall (n := n) (4 * R), bmDbarKernel j k x * (χ x - χ 0)))
        + ((∫ x : Fin n → ℂ, bmKernel k x * dbarCoord j h x)
          + (∫ x in eucBall (n := n) (4 * R), bmDbarKernel j k x * (h x - h 0))) := by ring
    _ = g 0 * ((∫ x : Fin n → ℂ, bmKernel k x * dbarCoord j χ x)
          + (∫ x in eucBall (n := n) (4 * R), bmDbarKernel j k x * (χ x - χ 0))) := by
          rw [hEh]; ring
    _ = g 0 * bmC0 n j k := by rw [hEχ, hχ1def]; rfl

theorem bmPot_repr {n : ℕ} (hn : 0 < n) : ∃ c : Fin n → Fin n → ℂ,
  (∀ (j k : Fin n) (g : (Fin n → ℂ) → ℂ) (R : ℝ), 0 < R → ContDiff ℝ 1 g →
    (∀ x, R ≤ eucNorm x → g x = 0) →
    ∫ x, bmKernel k x * Work.CR.Flat.dCoord j g x
      = -∫ x in eucBall (4 * R), bmDzKernel j k x * (g x - g 0)) ∧
  (∀ (j k : Fin n) (g : (Fin n → ℂ) → ℂ) (R : ℝ), 0 < R → ContDiff ℝ 1 g →
    (∀ x, R ≤ eucNorm x → g x = 0) →
    ∫ x, bmKernel k x * Work.CR.Flat.dbarCoord j g x
      = (-∫ x in eucBall (4 * R), bmDbarKernel j k x * (g x - g 0)) - c j k * g 0) := by
  refine ⟨fun j k => -bmC0 n j k, ?_, ?_⟩
  · intro j k g R hR hg hsupp
    exact bmCz.integral_bmKernel_mul_dCoord hn j k g R hR hg hsupp
  · intro j k g R hR hg hsupp
    have h := bmPot_repr_aux hn j k g R hR hg hsupp
    have h1 : (∫ x : Fin n → ℂ, bmKernel k x * dbarCoord j g x)
        = g 0 * bmC0 n j k
          - ∫ x in eucBall (n := n) (4 * R), bmDbarKernel j k x * (g x - g 0) :=
      (eq_sub_iff_add_eq).mpr h
    rw [h1]
    ring

end Work.NN.Core
