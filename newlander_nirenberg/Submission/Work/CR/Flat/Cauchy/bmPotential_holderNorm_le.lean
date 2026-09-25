import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmDefs
import Submission.Work.CR.Flat.Cauchy.bmSetup
import Submission.Work.CR.Flat.Cauchy.bmCZDefs
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Cauchy.fderiv_bmPotential
import Submission.Work.CR.Flat.Cauchy.bmPot_dbarCoord
import Submission.Work.CR.Flat.Cauchy.bmPotential_contDiff_one
import Submission.Work.CR.Flat.Cauchy.bmPotential_solves_dbar
import Submission.Work.CR.Flat.Cauchy.bmKernel_divergence_aux
import Submission.Work.CR.Flat.Cauchy.bmCz.dCoord_bmKernel
import Submission.Work.CR.Flat.Cauchy.bmCz.norm_bmDzKernel_sub_le
import Submission.Work.CR.Flat.Cauchy.bmCz.integral_bmDzKernel_eucShell_eq_zero
import Submission.Work.CR.Flat.Cauchy.bmCz.abs_eucNorm_sub_le
import Submission.Work.CR.Flat.Cauchy.bmCz.exists_lipschitz_eucCutoff
import Submission.Work.CR.Flat.Cauchy.bmCz.eucRadialBound
import Submission.Work.CR.Flat.Cauchy.bmCz.hasFDerivAt_bmKernel
import Submission.Work.CR.Flat.Cauchy.bmCz.bmDbarKernel_shell_eq_zero
import Submission.Work.CR.Flat.Cauchy.bmCz.norm_bmDbarKernel_sub_le
import Submission.Work.CR.Flat.Cauchy.bmCz.czKernel_holderBound
import Submission.Work.CR.Flat.Cauchy.bmCz.integral_bmKernel_mul_dCoord
import Submission.Work.CR.Flat.Cauchy.bmCz.integral_bmKernel_mul_dbarCoord
import Submission.Work.CR.Flat.Cauchy.bmCz.bmKernel_decay_le
import Submission.Work.CR.Flat.Cauchy.bmCz.bmPot_dCoord
import Submission.Work.CR.Flat.Cauchy.bmCz.norm_fderiv_le_sum_wirtinger
import Submission.Work.CR.Flat.Cauchy.bmCz.norm_fderiv_sub_le_sum_wirtinger

noncomputable section

open scoped NNReal ENNReal
open MeasureTheory Set

namespace Work.CR.Flat.Cauchy

/-! ## Support lemmas for the half-size polydisc -/

/-- If `∑ j, r j ≤ ‖y‖` (sup norm) then some coordinate of `y` is at least `r` there. -/
lemma exists_coord_le_of_sum_le_norm {n : ℕ} (hn : 0 < n) {r : Fin n → ℝ} {y : Fin n → ℂ}
    (h : ∑ j, r j ≤ ‖y‖) : ∃ k, r k ≤ ‖y k‖ := by
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  have hsum : ∑ j, ‖y j‖ < ∑ j, r j :=
    Finset.sum_lt_sum (fun j _ => le_of_lt (hcon j))
      ⟨⟨0, hn⟩, Finset.mem_univ _, hcon ⟨0, hn⟩⟩
  have hle : ‖y‖ ≤ ∑ j, ‖y j‖ := by
    rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ => norm_nonneg _)]
    exact fun j => Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ j)
  linarith

/-- If `√n · ∑ j, r j ≤ eucNorm y` then some coordinate of `y` is at least `r` there. -/
lemma exists_coord_le_of_sqrt_mul_sum_le_eucNorm {n : ℕ} (hn : 0 < n) {r : Fin n → ℝ}
    (hr : ∀ j, 0 < r j) {y : Fin n → ℂ}
    (h : Real.sqrt n * (∑ j, r j) ≤ eucNorm y) : ∃ k, r k ≤ ‖y k‖ := by
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  have hsq : ∑ j, ‖y j‖ ^ 2 < ∑ j, (r j) ^ 2 :=
    Finset.sum_lt_sum
      (fun j _ => by nlinarith [norm_nonneg (y j), hcon j, hr j])
      ⟨⟨0, hn⟩, Finset.mem_univ _, by
        nlinarith [norm_nonneg (y ⟨0, hn⟩), hcon ⟨0, hn⟩, hr ⟨0, hn⟩]⟩
  have hle : ∑ j, (r j) ^ 2 ≤ (∑ j, r j) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [pow_two]
    exact Finset.single_le_sum
      (fun k _ => mul_nonneg (le_of_lt (hr j)) (le_of_lt (hr k))) (Finset.mem_univ j)
  have hsumpos : 0 < ∑ j, r j :=
    Finset.sum_pos (fun j _ => hr j) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hlt : eucNorm y < ∑ j, r j := by
    have h2 : eucNorm y ^ 2 < (∑ j, r j) ^ 2 := by
      rw [eucNorm_sq]; linarith
    nlinarith [h2, eucNorm_nonneg y, hsumpos]
  have hge : ∑ j, r j ≤ eucNorm y := by
    have h1 : 1 ≤ Real.sqrt n := by
      have h2 : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
      have h3 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [Real.sqrt_nonneg n]
    nlinarith
  linarith

/-! ## Integrability of the euclidean power over a ball -/

lemma integrableOn_norm_rpow_ball_pi {n : ℕ} (hn : 0 < n) {s : ℝ}
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

/-! ## A `norm_setIntegral_le_of_norm_le` helper -/

/-! ## Integrability of the potential integrand -/

/-- A function vanishing outside a euclidean ball has compact support. -/
lemma isCompact_eucClosedBall {n : ℕ} (R : ℝ) : IsCompact (eucClosedBall (n := n) R) := by
  refine (isCompact_closedBall (0 : Fin n → ℂ) R).of_isClosed_subset
    (isClosed_le continuous_eucNorm continuous_const) ?_
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  exact (pi_norm_le_eucNorm x).trans hx

lemma hasCompactSupport_of_eucNorm {n : ℕ} {g : (Fin n → ℂ) → ℂ} {R : ℝ}
    (hg : ∀ x, R ≤ eucNorm x → g x = 0) : HasCompactSupport g := by
  refine (isCompact_eucClosedBall R).of_isClosed_subset (isClosed_tsupport g) ?_
  rw [tsupport]
  refine closure_minimal ?_ (isCompact_eucClosedBall R).isClosed
  intro x hx
  by_contra hcon
  exact hx (hg x (le_of_lt (lt_of_not_ge hcon)))

lemma integrable_bmKernel_mul {n : ℕ} (hn : 0 < n) (j : Fin n) {g : (Fin n → ℂ) → ℂ}
    (hg : Continuous g) (hgs : HasCompactSupport g) :
    Integrable (fun x => bmKernel j x * g x) := by
  have h := (locallyIntegrable_bmKernel hn j).integrable_smul_left_of_hasCompactSupport hg hgs
  simpa only [smul_eq_mul, mul_comm] using h

lemma integrableOn_bmKernel_mul {n : ℕ} (hn : 0 < n) (j : Fin n) {g : (Fin n → ℂ) → ℂ}
    {S : ℝ} (hg : Continuous g) (hgs : HasCompactSupport g) :
    IntegrableOn (fun x => bmKernel j x * g x) (eucBall S) :=
  (integrable_bmKernel_mul hn j hg hgs).integrableOn


/-! ## The potential as an integral over the half-size window -/

/-- If `f j (z + ·)` vanishes off `eucBall S` then the `j`-th term of the potential is an integral
over that ball. -/
lemma bmPotential_eq_sum_ball {n : ℕ} {f : Fin n → (Fin n → ℂ) → ℂ} {S : ℝ}
    {z : Fin n → ℂ} (h : ∀ j x, S ≤ eucNorm x → f j (z + x) = 0) :
    bmPotential f z = ∑ j, ∫ x in eucBall S, bmKernel j x * f j (z + x) := by
  rw [bmPotential_eq_bmPot]
  simp only [bmPot]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := eucBall S) (f := fun x => bmKernel j x * f j (z + x)) (fun x hx => ?_)]
  rw [h j x (not_lt.mp hx), mul_zero]

/-- The same for the difference of two translates. -/
lemma bmPotential_sub_eq_sum_ball {n : ℕ} (hn : 0 < n) {f : Fin n → (Fin n → ℂ) → ℂ}
    {S : ℝ} {z z' : Fin n → ℂ}
    (h : ∀ j x, S ≤ eucNorm x → f j (z + x) = 0)
    (h' : ∀ j x, S ≤ eucNorm x → f j (z' + x) = 0)
    (hf : ∀ j, ContDiff ℝ 1 (f j)) :
    bmPotential f z - bmPotential f z'
      = ∑ j, ∫ x in eucBall S, bmKernel j x * (f j (z + x) - f j (z' + x)) := by
  have hcont : ∀ j, Continuous (fun x => f j (z + x)) := fun j =>
    (hf j).continuous.comp (continuous_const.add continuous_id)
  have hcont' : ∀ j, Continuous (fun x => f j (z' + x)) := fun j =>
    (hf j).continuous.comp (continuous_const.add continuous_id)
  have hint : ∀ j, IntegrableOn (fun x => bmKernel j x * f j (z + x)) (eucBall S) := fun j =>
    integrableOn_bmKernel_mul hn j (hcont j) (hasCompactSupport_of_eucNorm (h j))
  have hint' : ∀ j, IntegrableOn (fun x => bmKernel j x * f j (z' + x)) (eucBall S) := fun j =>
    integrableOn_bmKernel_mul hn j (hcont' j) (hasCompactSupport_of_eucNorm (h' j))
  rw [bmPotential_eq_sum_ball h, bmPotential_eq_sum_ball h',
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← integral_sub (hint j) (hint' j)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  ring

/-! ## The `0`-th iterated derivative -/

private lemma norm_iteratedFDerivWithin_zero_sub {n : ℕ} (f : (Fin n → ℂ) → ℂ) (Ω : Set (Fin n → ℂ))
    (x y : Fin n → ℂ) :
    ‖iteratedFDerivWithin ℝ 0 f Ω x - iteratedFDerivWithin ℝ 0 f Ω y‖ = ‖f x - f y‖ := by
  refine le_antisymm ?_ ?_
  · refine ContinuousMultilinearMap.opNorm_le_bound (M := ‖f x - f y‖) (norm_nonneg _) fun m => ?_
    rw [ContinuousMultilinearMap.sub_apply, iteratedFDerivWithin_zero_apply,
      iteratedFDerivWithin_zero_apply]
    rw [show (∏ i : Fin 0, ‖m i‖) = 1 from by simp, mul_one]
  · have h := ContinuousMultilinearMap.le_opNorm
      (iteratedFDerivWithin ℝ 0 f Ω x - iteratedFDerivWithin ℝ 0 f Ω y) (0 : Fin 0 → Fin n → ℂ)
    simp only [ContinuousMultilinearMap.sub_apply, iteratedFDerivWithin_zero_apply] at h
    rw [show (∏ i : Fin 0, ‖(0 : Fin 0 → Fin n → ℂ) i‖) = 1 from by simp, mul_one] at h
    exact h

/-- `∂_j` of a translate. -/
lemma dCoord_comp_add' {n : ℕ} (j : Fin n) (g : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    Work.CR.Flat.dCoord j (fun x : Fin n → ℂ => g (z + x))
      = fun x => Work.CR.Flat.dCoord j g (z + x) := by
  funext x
  simp only [Work.CR.Flat.dCoord, fderiv_comp_add_left]

/-- `∂̄_j` of a translate. -/
lemma dbarCoord_comp_add' {n : ℕ} (j : Fin n) (g : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    Work.CR.Flat.dbarCoord j (fun x : Fin n → ℂ => g (z + x))
      = fun x => Work.CR.Flat.dbarCoord j g (z + x) := by
  funext x
  simp only [Work.CR.Flat.dbarCoord, fderiv_comp_add_left]

/-- Exponent conversion: `a ^ (-(2n+1)) = 1 / a ^ (2n+1)`. -/
lemma rpow_neg_two_mul_add_one {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    a ^ (-(2 * (n : ℝ) + 1)) = 1 / a ^ (2 * n + 1) := by
  rw [show -(2 * (n : ℝ) + 1) = -(((2 * n + 1 : ℕ)) : ℝ) by push_cast; ring]
  rw [Real.rpow_neg ha, Real.rpow_natCast, one_div]

/-- Unfolding `holderNorm` at `k = 1`. -/
lemma holderNorm_one_eq_pi {n : ℕ} (α : ℝ) (f : (Fin n → ℂ) → ℂ) (Ω : Set (Fin n → ℂ)) :
    holderNorm 1 α f Ω
      = (iterDerivNorm 0 f Ω + holderSeminorm 0 α f Ω)
        + (iterDerivNorm 1 f Ω + holderSeminorm 1 α f Ω) := by
  rw [holderNorm, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

set_option maxHeartbeats 1600000 in
theorem bmPotential_holderNorm_le {n : ℕ} (hn : 0 < n) {c : Fin n → ℂ} {r : Fin n → ℝ}
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (hr : ∀ j, 0 < r j) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Fin n → (Fin n → ℂ) → ℂ, (∀ j, ContDiff ℝ 1 (f j)) →
      (∀ j z, (∃ k, r k / 2 ≤ ‖z k - c k‖) → f j z = 0) →
      holderNorm 1 α (bmPotential f) (polydisc c (fun j => r j / 2))
        ≤ ENNReal.ofReal C * ∑ j, holderNorm 0 α (f j) Set.univ := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  -- ### the two radii and the `L¹`-mass constant
  set Reuc : ℝ := ∑ k, r k with hReucdef
  set Rsup : ℝ := ∑ k, (r k / 2 + ‖c k‖) with hRsupdef
  have hReucpos : 0 < Reuc := by
    rw [hReucdef]
    exact Finset.sum_pos (fun j _ => hr j) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hRsuppos : 0 < Rsup := by
    rw [hRsupdef]
    refine Finset.sum_pos (fun j _ => ?_) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    have h := hr j; positivity
  set κ : ℝ := (Module.finrank ℝ (Fin n → ℂ) : ℝ) * (volume : Measure (Fin n → ℂ)).real
      (Metric.ball (0 : Fin n → ℂ) 1) * Reuc with hκdef
  have hκpos : 0 < κ := by
    rw [hκdef]
    refine mul_pos (mul_pos ?_ ?_) hReucpos
    · exact_mod_cast Module.finrank_pos
    · rw [Measure.real_def]
      exact ENNReal.toReal_pos (ne_of_gt (Metric.measure_ball_pos volume 0 one_pos))
        (ne_of_lt MeasureTheory.measure_ball_lt_top)
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
  have hP1dz : ∀ k j : Fin n, ∀ x : Fin n → ℂ, x ≠ 0 →
      ‖bmDzKernel k j x‖ ≤ A / (eucNorm x) ^ (2 * n) := by
    intro k j x hx
    exact (hAdecDz k j x hx).trans
      (div_le_div_of_nonneg_right hAle (pow_nonneg (eucNorm_nonneg x) _))
  have hP1dbar : ∀ j k : Fin n, ∀ x : Fin n → ℂ, x ≠ 0 →
      ‖bmDbarKernel j k x‖ ≤ A / (eucNorm x) ^ (2 * n) := by
    intro j k x hx
    exact (hAdecDbar j k x hx).trans
      (div_le_div_of_nonneg_right hAle (pow_nonneg (eucNorm_nonneg x) _))
  have hP2dz : ∀ k j : Fin n, ∀ x h : Fin n → ℂ, 2 * eucNorm h ≤ eucNorm x →
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
  have hP2dbar : ∀ j k : Fin n, ∀ x h : Fin n → ℂ, 2 * eucNorm h ≤ eucNorm x →
      ‖bmDbarKernel j k (x - h) - bmDbarKernel j k x‖
        ≤ A * eucNorm h / (eucNorm x) ^ (2 * n + 1) := by
    intro j k x h hxh
    exact (hCp3 j k x h hxh).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC3le (eucNorm_nonneg h))
        (pow_nonneg (eucNorm_nonneg x) _))
  have hH2dz : ∀ k j : Fin n, ∀ a b : ℝ, 0 < a → a < b →
      ∫ x in eucShell a b, bmDzKernel k j x = 0 :=
    fun k j a b ha _ => bmCz.integral_bmDzKernel_eucShell_eq_zero (k := k) (j := j) (ρ := b) ha
  have hH2dbar : ∀ j k : Fin n, ∀ a b : ℝ, 0 < a → a < b →
      ∫ x in eucShell a b, bmDbarKernel j k x = 0 :=
    fun j k a b ha _ => bmCz.bmDbarKernel_shell_eq_zero hn (j := j) (k := k) (b := b) ha
  -- ### the Calderón-Zygmund constants, uniformly over the finitely many kernels
  have hCZdz : ∀ p : Fin n × Fin n, ∃ C : ℝ, 0 < C ∧ ∀ (K : ℝ), 0 ≤ K →
      ∀ g : (Fin n → ℂ) → ℂ,
      (∀ x y : Fin n → ℂ, ‖g x - g y‖ ≤ K * ‖x - y‖ ^ α) →
      (∀ x : Fin n → ℂ, Reuc ≤ eucNorm x → g x = 0) →
      (∀ z : Fin n → ℂ,
        ‖∫ x in eucBall (4 * Reuc), bmDzKernel p.1 p.2 x * (g (z + x) - g z)‖ ≤ C * K) ∧
      (∀ z z' : Fin n → ℂ,
        ‖(∫ x in eucBall (4 * Reuc), bmDzKernel p.1 p.2 x * (g (z + x) - g z))
            - (∫ x in eucBall (4 * Reuc), bmDzKernel p.1 p.2 x * (g (z' + x) - g z'))‖
          ≤ C * K * ‖z - z'‖ ^ α) := by
    intro p
    exact bmCz.czKernel_holderBound hn hα hα1 hReucpos (hmeasDz p.1 p.2) hApos
      (hP1dz p.1 p.2) (hP2dz p.1 p.2) (hH2dz p.1 p.2)
  have hCZdbar : ∀ p : Fin n × Fin n, ∃ C : ℝ, 0 < C ∧ ∀ (K : ℝ), 0 ≤ K →
      ∀ g : (Fin n → ℂ) → ℂ,
      (∀ x y : Fin n → ℂ, ‖g x - g y‖ ≤ K * ‖x - y‖ ^ α) →
      (∀ x : Fin n → ℂ, Reuc ≤ eucNorm x → g x = 0) →
      (∀ z : Fin n → ℂ,
        ‖∫ x in eucBall (4 * Reuc), bmDbarKernel p.1 p.2 x * (g (z + x) - g z)‖ ≤ C * K) ∧
      (∀ z z' : Fin n → ℂ,
        ‖(∫ x in eucBall (4 * Reuc), bmDbarKernel p.1 p.2 x * (g (z + x) - g z))
            - (∫ x in eucBall (4 * Reuc), bmDbarKernel p.1 p.2 x * (g (z' + x) - g z'))‖
          ≤ C * K * ‖z - z'‖ ^ α) := by
    intro p
    exact bmCz.czKernel_holderBound hn hα hα1 hReucpos (hmeasDbar p.1 p.2) hApos
      (hP1dbar p.1 p.2) (hP2dbar p.1 p.2) (hH2dbar p.1 p.2)
  choose Cdz hCdz using hCZdz
  choose Cdbar hCZdbar using hCZdbar
  obtain ⟨cc, hcc⟩ := bmCz.integral_bmKernel_mul_dbarCoord hn
  set Cs : ℝ := (∑ p : Fin n × Fin n, Cdz p) + (∑ p : Fin n × Fin n, Cdbar p) with hCsdef
  set Cc : ℝ := ∑ p : Fin n × Fin n, ‖cc p.1 p.2‖ with hCcdef
  have hCs0 : 0 ≤ Cs := by
    rw [hCsdef]
    exact add_nonneg (Finset.sum_nonneg fun p _ => (hCdz p).1.le)
      (Finset.sum_nonneg fun p _ => (hCZdbar p).1.le)
  have hCc0 : 0 ≤ Cc := by
    rw [hCcdef]; exact Finset.sum_nonneg fun p _ => norm_nonneg _
  set B : ℝ := 2 * (n : ℝ) * (2 * Cs + Cc) with hBdef
  have hB0 : 0 ≤ B := by
    rw [hBdef]; positivity
  refine ⟨κ + 2 * B, by positivity, ?_⟩
  intro f hf hsupp
  -- ### support of `f` in the two balls
  have hsuppSup : ∀ j x, Rsup ≤ ‖x‖ → f j x = 0 := by
    intro j x hx
    refine hsupp j x ?_
    by_contra hcon
    simp only [not_exists, not_le] at hcon
    have hpt : ∀ k, ‖x k‖ < r k / 2 + ‖c k‖ := by
      intro k
      have h := norm_add_le (x k - c k) (c k)
      have h2 : ‖x k‖ ≤ ‖x k - c k‖ + ‖c k‖ := by simpa [sub_add_cancel] using h
      have h3 := hcon k
      linarith
    have h1 : ∑ k, ‖x k‖ < ∑ k, (r k / 2 + ‖c k‖) :=
      Finset.sum_lt_sum (fun k _ => le_of_lt (hpt k))
        ⟨⟨0, hn⟩, Finset.mem_univ _, hpt ⟨0, hn⟩⟩
    have h2 : ‖x‖ ≤ ∑ k, ‖x k‖ := by
      rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun k _ => norm_nonneg _)]
      exact fun k => Finset.single_le_sum (fun k _ => norm_nonneg _) (Finset.mem_univ k)
    rw [hRsupdef] at hx
    linarith
  have hsuppE : ∀ z : Fin n → ℂ, (∀ k, ‖z k - c k‖ < r k / 2) → ∀ j x,
      Reuc ≤ eucNorm x → f j (z + x) = 0 := by
    intro z hz j x hx
    refine hsupp j (z + x) ?_
    by_contra hcon
    simp only [not_exists, not_le] at hcon
    have hpt : ∀ k, ‖x k‖ < r k := by
      intro k
      have h := norm_add_le (x k + (z k - c k)) (-(z k - c k))
      have hx : (x k + (z k - c k)) + (-(z k - c k)) = x k := by ring
      rw [hx, norm_neg] at h
      have h2 : ‖x k‖ ≤ ‖x k + (z k - c k)‖ + ‖z k - c k‖ := h
      have h3 : ‖x k + (z k - c k)‖ = ‖(z + x) k - c k‖ := by
        rw [show x k + (z k - c k) = (z + x) k - c k from by rw [Pi.add_apply]; ring]
      rw [h3] at h2
      have h4 := hcon k
      have h5 := hz k
      linarith
    have hsq : ∑ k, ‖x k‖ ^ 2 < ∑ k, (r k) ^ 2 :=
      Finset.sum_lt_sum
        (fun k _ => by nlinarith [norm_nonneg (x k), hpt k, hr k])
        ⟨⟨0, hn⟩, Finset.mem_univ _, by
          nlinarith [norm_nonneg (x ⟨0, hn⟩), hpt ⟨0, hn⟩, hr ⟨0, hn⟩]⟩
    have hle : ∑ k, (r k) ^ 2 ≤ (∑ k, r k) ^ 2 := by
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [pow_two]
      exact Finset.single_le_sum
        (fun l _ => mul_nonneg (le_of_lt (hr k)) (le_of_lt (hr l))) (Finset.mem_univ k)
    have hlt : eucNorm x < Reuc := by
      have h2 : eucNorm x ^ 2 < (∑ k, r k) ^ 2 := by rw [eucNorm_sq]; linarith
      rw [hReucdef]
      nlinarith [h2, eucNorm_nonneg x, hReucpos]
    linarith
  -- ### the finite part: extract the sup norm `A'` and the Hölder constant `K'`
  by_cases htop : ∑ j, holderNorm 0 α (f j) Set.univ = ⊤
  · rw [htop, ENNReal.mul_top (by rw [ENNReal.ofReal_ne_zero_iff]; positivity)]
    exact le_top
  · have hfin : ∀ j, holderNorm 0 α (f j) Set.univ ≠ ⊤ := by
      intro j hj
      have hle : holderNorm 0 α (f j) Set.univ ≤ ∑ i, holderNorm 0 α (f i) Set.univ :=
        Finset.single_le_sum (f := fun i => holderNorm 0 α (f i) Set.univ)
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
          rwa [norm_iteratedFDerivWithin_zero_sub] at h
        rw [← hK'eq j] at h1
        have h2 : ‖f j x - f j y‖ / ‖x - y‖ ^ α ≤ K' j :=
          (ENNReal.ofReal_le_ofReal_iff (hK'0 j)).mp h1
        have h3 : 0 < ‖x - y‖ ^ α :=
          Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
        rwa [div_le_iff₀ h3] at h2
    have hsa : 0 ≤ ∑ j, A' j := Finset.sum_nonneg fun j _ => hA'0 j
    have hsk : 0 ≤ ∑ j, K' j := Finset.sum_nonneg fun j _ => hK'0 j
    set P : Set (Fin n → ℂ) := polydisc c (fun j => r j / 2) with hPdef
    have hPopen : IsOpen P := hPdef ▸ isOpen_polydisc c _
    -- ### the `L¹`-mass of the kernel on the window
    have hintE : IntegrableOn (fun x : Fin n → ℂ => ‖x‖ ^ (1 - 2 * (n : ℝ))) (eucBall Reuc) :=
      IntegrableOn.mono_set (integrableOn_norm_rpow_ball_pi hn (by linarith) hReucpos)
        eucBall_subset_ball
    have hκbd : ∫ x in (eucBall Reuc : Set (Fin n → ℂ)), ‖x‖ ^ (1 - 2 * (n : ℝ)) ≤ κ := by
      refine (setIntegral_mono_set (integrableOn_norm_rpow_ball_pi hn (by linarith) hReucpos)
        (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg x) _)
        (Filter.Eventually.of_forall fun x hx => eucBall_subset_ball hx)).trans (le_of_eq ?_)
      rw [bmCz.integral_norm_rpow_ball hn (by linarith) hReucpos, hκdef]
      rw [show (Module.finrank ℝ (Fin n → ℂ) : ℝ) = 2 * (n : ℝ) by
        rw [Module.finrank_pi_fintype]
        simp [Complex.finrank_real_complex, Finset.sum_const, nsmul_eq_mul]
        ring]
      rw [show (1 - 2 * (n : ℝ)) + 2 * (n : ℝ) = 1 by ring, Real.rpow_one, div_one]
    -- ### (i) the supremum of the potential
    have hT0 : iterDerivNorm 0 (bmPotential f) P ≤ ENNReal.ofReal (κ * ∑ j, A' j) := by
      rw [iterDerivNorm_zero]
      refine iSup₂_le fun p hp => ?_
      have hp' : ∀ k, ‖p k - c k‖ < r k / 2 := hp
      refine ENNReal.ofReal_le_ofReal ?_
      rw [bmPotential_eq_sum_ball (h := fun j x hx => hsuppE p hp' j x hx)]
      refine (norm_sum_le _ _).trans ?_
      have hstep : ∀ j : Fin n, ‖∫ x in eucBall Reuc, bmKernel j x * f j (p + x)‖
          ≤ A' j * κ := by
        intro j
        have hdom : IntegrableOn (fun x : Fin n → ℂ => A' j * ‖x‖ ^ (1 - 2 * (n : ℝ)))
            (eucBall Reuc) := hintE.const_mul (A' j)
        refine (norm_setIntegral_le_of_norm_le' (measurableSet_eucBall Reuc) hdom ?_).trans ?_
        · intro x _
          rw [norm_mul]
          calc ‖bmKernel j x‖ * ‖f j (p + x)‖ ≤ ‖x‖ ^ (1 - 2 * (n : ℝ)) * A' j :=
                mul_le_mul (norm_bmKernel_le j x) (hfA j (p + x)) (norm_nonneg _)
                  (Real.rpow_nonneg (norm_nonneg x) _)
            _ = A' j * ‖x‖ ^ (1 - 2 * (n : ℝ)) := by ring
        · rw [integral_const_mul]
          exact mul_le_mul_of_nonneg_left hκbd (hA'0 j)
      calc ∑ j, ‖∫ x in eucBall Reuc, bmKernel j x * f j (p + x)‖
          ≤ ∑ j, A' j * κ := Finset.sum_le_sum fun j _ => hstep j
        _ = (∑ j, A' j) * κ := (Finset.sum_mul _ _ _).symm
        _ = κ * ∑ j, A' j := by ring
    -- ### (ii) the Hölder seminorm of the potential
    have hT1 : holderSeminorm 0 α (bmPotential f) P ≤ ENNReal.ofReal (κ * ∑ j, K' j) := by
      refine iSup₂_le fun p hp => iSup₂_le fun q hq => iSup_le fun hpq => ?_
      have hp' : ∀ k, ‖p k - c k‖ < r k / 2 := hp
      have hq' : ∀ k, ‖q k - c k‖ < r k / 2 := hq
      rw [norm_iteratedFDerivWithin_zero_sub]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [bmPotential_sub_eq_sum_ball hn (hsuppE p hp') (hsuppE q hq') hf]
      have h3 : 0 < ‖p - q‖ ^ α :=
        Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hpq)) α
      rw [div_le_iff₀ h3]
      have hstep : ∀ j : Fin n,
          ‖∫ x in eucBall Reuc, bmKernel j x * (f j (p + x) - f j (q + x))‖
            ≤ K' j * ‖p - q‖ ^ α * κ := by
        intro j
        have hdom : IntegrableOn (fun x : Fin n → ℂ => K' j * ‖p - q‖ ^ α
            * ‖x‖ ^ (1 - 2 * (n : ℝ))) (eucBall Reuc) := hintE.const_mul (K' j * ‖p - q‖ ^ α)
        refine (norm_setIntegral_le_of_norm_le' (measurableSet_eucBall Reuc) hdom ?_).trans ?_
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
          exact mul_le_mul_of_nonneg_left hκbd
            (mul_nonneg (hK'0 j) (Real.rpow_nonneg (norm_nonneg _) _))
      calc ‖∑ j, ∫ x in eucBall Reuc, bmKernel j x * (f j (p + x) - f j (q + x))‖
          ≤ ∑ j, K' j * ‖p - q‖ ^ α * κ :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hstep j)
        _ = (∑ j, K' j) * ‖p - q‖ ^ α * κ := by rw [← Finset.sum_mul, ← Finset.sum_mul]
        _ = κ * (∑ j, K' j) * ‖p - q‖ ^ α := by ring
    have hfKshift : ∀ j (p : Fin n → ℂ) x y,
        ‖f j (p + x) - f j (p + y)‖ ≤ K' j * ‖x - y‖ ^ α := by
      intro j p x y
      have h := hfK j (p + x) (p + y)
      rwa [show (p + x) - (p + y) = x - y from by ring] at h
    -- ### the derivative representations
    have hcont1 : ∀ (j : Fin n) (z : Fin n → ℂ), ContDiff ℝ 1 (fun x => f j (z + x)) :=
      fun j z => (hf j).comp (contDiff_const.add contDiff_id)
    have hdCoord : ∀ k : Fin n, ∀ p : Fin n → ℂ, (∀ m, ‖p m - c m‖ < r m / 2) →
        Work.CR.Flat.dCoord k (bmPotential f) p
          = -∑ j, ∫ x in eucBall (4 * Reuc), bmDzKernel k j x * (f j (p + x) - f j p) := by
      intro k p hp
      have h1 : Work.CR.Flat.dCoord k (bmPotential f) p
          = ∑ j, ∫ x, bmKernel j x * Work.CR.Flat.dCoord k (f j) (p + x) := by
        rw [funext (fun w => bmPotential_eq_bmPot f w)]
        exact bmCz.bmPot_dCoord hn hf hRsuppos hsuppSup k p
      rw [h1]
      have hper : ∀ j : Fin n, ∫ x, bmKernel j x * Work.CR.Flat.dCoord k (f j) (p + x)
          = -∫ x in eucBall (4 * Reuc), bmDzKernel k j x * (f j (p + x) - f j p) := by
        intro j
        have hcomp : (∫ x, bmKernel j x * Work.CR.Flat.dCoord k (fun y => f j (p + y)) x)
            = ∫ x, bmKernel j x * Work.CR.Flat.dCoord k (f j) (p + x) :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => by
            show bmKernel j x * Work.CR.Flat.dCoord k (fun y => f j (p + y)) x
              = bmKernel j x * Work.CR.Flat.dCoord k (f j) (p + x)
            rw [show Work.CR.Flat.dCoord k (fun y => f j (p + y)) x
                = Work.CR.Flat.dCoord k (f j) (p + x) from congrFun (dCoord_comp_add' k (f j) p) x])
        rw [← hcomp]
        simpa using (bmCz.integral_bmKernel_mul_dCoord hn k j (fun x => f j (p + x)) Reuc hReucpos
          (hcont1 j p) (hsuppE p hp j))
      rw [Finset.sum_congr rfl (fun j _ => hper j), Finset.sum_neg_distrib]
    have hdbarCoord : ∀ k : Fin n, ∀ p : Fin n → ℂ, (∀ m, ‖p m - c m‖ < r m / 2) →
        Work.CR.Flat.dbarCoord k (bmPotential f) p
          = (-∑ j, ∫ x in eucBall (4 * Reuc), bmDbarKernel k j x * (f j (p + x) - f j p))
            - ∑ j, cc k j * f j p := by
      intro k p hp
      have h1 : Work.CR.Flat.dbarCoord k (bmPotential f) p
          = ∑ j, ∫ x, bmKernel j x * Work.CR.Flat.dbarCoord k (f j) (p + x) := by
        rw [funext (fun w => bmPotential_eq_bmPot f w)]
        exact bmPot_dbarCoord hn hf hRsuppos hsuppSup k p
      rw [h1]
      have hper : ∀ j : Fin n, ∫ x, bmKernel j x * Work.CR.Flat.dbarCoord k (f j) (p + x)
          = (-∫ x in eucBall (4 * Reuc), bmDbarKernel k j x * (f j (p + x) - f j p))
            - cc k j * f j p := by
        intro j
        have hcomp : (∫ x, bmKernel j x * Work.CR.Flat.dbarCoord k (fun y => f j (p + y)) x)
            = ∫ x, bmKernel j x * Work.CR.Flat.dbarCoord k (f j) (p + x) :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => by
            show bmKernel j x * Work.CR.Flat.dbarCoord k (fun y => f j (p + y)) x
              = bmKernel j x * Work.CR.Flat.dbarCoord k (f j) (p + x)
            rw [show Work.CR.Flat.dbarCoord k (fun y => f j (p + y)) x
                = Work.CR.Flat.dbarCoord k (f j) (p + x) from
                  congrFun (dbarCoord_comp_add' k (f j) p) x])
        rw [← hcomp]
        simpa using (hcc k j (fun x => f j (p + x)) Reuc hReucpos (hcont1 j p) (hsuppE p hp j))
      rw [Finset.sum_congr rfl (fun j _ => hper j), Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    -- ### summed bounds for the families of constants
    have slice_le : ∀ (X : Fin n × Fin n → ℝ), (∀ p, 0 ≤ X p) → ∀ k : Fin n,
        ∑ j, X (k, j) ≤ ∑ p : Fin n × Fin n, X p := by
      intro X hX k
      have hinj : ∀ a ∈ (Finset.univ : Finset (Fin n)), ∀ b ∈ Finset.univ,
          (k, a) = (k, b) → a = b := fun a _ b _ h => by simpa using congrArg Prod.snd h
      rw [← Finset.sum_image (f := X) (g := fun j => (k, j)) hinj]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun p _ _ => hX p)
    have hsumDz : ∀ k : Fin n, ∑ j, Cdz (k, j) * K' j ≤ Cs * ∑ j, K' j := by
      intro k
      have h1 : ∑ j, Cdz (k, j) * K' j ≤ ∑ j, ∑ i, Cdz (k, j) * K' i :=
        Finset.sum_le_sum fun j _ =>
          Finset.single_le_sum (fun i _ => mul_nonneg ((hCdz (k, j)).1.le) (hK'0 i))
            (Finset.mem_univ j)
      have h2 : ∑ j, ∑ i, Cdz (k, j) * K' i = (∑ j, Cdz (k, j)) * (∑ i, K' i) := by
        rw [Finset.sum_mul]
        exact (Finset.sum_congr rfl fun j _ => Finset.mul_sum _ _ _).symm
      have h3 : (∑ j, Cdz (k, j)) ≤ Cs := by
        rw [hCsdef]
        exact (slice_le Cdz (fun p => (hCdz p).1.le) k).trans
          (le_add_of_nonneg_right (Finset.sum_nonneg fun p _ => (hCZdbar p).1.le))
      calc ∑ j, Cdz (k, j) * K' j ≤ (∑ j, Cdz (k, j)) * (∑ i, K' i) := h1.trans (le_of_eq h2)
        _ ≤ Cs * ∑ j, K' j := mul_le_mul_of_nonneg_right h3 hsk
    have hsumDbar : ∀ k : Fin n, ∑ j, Cdbar (k, j) * K' j ≤ Cs * ∑ j, K' j := by
      intro k
      have h1 : ∑ j, Cdbar (k, j) * K' j ≤ ∑ j, ∑ i, Cdbar (k, j) * K' i :=
        Finset.sum_le_sum fun j _ =>
          Finset.single_le_sum (fun i _ => mul_nonneg ((hCZdbar (k, j)).1.le) (hK'0 i))
            (Finset.mem_univ j)
      have h2 : ∑ j, ∑ i, Cdbar (k, j) * K' i = (∑ j, Cdbar (k, j)) * (∑ i, K' i) := by
        rw [Finset.sum_mul]
        exact (Finset.sum_congr rfl fun j _ => Finset.mul_sum _ _ _).symm
      have h3 : (∑ j, Cdbar (k, j)) ≤ Cs := by
        rw [hCsdef]
        exact (slice_le Cdbar (fun p => (hCZdbar p).1.le) k).trans
          (le_add_of_nonneg_left (Finset.sum_nonneg fun p _ => (hCdz p).1.le))
      calc ∑ j, Cdbar (k, j) * K' j ≤ (∑ j, Cdbar (k, j)) * (∑ i, K' i) := h1.trans (le_of_eq h2)
        _ ≤ Cs * ∑ j, K' j := mul_le_mul_of_nonneg_right h3 hsk
    have hsumCcG : ∀ (X : Fin n → ℝ), (∀ j, 0 ≤ X j) → ∀ k : Fin n,
        ∑ j, ‖cc k j‖ * X j ≤ Cc * ∑ j, X j := by
      intro X hX k
      have h1 : ∑ j, ‖cc k j‖ * X j ≤ ∑ j, ∑ i, ‖cc k j‖ * X i :=
        Finset.sum_le_sum fun j _ =>
          Finset.single_le_sum (f := fun i => ‖cc k j‖ * X i)
            (fun i _ => mul_nonneg (norm_nonneg _) (hX i)) (Finset.mem_univ j)
      have h2 : ∑ j, ∑ i, ‖cc k j‖ * X i = (∑ j, ‖cc k j‖) * (∑ i, X i) := by
        rw [Finset.sum_mul]
        exact (Finset.sum_congr rfl fun j _ => Finset.mul_sum _ _ _).symm
      have h3 : (∑ j, ‖cc k j‖) ≤ Cc := by
        rw [hCcdef]
        exact slice_le (fun p : Fin n × Fin n => ‖cc p.1 p.2‖)
          (fun p => norm_nonneg _) k
      calc ∑ j, ‖cc k j‖ * X j ≤ (∑ j, ‖cc k j‖) * (∑ i, X i) := h1.trans (le_of_eq h2)
        _ ≤ Cc * ∑ j, X j := mul_le_mul_of_nonneg_right h3 (Finset.sum_nonneg fun j _ => hX j)
    have hsumCcK : ∀ k : Fin n, ∑ j, ‖cc k j‖ * K' j ≤ Cc * ∑ j, K' j :=
      fun k => hsumCcG K' hK'0 k
    -- ### pointwise bounds for the two Wirtinger derivatives
    have hbdz : ∀ k : Fin n, ∀ p : Fin n → ℂ, (∀ m, ‖p m - c m‖ < r m / 2) →
        ‖Work.CR.Flat.dCoord k (bmPotential f) p‖ ≤ Cs * ∑ j, K' j := by
      intro k p hp
      rw [hdCoord k p hp, norm_neg]
      exact (norm_sum_le _ _).trans
        ((Finset.sum_le_sum fun j _ => by
          have hcz := ((hCdz (k, j)).2 (K' j) (hK'0 j) (fun x => f j (p + x)) (hfKshift j p)
            (hsuppE p hp j)).1 0
          simpa using hcz).trans (hsumDz k))
    have hbdbar : ∀ k : Fin n, ∀ p : Fin n → ℂ, (∀ m, ‖p m - c m‖ < r m / 2) →
        ‖Work.CR.Flat.dbarCoord k (bmPotential f) p‖
          ≤ (Cs * ∑ j, K' j) + Cc * ∑ j, A' j := by
      intro k p hp
      rw [hdbarCoord k p hp]
      refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_neg]
        exact (norm_sum_le _ _).trans
          ((Finset.sum_le_sum fun j _ => by
            have hcz := ((hCZdbar (k, j)).2 (K' j) (hK'0 j) (fun x => f j (p + x)) (hfKshift j p)
              (hsuppE p hp j)).1 0
            simpa using hcz).trans (hsumDbar k))
      · refine (norm_sum_le _ _).trans ?_
        calc ∑ j, ‖cc k j * f j p‖ ≤ ∑ j, ‖cc k j‖ * A' j :=
              Finset.sum_le_sum fun j _ => by
                rw [norm_mul]
                exact mul_le_mul_of_nonneg_left (hfA j p) (norm_nonneg _)
          _ ≤ Cc * ∑ j, A' j := hsumCcG A' hA'0 k
    -- ### (iii) the norm of the differential
    have hT2 : iterDerivNorm 1 (bmPotential f) P
        ≤ ENNReal.ofReal (B * ((∑ j, A' j) + (∑ j, K' j))) := by
      refine iSup₂_le fun p hp => ?_
      have hp' : ∀ k, ‖p k - c k‖ < r k / 2 := hp
      have hnorm : ‖iteratedFDerivWithin ℝ 1 (bmPotential f) P p‖
          = ‖fderiv ℝ (bmPotential f) p‖ := by
        rw [norm_iteratedFDerivWithin_one _ (hPopen.uniqueDiffWithinAt hp),
          fderivWithin_of_isOpen hPopen hp]
      rw [hnorm]
      refine ENNReal.ofReal_le_ofReal ?_
      refine (bmCz.norm_fderiv_le_sum_wirtinger (bmPotential f) p).trans ?_
      have h1 : ∀ k : Fin n, ‖Work.CR.Flat.dCoord k (bmPotential f) p‖
            + ‖Work.CR.Flat.dbarCoord k (bmPotential f) p‖
          ≤ (2 * Cs + Cc) * ((∑ j, A' j) + (∑ j, K' j)) := by
        intro k
        refine (add_le_add (hbdz k p hp') (hbdbar k p hp')).trans ?_
        nlinarith [hCs0, hCc0, hsa, hsk]
      have h2 : ∑ k, (‖Work.CR.Flat.dCoord k (bmPotential f) p‖
            + ‖Work.CR.Flat.dbarCoord k (bmPotential f) p‖)
          ≤ (n : ℝ) * ((2 * Cs + Cc) * ((∑ j, A' j) + (∑ j, K' j))) := by
        refine (Finset.sum_le_sum fun k _ => h1 k).trans (le_of_eq ?_)
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      calc 2 * ∑ k, (‖Work.CR.Flat.dCoord k (bmPotential f) p‖
              + ‖Work.CR.Flat.dbarCoord k (bmPotential f) p‖)
          ≤ 2 * ((n : ℝ) * ((2 * Cs + Cc) * ((∑ j, A' j) + (∑ j, K' j)))) :=
            mul_le_mul_of_nonneg_left h2 (by norm_num)
        _ = B * ((∑ j, A' j) + (∑ j, K' j)) := by
            rw [hBdef]; ring
    -- ### (iv) the Hölder seminorm of the differential
    have hT3 : holderSeminorm 1 α (bmPotential f) P
        ≤ ENNReal.ofReal (B * ∑ j, K' j) := by
      refine iSup₂_le fun p hp => iSup₂_le fun q hq => iSup_le fun hpq => ?_
      have hp' : ∀ k, ‖p k - c k‖ < r k / 2 := hp
      have hq' : ∀ k, ‖q k - c k‖ < r k / 2 := hq
      have hnorm : ‖iteratedFDerivWithin ℝ 1 (bmPotential f) P p
            - iteratedFDerivWithin ℝ 1 (bmPotential f) P q‖
          ≤ ‖fderiv ℝ (bmPotential f) p - fderiv ℝ (bmPotential f) q‖ := by
        refine ContinuousMultilinearMap.opNorm_le_bound
          (M := ‖fderiv ℝ (bmPotential f) p - fderiv ℝ (bmPotential f) q‖)
          (norm_nonneg _) fun m => ?_
        have key : (iteratedFDerivWithin ℝ 1 (bmPotential f) P p
              - iteratedFDerivWithin ℝ 1 (bmPotential f) P q) m
            = (fderiv ℝ (bmPotential f) p - fderiv ℝ (bmPotential f) q) (m 0) := by
          rw [ContinuousMultilinearMap.sub_apply, ContinuousLinearMap.sub_apply,
            iteratedFDerivWithin_one_apply (hPopen.uniqueDiffWithinAt hp),
            iteratedFDerivWithin_one_apply (hPopen.uniqueDiffWithinAt hq),
            fderivWithin_of_isOpen hPopen hp, fderivWithin_of_isOpen hPopen hq]
        rw [key]
        have hprod : (∏ i : Fin 1, ‖m i‖) = ‖m 0‖ := by simp
        calc ‖(fderiv ℝ (bmPotential f) p - fderiv ℝ (bmPotential f) q) (m 0)‖
            ≤ ‖fderiv ℝ (bmPotential f) p - fderiv ℝ (bmPotential f) q‖ * ‖m 0‖ :=
              (fderiv ℝ (bmPotential f) p - fderiv ℝ (bmPotential f) q).le_opNorm (m 0)
          _ = ‖fderiv ℝ (bmPotential f) p - fderiv ℝ (bmPotential f) q‖
                * ∏ i : Fin 1, ‖m i‖ := by rw [hprod]
      have h3 : 0 < ‖p - q‖ ^ α := Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hpq)) α
      refine ENNReal.ofReal_le_ofReal ?_
      rw [div_le_iff₀ h3]
      refine (hnorm.trans (bmCz.norm_fderiv_sub_le_sum_wirtinger (bmPotential f) p q)).trans ?_
      have hdz : ∀ k : Fin n, ‖Work.CR.Flat.dCoord k (bmPotential f) p
            - Work.CR.Flat.dCoord k (bmPotential f) q‖ ≤ Cs * (∑ j, K' j) * ‖p - q‖ ^ α := by
        intro k
        rw [hdCoord k p hp', hdCoord k q hq']
        rw [show (-∑ j, ∫ x in eucBall (4 * Reuc), bmDzKernel k j x * (f j (p + x) - f j p))
            - (-∑ j, ∫ x in eucBall (4 * Reuc), bmDzKernel k j x * (f j (q + x) - f j q))
            = -((∑ j, ∫ x in eucBall (4 * Reuc), bmDzKernel k j x * (f j (p + x) - f j p))
                - (∑ j, ∫ x in eucBall (4 * Reuc), bmDzKernel k j x * (f j (q + x) - f j q)))
            from by ring, norm_neg]
        have hsub : (∑ j, ∫ x in eucBall (4 * Reuc), bmDzKernel k j x * (f j (p + x) - f j p))
              - (∑ j, ∫ x in eucBall (4 * Reuc), bmDzKernel k j x * (f j (q + x) - f j q))
            = ∑ j, ((∫ x in eucBall (4 * Reuc), bmDzKernel k j x * (f j (p + x) - f j p))
                - ∫ x in eucBall (4 * Reuc), bmDzKernel k j x * (f j (q + x) - f j q)) := by
          rw [sub_eq_add_neg _ _, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [hsub]
        refine (norm_sum_le _ _).trans ((Finset.sum_le_sum
          (g := fun j => Cdz (k, j) * K' j * ‖p - q‖ ^ α) fun j _ => ?_).trans ?_)
        · have hcz := ((hCdz (k, j)).2 (K' j) (hK'0 j) (fun x => f j (p + x)) (hfKshift j p)
            (hsuppE p hp' j)).2 0 (q - p)
          simp only [zero_add, add_zero] at hcz
          have heq : (∫ x in eucBall (4 * Reuc),
                bmDzKernel k j x * (f j (p + (q - p + x)) - f j (p + (q - p))))
              = ∫ x in eucBall (4 * Reuc), bmDzKernel k j x * (f j (q + x) - f j q) := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
            show bmDzKernel k j x * (f j (p + (q - p + x)) - f j (p + (q - p)))
              = bmDzKernel k j x * (f j (q + x) - f j q)
            rw [show p + (q - p + x) = q + x from by abel,
              show p + (q - p) = q from by abel]
          rw [heq] at hcz
          rw [show ‖(0 : Fin n → ℂ) - (q - p)‖ = ‖p - q‖ from by
            rw [zero_sub, norm_neg, norm_sub_rev]] at hcz
          exact hcz
        · calc ∑ j, Cdz (k, j) * K' j * ‖p - q‖ ^ α
              = (∑ j, Cdz (k, j) * K' j) * ‖p - q‖ ^ α := (Finset.sum_mul _ _ _).symm
            _ ≤ (Cs * ∑ j, K' j) * ‖p - q‖ ^ α :=
                mul_le_mul_of_nonneg_right (hsumDz k) (Real.rpow_nonneg (norm_nonneg _) _)
            _ = Cs * (∑ j, K' j) * ‖p - q‖ ^ α := by ring
      have hdbar : ∀ k : Fin n, ‖Work.CR.Flat.dbarCoord k (bmPotential f) p
            - Work.CR.Flat.dbarCoord k (bmPotential f) q‖
          ≤ (Cs + Cc) * (∑ j, K' j) * ‖p - q‖ ^ α := by
        intro k
        rw [hdbarCoord k p hp', hdbarCoord k q hq']
        have hdecomp : ((-∑ j, ∫ x in eucBall (4 * Reuc), bmDbarKernel k j x * (f j (p + x) - f j p))
              - ∑ j, cc k j * f j p)
            - ((-∑ j, ∫ x in eucBall (4 * Reuc), bmDbarKernel k j x * (f j (q + x) - f j q))
              - ∑ j, cc k j * f j q)
            = ((-∑ j, ∫ x in eucBall (4 * Reuc), bmDbarKernel k j x * (f j (p + x) - f j p))
                - (-∑ j, ∫ x in eucBall (4 * Reuc), bmDbarKernel k j x * (f j (q + x) - f j q)))
              - ((∑ j, cc k j * f j p) - (∑ j, cc k j * f j q)) := by ring
        rw [hdecomp]
        have hInt : ‖(-(∑ j, ∫ x in eucBall (4 * Reuc), bmDbarKernel k j x * (f j (p + x) - f j p))
              - (-(∑ j, ∫ x in eucBall (4 * Reuc), bmDbarKernel k j x * (f j (q + x) - f j q))))‖
            ≤ Cs * (∑ j, K' j) * ‖p - q‖ ^ α := by
          rw [show (-(∑ j, ∫ x in eucBall (4 * Reuc), bmDbarKernel k j x * (f j (p + x) - f j p))
                - (-(∑ j, ∫ x in eucBall (4 * Reuc), bmDbarKernel k j x * (f j (q + x) - f j q))))
              = -((∑ j, ∫ x in eucBall (4 * Reuc), bmDbarKernel k j x * (f j (p + x) - f j p))
                  - (∑ j, ∫ x in eucBall (4 * Reuc), bmDbarKernel k j x * (f j (q + x) - f j q)))
              from by ring, norm_neg]
          have hsub : (∑ j, ∫ x in eucBall (4 * Reuc), bmDbarKernel k j x * (f j (p + x) - f j p))
                - (∑ j, ∫ x in eucBall (4 * Reuc), bmDbarKernel k j x * (f j (q + x) - f j q))
              = ∑ j, ((∫ x in eucBall (4 * Reuc), bmDbarKernel k j x * (f j (p + x) - f j p))
                  - ∫ x in eucBall (4 * Reuc), bmDbarKernel k j x * (f j (q + x) - f j q)) := by
            rw [sub_eq_add_neg _ _, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun j _ => by ring
          rw [hsub]
          refine (norm_sum_le _ _).trans ((Finset.sum_le_sum
            (g := fun j => Cdbar (k, j) * K' j * ‖p - q‖ ^ α) fun j _ => ?_).trans ?_)
          · have hcz := ((hCZdbar (k, j)).2 (K' j) (hK'0 j) (fun x => f j (p + x)) (hfKshift j p)
              (hsuppE p hp' j)).2 0 (q - p)
            simp only [zero_add, add_zero] at hcz
            have heq : (∫ x in eucBall (4 * Reuc),
                  bmDbarKernel k j x * (f j (p + (q - p + x)) - f j (p + (q - p))))
                = ∫ x in eucBall (4 * Reuc), bmDbarKernel k j x * (f j (q + x) - f j q) := by
              refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
              show bmDbarKernel k j x * (f j (p + (q - p + x)) - f j (p + (q - p)))
                = bmDbarKernel k j x * (f j (q + x) - f j q)
              rw [show p + (q - p + x) = q + x from by abel,
                show p + (q - p) = q from by abel]
            rw [heq] at hcz
            rw [show ‖(0 : Fin n → ℂ) - (q - p)‖ = ‖p - q‖ from by
              rw [zero_sub, norm_neg, norm_sub_rev]] at hcz
            exact hcz
          · calc ∑ j, Cdbar (k, j) * K' j * ‖p - q‖ ^ α
                = (∑ j, Cdbar (k, j) * K' j) * ‖p - q‖ ^ α := (Finset.sum_mul _ _ _).symm
              _ ≤ (Cs * ∑ j, K' j) * ‖p - q‖ ^ α :=
                  mul_le_mul_of_nonneg_right (hsumDbar k) (Real.rpow_nonneg (norm_nonneg _) _)
              _ = Cs * (∑ j, K' j) * ‖p - q‖ ^ α := by ring
        have hB : ‖(∑ j, cc k j * f j p) - (∑ j, cc k j * f j q)‖
            ≤ Cc * (∑ j, K' j) * ‖p - q‖ ^ α := by
          rw [show (∑ j, cc k j * f j p) - (∑ j, cc k j * f j q)
              = ∑ j, (cc k j * f j p - cc k j * f j q) from by
            rw [sub_eq_add_neg _ _, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun j _ => by ring]
          refine (norm_sum_le _ _).trans ((Finset.sum_le_sum
            (g := fun j => ‖cc k j‖ * K' j * ‖p - q‖ ^ α) fun j _ => ?_).trans ?_)
          · rw [← mul_sub]
            calc ‖cc k j * (f j p - f j q)‖ = ‖cc k j‖ * ‖f j p - f j q‖ := norm_mul _ _
              _ ≤ ‖cc k j‖ * (K' j * ‖p - q‖ ^ α) :=
                  mul_le_mul_of_nonneg_left (hfK j p q) (norm_nonneg _)
              _ = ‖cc k j‖ * K' j * ‖p - q‖ ^ α := by ring
          · calc ∑ j, ‖cc k j‖ * K' j * ‖p - q‖ ^ α
                = (∑ j, ‖cc k j‖ * K' j) * ‖p - q‖ ^ α := (Finset.sum_mul _ _ _).symm
              _ ≤ (Cc * ∑ j, K' j) * ‖p - q‖ ^ α :=
                  mul_le_mul_of_nonneg_right (hsumCcK k) (Real.rpow_nonneg (norm_nonneg _) _)
              _ = Cc * (∑ j, K' j) * ‖p - q‖ ^ α := by ring
        calc ‖(-(∑ j, ∫ x in eucBall (4 * Reuc), bmDbarKernel k j x * (f j (p + x) - f j p))
                - (-(∑ j, ∫ x in eucBall (4 * Reuc), bmDbarKernel k j x * (f j (q + x) - f j q))))
              - ((∑ j, cc k j * f j p) - (∑ j, cc k j * f j q))‖
            ≤ ‖(-(∑ j, ∫ x in eucBall (4 * Reuc), bmDbarKernel k j x * (f j (p + x) - f j p))
                - (-(∑ j, ∫ x in eucBall (4 * Reuc), bmDbarKernel k j x * (f j (q + x) - f j q))))‖
              + ‖(∑ j, cc k j * f j p) - (∑ j, cc k j * f j q)‖ := norm_sub_le _ _
          _ ≤ Cs * (∑ j, K' j) * ‖p - q‖ ^ α + Cc * (∑ j, K' j) * ‖p - q‖ ^ α :=
              add_le_add hInt hB
          _ = (Cs + Cc) * (∑ j, K' j) * ‖p - q‖ ^ α := by ring
      have h1 : ∀ k : Fin n, ‖Work.CR.Flat.dCoord k (bmPotential f) p
              - Work.CR.Flat.dCoord k (bmPotential f) q‖
            + ‖Work.CR.Flat.dbarCoord k (bmPotential f) p
              - Work.CR.Flat.dbarCoord k (bmPotential f) q‖
          ≤ (2 * Cs + Cc) * (∑ j, K' j) * ‖p - q‖ ^ α := by
        intro k
        refine (add_le_add (hdz k) (hdbar k)).trans ?_
        nlinarith [hCs0, hCc0, hsk, Real.rpow_nonneg (norm_nonneg (p - q)) α]
      have h2 : ∑ k, (‖Work.CR.Flat.dCoord k (bmPotential f) p
              - Work.CR.Flat.dCoord k (bmPotential f) q‖
            + ‖Work.CR.Flat.dbarCoord k (bmPotential f) p
              - Work.CR.Flat.dbarCoord k (bmPotential f) q‖)
          ≤ (n : ℝ) * ((2 * Cs + Cc) * (∑ j, K' j) * ‖p - q‖ ^ α) := by
        refine (Finset.sum_le_sum fun k _ => h1 k).trans (le_of_eq ?_)
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      calc 2 * ∑ k, (‖Work.CR.Flat.dCoord k (bmPotential f) p
              - Work.CR.Flat.dCoord k (bmPotential f) q‖
            + ‖Work.CR.Flat.dbarCoord k (bmPotential f) p
              - Work.CR.Flat.dbarCoord k (bmPotential f) q‖)
          ≤ 2 * ((n : ℝ) * ((2 * Cs + Cc) * (∑ j, K' j) * ‖p - q‖ ^ α)) :=
            mul_le_mul_of_nonneg_left h2 (by norm_num)
        _ = B * (∑ j, K' j) * ‖p - q‖ ^ α := by
            rw [hBdef]; ring
    -- ### assembly
    have h0j : ∀ j, holderNorm 0 α (f j) Set.univ = ENNReal.ofReal (A' j + K' j) := by
      intro j
      rw [holderNorm, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, ← hA'eq j, ← hK'eq j,
        ← ENNReal.ofReal_add (hA'0 j) (hK'0 j)]
    have h0 : ∑ j, holderNorm 0 α (f j) Set.univ
        = ENNReal.ofReal (∑ j, (A' j + K' j)) := by
      rw [Finset.sum_congr rfl (fun j _ => h0j j),
        ← ENNReal.ofReal_sum_of_nonneg (fun j _ => add_nonneg (hA'0 j) (hK'0 j))]
    have hAB : ∑ j, (A' j + K' j) = (∑ j, A' j) + (∑ j, K' j) := Finset.sum_add_distrib
    have hsat : 0 ≤ (∑ j, A' j) + (∑ j, K' j) := add_nonneg hsa hsk
    have hmain : holderNorm 1 α (bmPotential f) P
        ≤ ENNReal.ofReal ((κ + 2 * B) * ((∑ j, A' j) + (∑ j, K' j))) := by
      rw [holderNorm_one_eq_pi]
      have hb1 : iterDerivNorm 0 (bmPotential f) P + holderSeminorm 0 α (bmPotential f) P
          ≤ ENNReal.ofReal (κ * (∑ j, A' j) + κ * (∑ j, K' j)) := by
        rw [ENNReal.ofReal_add (mul_nonneg hκpos.le hsa) (mul_nonneg hκpos.le hsk)]
        exact add_le_add hT0 hT1
      have hb2 : iterDerivNorm 1 (bmPotential f) P + holderSeminorm 1 α (bmPotential f) P
          ≤ ENNReal.ofReal (B * ((∑ j, A' j) + (∑ j, K' j)) + B * (∑ j, K' j)) := by
        rw [ENNReal.ofReal_add (mul_nonneg hB0 hsat) (mul_nonneg hB0 hsk)]
        exact add_le_add hT2 hT3
      refine (add_le_add hb1 hb2).trans ?_
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      nlinarith [hκpos.le, hB0, hsa, hsk]
    calc holderNorm 1 α (bmPotential f) P
        ≤ ENNReal.ofReal ((κ + 2 * B) * ((∑ j, A' j) + (∑ j, K' j))) := hmain
      _ = ENNReal.ofReal (κ + 2 * B) * ENNReal.ofReal ((∑ j, A' j) + (∑ j, K' j)) :=
          ENNReal.ofReal_mul (by positivity)
      _ = ENNReal.ofReal (κ + 2 * B) * ∑ j, holderNorm 0 α (f j) Set.univ := by
          rw [h0, hAB]

end Work.CR.Flat.Cauchy
