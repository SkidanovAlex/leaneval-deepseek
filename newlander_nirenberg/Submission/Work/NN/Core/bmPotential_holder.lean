import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Cauchy.bmDefs
import Submission.Work.CR.Flat.Cauchy.bmCZDefs
import Submission.Work.CR.Flat.Cauchy.bmSetup
import Submission.Work.CR.Flat.Cauchy.bmPotential_contDiff_one
import Submission.Work.CR.Flat.Cauchy.bmPot_dbarCoord
import Submission.Work.CR.Flat.Cauchy.fderiv_bmPotential
import Submission.Work.CR.Flat.Cauchy.bmCz.eucRadialBound
import Submission.Work.CR.Flat.Cauchy.bmCz.bmKernel_decay_le
import Submission.Work.CR.Flat.Cauchy.bmCz.bmDbarKernel_shell_eq_zero
import Submission.Work.CR.Flat.Cauchy.bmCz.norm_bmDbarKernel_sub_le
import Submission.Work.CR.Flat.Cauchy.bmCz.norm_bmDzKernel_sub_le
import Submission.Work.CR.Flat.Cauchy.bmCz.integral_bmDzKernel_eucShell_eq_zero
import Submission.Work.CR.Flat.Cauchy.bmCz.integral_bmKernel_mul_dCoord
import Submission.Work.CR.Flat.Cauchy.bmCz.bmPot_dCoord
import Submission.Work.NN.Core.bmPot_repr
import Submission.Work.NN.Core.czHolderEstimate

noncomputable section

set_option maxHeartbeats 1000000

open MeasureTheory Set
open scoped NNReal ENNReal
open Work.CR.Flat

namespace Work.NN.Core

open Work.CR.Flat.Cauchy

/-! ## Decomposition of the real derivative into Wirtinger derivatives -/

/-- The real derivative is recovered from the Wirtinger derivatives in the coordinate directions
`e_k = Pi.single k 1` and `i e_k = Pi.single k I`. -/
lemma fderiv_wirtinger {n : ℕ} (u : (Fin n → ℂ) → ℂ) (z v : Fin n → ℂ) :
    fderiv ℝ u z v = ∑ k, (((v k).re : ℝ) • (fderiv ℝ u z (Pi.single k (1:ℂ)))
        + ((v k).im : ℝ) • (fderiv ℝ u z (Pi.single k Complex.I))) := by
  have hv : v = ∑ k, (((v k).re : ℝ) • (Pi.single k (1:ℂ) : Fin n → ℂ)
      + ((v k).im : ℝ) • (Pi.single k Complex.I : Fin n → ℂ)) := by
    funext m
    rw [Finset.sum_apply, Finset.sum_eq_single m]
    · simp [Complex.re_add_im]
    · intro k _ hk; simp [Pi.single_apply, hk]
    · intro h; exact absurd (Finset.mem_univ m) h
  conv_lhs => rw [hv]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_add, map_smul, map_smul]

/-- `fderiv ℝ u z (Pi.single k 1) = dCoord k u z + dbarCoord k u z`. -/
lemma fderiv_single_one {n : ℕ} (u : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) (k : Fin n) :
    fderiv ℝ u z (Pi.single k (1:ℂ)) = dCoord k u z + dbarCoord k u z := by
  rw [dCoord, dbarCoord]; ring

/-- `fderiv ℝ u z (Pi.single k I) = I * (dCoord k u z - dbarCoord k u z)`. -/
lemma fderiv_single_I {n : ℕ} (u : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) (k : Fin n) :
    fderiv ℝ u z (Pi.single k Complex.I) = Complex.I * (dCoord k u z - dbarCoord k u z) := by
  have key : dbarCoord k u z - dCoord k u z = Complex.I * fderiv ℝ u z (Pi.single k Complex.I) := by
    rw [dCoord, dbarCoord]; ring
  rw [show dCoord k u z - dbarCoord k u z = -(dbarCoord k u z - dCoord k u z) from by ring, key]
  rw [mul_neg, ← mul_assoc, Complex.I_mul_I]; ring

/-- The operator norm of the real derivative is controlled by the Wirtinger derivatives. -/
lemma norm_fderiv_le_wirtinger {n : ℕ} (u : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    ‖fderiv ℝ u z‖ ≤ 2 * ∑ k, (‖dCoord k u z‖ + ‖dbarCoord k u z‖) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
  rw [fderiv_wirtinger u z v]
  calc ‖∑ k, (((v k).re : ℝ) • (fderiv ℝ u z (Pi.single k (1:ℂ)))
          + ((v k).im : ℝ) • (fderiv ℝ u z (Pi.single k Complex.I)))‖
      ≤ ∑ k, ‖((v k).re : ℝ) • (fderiv ℝ u z (Pi.single k (1:ℂ)))
          + ((v k).im : ℝ) • (fderiv ℝ u z (Pi.single k Complex.I))‖ := norm_sum_le _ _
    _ ≤ ∑ k, 2 * (‖dCoord k u z‖ + ‖dbarCoord k u z‖) * ‖v‖ := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        rw [fderiv_single_one u z k, fderiv_single_I u z k]
        have hvk : ‖v k‖ ≤ ‖v‖ := norm_le_pi_norm v k
        have hre : |(v k).re| ≤ ‖v‖ := le_trans (Complex.abs_re_le_norm (v k)) hvk
        have him : |(v k).im| ≤ ‖v‖ := le_trans (Complex.abs_im_le_norm (v k)) hvk
        have h2 : ‖Complex.I * (dCoord k u z - dbarCoord k u z)‖
            ≤ ‖dCoord k u z‖ + ‖dbarCoord k u z‖ := by
          rw [norm_mul, Complex.norm_I, one_mul]; exact norm_sub_le _ _
        have h1 : ‖dCoord k u z + dbarCoord k u z‖ ≤ ‖dCoord k u z‖ + ‖dbarCoord k u z‖ :=
          norm_add_le _ _
        calc ‖((v k).re : ℝ) • (dCoord k u z + dbarCoord k u z)
              + ((v k).im : ℝ) • (Complex.I * (dCoord k u z - dbarCoord k u z))‖
            ≤ ‖((v k).re : ℝ) • (dCoord k u z + dbarCoord k u z)‖
              + ‖((v k).im : ℝ) • (Complex.I * (dCoord k u z - dbarCoord k u z))‖ := norm_add_le _ _
          _ = |(v k).re| * ‖dCoord k u z + dbarCoord k u z‖
              + |(v k).im| * ‖Complex.I * (dCoord k u z - dbarCoord k u z)‖ := by
              rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
          _ ≤ ‖v‖ * (‖dCoord k u z‖ + ‖dbarCoord k u z‖)
              + ‖v‖ * (‖dCoord k u z‖ + ‖dbarCoord k u z‖) :=
              add_le_add (mul_le_mul hre h1 (norm_nonneg _) (norm_nonneg _))
                (mul_le_mul him h2 (norm_nonneg _) (norm_nonneg _))
          _ = 2 * (‖dCoord k u z‖ + ‖dbarCoord k u z‖) * ‖v‖ := by ring
    _ = (∑ k, 2 * (‖dCoord k u z‖ + ‖dbarCoord k u z‖)) * ‖v‖ := by rw [Finset.sum_mul]
    _ = (2 * ∑ k, (‖dCoord k u z‖ + ‖dbarCoord k u z‖)) * ‖v‖ := by rw [Finset.mul_sum]

/-- Difference version of `norm_fderiv_le_wirtinger`. -/
lemma norm_fderiv_sub_le_wirtinger {n : ℕ} (u : (Fin n → ℂ) → ℂ) (z z' : Fin n → ℂ) :
    ‖fderiv ℝ u z - fderiv ℝ u z'‖
      ≤ 2 * ∑ k, (‖dCoord k u z - dCoord k u z'‖ + ‖dbarCoord k u z - dbarCoord k u z'‖) := by
  have hA : ∀ k, fderiv ℝ u z (Pi.single k (1:ℂ)) - fderiv ℝ u z' (Pi.single k (1:ℂ))
      = (dCoord k u z - dCoord k u z') + (dbarCoord k u z - dbarCoord k u z') := by
    intro k; rw [fderiv_single_one, fderiv_single_one]; ring
  have hB : ∀ k, fderiv ℝ u z (Pi.single k Complex.I) - fderiv ℝ u z' (Pi.single k Complex.I)
      = Complex.I * ((dCoord k u z - dCoord k u z') - (dbarCoord k u z - dbarCoord k u z')) := by
    intro k
    have key : (dbarCoord k u z - dbarCoord k u z') - (dCoord k u z - dCoord k u z')
        = Complex.I * (fderiv ℝ u z (Pi.single k Complex.I) - fderiv ℝ u z' (Pi.single k Complex.I)) := by
      rw [fderiv_single_I, fderiv_single_I, mul_sub, ← mul_assoc, ← mul_assoc, Complex.I_mul_I]
      ring
    rw [show (dCoord k u z - dCoord k u z') - (dbarCoord k u z - dbarCoord k u z')
        = -((dbarCoord k u z - dbarCoord k u z') - (dCoord k u z - dCoord k u z')) from by ring, key]
    rw [mul_neg, ← mul_assoc, Complex.I_mul_I]; ring
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
  rw [ContinuousLinearMap.sub_apply, fderiv_wirtinger u z v, fderiv_wirtinger u z' v,
    ← Finset.sum_sub_distrib]
  calc ‖∑ k, (((v k).re : ℝ) • (fderiv ℝ u z (Pi.single k (1:ℂ)))
          + ((v k).im : ℝ) • (fderiv ℝ u z (Pi.single k Complex.I))
          - (((v k).re : ℝ) • (fderiv ℝ u z' (Pi.single k (1:ℂ)))
            + ((v k).im : ℝ) • (fderiv ℝ u z' (Pi.single k Complex.I))))‖
      ≤ ∑ k, ‖((v k).re : ℝ) • (fderiv ℝ u z (Pi.single k (1:ℂ)))
          + ((v k).im : ℝ) • (fderiv ℝ u z (Pi.single k Complex.I))
          - (((v k).re : ℝ) • (fderiv ℝ u z' (Pi.single k (1:ℂ)))
            + ((v k).im : ℝ) • (fderiv ℝ u z' (Pi.single k Complex.I)))‖ := norm_sum_le _ _
    _ ≤ ∑ k, 2 * (‖dCoord k u z - dCoord k u z'‖ + ‖dbarCoord k u z - dbarCoord k u z'‖) * ‖v‖ := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        rw [show ((v k).re : ℝ) • (fderiv ℝ u z (Pi.single k (1:ℂ)))
              + ((v k).im : ℝ) • (fderiv ℝ u z (Pi.single k Complex.I))
              - (((v k).re : ℝ) • (fderiv ℝ u z' (Pi.single k (1:ℂ)))
                + ((v k).im : ℝ) • (fderiv ℝ u z' (Pi.single k Complex.I)))
            = ((v k).re : ℝ) • (fderiv ℝ u z (Pi.single k (1:ℂ)) - fderiv ℝ u z' (Pi.single k (1:ℂ)))
              + ((v k).im : ℝ) • (fderiv ℝ u z (Pi.single k Complex.I) - fderiv ℝ u z' (Pi.single k Complex.I))
            from by rw [smul_sub, smul_sub]; abel,
          hA k, hB k]
        have hvk : ‖v k‖ ≤ ‖v‖ := norm_le_pi_norm v k
        have hre : |(v k).re| ≤ ‖v‖ := le_trans (Complex.abs_re_le_norm (v k)) hvk
        have him : |(v k).im| ≤ ‖v‖ := le_trans (Complex.abs_im_le_norm (v k)) hvk
        have h2 : ‖Complex.I * ((dCoord k u z - dCoord k u z') - (dbarCoord k u z - dbarCoord k u z'))‖
            ≤ ‖dCoord k u z - dCoord k u z'‖ + ‖dbarCoord k u z - dbarCoord k u z'‖ := by
          rw [norm_mul, Complex.norm_I, one_mul]; exact norm_sub_le _ _
        have h1 : ‖(dCoord k u z - dCoord k u z') + (dbarCoord k u z - dbarCoord k u z')‖
            ≤ ‖dCoord k u z - dCoord k u z'‖ + ‖dbarCoord k u z - dbarCoord k u z'‖ := norm_add_le _ _
        calc ‖((v k).re : ℝ) • ((dCoord k u z - dCoord k u z') + (dbarCoord k u z - dbarCoord k u z'))
              + ((v k).im : ℝ) • (Complex.I * ((dCoord k u z - dCoord k u z') - (dbarCoord k u z - dbarCoord k u z')))‖
            ≤ ‖((v k).re : ℝ) • ((dCoord k u z - dCoord k u z') + (dbarCoord k u z - dbarCoord k u z'))‖
              + ‖((v k).im : ℝ) • (Complex.I * ((dCoord k u z - dCoord k u z') - (dbarCoord k u z - dbarCoord k u z')))‖ := norm_add_le _ _
          _ = |(v k).re| * ‖(dCoord k u z - dCoord k u z') + (dbarCoord k u z - dbarCoord k u z')‖
              + |(v k).im| * ‖Complex.I * ((dCoord k u z - dCoord k u z') - (dbarCoord k u z - dbarCoord k u z'))‖ := by
              rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
          _ ≤ ‖v‖ * (‖dCoord k u z - dCoord k u z'‖ + ‖dbarCoord k u z - dbarCoord k u z'‖)
              + ‖v‖ * (‖dCoord k u z - dCoord k u z'‖ + ‖dbarCoord k u z - dbarCoord k u z'‖) :=
              add_le_add (mul_le_mul hre h1 (norm_nonneg _) (norm_nonneg _))
                (mul_le_mul him h2 (norm_nonneg _) (norm_nonneg _))
          _ = 2 * (‖dCoord k u z - dCoord k u z'‖ + ‖dbarCoord k u z - dbarCoord k u z'‖) * ‖v‖ := by ring
    _ = (∑ k, 2 * (‖dCoord k u z - dCoord k u z'‖ + ‖dbarCoord k u z - dbarCoord k u z'‖)) * ‖v‖ := by
        rw [Finset.sum_mul]
    _ = (2 * ∑ k, (‖dCoord k u z - dCoord k u z'‖ + ‖dbarCoord k u z - dbarCoord k u z'‖)) * ‖v‖ := by
        rw [Finset.mul_sum]


/-! ## Convexity of the polydisc -/

lemma convex_polydisc {n : ℕ} (c : Fin n → ℂ) (r : Fin n → ℝ) :
    Convex ℝ (polydisc c r) := by
  intro x hx y hy a b ha hb hab
  rw [mem_polydisc] at hx hy ⊢
  intro j
  have hx' := hx j
  have hy' := hy j
  have hkey : (a • x + b • y) j - c j = (a : ℂ) * (x j - c j) + (b : ℂ) * (y j - c j) := by
    have h1 : ((a : ℂ) + (b : ℂ)) = 1 := by rw [← Complex.ofReal_add, hab]; simp
    simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul]
    rw [mul_sub, mul_sub]
    linear_combination (c j) * h1
  rw [hkey]
  have hbnd : ‖(a : ℂ) * (x j - c j) + (b : ℂ) * (y j - c j)‖
      ≤ a * ‖x j - c j‖ + b * ‖y j - c j‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Work.CR.Flat.Cauchy.bmCz.norm_ofReal_eq_abs,
      Work.CR.Flat.Cauchy.bmCz.norm_ofReal_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
  refine hbnd.trans_lt ?_
  rcases eq_or_lt_of_le ha with ha0 | hapos
  · subst ha0
    have hb1 : b = 1 := by linarith
    subst hb1
    simp only [zero_mul, zero_add, one_mul]
    exact hy'
  · refine (add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hx' hapos)
      (mul_le_mul_of_nonneg_left (le_of_lt hy') hb)).trans_eq ?_
    rw [← add_mul, hab, one_mul]

/-! ## Compact support and integrability helpers -/

lemma isCompact_eucClosedBall {n : ℕ} (R : ℝ) : IsCompact (eucClosedBall (n := n) R) := by
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Fin n → ℂ) (max R 0))
    (isClosed_le continuous_eucNorm continuous_const) ?_
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  exact (pi_norm_le_eucNorm x).trans (le_trans hx (le_max_left R 0))

lemma hasCompactSupport_of_eucNorm {n : ℕ} {g : (Fin n → ℂ) → ℂ} {R : ℝ}
    (hg : ∀ x, R ≤ eucNorm x → g x = 0) : HasCompactSupport g := by
  refine (isCompact_eucClosedBall R).of_isClosed_subset (isClosed_tsupport g) ?_
  rw [tsupport]
  refine closure_minimal (fun x hx => ?_) (isCompact_eucClosedBall R).isClosed
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

/-! ## The potential as an integral over a euclidean ball -/

lemma bmPotential_eq_sum_ball {n : ℕ} {f : Fin n → (Fin n → ℂ) → ℂ} {S : ℝ}
    {z : Fin n → ℂ} (h : ∀ j x, S ≤ eucNorm x → f j (z + x) = 0) :
    bmPotential f z = ∑ j, ∫ x in eucBall S, bmKernel j x * f j (z + x) := by
  rw [bmPotential_eq_bmPot]
  simp only [bmPot]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    simp only [Set.mem_compl_iff, mem_eucBall, not_lt] at hx
    rw [h j x hx, mul_zero])).symm

/-! ## The `0`-th iterated derivative -/

lemma norm_iteratedFDerivWithin_zero_sub {n : ℕ} (f : (Fin n → ℂ) → ℂ) (Ω : Set (Fin n → ℂ))
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

lemma holderNorm_zero_eq {n : ℕ} (α : ℝ) (g : (Fin n → ℂ) → ℂ) (Ω : Set (Fin n → ℂ)) :
    holderNorm 0 α g Ω = iterDerivNorm 0 g Ω + holderSeminorm 0 α g Ω := by
  rw [holderNorm]
  rw [show Finset.range (0 + 1) = {0} from rfl, Finset.sum_singleton]

/-! ## Integrability of powers of the euclidean norm on a ball -/

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

lemma integrableOn_eucNorm_rpow {n : ℕ} (hn : 0 < n) {β : ℝ}
    (hβ : -(2 * (n : ℝ)) < β) (hβ0 : β < 0) (R : ℝ) :
    IntegrableOn (fun x : Fin n → ℂ => (eucNorm x) ^ β) (eucBall R) := by
  have hmax : (0 : ℝ) < max R 1 := lt_of_lt_of_le zero_lt_one (le_max_right R 1)
  have hbase : IntegrableOn (fun x : Fin n → ℂ => ‖x‖ ^ β) (eucBall R) :=
    (integrableOn_norm_rpow_ball_pi hn hβ hmax).mono_set (by
      intro x hx
      rw [mem_eucBall] at hx
      rw [Metric.mem_ball, dist_zero_right]
      exact lt_of_lt_of_le (lt_of_le_of_lt (pi_norm_le_eucNorm x) hx) (le_max_left R 1))
  refine hbase.mono' ((Work.CR.Flat.Cauchy.bmCz.measurable_eucNorm_rpow β).aestronglyMeasurable.mono_measure
    Measure.restrict_le_self) (Filter.Eventually.of_forall (fun x => ?_))
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (eucNorm_nonneg x) _)]
  rcases eq_or_ne x 0 with hx0 | hxne
  · subst hx0
    simp [Real.zero_rpow (ne_of_lt hβ0)]
  · exact Real.rpow_le_rpow_of_nonpos (norm_pos_iff.mpr hxne) (pi_norm_le_eucNorm x) hβ0.le


lemma norm_setIntegral_le_of_norm_le' {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} (hs : MeasurableSet s) {F : α → ℂ} {g : α → ℝ}
    (hg : IntegrableOn g s μ) (h : ∀ x ∈ s, ‖F x‖ ≤ g x) :
    ‖∫ x in s, F x ∂μ‖ ≤ ∫ x in s, g x ∂μ := by
  rw [← integral_indicator hs (f := F), ← integral_indicator hs (f := g)]
  refine norm_integral_le_of_norm_le (hg.integrable_indicator hs)
    (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]; exact h x hx
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; simp

/-- `dCoord` of a translation: `∂_j (y ↦ g (z + y)) x = ∂_j g (z + x)`. -/
lemma dCoord_comp_add {n : ℕ} (j : Fin n) {g : (Fin n → ℂ) → ℂ} {z x : Fin n → ℂ}
    (hg : DifferentiableAt ℝ g (z + x)) :
    dCoord j (fun y => g (z + y)) x = dCoord j g (z + x) := by
  have hshift : HasFDerivAt (fun y : Fin n → ℂ => z + y)
      (ContinuousLinearMap.id ℝ (Fin n → ℂ)) x :=
    (hasFDerivAt_id x).const_add z
  have h := (hg.hasFDerivAt).comp x hshift
  simp only [Function.comp_def, ContinuousLinearMap.id_comp] at h
  rw [dCoord, dCoord, h.fderiv, ContinuousLinearMap.comp_id]

lemma iteratedFDerivWithin_one_sub_le {n : ℕ} (u : (Fin n → ℂ) → ℂ) (Ω : Set (Fin n → ℂ))
    (x y : Fin n → ℂ) (hx : UniqueDiffWithinAt ℝ Ω x) (hy : UniqueDiffWithinAt ℝ Ω y) :
    ‖iteratedFDerivWithin ℝ 1 u Ω x - iteratedFDerivWithin ℝ 1 u Ω y‖
      ≤ ‖fderivWithin ℝ u Ω x - fderivWithin ℝ u Ω y‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound
    (M := ‖fderivWithin ℝ u Ω x - fderivWithin ℝ u Ω y‖) (norm_nonneg _) (fun m => ?_)
  rw [ContinuousMultilinearMap.sub_apply, iteratedFDerivWithin_one_apply hx,
    iteratedFDerivWithin_one_apply hy]
  calc ‖(fderivWithin ℝ u Ω x) (m 0) - (fderivWithin ℝ u Ω y) (m 0)‖
      = ‖((fderivWithin ℝ u Ω x) - (fderivWithin ℝ u Ω y)) (m 0)‖ := by
        rw [← ContinuousLinearMap.sub_apply]
    _ ≤ ‖(fderivWithin ℝ u Ω x) - (fderivWithin ℝ u Ω y)‖ * ‖m 0‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖(fderivWithin ℝ u Ω x) - (fderivWithin ℝ u Ω y)‖ * ∏ i, ‖m i‖ := by
        rw [show (∏ i : Fin 1, ‖m i‖) = ‖m 0‖ from by simp]

/-! ## The Calderón–Zygmund estimate and the `∂̄`-representation (temporary local copies) -/

/-! ## The Calderón–Zygmund bound, uniform in the kernel -/

theorem czHolderBound_uniform {ι : Type*} [Fintype ι] [Nonempty ι]
    {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) {R : ℝ} (hR : 0 < R)
    {Φ : ι → (Fin n → ℂ) → ℂ} (hΦm : ∀ i, AEStronglyMeasurable (Φ i) volume)
    {A : ℝ} (hA : 0 < A)
    (hP1 : ∀ i x, x ≠ 0 → ‖Φ i x‖ ≤ A / (eucNorm x) ^ (2 * n))
    (hP2 : ∀ i x h, 2 * eucNorm h ≤ eucNorm x →
      ‖Φ i (x - h) - Φ i x‖ ≤ A * eucNorm h / (eucNorm x) ^ (2 * n + 1))
    (hH2 : ∀ i a b, 0 < a → a < b → ∫ x in eucShell a b, Φ i x = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i : ι) (K : ℝ), 0 ≤ K → ∀ g : (Fin n → ℂ) → ℂ,
      (∀ x y : Fin n → ℂ, ‖g x - g y‖ ≤ K * ‖x - y‖ ^ α) →
      (∀ x : Fin n → ℂ, R ≤ ‖x‖ → g x = 0) →
      (∀ z : Fin n → ℂ,
        ‖∫ x in eucBall (4 * R), Φ i x * (g (z + x) - g z)‖ ≤ C * K) ∧
      (∀ z z' : Fin n → ℂ,
        ‖(∫ x in eucBall (4 * R), Φ i x * (g (z + x) - g z))
            - (∫ x in eucBall (4 * R), Φ i x * (g (z' + x) - g z'))‖
          ≤ C * K * ‖z - z'‖ ^ α) := by
  classical
  choose Cf hCfpos hCfb using
    fun i => czHolderEstimate hn hα hα1 hR (hΦm i) hA (hP1 i) (hP2 i) (hH2 i)
  refine ⟨Finset.univ.sup' Finset.univ_nonempty Cf, ?_, ?_⟩
  · exact lt_of_lt_of_le (hCfpos (Classical.arbitrary ι))
      (Finset.le_sup' Cf (Finset.mem_univ _))
  · intro i K hK g hg hsupp
    have hle : Cf i ≤ Finset.univ.sup' Finset.univ_nonempty Cf := Finset.le_sup' Cf (Finset.mem_univ i)
    obtain ⟨hb1, hb2⟩ := hCfb i K hK g hg hsupp
    refine ⟨fun z => ?_, fun z z' => ?_⟩
    · exact le_trans (hb1 z) (mul_le_mul_of_nonneg_right hle hK)
    · exact le_trans (hb2 z z') (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hK) (by positivity))

lemma ofReal_mul_add (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (M : ℝ≥0∞) :
    ENNReal.ofReal a * M + ENNReal.ofReal b * M = ENNReal.ofReal (a + b) * M := by
  rw [← add_mul, ← ENNReal.ofReal_add ha hb]

lemma holderNorm_one_eq {n : ℕ} (α : ℝ) (g : (Fin n → ℂ) → ℂ) (Ω : Set (Fin n → ℂ)) :
    holderNorm 1 α g Ω
      = (iterDerivNorm 0 g Ω + holderSeminorm 0 α g Ω)
        + (iterDerivNorm 1 g Ω + holderSeminorm 1 α g Ω) := by
  rw [holderNorm, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  simp

/-! ## The main theorem -/

/-- **Calderón–Zygmund (Bochner–Martinelli Schauder) estimate for the Bochner–Martinelli
potential.** -/
theorem bmPotential_holder {n : ℕ} (hn : 0 < n) {c : Fin n → ℂ} {r : Fin n → ℝ}
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (hr : ∀ j, 0 < r j) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Fin n → (Fin n → ℂ) → ℂ, (∀ j, ContDiff ℝ 1 (f j)) →
      (∀ j z, (∃ k, r k / 2 ≤ ‖z k - c k‖) → f j z = 0) →
      holderNorm 1 α (Work.CR.Flat.Cauchy.bmPotential f) (polydisc c (fun j => r j / 2))
        ≤ ENNReal.ofReal C * ∑ j, holderNorm 0 α (f j) Set.univ := by
  classical
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set P : Set (Fin n → ℂ) := polydisc c (fun j => r j / 2) with hPdef
  set ρ : ℝ := ∑ j, r j / 2 + ‖c‖ with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]
    have h : 0 < ∑ j, r j / 2 :=
      Finset.sum_pos (fun j _ => by have := hr j; linarith) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    linarith [norm_nonneg c]
  set R : ℝ := 100 * ((n : ℝ) + 1) * (ρ + 1) with hRdef
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have hsqrtpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hsle : Real.sqrt n ≤ (n : ℝ) + 1 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by linarith, ?_⟩
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsle (show (0:ℝ) ≤ 2 * ρ by linarith [hρpos.le])
  have hR2ρ : 2 * ρ ≤ R := by rw [hRdef]; nlinarith [hρpos.le, hn1]
  have hcond : 2 * ρ ≤ R / Real.sqrt n := by
    rw [hRdef, le_div_iff₀ hsqrtpos]
    nlinarith [hmul, hρpos.le, hn1]
  have hmemP : ∀ z : Fin n → ℂ, z ∈ P → ‖z‖ < ρ := by
    intro z hz
    rw [hPdef, mem_polydisc] at hz
    have h1 : ‖z - c‖ ≤ ∑ j, ‖z j - c j‖ := by
      rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ => norm_nonneg _)]
      intro j; exact Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ j)
    have h2 : ∑ j, ‖z j - c j‖ < ∑ j, r j / 2 :=
      Finset.sum_lt_sum (fun j _ => le_of_lt (hz j))
        ⟨⟨0, hn⟩, Finset.mem_univ _, hz ⟨0, hn⟩⟩
    calc ‖z‖ = ‖(z - c) + c‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
      _ < ρ := by rw [hρdef]; linarith
  -- kernel decay
  have hnormker : ∀ (j : Fin n) (x : Fin n → ℂ),
      ‖bmKernel j x‖ ≤ (eucNorm x) ^ (1 - 2 * (n : ℝ)) := by
    intro j x
    rcases eq_or_ne x 0 with hx | hx
    · subst hx
      rw [norm_bmKernel]
      simp only [eucNorm_zero, norm_zero, Pi.zero_apply, zero_div]
      exact Real.rpow_nonneg le_rfl _
    · have hy : 0 < eucNorm x := eucNorm_pos hx
      rw [norm_bmKernel]
      refine (div_le_div_of_nonneg_right (norm_apply_le_eucNorm x j)
        (pow_nonneg (eucNorm_nonneg x) _)).trans_eq ?_
      rw [Real.rpow_sub hy 1 (2 * (n : ℝ)), Real.rpow_one,
        ← Real.rpow_natCast (eucNorm x) (2 * n)]
      congr 1
      push_cast
      ring
  -- the CZ data
  have hmeas_dz : ∀ k j : Fin n, AEStronglyMeasurable (bmDzKernel k j) volume :=
    fun k j => (Work.CR.Flat.Cauchy.bmCz.bmKernel_decay_le hn).1 k j
  have hmeas_dbar : ∀ j k : Fin n, AEStronglyMeasurable (bmDbarKernel j k) volume :=
    fun j k => (Work.CR.Flat.Cauchy.bmCz.bmKernel_decay_le hn).2.1 j k
  obtain ⟨Cdec, hCdecpos, hdec_dz, hdec_dbar⟩ := (Work.CR.Flat.Cauchy.bmCz.bmKernel_decay_le hn).2.2
  obtain ⟨Cdiff_dz, hCdiff_dz_pos, hCdiff_dz⟩ :=
    Work.CR.Flat.Cauchy.bmCz.norm_bmDzKernel_sub_le hn
  obtain ⟨Cdiff_dbar, hCdiff_dbar_pos, hCdiff_dbar⟩ :=
    Work.CR.Flat.Cauchy.bmCz.norm_bmDbarKernel_sub_le hn
  have hsz_dbar : 0 < max Cdec Cdiff_dbar := lt_of_lt_of_le hCdecpos (le_max_left _ _)
  have hsz_dz : 0 < max Cdec Cdiff_dz := lt_of_lt_of_le hCdecpos (le_max_left _ _)
  have hP1_dbar : ∀ p : Fin n × Fin n, ∀ x : Fin n → ℂ, x ≠ 0 →
      ‖bmDbarKernel p.1 p.2 x‖ ≤ max Cdec Cdiff_dbar / (eucNorm x) ^ (2 * n) := by
    intro p x hx
    exact (hdec_dbar p.1 p.2 x hx).trans
      (div_le_div_of_nonneg_right (le_max_left _ _) (pow_nonneg (eucNorm_nonneg x) _))
  have hP2_dbar : ∀ p : Fin n × Fin n, ∀ x h : Fin n → ℂ, 2 * eucNorm h ≤ eucNorm x →
      ‖bmDbarKernel p.1 p.2 (x - h) - bmDbarKernel p.1 p.2 x‖
        ≤ max Cdec Cdiff_dbar * eucNorm h / (eucNorm x) ^ (2 * n + 1) := by
    intro p x h hxh
    calc ‖bmDbarKernel p.1 p.2 (x - h) - bmDbarKernel p.1 p.2 x‖
        ≤ Cdiff_dbar * eucNorm h / (eucNorm x) ^ (2 * n + 1) := hCdiff_dbar p.1 p.2 x h hxh
      _ ≤ max Cdec Cdiff_dbar * eucNorm h / (eucNorm x) ^ (2 * n + 1) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_right _ _) (eucNorm_nonneg h))
            (pow_nonneg (eucNorm_nonneg x) _)
  have hP1_dz : ∀ p : Fin n × Fin n, ∀ x : Fin n → ℂ, x ≠ 0 →
      ‖bmDzKernel p.1 p.2 x‖ ≤ max Cdec Cdiff_dz / (eucNorm x) ^ (2 * n) := by
    intro p x hx
    exact (hdec_dz p.1 p.2 x hx).trans
      (div_le_div_of_nonneg_right (le_max_left _ _) (pow_nonneg (eucNorm_nonneg x) _))
  have hP2_dz : ∀ p : Fin n × Fin n, ∀ x h : Fin n → ℂ, 2 * eucNorm h ≤ eucNorm x →
      ‖bmDzKernel p.1 p.2 (x - h) - bmDzKernel p.1 p.2 x‖
        ≤ max Cdec Cdiff_dz * eucNorm h / (eucNorm x) ^ (2 * n + 1) := by
    intro p x h hxh
    rcases eq_or_lt_of_le (eucNorm_nonneg x) with hx0 | hxpos
    · have hx : x = 0 := eucNorm_eq_zero.mp hx0.symm
      have hh0 : h = 0 := by
        have h2 : eucNorm h = 0 := by
          have := hxh; rw [← hx0] at this
          linarith [eucNorm_nonneg h]
        exact eucNorm_eq_zero.mp h2
      subst hx; subst hh0
      simp
    · calc ‖bmDzKernel p.1 p.2 (x - h) - bmDzKernel p.1 p.2 x‖
          ≤ Cdiff_dz * eucNorm h * (eucNorm x) ^ (-(2 * (n : ℝ) + 1)) := hCdiff_dz p.1 p.2 x h hxh
        _ = Cdiff_dz * eucNorm h / (eucNorm x) ^ (2 * n + 1) := by
            rw [Real.rpow_neg hxpos.le, div_eq_mul_inv,
              ← Real.rpow_natCast (eucNorm x) (2 * n + 1)]
            push_cast
            ring
        _ ≤ max Cdec Cdiff_dz * eucNorm h / (eucNorm x) ^ (2 * n + 1) :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_max_right _ _) (eucNorm_nonneg h))
              (pow_nonneg (eucNorm_nonneg x) _)
  have hH2_dbar : ∀ i : Fin n × Fin n, ∀ a b : ℝ, 0 < a → a < b →
      ∫ x in eucShell a b, bmDbarKernel i.1 i.2 x = 0 :=
    fun i a b ha _ => Work.CR.Flat.Cauchy.bmCz.bmDbarKernel_shell_eq_zero hn ha
  have hH2_dz : ∀ i : Fin n × Fin n, ∀ a b : ℝ, 0 < a → a < b →
      ∫ x in eucShell a b, bmDzKernel i.1 i.2 x = 0 :=
    fun i a b ha _ => Work.CR.Flat.Cauchy.bmCz.integral_bmDzKernel_eucShell_eq_zero (k := i.1) (j := i.2) ha
  haveI : Nonempty (Fin n × Fin n) := ⟨(⟨0, hn⟩, ⟨0, hn⟩)⟩
  obtain ⟨Cbar, hCbarpos, hCbarb⟩ :=
    czHolderBound_uniform hn hα hα1 hRpos (Φ := fun i : Fin n × Fin n => bmDbarKernel i.1 i.2)
      (fun i => hmeas_dbar i.1 i.2) hsz_dbar hP1_dbar hP2_dbar hH2_dbar
  obtain ⟨Cdz, hCdzpos, hCdzb⟩ :=
    czHolderBound_uniform hn hα hα1 hRpos (Φ := fun i : Fin n × Fin n => bmDzKernel i.1 i.2)
      (fun i => hmeas_dz i.1 i.2) hsz_dz hP1_dz hP2_dz hH2_dz
  -- the radial integral bound
  obtain ⟨Crad, hCradpos, hCrad⟩ := Work.CR.Flat.Cauchy.bmCz.eucRadialBound (n := n) hn (1 - 2 * (n : ℝ)) (by linarith)
  have hradial : ∫ x in eucBall (n := n) R, (eucNorm x) ^ (1 - 2 * (n : ℝ)) ≤ Crad * R := by
    have h := hCrad R hRpos
    rw [show (1 - 2 * (n : ℝ)) + 2 * (n : ℝ) = 1 by ring, Real.rpow_one] at h
    exact h
  -- the representation
  obtain ⟨cvec, hrepr_dz, hrepr_dbar⟩ := bmPot_repr hn
  set Cc : ℝ := ∑ j, ∑ k, ‖cvec j k‖ with hCcdef
  have hCcnn : 0 ≤ Cc := Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => norm_nonneg _))
  set C0 : ℝ := 2 * (Crad * R) + 2 * (2 * ((n : ℝ) * (Cdz + Cbar + Cc))) with hC0def
  have hC0pos : 0 < C0 := by rw [hC0def]; positivity
  refine ⟨C0, hC0pos, ?_⟩
  rw [hC0def]
  intro f hf hsupp
  -- support facts
  have hsuppP : ∀ j y, ρ ≤ ‖y‖ → f j y = 0 := by
    intro j y hy
    by_contra hcon
    have hmem : y ∈ P := by
      rw [hPdef, mem_polydisc]
      by_contra h
      obtain ⟨k, hk⟩ := not_forall.mp h
      exact hcon (hsupp j y ⟨k, not_lt.mp hk⟩)
    exact absurd (hmemP y hmem) (not_lt.mpr hy)
  have hsupp_euc : ∀ k x, R ≤ eucNorm x → f k x = 0 := by
    intro k x hx
    refine hsuppP k x ?_
    have h1 : eucNorm x / Real.sqrt n ≤ ‖x‖ := by
      rw [div_le_iff₀ hsqrtpos]
      calc eucNorm x ≤ Real.sqrt n * ‖x‖ := Work.CR.Flat.Cauchy.bmCz.eucNorm_le_sqrt_mul_norm x
        _ = ‖x‖ * Real.sqrt n := by ring
    have hxa : ρ ≤ R / Real.sqrt n := by linarith [hcond]
    exact le_trans hxa (le_trans (div_le_div_of_nonneg_right hx hsqrtpos.le) h1)
  have hsupp_shift : ∀ z, z ∈ P → ∀ k x, R ≤ eucNorm x → f k (z + x) = 0 := by
    intro z hz k x hx
    refine hsuppP k (z + x) ?_
    have hzlt := hmemP z hz
    have hxe : 2 * ρ ≤ ‖x‖ := by
      have h1 : eucNorm x / Real.sqrt n ≤ ‖x‖ := by
        rw [div_le_iff₀ hsqrtpos]
        calc eucNorm x ≤ Real.sqrt n * ‖x‖ := Work.CR.Flat.Cauchy.bmCz.eucNorm_le_sqrt_mul_norm x
          _ = ‖x‖ * Real.sqrt n := by ring
      have hxa : 2 * ρ ≤ R / Real.sqrt n := hcond
      exact le_trans hxa (le_trans (div_le_div_of_nonneg_right hx hsqrtpos.le) h1)
    have h2 : ‖x‖ - ‖z‖ ≤ ‖z + x‖ := by
      have h := norm_sub_le (z + x) z
      rw [add_sub_cancel_left] at h
      linarith
    linarith
  have hsupp_shift_sup : ∀ z, z ∈ P → ∀ k x, R ≤ ‖x‖ → f k (z + x) = 0 := by
    intro z hz k x hx
    refine hsuppP k (z + x) ?_
    have hzlt := hmemP z hz
    have h2 : ‖x‖ - ‖z‖ ≤ ‖z + x‖ := by
      have h := norm_sub_le (z + x) z
      rw [add_sub_cancel_left] at h
      linarith
    linarith
  -- the region / finiteness dichotomy
  have hsupp_sup : ∀ k x, R ≤ ‖x‖ → f k x = 0 := by
    intro k x hx
    exact hsuppP k x (le_trans (by linarith [hρpos.le, hR2ρ]) hx)
  by_cases hMtop : (∑ j, holderNorm 0 α (f j) Set.univ) = ⊤
  · rw [hMtop]
    have hne : ENNReal.ofReal C0 ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact hC0pos
    rw [ENNReal.mul_top hne]
    exact le_top
  · have hfin : ∀ k, iterDerivNorm 0 (f k) Set.univ ≠ ⊤ ∧ holderSeminorm 0 α (f k) Set.univ ≠ ⊤ := by
      intro k
      have h2 : holderNorm 0 α (f k) Set.univ ≤ ∑ j, holderNorm 0 α (f j) Set.univ :=
        Finset.single_le_sum (f := fun j => holderNorm 0 α (f j) Set.univ)
          (fun i _ => bot_le) (Finset.mem_univ k)
      have h3 : iterDerivNorm 0 (f k) Set.univ ≤ ∑ j, holderNorm 0 α (f j) Set.univ := by
        calc iterDerivNorm 0 (f k) Set.univ
            ≤ iterDerivNorm 0 (f k) Set.univ + holderSeminorm 0 α (f k) Set.univ :=
              le_add_of_nonneg_right bot_le
          _ = holderNorm 0 α (f k) Set.univ := (holderNorm_zero_eq α (f k) Set.univ).symm
          _ ≤ ∑ j, holderNorm 0 α (f j) Set.univ := h2
      have h4 : holderSeminorm 0 α (f k) Set.univ ≤ ∑ j, holderNorm 0 α (f j) Set.univ := by
        calc holderSeminorm 0 α (f k) Set.univ
            ≤ iterDerivNorm 0 (f k) Set.univ + holderSeminorm 0 α (f k) Set.univ :=
              le_add_of_nonneg_left bot_le
          _ = holderNorm 0 α (f k) Set.univ := (holderNorm_zero_eq α (f k) Set.univ).symm
          _ ≤ ∑ j, holderNorm 0 α (f j) Set.univ := h2
      exact ⟨ne_top_of_le_ne_top hMtop h3, ne_top_of_le_ne_top hMtop h4⟩
    set a : Fin n → ℝ := fun k => (iterDerivNorm 0 (f k) Set.univ).toReal with hadef
    set hh : Fin n → ℝ := fun k => (holderSeminorm 0 α (f k) Set.univ).toReal with hhdef
    set M' : ℝ := ∑ k, (a k + hh k) with hM'def
    have hann : ∀ k, 0 ≤ a k ∧ 0 ≤ hh k := by
      intro k
      rw [hadef, hhdef]
      exact ⟨ENNReal.toReal_nonneg, ENNReal.toReal_nonneg⟩
    have ha_bound : ∀ k y, ‖f k y‖ ≤ a k := by
      intro k y
      have h1 : ENNReal.ofReal ‖f k y‖ ≤ iterDerivNorm 0 (f k) Set.univ := by
        rw [← norm_iteratedFDerivWithin_zero (𝕜 := ℝ) (s := Set.univ) (f := f k) (x := y)]
        exact le_iterDerivNorm 0 (f k) Set.univ (Set.mem_univ y)
      have h2 := (ENNReal.ofReal_le_iff_le_toReal (hfin k).1).mp h1
      simpa only [hadef] using h2
    have hhh : ∀ k x y, ‖f k x - f k y‖ ≤ hh k * ‖x - y‖ ^ α := by
      intro k x y
      rcases eq_or_ne x y with hxy | hxy
      · subst hxy; simp [Real.zero_rpow (ne_of_gt hα)]
      · have h1 : ENNReal.ofReal (‖iteratedFDerivWithin ℝ 0 (f k) Set.univ x
              - iteratedFDerivWithin ℝ 0 (f k) Set.univ y‖ / ‖x - y‖ ^ α)
            ≤ holderSeminorm 0 α (f k) Set.univ :=
          le_holderSeminorm 0 α (f k) Set.univ (Set.mem_univ x) (Set.mem_univ y) hxy
        rw [norm_iteratedFDerivWithin_zero_sub (f k) Set.univ x y] at h1
        have h2 := (ENNReal.ofReal_le_iff_le_toReal (hfin k).2).mp h1
        have h3 : ‖f k x - f k y‖ / ‖x - y‖ ^ α ≤ hh k := by simpa only [hhdef] using h2
        rw [div_le_iff₀ (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α)] at h3
        exact h3
    have hM'le : ENNReal.ofReal M' ≤ ∑ j, holderNorm 0 α (f j) Set.univ := by
      rw [hM'def, ENNReal.ofReal_sum_of_nonneg (fun k _ => add_nonneg (hann k).1 (hann k).2)]
      refine Finset.sum_le_sum (fun k _ => ?_)
      rw [holderNorm_zero_eq, ENNReal.ofReal_add (hann k).1 (hann k).2]
      exact add_le_add ENNReal.ofReal_toReal_le ENNReal.ofReal_toReal_le
    -- the representations
    have hdbar_rep : ∀ j (z : Fin n → ℂ), z ∈ P →
        dbarCoord j (bmPotential f) z
          = -∑ k, (∫ x in eucBall (4 * R), bmDbarKernel j k x * (f k (z + x) - f k z))
            - ∑ k, cvec j k * f k z := by
      intro j z hz
      rw [show bmPotential f = bmPot f from funext (bmPotential_eq_bmPot f)]
      rw [bmPot_dbarCoord hn hf hRpos (fun k x hx => hsupp_sup k x hx) j z]
      calc ∑ k, ∫ x, bmKernel k x * dbarCoord j (f k) (z + x)
          = ∑ k, ((-∫ x in eucBall (4 * R), bmDbarKernel j k x * (f k (z + x) - f k z))
              - cvec j k * f k z) := by
            refine Finset.sum_congr rfl (fun k _ => ?_)
            have hcomp : (∫ x, bmKernel k x * dbarCoord j (f k) (z + x))
                = ∫ x, bmKernel k x * dbarCoord j (fun y => f k (z + y)) x := by
              apply integral_congr_ae
              filter_upwards with x
              rw [dbarCoord_comp_add j (((hf k).differentiable one_ne_zero).differentiableAt)]
            rw [hcomp, hrepr_dbar j k (fun y => f k (z + y)) R hRpos
              ((hf k).comp (contDiff_const.add contDiff_id))
              (fun x hx => hsupp_shift z hz k x hx)]
            simp only [add_zero]
        _ = (∑ k, (-∫ x in eucBall (4 * R), bmDbarKernel j k x * (f k (z + x) - f k z)))
              - ∑ k, cvec j k * f k z :=
            Finset.sum_sub_distrib (f := fun k => -∫ x in eucBall (4 * R),
                bmDbarKernel j k x * (f k (z + x) - f k z)) (g := fun k => cvec j k * f k z)
        _ = -∑ k, (∫ x in eucBall (4 * R), bmDbarKernel j k x * (f k (z + x) - f k z))
              - ∑ k, cvec j k * f k z := by
            rw [Finset.sum_neg_distrib (f := fun k => ∫ x in eucBall (4 * R),
              bmDbarKernel j k x * (f k (z + x) - f k z))]
    have hdCoord_rep : ∀ j (z : Fin n → ℂ), z ∈ P →
        dCoord j (bmPotential f) z
          = -∑ k, (∫ x in eucBall (4 * R), bmDzKernel j k x * (f k (z + x) - f k z)) := by
      intro j z hz
      rw [show bmPotential f = bmPot f from funext (bmPotential_eq_bmPot f)]
      rw [Work.CR.Flat.Cauchy.bmCz.bmPot_dCoord hn hf hRpos (fun k x hx => hsupp_sup k x hx) j z]
      calc ∑ k, ∫ x, bmKernel k x * dCoord j (f k) (z + x)
          = ∑ k, (-∫ x in eucBall (4 * R), bmDzKernel j k x * (f k (z + x) - f k z)) := by
            refine Finset.sum_congr rfl (fun k _ => ?_)
            have hcomp : (∫ x, bmKernel k x * dCoord j (f k) (z + x))
                = ∫ x, bmKernel k x * dCoord j (fun y => f k (z + y)) x := by
              apply integral_congr_ae
              filter_upwards with x
              rw [dCoord_comp_add j (((hf k).differentiable one_ne_zero).differentiableAt)]
            rw [hcomp, hrepr_dz j k (fun y => f k (z + y)) R hRpos
              ((hf k).comp (contDiff_const.add contDiff_id))
              (fun x hx => hsupp_shift z hz k x hx)]
            simp only [add_zero]
        _ = -∑ k, (∫ x in eucBall (4 * R), bmDzKernel j k x * (f k (z + x) - f k z)) :=
            Finset.sum_neg_distrib (f := fun k => ∫ x in eucBall (4 * R),
              bmDzKernel j k x * (f k (z + x) - f k z))
    -- the sup bound
    have hsup_bound : ∀ z, z ∈ P → ‖bmPotential f z‖ ≤ (Crad * R) * M' := by
      intro z hz
      have hshift : ∀ k x, R ≤ eucNorm x → f k (z + x) = 0 := fun k x hx => hsupp_shift z hz k x hx
      rw [bmPotential_eq_sum_ball (z := z) hshift]
      have hterm : ∀ k, ‖∫ x in eucBall R, bmKernel k x * f k (z + x)‖ ≤ a k * (Crad * R) := by
        intro k
        have hcont : Continuous (fun x => f k (z + x)) :=
          (hf k).continuous.comp (continuous_const.add continuous_id)
        have hcs : HasCompactSupport (fun x => f k (z + x)) := hasCompactSupport_of_eucNorm (hshift k)
        have hint : IntegrableOn (fun x => bmKernel k x * f k (z + x)) (eucBall R) :=
          integrableOn_bmKernel_mul hn k hcont hcs
        have hmaj : IntegrableOn (fun x => a k * (eucNorm x) ^ (1 - 2 * (n : ℝ))) (eucBall R) :=
          (integrableOn_eucNorm_rpow hn (by linarith) (by linarith) R).const_mul (a k)
        have hle : ∀ x ∈ eucBall R,
            ‖bmKernel k x * f k (z + x)‖ ≤ a k * (eucNorm x) ^ (1 - 2 * (n : ℝ)) := by
          intro x _
          rw [norm_mul, mul_comm]
          exact mul_le_mul (ha_bound k (z + x)) (hnormker k x) (norm_nonneg _) (hann k).1
        calc ‖∫ x in eucBall R, bmKernel k x * f k (z + x)‖
            ≤ ∫ x in eucBall R, a k * (eucNorm x) ^ (1 - 2 * (n : ℝ)) :=
              norm_setIntegral_le_of_norm_le' (measurableSet_eucBall R) hmaj hle
          _ = a k * ∫ x in eucBall R, (eucNorm x) ^ (1 - 2 * (n : ℝ)) :=
              MeasureTheory.integral_const_mul _ _
          _ ≤ a k * (Crad * R) := mul_le_mul_of_nonneg_left hradial (hann k).1
      calc ‖∑ k, ∫ x in eucBall R, bmKernel k x * f k (z + x)‖
          ≤ ∑ k, ‖∫ x in eucBall R, bmKernel k x * f k (z + x)‖ := norm_sum_le _ _
        _ ≤ ∑ k, a k * (Crad * R) := Finset.sum_le_sum (fun k _ => hterm k)
        _ = (∑ k, a k) * (Crad * R) := by rw [Finset.sum_mul]
        _ ≤ M' * (Crad * R) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            rw [hM'def]
            exact Finset.sum_le_sum (fun k _ => le_add_of_nonneg_right (hann k).2)
        _ = (Crad * R) * M' := by ring
    -- the Holder bound for the potential
    have hholder_u : ∀ x y, x ∈ P → y ∈ P →
        ‖bmPotential f x - bmPotential f y‖ ≤ (Crad * R) * M' * ‖x - y‖ ^ α := by
      intro x y hx hy
      have hsx : ∀ k z, R ≤ eucNorm z → f k (x + z) = 0 := fun k z hz => hsupp_shift x hx k z hz
      have hsy : ∀ k z, R ≤ eucNorm z → f k (y + z) = 0 := fun k z hz => hsupp_shift y hy k z hz
      rw [bmPotential_eq_sum_ball (z := x) hsx, bmPotential_eq_sum_ball (z := y) hsy,
        ← Finset.sum_sub_distrib]
      have hterm : ∀ k, ‖(∫ z in eucBall R, bmKernel k z * f k (x + z))
          - (∫ z in eucBall R, bmKernel k z * f k (y + z))‖
          ≤ hh k * (Crad * R) * ‖x - y‖ ^ α := by
        intro k
        have hcsz : HasCompactSupport (fun z => f k (x + z)) := hasCompactSupport_of_eucNorm (hsx k)
        have hcsy : HasCompactSupport (fun z => f k (y + z)) := hasCompactSupport_of_eucNorm (hsy k)
        have hix : IntegrableOn (fun z => bmKernel k z * f k (x + z)) (eucBall R) :=
          integrableOn_bmKernel_mul hn k
            ((hf k).continuous.comp (continuous_const.add continuous_id)) hcsz
        have hiy : IntegrableOn (fun z => bmKernel k z * f k (y + z)) (eucBall R) :=
          integrableOn_bmKernel_mul hn k
            ((hf k).continuous.comp (continuous_const.add continuous_id)) hcsy
        have hmaj : IntegrableOn (fun z => hh k * ‖x - y‖ ^ α * (eucNorm z) ^ (1 - 2 * (n : ℝ)))
            (eucBall R) :=
          (integrableOn_eucNorm_rpow hn (by linarith) (by linarith) R).const_mul _
        have hle : ∀ z ∈ eucBall R, ‖bmKernel k z * (f k (x + z) - f k (y + z))‖
            ≤ hh k * ‖x - y‖ ^ α * (eucNorm z) ^ (1 - 2 * (n : ℝ)) := by
          intro z _
          rw [norm_mul]
          have hxy : (x + z) - (y + z) = x - y := by abel
          calc ‖bmKernel k z‖ * ‖f k (x + z) - f k (y + z)‖
              ≤ (eucNorm z) ^ (1 - 2 * (n : ℝ)) * (hh k * ‖x - y‖ ^ α) := by
                refine mul_le_mul (hnormker k z) ?_ (norm_nonneg _)
                  (Real.rpow_nonneg (eucNorm_nonneg z) _)
                rw [← hxy]; exact hhh k (x + z) (y + z)
            _ = hh k * ‖x - y‖ ^ α * (eucNorm z) ^ (1 - 2 * (n : ℝ)) := by ring
        have hcongr : (∫ z in eucBall R,
              (bmKernel k z * f k (x + z) - bmKernel k z * f k (y + z)))
            = ∫ z in eucBall R, bmKernel k z * (f k (x + z) - f k (y + z)) := by
          apply integral_congr_ae
          filter_upwards with z
          ring
        rw [← integral_sub hix hiy, hcongr]
        calc ‖∫ z in eucBall R, bmKernel k z * (f k (x + z) - f k (y + z))‖
            ≤ ∫ z in eucBall R, hh k * ‖x - y‖ ^ α * (eucNorm z) ^ (1 - 2 * (n : ℝ)) :=
              norm_setIntegral_le_of_norm_le' (measurableSet_eucBall R) hmaj hle
          _ = hh k * ‖x - y‖ ^ α * ∫ z in eucBall R, (eucNorm z) ^ (1 - 2 * (n : ℝ)) :=
              MeasureTheory.integral_const_mul _ _
          _ ≤ hh k * ‖x - y‖ ^ α * (Crad * R) :=
              mul_le_mul_of_nonneg_left hradial (by positivity)
          _ = hh k * (Crad * R) * ‖x - y‖ ^ α := by ring
      calc ‖∑ k, ((∫ z in eucBall R, bmKernel k z * f k (x + z))
            - (∫ z in eucBall R, bmKernel k z * f k (y + z)))‖
          ≤ ∑ k, ‖(∫ z in eucBall R, bmKernel k z * f k (x + z))
            - (∫ z in eucBall R, bmKernel k z * f k (y + z))‖ := norm_sum_le _ _
        _ ≤ ∑ k, hh k * (Crad * R) * ‖x - y‖ ^ α := Finset.sum_le_sum (fun k _ => hterm k)
        _ = (∑ k, hh k) * ((Crad * R) * ‖x - y‖ ^ α) := by
            rw [Finset.sum_congr rfl (fun k _ => show hh k * (Crad * R) * ‖x - y‖ ^ α
              = hh k * ((Crad * R) * ‖x - y‖ ^ α) from by ring)]
            exact (Finset.sum_mul Finset.univ hh _).symm
        _ ≤ M' * ((Crad * R) * ‖x - y‖ ^ α) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            rw [hM'def]
            exact Finset.sum_le_sum (fun k _ => le_add_of_nonneg_left (hann k).1)
        _ = (Crad * R) * M' * ‖x - y‖ ^ α := by ring
    -- the gradient bounds
    have hdbar_le : ∀ j z, z ∈ P → ‖dbarCoord j (bmPotential f) z‖ ≤ (Cbar + Cc) * M' := by
      intro j z hz
      rw [hdbar_rep j z hz]
      have h1 : ‖∑ k, (∫ x in eucBall (4 * R), bmDbarKernel j k x * (f k (z + x) - f k z))‖
          ≤ ∑ k, Cbar * hh k :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ =>
          (hCbarb (j, k) (hh k) (hann k).2 (f k) (hhh k)
            (fun x hx => hsupp_sup k x hx)).1 z))
      have h2 : ‖∑ k, cvec j k * f k z‖ ≤ ∑ k, ‖cvec j k‖ * a k :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (ha_bound k z) (norm_nonneg _)))
      have h3 : ∑ k, Cbar * hh k ≤ Cbar * M' := by
        rw [hM'def, Finset.mul_sum]
        exact Finset.sum_le_sum (fun k _ => by
          rw [mul_add]
          exact le_add_of_nonneg_left (mul_nonneg hCbarpos.le (hann k).1))
      have h4 : ∑ k, ‖cvec j k‖ * a k ≤ Cc * M' := by
        have h5 : ∑ k, ‖cvec j k‖ * a k ≤ (∑ k, ‖cvec j k‖) * (∑ k, a k) := by
          calc ∑ k, ‖cvec j k‖ * a k
              ≤ ∑ k, (∑ i, ‖cvec j i‖) * a k := Finset.sum_le_sum (fun k _ =>
                  mul_le_mul_of_nonneg_right
                    (Finset.single_le_sum (f := fun i => ‖cvec j i‖)
                      (fun i _ => norm_nonneg _) (Finset.mem_univ k)) (hann k).1)
            _ = (∑ i, ‖cvec j i‖) * (∑ k, a k) := by rw [Finset.mul_sum]
        have h6 : (∑ k, a k) ≤ M' := by
          rw [hM'def]
          exact Finset.sum_le_sum (fun k _ => le_add_of_nonneg_right (hann k).2)
        have h7 : (∑ k, ‖cvec j k‖) ≤ Cc := by
          rw [hCcdef]
          exact Finset.single_le_sum (f := fun i => ∑ k, ‖cvec i k‖)
            (fun i _ => Finset.sum_nonneg (fun k _ => norm_nonneg _)) (Finset.mem_univ j)
        calc ∑ k, ‖cvec j k‖ * a k ≤ (∑ k, ‖cvec j k‖) * (∑ k, a k) := h5
          _ ≤ (∑ k, ‖cvec j k‖) * M' := mul_le_mul_of_nonneg_left h6 (by positivity)
          _ ≤ Cc * M' := mul_le_mul_of_nonneg_right h7 (by positivity)
      calc ‖-∑ k, (∫ x in eucBall (4 * R), bmDbarKernel j k x * (f k (z + x) - f k z))
            - ∑ k, cvec j k * f k z‖
          ≤ ‖-∑ k, (∫ x in eucBall (4 * R), bmDbarKernel j k x * (f k (z + x) - f k z))‖
            + ‖∑ k, cvec j k * f k z‖ := norm_sub_le _ _
        _ = ‖∑ k, (∫ x in eucBall (4 * R), bmDbarKernel j k x * (f k (z + x) - f k z))‖
            + ‖∑ k, cvec j k * f k z‖ := by rw [norm_neg]
        _ ≤ (∑ k, Cbar * hh k) + (∑ k, ‖cvec j k‖ * a k) := add_le_add h1 h2
        _ ≤ Cbar * M' + Cc * M' := add_le_add h3 h4
        _ = (Cbar + Cc) * M' := by ring
    have hdCoord_le : ∀ j z, z ∈ P → ‖dCoord j (bmPotential f) z‖ ≤ Cdz * M' := by
      intro j z hz
      rw [hdCoord_rep j z hz]
      calc ‖-∑ k, (∫ x in eucBall (4 * R), bmDzKernel j k x * (f k (z + x) - f k z))‖
          = ‖∑ k, (∫ x in eucBall (4 * R), bmDzKernel j k x * (f k (z + x) - f k z))‖ :=
            norm_neg _
        _ ≤ ∑ k, Cdz * hh k :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ =>
              (hCdzb (j, k) (hh k) (hann k).2 (f k) (hhh k)
                (fun x hx => hsupp_sup k x hx)).1 z))
        _ ≤ Cdz * M' := by
            rw [hM'def, Finset.mul_sum]
            exact Finset.sum_le_sum (fun k _ => by
              rw [mul_add]
              exact le_add_of_nonneg_left (mul_nonneg hCdzpos.le (hann k).1))
    have hdCoord_holder : ∀ j x y, x ∈ P → y ∈ P →
        ‖dCoord j (bmPotential f) x - dCoord j (bmPotential f) y‖ ≤ Cdz * M' * ‖x - y‖ ^ α := by
      intro j x y hx hy
      rw [hdCoord_rep j x hx, hdCoord_rep j y hy]
      have hsplit : (-∑ k, (∫ z in eucBall (4 * R), bmDzKernel j k z * (f k (x + z) - f k x)))
            - (-∑ k, (∫ z in eucBall (4 * R), bmDzKernel j k z * (f k (y + z) - f k y)))
          = -∑ k, ((∫ z in eucBall (4 * R), bmDzKernel j k z * (f k (x + z) - f k x))
              - (∫ z in eucBall (4 * R), bmDzKernel j k z * (f k (y + z) - f k y))) := by
        rw [Finset.sum_sub_distrib]
        ring
      rw [hsplit, norm_neg]
      calc ‖∑ k, ((∫ z in eucBall (4 * R), bmDzKernel j k z * (f k (x + z) - f k x))
              - (∫ z in eucBall (4 * R), bmDzKernel j k z * (f k (y + z) - f k y)))‖
          ≤ ∑ k, ‖(∫ z in eucBall (4 * R), bmDzKernel j k z * (f k (x + z) - f k x))
              - (∫ z in eucBall (4 * R), bmDzKernel j k z * (f k (y + z) - f k y))‖ :=
            norm_sum_le _ _
        _ ≤ ∑ k, Cdz * hh k * ‖x - y‖ ^ α := Finset.sum_le_sum (fun k _ =>
              (hCdzb (j, k) (hh k) (hann k).2 (f k) (hhh k)
                (fun z hz => hsupp_sup k z hz)).2 x y)
        _ = Cdz * (∑ k, hh k) * ‖x - y‖ ^ α := by
            rw [(Finset.sum_mul Finset.univ (fun k => Cdz * hh k) (‖x - y‖ ^ α)).symm,
              (Finset.mul_sum Finset.univ hh Cdz).symm]
        _ ≤ Cdz * M' * ‖x - y‖ ^ α := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            refine mul_le_mul_of_nonneg_left ?_ hCdzpos.le
            rw [hM'def]
            exact Finset.sum_le_sum (fun k _ => le_add_of_nonneg_left (hann k).1)
    have hdbar_holder : ∀ j x y, x ∈ P → y ∈ P →
        ‖dbarCoord j (bmPotential f) x - dbarCoord j (bmPotential f) y‖
          ≤ (Cbar + Cc) * M' * ‖x - y‖ ^ α := by
      intro j x y hx hy
      rw [hdbar_rep j x hx, hdbar_rep j y hy]
      have hsplit : ((-∑ k, (∫ z in eucBall (4 * R), bmDbarKernel j k z * (f k (x + z) - f k x)))
              - ∑ k, cvec j k * f k x)
            - ((-∑ k, (∫ z in eucBall (4 * R), bmDbarKernel j k z * (f k (y + z) - f k y)))
              - ∑ k, cvec j k * f k y)
          = -∑ k, ((∫ z in eucBall (4 * R), bmDbarKernel j k z * (f k (x + z) - f k x))
              - (∫ z in eucBall (4 * R), bmDbarKernel j k z * (f k (y + z) - f k y)))
            - ∑ k, cvec j k * (f k x - f k y) := by
        rw [Finset.sum_sub_distrib (f := fun k => ∫ z in eucBall (4 * R),
              bmDbarKernel j k z * (f k (x + z) - f k x))
              (g := fun k => ∫ z in eucBall (4 * R),
                bmDbarKernel j k z * (f k (y + z) - f k y)),
          show (∑ k, cvec j k * (f k x - f k y)) = (∑ k, cvec j k * f k x)
              - ∑ k, cvec j k * f k y from by
            rw [← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl (fun k _ => by ring)]
        ring
      rw [hsplit]
      have h1 : ‖∑ k, ((∫ z in eucBall (4 * R), bmDbarKernel j k z * (f k (x + z) - f k x))
              - (∫ z in eucBall (4 * R), bmDbarKernel j k z * (f k (y + z) - f k y)))‖
          ≤ ∑ k, Cbar * hh k * ‖x - y‖ ^ α :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ =>
          (hCbarb (j, k) (hh k) (hann k).2 (f k) (hhh k)
            (fun z hz => hsupp_sup k z hz)).2 x y))
      have h2 : ‖∑ k, cvec j k * (f k x - f k y)‖ ≤ ∑ k, ‖cvec j k‖ * hh k * ‖x - y‖ ^ α :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => by
          rw [norm_mul]
          calc ‖cvec j k‖ * ‖f k x - f k y‖ ≤ ‖cvec j k‖ * (hh k * ‖x - y‖ ^ α) :=
                mul_le_mul_of_nonneg_left (hhh k x y) (norm_nonneg _)
            _ = ‖cvec j k‖ * hh k * ‖x - y‖ ^ α := by ring))
      have h3 : ∑ k, Cbar * hh k * ‖x - y‖ ^ α ≤ Cbar * M' * ‖x - y‖ ^ α := by
        rw [(Finset.sum_mul Finset.univ (fun k => Cbar * hh k) (‖x - y‖ ^ α)).symm,
          (Finset.mul_sum Finset.univ hh Cbar).symm]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        refine mul_le_mul_of_nonneg_left ?_ hCbarpos.le
        rw [hM'def]
        exact Finset.sum_le_sum (fun k _ => le_add_of_nonneg_left (hann k).1)
      have h4 : ∑ k, ‖cvec j k‖ * hh k * ‖x - y‖ ^ α ≤ Cc * M' * ‖x - y‖ ^ α := by
        rw [(Finset.sum_mul Finset.univ (fun k => ‖cvec j k‖ * hh k) (‖x - y‖ ^ α)).symm]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        calc ∑ k, ‖cvec j k‖ * hh k ≤ (∑ k, ‖cvec j k‖) * (∑ k, hh k) := by
              calc ∑ k, ‖cvec j k‖ * hh k ≤ ∑ k, (∑ i, ‖cvec j i‖) * hh k :=
                    Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right
                      (Finset.single_le_sum (f := fun i => ‖cvec j i‖)
                        (fun i _ => norm_nonneg _) (Finset.mem_univ k)) (hann k).2)
                _ = (∑ i, ‖cvec j i‖) * (∑ k, hh k) := by rw [Finset.mul_sum]
          _ ≤ (∑ k, ‖cvec j k‖) * M' := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              rw [hM'def]
              exact Finset.sum_le_sum (fun k _ => le_add_of_nonneg_left (hann k).1)
          _ ≤ Cc * M' := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              rw [hCcdef]
              exact Finset.single_le_sum (f := fun i => ∑ k, ‖cvec i k‖)
                (fun i _ => Finset.sum_nonneg (fun k _ => norm_nonneg _)) (Finset.mem_univ j)
      calc ‖-∑ k, ((∫ z in eucBall (4 * R), bmDbarKernel j k z * (f k (x + z) - f k x))
              - (∫ z in eucBall (4 * R), bmDbarKernel j k z * (f k (y + z) - f k y)))
            - ∑ k, cvec j k * (f k x - f k y)‖
          ≤ ‖-∑ k, ((∫ z in eucBall (4 * R), bmDbarKernel j k z * (f k (x + z) - f k x))
              - (∫ z in eucBall (4 * R), bmDbarKernel j k z * (f k (y + z) - f k y)))‖
            + ‖∑ k, cvec j k * (f k x - f k y)‖ := norm_sub_le _ _
        _ = ‖∑ k, ((∫ z in eucBall (4 * R), bmDbarKernel j k z * (f k (x + z) - f k x))
              - (∫ z in eucBall (4 * R), bmDbarKernel j k z * (f k (y + z) - f k y)))‖
            + ‖∑ k, cvec j k * (f k x - f k y)‖ := by rw [norm_neg]
        _ ≤ (∑ k, Cbar * hh k * ‖x - y‖ ^ α) + (∑ k, ‖cvec j k‖ * hh k * ‖x - y‖ ^ α) :=
            add_le_add h1 h2
        _ ≤ Cbar * M' * ‖x - y‖ ^ α + Cc * M' * ‖x - y‖ ^ α := add_le_add h3 h4
        _ = (Cbar + Cc) * M' * ‖x - y‖ ^ α := by ring
    set G2 : ℝ := 2 * ((n : ℝ) * (Cdz + Cbar + Cc)) with hG2def
    have hfderiv_le : ∀ z, z ∈ P → ‖fderiv ℝ (bmPotential f) z‖ ≤ G2 * M' := by
      intro z hz
      calc ‖fderiv ℝ (bmPotential f) z‖
          ≤ 2 * ∑ j, (‖dCoord j (bmPotential f) z‖ + ‖dbarCoord j (bmPotential f) z‖) :=
            norm_fderiv_le_wirtinger _ _
        _ ≤ 2 * ∑ j, (Cdz * M' + (Cbar + Cc) * M') :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ =>
              add_le_add (hdCoord_le j z hz) (hdbar_le j z hz))) (by norm_num)
        _ = G2 * M' := by
            rw [hG2def, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            push_cast
            ring
    have hfderiv_holder : ∀ x y, x ∈ P → y ∈ P →
        ‖fderiv ℝ (bmPotential f) x - fderiv ℝ (bmPotential f) y‖ ≤ G2 * M' * ‖x - y‖ ^ α := by
      intro x y hx hy
      calc ‖fderiv ℝ (bmPotential f) x - fderiv ℝ (bmPotential f) y‖
          ≤ 2 * ∑ j, (‖dCoord j (bmPotential f) x - dCoord j (bmPotential f) y‖
              + ‖dbarCoord j (bmPotential f) x - dbarCoord j (bmPotential f) y‖) :=
            norm_fderiv_sub_le_wirtinger _ _ _
        _ ≤ 2 * ∑ j, (Cdz * M' * ‖x - y‖ ^ α + (Cbar + Cc) * M' * ‖x - y‖ ^ α) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ =>
              add_le_add (hdCoord_holder j x y hx hy) (hdbar_holder j x y hx hy))) (by norm_num)
        _ = G2 * M' * ‖x - y‖ ^ α := by
            rw [hG2def, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            push_cast
            ring
    -- assembling the four norms
    set M : ℝ≥0∞ := ∑ j, holderNorm 0 α (f j) Set.univ with hMdef
    have hPopen : IsOpen P := by rw [hPdef]; exact isOpen_polydisc c _
    have hE1 : iterDerivNorm 0 (bmPotential f) P ≤ ENNReal.ofReal (Crad * R) * M := by
      rw [iterDerivNorm]
      refine iSup₂_le (fun z hz => ?_)
      rw [norm_iteratedFDerivWithin_zero]
      calc ENNReal.ofReal ‖bmPotential f z‖ ≤ ENNReal.ofReal ((Crad * R) * M') :=
            ENNReal.ofReal_le_ofReal (hsup_bound z hz)
        _ = ENNReal.ofReal (Crad * R) * ENNReal.ofReal M' := ENNReal.ofReal_mul (by positivity)
        _ ≤ ENNReal.ofReal (Crad * R) * M := by
            rw [hMdef]; exact mul_le_mul_right hM'le _
    have hE2 : holderSeminorm 0 α (bmPotential f) P ≤ ENNReal.ofReal (Crad * R) * M := by
      rw [holderSeminorm]
      refine iSup₂_le (fun x hx => iSup₂_le (fun y hy => iSup_le (fun hxy => ?_)))
      rw [norm_iteratedFDerivWithin_zero_sub]
      have hb : ‖bmPotential f x - bmPotential f y‖ / ‖x - y‖ ^ α ≤ (Crad * R) * M' := by
        rw [div_le_iff₀ (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α)]
        simpa only [mul_assoc] using hholder_u x y hx hy
      calc ENNReal.ofReal (‖bmPotential f x - bmPotential f y‖ / ‖x - y‖ ^ α)
          ≤ ENNReal.ofReal ((Crad * R) * M') := ENNReal.ofReal_le_ofReal hb
        _ = ENNReal.ofReal (Crad * R) * ENNReal.ofReal M' := ENNReal.ofReal_mul (by positivity)
        _ ≤ ENNReal.ofReal (Crad * R) * M := by
            rw [hMdef]; exact mul_le_mul_right hM'le _
    have hE3 : iterDerivNorm 1 (bmPotential f) P ≤ ENNReal.ofReal G2 * M := by
      rw [iterDerivNorm]
      refine iSup₂_le (fun z hz => ?_)
      rw [norm_iteratedFDerivWithin_one (bmPotential f) (hPopen.uniqueDiffWithinAt hz),
        fderivWithin_of_isOpen hPopen hz]
      calc ENNReal.ofReal ‖fderiv ℝ (bmPotential f) z‖ ≤ ENNReal.ofReal (G2 * M') :=
            ENNReal.ofReal_le_ofReal (hfderiv_le z hz)
        _ = ENNReal.ofReal G2 * ENNReal.ofReal M' := ENNReal.ofReal_mul (by positivity)
        _ ≤ ENNReal.ofReal G2 * M := by
            rw [hMdef]; exact mul_le_mul_right hM'le _
    have hE4 : holderSeminorm 1 α (bmPotential f) P ≤ ENNReal.ofReal G2 * M := by
      rw [holderSeminorm]
      refine iSup₂_le (fun x hx => iSup₂_le (fun y hy => iSup_le (fun hxy => ?_)))
      have hI : ‖iteratedFDerivWithin ℝ 1 (bmPotential f) P x
            - iteratedFDerivWithin ℝ 1 (bmPotential f) P y‖
          ≤ ‖fderiv ℝ (bmPotential f) x - fderiv ℝ (bmPotential f) y‖ :=
        (iteratedFDerivWithin_one_sub_le (bmPotential f) P x y
          (hPopen.uniqueDiffWithinAt hx) (hPopen.uniqueDiffWithinAt hy)).trans
          (le_of_eq (by rw [fderivWithin_of_isOpen hPopen hx, fderivWithin_of_isOpen hPopen hy]))
      have hb : ‖iteratedFDerivWithin ℝ 1 (bmPotential f) P x
            - iteratedFDerivWithin ℝ 1 (bmPotential f) P y‖ / ‖x - y‖ ^ α ≤ G2 * M' := by
        rw [div_le_iff₀ (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α)]
        exact hI.trans (by simpa only [mul_assoc] using hfderiv_holder x y hx hy)
      calc ENNReal.ofReal (‖iteratedFDerivWithin ℝ 1 (bmPotential f) P x
            - iteratedFDerivWithin ℝ 1 (bmPotential f) P y‖ / ‖x - y‖ ^ α)
          ≤ ENNReal.ofReal (G2 * M') := ENNReal.ofReal_le_ofReal hb
        _ = ENNReal.ofReal G2 * ENNReal.ofReal M' := ENNReal.ofReal_mul (by positivity)
        _ ≤ ENNReal.ofReal G2 * M := by
            rw [hMdef]; exact mul_le_mul_right hM'le _
    rw [holderNorm_one_eq]
    calc ((iterDerivNorm 0 (bmPotential f) P + holderSeminorm 0 α (bmPotential f) P)
          + (iterDerivNorm 1 (bmPotential f) P + holderSeminorm 1 α (bmPotential f) P))
        ≤ (ENNReal.ofReal (Crad * R) * M + ENNReal.ofReal (Crad * R) * M)
          + (ENNReal.ofReal G2 * M + ENNReal.ofReal G2 * M) :=
          add_le_add (add_le_add hE1 hE2) (add_le_add hE3 hE4)
      _ = ENNReal.ofReal (2 * (Crad * R) + 2 * G2) * M := by
          rw [ofReal_mul_add (Crad * R) (Crad * R) (by positivity) (by positivity),
            ofReal_mul_add G2 G2 (by positivity) (by positivity),
            ofReal_mul_add (Crad * R + Crad * R) (G2 + G2) (by positivity) (by positivity),
            show (Crad * R + Crad * R) + (G2 + G2) = 2 * (Crad * R) + 2 * G2 by ring]
      _ = ENNReal.ofReal (2 * (Crad * R) + 2 * (2 * ((n : ℝ) * (Cdz + Cbar + Cc)))) * M := by
          rw [hG2def]

end Work.NN.Core
