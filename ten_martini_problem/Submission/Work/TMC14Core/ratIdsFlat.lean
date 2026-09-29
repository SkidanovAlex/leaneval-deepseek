import Mathlib
import Submission.Work.TMC14Core.Assembly
import Submission.Work.TMComp.IDSPrufer.rotLift_approx
import Submission.Work.TMPuig.rotLift_continuousOn_of_reducible
import Submission.Work.TMComp.RotBasics.PSIter
import Submission.Work.TMComp.RotBasics.Defs
import Submission.Work.TMC14Core.eigvecDetOne
import Submission.Work.TMC14Core.posLiftTauInt
import Submission.Work.TMC14Core.iterRMapComplex

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC14Core

open scoped BigOperators




theorem pruferStep_bridge : @TMC14Core.pruferStep = @Work.TMContract.pruferStep := rfl

theorem tmC_bridge_local : @TMC14Core.tmC = @Work.TMContract.tmC := rfl

theorem pruferIter_bridge (α lam E : ℝ) : ∀ (n : ℕ) (x t : ℝ),
    TMC14Core.pruferIter α lam E n x t = Work.TMContract.pruferIter α lam E n x t := by
  intro n
  induction n with
  | zero => intro x t; rfl
  | succ n ih =>
    intro x t
    simp only [TMC14Core.pruferIter, Work.TMContract.pruferIter]
    rw [ih]
    exact congrFun (congrFun pruferStep_bridge _) _

theorem iterC_bridge_apply (α lam : ℝ) (z : ℂ) : ∀ (n : ℕ) (x : ℝ),
    TMC14Core.iterC α lam z n x = Work.TMContract.iterC α lam z n x := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
    intro x
    simp only [TMC14Core.iterC, Work.TMContract.iterC]
    rw [ih]
    have htm : TMC14Core.tmC lam z (x + (n:ℝ)*α) = Work.TMContract.tmC lam z (x + (n:ℝ)*α) :=
      congrFun (congrFun (congrFun tmC_bridge_local lam) z) (x + (n:ℝ)*α)
    rw [htm]

theorem rotLift_bridge (α lam E : ℝ) :
    TMC14Core.rotLift α lam E = Work.TMContract.rotLift α lam E := by
  unfold TMC14Core.rotLift Work.TMContract.rotLift
  congr 1
  funext n
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  exact pruferIter_bridge α lam E n x 0

theorem continuous_rotLift_local (α lam : ℝ) :
    Continuous (fun E : ℝ => TMC14Core.rotLift α lam E) := by
  have h : (fun E : ℝ => TMC14Core.rotLift α lam E)
      = fun E : ℝ => Work.TMContract.rotLift α lam E := by
    funext E; exact rotLift_bridge α lam E
  rw [h]
  exact Work.TMPuig.continuous_rotLift α lam

def gq (α lam E : ℝ) (q : ℕ) (θ : ℝ) : CircleDeg1Lift where
  toOrderHom := ⟨fun t => Work.TMContract.pruferIter α lam E q θ t,
    Work.TMComp.IDSPrufer.pruferIter_mono α lam E q θ⟩
  map_add_one' := fun t => Work.TMComp.IDSPrufer.pruferIter_add_one α lam E q θ t

@[simp] theorem gq_apply (α lam E : ℝ) (q : ℕ) (θ t : ℝ) :
    (gq α lam E q θ) t = Work.TMContract.pruferIter α lam E q θ t := rfl

theorem gq_pow_apply (p : ℤ) (q : ℕ) (hq : 1 ≤ q) (lam E θ t : ℝ) (n : ℕ) :
    ((gq ((p:ℝ)/(q:ℝ)) lam E q θ)^n) t
      = Work.TMContract.pruferIter ((p:ℝ)/(q:ℝ)) lam E (n * q) θ t := by
  rw [CircleDeg1Lift.coe_pow]
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply, Nat.zero_mul]
    rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, gq_apply]
    rw [show (n+1) * q = n * q + q by ring]
    rw [Work.TMComp.IDSPrufer.pruferIter_cocycle]
    have hq0 : (q:ℝ) ≠ 0 := by
      exact_mod_cast (by omega : q ≠ 0)
    have hX : ((n*q : ℕ) : ℝ) * ((p:ℝ)/(q:ℝ)) = (((n:ℤ) * p : ℤ) : ℝ) := by
      push_cast
      field_simp
    rw [hX, Work.TMComp.RotBasics.pruferIter_periodic_x_int]

theorem iterR_det (α lam E : ℝ) (n : ℕ) (x : ℝ) :
    (Work.TMComp.RotBasics.iterR α lam E n x).det = 1 := by
  induction n with
  | zero => exact Matrix.det_one
  | succ n ih =>
    simp only [Work.TMComp.RotBasics.iterR]
    rw [Matrix.det_mul, ih, mul_one]
    simp [Work.TMContract.tmR, Matrix.det_fin_two]

theorem trace_map_ofReal (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (A.map Complex.ofRealHom).trace = (A.trace : ℂ) := by
  simp only [Matrix.trace_fin_two, Matrix.map_apply]
  norm_num

theorem trAq_trace_cast (p : ℤ) (q : ℕ) (lam E θ : ℝ) :
    TMC14Core.trAq p q lam (E : ℂ) θ
      = ((Work.TMComp.RotBasics.iterR ((p:ℝ)/(q:ℝ)) lam E q θ).trace : ℂ) := by
  have h : TMC14Core.trAq p q lam (E:ℂ) θ
      = (Work.TMContract.iterC ((p:ℝ)/(q:ℝ)) lam (E:ℂ) q θ) 0 0
        + (Work.TMContract.iterC ((p:ℝ)/(q:ℝ)) lam (E:ℂ) q θ) 1 1 := by
    simp only [TMC14Core.trAq]
    rw [iterC_bridge_apply ((p:ℝ)/(q:ℝ)) lam (E:ℂ) q θ]
  rw [h, ← Matrix.trace_fin_two, ← iterRMapComplex, trace_map_ofReal]

theorem natCast_pos_of_le_one {n : ℕ} (h : 1 ≤ n) : (0:ℝ) < (n:ℝ) := by
  exact_mod_cast (by omega : 0 < n)

theorem natCast_ne_zero_of_le_one {n : ℕ} (h : 1 ≤ n) : (n:ℝ) ≠ 0 :=
  ne_of_gt (natCast_pos_of_le_one h)

theorem tau_gq_int (p : ℤ) (q : ℕ) (hq : 1 ≤ q) (lam E θ : ℝ)
    (htr : 2 < |(Work.TMComp.RotBasics.iterR ((p:ℝ)/(q:ℝ)) lam E q θ).trace|) :
    ∃ k : ℤ, (gq ((p:ℝ)/(q:ℝ)) lam E q θ).translationNumber = (k : ℝ) := by
  have hdet : (Work.TMComp.RotBasics.iterR ((p:ℝ)/(q:ℝ)) lam E q θ).det = 1 :=
    iterR_det _ _ _ _ _
  have hlam : ∃ (l : ℝ) (v : Fin 2 → ℝ), v ≠ 0 ∧
      (Work.TMComp.RotBasics.iterR ((p:ℝ)/(q:ℝ)) lam E q θ).mulVec v = l • v :=
    eigvecDetOne _ hdet htr
  refine posLiftTauInt ?_ (by rw [hdet]; norm_num) hlam
  exact Work.TMComp.RotBasics.pruferIter_isPosLift ((p:ℝ)/(q:ℝ)) lam E q θ

theorem tau_gq_const (p : ℤ) (q : ℕ) (hq : 1 ≤ q) (lam E : ℝ)
    (htr : ∀ θ : ℝ, 2 < |(Work.TMComp.RotBasics.iterR ((p:ℝ)/(q:ℝ)) lam E q θ).trace|) :
    ∀ θ θ' : ℝ, (gq ((p:ℝ)/(q:ℝ)) lam E q θ).translationNumber
      = (gq ((p:ℝ)/(q:ℝ)) lam E q θ').translationNumber := by
  have hloc : IsLocallyConstant
      (fun θ : ℝ => (gq ((p:ℝ)/(q:ℝ)) lam E q θ).translationNumber) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro θ0
    obtain ⟨k, hk⟩ := tau_gq_int p q hq lam E θ0 (htr θ0)
    have hcont : Continuous
        (fun θ : ℝ => Work.TMContract.pruferIter ((p:ℝ)/(q:ℝ)) lam E (5 * q) θ 0) :=
      (Work.TMComp.IDSPrufer.pruferIter_continuous ((p:ℝ)/(q:ℝ)) lam E (5 * q)).comp
        (continuous_id.prodMk continuous_const)
    have h0 : |Work.TMContract.pruferIter ((p:ℝ)/(q:ℝ)) lam E (5 * q) θ0 0 / 5 - (k:ℝ)| ≤ 1/5 := by
      have hdg := CircleDeg1Lift.dist_pow_map_zero_mul_translationNumber_le
        (gq ((p:ℝ)/(q:ℝ)) lam E q θ0) 5
      rw [gq_pow_apply p q hq] at hdg
      rw [Real.dist_eq, hk] at hdg
      have h5 : (0:ℝ) < 5 := by norm_num
      rw [div_sub' (by norm_num : (5:ℝ) ≠ 0), abs_div, abs_of_pos h5, div_le_iff₀ h5]
      have : (1:ℝ)/5 * 5 = 1 := by norm_num
      rw [this]
      exact hdg
    filter_upwards [hcont.continuousAt.eventually
      (Metric.ball_mem_nhds _ (by norm_num : (0:ℝ) < 1))] with θ hθ
    rw [Real.dist_eq] at hθ
    obtain ⟨k', hk'⟩ := tau_gq_int p q hq lam E θ (htr θ)
    have h1 : |Work.TMContract.pruferIter ((p:ℝ)/(q:ℝ)) lam E (5 * q) θ 0 / 5 - (k':ℝ)| ≤ 1/5 := by
      have hdg := CircleDeg1Lift.dist_pow_map_zero_mul_translationNumber_le
        (gq ((p:ℝ)/(q:ℝ)) lam E q θ) 5
      rw [gq_pow_apply p q hq] at hdg
      rw [Real.dist_eq, hk'] at hdg
      have h5 : (0:ℝ) < 5 := by norm_num
      rw [div_sub' (by norm_num : (5:ℝ) ≠ 0), abs_div, abs_of_pos h5, div_le_iff₀ h5]
      have : (1:ℝ)/5 * 5 = 1 := by norm_num
      rw [this]
      exact hdg
    have h2 : |Work.TMContract.pruferIter ((p:ℝ)/(q:ℝ)) lam E (5 * q) θ 0 / 5 - (k:ℝ)| ≤ 2/5 := by
      have h3 : |Work.TMContract.pruferIter ((p:ℝ)/(q:ℝ)) lam E (5*q) θ 0 / 5
          - Work.TMContract.pruferIter ((p:ℝ)/(q:ℝ)) lam E (5*q) θ0 0 / 5| ≤ 1/5 := by
        rw [div_sub_div_same, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 5)]
        rw [div_le_iff₀ (by norm_num : (0:ℝ) < 5)]
        have : (1:ℝ)/5 * 5 = 1 := by norm_num
        rw [this]
        exact le_of_lt hθ
      calc |Work.TMContract.pruferIter ((p:ℝ)/(q:ℝ)) lam E (5*q) θ 0 / 5 - (k:ℝ)|
          ≤ |Work.TMContract.pruferIter ((p:ℝ)/(q:ℝ)) lam E (5*q) θ 0 / 5
              - Work.TMContract.pruferIter ((p:ℝ)/(q:ℝ)) lam E (5*q) θ0 0 / 5|
            + |Work.TMContract.pruferIter ((p:ℝ)/(q:ℝ)) lam E (5*q) θ0 0 / 5 - (k:ℝ)| :=
            abs_sub_le _ _ _
        _ ≤ 1/5 + 1/5 := add_le_add h3 h0
        _ = 2/5 := by norm_num
    have hkint : |(k':ℝ) - (k:ℝ)| ≤ 3/5 := by
      have h1' : |(k':ℝ) - Work.TMContract.pruferIter ((p:ℝ)/(q:ℝ)) lam E (5*q) θ 0 / 5| ≤ 1/5 := by
        rw [abs_sub_comm]; exact h1
      calc |(k':ℝ) - (k:ℝ)|
          = |((k':ℝ) - Work.TMContract.pruferIter ((p:ℝ)/(q:ℝ)) lam E (5*q) θ 0 / 5)
              + (Work.TMContract.pruferIter ((p:ℝ)/(q:ℝ)) lam E (5*q) θ 0 / 5 - (k:ℝ))| := by
            ring_nf
        _ ≤ |(k':ℝ) - Work.TMContract.pruferIter ((p:ℝ)/(q:ℝ)) lam E (5*q) θ 0 / 5|
            + |Work.TMContract.pruferIter ((p:ℝ)/(q:ℝ)) lam E (5*q) θ 0 / 5 - (k:ℝ)| :=
            abs_add_le _ _
        _ ≤ 1/5 + 2/5 := add_le_add h1' h2
        _ = 3/5 := by norm_num
    have hkk : k' = k := by
      have hcast2 : ((k' - k : ℤ) : ℝ) = (k':ℝ) - (k:ℝ) := by push_cast; ring
      have hlt : |((k' - k : ℤ) : ℝ)| < 1 := by rw [hcast2]; linarith
      have hz0 : (k' - k : ℤ) = 0 := by
        rw [abs_lt] at hlt
        have h1 : (-1:ℤ) < k' - k := by exact_mod_cast hlt.1
        have h2 : k' - k < 1 := by exact_mod_cast hlt.2
        omega
      omega
    rw [hk', hk, hkk]
  exact fun θ θ' => hloc.apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ θ) (Set.mem_univ θ')

theorem rotLift_eq_int_div (p : ℤ) (q : ℕ) (hq : 1 ≤ q) (lam E : ℝ)
    (htr : ∀ θ : ℝ, 2 < |(Work.TMComp.RotBasics.iterR ((p:ℝ)/(q:ℝ)) lam E q θ).trace|) :
    ∃ k : ℤ, TMC14Core.rotLift ((p:ℝ)/(q:ℝ)) lam E = (k : ℝ) / (q : ℝ) := by
  have hqpos : (0:ℝ) < (q:ℝ) := natCast_pos_of_le_one hq
  obtain ⟨k, hk⟩ := tau_gq_int p q hq lam E 0 (htr 0)
  have hconst := tau_gq_const p q hq lam E htr
  have hkall : ∀ θ : ℝ, (gq ((p:ℝ)/(q:ℝ)) lam E q θ).translationNumber = (k:ℝ) := by
    intro θ; rw [hconst θ 0, hk]
  refine ⟨k, ?_⟩
  rw [rotLift_bridge]
  have hbound : ∀ n : ℕ, 1 ≤ n →
      |Work.TMContract.rotLift ((p:ℝ)/(q:ℝ)) lam E - (k:ℝ)/(q:ℝ)| ≤ 2/((n:ℝ)*(q:ℝ)) := by
    intro n hn
    have hnq1 : 1 ≤ n * q := by
      simpa using (Nat.mul_le_mul hn hq : 1 * 1 ≤ n * q)
    have hra := Work.TMComp.IDSPrufer.rotLift_approx ((p:ℝ)/(q:ℝ)) lam E (n := n * q) hnq1
    have hpt : ∀ x : ℝ, |Work.TMContract.pruferIter ((p:ℝ)/(q:ℝ)) lam E (n*q) x 0
        - (n:ℝ)*(k:ℝ)| ≤ 1 := by
      intro x
      have hdg := CircleDeg1Lift.dist_pow_map_zero_mul_translationNumber_le
        (gq ((p:ℝ)/(q:ℝ)) lam E q x) n
      rw [gq_pow_apply p q hq] at hdg
      rw [Real.dist_eq, hkall x] at hdg
      exact hdg
    have hfcont : Continuous
        (fun x : ℝ => Work.TMContract.pruferIter ((p:ℝ)/(q:ℝ)) lam E (n*q) x 0) :=
      (Work.TMComp.IDSPrufer.pruferIter_continuous ((p:ℝ)/(q:ℝ)) lam E (n*q)).comp
        (continuous_id.prodMk continuous_const)
    have hIf : IntervalIntegrable
        (fun x : ℝ => Work.TMContract.pruferIter ((p:ℝ)/(q:ℝ)) lam E (n*q) x 0) volume 0 1 :=
      hfcont.intervalIntegrable 0 1
    have hInt : |(∫ x in (0:ℝ)..1, Work.TMContract.pruferIter ((p:ℝ)/(q:ℝ)) lam E (n*q) x 0)
        - (n:ℝ)*(k:ℝ)| ≤ 1 := by
      have h1 : (∫ x in (0:ℝ)..1, Work.TMContract.pruferIter ((p:ℝ)/(q:ℝ)) lam E (n*q) x 0)
          - (n:ℝ)*(k:ℝ)
          = ∫ x in (0:ℝ)..1, (Work.TMContract.pruferIter ((p:ℝ)/(q:ℝ)) lam E (n*q) x 0
              - (n:ℝ)*(k:ℝ)) := by
        rw [intervalIntegral.integral_sub hIf intervalIntegrable_const,
          intervalIntegral.integral_const]
        simp
      rw [h1]
      have hf : IntervalIntegrable
          (fun x : ℝ => |Work.TMContract.pruferIter ((p:ℝ)/(q:ℝ)) lam E (n*q) x 0
            - (n:ℝ)*(k:ℝ)|) volume 0 1 :=
        (hIf.sub intervalIntegrable_const).abs
      calc |∫ x in (0:ℝ)..1, (Work.TMContract.pruferIter ((p:ℝ)/(q:ℝ)) lam E (n*q) x 0
              - (n:ℝ)*(k:ℝ))|
          ≤ ∫ x in (0:ℝ)..1, |Work.TMContract.pruferIter ((p:ℝ)/(q:ℝ)) lam E (n*q) x 0
              - (n:ℝ)*(k:ℝ)| :=
            intervalIntegral.abs_integral_le_integral_abs (by norm_num)
        _ ≤ ∫ _x in (0:ℝ)..1, (1:ℝ) :=
            intervalIntegral.integral_mono_on (by norm_num) hf intervalIntegrable_const
              (fun x _ => hpt x)
        _ = 1 := by simp
    have hNpos : (0:ℝ) < (n:ℝ)*(q:ℝ) :=
      mul_pos (natCast_pos_of_le_one hn) hqpos
    have hcast : ((n*q : ℕ) : ℝ) = (n:ℝ)*(q:ℝ) := by push_cast; ring
    have hkey : ((n:ℝ)*(q:ℝ)) * ((k:ℝ)/(q:ℝ)) = (n:ℝ)*(k:ℝ) := by
      field_simp
    have hstep : |(∫ x in (0:ℝ)..1, Work.TMContract.pruferIter ((p:ℝ)/(q:ℝ)) lam E (n*q) x 0)
        / ((n:ℝ)*(q:ℝ)) - (k:ℝ)/(q:ℝ)| ≤ 1/((n:ℝ)*(q:ℝ)) := by
      have hsplit : (∫ x in (0:ℝ)..1, Work.TMContract.pruferIter ((p:ℝ)/(q:ℝ)) lam E (n*q) x 0)
          / ((n:ℝ)*(q:ℝ)) - (k:ℝ)/(q:ℝ)
          = ((∫ x in (0:ℝ)..1, Work.TMContract.pruferIter ((p:ℝ)/(q:ℝ)) lam E (n*q) x 0)
              - (n:ℝ)*(k:ℝ)) / ((n:ℝ)*(q:ℝ)) := by
        rw [div_sub' (ne_of_gt hNpos), hkey]
      rw [hsplit, abs_div, abs_of_pos hNpos, div_le_iff₀ hNpos]
      have hh : (1:ℝ)/((n:ℝ)*(q:ℝ)) * ((n:ℝ)*(q:ℝ)) = 1 := by
        rw [one_div, inv_mul_cancel₀ (ne_of_gt hNpos)]
      rw [hh]
      exact hInt
    rw [hcast] at hra
    calc |Work.TMContract.rotLift ((p:ℝ)/(q:ℝ)) lam E - (k:ℝ)/(q:ℝ)|
        ≤ |Work.TMContract.rotLift ((p:ℝ)/(q:ℝ)) lam E
            - (∫ x in (0:ℝ)..1, Work.TMContract.pruferIter ((p:ℝ)/(q:ℝ)) lam E (n*q) x 0)
            / ((n:ℝ)*(q:ℝ))|
          + |(∫ x in (0:ℝ)..1, Work.TMContract.pruferIter ((p:ℝ)/(q:ℝ)) lam E (n*q) x 0)
            / ((n:ℝ)*(q:ℝ)) - (k:ℝ)/(q:ℝ)| := abs_sub_le _ _ _
      _ ≤ 1/((n:ℝ)*(q:ℝ)) + 1/((n:ℝ)*(q:ℝ)) := add_le_add hra hstep
      _ = 2/((n:ℝ)*(q:ℝ)) := by ring
  have hzero : |Work.TMContract.rotLift ((p:ℝ)/(q:ℝ)) lam E - (k:ℝ)/(q:ℝ)| ≤ 0 := by
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    obtain ⟨n, hn⟩ := exists_nat_gt (2/(ε*(q:ℝ)) + 1)
    have hn1 : 1 ≤ n := by
      have hpos : (0:ℝ) < 2/(ε*(q:ℝ)) := by
        exact div_pos (by norm_num) (mul_pos hε hqpos)
      have hlt1 : (1:ℝ) < (n:ℝ) := by linarith
      exact_mod_cast le_of_lt hlt1
    have hb := hbound n hn1
    have hNpos : (0:ℝ) < (n:ℝ)*(q:ℝ) :=
      mul_pos (natCast_pos_of_le_one hn1) hqpos
    have hlt : 2/((n:ℝ)*(q:ℝ)) ≤ ε := by
      rw [div_le_iff₀ hNpos]
      have hn2 : 2/(ε*(q:ℝ)) < (n:ℝ) := by linarith [hn]
      rw [div_lt_iff₀ (mul_pos hε hqpos)] at hn2
      nlinarith [hn2, hε, hqpos]
    linarith [hb, hlt]
  have hfin : Work.TMContract.rotLift ((p:ℝ)/(q:ℝ)) lam E - (k:ℝ)/(q:ℝ) = 0 :=
    abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _))
  linarith [hfin]

theorem eq_on_Ioo_of_continuous_int_le {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ}
    (hint : ∀ E ∈ Ioo a b, ∃ z : ℤ, f E = (z : ℝ)) :
    ∀ E ∈ Ioo a b, ∀ E' ∈ Ioo a b, E ≤ E' → f E = f E' := by
  intro E hE E' hE' hle
  obtain ⟨k, hk⟩ := hint E hE
  obtain ⟨k', hk'⟩ := hint E' hE'
  by_cases hle2 : (k:ℝ) ≤ (k':ℝ)
  · by_cases heq : (k:ℝ) = (k':ℝ)
    · rw [hk, hk', heq]
    · have hkl : k < k' := by
        have : (k:ℝ) < (k':ℝ) := lt_of_le_of_ne hle2 heq
        exact_mod_cast this
      have hk1 : (k:ℝ) + 1 ≤ (k':ℝ) := by
        have : k + 1 ≤ k' := by omega
        exact_mod_cast this
      have hy1 : f E ≤ (k:ℝ) + 1/2 := by rw [hk]; linarith
      have hy2 : (k:ℝ) + 1/2 ≤ f E' := by rw [hk']; linarith
      obtain ⟨c, hc, hfc⟩ :=
        intermediate_value_Icc hle hf.continuousOn (show (k:ℝ) + 1/2 ∈ Icc (f E) (f E') from ⟨hy1, hy2⟩)
      have hcab : c ∈ Ioo a b :=
        ⟨lt_of_lt_of_le hE.1 hc.1, lt_of_le_of_lt hc.2 hE'.2⟩
      obtain ⟨z, hz⟩ := hint c hcab
      have hz2 : (z:ℝ) = (k:ℝ) + 1/2 := by rw [← hz, hfc]
      exfalso
      have hz3 : (2*z - 2*k : ℤ) = 1 := by
        have h3 : ((2*z - 2*k : ℤ) : ℝ) = 1 := by push_cast; linarith
        exact_mod_cast h3
      omega
  · push_neg at hle2
    have hkl : k' < k := by exact_mod_cast hle2
    have hk1 : (k':ℝ) + 1 ≤ (k:ℝ) := by
      have : k' + 1 ≤ k := by omega
      exact_mod_cast this
    have hy1 : f E' ≤ (k':ℝ) + 1/2 := by rw [hk']; linarith
    have hy2 : (k':ℝ) + 1/2 ≤ f E := by rw [hk]; linarith
    obtain ⟨c, hc, hfc⟩ :=
      intermediate_value_Icc' hle hf.continuousOn (show (k':ℝ) + 1/2 ∈ Icc (f E') (f E) from ⟨hy1, hy2⟩)
    have hcab : c ∈ Ioo a b :=
      ⟨lt_of_lt_of_le hE.1 hc.1, lt_of_le_of_lt hc.2 hE'.2⟩
    obtain ⟨z, hz⟩ := hint c hcab
    have hz2 : (z:ℝ) = (k':ℝ) + 1/2 := by rw [← hz, hfc]
    exfalso
    have hz3 : (2*z - 2*k' : ℤ) = 1 := by
      have h3 : ((2*z - 2*k' : ℤ) : ℝ) = 1 := by push_cast; linarith
      exact_mod_cast h3
    omega

theorem eq_on_Ioo_of_continuous_int {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ}
    (hint : ∀ E ∈ Ioo a b, ∃ z : ℤ, f E = (z : ℝ)) :
    ∀ E ∈ Ioo a b, ∀ E' ∈ Ioo a b, f E = f E' := by
  intro E hE E' hE'
  rcases le_total E E' with hle | hle
  · exact eq_on_Ioo_of_continuous_int_le hf hint E hE E' hE' hle
  · exact (eq_on_Ioo_of_continuous_int_le hf hint E' hE' E hE hle).symm

theorem rotLift_const_on_gap (p : ℤ) (q : ℕ) (hq : 1 ≤ q) (lam : ℝ) {a b : ℝ} (hab : a < b)
    (htr : ∀ E ∈ Ioo a b, ∀ θ, 2 < |(Work.TMComp.RotBasics.iterR ((p:ℝ)/(q:ℝ)) lam E q θ).trace|) :
    TMC14Core.rotLift ((p:ℝ)/(q:ℝ)) lam a = TMC14Core.rotLift ((p:ℝ)/(q:ℝ)) lam b := by
  have hq0 : (q:ℝ) ≠ 0 := natCast_ne_zero_of_le_one hq
  have hcont : Continuous
      (fun E : ℝ => (q:ℝ) * TMC14Core.rotLift ((p:ℝ)/(q:ℝ)) lam E) := by
    rw [show (fun E : ℝ => (q:ℝ) * TMC14Core.rotLift ((p:ℝ)/(q:ℝ)) lam E)
        = fun E : ℝ => (q:ℝ) * Work.TMContract.rotLift ((p:ℝ)/(q:ℝ)) lam E from by
      funext E; rw [rotLift_bridge]]
    exact continuous_const.mul (Work.TMPuig.continuous_rotLift _ lam)
  have hint : ∀ E ∈ Ioo a b, ∃ z : ℤ,
      (q:ℝ) * TMC14Core.rotLift ((p:ℝ)/(q:ℝ)) lam E = (z:ℝ) := by
    intro E hE
    obtain ⟨k, hk⟩ := rotLift_eq_int_div p q hq lam E (fun θ => htr E hE θ)
    exact ⟨k, by rw [hk]; field_simp⟩
  have hmid : (a+b)/2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hv : ∀ E ∈ Ioo a b, (q:ℝ) * TMC14Core.rotLift ((p:ℝ)/(q:ℝ)) lam E
      = (q:ℝ) * TMC14Core.rotLift ((p:ℝ)/(q:ℝ)) lam ((a+b)/2) :=
    fun E hE => eq_on_Ioo_of_continuous_int hcont hint E hE _ hmid
  have hcl : ∀ E ∈ Icc a b, (q:ℝ) * TMC14Core.rotLift ((p:ℝ)/(q:ℝ)) lam E
      = (q:ℝ) * TMC14Core.rotLift ((p:ℝ)/(q:ℝ)) lam ((a+b)/2) := by
    have hclosed : IsClosed {E : ℝ | (q:ℝ) * TMC14Core.rotLift ((p:ℝ)/(q:ℝ)) lam E
        = (q:ℝ) * TMC14Core.rotLift ((p:ℝ)/(q:ℝ)) lam ((a+b)/2)} :=
      isClosed_eq hcont continuous_const
    intro E hE
    have hsub : Ioo a b ⊆ {E : ℝ | (q:ℝ) * TMC14Core.rotLift ((p:ℝ)/(q:ℝ)) lam E
        = (q:ℝ) * TMC14Core.rotLift ((p:ℝ)/(q:ℝ)) lam ((a+b)/2)} := hv
    have hcl2 := closure_minimal hsub hclosed
    rw [closure_Ioo (ne_of_lt hab)] at hcl2
    exact hcl2 hE
  have ha := hcl a ⟨le_rfl, le_of_lt hab⟩
  have hb := hcl b ⟨le_of_lt hab, le_rfl⟩
  have hmul : (q:ℝ) * TMC14Core.rotLift ((p:ℝ)/(q:ℝ)) lam a
      = (q:ℝ) * TMC14Core.rotLift ((p:ℝ)/(q:ℝ)) lam b := ha.trans hb.symm
  exact mul_left_cancel₀ hq0 hmul

theorem ratIdsFlat : Work.TMC14Core.RatIdsFlat := by
  intro p q lam hlam a b hab hhyp
  by_cases hq0 : q = 0
  · subst hq0
    exfalso
    have hE : (a+b)/2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
    have h := hhyp ((a+b)/2) hE 0
    have h2 : TMC14Core.trAq p 0 lam (((a+b)/2 : ℝ) : ℂ) 0 = 2 := by
      simp only [TMC14Core.trAq, TMC14Core.iterC]
      norm_num
    rw [h2] at h
    norm_num at h
  · have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq0
    have htr : ∀ E ∈ Ioo a b, ∀ θ,
        2 < |(Work.TMComp.RotBasics.iterR ((p:ℝ)/(q:ℝ)) lam E q θ).trace| := by
      intro E hE θ
      have h := hhyp E hE θ
      rw [trAq_trace_cast p q lam E θ, Complex.norm_real, Real.norm_eq_abs] at h
      exact h
    have hkey := rotLift_const_on_gap p q hq1 lam hab htr
    simp only [TMC14Core.ids]
    rw [hkey]

end Work.TMC14Core
