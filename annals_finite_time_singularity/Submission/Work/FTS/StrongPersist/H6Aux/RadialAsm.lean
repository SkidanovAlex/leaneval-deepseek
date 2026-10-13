/-
# `Work.FTS.StrongPersist.H6Aux.RadialAsm` — the assembly of the radial slot bound

Insurance module for the radial half of `Corr_HkSq6`.  It proves

* `Alt_ampA_dzdIter_bound6` — the uniform jet bound `|D_z^j (ampA α)| ≤ K` for `j ≤ 6`,
  `α ∈ (0,1]` (`E2pkg.ampA_dzdIter_bound` at order `6`, via `E2Bound.zop_phi_bound 6`);
* `Alt_SlotSum_radA_ptwise` — the pointwise decomposition
  `SlotSum (radA α f) z ≤ 2·(ampA-slot sum) z + 2C₀f²·(ampB/c-slot sum) z`
  (Leibniz/`DzdIter_add_of_diff` for the two summands of `radA`);
* `Alt_SlotSum_radA_le` — the end-to-end radial bound
  `∫_z SlotSum (radA α f) ≤ C·HkSq α 6 f`, from `L6Aux.L12SlotSum6` (the `L₁₂f` slots),
  `L3Aux.Transport_L12_zero_le`/`Alt_C0_sq_le_HkSq6` (the projector constant) and the
  z-multiplier slot lemma `ZopSlotMul_le`, passed here as the hypothesis `hZop`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongPersist.H6Aux.RadialAux
import Submission.Work.FTS.StrongPersist.H6Aux.CorrAux
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAId
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAZop
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_coeff_bound
import Submission.Work.FTS.CoercivityFix.E2Bound.zop_phi_bound
import Submission.Work.FTS.StrongPersist.L6Aux.L12SlotSum6
import Submission.Work.FTS.StrongPersist.H6Aux.ZopSlotMul_le
import Submission.Work.Elliptic.L12Aux
import Submission.Work.Spaces.c_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Aux

open Work.Spaces (HkMem HkSq HkNorm)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## §1 The jet bound for `ampA` at order six -/

theorem Alt_ampA_dzdIter_bound6 : ∃ K : ℝ, 0 ≤ K ∧ ∀ α ∈ Set.Ioc 0 1, ∀ j ≤ 6,
    ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampA α) z| ≤ K := by
  obtain ⟨K₀, hK₀, hK₀b⟩ := Work.FTS.CoercivityFix.E2Bound.zop_phi_bound 6
  refine ⟨20 * K₀, by positivity, ?_⟩
  intro α hαIoc j hj z hz
  have hcpos : 0 < Work.Spaces.c α := Work.FTS.StrongPersist.L3Aux.c_pos hαIoc.1 hαIoc.2
  have h2c : 2 / Work.Spaces.c α ≤ 20 := by
    rw [div_le_iff₀ hcpos]
    have h := (Work.Spaces.c_bounds α hαIoc.1 hαIoc.2).1
    linarith
  have hphi : |Work.Spaces.Zop^[j] (fun z : ℝ => z / (1 + z) ^ 2) z| ≤ K₀ :=
    hK₀b j hj z hz
  calc |Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampA α) z|
      = |Work.Spaces.Zop^[j] (Work.FTS.CoercivityFix.Transfer.ampA α) z| := by
        rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter]
    _ = |Work.Spaces.Zop^[j] (fun z => (2 / Work.Spaces.c α) * (z / (1 + z) ^ 2)) z| := by
        rw [Work.FTS.CoercivityFix.Transfer.E2pkg.ampA_eq_const_mul_fA]
    _ = |(2 / Work.Spaces.c α)
          * Work.Spaces.Zop^[j] (fun z : ℝ => z / (1 + z) ^ 2) z| := by
        rw [Work.FTS.CoercivityFix.Transfer.E2pkg.Zop_iter_const_mul]
    _ = (2 / Work.Spaces.c α)
          * |Work.Spaces.Zop^[j] (fun z : ℝ => z / (1 + z) ^ 2) z| := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ (2 / Work.Spaces.c α) * K₀ := mul_le_mul_of_nonneg_left hphi (by positivity)
    _ ≤ 20 * K₀ := mul_le_mul_of_nonneg_right h2c hK₀

/-! ## §2 The pointwise decomposition of the radial slot sum -/

theorem Alt_SlotSum_radA_ptwise {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem7 : Work.Spaces.HkMem α 7 f)
    {z : ℝ} (hz : z ∈ Set.Ioi (0 : ℝ)) :
    Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f) z
      ≤ 2 * (∑ q ∈ Finset.range 7, (Work.Elliptic.DzdIter q
            (fun z' => Work.FTS.CoercivityFix.Transfer.ampA α z'
              * Work.Coercivity.L12f f z') z) ^ 2 * (Work.Spaces.w z) ^ 2)
        + (2 * (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2)
          * (∑ q ∈ Finset.range 7, (Work.Elliptic.DzdIter q
              (fun z' => Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α) z) ^ 2
                * (Work.Spaces.w z) ^ 2) := by
  have hu6 : ContDiffOn ℝ 6 (fun z' => Work.Coercivity.L12f f z') (Set.Ioi (0 : ℝ)) := by
    have h := Work.FTS.StrongPersist.contDiffOn6_L12_of (α := α) (f := f) hsm hmem7
    have hfun : (fun z' => Work.Coercivity.L12f f z') = fun z' => Work.Construction.L12 f z' :=
      rfl
    rw [hfun]
    exact h
  have hA6 : ContDiffOn ℝ 6 (fun z' => Work.FTS.CoercivityFix.Transfer.ampA α z'
      * Work.Coercivity.L12f f z') (Set.Ioi (0 : ℝ)) :=
    (contDiffOn_six_ampA hα hα1).mul hu6
  have hnegA6 : ContDiffOn ℝ 6 (fun z' => -(Work.FTS.CoercivityFix.Transfer.ampA α z'
      * Work.Coercivity.L12f f z')) (Set.Ioi (0 : ℝ)) := hA6.neg
  have hB6 : ContDiffOn ℝ 6 (fun z' => Work.FTS.CoercivityFix.Transfer.ampB α z'
      / Work.Spaces.c α) (Set.Ioi (0 : ℝ)) := contDiffOn_six_ampB_div α
  have hBC6 : ContDiffOn ℝ 6 (fun z' => (Work.FTS.CoercivityFix.Transfer.ampB α z'
      / Work.Spaces.c α) * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)
      (Set.Ioi (0 : ℝ)) := by
    have hconst : ContDiffOn ℝ 6 (fun _ : ℝ =>
        Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) (Set.Ioi (0 : ℝ)) :=
      contDiffOn_const
    have h1 : ContDiffOn ℝ 6 (fun z' => Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
        * (Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α))
        (Set.Ioi (0 : ℝ)) := hconst.mul hB6
    refine h1.congr (fun z' _ => ?_)
    ring
  have hSlotEq : Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f) z
      = ∑ q ∈ Finset.range 7,
          (Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2 := by
    rw [Work.FTS.StrongPersist.SlotSum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Work.Elliptic.DzIter_rad]
  rw [hSlotEq]
  have hterm : ∀ q ∈ Finset.range 7,
      (Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
          * (Work.Spaces.w z) ^ 2
        ≤ 2 * ((Work.Elliptic.DzdIter q (fun z' => Work.FTS.CoercivityFix.Transfer.ampA α z'
                * Work.Coercivity.L12f f z') z) ^ 2 * (Work.Spaces.w z) ^ 2)
          + (2 * (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2)
            * ((Work.Elliptic.DzdIter q (fun z' =>
                  Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α) z) ^ 2
                * (Work.Spaces.w z) ^ 2) := by
    intro q hq
    have hq6 : q ≤ 6 := Nat.le_of_lt_succ (Finset.mem_range.mp hq)
    -- the two summands of `radA` and their `D_z`-additivity
    have hcongr : Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α f) z
        = Work.Elliptic.DzdIter q (fun z' => -(Work.FTS.CoercivityFix.Transfer.ampA α z'
            * Work.Coercivity.L12f f z')
          + ((Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α)
            * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)) z := by
      refine Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_congr_of_eqOn _ _
        (fun z' _ => ?_) q z hz
      rw [Work.FTS.CoercivityFix.Transfer.radA_eq]
      simp only [Work.FTS.CoercivityFix.Transfer.ampA, Work.FTS.CoercivityFix.Transfer.ampB]
      ring
    have hdiff1 : ∀ b < q, ∀ z' ∈ Set.Ioi (0 : ℝ),
        DifferentiableAt ℝ (Work.Elliptic.DzdIter b
          (fun z' => -(Work.FTS.CoercivityFix.Transfer.ampA α z'
            * Work.Coercivity.L12f f z'))) z' := by
      intro b hb z' hz'
      have hb6 : b + 1 ≤ 6 := by omega
      have hcont : ContDiffOn ℝ (b + 1)
          (fun z' => -(Work.FTS.CoercivityFix.Transfer.ampA α z'
            * Work.Coercivity.L12f f z')) (Set.Ioi (0 : ℝ)) :=
        hnegA6.of_le (by exact_mod_cast hb6)
      rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter]
      exact Work.FTS.CoercivityFix.Transfer.E1Parts.differentiableAt_Zop_iter_of_contDiffOn
        hcont hz'
    have hdiff2 : ∀ b < q, ∀ z' ∈ Set.Ioi (0 : ℝ),
        DifferentiableAt ℝ (Work.Elliptic.DzdIter b
          (fun z' => (Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α)
            * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)) z' := by
      intro b hb z' hz'
      have hb6 : b + 1 ≤ 6 := by omega
      have hcont : ContDiffOn ℝ (b + 1)
          (fun z' => (Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α)
            * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) (Set.Ioi (0 : ℝ)) :=
        hBC6.of_le (by exact_mod_cast hb6)
      rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter]
      exact Work.FTS.CoercivityFix.Transfer.E1Parts.differentiableAt_Zop_iter_of_contDiffOn
        hcont hz'
    have hadd : Work.Elliptic.DzdIter q (fun z' => -(Work.FTS.CoercivityFix.Transfer.ampA α z'
            * Work.Coercivity.L12f f z')
          + ((Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α)
            * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)) z
        = Work.Elliptic.DzdIter q (fun z' => -(Work.FTS.CoercivityFix.Transfer.ampA α z'
            * Work.Coercivity.L12f f z')) z
          + Work.Elliptic.DzdIter q (fun z' =>
              (Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α)
                * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) z :=
      Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_add_of_diff q _ _ hdiff1 hdiff2 z hz
    have hneg : Work.Elliptic.DzdIter q (fun z' => -(Work.FTS.CoercivityFix.Transfer.ampA α z'
          * Work.Coercivity.L12f f z')) z
        = - Work.Elliptic.DzdIter q (fun z' => Work.FTS.CoercivityFix.Transfer.ampA α z'
            * Work.Coercivity.L12f f z') z := by
      have h1 : (fun z' => -(Work.FTS.CoercivityFix.Transfer.ampA α z'
            * Work.Coercivity.L12f f z'))
          = fun z' => (-1) * (Work.FTS.CoercivityFix.Transfer.ampA α z'
              * Work.Coercivity.L12f f z') := by
        funext z'; ring
      rw [h1, Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter,
        Work.FTS.CoercivityFix.Transfer.E2pkg.Zop_iter_const_mul,
        ← Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter]
      ring
    have hbc : Work.Elliptic.DzdIter q (fun z' =>
          (Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α)
            * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) z
        = Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
          * Work.Elliptic.DzdIter q (fun z' =>
              Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α) z := by
      have h1 : (fun z' => (Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α)
            * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)
          = fun z' => Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
              * (Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α) := by
        funext z'; ring
      rw [h1, Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter,
        Work.FTS.CoercivityFix.Transfer.E2pkg.Zop_iter_const_mul,
        ← Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter]
    have hsq : (Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
        ≤ 2 * (Work.Elliptic.DzdIter q (fun z' => Work.FTS.CoercivityFix.Transfer.ampA α z'
              * Work.Coercivity.L12f f z') z) ^ 2
          + 2 * (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
              * Work.Elliptic.DzdIter q (fun z' =>
                  Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α) z) ^ 2 := by
      rw [hcongr, hadd, hneg, hbc]
      nlinarith [sq_nonneg (Work.Elliptic.DzdIter q (fun z' =>
            Work.FTS.CoercivityFix.Transfer.ampA α z' * Work.Coercivity.L12f f z') z
          + Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
            * Work.Elliptic.DzdIter q (fun z' =>
                Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α) z)]
    calc (Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
          * (Work.Spaces.w z) ^ 2
        ≤ (2 * (Work.Elliptic.DzdIter q (fun z' => Work.FTS.CoercivityFix.Transfer.ampA α z'
                * Work.Coercivity.L12f f z') z) ^ 2
            + 2 * (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
                * Work.Elliptic.DzdIter q (fun z' =>
                    Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α) z) ^ 2)
              * (Work.Spaces.w z) ^ 2 :=
          mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
      _ = 2 * ((Work.Elliptic.DzdIter q (fun z' => Work.FTS.CoercivityFix.Transfer.ampA α z'
                * Work.Coercivity.L12f f z') z) ^ 2 * (Work.Spaces.w z) ^ 2)
            + (2 * (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2)
              * ((Work.Elliptic.DzdIter q (fun z' =>
                    Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α) z) ^ 2
                  * (Work.Spaces.w z) ^ 2) := by ring
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-! ## §3 Helpers for the end-to-end radial bound -/

theorem Alt_SlotSum_eq (B : ℝ → ℝ) (z : ℝ) :
    Work.FTS.StrongPersist.SlotSum B z
      = ∑ q ∈ Finset.range 7,
          (Work.Elliptic.DzdIter q B z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
  rw [Work.FTS.StrongPersist.SlotSum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Work.Elliptic.DzIter_rad]

theorem Alt_continuousOn_w : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi (0 : ℝ)) := by
  have hEq : (fun z : ℝ => Work.Spaces.w z) = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 := rfl
  rw [hEq]
  exact ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
    (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))

theorem Alt_continuousOn_slotSum {A : ℝ → ℝ} {n : ℕ}
    (h : ContDiffOn ℝ n A (Set.Ioi (0 : ℝ))) :
    ContinuousOn (fun z => ∑ q ∈ Finset.range (n + 1),
        (Work.Elliptic.DzdIter q A z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioi (0 : ℝ)) := by
  have hfun : (fun z => ∑ q ∈ Finset.range (n + 1),
        (Work.Elliptic.DzdIter q A z) ^ 2 * (Work.Spaces.w z) ^ 2)
      = fun z => ∑ q ∈ Finset.range (n + 1),
          ((Work.Spaces.Zop^[q] A) z * Work.Spaces.w z) ^ 2 := by
    funext z
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter]
    ring
  rw [hfun]
  refine continuousOn_finsetSum _ (fun q hq => ?_)
  have hq' : q ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hq)
  refine ContinuousOn.pow ?_ 2
  refine ContinuousOn.mul ?_ Alt_continuousOn_w
  have hiter : ContinuousOn (Work.Spaces.Zop^[q] A) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.CoercivityFix.Transfer.E1Parts.continuousOn_Zop_iter_of_contDiffOn
      (b := q) (n := n - q)
      (h.of_le (by exact_mod_cast (le_of_eq (Nat.add_sub_cancel' hq') : q + (n - q) ≤ n)))
  exact hiter

/-! ## §4 The end-to-end radial bound -/

theorem Alt_SlotSum_radA_le
    (hZop : ∃ C : ℝ, 0 < C ∧ ∀ (φ u : ℝ → ℝ) (K : ℝ), 0 ≤ K →
      (∀ j ≤ 6, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Elliptic.DzdIter j φ z| ≤ K) →
      ContDiffOn ℝ 6 φ (Set.Ioi (0 : ℝ)) → ContDiffOn ℝ 6 u (Set.Ioi (0 : ℝ)) →
      ∀ z ∈ Set.Ioi (0 : ℝ),
        (∑ q ∈ Finset.range 7,
            (Work.Elliptic.DzdIter q (fun z' => φ z' * u z') z) ^ 2 * (Work.Spaces.w z) ^ 2)
          ≤ C * (1 + K) ^ 2
            * (∑ q ∈ Finset.range 7,
                (Work.Elliptic.DzdIter q u z) ^ 2 * (Work.Spaces.w z) ^ 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ f : ℝ → ℝ → ℝ,
      Work.FTS.StrongPersist.H6Adm α f → Work.Spaces.HkMem α 7 f →
        MeasureTheory.IntegrableOn
          (Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f))
          Work.Spaces.Iz ∧
        (∫ z in Work.Spaces.Iz,
            Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f) z)
          ≤ C * Work.Spaces.HkSq α 6 f := by
  obtain ⟨Czop, hCzop, hzopb⟩ := hZop
  obtain ⟨C₁, hC₁pos, hC₁b⟩ := Work.FTS.StrongPersist.L6Aux.L12SlotSum6
  obtain ⟨Cc0, hCc0pos, hC0b⟩ := Alt_C0_sq_le_HkSq6
  obtain ⟨Cb, hCbpos, hBb⟩ := Alt_slotSum_ampB_div_le
  obtain ⟨KA, hKA, hKAb⟩ := Alt_ampA_dzdIter_bound6
  refine ⟨2 * (Czop * (1 + KA) ^ 2 * C₁) + 2 * (Cc0 * Cb), ?_, ?_⟩
  · have h1 : 0 < Czop * (1 + KA) ^ 2 * C₁ := by
      have hK1 : 0 < 1 + KA := by linarith
      exact mul_pos (mul_pos hCzop (pow_pos hK1 2)) hC₁pos
    have h2 : 0 < Cc0 * Cb := mul_pos hCc0pos hCbpos
    linarith
  intro α hαIoc f hf hmem7
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hf.reg.1
  have hmem6 : Work.Spaces.HkMem α 6 f :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hsm hmem7
  have hu6 : ContDiffOn ℝ 6 (fun z' => Work.Coercivity.L12f f z') (Set.Ioi (0 : ℝ)) := by
    have h := Work.FTS.StrongPersist.contDiffOn6_L12_of (α := α) (f := f) hsm hmem7
    have hfun : (fun z' => Work.Coercivity.L12f f z')
        = fun z' => Work.Construction.L12 f z' := rfl
    rw [hfun]
    exact h
  have hA6 : ContDiffOn ℝ 6 (fun z' => Work.FTS.CoercivityFix.Transfer.ampA α z'
      * Work.Coercivity.L12f f z') (Set.Ioi (0 : ℝ)) :=
    (contDiffOn_six_ampA hα hα1).mul hu6
  -- abbreviations
  set u : ℝ → ℝ := fun z' => Work.Coercivity.L12f f z' with hu
  set C0 : ℝ := Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 with hC0
  set S1 : ℝ → ℝ := fun z => ∑ q ∈ Finset.range 7, (Work.Elliptic.DzdIter q
      (fun z' => Work.FTS.CoercivityFix.Transfer.ampA α z' * u z') z) ^ 2
        * (Work.Spaces.w z) ^ 2 with hS1
  set S2 : ℝ → ℝ := fun z => ∑ q ∈ Finset.range 7, (Work.Elliptic.DzdIter q
      (fun z' => Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α) z) ^ 2
        * (Work.Spaces.w z) ^ 2 with hS2
  set Su : ℝ → ℝ := fun z => ∑ q ∈ Finset.range 7,
      (Work.Elliptic.DzdIter q u z) ^ 2 * (Work.Spaces.w z) ^ 2 with hSu
  set S3 : ℝ → ℝ := fun z => ∑ q ∈ Finset.range 7,
      (Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
        * (Work.Spaces.w z) ^ 2 with hS3
  have hSnn : ∀ S : ℝ → ℝ, (∀ z, 0 ≤ S z) → 0 ≤ ∫ z in Set.Ioi (0 : ℝ), S z :=
    fun S hS => integral_nonneg hS
  -- `L₁₂f`-slots: integrability and bound
  have hL12i := hC₁b α hα hα1 f hsm hmem6 hf.l12
  have hExp_eq : (fun z => ∑ q ∈ Finset.range 7,
      (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z) z 0) ^ 2
        * (Work.Spaces.w z) ^ 2) = Su := by
    rw [hSu, hu]
    funext z
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Work.Elliptic.DzIter_rad]
    rfl
  have hIzIoi : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ))).symm
  have hIoiIz : Set.Ioi (0 : ℝ) =ᵐ[volume] Work.Spaces.Iz :=
    MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ))
  have hUint : MeasureTheory.IntegrableOn Su (Set.Ioi (0 : ℝ)) := by
    have h2 : MeasureTheory.IntegrableOn (fun z => ∑ q ∈ Finset.range 7,
        (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z) z 0) ^ 2
          * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := hL12i.1
    rw [hExp_eq] at h2
    exact h2.congr_set_ae hIoiIz
  have hUbd : (∫ z in Set.Ioi (0 : ℝ), Su z) ≤ C₁ * Work.Spaces.HkSq α 6 f := by
    have h2 : (∫ z in Work.Spaces.Iz, ∑ q ∈ Finset.range 7,
        (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z) z 0) ^ 2
          * (Work.Spaces.w z) ^ 2) ≤ C₁ * Work.Spaces.HkSq α 6 f := hL12i.2
    rw [hExp_eq] at h2
    rwa [(MeasureTheory.setIntegral_congr_set (μ := volume) hIoiIz).symm] at h2
  -- the z-multiplier bound
  have hZp : ∀ z ∈ Set.Ioi (0 : ℝ), S1 z ≤ Czop * (1 + KA) ^ 2 * Su z := by
    intro z hz
    have h := hzopb (fun z' => Work.FTS.CoercivityFix.Transfer.ampA α z') u KA hKA
      (fun j hj z' hz' => hKAb α hαIoc j hj z' hz') (contDiffOn_six_ampA hα hα1) hu6 z hz
    rwa [hS1, hSu]
  have hS1nn : ∀ z, 0 ≤ S1 z := by
    intro z
    rw [hS1]
    exact Finset.sum_nonneg fun q _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hS2nn : ∀ z, 0 ≤ S2 z := by
    intro z
    rw [hS2]
    exact Finset.sum_nonneg fun q _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hS3nn : ∀ z, 0 ≤ S3 z := by
    intro z
    rw [hS3]
    exact Finset.sum_nonneg fun q _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hS1int : MeasureTheory.IntegrableOn S1 (Set.Ioi (0 : ℝ)) := by
    refine Integrable.mono' (hUint.const_mul (Czop * (1 + KA) ^ 2)) ?_ ?_
    · rw [hS1]
      exact (Alt_continuousOn_slotSum (n := 6) hA6).aestronglyMeasurable measurableSet_Ioi
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hS1nn z)]
      exact hZp z hz
  have hS1bd : (∫ z in Set.Ioi (0 : ℝ), S1 z)
      ≤ (Czop * (1 + KA) ^ 2) * (∫ z in Set.Ioi (0 : ℝ), Su z) := by
    have h := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall hS1nn) (hUint.const_mul (Czop * (1 + KA) ^ 2))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hZp)
    rwa [MeasureTheory.integral_const_mul] at h
  have hS2int : MeasureTheory.IntegrableOn S2 (Set.Ioi (0 : ℝ)) := by
    have h2 : MeasureTheory.IntegrableOn (fun z => ∑ q ∈ Finset.range 7,
        (Work.Elliptic.DzdIter q (fun z' =>
          Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α) z) ^ 2
            * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := (hBb α hαIoc).1
    rw [← hS2] at h2
    exact h2.congr_set_ae hIoiIz
  have hS2bd : (∫ z in Set.Ioi (0 : ℝ), S2 z) ≤ Cb := by
    have h2 : (∫ z in Work.Spaces.Iz, ∑ q ∈ Finset.range 7,
        (Work.Elliptic.DzdIter q (fun z' =>
          Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α) z) ^ 2
            * (Work.Spaces.w z) ^ 2) ≤ Cb := (hBb α hαIoc).2
    rw [← hS2] at h2
    rwa [(MeasureTheory.setIntegral_congr_set (μ := volume) hIoiIz).symm] at h2
  -- the pointwise majorant
  have hpt : ∀ z ∈ Set.Ioi (0 : ℝ), S3 z ≤ 2 * S1 z + (2 * C0 ^ 2) * S2 z := by
    intro z hz
    rw [hS3, hS1, hS2, hC0]
    simp only
    rw [← Alt_SlotSum_eq (Work.FTS.CoercivityFix.Transfer.radA α f) z]
    exact Alt_SlotSum_radA_ptwise hα hα1 f hsm hmem7 hz
  have hMono : (∫ z in Set.Ioi (0 : ℝ), S3 z)
      ≤ ∫ z in Set.Ioi (0 : ℝ), (2 * S1 z + (2 * C0 ^ 2) * S2 z) :=
    MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall hS3nn)
      ((hS1int.const_mul 2).add (hS2int.const_mul (2 * C0 ^ 2)))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hpt)
  have hSplit : (∫ z in Set.Ioi (0 : ℝ), (2 * S1 z + (2 * C0 ^ 2) * S2 z))
      = 2 * (∫ z in Set.Ioi (0 : ℝ), S1 z)
        + (2 * C0 ^ 2) * (∫ z in Set.Ioi (0 : ℝ), S2 z) := by
    rw [MeasureTheory.integral_add (hS1int.const_mul 2) (hS2int.const_mul (2 * C0 ^ 2)),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have hC0sq : C0 ^ 2 ≤ Cc0 * Work.Spaces.HkSq α 6 f := by
    rw [hC0]
    exact hC0b α hαIoc f hf hmem7
  have hCz : 0 ≤ Czop * (1 + KA) ^ 2 := mul_nonneg hCzop.le (sq_nonneg _)
  have hS2nnint : 0 ≤ ∫ z in Set.Ioi (0 : ℝ), S2 z := integral_nonneg hS2nn
  have hstep1 : 2 * (∫ z in Set.Ioi (0 : ℝ), S1 z)
      ≤ 2 * (Czop * (1 + KA) ^ 2 * (C₁ * Work.Spaces.HkSq α 6 f)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact hS1bd.trans (mul_le_mul_of_nonneg_left hUbd hCz)
  have hstep2 : (2 * C0 ^ 2) * (∫ z in Set.Ioi (0 : ℝ), S2 z)
      ≤ (2 * (Cc0 * Work.Spaces.HkSq α 6 f)) * Cb := by
    have hb0 : 0 ≤ 2 * (Cc0 * Work.Spaces.HkSq α 6 f) :=
      le_trans (by positivity)
        (mul_le_mul_of_nonneg_left hC0sq (by norm_num))
    exact mul_le_mul (mul_le_mul_of_nonneg_left hC0sq (by norm_num)) hS2bd
      hS2nnint hb0
  have hchain : (∫ z in Set.Ioi (0 : ℝ), S3 z)
      ≤ (2 * (Czop * (1 + KA) ^ 2 * C₁) + 2 * (Cc0 * Cb)) * Work.Spaces.HkSq α 6 f := by
    calc (∫ z in Set.Ioi (0 : ℝ), S3 z)
        ≤ ∫ z in Set.Ioi (0 : ℝ), (2 * S1 z + (2 * C0 ^ 2) * S2 z) := hMono
      _ = 2 * (∫ z in Set.Ioi (0 : ℝ), S1 z)
            + (2 * C0 ^ 2) * (∫ z in Set.Ioi (0 : ℝ), S2 z) := hSplit
      _ ≤ 2 * (Czop * (1 + KA) ^ 2 * (C₁ * Work.Spaces.HkSq α 6 f))
            + (2 * (Cc0 * Work.Spaces.HkSq α 6 f)) * Cb := add_le_add hstep1 hstep2
      _ = (2 * (Czop * (1 + KA) ^ 2 * C₁) + 2 * (Cc0 * Cb)) * Work.Spaces.HkSq α 6 f := by
          ring
  have hS3_eq : Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f)
      = S3 := by
    rw [hS3]
    funext z
    exact Alt_SlotSum_eq _ z
  refine ⟨?_, ?_⟩
  · have h2 : MeasureTheory.IntegrableOn S3 (Set.Ioi (0 : ℝ)) := by
      refine Integrable.mono' ((hS1int.const_mul 2).add (hS2int.const_mul (2 * C0 ^ 2))) ?_ ?_
      · rw [hS3]
        exact (Alt_continuousOn_slotSum (n := 6)
          (contDiffOn_six_radA hα hα1 hsm hmem7)).aestronglyMeasurable measurableSet_Ioi
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (hS3nn z)]
        exact hpt z hz
    have h3 : MeasureTheory.IntegrableOn S3 Work.Spaces.Iz := h2.congr_set_ae hIzIoi
    rwa [← hS3_eq] at h3
  · have h2 : (∫ z in Work.Spaces.Iz, S3 z)
        ≤ (2 * (Czop * (1 + KA) ^ 2 * C₁) + 2 * (Cc0 * Cb)) * Work.Spaces.HkSq α 6 f := by
      rw [(MeasureTheory.setIntegral_congr_set (μ := volume) hIoiIz).symm]
      exact hchain
    rwa [← hS3_eq] at h2

/-- **The radial slot bound, end to end** (the `ZopSlotMul_le` multiplier estimate of the
sibling module instantiated in `Alt_SlotSum_radA_le`). -/
theorem Alt_SlotSum_radA_le' : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ f : ℝ → ℝ → ℝ,
    Work.FTS.StrongPersist.H6Adm α f → Work.Spaces.HkMem α 7 f →
      MeasureTheory.IntegrableOn
        (Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f))
        Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz,
          Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f) z)
        ≤ C * Work.Spaces.HkSq α 6 f :=
  Alt_SlotSum_radA_le Work.FTS.StrongPersist.H6Aux.ZopSlotMul_le

end Work.FTS.StrongPersist.H6Aux
