import Mathlib
import Submission.Work.RPCore.Chain.C4Defs
import Submission.Work.RPCore.Chain.ChainDefs
import Submission.Work.RPCore.Chain.ChainProj
import Submission.Work.RPCore.Chain.chainAction_sub_refGF
import Submission.Work.RPCore.Chain.bounds_of_periodic_slab
import Submission.Work.RPCore.Chain.norm_fderiv_pullback_le

namespace Work.RPCore.Chain

open Work.RPV
open scoped BigOperators

noncomputable section

theorem chainPert_bounds (n N : ℕ) (δ : ℝ) (W : Fin (n + 1) → Work.RPV.PS → ℝ)
    (hWc : ∀ j, ContDiff ℝ 3 (W j))
    (hWmid : ∀ j : Fin (n + 1), midBlock N (j : ℕ) → W j = Work.RPV.Wrot δ)
    (hWper : ∀ j x, W j (Work.RPV.Tk 1 x) = W j x)
    (hWsup : ∀ j : Fin (n + 1), ¬ midBlock N (j : ℕ) →
      ∃ R : ℝ, ∀ x, R ≤ |x.1.1| + |x.2.1| + |x.2.2| → W j x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      ContDiff ℝ 2 (fun z : ChainSp n =>
        Work.RPV.chainAction n W z.1 z.2
          - Work.RPV.chainAction n (fun j => refGF N δ (j : ℕ)) z.1 z.2) ∧
      (∀ z : ChainSp n,
        |Work.RPV.chainAction n W z.1 z.2
          - Work.RPV.chainAction n (fun j => refGF N δ (j : ℕ)) z.1 z.2| ≤ C) ∧
      (∀ z : ChainSp n,
        ‖fderiv ℝ (fun z : ChainSp n =>
          Work.RPV.chainAction n W z.1 z.2
            - Work.RPV.chainAction n (fun j => refGF N δ (j : ℕ)) z.1 z.2) z‖ ≤ C) := by
  classical
  -- (1) the perturbation is the (negated) sum of the individual summands
  have hpt : ∀ z : ChainSp n,
      Work.RPV.chainAction n W z.1 z.2
        - Work.RPV.chainAction n (fun j => refGF N δ (j : ℕ)) z.1 z.2
      = -∑ j : Fin (n + 1), stepFun n N δ W j z :=
    fun z => chainAction_sub_refGF n N δ W hWmid z
  -- (2) each summand is `C³`
  have hcd : ∀ j : Fin (n + 1), ContDiff ℝ 3 (stepFun n N δ W j) :=
    fun j => contDiff_stepFun (hWc j)
  -- (3) each summand is bounded, together with its derivative, by a constant
  have hbdd : ∀ j : Fin (n + 1),
      ∃ M : ℝ, 0 ≤ M ∧ (∀ z : ChainSp n, |stepFun n N δ W j z| ≤ M) ∧
        (∀ z : ChainSp n, ‖fderiv ℝ (stepFun n N δ W j) z‖ ≤ M) := by
    intro j
    by_cases hm : midBlock N (j : ℕ)
    · refine ⟨0, le_refl 0, ?_, ?_⟩
      · intro z; rw [stepFun_of_mid hm z]; simp
      · intro z; rw [stepFun_eq_zero hm]; simp
    · obtain ⟨Rj, hRj⟩ := hWsup j hm
      obtain ⟨M, hM0, hfx, hdfx⟩ :=
        bounds_of_periodic_slab (W j) ((hWc j).of_le (by norm_num)) (hWper j) Rj hRj
      refine ⟨M, hM0, ?_, ?_⟩
      · intro z; rw [stepFun_of_not_mid hm z]; exact hfx (projPS n j z)
      · intro z
        rw [stepFun_eq_pullback hm]
        calc ‖fderiv ℝ (fun z : ChainSp n => W j (projPS n j z)) z‖
            ≤ M * ‖projPS n j‖ :=
              norm_fderiv_pullback_le (W j) (projPS n j) M ((hWc j).differentiable (by norm_num)) hdfx z
          _ ≤ M * 1 := mul_le_mul_of_nonneg_left (opNorm_projPS_le_one n j) hM0
          _ = M := mul_one M
  choose Mb hMb using hbdd
  have hMb0 : ∀ j : Fin (n + 1), 0 ≤ Mb j := fun j => (hMb j).1
  have hMb1 : ∀ j : Fin (n + 1), ∀ z : ChainSp n, |stepFun n N δ W j z| ≤ Mb j :=
    fun j => (hMb j).2.1
  have hMb2 : ∀ j : Fin (n + 1), ∀ z : ChainSp n, ‖fderiv ℝ (stepFun n N δ W j) z‖ ≤ Mb j :=
    fun j => (hMb j).2.2
  refine ⟨∑ j : Fin (n + 1), Mb j, Finset.sum_nonneg (fun j _ => hMb0 j), ?_, ?_, ?_⟩
  · -- the perturbation is `C²`
    have hfun : (fun z : ChainSp n =>
        Work.RPV.chainAction n W z.1 z.2
          - Work.RPV.chainAction n (fun j => refGF N δ (j : ℕ)) z.1 z.2)
        = fun z => -∑ j : Fin (n + 1), stepFun n N δ W j z := funext hpt
    rw [hfun]
    have hs : ContDiff ℝ 3 (fun z : ChainSp n => ∑ j : Fin (n + 1), stepFun n N δ W j z) :=
      ContDiff.sum (fun j _ => hcd j)
    exact (hs.neg).of_le (by norm_num)
  · -- value bound
    intro z
    rw [hpt z]
    calc |-(∑ j : Fin (n + 1), stepFun n N δ W j z)|
        = |∑ j : Fin (n + 1), stepFun n N δ W j z| := abs_neg _
      _ ≤ ∑ j : Fin (n + 1), |stepFun n N δ W j z| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin (n + 1), Mb j := Finset.sum_le_sum (fun j _ => hMb1 j z)
  · -- derivative bound
    intro z
    have hfun : (fun z : ChainSp n =>
        Work.RPV.chainAction n W z.1 z.2
          - Work.RPV.chainAction n (fun j => refGF N δ (j : ℕ)) z.1 z.2)
        = fun z => -∑ j : Fin (n + 1), stepFun n N δ W j z := funext hpt
    rw [hfun]
    have hfd : fderiv ℝ (fun z : ChainSp n => -∑ j : Fin (n + 1), stepFun n N δ W j z) z
        = -∑ j : Fin (n + 1), fderiv ℝ (stepFun n N δ W j) z := by
      have hs : fderiv ℝ (fun z : ChainSp n => ∑ j : Fin (n + 1), stepFun n N δ W j z) z
          = ∑ j : Fin (n + 1), fderiv ℝ (stepFun n N δ W j) z := by
        have h1 : (fun z : ChainSp n => ∑ j : Fin (n + 1), stepFun n N δ W j z)
            = ∑ j : Fin (n + 1), stepFun n N δ W j := by
          funext w; rw [Finset.sum_apply]
        rw [h1]
        exact fderiv_sum (fun j _ => ((hcd j).differentiable (by norm_num)).differentiableAt)
      have h2 : (fun z : ChainSp n => -∑ j : Fin (n + 1), stepFun n N δ W j z)
          = -(fun z : ChainSp n => ∑ j : Fin (n + 1), stepFun n N δ W j z) := rfl
      rw [h2, fderiv_neg, hs]
    rw [hfd]
    calc ‖-∑ j : Fin (n + 1), fderiv ℝ (stepFun n N δ W j) z‖
        = ‖∑ j : Fin (n + 1), fderiv ℝ (stepFun n N δ W j) z‖ := norm_neg _
      _ ≤ ∑ j : Fin (n + 1), ‖fderiv ℝ (stepFun n N δ W j) z‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin (n + 1), Mb j := Finset.sum_le_sum (fun j _ => hMb2 j z)

end

end Work.RPCore.Chain
