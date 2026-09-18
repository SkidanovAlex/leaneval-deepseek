import Mathlib
import Submission.Work.MassTransferenceAlt.Tree.Data

namespace Work.MassTransferenceAlt.Tree

open Finset

/-- **Mass conservation at one node.**  The total `f`-volume of the children of a node
is at least the `f`-volume of the node. -/
lemma vfChildrenGe (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) (c ρ : ℕ → ℝ) (η : ℝ)
    (T : Work.MassTransferenceAlt.TreeData d c ρ η) (n : ℕ) (B : ℕ) (hB : B ∈ T.lev n) :
    Work.MassTransferenceAlt.vf d ρ B
      ≤ ∑ i ∈ (T.lev (n+1)).filter (fun i => T.par (n+1) i = some B),
          Work.MassTransferenceAlt.vf d ρ i := by
  classical
  -- The children of `B` at level `n+1`.
  set F : Finset ℕ := (T.lev (n+1)).filter (fun i => T.par (n+1) i = some B) with hF
  have hρB : 0 < ρ B := (T.good n B hB).1
  -- The children form a local level of `B` with `nsub d (ρ B)` sub-levels.
  have hloc := T.loc n B hB
  rw [← hF] at hloc
  obtain ⟨hpos, hthr, hIv, hdisj1, hdisj3, hsub_lt, hnon, hlevel, hdecay⟩ := hloc
  -- Split the sum over the children according to the sub-level.
  have hdecomp : ∑ i ∈ F, (ρ i)^d
      = ∑ k ∈ range (Work.MassTransferenceAlt.nsub d (ρ B)),
          ∑ i ∈ F.filter (fun i => T.sub (n+1) i = k), (ρ i)^d :=
    (Finset.sum_fiberwise_of_maps_to (s := F) (t := range (Work.MassTransferenceAlt.nsub d (ρ B)))
      (g := fun i => T.sub (n+1) i) (fun i hi => mem_range.mpr (hsub_lt i hi)) _).symm
  -- Each sub-level carries at least `ρ B / 16`, and there are `nsub d (ρ B)` of them.
  have hlevel' : ((Work.MassTransferenceAlt.nsub d (ρ B) : ℕ) : ℝ) * (ρ B / 16)
      ≤ ∑ i ∈ F, (ρ i)^d := by
    calc ((Work.MassTransferenceAlt.nsub d (ρ B) : ℕ) : ℝ) * (ρ B / 16)
        = ∑ _k ∈ range (Work.MassTransferenceAlt.nsub d (ρ B)), (ρ B / 16) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ k ∈ range (Work.MassTransferenceAlt.nsub d (ρ B)),
            ∑ i ∈ F.filter (fun i => T.sub (n+1) i = k), (ρ i)^d :=
          Finset.sum_le_sum (fun k hk => hlevel k (mem_range.mp hk))
      _ = ∑ i ∈ F, (ρ i)^d := hdecomp.symm
  -- `nsub d R > 16 R ^ (d-1)`, hence `nsub d R * (R/16) > R^d`.
  have hpow : (ρ B)^d < ((Work.MassTransferenceAlt.nsub d (ρ B) : ℕ) : ℝ) * (ρ B / 16) := by
    have hlt := Work.MassTransferenceAlt.lt_nsub hρB hd1
    have hRd : (ρ B)^d = (ρ B)^(d-1) * ρ B := by
      conv_lhs => rw [show d = (d - 1) + 1 by ring]
      rw [Real.rpow_add hρB, Real.rpow_one]
    rw [hRd]
    nlinarith [hlt, Real.rpow_pos_of_pos hρB (d-1)]
  have hsum : (ρ B)^d < ∑ i ∈ F, (ρ i)^d := lt_of_lt_of_le hpow hlevel'
  -- Multiply by `2 ^ d`.
  have h2 : (0:ℝ) < (2:ℝ)^d := Real.rpow_pos_of_pos (by norm_num) d
  have hmain : (2 * ρ B)^d ≤ ∑ i ∈ F, (2 * ρ i)^d := by
    have hmul := mul_le_mul_of_nonneg_left hsum.le h2.le
    rw [Finset.mul_sum] at hmul
    calc (2 * ρ B)^d = (2:ℝ)^d * (ρ B)^d := Real.mul_rpow (by norm_num) hρB.le
      _ ≤ ∑ i ∈ F, (2:ℝ)^d * (ρ i)^d := hmul
      _ = ∑ i ∈ F, (2 * ρ i)^d :=
          Finset.sum_congr rfl (fun i hi => by rw [Real.mul_rpow (by norm_num) (hpos i hi).le])
  simpa only [Work.MassTransferenceAlt.vf] using hmain

end Work.MassTransferenceAlt.Tree
