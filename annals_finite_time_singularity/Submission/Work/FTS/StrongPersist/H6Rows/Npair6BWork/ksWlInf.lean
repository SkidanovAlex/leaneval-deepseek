import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.KsAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

set_option autoImplicit false

/-- Every `∂_z`-iterate of the identically zero function vanishes. -/
private lemma pzIter_zero_fun (k : ℕ) :
    Work.Spaces.pzIter k (fun _ _ : ℝ => (0:ℝ)) = fun _ _ => (0:ℝ) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Work.Spaces.pzIter_succ, ih]; funext z θ; simp [Work.Spaces.pz]

-- Import `Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.KsAux` (which defines
-- `KsFun α = fun z _ => α * (2 * z / (1 + z) ^ 2)` — definitionally the function below — and
-- proves the helpers `KsFun_eq_FK`, `pzIter_KsFun`, `ks_pz_bound`,
-- `DthIter_KsFun_eq_zero`), plus `Submission.Work.Spaces.Defs` (`WlInf`, `WlInfMem`,
-- `supAbs_le`, `HkAux.supFinite_of_pointwise`).
-- Route: `pzIter_KsFun` + `ks_pz_bound` give `supAbs ((z+1)^k ∂_z^k Ks) ≤ 2α·k!(k+1)` for
-- `k ≤ 6` via `Work.Spaces.supAbs_le`, and `DthIter_KsFun_eq_zero` kills every `j ≥ 1`
-- angular slot (`supAbs` of the identically zero function is ≤ 0).  Summing,
-- `WlInf α 6 Ks ≤ 2α·Σ_{k≤6} k!(k+1) = 11826α`.
theorem ksWlInf : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    Work.Spaces.WlInfMem α 6 (fun z (_ : ℝ) => α * (2 * z / (1 + z) ^ 2)) ∧
    Work.Spaces.WlInf α 6 (fun z (_ : ℝ) => α * (2 * z / (1 + z) ^ 2)) ≤ C * α := by
  refine ⟨11826, by norm_num, fun α hαI => ?_⟩
  obtain ⟨hαpos, hαle⟩ := hαI
  have hα0 : 0 ≤ α := le_of_lt hαpos
  have hKs : (fun z (_ : ℝ) => α * (2 * z / (1 + z) ^ 2)) = KsFun α := rfl
  refine ⟨?_, ?_⟩
  · rw [hKs]
    -- `WlInfMem α 6 (KsFun α)`: the radial slots are bounded by `ks_pz_bound`, the
    -- angular slots are identically zero.
    refine ⟨fun k hk => ?_, fun j hj k hk hj1 hkj => ?_⟩
    · refine ⟨2 * α * ((k.factorial : ℝ) * (k + 1)), fun y hy => ?_⟩
      obtain ⟨z, hz, θ, hθ, rfl⟩ := hy
      exact ks_pz_bound α hα0 k z hz θ
    · refine ⟨0, fun y hy => ?_⟩
      obtain ⟨z, hz, θ, hθ, rfl⟩ := hy
      have h1 : Work.Spaces.pzIter k (Work.Spaces.DthIter j (KsFun α)) = fun _ _ => (0:ℝ) := by
        rw [DthIter_KsFun_eq_zero α hj1, pzIter_zero_fun]
      rw [h1]
      simp
  · rw [hKs, Work.Spaces.WlInf]
    -- The angular sum vanishes identically: every surviving slot (`j ≥ 1`) is the
    -- supremum of the zero function.
    have hth : (∑ j ∈ Finset.range (6 + 1), ∑ k ∈ Finset.range (6 + 1),
        if 1 ≤ j ∧ k + j ≤ 6 then
          Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
            * Work.Spaces.pzIter k (Work.Spaces.DthIter j (KsFun α)) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        else 0) ≤ 0 := by
      refine Finset.sum_nonpos fun j hj => Finset.sum_nonpos fun k hk => ?_
      by_cases hc : 1 ≤ j ∧ k + j ≤ 6
      · rw [if_pos hc]
        refine Work.Spaces.supAbs_le (fun z hz θ hθ => ?_)
        have h1 : Work.Spaces.pzIter k (Work.Spaces.DthIter j (KsFun α)) = fun _ _ => (0:ℝ) := by
          rw [DthIter_KsFun_eq_zero α hc.1, pzIter_zero_fun]
        rw [h1]
        simp
      · rw [if_neg hc]
    -- The radial sum is bounded by `∑_{k ≤ 6} 2α·k!(k+1) = 11826α`.
    have hz_sum : (∑ k ∈ Finset.range (6 + 1),
        Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k (KsFun α) z θ))
        ≤ 2 * α * 5913 :=
      calc (∑ k ∈ Finset.range (6 + 1),
            Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k (KsFun α) z θ))
          ≤ ∑ k ∈ Finset.range (6 + 1), 2 * α * ((k.factorial : ℝ) * (k + 1)) :=
            Finset.sum_le_sum fun k hk => Work.Spaces.supAbs_le (fun z hz θ hθ =>
              ks_pz_bound α hα0 k z hz θ)
        _ = 2 * α * 5913 := by
            norm_num [Finset.sum_range_succ, Nat.factorial]
            ring
    calc (∑ k ∈ Finset.range (6 + 1),
          Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k (KsFun α) z θ))
        + (∑ j ∈ Finset.range (6 + 1), ∑ k ∈ Finset.range (6 + 1),
          if 1 ≤ j ∧ k + j ≤ 6 then
            Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
              * Work.Spaces.pzIter k (Work.Spaces.DthIter j (KsFun α)) z θ
              * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
          else 0)
        ≤ 2 * α * 5913 + 0 := add_le_add hz_sum hth
      _ = 11826 * α := by ring

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
