import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Nonlinear.Pieces.Ctx
import Submission.Work.FTS.Nonlinear.Pieces.Basic
import Submission.Work.Spaces.WlInf_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Real

/-- The `𝒲^{l,∞}`-structure of `Work.Spaces` is monotone in the order: for `l ≤ l'`, membership
at `l'` gives membership at `l`, and the norm at `l` is bounded by the norm at `l'`.

This is what lets row 14 read the `𝒲^{5,∞}`-fact `StarPkg.dU` (control of `∂_θ(U(Φ̃_*))`) at the
order `4` at which the transport interface `N4Extra.st` is stated.  (A public version of the
same fact is being produced independently at `FTS/Nonlinear/Pieces/RNP/WlInf_mono`.) -/
private theorem wlInf_mono_4_5 {α : ℝ} {l l' : ℕ} (hll : l ≤ l') {f : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.WlInfMem α l' f) :
    Work.Spaces.WlInfMem α l f ∧ Work.Spaces.WlInf α l f ≤ Work.Spaces.WlInf α l' f := by
  refine ⟨⟨fun k hk => hmem.1 k (le_trans hk hll), fun j hj k hk hj1 hjk =>
    hmem.2 j (le_trans hj hll) k (le_trans hk hll) hj1 (le_trans hjk hll)⟩, ?_⟩
  rw [Work.Spaces.WlInf, Work.Spaces.WlInf]
  have hZ : (∑ k ∈ Finset.range (l + 1),
        Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k f z θ))
      ≤ (∑ k ∈ Finset.range (l' + 1),
        Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k f z θ)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (Nat.succ_le_succ hll)) ?_
    intro k hk _
    exact Work.Spaces.supAbs_nonneg (hmem.1 k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
  have hb : ∀ j ≤ l', ∀ k ≤ l', 0 ≤ (if 1 ≤ j ∧ k + j ≤ l' then
        Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k
          (Work.Spaces.DthIter j f) z θ * (Real.sin (2 * θ)) ^ (-(α / 5))
          / (α + Real.sin (2 * θ)))
        else 0) := by
    intro j hj k hk
    by_cases h2 : 1 ≤ j ∧ k + j ≤ l'
    · rw [if_pos h2]
      exact Work.Spaces.supAbs_nonneg (hmem.2 j hj k hk h2.1 h2.2)
    · rw [if_neg h2]
  have hM1 : (∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
        if 1 ≤ j ∧ k + j ≤ l then
          Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k
            (Work.Spaces.DthIter j f) z θ * (Real.sin (2 * θ)) ^ (-(α / 5))
            / (α + Real.sin (2 * θ)))
        else 0)
      ≤ (∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
        if 1 ≤ j ∧ k + j ≤ l' then
          Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k
            (Work.Spaces.DthIter j f) z θ * (Real.sin (2 * θ)) ^ (-(α / 5))
            / (α + Real.sin (2 * θ)))
        else 0) := by
    refine Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk => ?_
    have hjle : j ≤ l' := le_trans (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hll
    have hkle : k ≤ l' := le_trans (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) hll
    by_cases h : 1 ≤ j ∧ k + j ≤ l
    · rw [if_pos h, if_pos ⟨h.1, le_trans h.2 hll⟩]
    · rw [if_neg h]
      by_cases h2 : 1 ≤ j ∧ k + j ≤ l'
      · rw [if_pos h2]
        exact Work.Spaces.supAbs_nonneg (hmem.2 j hjle k hkle h2.1 h2.2)
      · rw [if_neg h2]
  have hM2a : (∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
        if 1 ≤ j ∧ k + j ≤ l' then
          Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k
            (Work.Spaces.DthIter j f) z θ * (Real.sin (2 * θ)) ^ (-(α / 5))
            / (α + Real.sin (2 * θ)))
        else 0)
      ≤ (∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l' + 1),
        if 1 ≤ j ∧ k + j ≤ l' then
          Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k
            (Work.Spaces.DthIter j f) z θ * (Real.sin (2 * θ)) ^ (-(α / 5))
            / (α + Real.sin (2 * θ)))
        else 0) := by
    refine Finset.sum_le_sum fun j hj => ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (Nat.succ_le_succ hll)) ?_
    intro k hk _
    exact hb j (le_trans (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hll) k
      (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  have hM2b : (∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l' + 1),
        if 1 ≤ j ∧ k + j ≤ l' then
          Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k
            (Work.Spaces.DthIter j f) z θ * (Real.sin (2 * θ)) ^ (-(α / 5))
            / (α + Real.sin (2 * θ)))
        else 0)
      ≤ (∑ j ∈ Finset.range (l' + 1), ∑ k ∈ Finset.range (l' + 1),
        if 1 ≤ j ∧ k + j ≤ l' then
          Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k
            (Work.Spaces.DthIter j f) z θ * (Real.sin (2 * θ)) ^ (-(α / 5))
            / (α + Real.sin (2 * θ)))
        else 0) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (Nat.succ_le_succ hll)) ?_
    intro j hj _
    exact Finset.sum_nonneg fun k hk =>
      hb j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) k
        (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  linarith [hZ, hM1, hM2a, hM2b]

theorem row14 (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.Nonlin.N4Norm Ci α₂)
    (hE : Work.FTS.Nonlin.N4Extra IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.StarPkg α Cs Φs →
      Work.FTS.Nonlin.EllPkgG α Ce g Φg → 0 < α → α ≤ 1 → α ≤ α₂ →
      |IP α (Work.FTS.Nonlin.N2sg α Φs g) g|
        ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2) := by
  refine ⟨|2 * Ct * Cs| + 1, ?_, ?_⟩
  · have := abs_nonneg (2 * Ct * Cs); linarith
  · intro α g Φs Φg hgal hstar hell hα hα1 hαα₂
    have hCt : 0 < Ct := hE.pos.1
    have hg4 : Work.FTS.Nonlin.RegQ α 4 g := Work.FTS.Nonlin.galClass_regQ4 hgal
    have hαIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
    have hvanish : Work.Spaces.VanishTheta
        (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) := by
      simpa only [Work.FTS.Nonlin.PhiTs] using hstar.vanishU
    have hW5 : Work.Spaces.WlInfMem α 5
        (Work.Spaces.pth (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs))) := by
      simpa only [Work.FTS.Nonlin.PhiTs] using hstar.dU.1
    have hW5le : Work.Spaces.WlInf α 5
        (Work.Spaces.pth (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)))
        ≤ Cs * α := by
      simpa only [Work.FTS.Nonlin.PhiTs] using hstar.dU.2
    obtain ⟨hW4, hW45⟩ := wlInf_mono_4_5 (show (4 : ℕ) ≤ 5 by norm_num) hW5
    set U : Work.FTS.Galerkin.Fn :=
      Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) with hU
    rw [hU] at hvanish hW4 hW45 hW5le
    have hCsα : Work.Spaces.WlInf α 4 (Work.Spaces.pth U) ≤ Cs * α := le_trans hW45 hW5le
    have hst := hE.st α hαIoc U g hvanish hW4 hg4
    have hsm := hE.smul α hαIoc (-2)
      (fun z θ => U z θ * Work.Spaces.pth g z θ) g hg4
    have hfun : Work.FTS.Nonlin.N2sg α Φs g
        = (fun z θ => (-2) * ((fun z θ => U z θ
            * Work.Spaces.pth g z θ) z θ)) := by
      funext z θ
      simp only [Work.FTS.Nonlin.N2sg, hU, Work.FTS.Nonlin.PhiTs]
      ring
    rw [hfun, hsm, abs_mul, abs_of_neg (by norm_num : (-2 : ℝ) < 0)]
    have hXsq : (0 : ℝ) ≤ Work.FTS.Nonlin.Xn α g ^ 2 := sq_nonneg _
    have hαp : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
    have hαhalf : α ^ (-(1 / 2 : ℝ)) * α = Real.sqrt α := by
      have h1 : α ^ (-(1 / 2 : ℝ)) * α ^ (1 : ℝ) = α ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_add hα, show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num]
      rw [Real.rpow_one α] at h1
      rw [Real.sqrt_eq_rpow]
      exact h1
    have hstep1 : 2 * |IP α (fun z θ => U z θ * Work.Spaces.pth g z θ) g|
        ≤ 2 * (Ct * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 (Work.Spaces.pth U)
            * Work.FTS.Nonlin.Xn α g ^ 2) :=
      mul_le_mul_of_nonneg_left hst (by norm_num)
    have hstep2 : 2 * (Ct * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 (Work.Spaces.pth U)
            * Work.FTS.Nonlin.Xn α g ^ 2)
        ≤ 2 * (Ct * α ^ (-(1 / 2 : ℝ)) * (Cs * α) * Work.FTS.Nonlin.Xn α g ^ 2) := by
      have h1 : Work.Spaces.WlInf α 4 (Work.Spaces.pth U) * Work.FTS.Nonlin.Xn α g ^ 2
          ≤ (Cs * α) * Work.FTS.Nonlin.Xn α g ^ 2 :=
        mul_le_mul_of_nonneg_right hCsα hXsq
      have h2 : 0 ≤ 2 * (Ct * α ^ (-(1 / 2 : ℝ))) := by nlinarith [hCt, hαp]
      calc 2 * (Ct * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 (Work.Spaces.pth U)
              * Work.FTS.Nonlin.Xn α g ^ 2)
          = (2 * (Ct * α ^ (-(1 / 2 : ℝ)))) * (Work.Spaces.WlInf α 4 (Work.Spaces.pth U)
              * Work.FTS.Nonlin.Xn α g ^ 2) := by ring
        _ ≤ (2 * (Ct * α ^ (-(1 / 2 : ℝ)))) * ((Cs * α)
              * Work.FTS.Nonlin.Xn α g ^ 2) := mul_le_mul_of_nonneg_left h1 h2
        _ = 2 * (Ct * α ^ (-(1 / 2 : ℝ)) * (Cs * α) * Work.FTS.Nonlin.Xn α g ^ 2) := by ring
    have hstep3 : 2 * (Ct * α ^ (-(1 / 2 : ℝ)) * (Cs * α) * Work.FTS.Nonlin.Xn α g ^ 2)
        = 2 * Ct * Cs * Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2 := by
      rw [show 2 * (Ct * α ^ (-(1 / 2 : ℝ)) * (Cs * α) * Work.FTS.Nonlin.Xn α g ^ 2)
            = 2 * (Ct * (Cs * (α ^ (-(1 / 2 : ℝ)) * α))
              * Work.FTS.Nonlin.Xn α g ^ 2) from by ring, hαhalf]
      ring
    have hstep4 : 2 * Ct * Cs * Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2
        ≤ (|2 * Ct * Cs| + 1) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2) := by
      have hc : 2 * Ct * Cs ≤ |2 * Ct * Cs| + 1 := by
        have := le_abs_self (2 * Ct * Cs); linarith
      rw [show 2 * Ct * Cs * Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2
            = (2 * Ct * Cs) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2) from by ring]
      exact mul_le_mul_of_nonneg_right hc (mul_nonneg (Real.sqrt_nonneg α) hXsq)
    linarith [hstep1, hstep2, hstep3, hstep4]

end Work.FTS.Nonlinear.Pieces.RNP
