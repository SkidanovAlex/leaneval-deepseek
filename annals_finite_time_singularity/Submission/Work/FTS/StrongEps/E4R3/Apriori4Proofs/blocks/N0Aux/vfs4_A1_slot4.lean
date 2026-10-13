import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.L3Rhs.N0gAuxDefs
import Submission.Work.FTS.LocData6.DthIter_Gam_abs_le6
import Submission.Work.FTS.LocData.DthIter_Gam_abs_le
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsAngMassAux
import Submission.Work.Spaces.c_bounds
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.Coercivity.gamDth_l2_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- The statement uses the notation `π` for `Real.pi`.  This file is compiled with
-- `autoImplicit = false`, so the locale has to be opened for `π` to resolve (as in the
-- sibling `vfs4_VfsA2_jet`).
open scoped Real

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux

open Work.FTS.StrongPersist.L3Rhs (VfsA1 VfsGc dthU_iter_VfsA1_of_mem)

/-- **The order-`4` `dthU`-jet of `VfsA1 α` against the weight `sin(2θ)^{-γ(α)}`.**

`VfsA1 α = (3/2)·dthU (Γ/c)`, hence `dthU^[4] (VfsA1 α) = (3/2)·dthU^[5] (Γ/c)`.  The angular
jet bound `|dthU^m Γ| ≤ 10⁵·Γ` for `m ≤ 6` (`LocData6.DthIter_Gam_abs_le6`, via
`LocData.DthIter_rad_eq`) and `1/c ≤ 10` (`Spaces.c_bounds`) give

`|dthU^[4] (VfsA1 α) θ| ≤ (3/2)·10·10⁵·Γ(θ) = 1.5·10⁶·Γ(θ)`.

Squaring, `Γ(θ)² ≤ sin(2θ)^{2α/3}` (`Coercivity.Gam_sq_le_sin_two`) and
`2α/3 - γ(α) = -(1 - 17α/30)` (with `γ(α) = 1 + α/10`) give the claim, the constant being
`(1.5·10⁶)² = 2.25·10¹² = 2250000000000`. -/
theorem vfs4_A1_slot4 :
    ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      (Work.Spaces.dthU^[4] (Work.FTS.StrongPersist.L3Rhs.VfsA1 α) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        ≤ 2250000000000 * (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)) := by
  intro α hα hα1 θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hs_pos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hGam : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθI).1
  -- ## 1. the fourth jet of `VfsA1 α` is the fifth jet of `Γ/c`
  have h1 : Work.Spaces.dthU^[4] (VfsA1 α) θ = (3 / 2) * Work.Spaces.dthU^[5] (VfsGc α) θ :=
    dthU_iter_VfsA1_of_mem hθ 4
  -- ## 2. the constant factor `1/c` comes out of the jet
  have h2 : Work.Spaces.dthU^[5] (VfsGc α) θ
      = (1 / Work.Spaces.c α) * Work.Spaces.dthU^[5] (fun t => Work.Spaces.Gam α t) θ := by
    have hfun : VfsGc α = fun t : ℝ => (1 / Work.Spaces.c α) * Work.Spaces.Gam α t := by
      funext t
      rw [VfsGc]
      ring
    rw [hfun]
    simpa using congrFun (Work.Spaces.dthU_iter_const_mul 5 (1 / Work.Spaces.c α)
      (fun t => Work.Spaces.Gam α t)) θ
  -- ## 3. the angular jet bound for `Γ`
  have h3 : |Work.Spaces.dthU^[5] (fun t => Work.Spaces.Gam α t) θ|
      ≤ 100000 * Work.Spaces.Gam α θ := by
    have hkey := Work.FTS.LocData6.DthIter_Gam_abs_le6 5 (by norm_num) α hα hα1 hθI
    rw [Work.FTS.LocData.DthIter_rad_eq 5 (fun t => Work.Spaces.Gam α t) 0 θ] at hkey
    exact hkey
  -- ## 4. `1/c ≤ 10`
  have hc_inv : 1 / Work.Spaces.c α ≤ 10 := by
    have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
    have hcpos : (0 : ℝ) < Work.Spaces.c α := by linarith
    rw [div_le_iff₀ hcpos]
    linarith
  -- ## 5. the unweighted square bound, with the constant `(1.5·10⁶)²`
  have h4 : (Work.Spaces.dthU^[4] (VfsA1 α) θ) ^ 2
      ≤ 2250000000000 * (Work.Spaces.Gam α θ) ^ 2 := by
    have hcpos : (0 : ℝ) < 1 / Work.Spaces.c α := by
      have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
      exact one_div_pos.mpr (by linarith)
    have heq : |Work.Spaces.dthU^[4] (VfsA1 α) θ|
        = (3 / 2) * ((1 / Work.Spaces.c α)
            * |Work.Spaces.dthU^[5] (fun t => Work.Spaces.Gam α t) θ|) := by
      rw [h1, h2]
      simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (3 : ℝ) / 2),
        abs_of_pos hcpos]
    have hb : |Work.Spaces.dthU^[4] (VfsA1 α) θ| ≤ 1500000 * Work.Spaces.Gam α θ := by
      rw [heq]
      calc (3 / 2) * ((1 / Work.Spaces.c α)
              * |Work.Spaces.dthU^[5] (fun t => Work.Spaces.Gam α t) θ|)
          ≤ (3 / 2) * ((1 / Work.Spaces.c α) * (100000 * Work.Spaces.Gam α θ)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hcpos.le) (by norm_num)
        _ ≤ (3 / 2) * (10 * (100000 * Work.Spaces.Gam α θ)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hc_inv (mul_nonneg (by norm_num) hGam))
              (by norm_num)
        _ = 1500000 * Work.Spaces.Gam α θ := by ring
    calc (Work.Spaces.dthU^[4] (VfsA1 α) θ) ^ 2
        = |Work.Spaces.dthU^[4] (VfsA1 α) θ| ^ 2 := by rw [sq_abs]
      _ ≤ (1500000 * Work.Spaces.Gam α θ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
      _ = 2250000000000 * (Work.Spaces.Gam α θ) ^ 2 := by ring
  -- ## 6. pass to the weighted estimate
  have hTγ : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hs_pos.le _
  have hexp : 2 * α / 3 + -(Work.Spaces.gam α) = -(1 - 17 * α / 30) := by
    rw [Work.Spaces.gam]
    ring
  have hprod : (Real.sin (2 * θ)) ^ (2 * α / 3) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      = (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)) := by
    rw [← Real.rpow_add hs_pos, hexp]
  calc (Work.Spaces.dthU^[4] (VfsA1 α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ (2250000000000 * (Work.Spaces.Gam α θ) ^ 2)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
        mul_le_mul_of_nonneg_right h4 hTγ
    _ = 2250000000000 * ((Work.Spaces.Gam α θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
    _ ≤ 2250000000000 * ((Real.sin (2 * θ)) ^ (2 * α / 3)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (Work.Coercivity.Gam_sq_le_sin_two α hα θ hθI) hTγ)
          (by norm_num)
    _ = 2250000000000 * (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)) := by rw [hprod]

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux
