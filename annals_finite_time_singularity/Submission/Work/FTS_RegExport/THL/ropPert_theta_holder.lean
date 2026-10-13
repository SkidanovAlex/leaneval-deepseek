import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.RegExportIface.Defs
import Submission.Work.FTS_RegExport.THL.theta_holder_of_HkMem
import Submission.Work.FTS_RegExport.RXT.SysAux.pertSlot_tendsto

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.THL

theorem ropPert_theta_holder {α Ce C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    {g : Work.FTS.Galerkin.Fam} (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g) :
    ∀ S > 0, ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ, 0 < z →
      ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2), ∀ θ' ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
        |Work.Construction.Rop (Work.FTS.Regularity.pExp α)
            (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ))) z θ
          - Work.Construction.Rop (Work.FTS.Regularity.pExp α)
            (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ))) z θ'|
          ≤ M * min z 1 * |θ - θ'| ^ (Work.FTS.Regularity.pExp α / 20) := by
  intro S hS
  -- the exponent data for the `ℋ⁴ ⟹` Hölder leaf `theta_holder_of_HkMem`
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  obtain ⟨C, hC0, hA3⟩ := theta_holder_of_HkMem hαG hαG1
  -- the class-`C` approximants of the solution on `[0,S]`
  obtain ⟨gn, B, L, hApprox, _hLip, hJet, _hμ⟩ := hOK.2 S hS
  refine ⟨C * (max Ce 0 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2)), ?_, ?_⟩
  · exact mul_nonneg hC0 (mul_nonneg (le_max_right Ce 0)
      (mul_nonneg (le_max_right C₀ 0) (sq_nonneg _)))
  · intro τ hτ z hz θ hθ θ' hθ'
    -- the perturbation slot of the approximants converges to the one of the limit slice
    have htend := Work.FTS_RegExport.RXT.SysAux.pertSlot_tendsto (α := α) (Ce := Ce) (C₀ := C₀)
      (Φs := Φs) (E := E) (g := g) hα hα13 hEll hEL3 hOK hS (gn := gn) (B := B) hApprox hJet hτ
    have hconvθ := (htend z θ hz hθ.1 hθ.2).1
    have hconvθ' := (htend z θ' hz hθ'.1 hθ'.2).1
    refine le_of_tendsto' ((hconvθ.sub hconvθ').abs) (fun n => ?_)
    -- the per-approximant estimate: `EllPkgGo` puts the slot in `ℋ⁴` with a bounded norm
    obtain ⟨hCn, hXn, _⟩ := hApprox n τ hτ
    obtain ⟨hGo, _⟩ := hEll (Work.FTS.Galerkin.slice (gn n) τ) hCn
    have hR4 : ContDiffOn ℝ 4 (Function.uncurry (Work.Construction.Rop (Work.FTS.Regularity.pExp α)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice (gn n) τ)
          (E (Work.FTS.Galerkin.slice (gn n) τ))))) Work.FTS.EllipticEst.Q0 :=
      Work.FTS.EllipticEst.SmoothOpen.forall hGo.R.1.1 4
    have hRmem : Work.Spaces.HkMem (Work.FTS.Regularity.pExp α) 4
        (Work.Construction.Rop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
            (Work.FTS.Galerkin.slice (gn n) τ) (E (Work.FTS.Galerkin.slice (gn n) τ)))) :=
      hGo.R.1.2
    have hXn0 : 0 ≤ Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α)
        (Work.FTS.Galerkin.slice (gn n) τ) := Work.Spaces.HkNorm_nonneg _ _ _
    have hnorm : Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4
        (Work.Construction.Rop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
            (Work.FTS.Galerkin.slice (gn n) τ) (E (Work.FTS.Galerkin.slice (gn n) τ))))
        ≤ max Ce 0 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) := by
      refine le_trans hGo.R.2 (le_trans (mul_le_mul_of_nonneg_right (le_max_left Ce 0) hXn0) ?_)
      exact mul_le_mul_of_nonneg_left
        (le_trans hXn (mul_le_mul_of_nonneg_right (le_max_left C₀ 0)
          (sq_nonneg (Work.FTS.Regularity.pExp α)))) (le_max_right Ce 0)
    have h3 := hA3 (Work.Construction.Rop (Work.FTS.Regularity.pExp α)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice (gn n) τ)
          (E (Work.FTS.Galerkin.slice (gn n) τ)))) hR4 hRmem z hz θ hθ θ' hθ'
    rw [Work.Spaces.gam_sub_one (Work.FTS.Regularity.pExp α),
      show Work.FTS.Regularity.pExp α / 10 / 2 = Work.FTS.Regularity.pExp α / 20 by ring] at h3
    refine le_trans h3 ?_
    have hm0 : 0 ≤ min z 1 := le_min hz.le zero_le_one
    have hp0 : (0 : ℝ) ≤ |θ - θ'| ^ (Work.FTS.Regularity.pExp α / 20) :=
      Real.rpow_nonneg (abs_nonneg _) _
    refine le_trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hnorm (mul_nonneg hC0 hm0)) hp0) (le_of_eq ?_)
    ring

end Work.FTS_RegExport.THL
