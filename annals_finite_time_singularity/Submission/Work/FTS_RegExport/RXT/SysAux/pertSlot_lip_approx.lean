import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.RegExportIface.Defs
import Submission.Work.FTS_RegExport.RXT.Slots.v2_velPert
import Submission.Work.FTS.ClassC.A1
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS_RegExport.RXT.velVanish2
import Submission.Work.FTS_RegExport.RXT.Slots.v2_hkMem_pointwise_min
import Submission.Work.FTS.GalFields.RHS.SharpAux.Core
import Submission.Work.FTS.StrongEps.EComparison.Reduction

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.SysAux

theorem pertSlot_lip_approx {α Ce L : ℝ} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    {S : ℝ} {gn : ℕ → Work.FTS.Galerkin.Fam}
    (hClass : ∀ n, ∀ τ ∈ Set.Icc (0:ℝ) S,
      Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice (gn n) τ))
    (hLip : ∀ n, ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
      Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α)
        (Work.FTS.Galerkin.slice (gn n) τ - Work.FTS.Galerkin.slice (gn n) τ') ≤ L * |τ - τ'|) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (|Work.Construction.Rop (Work.FTS.Regularity.pExp α)
            (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice (gn n) τ)
              (E (Work.FTS.Galerkin.slice (gn n) τ))) z θ
          - Work.Construction.Rop (Work.FTS.Regularity.pExp α)
            (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice (gn n) τ')
              (E (Work.FTS.Galerkin.slice (gn n) τ'))) z θ| ≤ K * |τ - τ'|) ∧
      (|Work.Construction.Vop
            (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice (gn n) τ)
              (E (Work.FTS.Galerkin.slice (gn n) τ))) z θ
          - Work.Construction.Vop
            (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice (gn n) τ')
              (E (Work.FTS.Galerkin.slice (gn n) τ'))) z θ| ≤ K * |τ - τ'|) ∧
      (|Work.Construction.Uop (Work.FTS.Regularity.pExp α)
            (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice (gn n) τ)
              (E (Work.FTS.Galerkin.slice (gn n) τ))) z θ / Real.sin (2 * θ)
          - Work.Construction.Uop (Work.FTS.Regularity.pExp α)
            (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice (gn n) τ')
              (E (Work.FTS.Galerkin.slice (gn n) τ'))) z θ / Real.sin (2 * θ)| ≤ K * |τ - τ'|) := by
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  obtain ⟨Ct, hCt0, hCt⟩ := Work.FTS_RegExport.RXT.v2_hkMem_pointwise_min hαG hαG1
  refine ⟨Ct * max Ce 0 * max L 0,
    mul_nonneg (mul_nonneg hCt0 (le_max_right _ _)) (le_max_right _ _), ?_⟩
  intro n τ hτ τ' hτ' z θ hz hθ hθ2
  have hCu : Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α)
      (Work.FTS.Galerkin.slice (gn n) τ) := hClass n τ hτ
  have hCv : Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α)
      (Work.FTS.Galerkin.slice (gn n) τ') := hClass n τ' hτ'
  set Δ : Work.FTS.Galerkin.Fn :=
    fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ - Work.FTS.Galerkin.slice (gn n) τ' z θ
    with hΔ
  have hCΔ : Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) Δ :=
    Work.FTS.StrongEps.EComparison.classC_sub hCu hCv
  set Xu : Work.FTS.Galerkin.Fn := Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
    (Work.FTS.Galerkin.slice (gn n) τ) (E (Work.FTS.Galerkin.slice (gn n) τ)) with hXu
  set Xv : Work.FTS.Galerkin.Fn := Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
    (Work.FTS.Galerkin.slice (gn n) τ') (E (Work.FTS.Galerkin.slice (gn n) τ')) with hXv
  set Xd : Work.FTS.Galerkin.Fn := Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
    Δ (E Δ) with hXd
  obtain ⟨hGo, _hK6⟩ := hEll Δ hCΔ
  have hSu : Work.FTS.EllipticEst.SmoothOpen Xu :=
    Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil hαG
      (hEll (Work.FTS.Galerkin.slice (gn n) τ) hCu).1
  have hSv : Work.FTS.EllipticEst.SmoothOpen Xv :=
    Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil hαG
      (hEll (Work.FTS.Galerkin.slice (gn n) τ') hCv).1
  have hSd : Work.FTS.EllipticEst.SmoothOpen Xd :=
    Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil hαG hGo
  have hXn0 : 0 ≤ Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) Δ :=
    Work.Spaces.HkNorm_nonneg _ _ _
  have hXnΔ : Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) Δ ≤ max L 0 * |τ - τ'| := by
    refine le_trans (hLip n τ hτ τ' hτ') ?_
    exact mul_le_mul_of_nonneg_right (le_max_left L 0) (abs_nonneg _)
  -- ## the pointwise telescoping of the residues
  have hpot : ∀ z' θ' : ℝ, 0 < z' → Xu z' θ' = Xd z' θ' + Xv z' θ' := by
    intro z' θ' hz'
    have hL : Work.Construction.L12 Δ z'
        = Work.Construction.L12 (Work.FTS.Galerkin.slice (gn n) τ) z'
          - Work.Construction.L12 (Work.FTS.Galerkin.slice (gn n) τ') z' :=
      Work.FTS.StrongEps.EComparison.L12_sub_HkMem hCu.reg hCv.reg
        (Work.FTS.ClassC.classC_hkMem_four hCu) (Work.FTS.ClassC.classC_hkMem_four hCv)
        z' hz'.le
    have hE' : E Δ z' θ'
        = E (Work.FTS.Galerkin.slice (gn n) τ) z' θ'
          - E (Work.FTS.Galerkin.slice (gn n) τ') z' θ' := by
      have h2 : E Δ = E (Work.FTS.Galerkin.slice (gn n) τ)
          - E (Work.FTS.Galerkin.slice (gn n) τ') := by
        rw [hΔ]
        exact map_sub E _ _
      exact congrFun (congrFun h2 z') θ'
    rw [hXu, hXd, hXv]
    unfold Work.Construction.PhiTil Work.Construction.Theta
    rw [hL, hE']
    ring
  -- ## additivity of the three slots
  have hRadd : Work.Construction.Rop (Work.FTS.Regularity.pExp α) Xu z θ
      = Work.Construction.Rop (Work.FTS.Regularity.pExp α) Xd z θ
        + Work.Construction.Rop (Work.FTS.Regularity.pExp α) Xv z θ := by
    calc Work.Construction.Rop (Work.FTS.Regularity.pExp α) Xu z θ
        = Work.Construction.Rop (Work.FTS.Regularity.pExp α)
            (fun z θ => Xd z θ + Xv z θ) z θ :=
          Work.FTS.GalFields.RHS.Sharp.Rop_congr_Q0
            (f := Xu) (g := fun z θ => Xd z θ + Xv z θ)
            (fun z' θ' hz' _ _ => hpot z' θ' hz') z θ hz hθ hθ2
      _ = Work.Construction.Rop (Work.FTS.Regularity.pExp α) Xd z θ
            + Work.Construction.Rop (Work.FTS.Regularity.pExp α) Xv z θ :=
          Work.FTS.GalFields.RHS.Sharp.Rop_add_Q0 hSd hSv z θ hz hθ hθ2
  have hVadd : Work.Construction.Vop Xu z θ
      = Work.Construction.Vop Xd z θ + Work.Construction.Vop Xv z θ := by
    calc Work.Construction.Vop Xu z θ
        = Work.Construction.Vop (fun z θ => Xd z θ + Xv z θ) z θ :=
          Work.FTS.GalFields.RHS.Sharp.Vop_congr_Q0
            (f := Xu) (g := fun z θ => Xd z θ + Xv z θ)
            (fun z' θ' hz' _ _ => hpot z' θ' hz') z θ hz hθ hθ2
      _ = Work.Construction.Vop Xd z θ + Work.Construction.Vop Xv z θ :=
          Work.FTS.GalFields.RHS.Sharp.Vop_add_Q0 hSd hSv z θ hz hθ hθ2
  have hUadd : Work.Construction.Uop (Work.FTS.Regularity.pExp α) Xu z θ
        / Work.Construction.s2 θ
      = Work.Construction.Uop (Work.FTS.Regularity.pExp α) Xd z θ / Work.Construction.s2 θ
        + Work.Construction.Uop (Work.FTS.Regularity.pExp α) Xv z θ / Work.Construction.s2 θ := by
    have hc : Work.Construction.Uop (Work.FTS.Regularity.pExp α) Xu z θ
        = Work.Construction.Uop (Work.FTS.Regularity.pExp α)
            (fun z θ => Xd z θ + Xv z θ) z θ :=
      Work.FTS.GalFields.RHS.Sharp.Uop_congr_Q0
        (f := Xu) (g := fun z θ => Xd z θ + Xv z θ)
        (fun z' θ' hz' _ _ => hpot z' θ' hz') z θ hz hθ hθ2
    rw [hc, Work.FTS.GalFields.RHS.Sharp.Uop_add_Q0 hSd hSv z θ hz hθ hθ2]
    ring
  -- ## the pointwise bounds of the difference slots
  have hnormR : Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4
      (Work.Construction.Rop (Work.FTS.Regularity.pExp α) Xd)
      ≤ max Ce 0 * Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) Δ :=
    le_trans hGo.R.2 (mul_le_mul_of_nonneg_right (le_max_left Ce 0) hXn0)
  have hnormV : Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4
      (Work.Construction.Vop Xd)
      ≤ max Ce 0 * Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) Δ :=
    le_trans hGo.V.2 (mul_le_mul_of_nonneg_right (le_max_left Ce 0) hXn0)
  have hnormU : Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4
      (fun z θ => Work.Construction.Uop (Work.FTS.Regularity.pExp α) Xd z θ
        / Work.Construction.s2 θ)
      ≤ max Ce 0 * Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) Δ :=
    le_trans hGo.U.2 (mul_le_mul_of_nonneg_right (le_max_left Ce 0) hXn0)
  -- the abstract arithmetic package: from the trade-off bound and the `τ`-modulus
  have key : ∀ (Q : ℝ → ℝ → ℝ),
      ContDiffOn ℝ 4 (Function.uncurry Q) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.HkMem (Work.FTS.Regularity.pExp α) 4 Q →
      Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4 Q
        ≤ max Ce 0 * Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) Δ →
      |Q z θ| ≤ Ct * max Ce 0 * max L 0 * |τ - τ'| := by
    intro Q hcd hmem hMQ
    have h1 : |Q z θ| ≤ Ct * min z 1 * Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4 Q :=
      hCt Q hcd hmem 0 0 (by norm_num) z θ hz hθ hθ2
    have h2 : Ct * min z 1 * Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4 Q
        ≤ Ct * (max Ce 0 * (max L 0 * |τ - τ'|)) := by
      have hN0 : 0 ≤ Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4 Q :=
        Work.Spaces.HkNorm_nonneg _ _ _
      have hstep : Ct * min z 1 ≤ Ct * 1 := mul_le_mul_of_nonneg_left (min_le_right z 1) hCt0
      calc Ct * min z 1 * Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4 Q
          ≤ (Ct * 1) * Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4 Q :=
            mul_le_mul_of_nonneg_right hstep hN0
        _ ≤ Ct * (max Ce 0 * Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) Δ) := by
            rw [mul_one]
            exact mul_le_mul_of_nonneg_left hMQ hCt0
        _ ≤ Ct * (max Ce 0 * (max L 0 * |τ - τ'|)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hXnΔ (le_max_right Ce 0)) hCt0
    calc |Q z θ| ≤ Ct * min z 1 * Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4 Q := h1
      _ ≤ Ct * (max Ce 0 * (max L 0 * |τ - τ'|)) := h2
      _ = Ct * max Ce 0 * max L 0 * |τ - τ'| := by ring
  have hRb : |Work.Construction.Rop (Work.FTS.Regularity.pExp α) Xd z θ|
      ≤ Ct * max Ce 0 * max L 0 * |τ - τ'| :=
    key _ (hGo.R.1.1.forall 4) hGo.R.1.2 hnormR
  have hVb : |Work.Construction.Vop Xd z θ|
      ≤ Ct * max Ce 0 * max L 0 * |τ - τ'| :=
    key _ (hGo.V.1.1.forall 4) hGo.V.1.2 hnormV
  have hUb : |Work.Construction.Uop (Work.FTS.Regularity.pExp α) Xd z θ
        / Work.Construction.s2 θ| ≤ Ct * max Ce 0 * max L 0 * |τ - τ'| :=
    key _ (hGo.U.1.1.forall 4) hGo.U.1.2 hnormU
  refine ⟨?_, ?_, ?_⟩
  · calc |Work.Construction.Rop (Work.FTS.Regularity.pExp α) Xu z θ
          - Work.Construction.Rop (Work.FTS.Regularity.pExp α) Xv z θ|
        = |Work.Construction.Rop (Work.FTS.Regularity.pExp α) Xd z θ| := by
          rw [hRadd, add_sub_cancel_right]
      _ ≤ Ct * max Ce 0 * max L 0 * |τ - τ'| := hRb
  · calc |Work.Construction.Vop Xu z θ - Work.Construction.Vop Xv z θ|
        = |Work.Construction.Vop Xd z θ| := by rw [hVadd, add_sub_cancel_right]
      _ ≤ Ct * max Ce 0 * max L 0 * |τ - τ'| := hVb
  · calc |Work.Construction.Uop (Work.FTS.Regularity.pExp α) Xu z θ
            / Work.Construction.s2 θ
          - Work.Construction.Uop (Work.FTS.Regularity.pExp α) Xv z θ
            / Work.Construction.s2 θ|
        = |Work.Construction.Uop (Work.FTS.Regularity.pExp α) Xd z θ
            / Work.Construction.s2 θ| := by rw [hUadd, add_sub_cancel_right]
      _ ≤ Ct * max Ce 0 * max L 0 * |τ - τ'| := hUb

end Work.FTS_RegExport.RXT.SysAux
