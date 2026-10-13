/-
# `SharpAux/Identity` — the master pointwise identity for the difference of `N`

`Work.FTS.GalFields.RHS.Sharp.N_diff_eq_sum`: on the open quadrant `Qd`,

`N α (F_*+g) (Φ_s+EllSol g) - N α (F_*+g') (Φ_s+EllSol g')`

equals the sum of the twenty monomials `TRA … TED` of `SharpAux/Defs.lean`.  The proof is a
telescoping of each of the five summands of `N`, using `Z = Zs + Zg`, `Z' = Zs + Zg'`,
`Zg = Δ + Zg'`, `FK(F) = FK(F') + FK(h)`, `D_θF = D_θF' + D_θh`, `D_zF = D_zF' + D_zh` and
`F = F' + h` on `Qd`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.GalFields.RHS.SharpAux.Core

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.RHS.Sharp

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000
set_option pp.deepTerms true

theorem N_diff_eq_sum {α α₂ Ci Ce Cs : ℝ} {Φs : Fn} {EllSol : Fn → Fn}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hell : ∀ g : Fn, Work.FTS.Nonlin.GalClass α g →
      Work.FTS.VocabO.EllPkgGo α Ce g (EllSol g))
    (hEllSub : ∀ g g' : Fn,
      EllSol (fun z θ => g z θ - g' z θ) = fun z θ => EllSol g z θ - EllSol g' z θ)
    (hα : 0 < α) (hαα₂ : α ≤ α₂) {g g' h : Fn}
    (hg : Work.FTS.Nonlin.GalClass α g) (hg' : Work.FTS.Nonlin.GalClass α g')
    (hh : Work.FTS.Nonlin.GalClass α h) (hh_eq : ∀ z θ : ℝ, h z θ = g z θ - g' z θ)
    (hα1 : α ≤ 1) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      (Work.Construction.N α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + EllSol g z θ) z θ
        - Work.Construction.N α (Work.Construction.Ftot α g')
          (fun z θ => Φs z θ + EllSol g' z θ) z θ)
      = (TRA α Φs h + TRB α EllSol g' h + TRC α EllSol h + TRD α EllSol g h
        + TUA α Φs h + TUB α EllSol g' h + TUC α EllSol h + TUD α EllSol g h
        + TVA α Φs h + TVB α EllSol g' h + TVC α EllSol h + TVD α EllSol g h
        + TDA α h + TDB α g' h + TDC α h + TDD α g h
        + TEA α h + TEB α g' h + TEC α h + TED α g h) z θ := by
  intro z θ hq
  obtain ⟨hz, hθ1, hθ2⟩ : z ∈ Set.Ioi (0 : ℝ) ∧ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    simpa only [Work.Construction.Qd, Set.mem_prod] using hq
  have hzle : (0 : ℝ) ≤ z := le_of_lt hz
  have hs2ne : Real.sin (2 * θ) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
  -- ## smoothness of the data
  have hFstarS : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  have hgS : Work.FTS.EllipticEst.SmoothOpen g :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad hg.reg.1
  have hg'S : Work.FTS.EllipticEst.SmoothOpen g' :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad hg'.reg.1
  have hhS : Work.FTS.EllipticEst.SmoothOpen h :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad hh.reg.1
  have hZs : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) :=
    smoothOpen_PhiTil_star hα hα1 hstar
  have hZg : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.PhiTil α g (EllSol g)) := smoothOpen_PhiTil hα (hell g hg)
  have hZg' : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.PhiTil α g' (EllSol g')) := smoothOpen_PhiTil hα (hell g' hg')
  have hDl : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.PhiTil α h (EllSol h)) := smoothOpen_PhiTil hα (hell h hh)
  -- ## honesty of the data
  have hg4 : Work.Spaces.HkMem α 4 g :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hgS hg.reg.2.1
  have hg'4 : Work.Spaces.HkMem α 4 g' :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hg'S hg'.reg.2.1
  have hh4 : Work.Spaces.HkMem α 4 h :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hhS hh.reg.2.1
  -- ## the potential identities on `Q0`
  have hpot1 : ∀ z' θ' : ℝ, 0 < z' →
      Work.Construction.PhiTil α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + EllSol g z θ) z' θ'
        = Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z' θ'
          + Work.Construction.PhiTil α g (EllSol g) z' θ' := by
    intro z' θ' hz'
    have hL := (Work.FTS.Nonlinear.Pieces.L12FK_add_ge0 (α := α) (g := g) hα hα1 hg).1 z'
      (le_of_lt hz')
    simp only [Work.Construction.PhiTil, Work.Construction.Theta]
    rw [hL]
    ring
  have hpot2 : ∀ z' θ' : ℝ, 0 < z' →
      Work.Construction.PhiTil α (Work.Construction.Ftot α g')
          (fun z θ => Φs z θ + EllSol g' z θ) z' θ'
        = Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z' θ'
          + Work.Construction.PhiTil α g' (EllSol g') z' θ' := by
    intro z' θ' hz'
    have hL := (Work.FTS.Nonlinear.Pieces.L12FK_add_ge0 (α := α) (g := g') hα hα1 hg').1 z'
      (le_of_lt hz')
    simp only [Work.Construction.PhiTil, Work.Construction.Theta]
    rw [hL]
    ring
  have hpot3 : ∀ z' θ' : ℝ, 0 < z' →
      Work.Construction.PhiTil α g (EllSol g) z' θ'
        = Work.Construction.PhiTil α h (EllSol h) z' θ'
          + Work.Construction.PhiTil α g' (EllSol g') z' θ' := by
    intro z' θ' hz'
    have hL : Work.Construction.L12 g z' = Work.Construction.L12 h z' +
        Work.Construction.L12 g' z' :=
      L12_sub_ge0 hgS hg'S hhS hg4 hg'4 hh4 hh_eq hz'.le
    have hEls : EllSol h z' θ' = EllSol g z' θ' - EllSol g' z' θ' := by
      have hfun : h = (fun z θ => g z θ - g' z θ) := by
        funext z θ
        exact hh_eq z θ
      rw [hfun]
      exact congrFun (congrFun (hEllSub g g') z') θ'
    simp only [Work.Construction.PhiTil, Work.Construction.Theta]
    rw [hL, hEls]
    ring
  -- ## additivity of `ℛ`, `U`, `V` on the potentials
  have r1 : Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + EllSol g z θ)) z θ
      = Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Rop α (Work.Construction.PhiTil α g (EllSol g)) z θ := by
    calc Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + EllSol g z θ)) z θ
        = Work.Construction.Rop α (fun z θ =>
            Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
              + Work.Construction.PhiTil α g (EllSol g) z θ) z θ :=
          Rop_congr_Q0 (f := Work.Construction.PhiTil α (Work.Construction.Ftot α g)
              (fun z θ => Φs z θ + EllSol g z θ))
            (g := fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
              + Work.Construction.PhiTil α g (EllSol g) z θ)
            (fun z' θ' hz' _ _ => hpot1 z' θ' hz') z θ hz hθ1 hθ2
      _ = Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Rop α (Work.Construction.PhiTil α g (EllSol g)) z θ :=
          Rop_add_Q0 hZs hZg z θ hz hθ1 hθ2
  have r2 : Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Ftot α g')
        (fun z θ => Φs z θ + EllSol g' z θ)) z θ
      = Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Rop α (Work.Construction.PhiTil α g' (EllSol g')) z θ := by
    calc Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Ftot α g')
          (fun z θ => Φs z θ + EllSol g' z θ)) z θ
        = Work.Construction.Rop α (fun z θ =>
            Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
              + Work.Construction.PhiTil α g' (EllSol g') z θ) z θ :=
          Rop_congr_Q0 (f := Work.Construction.PhiTil α (Work.Construction.Ftot α g')
              (fun z θ => Φs z θ + EllSol g' z θ))
            (g := fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
              + Work.Construction.PhiTil α g' (EllSol g') z θ)
            (fun z' θ' hz' _ _ => hpot2 z' θ' hz') z θ hz hθ1 hθ2
      _ = Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Rop α (Work.Construction.PhiTil α g' (EllSol g')) z θ :=
          Rop_add_Q0 hZs hZg' z θ hz hθ1 hθ2
  have r3 : Work.Construction.Rop α (Work.Construction.PhiTil α g (EllSol g)) z θ
      = Work.Construction.Rop α (Work.Construction.PhiTil α h (EllSol h)) z θ
        + Work.Construction.Rop α (Work.Construction.PhiTil α g' (EllSol g')) z θ := by
    calc Work.Construction.Rop α (Work.Construction.PhiTil α g (EllSol g)) z θ
        = Work.Construction.Rop α (fun z θ =>
            Work.Construction.PhiTil α h (EllSol h) z θ
              + Work.Construction.PhiTil α g' (EllSol g') z θ) z θ :=
          Rop_congr_Q0 (f := Work.Construction.PhiTil α g (EllSol g))
            (g := fun z θ => Work.Construction.PhiTil α h (EllSol h) z θ
              + Work.Construction.PhiTil α g' (EllSol g') z θ)
            (fun z' θ' hz' _ _ => hpot3 z' θ' hz') z θ hz hθ1 hθ2
      _ = Work.Construction.Rop α (Work.Construction.PhiTil α h (EllSol h)) z θ
        + Work.Construction.Rop α (Work.Construction.PhiTil α g' (EllSol g')) z θ :=
          Rop_add_Q0 hDl hZg' z θ hz hθ1 hθ2
  have h1z : (1 : ℝ) + z ≠ 0 := by positivity
  have hz0 : z ≠ 0 := ne_of_gt hz
  have r4 : Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
      = (z / (1 + z)) * StarH α Φs z θ := by
    have hfac : (z / (1 + z)) * ((z + 1) / z) = 1 := by field_simp <;> ring
    simp only [StarH, Work.FTS.Nonlin.PhiTs]
    rw [show (z / (1 + z)) * ((z + 1) / z
          * Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ)
        = ((z / (1 + z)) * ((z + 1) / z))
          * Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        from by ring, hfac, one_mul]
  have u1 : Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + EllSol g z θ)) z θ
      = Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Uop α (Work.Construction.PhiTil α g (EllSol g)) z θ := by
    calc Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + EllSol g z θ)) z θ
        = Work.Construction.Uop α (fun z θ =>
            Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
              + Work.Construction.PhiTil α g (EllSol g) z θ) z θ :=
          Uop_congr_Q0 (f := Work.Construction.PhiTil α (Work.Construction.Ftot α g)
              (fun z θ => Φs z θ + EllSol g z θ))
            (g := fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
              + Work.Construction.PhiTil α g (EllSol g) z θ)
            (fun z' θ' hz' _ _ => hpot1 z' θ' hz') z θ hz hθ1 hθ2
      _ = Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Uop α (Work.Construction.PhiTil α g (EllSol g)) z θ :=
          Uop_add_Q0 hZs hZg z θ hz hθ1 hθ2
  have u2 : Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Ftot α g')
        (fun z θ => Φs z θ + EllSol g' z θ)) z θ
      = Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Uop α (Work.Construction.PhiTil α g' (EllSol g')) z θ := by
    calc Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Ftot α g')
          (fun z θ => Φs z θ + EllSol g' z θ)) z θ
        = Work.Construction.Uop α (fun z θ =>
            Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
              + Work.Construction.PhiTil α g' (EllSol g') z θ) z θ :=
          Uop_congr_Q0 (f := Work.Construction.PhiTil α (Work.Construction.Ftot α g')
              (fun z θ => Φs z θ + EllSol g' z θ))
            (g := fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
              + Work.Construction.PhiTil α g' (EllSol g') z θ)
            (fun z' θ' hz' _ _ => hpot2 z' θ' hz') z θ hz hθ1 hθ2
      _ = Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Uop α (Work.Construction.PhiTil α g' (EllSol g')) z θ :=
          Uop_add_Q0 hZs hZg' z θ hz hθ1 hθ2
  have u3 : Work.Construction.Uop α (Work.Construction.PhiTil α g (EllSol g)) z θ
      = Work.Construction.Uop α (Work.Construction.PhiTil α h (EllSol h)) z θ
        + Work.Construction.Uop α (Work.Construction.PhiTil α g' (EllSol g')) z θ := by
    calc Work.Construction.Uop α (Work.Construction.PhiTil α g (EllSol g)) z θ
        = Work.Construction.Uop α (fun z θ =>
            Work.Construction.PhiTil α h (EllSol h) z θ
              + Work.Construction.PhiTil α g' (EllSol g') z θ) z θ :=
          Uop_congr_Q0 (f := Work.Construction.PhiTil α g (EllSol g))
            (g := fun z θ => Work.Construction.PhiTil α h (EllSol h) z θ
              + Work.Construction.PhiTil α g' (EllSol g') z θ)
            (fun z' θ' hz' _ _ => hpot3 z' θ' hz') z θ hz hθ1 hθ2
      _ = Work.Construction.Uop α (Work.Construction.PhiTil α h (EllSol h)) z θ
        + Work.Construction.Uop α (Work.Construction.PhiTil α g' (EllSol g')) z θ :=
          Uop_add_Q0 hDl hZg' z θ hz hθ1 hθ2
  have hcancel : ∀ (X : ℝ), Real.sin (2 * θ) * (X / Real.sin (2 * θ)) = X := by
    intro X
    rw [div_eq_mul_inv, mul_comm (Real.sin (2 * θ)) (X * (Real.sin (2 * θ))⁻¹), mul_assoc,
      inv_mul_cancel₀ hs2ne, mul_one]
  have u4 : Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
      = Real.sin (2 * θ) * UsPhi α Φs z θ := by
    have hc := hcancel (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
    simp only [UsPhi, Work.Construction.s2, Work.FTS.Nonlin.PhiTs] at hc ⊢
    exact hc.symm
  have u5 : Work.Construction.Uop α (Work.Construction.PhiTil α g' (EllSol g')) z θ
      = Real.sin (2 * θ)
        * (Work.Construction.Uop α (Work.Construction.PhiTil α g' (EllSol g')) z θ
          / Real.sin (2 * θ)) :=
    (hcancel (Work.Construction.Uop α (Work.Construction.PhiTil α g' (EllSol g')) z θ)).symm
  have u6 : Work.Construction.Uop α (Work.Construction.PhiTil α h (EllSol h)) z θ
      = Real.sin (2 * θ)
        * (Work.Construction.Uop α (Work.Construction.PhiTil α h (EllSol h)) z θ
          / Real.sin (2 * θ)) :=
    (hcancel (Work.Construction.Uop α (Work.Construction.PhiTil α h (EllSol h)) z θ)).symm
  have v1 : Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + EllSol g z θ)) z θ
      = Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Vop (Work.Construction.PhiTil α g (EllSol g)) z θ := by
    calc Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + EllSol g z θ)) z θ
        = Work.Construction.Vop (fun z θ =>
            Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
              + Work.Construction.PhiTil α g (EllSol g) z θ) z θ :=
          Vop_congr_Q0 (f := Work.Construction.PhiTil α (Work.Construction.Ftot α g)
              (fun z θ => Φs z θ + EllSol g z θ))
            (g := fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
              + Work.Construction.PhiTil α g (EllSol g) z θ)
            (fun z' θ' hz' _ _ => hpot1 z' θ' hz') z θ hz hθ1 hθ2
      _ = Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Vop (Work.Construction.PhiTil α g (EllSol g)) z θ :=
          Vop_add_Q0 hZs hZg z θ hz hθ1 hθ2
  have v2 : Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Ftot α g')
        (fun z θ => Φs z θ + EllSol g' z θ)) z θ
      = Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Vop (Work.Construction.PhiTil α g' (EllSol g')) z θ := by
    calc Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Ftot α g')
          (fun z θ => Φs z θ + EllSol g' z θ)) z θ
        = Work.Construction.Vop (fun z θ =>
            Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
              + Work.Construction.PhiTil α g' (EllSol g') z θ) z θ :=
          Vop_congr_Q0 (f := Work.Construction.PhiTil α (Work.Construction.Ftot α g')
              (fun z θ => Φs z θ + EllSol g' z θ))
            (g := fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
              + Work.Construction.PhiTil α g' (EllSol g') z θ)
            (fun z' θ' hz' _ _ => hpot2 z' θ' hz') z θ hz hθ1 hθ2
      _ = Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Vop (Work.Construction.PhiTil α g' (EllSol g')) z θ :=
          Vop_add_Q0 hZs hZg' z θ hz hθ1 hθ2
  have v3 : Work.Construction.Vop (Work.Construction.PhiTil α g (EllSol g)) z θ
      = Work.Construction.Vop (Work.Construction.PhiTil α h (EllSol h)) z θ
        + Work.Construction.Vop (Work.Construction.PhiTil α g' (EllSol g')) z θ := by
    calc Work.Construction.Vop (Work.Construction.PhiTil α g (EllSol g)) z θ
        = Work.Construction.Vop (fun z θ =>
            Work.Construction.PhiTil α h (EllSol h) z θ
              + Work.Construction.PhiTil α g' (EllSol g') z θ) z θ :=
          Vop_congr_Q0 (f := Work.Construction.PhiTil α g (EllSol g))
            (g := fun z θ => Work.Construction.PhiTil α h (EllSol h) z θ
              + Work.Construction.PhiTil α g' (EllSol g') z θ)
            (fun z' θ' hz' _ _ => hpot3 z' θ' hz') z θ hz hθ1 hθ2
      _ = Work.Construction.Vop (Work.Construction.PhiTil α h (EllSol h)) z θ
        + Work.Construction.Vop (Work.Construction.PhiTil α g' (EllSol g')) z θ :=
          Vop_add_Q0 hDl hZg' z θ hz hθ1 hθ2
  -- ## the derivative, moment and value identities
  have hg_eq : g = fun z θ => g' z θ + h z θ := by
    funext z' θ'
    have := hh_eq z' θ'
    linarith
  have d1 : Work.Spaces.pz (Work.Construction.Ftot α g) z θ
      = Work.Spaces.pz (Work.Construction.Fstar α) z θ + Work.Spaces.pz g z θ :=
    pz_add_Q0 hFstarS hgS z θ hz hθ1 hθ2
  have d2 : Work.Spaces.pz (Work.Construction.Ftot α g') z θ
      = Work.Spaces.pz (Work.Construction.Fstar α) z θ + Work.Spaces.pz g' z θ :=
    pz_add_Q0 hFstarS hg'S z θ hz hθ1 hθ2
  have d3 : Work.Spaces.pz g z θ = Work.Spaces.pz g' z θ + Work.Spaces.pz h z θ := by
    rw [hg_eq]
    exact pz_add_Q0 hg'S hhS z θ hz hθ1 hθ2
  have d4 : Work.Spaces.pth (Work.Construction.Ftot α g) z θ
      = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth g z θ :=
    pth_add_Q0 hFstarS hgS z θ hz hθ1 hθ2
  have d5 : Work.Spaces.pth (Work.Construction.Ftot α g') z θ
      = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth g' z θ :=
    pth_add_Q0 hFstarS hg'S z θ hz hθ1 hθ2
  have d6 : Work.Spaces.pth g z θ = Work.Spaces.pth g' z θ + Work.Spaces.pth h z θ := by
    rw [hg_eq]
    exact pth_add_Q0 hg'S hhS z θ hz hθ1 hθ2
  have k1 : Work.Construction.FK (Work.Construction.Ftot α g) z
      = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK g z :=
    (Work.FTS.Nonlinear.Pieces.L12FK_add_ge0 (α := α) (g := g) hα hα1 hg).2 z hzle
  have k2 : Work.Construction.FK (Work.Construction.Ftot α g') z
      = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK g' z :=
    (Work.FTS.Nonlinear.Pieces.L12FK_add_ge0 (α := α) (g := g') hα hα1 hg').2 z hzle
  have k3 : Work.Construction.FK g z
      = Work.Construction.FK g' z + Work.Construction.FK h z :=
    (FK_sub hgS hg'S hhS hg4 hg'4 hh4 hh_eq (z := z) hz).trans (by ring)
  have k4 : Work.Construction.FK (Work.Construction.Fstar α) z = Fkstar α z θ := by
    simp only [Fkstar, Work.Spaces.hKer_apply, Work.FTS.Nonlinear.FstarPkg.FK_Fstar hα hα1]
    ring
  have f1 : Work.Construction.Ftot α g z θ
      = Work.Construction.Fstar α z θ + g z θ := by
    simp only [Work.Construction.Ftot]
  have f2 : Work.Construction.Ftot α g' z θ
      = Work.Construction.Fstar α z θ + g' z θ := by
    simp only [Work.Construction.Ftot]
  -- ## the `U`-terms in undivided form (the `sin 2θ` denominator cancels)
  have hTUAund : TUA α Φs h z θ
      = (-2) * (Work.Construction.Uop α
          (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        * Work.Spaces.pth h z θ) := by
    simp only [TUA, UsPhi, Work.FTS.Nonlin.PhiTs, Work.Spaces.Dth, Work.Construction.s2]
    field_simp <;> ring
  have hTUBund : TUB α EllSol g' h z θ
      = (-2) * (Work.Construction.Uop α
          (Work.Construction.PhiTil α g' (EllSol g')) z θ
        * Work.Spaces.pth h z θ) := by
    simp only [TUB, Zgof, Work.Spaces.Dth, Work.Construction.s2]
    field_simp <;> ring
  have hTUCund : TUC α EllSol h z θ
      = (-2) * (Work.Spaces.pth (Work.Construction.Fstar α) z θ
        * Work.Construction.Uop α (Work.Construction.PhiTil α h (EllSol h)) z θ) := by
    simp only [TUC, Dof, DthFstar, Work.Spaces.Dth, Work.Construction.s2]
    field_simp <;> ring
  have hTUDund : TUD α EllSol g h z θ
      = (-2) * (Work.Construction.Uop α
          (Work.Construction.PhiTil α h (EllSol h)) z θ
        * Work.Spaces.pth g z θ) := by
    simp only [TUD, Dof, Work.Spaces.Dth, Work.Construction.s2]
    field_simp <;> ring
  -- ## the telescoping
  simp only [Work.Construction.N, Work.Spaces.Dz, Work.Construction.s2]
  rw [r1, r2, r3, r4, u1, u2, u3, v1, v2, v3,
    d1, d2, d3, d4, d5, d6, k1, k2, k3, k4, f1, f2]
  simp only [Pi.add_apply]
  rw [hTUAund, hTUBund, hTUCund, hTUDund]
  simp only [TRA, TRB, TRC, TRD, TUA, TUB, TUC, TUD, TVA, TVB, TVC, TVD,
    TDA, TDB, TDC, TDD, TEA, TEB, TEC, TED, StarH, UsPhi, Vstar, Fkstar, DthFstar, DzFstar,
    Zgof, Dof, Work.FTS.Nonlin.PhiTs, Work.Spaces.Dz, Work.Spaces.Dth, Work.Construction.s2,
    sinSq, pfac]
  rw [d6, d3, hh_eq]
  ring

end Work.FTS.GalFields.RHS.Sharp
