/-
# `CCSharp/IdentityC` — the pointwise identity for the `ClassC`-level difference of `N`

`NDiffIdC`: on the open quadrant `Qd`,

`N α (F_*+W₁) (Φ_s+E W₁) - N α (F_*+W₂) (Φ_s+E W₂) = foldr (+) 0 (Sharp.termList α Φs E W₁ W₂ h)`

with `h = W₁ - W₂`.

This is `SharpAux.Identity.N_diff_eq_sum` ported from `Gal`/`Sharp`-class data to the class `C`:

* `GalClass α g, g', h` becomes `ClassC α W₁, W₂, h` (`hh_eq : h = W₁ - W₂`);
* `L12FK_add_ge0` is replaced by `NZeroAux.L12add` + `EpsWPLim.FK_Fstar_add_of_SmoothOpen_HkMem`;
* the *only* place where `hEllSub` (an equality of functions) was used is `hpot3`; here it is
  replaced by `hpot3δ : PhiTil α W₁ (E W₁) = PhiTil α h δ + PhiTil α W₂ (E W₂)` (pure algebra,
  `δ := E W₁ - E W₂`) followed by the **slot identity** `SlotR/U/V α h δ = SlotR/U/V α h (E h)`
  on the quadrant (`EComparison.slot_eq_of_source`, via `EllPkgCls_E_sub_of_theta`).

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsRLX.CCSharp.Base
import Submission.Work.FTS.GalFields.RHS.SharpAux.Core
import Submission.Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC
import Submission.Work.FTS.GalFields.RHS.SharpAux.Assembly
import Submission.Work.FTS.StrongEps.EpsWPLim.Basic
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.L12add

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX.CCSharp

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000
set_option pp.deepTerms true

/-- `PhiTil α F Φ` is `C^∞` on the open quadrant as soon as `Φ` is and `z ↦ L₁₂(F)(z)` is
(the two ingredients of its definition). -/
theorem smoothOpen_PhiTil_of_open {α : ℝ} (hα : 0 < α) {F Φ : Fn}
    (hΦ : Work.FTS.EllipticEst.SmoothOpen Φ)
    (hL : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 F z)) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.PhiTil α F Φ) := by
  have hEq : Work.Construction.PhiTil α F Φ = fun z θ =>
      Φ z θ - (1 / (4 * α)) * Work.Construction.s2 θ * Work.Construction.L12 F z := rfl
  rw [hEq]
  simp only [Work.Construction.s2]
  refine Work.FTS.NonlinRows.smoothOpen_sub hΦ ?_
  exact Work.FTS.NonlinRows.NRow10aux.smoothOpen_mul
    (Work.FTS.NonlinRows.smoothOpen_const_mul (1 / (4 * α))
      Work.FTS.GalFields.RHS.smoothOpen_sin_two)
    hL

theorem NDiffIdC {α Ce Cs : ℝ} {Φs : Fn} {E : Fn → Fn}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    {W₁ W₂ h : Fn} (hW₁ : Work.FTS.ClassC.ClassC α W₁)
    (hW₂ : Work.FTS.ClassC.ClassC α W₂) (hh : Work.FTS.ClassC.ClassC α h)
    (hh_eq : ∀ z θ : ℝ, h z θ = W₁ z θ - W₂ z θ) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      (Work.Construction.N α (Work.Construction.Ftot α W₁)
          (fun z θ => Φs z θ + E W₁ z θ) z θ
        - Work.Construction.N α (Work.Construction.Ftot α W₂)
          (fun z θ => Φs z θ + E W₂ z θ) z θ)
      = (List.foldr (fun f acc => f + acc) (0 : Fn)
          (Work.FTS.GalFields.RHS.Sharp.termList α Φs E W₁ W₂ h)) z θ := by
  intro z θ hq
  obtain ⟨hz, hθ1, hθ2⟩ : z ∈ Set.Ioi (0 : ℝ) ∧ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    simpa only [Work.Construction.Qd, Set.mem_prod] using hq
  have hzle : (0 : ℝ) ≤ z := le_of_lt hz
  have hs2ne : Real.sin (2 * θ) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
  -- the difference potential `δ = E W₁ - E W₂`
  set δ : Fn := fun z θ => E W₁ z θ - E W₂ z θ with hδdef
  -- ## smoothness of the data
  have hFstarS : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  have hW₁S : Work.FTS.EllipticEst.SmoothOpen W₁ := hW₁.reg
  have hW₂S : Work.FTS.EllipticEst.SmoothOpen W₂ := hW₂.reg
  have hhS : Work.FTS.EllipticEst.SmoothOpen h := hh.reg
  have hδS : Work.FTS.EllipticEst.SmoothOpen δ := by
    rw [hδdef]
    exact Work.FTS.EllipticEst.smoothOpen_sub (hEll W₁ hW₁).1.smooth (hEll W₂ hW₂).1.smooth
  have hZs : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) :=
    Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil_star hα hα1 hstar
  have hZg₁ : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.PhiTil α W₁ (E W₁)) :=
    Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil hα (hEll W₁ hW₁).1
  have hZg₂ : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.PhiTil α W₂ (E W₂)) :=
    Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil hα (hEll W₂ hW₂).1
  have hDl : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.PhiTil α h (E h)) :=
    Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil hα (hEll h hh).1
  have hDlδ : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.PhiTil α h δ) :=
    smoothOpen_PhiTil_of_open hα hδS
      (Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC hα hh)
  -- ## honesty of the data
  have hW₁4 : Work.Spaces.HkMem α 4 W₁ := cMem hW₁ (by norm_num)
  have hW₂4 : Work.Spaces.HkMem α 4 W₂ := cMem hW₂ (by norm_num)
  have hh4 : Work.Spaces.HkMem α 4 h := cMem hh (by norm_num)
  -- ## the potential identities on `Q0`
  have hpot1 : ∀ z' θ' : ℝ, 0 < z' →
      Work.Construction.PhiTil α (Work.Construction.Ftot α W₁)
          (fun z θ => Φs z θ + E W₁ z θ) z' θ'
        = Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z' θ'
          + Work.Construction.PhiTil α W₁ (E W₁) z' θ' := by
    intro z' θ' hz'
    have hL : Work.Construction.L12 (Work.Construction.Ftot α W₁) z'
        = Work.Construction.L12 (Work.Construction.Fstar α) z'
          + Work.Construction.L12 W₁ z' :=
      (Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.L12add hα hα1 hW₁.reg hW₁4).1 z'
        (le_of_lt hz')
    simp only [Work.Construction.PhiTil, Work.Construction.Theta]
    rw [hL]
    ring
  have hpot2 : ∀ z' θ' : ℝ, 0 < z' →
      Work.Construction.PhiTil α (Work.Construction.Ftot α W₂)
          (fun z θ => Φs z θ + E W₂ z θ) z' θ'
        = Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z' θ'
          + Work.Construction.PhiTil α W₂ (E W₂) z' θ' := by
    intro z' θ' hz'
    have hL : Work.Construction.L12 (Work.Construction.Ftot α W₂) z'
        = Work.Construction.L12 (Work.Construction.Fstar α) z'
          + Work.Construction.L12 W₂ z' :=
      (Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.L12add hα hα1 hW₂.reg hW₂4).1 z'
        (le_of_lt hz')
    simp only [Work.Construction.PhiTil, Work.Construction.Theta]
    rw [hL]
    ring
  -- the `L₁₂`-additivity along the difference
  have hL12sub : ∀ z' : ℝ, 0 ≤ z' →
      Work.Construction.L12 W₁ z' = Work.Construction.L12 h z' + Work.Construction.L12 W₂ z' :=
    fun z' hz' => Work.FTS.GalFields.RHS.Sharp.L12_sub_ge0 hW₁S hW₂S hhS hW₁4 hW₂4 hh4 hh_eq hz'
  -- the *new* potential identity: the `h`-node potential is `PhiTil α h δ`
  have hpot3δ : ∀ z' θ' : ℝ, 0 < z' →
      Work.Construction.PhiTil α W₁ (E W₁) z' θ'
        = Work.Construction.PhiTil α h δ z' θ'
          + Work.Construction.PhiTil α W₂ (E W₂) z' θ' := by
    intro z' θ' hz'
    have hL := hL12sub z' (le_of_lt hz')
    simp only [Work.Construction.PhiTil, Work.Construction.Theta]
    rw [hL]
    rw [hδdef]
    simp only
    ring
  -- the **slot identity** on the quadrant: the slot of the `h`-node depends only on the source
  have hslots := by
    have hfun : h = fun z θ => W₁ z θ - W₂ z θ := by
      funext z θ
      exact hh_eq z θ
    have hsub : Work.FTS.StrongEps.EComparison.EllPkgCls α Ce h δ := by
      rw [hfun, hδdef]
      exact Work.FTS.StrongEps.EComparison.EllPkgCls_E_sub_of_theta hEll hW₁ hW₂
        (Work.FTS.StrongEps.EComparison.theta_sub_of_classC hW₁ hW₂)
    have hpkg : Work.FTS.StrongEps.EComparison.EllPkgCls α Ce h (E h) :=
      Work.FTS.StrongEps.EComparison.EllPkgCls_of_pkg hEll hh
    exact Work.FTS.StrongEps.EComparison.slots_eq_of_source_quadrant hα hα1 hsub hpkg
  have hslotR : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Construction.Rop α (Work.Construction.PhiTil α h δ) z θ
        = Work.Construction.Rop α (Work.Construction.PhiTil α h (E h)) z θ := by
    intro z θ hz' hθ0 hθ1
    simpa only [Work.FTS.StrongEps.EComparison.SlotR] using hslots.1 z θ hz' hθ0 hθ1
  have hslotU : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Construction.Uop α (Work.Construction.PhiTil α h δ) z θ
        = Work.Construction.Uop α (Work.Construction.PhiTil α h (E h)) z θ := by
    intro z θ hz' hθ0 hθ1
    have h := hslots.2.1 z θ hz' hθ0 hθ1
    have hs : Real.sin (2 * θ) ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
    simp only [Work.FTS.StrongEps.EComparison.SlotU, div_eq_mul_inv] at h
    exact mul_right_cancel₀ (inv_ne_zero hs) h
  have hslotV : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Construction.Vop (Work.Construction.PhiTil α h δ) z θ
        = Work.Construction.Vop (Work.Construction.PhiTil α h (E h)) z θ := by
    intro z θ hz' hθ0 hθ1
    simpa only [Work.FTS.StrongEps.EComparison.SlotV] using hslots.2.2 z θ hz' hθ0 hθ1
  -- ## additivity of `ℛ`, `U`, `V` on the potentials
  have r1 : Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Ftot α W₁)
        (fun z θ => Φs z θ + E W₁ z θ)) z θ
      = Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Rop α (Work.Construction.PhiTil α W₁ (E W₁)) z θ := by
    calc Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Ftot α W₁)
          (fun z θ => Φs z θ + E W₁ z θ)) z θ
        = Work.Construction.Rop α (fun z θ =>
            Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
              + Work.Construction.PhiTil α W₁ (E W₁) z θ) z θ :=
          Work.FTS.GalFields.RHS.Sharp.Rop_congr_Q0
            (f := Work.Construction.PhiTil α (Work.Construction.Ftot α W₁)
              (fun z θ => Φs z θ + E W₁ z θ))
            (g := fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
              + Work.Construction.PhiTil α W₁ (E W₁) z θ)
            (fun z' θ' hz' _ _ => hpot1 z' θ' hz') z θ hz hθ1 hθ2
      _ = Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Rop α (Work.Construction.PhiTil α W₁ (E W₁)) z θ :=
          Work.FTS.GalFields.RHS.Sharp.Rop_add_Q0 hZs hZg₁ z θ hz hθ1 hθ2
  have r2 : Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Ftot α W₂)
        (fun z θ => Φs z θ + E W₂ z θ)) z θ
      = Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Rop α (Work.Construction.PhiTil α W₂ (E W₂)) z θ := by
    calc Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Ftot α W₂)
          (fun z θ => Φs z θ + E W₂ z θ)) z θ
        = Work.Construction.Rop α (fun z θ =>
            Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
              + Work.Construction.PhiTil α W₂ (E W₂) z θ) z θ :=
          Work.FTS.GalFields.RHS.Sharp.Rop_congr_Q0
            (f := Work.Construction.PhiTil α (Work.Construction.Ftot α W₂)
              (fun z θ => Φs z θ + E W₂ z θ))
            (g := fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
              + Work.Construction.PhiTil α W₂ (E W₂) z θ)
            (fun z' θ' hz' _ _ => hpot2 z' θ' hz') z θ hz hθ1 hθ2
      _ = Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Rop α (Work.Construction.PhiTil α W₂ (E W₂)) z θ :=
          Work.FTS.GalFields.RHS.Sharp.Rop_add_Q0 hZs hZg₂ z θ hz hθ1 hθ2
  have r3 : Work.Construction.Rop α (Work.Construction.PhiTil α W₁ (E W₁)) z θ
      = Work.Construction.Rop α (Work.Construction.PhiTil α h (E h)) z θ
        + Work.Construction.Rop α (Work.Construction.PhiTil α W₂ (E W₂)) z θ := by
    calc Work.Construction.Rop α (Work.Construction.PhiTil α W₁ (E W₁)) z θ
        = Work.Construction.Rop α (fun z θ =>
            Work.Construction.PhiTil α h δ z θ
              + Work.Construction.PhiTil α W₂ (E W₂) z θ) z θ :=
          Work.FTS.GalFields.RHS.Sharp.Rop_congr_Q0
            (f := Work.Construction.PhiTil α W₁ (E W₁))
            (g := fun z θ => Work.Construction.PhiTil α h δ z θ
              + Work.Construction.PhiTil α W₂ (E W₂) z θ)
            (fun z' θ' hz' _ _ => hpot3δ z' θ' hz') z θ hz hθ1 hθ2
      _ = Work.Construction.Rop α (Work.Construction.PhiTil α h δ) z θ
        + Work.Construction.Rop α (Work.Construction.PhiTil α W₂ (E W₂)) z θ :=
          Work.FTS.GalFields.RHS.Sharp.Rop_add_Q0 hDlδ hZg₂ z θ hz hθ1 hθ2
      _ = Work.Construction.Rop α (Work.Construction.PhiTil α h (E h)) z θ
        + Work.Construction.Rop α (Work.Construction.PhiTil α W₂ (E W₂)) z θ := by
          rw [hslotR z θ hz hθ1 hθ2]
  have h1z : (1 : ℝ) + z ≠ 0 := by positivity
  have hz0 : z ≠ 0 := ne_of_gt hz
  have r4 : Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
      = (z / (1 + z)) * Work.FTS.GalFields.RHS.Sharp.StarH α Φs z θ := by
    have hfac : (z / (1 + z)) * ((z + 1) / z) = 1 := by field_simp <;> ring
    simp only [Work.FTS.GalFields.RHS.Sharp.StarH, Work.FTS.Nonlin.PhiTs]
    rw [show (z / (1 + z)) * ((z + 1) / z
          * Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ)
        = ((z / (1 + z)) * ((z + 1) / z))
          * Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        from by ring, hfac, one_mul]
  have u1 : Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Ftot α W₁)
        (fun z θ => Φs z θ + E W₁ z θ)) z θ
      = Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Uop α (Work.Construction.PhiTil α W₁ (E W₁)) z θ := by
    calc Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Ftot α W₁)
          (fun z θ => Φs z θ + E W₁ z θ)) z θ
        = Work.Construction.Uop α (fun z θ =>
            Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
              + Work.Construction.PhiTil α W₁ (E W₁) z θ) z θ :=
          Work.FTS.GalFields.RHS.Sharp.Uop_congr_Q0
            (f := Work.Construction.PhiTil α (Work.Construction.Ftot α W₁)
              (fun z θ => Φs z θ + E W₁ z θ))
            (g := fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
              + Work.Construction.PhiTil α W₁ (E W₁) z θ)
            (fun z' θ' hz' _ _ => hpot1 z' θ' hz') z θ hz hθ1 hθ2
      _ = Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Uop α (Work.Construction.PhiTil α W₁ (E W₁)) z θ :=
          Work.FTS.GalFields.RHS.Sharp.Uop_add_Q0 hZs hZg₁ z θ hz hθ1 hθ2
  have u2 : Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Ftot α W₂)
        (fun z θ => Φs z θ + E W₂ z θ)) z θ
      = Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Uop α (Work.Construction.PhiTil α W₂ (E W₂)) z θ := by
    calc Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Ftot α W₂)
          (fun z θ => Φs z θ + E W₂ z θ)) z θ
        = Work.Construction.Uop α (fun z θ =>
            Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
              + Work.Construction.PhiTil α W₂ (E W₂) z θ) z θ :=
          Work.FTS.GalFields.RHS.Sharp.Uop_congr_Q0
            (f := Work.Construction.PhiTil α (Work.Construction.Ftot α W₂)
              (fun z θ => Φs z θ + E W₂ z θ))
            (g := fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
              + Work.Construction.PhiTil α W₂ (E W₂) z θ)
            (fun z' θ' hz' _ _ => hpot2 z' θ' hz') z θ hz hθ1 hθ2
      _ = Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Uop α (Work.Construction.PhiTil α W₂ (E W₂)) z θ :=
          Work.FTS.GalFields.RHS.Sharp.Uop_add_Q0 hZs hZg₂ z θ hz hθ1 hθ2
  have u3 : Work.Construction.Uop α (Work.Construction.PhiTil α W₁ (E W₁)) z θ
      = Work.Construction.Uop α (Work.Construction.PhiTil α h (E h)) z θ
        + Work.Construction.Uop α (Work.Construction.PhiTil α W₂ (E W₂)) z θ := by
    calc Work.Construction.Uop α (Work.Construction.PhiTil α W₁ (E W₁)) z θ
        = Work.Construction.Uop α (fun z θ =>
            Work.Construction.PhiTil α h δ z θ
              + Work.Construction.PhiTil α W₂ (E W₂) z θ) z θ :=
          Work.FTS.GalFields.RHS.Sharp.Uop_congr_Q0
            (f := Work.Construction.PhiTil α W₁ (E W₁))
            (g := fun z θ => Work.Construction.PhiTil α h δ z θ
              + Work.Construction.PhiTil α W₂ (E W₂) z θ)
            (fun z' θ' hz' _ _ => hpot3δ z' θ' hz') z θ hz hθ1 hθ2
      _ = Work.Construction.Uop α (Work.Construction.PhiTil α h δ) z θ
        + Work.Construction.Uop α (Work.Construction.PhiTil α W₂ (E W₂)) z θ :=
          Work.FTS.GalFields.RHS.Sharp.Uop_add_Q0 hDlδ hZg₂ z θ hz hθ1 hθ2
      _ = Work.Construction.Uop α (Work.Construction.PhiTil α h (E h)) z θ
        + Work.Construction.Uop α (Work.Construction.PhiTil α W₂ (E W₂)) z θ := by
          rw [hslotU z θ hz hθ1 hθ2]
  have hcancel : ∀ (X : ℝ), Real.sin (2 * θ) * (X / Real.sin (2 * θ)) = X := by
    intro X
    rw [div_eq_mul_inv, mul_comm (Real.sin (2 * θ)) (X * (Real.sin (2 * θ))⁻¹), mul_assoc,
      inv_mul_cancel₀ hs2ne, mul_one]
  have u4 : Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
      = Real.sin (2 * θ) * Work.FTS.GalFields.RHS.Sharp.UsPhi α Φs z θ := by
    have hc := hcancel (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
    simp only [Work.FTS.GalFields.RHS.Sharp.UsPhi, Work.Construction.s2,
      Work.FTS.Nonlin.PhiTs] at hc ⊢
    exact hc.symm
  have u5 : Work.Construction.Uop α (Work.Construction.PhiTil α W₂ (E W₂)) z θ
      = Real.sin (2 * θ)
        * (Work.Construction.Uop α (Work.Construction.PhiTil α W₂ (E W₂)) z θ
          / Real.sin (2 * θ)) :=
    (hcancel (Work.Construction.Uop α (Work.Construction.PhiTil α W₂ (E W₂)) z θ)).symm
  have u6 : Work.Construction.Uop α (Work.Construction.PhiTil α h (E h)) z θ
      = Real.sin (2 * θ)
        * (Work.Construction.Uop α (Work.Construction.PhiTil α h (E h)) z θ
          / Real.sin (2 * θ)) :=
    (hcancel (Work.Construction.Uop α (Work.Construction.PhiTil α h (E h)) z θ)).symm
  have v1 : Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Ftot α W₁)
        (fun z θ => Φs z θ + E W₁ z θ)) z θ
      = Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Vop (Work.Construction.PhiTil α W₁ (E W₁)) z θ := by
    calc Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Ftot α W₁)
          (fun z θ => Φs z θ + E W₁ z θ)) z θ
        = Work.Construction.Vop (fun z θ =>
            Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
              + Work.Construction.PhiTil α W₁ (E W₁) z θ) z θ :=
          Work.FTS.GalFields.RHS.Sharp.Vop_congr_Q0
            (f := Work.Construction.PhiTil α (Work.Construction.Ftot α W₁)
              (fun z θ => Φs z θ + E W₁ z θ))
            (g := fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
              + Work.Construction.PhiTil α W₁ (E W₁) z θ)
            (fun z' θ' hz' _ _ => hpot1 z' θ' hz') z θ hz hθ1 hθ2
      _ = Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Vop (Work.Construction.PhiTil α W₁ (E W₁)) z θ :=
          Work.FTS.GalFields.RHS.Sharp.Vop_add_Q0 hZs hZg₁ z θ hz hθ1 hθ2
  have v2 : Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Ftot α W₂)
        (fun z θ => Φs z θ + E W₂ z θ)) z θ
      = Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Vop (Work.Construction.PhiTil α W₂ (E W₂)) z θ := by
    calc Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Ftot α W₂)
          (fun z θ => Φs z θ + E W₂ z θ)) z θ
        = Work.Construction.Vop (fun z θ =>
            Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
              + Work.Construction.PhiTil α W₂ (E W₂) z θ) z θ :=
          Work.FTS.GalFields.RHS.Sharp.Vop_congr_Q0
            (f := Work.Construction.PhiTil α (Work.Construction.Ftot α W₂)
              (fun z θ => Φs z θ + E W₂ z θ))
            (g := fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
              + Work.Construction.PhiTil α W₂ (E W₂) z θ)
            (fun z' θ' hz' _ _ => hpot2 z' θ' hz') z θ hz hθ1 hθ2
      _ = Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Vop (Work.Construction.PhiTil α W₂ (E W₂)) z θ :=
          Work.FTS.GalFields.RHS.Sharp.Vop_add_Q0 hZs hZg₂ z θ hz hθ1 hθ2
  have v3 : Work.Construction.Vop (Work.Construction.PhiTil α W₁ (E W₁)) z θ
      = Work.Construction.Vop (Work.Construction.PhiTil α h (E h)) z θ
        + Work.Construction.Vop (Work.Construction.PhiTil α W₂ (E W₂)) z θ := by
    calc Work.Construction.Vop (Work.Construction.PhiTil α W₁ (E W₁)) z θ
        = Work.Construction.Vop (fun z θ =>
            Work.Construction.PhiTil α h δ z θ
              + Work.Construction.PhiTil α W₂ (E W₂) z θ) z θ :=
          Work.FTS.GalFields.RHS.Sharp.Vop_congr_Q0
            (f := Work.Construction.PhiTil α W₁ (E W₁))
            (g := fun z θ => Work.Construction.PhiTil α h δ z θ
              + Work.Construction.PhiTil α W₂ (E W₂) z θ)
            (fun z' θ' hz' _ _ => hpot3δ z' θ' hz') z θ hz hθ1 hθ2
      _ = Work.Construction.Vop (Work.Construction.PhiTil α h δ) z θ
        + Work.Construction.Vop (Work.Construction.PhiTil α W₂ (E W₂)) z θ :=
          Work.FTS.GalFields.RHS.Sharp.Vop_add_Q0 hDlδ hZg₂ z θ hz hθ1 hθ2
      _ = Work.Construction.Vop (Work.Construction.PhiTil α h (E h)) z θ
        + Work.Construction.Vop (Work.Construction.PhiTil α W₂ (E W₂)) z θ := by
          rw [hslotV z θ hz hθ1 hθ2]
  -- ## the derivative, moment and value identities
  have hW₁_eq : W₁ = fun z θ => W₂ z θ + h z θ := by
    funext z' θ'
    have := hh_eq z' θ'
    linarith
  have d1 : Work.Spaces.pz (Work.Construction.Ftot α W₁) z θ
      = Work.Spaces.pz (Work.Construction.Fstar α) z θ + Work.Spaces.pz W₁ z θ :=
    Work.FTS.GalFields.RHS.Sharp.pz_add_Q0 hFstarS hW₁S z θ hz hθ1 hθ2
  have d2 : Work.Spaces.pz (Work.Construction.Ftot α W₂) z θ
      = Work.Spaces.pz (Work.Construction.Fstar α) z θ + Work.Spaces.pz W₂ z θ :=
    Work.FTS.GalFields.RHS.Sharp.pz_add_Q0 hFstarS hW₂S z θ hz hθ1 hθ2
  have d3 : Work.Spaces.pz W₁ z θ = Work.Spaces.pz W₂ z θ + Work.Spaces.pz h z θ := by
    rw [hW₁_eq]
    exact Work.FTS.GalFields.RHS.Sharp.pz_add_Q0 hW₂S hhS z θ hz hθ1 hθ2
  have d4 : Work.Spaces.pth (Work.Construction.Ftot α W₁) z θ
      = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth W₁ z θ :=
    Work.FTS.GalFields.RHS.Sharp.pth_add_Q0 hFstarS hW₁S z θ hz hθ1 hθ2
  have d5 : Work.Spaces.pth (Work.Construction.Ftot α W₂) z θ
      = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth W₂ z θ :=
    Work.FTS.GalFields.RHS.Sharp.pth_add_Q0 hFstarS hW₂S z θ hz hθ1 hθ2
  have d6 : Work.Spaces.pth W₁ z θ = Work.Spaces.pth W₂ z θ + Work.Spaces.pth h z θ := by
    rw [hW₁_eq]
    exact Work.FTS.GalFields.RHS.Sharp.pth_add_Q0 hW₂S hhS z θ hz hθ1 hθ2
  have k1 : Work.Construction.FK (Work.Construction.Ftot α W₁) z
      = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK W₁ z :=
    Work.FTS.StrongEps.EpsWPLim.FK_Fstar_add_of_SmoothOpen_HkMem hW₁.reg hW₁4 hz
  have k2 : Work.Construction.FK (Work.Construction.Ftot α W₂) z
      = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK W₂ z :=
    Work.FTS.StrongEps.EpsWPLim.FK_Fstar_add_of_SmoothOpen_HkMem hW₂.reg hW₂4 hz
  have k3 : Work.Construction.FK W₁ z
      = Work.Construction.FK W₂ z + Work.Construction.FK h z :=
    (Work.FTS.GalFields.RHS.Sharp.FK_sub hW₁S hW₂S hhS hW₁4 hW₂4 hh4
      (fun z θ => (hh_eq z θ)) hz).trans (by ring)
  have k4 : Work.Construction.FK (Work.Construction.Fstar α) z
      = Work.FTS.GalFields.RHS.Sharp.Fkstar α z θ := by
    simp only [Work.FTS.GalFields.RHS.Sharp.Fkstar, Work.Spaces.hKer_apply,
      Work.FTS.Nonlinear.FstarPkg.FK_Fstar hα hα1]
    ring
  have f1 : Work.Construction.Ftot α W₁ z θ
      = Work.Construction.Fstar α z θ + W₁ z θ := by
    simp only [Work.Construction.Ftot]
  have f2 : Work.Construction.Ftot α W₂ z θ
      = Work.Construction.Fstar α z θ + W₂ z θ := by
    simp only [Work.Construction.Ftot]
  -- ## the `U`-terms in undivided form (the `sin 2θ` denominator cancels)
  have hTUAund : Work.FTS.GalFields.RHS.Sharp.TUA α Φs h z θ
      = (-2) * (Work.Construction.Uop α
          (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        * Work.Spaces.pth h z θ) := by
    simp only [Work.FTS.GalFields.RHS.Sharp.TUA, Work.FTS.GalFields.RHS.Sharp.UsPhi,
      Work.FTS.Nonlin.PhiTs, Work.Spaces.Dth, Work.Construction.s2]
    field_simp <;> ring
  have hTUBund : Work.FTS.GalFields.RHS.Sharp.TUB α E W₂ h z θ
      = (-2) * (Work.Construction.Uop α
          (Work.Construction.PhiTil α W₂ (E W₂)) z θ
        * Work.Spaces.pth h z θ) := by
    simp only [Work.FTS.GalFields.RHS.Sharp.TUB, Work.FTS.GalFields.RHS.Sharp.Zgof,
      Work.Spaces.Dth, Work.Construction.s2]
    field_simp <;> ring
  have hTUCund : Work.FTS.GalFields.RHS.Sharp.TUC α E h z θ
      = (-2) * (Work.Spaces.pth (Work.Construction.Fstar α) z θ
        * Work.Construction.Uop α (Work.Construction.PhiTil α h (E h)) z θ) := by
    simp only [Work.FTS.GalFields.RHS.Sharp.TUC, Work.FTS.GalFields.RHS.Sharp.DthFstar,
      Work.FTS.GalFields.RHS.Sharp.Dof, Work.Spaces.Dth, Work.Construction.s2]
    field_simp <;> ring
  have hTUDund : Work.FTS.GalFields.RHS.Sharp.TUD α E W₁ h z θ
      = (-2) * (Work.Construction.Uop α
          (Work.Construction.PhiTil α h (E h)) z θ
        * Work.Spaces.pth W₁ z θ) := by
    simp only [Work.FTS.GalFields.RHS.Sharp.TUD, Work.FTS.GalFields.RHS.Sharp.Dof,
      Work.Spaces.Dth, Work.Construction.s2]
    field_simp <;> ring
  -- ## the telescoping
  rw [Work.FTS.GalFields.RHS.Sharp.termList_foldr]
  simp only [Work.Construction.N, Work.Spaces.Dz, Work.Construction.s2]
  rw [r1, r2, r3, r4, u1, u2, u3, v1, v2, v3,
    d1, d2, d3, d4, d5, d6, k1, k2, k3, k4, f1, f2]
  simp only [Pi.add_apply]
  rw [hTUAund, hTUBund, hTUCund, hTUDund]
  simp only [Work.FTS.GalFields.RHS.Sharp.TRA, Work.FTS.GalFields.RHS.Sharp.TRB,
    Work.FTS.GalFields.RHS.Sharp.TRC, Work.FTS.GalFields.RHS.Sharp.TRD,
    Work.FTS.GalFields.RHS.Sharp.TUA, Work.FTS.GalFields.RHS.Sharp.TUB,
    Work.FTS.GalFields.RHS.Sharp.TUC, Work.FTS.GalFields.RHS.Sharp.TUD,
    Work.FTS.GalFields.RHS.Sharp.TVA, Work.FTS.GalFields.RHS.Sharp.TVB,
    Work.FTS.GalFields.RHS.Sharp.TVC, Work.FTS.GalFields.RHS.Sharp.TVD,
    Work.FTS.GalFields.RHS.Sharp.TDA, Work.FTS.GalFields.RHS.Sharp.TDB,
    Work.FTS.GalFields.RHS.Sharp.TDC, Work.FTS.GalFields.RHS.Sharp.TDD,
    Work.FTS.GalFields.RHS.Sharp.TEA, Work.FTS.GalFields.RHS.Sharp.TEB,
    Work.FTS.GalFields.RHS.Sharp.TEC, Work.FTS.GalFields.RHS.Sharp.TED,
    Work.FTS.GalFields.RHS.Sharp.StarH, Work.FTS.GalFields.RHS.Sharp.UsPhi,
    Work.FTS.GalFields.RHS.Sharp.Vstar, Work.FTS.GalFields.RHS.Sharp.Fkstar,
    Work.FTS.GalFields.RHS.Sharp.DthFstar, Work.FTS.GalFields.RHS.Sharp.DzFstar,
    Work.FTS.GalFields.RHS.Sharp.Zgof, Work.FTS.GalFields.RHS.Sharp.Dof,
    Work.FTS.Nonlin.PhiTs, Work.Spaces.Dz, Work.Spaces.Dth, Work.Construction.s2,
    Work.FTS.GalFields.RHS.Sharp.sinSq, Work.FTS.GalFields.RHS.Sharp.pfac]
  rw [d6, d3, hh_eq]
  ring

end Work.FTS.StrongEps.EpsRLX.CCSharp
