/-
# `H5/SmoothK5` — the `EllPkgK α 6`-variants of `NBlk_smooth` and `SmoothOpenRHS`

The level-four smoothness lemmas `ClassCRHS.NBlk_smooth` (`SmoothOpen` of the twenty pieces) and
`ClassCRHS.SmoothOpenRHS` (in particular `SmoothOpen` of `N`) are stated for the level-four
package `VocabO.EllPkgGo`.  The level-five `N`-block is stated for `ClassC.EllPkgK α 6`, whose
`.R`, `.U`, `.V`, `.smooth` fields have exactly the same projections; the two proofs therefore
transcribe verbatim, which this file records.  (Nothing here is new mathematics; the
`HkSumOpenClosure5` transfer needs `SmoothOpen (N …)` and `SmoothOpen (NBlk … k)`.)
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnNDefs
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnNAux
import Submission.Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS
import Submission.Work.FTS.StrongPersist.Star6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **`SmoothOpen` of the twenty `NBlk` pieces**, for `EllPkgK α 6` elliptic data. -/
theorem NBlk_smoothK {α Ce Cs6 : ℝ} {w Φs Φg : Fn} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hw : Work.FTS.ClassC.ClassC α w) (hell : Work.FTS.ClassC.EllPkgK α 6 Ce w Φg)
    (hstar : Work.FTS.StrongPersist.StarPkg6 α Cs6 Φs) :
    ∀ k ∈ Finset.range 20,
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k) := by
  have hsw : Work.FTS.VocabO.StarPkgo α Cs6 Φs := hstar.toStarPkgo2.toStarPkgo
  have hRsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg)) := hell.R.1.1
  have hUcsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α w Φg) z θ / Work.Construction.s2 θ) :=
    hell.U.1.1
  have hVcsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg)) := hell.V.1.1
  have hRssm : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      (z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_Rs_of_star hα0 hα1 hsw
  have hUssm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z *
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Work.Construction.s2 θ)) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_Us_of_star hα0 hα1 hsw
  have hVssm : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      (z + 1) / z * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_Vs_of_star hα0 hα1 hsw
  have hFWsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Construction.Fstar α z θ) :=
    Work.FTS.EllipticEst.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  have hDthFssm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dth (Work.Construction.Fstar α)) := hFWsm.Dth
  have hDzFssm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dz (Work.Construction.Fstar α)) := hFWsm.Dz
  have hDthwsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth w) := hw.reg.Dth
  have hDzwsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz w) := hw.reg.Dz
  have hFKesm : Work.FTS.EllipticEst.SmoothOpen
      (fun z _ => Work.Construction.FK (Work.Construction.Fstar α) z) :=
    Work.FTS.GalFields.RHS.smoothOpen_FK_Fstar_rad α hα0 hα1
  have hFKws : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.FK w z) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_FKw_of_classC hw
  have hFKnegsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z _ : ℝ => (-(2 * α)) * Work.Spaces.hKer z) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_FKneg α
  have hSinSq : Work.FTS.EllipticEst.SmoothOpen (fun x θ : ℝ => -Real.sin θ ^ 2) :=
    Work.FTS.Nonlinear.Open.row25_smoothOpen_neg_sinSq
  have hG : ∀ (A B : Fn), Work.FTS.EllipticEst.SmoothOpen A →
      Work.FTS.EllipticEst.SmoothOpen B →
      Work.FTS.EllipticEst.SmoothOpen (fun z θ => A z θ * B z θ) :=
    fun A B hA hB => Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hA hB
  have hC : ∀ (c : ℝ) (A : Fn), Work.FTS.EllipticEst.SmoothOpen A →
      Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * A z θ) :=
    fun c A hA => Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl c hA
  have hpw := hG (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg)) w hRsm hw.reg
  have hps := hG (fun z θ => Work.Construction.Fstar α z θ)
    (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg)) hFWsm hRsm
  have hphiw : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z / (1 + z) * w z θ) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_phi_mul hw.reg
  have hphiFs : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_phi_mul hFWsm
  have hphiDthw : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z / (1 + z) * Work.Spaces.Dth w z θ) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_phi_mul (hw.reg.Dth)
  have hphiDzw : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z / (1 + z) * Work.Spaces.Dz w z θ) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_phi_mul (hw.reg.Dz)
  have hphiDthFs : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_phi_mul hFWsm.Dth
  have hphiDzFs : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_phi_mul hFWsm.Dz
  intro k hk
  have hk20 : k < 20 := Finset.mem_range.mp hk
  interval_cases k
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]; exact hC 2 _ hpw
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]; exact hC 2 _ hps
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]; exact hC 2 _ (hG _ _ hRssm hphiw)
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]; exact hC 2 _ (hG _ _ hRssm hphiFs)
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]; exact hC (-2) _ (hG _ _ hUcsm hDthwsm)
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]; exact hC (-2) _ (hG _ _ hDthFssm hUcsm)
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]; exact hC (-2) _ (hG _ _ hUssm hphiDthw)
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]; exact hC (-2) _ (hG _ _ hUssm hphiDthFs)
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]; exact hC (-(2 * α)) _ (hG _ _ hVcsm hDzwsm)
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]; exact hC (-(2 * α)) _ (hG _ _ hDzFssm hVcsm)
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]; exact hC (-(2 * α)) _ (hG _ _ hVssm hphiDzw)
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]; exact hC (-(2 * α)) _ (hG _ _ hVssm hphiDzFs)
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]; exact hC (-(1 / 2)) _ (hG _ _ hFKws hDthwsm)
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]; exact hC (-(1 / 2)) _ (hG _ _ hDthFssm hFKws)
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]; exact hC (1 / 2) _ (hG _ _ hFKnegsm hDthwsm)
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]; exact hC (-(1 / 2)) _ (hG _ _ hFKesm hDthFssm)
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]
    exact hG _ _ hSinSq (hG _ _ hFKws hw.reg)
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]
    exact hG _ _ hSinSq (hG _ _ hFWsm hFKws)
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]
    exact hG _ _ hSinSq (hG _ _ hFKesm hw.reg)
  · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]
    exact hG _ _ hSinSq (hG _ _ hFKesm hFWsm)

/-- **`SmoothOpen (N α (F_*+w) (Φs+Φg))`** for `EllPkgK α 6` elliptic data (conjunct 5 of
`ClassCRHS.SmoothOpenRHS`, transcribed). -/
theorem SmoothOpenN_K {α Ce Cs6 : ℝ} {Φs w Φg : Fn}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hw : Work.FTS.ClassC.ClassC α w)
    (hell : Work.FTS.ClassC.EllPkgK α 6 Ce w Φg)
    (hstar : Work.FTS.StrongPersist.StarPkg6 α Cs6 Φs) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.N α (Work.Construction.Ftot α w)
      (fun z θ => Φs z θ + Φg z θ)) := by
  have hmem4 : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 4 (by norm_num) hw.mem
  have hL12w : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.L12 w z) :=
    Work.FTS.NonlinRows.smoothOpen_L12_radial hα hell.smooth hell.V.1.1
  have hFKw : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.FK w z) := by
    have hfs : Work.FTS.EllipticEst.SmoothOpen
        (fun z (_ : ℝ) => Work.Elliptic.Fstar w z) :=
      Work.FTS.NonlinRows.smoothOpen_radial (r := Work.Elliptic.Fstar w) hw.fsm
    refine (Work.FTS.NonlinRows.smoothOpen_const_mul 3 hfs).congr ?_
    intro z _ hz _ _
    exact (Work.FTS_RegExport.RXT.velPert_FK_eq w z).symm
  have hL12F : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.L12 (Work.Construction.Fstar α) z) :=
    Work.FTS.GalFields.RHS.smoothOpen_L12_Fstar_rad α hα hα1
  have hFKF : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.FK (Work.Construction.Fstar α) z) :=
    Work.FTS.GalFields.RHS.smoothOpen_FK_Fstar_rad α hα hα1
  have hL12tot : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.L12 (Work.Construction.Ftot α w) z) :=
    (Work.FTS.NonlinRows.smoothOpen_add hL12F hL12w).congr (by
      intro z _ hz _ _
      exact (Work.FTS.StrongPersist.H6Rows.NZaux.L12AddFstar hα hα1 hw.reg hmem4 z hz).symm)
  have hFKadd : ∀ z : ℝ, 0 < z → Work.Construction.FK (Work.Construction.Ftot α w) z
      = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK w z := by
    intro z hz
    exact Work.FTS.GalFields.RHS.FK_add_of_slices
      (a := Work.Construction.Fstar α) (b := w) (ne_of_gt hz)
      (Work.Stability.integrableOn_slice_Fstar α hα z)
      (Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hw.reg hmem4 hz)
  have hFKtot : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.FK (Work.Construction.Ftot α w) z) :=
    (Work.FTS.NonlinRows.smoothOpen_add hFKF hFKw).congr (by
      intro z _ hz _ _
      exact (hFKadd z hz).symm)
  have hΦ : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Φs z θ + Φg z θ) :=
    Work.FTS.NonlinRows.smoothOpen_add hstar.smooth hell.smooth
  have hTheta : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (1 / (4 * α)) * (Real.sin (2 * θ)
        * Work.Construction.L12 (Work.Construction.Ftot α w) z)) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul (1 / (4 * α))
      (Work.FTS.NonlinRows.smoothOpen_mul
        (Work.FTS.GalFields.RHS.smoothOpen_sin_two) hL12tot)
  have hPsi_eq : Work.Construction.PhiTil α (Work.Construction.Ftot α w)
        (fun z θ => Φs z θ + Φg z θ)
      = fun z θ => (Φs z θ + Φg z θ)
        - (1 / (4 * α)) * (Real.sin (2 * θ)
          * Work.Construction.L12 (Work.Construction.Ftot α w) z) := by
    funext z θ
    simp only [Work.Construction.PhiTil, Work.Construction.Theta, Work.Construction.s2]
    ring
  have hPsi : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.PhiTil α (Work.Construction.Ftot α w)
        (fun z θ => Φs z θ + Φg z θ)) :=
    hPsi_eq ▸ (Work.FTS.NonlinRows.smoothOpen_sub hΦ hTheta)
  have hRop := Work.FTS.NonlinRows.smoothOpen_Rop (α := α) hPsi
  have hUop : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Ftot α w)
        (fun z θ => Φs z θ + Φg z θ))) :=
    Work.FTS.EllipticEst.smoothOpen_Uop hPsi
  have hVop := Work.FTS.NonlinRows.smoothOpen_Vop hPsi
  have hF : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Ftot α w) :=
    Work.FTS.NonlinRows.smoothOpen_add
      (Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)) hw.reg
  have hpthF := Work.FTS.EllipticEst.SmoothOpen.pth hF
  have hDzF := Work.FTS.EllipticEst.SmoothOpen.Dz hF
  have t1 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (2 * Work.Construction.Rop α (Work.Construction.PhiTil α
          (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) z θ)
        * Work.Construction.Ftot α w z θ) :=
    Work.FTS.NonlinRows.smoothOpen_mul
      (Work.FTS.NonlinRows.smoothOpen_const_mul 2 hRop) hF
  have t2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (2 * Work.Construction.Uop α (Work.Construction.PhiTil α
          (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) z θ)
        * Work.Spaces.pth (Work.Construction.Ftot α w) z θ) :=
    Work.FTS.NonlinRows.smoothOpen_mul
      (Work.FTS.NonlinRows.smoothOpen_const_mul 2 hUop) hpthF
  have t3 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => ((2 * α) * Work.Construction.Vop (Work.Construction.PhiTil α
          (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) z θ)
        * Work.Spaces.Dz (Work.Construction.Ftot α w) z θ) :=
    Work.FTS.NonlinRows.smoothOpen_mul
      (Work.FTS.NonlinRows.smoothOpen_const_mul (2 * α) hVop) hDzF
  have t4 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (((1 / 2) * Real.sin (2 * θ)) * Work.Construction.FK
          (Work.Construction.Ftot α w) z)
        * Work.Spaces.pth (Work.Construction.Ftot α w) z θ) :=
    Work.FTS.NonlinRows.smoothOpen_mul
      (Work.FTS.NonlinRows.smoothOpen_mul
        (Work.FTS.NonlinRows.smoothOpen_const_mul (1 / 2)
          (Work.FTS.GalFields.RHS.smoothOpen_sin_two)) hFKtot) hpthF
  have t5 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Ftot α w) z)
        * Work.Construction.Ftot α w z θ) :=
    Work.FTS.NonlinRows.smoothOpen_mul
      (Work.FTS.NonlinRows.smoothOpen_mul
        (Work.FTS.GalFields.RHS.smoothOpen_sin_sq) hFKtot) hF
  have hmain : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => 2 * Work.Construction.Rop α (Work.Construction.PhiTil α
            (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) z θ
          * Work.Construction.Ftot α w z θ
        - 2 * Work.Construction.Uop α (Work.Construction.PhiTil α
            (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) z θ
          * Work.Spaces.pth (Work.Construction.Ftot α w) z θ
        - 2 * α * Work.Construction.Vop (Work.Construction.PhiTil α
            (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) z θ
          * Work.Spaces.Dz (Work.Construction.Ftot α w) z θ
        - (1 / 2) * Real.sin (2 * θ) * Work.Construction.FK (Work.Construction.Ftot α w) z
          * Work.Spaces.pth (Work.Construction.Ftot α w) z θ
        - Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Ftot α w) z
          * Work.Construction.Ftot α w z θ) :=
    Work.FTS.NonlinRows.smoothOpen_sub
      (Work.FTS.NonlinRows.smoothOpen_sub
        (Work.FTS.NonlinRows.smoothOpen_sub
          (Work.FTS.NonlinRows.smoothOpen_sub t1 t2) t3) t4) t5
  change Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => 2 * Work.Construction.Rop α (Work.Construction.PhiTil α
            (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) z θ
          * Work.Construction.Ftot α w z θ
        - 2 * Work.Construction.Uop α (Work.Construction.PhiTil α
            (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) z θ
          * Work.Spaces.pth (Work.Construction.Ftot α w) z θ
        - 2 * α * Work.Construction.Vop (Work.Construction.PhiTil α
            (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) z θ
          * Work.Spaces.Dz (Work.Construction.Ftot α w) z θ
        - (1 / 2) * Work.Construction.s2 θ * Work.Construction.FK
            (Work.Construction.Ftot α w) z
          * Work.Spaces.pth (Work.Construction.Ftot α w) z θ
        - Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Ftot α w) z
          * Work.Construction.Ftot α w z θ)
  exact hmain

end Work.FTS.StrongEps.H5
