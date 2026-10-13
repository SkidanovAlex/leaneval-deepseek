import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.OpenPkg.prod_field
import Submission.Work.FTS.OpenPkg.wprod_field_winf
import Submission.Work.FTS.OpenPkg.Good
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.NonlinRows.NRow10aux.mul_phi_Hk
import Submission.Work.FTS.NonlinRows.NRow10aux.starH_smoothOpen
import Submission.Work.FTS.NonlinRows.NRow1_7Aux
import Submission.Work.FTS.NonlinRows.NRow22
import Submission.Work.FTS.NonlinRows.Rl1.PvecMeasOpen
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Pieces.RNP.RNP24.angProfile_sinSq
import Submission.Work.FTS.GalFields.RHS.SharpAux.Core
import Submission.Work.FTS.GalBasis.cc.L12_add_of_HkMem
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnN0Aux
import Submission.Work.FTS.StrongPersist.L3Rhs.N1ssPriced
import Submission.Work.FTS.StrongPersist.L3Rhs.N2ssPriced
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.EllipticEst.UopHk.hkMemDzPth_of_shifted
import Submission.Work.FTS.PhiStar.StarPkgo2Aux.FieldRegularity
import Submission.Work.FTS_RegExport.RXT.velPert
import Submission.Work.FTS.LocData.HkMem_const_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsZero.ClassCHk

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

open Work.FTS.Galerkin (Fn)

/-!
# `NMemAux` — helpers and the `N₁`, `N₂` pieces of the split of `N`

This module supplies the elementary helpers (`Good` is closed under finite sums, `SmoothOpen`
of `z/(1+z)`, the angular profile `-sin²θ`, the class-`C` moment `FK w`) and the eight pieces
`N₁^{gg}`, `N₁^{gs}`, `N₁^{sg}`, `N₁^{ss}`, `N₂^{gg}`, `N₂^{gs}`, `N₂^{sg}`, `N₂^{ss}` of
`Work.FTS.Nonlin.Defs`, each proved `ℋ⁴`-honest and `C⁴` on the open quadrant
(`Work.FTS.OpenPkg.Good`).  The consumer is `Work.FTS.StrongEps.EpsZero.ClassCHk.NMem`.
-/

/-! ## Local helpers -/

/-- The zero function is `Good`. -/
theorem good_zero (α : ℝ) :
    Work.FTS.OpenPkg.Good α (0 : Fn) :=
  ⟨contDiffOn_const, Work.FTS.EllipticEst.HkMem_zero α 4⟩

/-- `Good` is closed under finite sums over `range n`. -/
theorem good_sum_range {α : ℝ} (n : ℕ) (P : ℕ → Fn)
    (h : ∀ i ∈ Finset.range n, Work.FTS.OpenPkg.Good α (P i)) :
    Work.FTS.OpenPkg.Good α (fun z θ => ∑ i ∈ Finset.range n, P i z θ) := by
  induction n with
  | zero =>
      have hzero : (fun z θ => ∑ i ∈ Finset.range 0, P i z θ) = (0 : Fn) := by
        funext z θ; simp
      rw [hzero]
      exact good_zero α
  | succ n ih =>
      have hsplit : (fun z θ => ∑ i ∈ Finset.range (n + 1), P i z θ)
          = (fun z θ => (∑ i ∈ Finset.range n, P i z θ) + P n z θ) := by
        funext z θ; rw [Finset.sum_range_succ]
      rw [hsplit]
      refine (ih (fun i hi => h i (Finset.mem_range.mpr ?_))).add
        (h n (Finset.mem_range.mpr (Nat.lt_succ_self n)))
      exact lt_trans (Finset.mem_range.mp hi) (Nat.lt_succ_self n)

/-- `SmoothOpen (f · g)` from `SmoothOpen f`, `SmoothOpen g`. -/
theorem so_mul {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * g z θ) :=
  Work.FTS.NonlinRows.NRow10aux.smoothOpen_mul hf hg

/-- `SmoothOpen (z ↦ z/(1+z))`. -/
theorem so_zdiv :
    Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => z / (1 + z)) := by
  refine Work.FTS.NonlinRows.smoothOpen_radial (r := fun z => z / (1 + z)) (fun n => ?_)
  exact ContDiffOn.div contDiffOn_id (contDiffOn_const.add contDiffOn_id)
    (fun z hz => ne_of_gt (by linarith [Set.mem_Ioi.mp hz]))

/-- `s2 θ = sin 2θ` is non-zero on the open angular interval. -/
theorem s2_ne_zero {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Construction.s2 θ ≠ 0 := by
  simp only [Work.Construction.s2]
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos]))

/-- The angular factor `-(sin θ)²` and its `D_θ`-iterates (`RNP24.angProfile_sinSq`). -/
theorem angSq_data :
    ∃ B : ℝ, 0 < B ∧
      Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => -((Real.sin θ) ^ 2)) ∧
      (∀ θ ∈ Work.Spaces.Iθ, |(-((Real.sin θ) ^ 2))| ≤ B) ∧
      (∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => -((Real.sin θ') ^ 2)) 0 θ|
          ≤ B * Real.sin (2 * θ)) := by
  obtain ⟨B, hB, hsi, hb, hi⟩ := Work.FTS.Nonlinear.Pieces.RNP.RNP24.angProfile_sinSq
  exact ⟨B, hB, Work.FTS.EllipticEst.smoothOpen_of_smoothInt hsi, hb, hi⟩

variable {α Ce Cs : ℝ} {w Φs Φg : Fn}

/-- `FK w` is `C^∞` on the open quadrant: `FK F = 3 F_*(F)` and the angular moment
`Elliptic.Fstar w` is smooth by the field `ClassC.fsm`. -/
theorem so_FKw (hw : Work.FTS.ClassC.ClassC α w) :
    Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => Work.Construction.FK w z) := by
  have hfs : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Elliptic.Fstar w z) :=
    Work.FTS.NonlinRows.smoothOpen_radial (r := fun z => Work.Elliptic.Fstar w z) hw.fsm
  refine (Work.FTS.NonlinRows.smoothOpen_const_mul 3 hfs).congr ?_
  intro z θ _ _ _
  exact (Work.FTS_RegExport.RXT.velPert_FK_eq w z).symm

/-! ## The `N₁` and `N₂` pieces -/

/-- `N₁^{gg} = 2 ℛ(Φ̃_g)·w`. -/
theorem good_N1gg (hα : 0 < α) (hα1 : α ≤ 1)
    (hw : Work.FTS.ClassC.ClassC α w) (hell : Work.FTS.VocabO.EllPkgGo α Ce w Φg) :
    Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N1gg α w Φg) := by
  obtain ⟨Cp, _, hprod⟩ := Work.FTS.OpenPkg.prod_field
  have hmem4 : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 4 (by norm_num) hw.mem
  have h1 : Work.Spaces.HkMem α 4 (fun z θ =>
      Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg) z θ * w z θ) :=
    (hprod α hα hα1 (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg)) w
      hell.R.1 ⟨hw.reg, hmem4⟩).1
  have hsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N1gg α w Φg) :=
    (so_mul (Work.FTS.NonlinRows.smoothOpen_const_mul 2 hell.R.1.1) hw.reg).congr
      (fun z θ _ _ _ => by simp only [Work.FTS.Nonlin.N1gg, Work.FTS.Nonlin.PhiTg]; try ring_nf)
  exact ⟨hsm.forall 4, Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4
    (Work.FTS.LocData.HkMem_const_mul α 4 2 h1)
    (fun z _ θ _ => by simp only [Work.FTS.Nonlin.N1gg, Work.FTS.Nonlin.PhiTg]; try ring_nf)⟩

/-- `N₁^{gs} = 2 ℛ(Φ̃_g)·F_*`. -/
theorem good_N1gs (hα : 0 < α) (hα1 : α ≤ 1)
    (hw : Work.FTS.ClassC.ClassC α w) (hell : Work.FTS.VocabO.EllPkgGo α Ce w Φg) :
    Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N1gs α w Φg) := by
  obtain ⟨Cwv, _, hwprod⟩ := Work.FTS.OpenPkg.wprod_field_winf
  obtain ⟨_, _, hFstarW⟩ := Work.FTS.Nonlinear.FstarPkg.Fstar_W
  have hFsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α
  have h1 : Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.Fstar α z θ *
      Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg) z θ) :=
    (hwprod α hα hα1 (Work.Construction.Fstar α)
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg)) hFsm
      (hFstarW α hα hα1).1 hell.R.1).1
  have hsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N1gs α w Φg) :=
    (so_mul (Work.FTS.NonlinRows.smoothOpen_const_mul 2 hell.R.1.1) hFsm).congr
      (fun z θ _ _ _ => by simp only [Work.FTS.Nonlin.N1gs, Work.FTS.Nonlin.PhiTg]; try ring_nf)
  exact ⟨hsm.forall 4, Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4
    (Work.FTS.LocData.HkMem_const_mul α 4 2 h1)
    (fun z _ θ _ => by simp only [Work.FTS.Nonlin.N1gs, Work.FTS.Nonlin.PhiTg]; try ring_nf)⟩

/-- `N₁^{sg} = 2 ℛ(Φ̃_*)·w = 2·(((z+1)/z)ℛ(Φ̃_*))·((z/(1+z))w)`. -/
theorem good_N1sg (hα : 0 < α) (hα1 : α ≤ 1)
    (hw : Work.FTS.ClassC.ClassC α w) (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N1sg α Φs w) := by
  obtain ⟨Cwv, _, hwprod⟩ := Work.FTS.OpenPkg.wprod_field_winf
  obtain ⟨Cm, _, hmulphi⟩ := Work.FTS.NonlinRows.NRow10aux.mul_phi_Hk
  have hmem4 : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 4 (by norm_num) hw.mem
  have hH1sm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) :=
    Work.FTS.NonlinRows.NRow10aux.starH_smoothOpen hα hα1 hstar.toStarPkgo
  have hH1W : Work.Spaces.WlInfMem α 4
      (fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) :=
    hstar.RW.1
  have hH2sm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z / (1 + z) * w z θ) :=
    so_mul so_zdiv hw.reg
  have hH2mem : Work.Spaces.HkMem α 4 (fun z θ => z / (1 + z) * w z θ) :=
    (hmulphi hα hα1 ⟨hw.reg, hmem4⟩).1
  have h1 : Work.Spaces.HkMem α 4 (fun z θ =>
      ((z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
        * (z / (1 + z) * w z θ)) :=
    (hwprod α hα hα1 _ _ hH1sm hH1W ⟨hH2sm, hH2mem⟩).1
  have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.Nonlin.N1sg α Φs w z θ
        = 2 * (((z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
              * (z / (1 + z) * w z θ)) := by
    intro z θ hz hθ hlt
    have hz0 : z ≠ 0 := ne_of_gt hz
    have h1z : (1 : ℝ) + z ≠ 0 := by linarith
    have hkey : (z + 1) / z * (z / (1 + z)) = (1 : ℝ) := by
      field_simp
      ring
    simp only [Work.FTS.Nonlin.N1sg]
    calc 2 * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ * w z θ
        = 2 * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ * w z θ
            * ((z + 1) / z * (z / (1 + z))) := by rw [hkey]; ring
      _ = 2 * (((z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
            * (z / (1 + z) * w z θ)) := by ring
  have hsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N1sg α Φs w) :=
    (Work.FTS.NonlinRows.smoothOpen_const_mul 2 (so_mul hH1sm hH2sm)).congr
      (fun z θ hz hθ hlt => (hpt z θ hz hθ hlt).symm)
  refine ⟨hsm.forall 4, ?_⟩
  exact Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4
    (Work.FTS.LocData.HkMem_const_mul α 4 2 h1)
    (fun z hz θ hθ => (hpt z θ hz hθ.1 hθ.2).symm)

/-- `N₁^{**} = 2 ℛ(Φ̃_*)·F_*` (priced row 11). -/
theorem good_N1ss (hα : 0 < α) (hα1 : α ≤ 1)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N1ss α Φs) := by
  obtain ⟨_, _, hrow⟩ := Work.FTS.StrongPersist.L3Rhs.N1ssPriced
  have hFsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α
  have hsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N1ss α Φs) :=
    (so_mul (Work.FTS.NonlinRows.smoothOpen_const_mul 2
      (Work.FTS.NonlinRows.smoothOpen_Rop
        (Work.FTS.NonlinRows.NRow10aux.smoothOpen_PhiTs hα hα1 hstar.toStarPkgo))) hFsm).congr
      (fun z θ _ _ _ => by simp only [Work.FTS.Nonlin.N1ss]; try ring_nf)
  exact ⟨hsm.forall 4, (hrow α ⟨hα, hα1⟩ Cs Φs hstar).1⟩

/-- `N₂^{gg} = -2 𝒰(Φ̃_g)·∂_θ w = -2·((Uop Φ̃_g)/s2)·D_θ w`. -/
theorem good_N2gg (hα : 0 < α) (hα1 : α ≤ 1)
    (hw : Work.FTS.ClassC.ClassC α w) (hell : Work.FTS.VocabO.EllPkgGo α Ce w Φg) :
    Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N2gg α w Φg) := by
  obtain ⟨Cp, _, hprod⟩ := Work.FTS.OpenPkg.prod_field
  have hmem5 : Work.Spaces.HkMem α 5 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 5 (by norm_num) hw.mem
  have hDthQ : Work.FTS.VocabO.HQo α 4 (Work.Spaces.Dth w) :=
    ⟨hw.reg.Dth, Work.FTS.StrongEps.ClassCRHS.hkMem_Dth_of_smoothOpen hα 4 hw.reg hmem5⟩
  have h1 : Work.Spaces.HkMem α 4 (fun z θ =>
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α w Φg) z θ / Work.Construction.s2 θ)
        * Work.Spaces.Dth w z θ) :=
    (hprod α hα hα1 _ (Work.Spaces.Dth w) hell.U.1 hDthQ).1
  have hsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N2gg α w Φg) :=
    (so_mul (Work.FTS.NonlinRows.smoothOpen_const_mul (-2)
      (Work.FTS.NonlinRows.Rl1.smoothOpen_Uop_open
        (Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil hα hell))) hw.reg.pth).congr
      (fun z θ _ _ _ => by simp only [Work.FTS.Nonlin.N2gg, Work.FTS.Nonlin.PhiTg]; try ring_nf)
  refine ⟨hsm.forall 4, ?_⟩
  refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4
    (Work.FTS.LocData.HkMem_const_mul α 4 (-2) h1) (fun z hz θ hθ => ?_)
  have hs : Work.Construction.s2 θ ≠ 0 := s2_ne_zero hθ
  have hD : Work.Spaces.Dth w z θ = Work.Construction.s2 θ * Work.Spaces.pth w z θ := by
    simp only [Work.Spaces.Dth, Work.Construction.s2]
  simp only [Work.FTS.Nonlin.N2gg, Work.FTS.Nonlin.PhiTg]
  rw [hD]
  field_simp
  try ring

/-- `N₂^{gs} = -2 𝒰(Φ̃_g)·∂_θF_* = -2·((Uop Φ̃_g)/s2)·D_θF_*`. -/
theorem good_N2gs (hα : 0 < α) (hα1 : α ≤ 1)
    (hell : Work.FTS.VocabO.EllPkgGo α Ce w Φg) :
    Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N2gs α w Φg) := by
  obtain ⟨Cwv, _, hwprod⟩ := Work.FTS.OpenPkg.wprod_field_winf
  obtain ⟨_, _, hDthFW⟩ := Work.FTS.Nonlinear.FstarPkg.DthFstar_W
  have hFsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α
  have h1 : Work.Spaces.HkMem α 4 (fun z θ =>
      Work.Spaces.Dth (Work.Construction.Fstar α) z θ *
        (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α w Φg) z θ / Work.Construction.s2 θ)) :=
    (hwprod α hα hα1 (Work.Spaces.Dth (Work.Construction.Fstar α)) _
      hFsm.Dth (hDthFW α hα hα1).1 hell.U.1).1
  have hsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N2gs α w Φg) :=
    (so_mul (Work.FTS.NonlinRows.smoothOpen_const_mul (-2)
      (Work.FTS.NonlinRows.Rl1.smoothOpen_Uop_open
        (Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil hα hell))) hFsm.pth).congr
      (fun z θ _ _ _ => by simp only [Work.FTS.Nonlin.N2gs, Work.FTS.Nonlin.PhiTg]; try ring_nf)
  refine ⟨hsm.forall 4, ?_⟩
  refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4
    (Work.FTS.LocData.HkMem_const_mul α 4 (-2) h1) (fun z hz θ hθ => ?_)
  have hs : Work.Construction.s2 θ ≠ 0 := s2_ne_zero hθ
  have hD : Work.Spaces.Dth (Work.Construction.Fstar α) z θ
      = Work.Construction.s2 θ * Work.Spaces.pth (Work.Construction.Fstar α) z θ := by
    simp only [Work.Spaces.Dth, Work.Construction.s2]
  simp only [Work.FTS.Nonlin.N2gs, Work.FTS.Nonlin.PhiTg]
  rw [hD]
  field_simp
  try ring

/-- `N₂^{sg} = -2 𝒰(Φ̃_*)·∂_θ w = -2·(((z+1)/z)(Uop Φ̃_*/s2))·((z/(1+z))D_θ w)`. -/
theorem good_N2sg (hα : 0 < α) (hα1 : α ≤ 1)
    (hw : Work.FTS.ClassC.ClassC α w) (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N2sg α Φs w) := by
  obtain ⟨Cwv, _, hwprod⟩ := Work.FTS.OpenPkg.wprod_field_winf
  obtain ⟨Cm, _, hmulphi⟩ := Work.FTS.NonlinRows.NRow10aux.mul_phi_Hk
  have hmem5 : Work.Spaces.HkMem α 5 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 5 (by norm_num) hw.mem
  have hDthQ : Work.FTS.VocabO.HQo α 4 (Work.Spaces.Dth w) :=
    ⟨hw.reg.Dth, Work.FTS.StrongEps.ClassCRHS.hkMem_Dth_of_smoothOpen hα 4 hw.reg hmem5⟩
  have hPhi : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.PhiTs α Φs) :=
    Work.FTS.NonlinRows.NRow10aux.smoothOpen_PhiTs hα hα1 hstar.toStarPkgo
  have hreg := Work.FTS.PhiStar.StarPkgo2Aux.FieldRegularity α (Work.FTS.Nonlin.PhiTs α Φs) hPhi
  have hH1sm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z *
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Work.Construction.s2 θ)) :=
    hreg.2.2.2.2.1
  have hH1W : Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) / z *
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Work.Construction.s2 θ)) :=
    hstar.UszW.1
  have hH2sm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z / (1 + z) * Work.Spaces.Dth w z θ) :=
    so_mul so_zdiv hDthQ.1
  have hH2mem : Work.Spaces.HkMem α 4 (fun z θ => z / (1 + z) * Work.Spaces.Dth w z θ) :=
    (hmulphi hα hα1 hDthQ).1
  have h1 : Work.Spaces.HkMem α 4 (fun z θ => ((z + 1) / z *
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Work.Construction.s2 θ))
        * (z / (1 + z) * Work.Spaces.Dth w z θ)) :=
    (hwprod α hα hα1 _ _ hH1sm hH1W ⟨hH2sm, hH2mem⟩).1
  have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.Nonlin.N2sg α Φs w z θ
        = -2 * (((z + 1) / z *
              (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Work.Construction.s2 θ))
            * (z / (1 + z) * Work.Spaces.Dth w z θ)) := by
    intro z θ hz hθ hlt
    have hz0 : z ≠ 0 := ne_of_gt hz
    have h1z : (1 : ℝ) + z ≠ 0 := by linarith
    have hs : Work.Construction.s2 θ ≠ 0 := s2_ne_zero ⟨hθ, hlt⟩
    have hkey : (z + 1) / z * (z / (1 + z)) = (1 : ℝ) := by
      field_simp
      ring
    simp only [Work.FTS.Nonlin.N2sg]
    calc -2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
          * Work.Spaces.pth w z θ
        = -2 * ((Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
              / Work.Construction.s2 θ)
            * (Work.Construction.s2 θ * Work.Spaces.pth w z θ)) := by field_simp <;> ring
      _ = -2 * ((Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
              / Work.Construction.s2 θ)
            * (Work.Construction.s2 θ * Work.Spaces.pth w z θ))
            * ((z + 1) / z * (z / (1 + z))) := by rw [hkey]; ring
      _ = -2 * (((z + 1) / z *
              (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Work.Construction.s2 θ))
            * (z / (1 + z) * (Work.Construction.s2 θ * Work.Spaces.pth w z θ))) := by ring
  have hsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N2sg α Φs w) :=
    (Work.FTS.NonlinRows.smoothOpen_const_mul (-2) (so_mul hH1sm hH2sm)).congr
      (fun z θ hz hθ hlt => (hpt z θ hz hθ hlt).symm)
  refine ⟨hsm.forall 4, ?_⟩
  exact Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4
    (Work.FTS.LocData.HkMem_const_mul α 4 (-2) h1)
    (fun z hz θ hθ => (hpt z θ hz hθ.1 hθ.2).symm)

/-- `N₂^{**} = -2 𝒰(Φ̃_*)·∂_θF_*` (priced row 15). -/
theorem good_N2ss (hα : 0 < α) (hα1 : α ≤ 1)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N2ss α Φs) := by
  obtain ⟨_, _, hrow⟩ := Work.FTS.StrongPersist.L3Rhs.N2ssPriced
  have hPhi : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.PhiTs α Φs) :=
    Work.FTS.NonlinRows.NRow10aux.smoothOpen_PhiTs hα hα1 hstar.toStarPkgo
  have hFsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α
  have hsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N2ss α Φs) :=
    (so_mul (Work.FTS.NonlinRows.smoothOpen_const_mul (-2)
      (Work.FTS.NonlinRows.Rl1.smoothOpen_Uop_open hPhi)) hFsm.pth).congr
      (fun z θ _ _ _ => by simp only [Work.FTS.Nonlin.N2ss]; try ring_nf)
  exact ⟨hsm.forall 4, (hrow α ⟨hα, hα1⟩ Cs Φs hstar).1⟩

end Work.FTS.StrongEps.EpsZero.ClassCHk
