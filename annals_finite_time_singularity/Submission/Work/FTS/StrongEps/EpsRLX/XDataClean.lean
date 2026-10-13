/-
Copyright: work module for the Elgindi finite-time singularity project.

# `EpsRLX/XDataClean.lean` — `XData` in the *import cone of the target*

`EpsRLX/XData.lean` proves the same statement (`XData`, the profile-only uniform a-priori data of
the pre-mollified right-hand side `profRHS`), but it imports `EpsLocalPStar/EpsRHSPBdd.lean`
(for the single auxiliary lemma `hkMem_neg_fts`), which transitively imports
`EpsGdotThird.lean` and hence `Gdot.lean`, where `Work.FTS.StrongEps.epsW` is *redefined* (the
second, conflicting definition of `Gdot.lean:64`).  Any module importing both `EpsSpace.lean` and
`Gdot.lean` dies at the import line (`environment already contains
'Work.FTS.StrongEps.epsW'`), and the target `EpsRHSPLipXProof.lean` must import `EpsSpace.lean`
(`EpsSq`, `EpsMem`, …).  This file is therefore a copy of `XData.lean` with

* the `EpsRHSPBdd` import dropped (its only use, `hkMem_neg_fts`, is replaced by
  `Work.FTS.NonlinRows.HkMem_neg'`, which has the same statement), and
* the explicit imports of the modules that `EpsRHSPBdd` had been supplying implicitly
  (`AK6Row` for `StrongPersist.AK_smoothO`, `OpenPkg.l12zero_field`, …),

so that the same proof goes through with an `EpsSpace`-compatible cone.

The statement and the proof body are those of `XData.lean`, byte for byte.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnN0
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnN
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnLGammaT
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsRHSXrhs
import Submission.Work.FTS.StrongEps.EpsLimitDefs
import Submission.Work.FTS.StrongEps.EpsLocalPSmall
import Submission.Work.FTS.StrongEps.HkSq_Jeps_step_le
import Submission.Work.FTS.StrongEps.EpsE4Thr.HkMem_Jeps_gain
import Submission.Work.FTS.StrongEps.PZeroAux.PzHkNormFour
import Submission.Work.FTS.StrongEps.PZeroAux.classC_Pz
import Submission.Work.FTS.StrongEps.JfamP_norm
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.GalFields.Norm.Basic
import Submission.Work.FTS.OpenPkg.l12zero_field
import Submission.Work.FTS.Nonlinear.Pieces.rowsAux
import Submission.Work.FTS.NonlinRows.NAux3
import Submission.Work.FTS.StrongPersist.H6Rows.AK6Row
import Submission.Work.FTS.CoercivityFix.Transfer.HkMem_descent_Q0Sm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX

set_option maxHeartbeats 2400000

theorem XDataClean {α Ce Cs C₀ B : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hα : α ∈ Set.Ioc 0 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hB : 0 ≤ B) :
    ∃ R : ℝ, 0 < R ∧ ∀ {W : Work.FTS.Galerkin.Fn}, Work.FTS.ClassC.ClassC α W →
      Work.FTS.Nonlin.Xn α W ≤ C₀ * α ^ 2 → Work.Spaces.HkNorm α 6 W ≤ B →
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W) ∧
      Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W) ∧
      Work.Spaces.HkSq α 4 (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W) ≤ R := by
  classical
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  -- ## the constants of the three block estimates
  obtain ⟨K1, hK1, hLGT⟩ :=
    Work.FTS.StrongEps.ClassCRHS.HkMemXnLGammaT (α := α) hα (C₀ := C₀) (B := B)
  obtain ⟨K2, hK2, hN0⟩ :=
    Work.FTS.StrongEps.ClassCRHS.HkMemXnN0 (α := α) hα (C₀ := C₀) (B := B)
  obtain ⟨K3, hK3, hN⟩ := Work.FTS.StrongEps.ClassCRHS.HkMemXnN (α := α) hα (C₀ := C₀) (B := B)
    (Ce := Ce) (Cs := Cs) (Φs := Φs)
  obtain ⟨KAK, hKAK, hra⟩ := Work.FTS.Nonlinear.Pieces.rak_bound
  have hAKmem : Work.Spaces.HkMem α 4 (Work.Construction.AK α) :=
    Work.FTS.NonlinRows.HkMem_AK α hα0 hα1
  have hAKbd : Work.FTS.Nonlin.Xn α (Work.Construction.AK α) ≤ KAK := hra hα0 hα1
  have hAKsmo : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.AK α) :=
    Work.FTS.StrongPersist.AK_smoothO α
  obtain ⟨CL, hCL, hl12z⟩ := Work.FTS.OpenPkg.l12zero_field
  have hCLnn : 0 ≤ CL := hCL.le
  set Lam : ℝ := max (2 * CL * (K2 + K3) * KAK) 0 with hLamdef
  set Nst : ℝ := max (2 * ((1 / 2) * (C₀ * α ^ 2) + 2 * B)) 0 with hNstdef
  set KX : ℝ := 16 * (K1 + Lam + K2 + K3 + Nst) with hKXdef
  have hKXnn : 0 ≤ KX := by
    rw [hKXdef]
    have h1 : 0 ≤ K1 := hK1.le
    have hL0 : 0 ≤ Lam := le_max_right _ _
    have hN0' : 0 ≤ Nst := le_max_right _ _
    have h2 : 0 ≤ K2 := hK2.le
    have h3 : 0 ≤ K3 := hK3.le
    linarith
  refine ⟨KX ^ 2 + 1, by positivity, ?_⟩
  intro W hwC hw4 hw6
  -- ## the data of `W`
  have hwSmo : Work.FTS.EllipticEst.SmoothOpen W := hwC.reg
  have hwMem6 : Work.Spaces.HkMem α 6 W :=
    Work.FTS.OpenPkg.HkMem_mono_open hwC.reg 6 (by norm_num) hwC.mem
  have hwMem5 : Work.Spaces.HkMem α 5 W :=
    Work.FTS.OpenPkg.HkMem_mono_open hwC.reg 5 (by norm_num) hwC.mem
  have hwMem4 : Work.Spaces.HkMem α 4 W :=
    Work.FTS.OpenPkg.HkMem_mono_open hwC.reg 4 (by norm_num) hwC.mem
  have hw5 : Work.Spaces.HkNorm α 5 W ≤ B :=
    le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 6) (k' := 5) (by norm_num)
      hwMem6) hw6
  have hDzmem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz W) :=
    (Work.FTS.CoercivityFix.Transfer.HkMem_descent_Q0Sm α hα0 4 (hwSmo.forall 5) hwMem5).2.2
  have hDzbd : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz W) ≤ B :=
    le_trans (Work.FTS.GalFields.Xn_Dz_le_Xn5 hα0 hwSmo hwMem5) hw5
  -- ## the elliptic package and the modulation bounds
  have hEllw : Work.FTS.VocabO.EllPkgGo α Ce W (E W) := (hEll W hwC).1
  have hmu0 := (hml W hwC hw4).1
  have hlam0 := (hml W hwC hw4).2
  -- ## the pieces of `X`
  set X : Work.FTS.Galerkin.Fn := Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W with hXdef
  set muU : ℝ := Work.FTS.Galerkin.muDyn α
      (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.Galerkin.famOf (fun _ : ℝ => W)))
      (Work.FTS.Galerkin.famOf (fun _ => W)) 0 with hmuUdef
  set lamU : ℝ := Work.FTS.Galerkin.lamDyn α
      (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.Galerkin.famOf (fun _ : ℝ => W)))
      (Work.FTS.Galerkin.famOf (fun _ => W)) 0 with hlamUdef
  have hmuU : |muU| ≤ 1 / 2 := by rw [hmuUdef]; exact hmu0
  have hlamU : |lamU| ≤ 1 := by rw [hlamUdef]; exact hlam0
  set mb : ℝ := Work.Construction.mubar
      (Work.Construction.N0 α (Work.Construction.Ftot α W) W)
      (Work.Construction.N α (Work.Construction.Ftot α W)
        (fun z θ => Φs z θ + E W z θ)) with hmb
  set P1 : Work.FTS.Galerkin.Fn := Work.FTS.StrongPersist.linPart α W with hP1
  set P2 : Work.FTS.Galerkin.Fn := fun z θ => -mb * Work.Construction.AK α z θ with hP2
  set P3 : Work.FTS.Galerkin.Fn :=
    Work.Construction.N0 α (Work.Construction.Ftot α W) W with hP3
  set P4 : Work.FTS.Galerkin.Fn := Work.Construction.N α (Work.Construction.Ftot α W)
      (fun z θ => Φs z θ + E W z θ) with hP4
  set P5 : Work.FTS.Galerkin.Fn := Work.Construction.Nstar muU lamU W with hP5
  have hXsplit : X = (P1 + ((P2 + P3) + P4)) + P5 := by
    funext z θ
    simp only [hXdef, Work.FTS.StrongEps.EpsLocalPStar.profRHS, hP1, hP2, hP3, hP4, hP5, hmb,
      hmuUdef, hlamUdef, Work.FTS.StrongPersist.rhsOf, Work.Construction.gRHS, Pi.add_apply]
    ring
  -- ## smoothness of the pieces
  obtain ⟨hL12totSmo, hFKtotSmo, hLGTsmo, hN0smo, hNsmo⟩ :=
    Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS hα0 hα1 hwC hEllw hstar
  have hP1smo : Work.FTS.EllipticEst.SmoothOpen P1 := by
    show Work.FTS.EllipticEst.SmoothOpen (-(Work.Coercivity.LGammaT α W))
    exact hLGTsmo.neg
  have hP2smo : Work.FTS.EllipticEst.SmoothOpen P2 := by
    rw [hP2]
    exact Work.FTS.StrongEps.PZeroAux.smoothOpen_const_mul_gen (-mb) hAKsmo
  have hP3smo : Work.FTS.EllipticEst.SmoothOpen P3 := hN0smo
  have hP4smo : Work.FTS.EllipticEst.SmoothOpen P4 := hNsmo
  have hP5eq : P5 = fun z θ => (-muU) * W z θ
      + (-(muU + lamU + muU * lamU)) * Work.Spaces.Dz W z θ := by
    funext z θ
    rw [hP5, Work.Construction.Nstar]
    ring
  have hP5smo : Work.FTS.EllipticEst.SmoothOpen P5 := by
    rw [hP5eq]
    exact Work.FTS.NonlinRows.smoothOpen_add
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-muU) hwSmo)
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-(muU + lamU + muU * lamU)) hwSmo.Dz)
  -- ## membership of the pieces
  have hP1mem : Work.Spaces.HkMem α 4 P1 := by
    show Work.Spaces.HkMem α 4 (-(Work.Coercivity.LGammaT α W))
    exact Work.FTS.NonlinRows.HkMem_neg' α 4 (hLGT (w := W) hwC hw4 hw6).1
  have hP2mem : Work.Spaces.HkMem α 4 P2 := by
    rw [hP2]
    exact Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen (-mb) hAKmem
  have hP3mem : Work.Spaces.HkMem α 4 P3 := by
    simpa only [hP3] using (hN0 (w := W) hwC hw4 hw6).1
  have hP4mem : Work.Spaces.HkMem α 4 P4 := by
    simpa only [hP4] using (hN (w := W) (Φg := E W) hwC hw4 hw6 hEllw hstar).1
  have hP5mem : Work.Spaces.HkMem α 4 P5 := by
    rw [hP5eq]
    exact Work.FTS.EllipticEst.HkMem_add_open
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-muU) hwSmo)
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-(muU + lamU + muU * lamU)) hwSmo.Dz)
      (Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen (-muU) hwMem4)
      (Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen (-(muU + lamU + muU * lamU)) hDzmem)
  -- ## the bounds of the pieces
  have hP1bd : Work.FTS.Nonlin.Xn α P1 ≤ K1 := by
    show Work.Spaces.HkNorm α 4 (-(Work.Coercivity.LGammaT α W)) ≤ K1
    rw [Work.FTS.EllipticEst.HkNorm_neg]
    exact (hLGT (w := W) hwC hw4 hw6).2
  have hP3bd : Work.FTS.Nonlin.Xn α P3 ≤ K2 := by
    simpa only [hP3] using (hN0 (w := W) hwC hw4 hw6).2
  have hP4bd : Work.FTS.Nonlin.Xn α P4 ≤ K3 := by
    simpa only [hP4] using (hN (w := W) (Φg := E W) hwC hw4 hw6 hEllw hstar).2
  have hmubar : |mb| ≤ CL * (K2 + K3) := by
    rw [hmb, Work.Construction.mubar]
    have h1 : |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W) W) 0|
        ≤ CL * Work.FTS.Nonlin.Xn α P3 := hl12z α hα0 hα1 P3 ⟨hP3smo, hP3mem⟩
    have h2 : |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W)
          (fun z θ => Φs z θ + E W z θ)) 0| ≤ CL * Work.FTS.Nonlin.Xn α P4 :=
      hl12z α hα0 hα1 P4 ⟨hP4smo, hP4mem⟩
    have h3 : Work.FTS.Nonlin.Xn α P3 ≤ K2 := hP3bd
    have h4 : Work.FTS.Nonlin.Xn α P4 ≤ K3 := hP4bd
    calc |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W) W) 0
            + Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W)
              (fun z θ => Φs z θ + E W z θ)) 0|
        ≤ |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W) W) 0|
          + |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W)
              (fun z θ => Φs z θ + E W z θ)) 0| := abs_add_le _ _
      _ ≤ CL * K2 + CL * K3 := add_le_add
          (le_trans h1 (mul_le_mul_of_nonneg_left h3 hCLnn))
          (le_trans h2 (mul_le_mul_of_nonneg_left h4 hCLnn))
      _ = CL * (K2 + K3) := by ring
  have hP2bd : Work.FTS.Nonlin.Xn α P2 ≤ Lam := by
    have h1 : Work.FTS.Nonlin.Xn α P2
        = |mb| * Work.FTS.Nonlin.Xn α (Work.Construction.AK α) := by
      rw [hP2, Work.FTS.Nonlin.Xn,
        Work.FTS.EllipticEst.HkNorm_const_mul (α := α) (k := 4) (c := -mb) hAKsmo.forall,
        abs_neg]
    rw [h1]
    have h2 : |mb| * Work.FTS.Nonlin.Xn α (Work.Construction.AK α)
        ≤ (CL * (K2 + K3)) * KAK :=
      mul_le_mul hmubar hAKbd (Work.Spaces.HkNorm_nonneg _ _ _)
        (le_trans (abs_nonneg _) hmubar)
    have hnn : 0 ≤ (CL * (K2 + K3)) * KAK :=
      mul_nonneg (mul_nonneg hCLnn (by linarith [hK2.le, hK3.le])) hKAK.le
    rw [hLamdef]
    refine le_trans (le_trans h2 ?_) (le_max_left _ _)
    nlinarith [hnn]
  have hP5bd : Work.FTS.Nonlin.Xn α P5 ≤ Nst := by
    rw [hP5eq]
    have hb1 : Work.Spaces.HkNorm α 4 (fun z θ => (-muU) * W z θ)
        = |muU| * Work.FTS.Nonlin.Xn α W := by
      rw [Work.FTS.EllipticEst.HkNorm_const_mul (α := α) (k := 4) (c := -muU) hwSmo.forall,
        abs_neg]
    have hb2 : Work.Spaces.HkNorm α 4
        (fun z θ => (-(muU + lamU + muU * lamU)) * Work.Spaces.Dz W z θ)
        = |muU + lamU + muU * lamU| * Work.FTS.Nonlin.Xn α (Work.Spaces.Dz W) := by
      rw [Work.FTS.EllipticEst.HkNorm_const_mul (α := α) (k := 4)
        (c := -(muU + lamU + muU * lamU)) hwSmo.Dz.forall, abs_neg]
    have hsum := Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα0
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-muU) hwSmo)
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-(muU + lamU + muU * lamU)) hwSmo.Dz)
      (Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen (-muU) hwMem4)
      (Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen (-(muU + lamU + muU * lamU)) hDzmem)
    have hkapp : |muU + lamU + muU * lamU| ≤ 2 := by
      have h1 : |muU| ≤ 1 / 2 := hmuU
      have h2 : |lamU| ≤ 1 := hlamU
      calc |muU + lamU + muU * lamU| ≤ |muU + lamU| + |muU * lamU| := abs_add_le _ _
        _ ≤ (|muU| + |lamU|) + |muU| * |lamU| := by
            refine add_le_add (abs_add_le _ _) (le_of_eq (abs_mul _ _))
        _ ≤ (1 / 2 + 1) + (1 / 2) * 1 := by
            refine add_le_add (add_le_add h1 h2) ?_
            exact mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
        _ = 2 := by norm_num
    have hstep : Work.Spaces.HkNorm α 4 (fun z θ => (-muU) * W z θ
        + (-(muU + lamU + muU * lamU)) * Work.Spaces.Dz W z θ)
        ≤ 2 * ((1 / 2) * (C₀ * α ^ 2) + 2 * B) := by
      refine le_trans hsum ?_
      rw [hb1, hb2]
      refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by norm_num)
      · exact mul_le_mul hmuU hw4 (Work.Spaces.HkNorm_nonneg _ _ _) (by norm_num)
      · exact mul_le_mul hkapp hDzbd (Work.Spaces.HkNorm_nonneg _ _ _) (by norm_num)
    rw [hNstdef]
    exact le_trans hstep (le_max_left _ _)
  -- ## the assembly of the pieces
  have hP23smo : Work.FTS.EllipticEst.SmoothOpen (P2 + P3) :=
    Work.FTS.NonlinRows.smoothOpen_add hP2smo hP3smo
  have hAsm1smo : Work.FTS.EllipticEst.SmoothOpen ((P2 + P3) + P4) :=
    Work.FTS.NonlinRows.smoothOpen_add hP23smo hP4smo
  have hAsm2smo : Work.FTS.EllipticEst.SmoothOpen (P1 + ((P2 + P3) + P4)) :=
    Work.FTS.NonlinRows.smoothOpen_add hP1smo hAsm1smo
  have hP23mem : Work.Spaces.HkMem α 4 (P2 + P3) :=
    Work.FTS.EllipticEst.HkMem_add_open hP2smo hP3smo hP2mem hP3mem
  have hAsm1mem : Work.Spaces.HkMem α 4 ((P2 + P3) + P4) :=
    Work.FTS.EllipticEst.HkMem_add_open hP23smo hP4smo hP23mem hP4mem
  have hAsm2mem : Work.Spaces.HkMem α 4 (P1 + ((P2 + P3) + P4)) :=
    Work.FTS.EllipticEst.HkMem_add_open hP1smo hAsm1smo hP1mem hAsm1mem
  -- ## the bound of `X`
  have hXbd : Work.FTS.Nonlin.Xn α X ≤ KX := by
    have hb1 : Work.FTS.Nonlin.Xn α ((P1 + ((P2 + P3) + P4)) + P5)
        ≤ 2 * (Work.FTS.Nonlin.Xn α (P1 + ((P2 + P3) + P4)) + Work.FTS.Nonlin.Xn α P5) :=
      Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα0 hAsm2smo hP5smo hAsm2mem hP5mem
    have hb2 : Work.FTS.Nonlin.Xn α (P1 + ((P2 + P3) + P4))
        ≤ 2 * (Work.FTS.Nonlin.Xn α P1 + Work.FTS.Nonlin.Xn α ((P2 + P3) + P4)) :=
      Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα0 hP1smo hAsm1smo hP1mem hAsm1mem
    have hb3 : Work.FTS.Nonlin.Xn α ((P2 + P3) + P4)
        ≤ 2 * (Work.FTS.Nonlin.Xn α (P2 + P3) + Work.FTS.Nonlin.Xn α P4) :=
      Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα0 hP23smo hP4smo hP23mem hP4mem
    have hb4 : Work.FTS.Nonlin.Xn α (P2 + P3)
        ≤ 2 * (Work.FTS.Nonlin.Xn α P2 + Work.FTS.Nonlin.Xn α P3) :=
      Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα0 hP2smo hP3smo hP2mem hP3mem
    have e4 : Work.FTS.Nonlin.Xn α (P2 + P3) ≤ 2 * (Lam + K2) := by linarith
    have e3 : Work.FTS.Nonlin.Xn α ((P2 + P3) + P4) ≤ 2 * (2 * (Lam + K2) + K3) := by linarith
    have e2 : Work.FTS.Nonlin.Xn α (P1 + ((P2 + P3) + P4))
        ≤ 2 * (K1 + 2 * (2 * (Lam + K2) + K3)) := by linarith
    have e1 : Work.FTS.Nonlin.Xn α ((P1 + ((P2 + P3) + P4)) + P5)
        ≤ 2 * (2 * (K1 + 2 * (2 * (Lam + K2) + K3)) + Nst) := by linarith
    rw [hXsplit]
    refine le_trans e1 ?_
    rw [hKXdef]
    linarith [hK1.le, hK2.le, hK3.le, le_max_right (2 * CL * (K2 + K3) * KAK) 0,
      le_max_right (2 * ((1 / 2) * (C₀ * α ^ 2) + 2 * B)) 0]
  -- ## `X` is smooth and honest
  have hXsmo : Work.FTS.EllipticEst.SmoothOpen X := by
    rw [hXsplit]
    exact Work.FTS.NonlinRows.smoothOpen_add hAsm2smo hP5smo
  have hXmem : Work.Spaces.HkMem α 4 X := by
    rw [hXsplit]
    exact Work.FTS.EllipticEst.HkMem_add_open hAsm2smo hP5smo hAsm2mem hP5mem
  -- ## the squared bound
  have hXsq : Work.Spaces.HkSq α 4 X ≤ KX ^ 2 + 1 := by
    have h1 : Work.Spaces.HkSq α 4 X = (Work.FTS.Nonlin.Xn α X) ^ 2 := by
      rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm,
        Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 X)]
    rw [h1]
    have h2 : (Work.FTS.Nonlin.Xn α X) ^ 2 ≤ KX ^ 2 :=
      pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 X) hXbd 2
    linarith
  exact ⟨hXsmo, hXmem, hXsq⟩

end Work.FTS.StrongEps.EpsRLX
