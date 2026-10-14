import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.Final.Assembly
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.GalFields.RHS.SharpAux.HonTerms.Base
import Submission.Work.FTS.NonlinRows.NAux3
import Submission.Work.FTS.Nonlinear.Pieces.rowsAux
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnN0
import Submission.Work.FTS.StrongEps.EpsE4Thr.DiagCurveIRho
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundR
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_LocDatum3a.Defs
import Submission.Work.FTS_RegExport.RXB.l12_aux
import Submission.Work.FTS_RegExport.RXR1.classC_sub_hyp
import Submission.Work.FTS_RegExport.RXT.velVanish2
import Submission.Work.FTS_RegExport.RXT.velVanish2Aux
import Submission.Work.FTS_RegExport.THL.cs7_rop_split
import Submission.Work.FTS_RegExport.THL.theta_holder_of_HkMem
import Submission.Work.FTS_RegExport.THL.vopPert_theta_holder
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.FTS.StrongEps.epsWP_hkMem4_bnd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.StrongEps

set_option maxHeartbeats 1600000

/-- Pointwise negation preserves `ℋ^k`-honesty. -/
theorem hkMem_neg_epsWP {α : ℝ} {k : ℕ} {f : Fn} (h : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α k (fun z θ => -f z θ) :=
  Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k
    (Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen (-1) h)
    (fun z θ _ _ => by ring)

/-- Pointwise negation preserves `SmoothOpen`. -/
theorem smoothOpen_neg_epsWP {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => -f z θ) :=
  Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => (hf.forall n).neg)

/-- **A uniform bound for the `μ̄`-coefficient of the scheme's right-hand side.**
`mubar (N₀) (N) = L₁₂(N₀)(0) + L₁₂(N)(0)`; both zero modes are priced by
`OpenPkg.l12zero_field` against the `ℋ⁴`-sizes of the two nonlinear blocks. -/
theorem epsWP_mubar_bound {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn → Fn}
    (hα : α ∈ Set.Ioc 0 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    ∃ CM : ℝ, 0 < CM ∧ ∀ w : Fn,
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      Work.Spaces.HkNorm α 6 w ≤ Ce →
      |Work.Construction.mubar
        (Work.Construction.N0 α (Work.Construction.Ftot α w) w)
        (Work.Construction.N α (Work.Construction.Ftot α w)
          (fun z θ => Φs z θ + E w z θ))| ≤ CM := by
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  obtain ⟨K0, hK0, hN0⟩ := ClassCRHS.HkMemXnN0 (α := α) hα (C₀ := C₀) (B := Ce)
  obtain ⟨K1, hK1, hN⟩ := ClassCRHS.HkMemXnN (α := α) hα (C₀ := C₀) (B := Ce) (Ce := Ce)
    (Cs := Cs) (Φs := Φs)
  obtain ⟨CZ, hCZ, hCZbd⟩ := Work.FTS.OpenPkg.l12zero_field
  refine ⟨CZ * (K0 + K1) + 1, by positivity, ?_⟩
  intro w hw hXw hBw
  have hellw : Work.FTS.VocabO.EllPkgGo α Ce w (E w) := (hEll w hw).1
  obtain ⟨_, _, _, hN0smo, hNsmo⟩ := ClassCRHS.SmoothOpenRHS hα0 hα1 hw hellw hstar
  obtain ⟨hmemN0, hbndN0⟩ := hN0 (w := w) hw hXw hBw
  obtain ⟨hmemN1, hbndN1⟩ := hN (w := w) (Φg := E w) hw hXw hBw hellw hstar
  have hN0Q : Work.FTS.VocabO.HQo α 4 (Work.Construction.N0 α (Work.Construction.Ftot α w) w) :=
    ⟨hN0smo, hmemN0⟩
  have hN1Q : Work.FTS.VocabO.HQo α 4
      (Work.Construction.N α (Work.Construction.Ftot α w) (fun z θ => Φs z θ + E w z θ)) :=
    ⟨hNsmo, hmemN1⟩
  have hL0 := hCZbd α hα0 hα1 _ hN0Q
  have hL1 := hCZbd α hα0 hα1 _ hN1Q
  have hmb : Work.Construction.mubar
      (Work.Construction.N0 α (Work.Construction.Ftot α w) w)
      (Work.Construction.N α (Work.Construction.Ftot α w) (fun z θ => Φs z θ + E w z θ))
      = Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α w) w) 0
        + Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α w)
            (fun z θ => Φs z θ + E w z θ)) 0 := rfl
  rw [hmb]
  have hstep : |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α w) w) 0|
        + |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α w)
            (fun z θ => Φs z θ + E w z θ)) 0| ≤ CZ * K0 + CZ * K1 :=
    add_le_add (le_trans hL0 (mul_le_mul_of_nonneg_left hbndN0 hCZ.le))
      (le_trans hL1 (mul_le_mul_of_nonneg_left hbndN1 hCZ.le))
  refine le_trans (abs_add_le _ _) ?_
  nlinarith [hstep, hCZ.le, hK0.le, hK1.le]

theorem epsWP_hkMem4_bnd {α C₀ Ce Cs T : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam} {ε : ℝ}
    (hα : α ∈ Set.Ioc 0 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
    (hC : ∀ s ∈ Set.Icc 0 T, Work.FTS.ClassC.ClassC α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s))
    (hb4 : ∀ s ∈ Set.Icc 0 T, Work.FTS.Nonlin.Xn α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s) ≤ C₀ * α ^ 2)
    (hb6 : ∀ s ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s) ≤ Ce) :
    ∃ KW : ℝ, 0 < KW ∧ ∀ s ∈ Set.Icc 0 T,
      Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s) ≤ KW := by
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  obtain ⟨Kl, hKl, hLGT⟩ := ClassCRHS.HkMemXnLGammaT (α := α) hα (C₀ := C₀) (B := Ce)
  obtain ⟨K0, hK0, hN0⟩ := ClassCRHS.HkMemXnN0 (α := α) hα (C₀ := C₀) (B := Ce)
  obtain ⟨KN, hKN, hN⟩ := ClassCRHS.HkMemXnN (α := α) hα (C₀ := C₀) (B := Ce) (Ce := Ce)
    (Cs := Cs) (Φs := Φs)
  obtain ⟨CM, hCM, hmub⟩ :=
    epsWP_mubar_bound (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (Φs := Φs) (E := E)
      hα hEll hstar
  obtain ⟨KAK, hKAK, hra⟩ := Work.FTS.Nonlinear.Pieces.rak_bound
  have hAKmem : Work.Spaces.HkMem α 4 (Work.Construction.AK α) :=
    Work.FTS.NonlinRows.HkMem_AK α hα0 hα1
  have hAKsmo : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.AK α) :=
    Work.FTS.StrongPersist.AK_smoothO α
  have hAKbd : Work.FTS.Nonlin.Xn α (Work.Construction.AK α) ≤ KAK := hra hα0 hα1
  set Lam : ℝ := 2 * CM * KAK + 1 with hLamdef
  set Kst : ℝ := 2 * ((1 / 2) * max (C₀ * α ^ 2) 0 + 2 * max Ce 0) + 1 with hKstdef
  have hLamnn : 0 ≤ Lam := by rw [hLamdef]; positivity
  have hKstnn : 0 ≤ Kst := by rw [hKstdef]; positivity
  have hKW : 0 < 16 * (Kl + Lam + K0 + KN + Kst) + 1 := by
    linarith [hKl, hLamnn, hK0, hKN, hKstnn]
  refine ⟨16 * (Kl + Lam + K0 + KN + Kst) + 1, hKW, ?_⟩
  intro s hs
  set w : Fn := slice (Work.FTS.StrongEps.JfamP ρ ε g) s with hwdef
  have hcls : Work.FTS.ClassC.ClassC α w := hC s hs
  have hXw : Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 := hb4 s hs
  have hBw : Work.Spaces.HkNorm α 6 w ≤ Ce := hb6 s hs
  have hwsmo : Work.FTS.EllipticEst.SmoothOpen w := hcls.reg
  have hw7 : Work.Spaces.HkMem α 7 w := hcls.mem
  have hw6 : Work.Spaces.HkMem α 6 w := Work.FTS.OpenPkg.HkMem_mono_open hwsmo 6 (by norm_num) hw7
  have hw5 : Work.Spaces.HkMem α 5 w := Work.FTS.OpenPkg.HkMem_mono_open hwsmo 5 (by norm_num) hw7
  have hw4 : Work.Spaces.HkMem α 4 w := Work.FTS.OpenPkg.HkMem_mono_open hwsmo 4 (by norm_num) hw7
  have hDzsmo : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz w) := hwsmo.Dz
  have hDz4 : Work.Spaces.HkMem α 4 (Work.Spaces.Dz w) :=
    Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α 4 hwsmo hw5
  have hXn5 : Work.FTS.GalFields.Xn5 α w ≤ Ce :=
    le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (α := α) (k := 6) (k' := 5)
      (by norm_num) hw6) hBw
  have hDzbd : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz w) ≤ Ce :=
    le_trans (Work.FTS.GalFields.Xn_Dz_le_Xn5 hα0 hwsmo hw5) hXn5
  have hellw : Work.FTS.VocabO.EllPkgGo α Ce w (E w) := (hEll w hcls).1
  obtain ⟨hmuOK, hlamOK⟩ := hml w hcls hXw
  obtain ⟨_, _, hLGTsmo, hN0smo, hNsmo⟩ :=
    ClassCRHS.SmoothOpenRHS hα0 hα1 hcls hellw hstar
  have hFtau : Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s
      = Work.Construction.Ftot α w := rfl
  have hPsis : slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g)) s
      = fun z θ => Φs z θ + E w z θ := rfl
  -- ### the five blocks of the right-hand side
  set P1 : Fn := Work.FTS.StrongPersist.linPart α w with hP1def
  set mb : ℝ := Work.Construction.mubar
    (Work.Construction.N0 α (Work.Construction.Ftot α w) w)
    (Work.Construction.N α (Work.Construction.Ftot α w)
      (fun z θ => Φs z θ + E w z θ)) with hmbdef
  set P2 : Fn := fun z θ => -mb * Work.Construction.AK α z θ with hP2def
  set P3 : Fn := Work.Construction.N0 α (Work.Construction.Ftot α w) w with hP3def
  set P4 : Fn := Work.Construction.N α (Work.Construction.Ftot α w)
    (fun z θ => Φs z θ + E w z θ) with hP4def
  set muU : ℝ := Work.FTS.Galerkin.muDyn α
    (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g))
    (Work.FTS.StrongEps.JfamP ρ ε g) s with hmuUdef
  set lamU : ℝ := Work.FTS.Galerkin.lamDyn α
    (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g))
    (Work.FTS.StrongEps.JfamP ρ ε g) s with hlamUdef
  set P5 : Fn := Work.Construction.Nstar muU lamU w with hP5def
  set A2 : Fn := fun z θ => P2 z θ + P3 z θ with hA2def
  set A3 : Fn := fun z θ => A2 z θ + P4 z θ with hA3def
  set A4 : Fn := fun z θ => P1 z θ + A3 z θ with hA4def
  set A5 : Fn := fun z θ => A4 z θ + P5 z θ with hA5def
  have hmuUbd : |muU| ≤ 1 / 2 := hmuOK
  have hlamUbd : |lamU| ≤ 1 := hlamOK
  -- ### the identification of `epsWP` with the block sum
  have hsplit : Work.FTS.StrongEps.epsWP α ρ ε Φs E g s = A5 := by
    funext z θ
    simp only [Work.FTS.StrongEps.epsWP, Work.FTS.Galerkin.dynLin, Work.FTS.Galerkin.dynRHS,
      Work.FTS.StrongPersist.linPart, Work.Construction.gRHS,
      Work.Construction.Nstar, Work.FTS.Galerkin.muDyn, Work.FTS.Galerkin.lamDyn,
      hP1def, hP2def, hP3def, hP4def, hP5def, hmbdef, hmuUdef, hlamUdef,
      hA2def, hA3def, hA4def, hA5def, hFtau, hPsis, hwdef]
    ring
  -- ### smoothness of the blocks
  have hP1smo : Work.FTS.EllipticEst.SmoothOpen P1 := by
    rw [hP1def]; exact smoothOpen_neg_epsWP hLGTsmo
  have hP2smo : Work.FTS.EllipticEst.SmoothOpen P2 := by
    rw [hP2def]; exact Work.FTS.NonlinRows.smoothOpen_const_mul (-mb) hAKsmo
  have hP3smo : Work.FTS.EllipticEst.SmoothOpen P3 := hN0smo
  have hP4smo : Work.FTS.EllipticEst.SmoothOpen P4 := hNsmo
  have hP5eq : P5 = fun z θ => (-muU) * w z θ
      + (-(muU + lamU + muU * lamU)) * Work.Spaces.Dz w z θ := by
    funext z θ
    rw [hP5def, Work.Construction.Nstar]
    ring
  have hP5smo : Work.FTS.EllipticEst.SmoothOpen P5 := by
    rw [hP5eq]
    exact Work.FTS.NonlinRows.smoothOpen_add
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-muU) hwsmo)
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-(muU + lamU + muU * lamU)) hDzsmo)
  -- ### membership of the blocks
  have hP1mem : Work.Spaces.HkMem α 4 P1 := by
    rw [hP1def]; exact hkMem_neg_epsWP (hLGT (w := w) hcls hXw hBw).1
  have hP2mem : Work.Spaces.HkMem α 4 P2 := by
    rw [hP2def]; exact Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen (-mb) hAKmem
  have hP3mem : Work.Spaces.HkMem α 4 P3 := (hN0 (w := w) hcls hXw hBw).1
  have hP4mem : Work.Spaces.HkMem α 4 P4 :=
    (hN (w := w) (Φg := E w) hcls hXw hBw hellw hstar).1
  have hP5mem : Work.Spaces.HkMem α 4 P5 := by
    rw [hP5eq]
    exact Work.FTS.EllipticEst.HkMem_add_open
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-muU) hwsmo)
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-(muU + lamU + muU * lamU)) hDzsmo)
      (Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen (-muU) hw4)
      (Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen (-(muU + lamU + muU * lamU)) hDz4)
  -- ### the bounds of the blocks
  have hmb_le : |mb| ≤ CM := by
    rw [hmbdef]; exact hmub w hcls hXw hBw
  have hP1bd : Work.FTS.Nonlin.Xn α P1 ≤ Kl := by
    rw [hP1def]
    show Work.Spaces.HkNorm α 4 (-(Work.Coercivity.LGammaT α w)) ≤ Kl
    rw [Work.FTS.EllipticEst.HkNorm_neg]
    exact (hLGT (w := w) hcls hXw hBw).2
  have hP2bd : Work.FTS.Nonlin.Xn α P2 ≤ Lam := by
    rw [hP2def]
    have h1 : Work.FTS.Nonlin.Xn α (fun z θ => -mb * Work.Construction.AK α z θ)
        = |mb| * Work.FTS.Nonlin.Xn α (Work.Construction.AK α) := by
      simpa only [abs_neg] using
        (Work.FTS.EllipticEst.HkNorm_const_mul (α := α) (k := 4) (c := -mb)
          (f := Work.Construction.AK α) hAKsmo.forall)
    rw [h1]
    have h2 : |mb| * Work.FTS.Nonlin.Xn α (Work.Construction.AK α) ≤ CM * KAK :=
      mul_le_mul hmb_le hAKbd (Work.Spaces.HkNorm_nonneg α 4 _) hCM.le
    rw [hLamdef]
    linarith [h2, hCM.le, hKAK.le]
  have hP3bd : Work.FTS.Nonlin.Xn α P3 ≤ K0 := (hN0 (w := w) hcls hXw hBw).2
  have hP4bd : Work.FTS.Nonlin.Xn α P4 ≤ KN :=
    (hN (w := w) (Φg := E w) hcls hXw hBw hellw hstar).2
  have hkapp : |muU + lamU + muU * lamU| ≤ 2 := by
    calc |muU + lamU + muU * lamU| ≤ |muU + lamU| + |muU * lamU| := abs_add_le _ _
      _ ≤ (|muU| + |lamU|) + |muU| * |lamU| :=
          add_le_add (abs_add_le _ _) (le_of_eq (abs_mul _ _))
      _ ≤ (1 / 2 + 1) + (1 / 2) * 1 :=
          add_le_add (add_le_add hmuUbd hlamUbd)
            (mul_le_mul hmuUbd hlamUbd (abs_nonneg _) (by norm_num))
      _ ≤ 2 := by norm_num
  have hP5bd : Work.FTS.Nonlin.Xn α P5 ≤ Kst := by
    rw [hP5eq]
    have hsum := Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα0
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-muU) hwsmo)
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-(muU + lamU + muU * lamU)) hDzsmo)
      (Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen (-muU) hw4)
      (Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen (-(muU + lamU + muU * lamU)) hDz4)
    have hc1 : Work.Spaces.HkNorm α 4 (fun z θ => (-muU) * w z θ)
        = |muU| * Work.FTS.Nonlin.Xn α w := by
      simpa only [abs_neg] using
        (Work.FTS.EllipticEst.HkNorm_const_mul (α := α) (k := 4) (c := -muU) (f := w)
          hwsmo.forall)
    have hc2 : Work.Spaces.HkNorm α 4
          (fun z θ => (-(muU + lamU + muU * lamU)) * Work.Spaces.Dz w z θ)
        = |muU + lamU + muU * lamU| * Work.FTS.Nonlin.Xn α (Work.Spaces.Dz w) := by
      simpa only [abs_neg] using
        (Work.FTS.EllipticEst.HkNorm_const_mul (α := α) (k := 4)
          (c := -(muU + lamU + muU * lamU)) (f := Work.Spaces.Dz w) hDzsmo.forall)
    refine le_trans hsum ?_
    rw [hc1, hc2]
    have hbr : |muU| * Work.FTS.Nonlin.Xn α w
          + |muU + lamU + muU * lamU| * Work.FTS.Nonlin.Xn α (Work.Spaces.Dz w)
        ≤ (1 / 2) * max (C₀ * α ^ 2) 0 + 2 * max Ce 0 :=
      add_le_add
        (mul_le_mul hmuUbd (le_trans hXw (le_max_left _ _))
          (Work.Spaces.HkNorm_nonneg α 4 w) (by norm_num))
        (mul_le_mul hkapp (le_trans hDzbd (le_max_left _ _))
          (Work.Spaces.HkNorm_nonneg α 4 (Work.Spaces.Dz w)) (by norm_num))
    rw [hKstdef]
    linarith [hbr]
  -- ### the assembly
  have hA2smo : Work.FTS.EllipticEst.SmoothOpen A2 :=
    Work.FTS.NonlinRows.smoothOpen_add hP2smo hP3smo
  have hA3smo : Work.FTS.EllipticEst.SmoothOpen A3 :=
    Work.FTS.NonlinRows.smoothOpen_add hA2smo hP4smo
  have hA4smo : Work.FTS.EllipticEst.SmoothOpen A4 :=
    Work.FTS.NonlinRows.smoothOpen_add hP1smo hA3smo
  have hA5smo : Work.FTS.EllipticEst.SmoothOpen A5 :=
    Work.FTS.NonlinRows.smoothOpen_add hA4smo hP5smo
  have hA2mem : Work.Spaces.HkMem α 4 A2 :=
    Work.FTS.EllipticEst.HkMem_add_open hP2smo hP3smo hP2mem hP3mem
  have hA3mem : Work.Spaces.HkMem α 4 A3 :=
    Work.FTS.EllipticEst.HkMem_add_open hA2smo hP4smo hA2mem hP4mem
  have hA4mem : Work.Spaces.HkMem α 4 A4 :=
    Work.FTS.EllipticEst.HkMem_add_open hP1smo hA3smo hP1mem hA3mem
  have hA5mem : Work.Spaces.HkMem α 4 A5 :=
    Work.FTS.EllipticEst.HkMem_add_open hA4smo hP5smo hA4mem hP5mem
  have hmem : Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s) := by
    rw [hsplit]; exact hA5mem
  have hbd : Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)
      ≤ 16 * (Kl + Lam + K0 + KN + Kst) + 1 := by
    rw [hsplit]
    have hb1 : Work.FTS.Nonlin.Xn α A5
        ≤ 2 * (Work.FTS.Nonlin.Xn α A4 + Work.FTS.Nonlin.Xn α P5) :=
      Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα0 hA4smo hP5smo hA4mem hP5mem
    have hb2 : Work.FTS.Nonlin.Xn α A4
        ≤ 2 * (Work.FTS.Nonlin.Xn α P1 + Work.FTS.Nonlin.Xn α A3) :=
      Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα0 hP1smo hA3smo hP1mem hA3mem
    have hb3 : Work.FTS.Nonlin.Xn α A3
        ≤ 2 * (Work.FTS.Nonlin.Xn α A2 + Work.FTS.Nonlin.Xn α P4) :=
      Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα0 hA2smo hP4smo hA2mem hP4mem
    have hb4 : Work.FTS.Nonlin.Xn α A2
        ≤ 2 * (Work.FTS.Nonlin.Xn α P2 + Work.FTS.Nonlin.Xn α P3) :=
      Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα0 hP2smo hP3smo hP2mem hP3mem
    have e4 : Work.FTS.Nonlin.Xn α A2 ≤ 2 * (Lam + K0) := by linarith [hb4, hP2bd, hP3bd]
    have e3 : Work.FTS.Nonlin.Xn α A3 ≤ 2 * (2 * (Lam + K0) + KN) := by
      linarith [hb3, e4, hP4bd]
    have e2 : Work.FTS.Nonlin.Xn α A4 ≤ 2 * (Kl + 2 * (2 * (Lam + K0) + KN)) := by
      linarith [hb2, hP1bd, e3]
    have e1 : Work.FTS.Nonlin.Xn α A5 ≤ 2 * (2 * (Kl + 2 * (2 * (Lam + K0) + KN)) + Kst) := by
      linarith [hb1, e2, hP5bd]
    linarith [e1, hKl.le, hLamnn, hK0.le, hKN.le, hKstnn]
  exact ⟨hmem, hbd⟩

end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.pth_vop_slot_bd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.pth_vop_slot_bd` — the `∂_θ`-slot of `𝒱(Φ̃(τ))` is bounded

For the modulated residual `Φ̃(τ) = v2_PhiT α Φs E g τ` of the RX-export interface, the
`θ`-derivative of the transport coefficient `𝒱(Φ̃) = ∂_θΦ̃ - tan θ · Φ̃` is bounded on the open
quadrant uniformly in `τ ∈ [0,S]`.

## Route

`v2_phiTil_split` (in `velVanish2Aux`) decomposes `Φ̃(τ) = Φ̃_* + Φ̃_pert` on the open quadrant
`Q0`, where `Φ̃_* = PhiTil (F_*) Φs` is the star residual and `Φ̃_pert = PhiTil (g(τ)) (E(g(τ)))`
is the perturbation residual.  Both pieces are smooth enough on `Q0` (`SmoothOpen Φ̃_*` from
`StarPkgo2`, `C³` for `Φ̃_pert` from `Sys.pert_tilde_contDiffOn`), so `∂_θ ∘ 𝒱` splits over the
sum (`pth_vop_add_of_split` below, built from the additivity of `pth`/`Vop` on `Q0`).

Each half is then priced by the *flat coefficient norm* `CoefTh` of `EllPkgGo`/`StarPkgo`:

* the star half `|∂_θ 𝒱(Φ̃_*)| ≤ Cs·α` is literally the `Vth` field of `StarPkgo2` read at
  order `0` (`abs_pth_le_coefTh`);
* the perturbation half `|∂_θ 𝒱(Φ̃_pert)| ≤ max Ce 0 · α^{-1/2} · (max C₀ 0 · α²)` is
  `Sys.vop_pert_pth_bd`, which prices the class-`C` approximants of `LimApprox` with the `Vth`
  field of `EllPkgGo` (and the uniform bound `Xn (g(τ)) ≤ C₀α²` of `DynOK'`) and passes to the
  limit along the jet convergence.

The two halves are added, giving `M = |Cs·α| + max Ce 0 · α^{-1/2} · (max C₀ 0 · α²)`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

set_option linter.unusedVariables false

namespace Work.FTS_RegExport.RXT.Sys

set_option autoImplicit false

/-! ## §1 The split of `∂_θ(𝒱 ·)` over a pointwise sum on the open quadrant -/

/-- The `θ`-derivative of `Vop Ψ` splits over a pointwise decomposition `Ψ = Ψ₁ + Ψ₂` of the
datum on the open quadrant, as soon as the two pieces are smooth enough (`Ψ₁` of class `C^∞`,
`Ψ₂` of class `C²`): both `pth` and `Vop` are additive on `Q0` for such data. -/
theorem pth_vop_add_of_split {Ψ Ψ₁ Ψ₂ : Work.FTS.Galerkin.Fn}
    (h₁ : Work.FTS.EllipticEst.SmoothOpen Ψ₁)
    (h₂ : ContDiffOn ℝ 2 (Function.uncurry Ψ₂) Work.FTS.EllipticEst.Q0)
    (hsplit : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → Ψ z θ = Ψ₁ z θ + Ψ₂ z θ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (Work.Construction.Vop Ψ) z θ
        = Work.Spaces.pth (Work.Construction.Vop Ψ₁) z θ
          + Work.Spaces.pth (Work.Construction.Vop Ψ₂) z θ := by
  intro z θ hz hθ hθ2
  have hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ2⟩
  -- additivity of `Vop` on the quadrant
  have hsum : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      Work.Construction.Vop Ψ z' θ'
        = Work.Construction.Vop Ψ₁ z' θ' + Work.Construction.Vop Ψ₂ z' θ' := by
    intro z' θ' hz' hθ' hθ'2
    have hzθ' : (z', θ') ∈ Work.FTS.EllipticEst.Q0 :=
      Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz', hθ', hθ'2⟩
    have h1c : ContDiffOn ℝ 1 (Function.uncurry Ψ₁) Work.FTS.EllipticEst.Q0 := h₁.forall 1
    have h2c : ContDiffOn ℝ 1 (Function.uncurry Ψ₂) Work.FTS.EllipticEst.Q0 :=
      h₂.of_le (by norm_num)
    calc Work.Construction.Vop Ψ z' θ'
        = Work.Construction.Vop (fun z θ => Ψ₁ z θ + Ψ₂ z θ) z' θ' :=
          Work.FTS.GalFields.RHS.Sharp.Vop_congr_Q0 hsplit z' θ' hz' hθ' hθ'2
      _ = Work.Construction.Vop Ψ₁ z' θ' + Work.Construction.Vop Ψ₂ z' θ' :=
          Work.FTS_RegExport.RXT.v2_vop_add_at h1c h2c hzθ'
  -- `pth` only sees the quadrant
  have hcongr : Work.Spaces.pth (Work.Construction.Vop Ψ) z θ
      = Work.Spaces.pth (fun z θ =>
          Work.Construction.Vop Ψ₁ z θ + Work.Construction.Vop Ψ₂ z θ) z θ :=
    Work.FTS.PhiStar.CoreAux.pth_congr_Q0 hsum z θ hz hθ hθ2
  -- additivity of `pth` on the two `Vop`-pieces
  have hV1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Construction.Vop Ψ₁))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.NonlinRows.smoothOpen_Vop h₁).forall 1
  have hV2 : ContDiffOn ℝ 1 (Function.uncurry (Work.Construction.Vop Ψ₂))
      Work.FTS.EllipticEst.Q0 := by
    have hp : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth Ψ₂))
        Work.FTS.EllipticEst.Q0 :=
      Work.FTS.StrongEps.contDiffOn_uncurry_pth_fin Work.FTS.EllipticEst.isOpen_Q0
        (h₂.of_le (by norm_num))
    have htan : ContDiffOn ℝ 1 (Function.uncurry (fun z θ : ℝ => Real.tan θ * Ψ₂ z θ))
        Work.FTS.EllipticEst.Q0 := by
      have h1 : ContDiffOn ℝ 1 (Function.uncurry (fun _ : ℝ => fun (θ : ℝ) => Real.tan θ))
          Work.FTS.EllipticEst.Q0 := (Work.FTS.NonlinRows.smoothOpen_tan).forall 1
      have h2 : ContDiffOn ℝ 1 (Function.uncurry Ψ₂) Work.FTS.EllipticEst.Q0 :=
        h₂.of_le (by norm_num)
      refine (h1.mul h2).congr (f₁ := Function.uncurry (fun _ : ℝ => fun (θ : ℝ) => Real.tan θ)
        * Function.uncurry Ψ₂) ?_
      intro p _
      rcases p with ⟨z', θ'⟩
      simp only [Function.uncurry, Pi.mul_apply]
    have hsame : Function.uncurry (Work.Construction.Vop Ψ₂)
        = (Function.uncurry (Work.Spaces.pth Ψ₂))
          - (Function.uncurry (fun z θ : ℝ => Real.tan θ * Ψ₂ z θ)) := by
      funext p
      rcases p with ⟨z', θ'⟩
      simp only [Function.uncurry, Work.Construction.Vop, Pi.sub_apply]
    rw [hsame]
    exact hp.sub htan
  exact hcongr.trans (Work.FTS_RegExport.RXT.v2_pth_add_at hV1 hV2 hzθ)

/-! ## §2 The target -/

theorem pth_vop_slot_bd {α Ce C₀ Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g) :
    ∀ S > 0, ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ z θ, 0 < z → 0 < θ →
      θ < Real.pi / 2 →
      |Work.Spaces.pth (fun z θ => Work.Construction.Vop
          (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ) z θ) z θ| ≤ M := by
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  intro S hS
  refine ⟨|Cs * Work.FTS.Regularity.pExp α|
    + max Ce 0 * (Work.FTS.Regularity.pExp α) ^ (-(1 / 2 : ℝ))
      * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2), ?_, ?_⟩
  · refine add_nonneg (abs_nonneg _) (mul_nonneg (mul_nonneg (le_max_right _ _) ?_) ?_)
    · exact Real.rpow_nonneg (le_of_lt hαG) _
    · exact mul_nonneg (le_max_right _ _) (sq_nonneg _)
  · intro τ hτ z θ hz hθ hθ2
    -- the star half: the `Vth` field of `StarPkgo2` read at order `0`
    have hstar : |Work.Spaces.pth (Work.Construction.Vop
        (Work.FTS_RegExport.RXT.v2_PhiStar α Φs)) z θ| ≤ |Cs * Work.FTS.Regularity.pExp α| := by
      have h1 : |Work.Spaces.pth (Work.Construction.Vop (Work.Construction.PhiTil
          (Work.FTS.Regularity.pExp α) (Work.Construction.Fstar (Work.FTS.Regularity.pExp α))
          Φs)) z θ| ≤ Cs * Work.FTS.Regularity.pExp α :=
        (Work.FTS.StrongPersist.H6Rows.abs_pth_le_coefTh hStar.Vth.1 z θ hz hθ hθ2).trans
          hStar.Vth.2
      simpa only [Work.FTS_RegExport.RXT.v2_PhiStar] using h1.trans (le_abs_self _)
    -- the perturbation half: `Sys.vop_pert_pth_bd`
    have hpert : |Work.Spaces.pth (Work.Construction.Vop
        (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ)) z θ|
        ≤ max Ce 0 * (Work.FTS.Regularity.pExp α) ^ (-(1 / 2 : ℝ))
          * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) := by
      simpa only [Work.FTS_RegExport.RXT.v2_PhiPert] using
        vop_pert_pth_bd (α := α) (Ce := Ce) (C₀ := C₀) hα hα13 hEll hEL3 hOK S hS τ hτ
          z θ hz hθ hθ2
    -- the split of `∂_θ(Vop ·)` over `Φ̃ = Φ̃_* + Φ̃_pert` on the open quadrant
    have hsplit : Work.Spaces.pth (Work.Construction.Vop
        (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ)) z θ
        = Work.Spaces.pth (Work.Construction.Vop
            (Work.FTS_RegExport.RXT.v2_PhiStar α Φs)) z θ
          + Work.Spaces.pth (Work.Construction.Vop
            (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ)) z θ := by
      refine pth_vop_add_of_split (Ψ := Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ)
        (Ψ₁ := Work.FTS_RegExport.RXT.v2_PhiStar α Φs)
        (Ψ₂ := Work.FTS_RegExport.RXT.v2_PhiPert α E g τ) ?_ ?_ ?_ z θ hz hθ hθ2
      · exact Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil_star hαG hαG1 hStar
      · exact (pert_tilde_contDiffOn (α := α) (C₀ := C₀) hα hα13 hEL3 hOK τ hτ.1).of_le
          (by norm_num)
      · intro z' θ' hz' hθ' hθ'2
        exact Work.FTS_RegExport.RXT.v2_phiTil_split (C₀ := C₀) hα hα13 hOK hτ.1 z' θ'
          (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz', hθ', hθ'2⟩)
    calc |Work.Spaces.pth (fun z θ => Work.Construction.Vop
          (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ) z θ) z θ|
        = |Work.Spaces.pth (Work.Construction.Vop
            (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ)) z θ| := rfl
      _ = |Work.Spaces.pth (Work.Construction.Vop
            (Work.FTS_RegExport.RXT.v2_PhiStar α Φs)) z θ
          + Work.Spaces.pth (Work.Construction.Vop
            (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ)) z θ| := by rw [hsplit]
      _ ≤ |Work.Spaces.pth (Work.Construction.Vop
            (Work.FTS_RegExport.RXT.v2_PhiStar α Φs)) z θ|
          + |Work.Spaces.pth (Work.Construction.Vop
            (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ)) z θ| := abs_add_le _ _
      _ ≤ |Cs * Work.FTS.Regularity.pExp α|
          + max Ce 0 * (Work.FTS.Regularity.pExp α) ^ (-(1 / 2 : ℝ))
            * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) := add_le_add hstar hpert

end Work.FTS_RegExport.RXT.Sys
end
end
