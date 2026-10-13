/-
# `H5/Asm` — the assembly of the `ℋ⁵`-bound for `epsWP` from the three block estimates

`epsWP α ρ ε Φs E g s` splits (definitionally) into the five blocks of the level-four proof:

  `P1 = -𝓛_Γ^T w`,  `P2 = -μ̄·AK α`,  `P3 = N₀`,  `P4 = N`,  `P5 = N_*`,

where `w = slice (JfamP ρ ε g) s`.  This module assembles the level-`5` estimate

  `HkMem α 5 (epsWP α ρ ε Φs E g s) ∧ HkNorm α 5 (epsWP …) ≤ KW`

from the three *block* estimates

* `hLGT` (`P1`, the level-`5` `𝓛_Γ^T` estimate),
* `hN0` (`P3`, the level-`5` `N₀` estimate),
* `hNb` (`P4`, the level-`5` `N` estimate),

together with the two elementary blocks `P2` (a fixed `ℋ⁶`-profile `AK α`, bounded at level five by
`AK6_mem_norm`) and `P5` (`N_*`, a linear combination of `w` and `D_z w`, bounded by `Xn6 α w ≤ Ce`).
The two remaining inputs are the `μ̄`-bound `epsWP_mubar_bound` and the `SmoothOpen`-package
`SmoothOpenRHS`, both already proved.

Separating the block estimates from the assembly keeps the three hard chapters independent; the
instantiation is one line each.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.StrongEps.H5.DataW
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.epsWP_hkMem4_bnd_fam
import Submission.Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS.StrongPersist.StarPkg6OfCore
import Submission.Work.FTS.StrongPersist.H6Rows.AK6Row
import Submission.Work.FTS.IPGen.OpenBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The level-`5` bound for `epsWP`, from the three block estimates.** -/
theorem epsWP_hkMem5_bnd_unif_of_blocks
    {α C₀ Ce Cs6 T Kl K0 KN : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar6 : Work.FTS.StrongPersist.StarPkg6 α Cs6 Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
    (hKl : 0 < Kl) (hK0 : 0 < K0) (hKN : 0 < KN)
    (hLGT : ∀ {w : Fn}, Work.FTS.ClassC.ClassC α w →
      Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 → Work.Spaces.HkNorm α 6 w ≤ Ce →
      Work.Spaces.HkMem α 5 (Work.Coercivity.LGammaT α w) ∧
      Work.Spaces.HkNorm α 5 (Work.Coercivity.LGammaT α w) ≤ Kl)
    (hN0 : ∀ {w : Fn}, Work.FTS.ClassC.ClassC α w →
      Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 → Work.Spaces.HkNorm α 6 w ≤ Ce →
      Work.Spaces.HkMem α 5 (Work.Construction.N0 α (Work.Construction.Ftot α w) w) ∧
      Work.Spaces.HkNorm α 5 (Work.Construction.N0 α (Work.Construction.Ftot α w) w) ≤ K0)
    (hNb : ∀ {w Φg : Fn}, Work.FTS.ClassC.ClassC α w →
      Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 → Work.Spaces.HkNorm α 6 w ≤ Ce →
      Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
      Work.FTS.StrongPersist.StarPkg6 α Cs6 Φs →
      Work.Spaces.HkMem α 5 (Work.Construction.N α (Work.Construction.Ftot α w)
        (fun z θ => Φs z θ + Φg z θ)) ∧
      Work.Spaces.HkNorm α 5 (Work.Construction.N α (Work.Construction.Ftot α w)
        (fun z θ => Φs z θ + Φg z θ)) ≤ KN) :
    ∃ KW : ℝ, 0 < KW ∧ ∀ (g : Fam) (ε : ℝ),
      (∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.ClassC.ClassC α
        (slice (Work.FTS.StrongEps.JfamP ρ ε g) s)) →
      (∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.Nonlin.Xn α
        (slice (Work.FTS.StrongEps.JfamP ρ ε g) s) ≤ C₀ * α ^ 2) →
      (∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.StrongGlobal.Xn6 α
        (slice (Work.FTS.StrongEps.JfamP ρ ε g) s) ≤ Ce) →
      ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkMem α 5 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s) ∧
        Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s) ≤ KW := by
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hstar4 : Work.FTS.VocabO2.StarPkgo2 α Cs6 Φs := hstar6.toStarPkgo2
  obtain ⟨CM, hCM, hmub⟩ :=
    Work.FTS.StrongEps.epsWP_mubar_bound (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs6)
      (Φs := Φs) (E := E) hα hEll hstar4
  obtain ⟨KAK, hKAK, hAK6⟩ := Work.FTS.StrongPersist.AK6_mem_norm
  set Kst : ℝ := 2 * ((1 / 2) * max Ce 0 + 2 * max Ce 0) + 1 with hKstdef
  have hKstnn : 0 ≤ Kst := by
    rw [hKstdef]
    positivity
  have hCMnn : 0 ≤ CM := hCM.le
  have hKAKnn : 0 ≤ KAK := hKAK.le
  -- ### the level-`5` `AK`-data, from the level-`6` bound
  have hAKsmo : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.AK α) :=
    Work.FTS.StrongPersist.AK_smoothO α
  have hAK6mem : Work.Spaces.HkMem α 6 (Work.Construction.AK α) := (hAK6 α hα0 hα1).1
  have hAK6bd : Work.Spaces.HkNorm α 6 (Work.Construction.AK α) ≤ KAK := (hAK6 α hα0 hα1).2
  have haksmem : Work.Spaces.HkMem α 5 (Work.Construction.AK α) :=
    Work.FTS.OpenPkg.HkMem_mono_open hAKsmo 5 (by norm_num) hAK6mem
  have hAK5bd : Work.Spaces.HkNorm α 5 (Work.Construction.AK α) ≤ KAK :=
    le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (α := α) (k := 6) (k' := 5)
      (by norm_num) hAK6mem) hAK6bd
  have hprodnn : 0 ≤ CM * KAK := mul_nonneg hCMnn hKAKnn
  refine ⟨16 * (Kl + CM * KAK + K0 + KN + Kst) + 1, by
    linarith [hKl, hprodnn, hK0, hKN, hKstnn], ?_⟩
  intro g ε hC hb4 hb6 s hs
  set w : Fn := slice (Work.FTS.StrongEps.JfamP ρ ε g) s with hwdef
  have hcls : Work.FTS.ClassC.ClassC α w := hC s hs
  have hXw : Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 := hb4 s hs
  have hBw : Work.Spaces.HkNorm α 6 w ≤ Ce := hb6 s hs
  have hwsmo : Work.FTS.EllipticEst.SmoothOpen w := hcls.reg
  have hw7 : Work.Spaces.HkMem α 7 w := hcls.mem
  have hw6 : Work.Spaces.HkMem α 6 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hwsmo 6 (by norm_num) hw7
  have hw5 : Work.Spaces.HkMem α 5 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hwsmo 5 (by norm_num) hw7
  have hXw5 : Work.Spaces.HkNorm α 5 w ≤ Ce :=
    le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (α := α) (k := 6) (k' := 5)
      (by norm_num) hw6) hBw
  have hDzsmo : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz w) := hwsmo.Dz
  have hDthsmo : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth w) := hwsmo.Dth
  have hDz5 : Work.Spaces.HkMem α 5 (Work.Spaces.Dz w) :=
    Work.FTS.IPGen.HkMem_Dz_le hwsmo hw6
  have hDth5 : Work.Spaces.HkMem α 5 (Work.Spaces.Dth w) :=
    Work.FTS.IPGen.HkMem_Dth_le (by linarith) hwsmo hw6
  have hDz5bd : Work.Spaces.HkNorm α 5 (Work.Spaces.Dz w) ≤ Ce := by
    refine le_trans (Real.sqrt_le_sqrt (Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm α 5
      (Work.FTS.StrongPersist.q0Sm_of_smoothOpen hwsmo 6) hw6)) ?_
    rw [← Work.Spaces.HkNorm]
    exact hBw
  have hDth5bd : Work.Spaces.HkNorm α 5 (Work.Spaces.Dth w) ≤ Ce := by
    refine le_trans (Real.sqrt_le_sqrt
      (Work.FTS.CoercivityStep.Norm.HkSq_Dth_le α hα0 5 hw6)) ?_
    rw [← Work.Spaces.HkNorm]
    exact hBw
  -- ### the elliptic and smoothness data of the blocks
  have hellw : Work.FTS.VocabO.EllPkgGo α Ce w (E w) := (hEll w hcls).1
  have hell6 : Work.FTS.ClassC.EllPkgK α 6 Ce w (E w) := (hEll w hcls).2
  obtain ⟨_, _, hLGTsmo, hN0smo, hNsmo⟩ :=
    Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS hα0 hα1 hcls hellw hstar4
  have hFtau : Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s
      = Work.Construction.Ftot α w := rfl
  have hPsis : slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g)) s
      = fun z θ => Φs z θ + E w z θ := rfl
  -- ### the five blocks
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
  have hmuUbd : |muU| ≤ 1 / 2 := (hml w hcls hXw).1
  have hlamUbd : |lamU| ≤ 1 := (hml w hcls hXw).2
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
    rw [hP1def]
    exact Work.FTS.StrongEps.smoothOpen_neg_epsWP hLGTsmo
  have hP2smo : Work.FTS.EllipticEst.SmoothOpen P2 := by
    rw [hP2def]
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (-mb) (Work.FTS.StrongPersist.AK_smoothO α)
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
  have hP1mem : Work.Spaces.HkMem α 5 P1 := by
    rw [hP1def]
    exact Work.FTS.StrongEps.hkMem_neg_epsWP (hLGT hcls hXw hBw).1
  have hP2mem : Work.Spaces.HkMem α 5 P2 := by
    rw [hP2def]
    exact Work.FTS.LocData.HkMem_const_mul α 5 (-mb) (haksmem)
  have hP3mem : Work.Spaces.HkMem α 5 P3 := (hN0 hcls hXw hBw).1
  have hP4mem : Work.Spaces.HkMem α 5 P4 := (hNb hcls hXw hBw hellw hell6 hstar6).1
  have hP5mem : Work.Spaces.HkMem α 5 P5 := by
    rw [hP5eq]
    exact Work.FTS.EllipticEst.RPFresh.HkMem_add_open α 5
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-muU) hwsmo)
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-(muU + lamU + muU * lamU)) hDzsmo)
      (Work.FTS.LocData.HkMem_const_mul α 5 (-muU) hw5)
      (Work.FTS.LocData.HkMem_const_mul α 5 (-(muU + lamU + muU * lamU)) hDz5)
  -- ### the bounds of the blocks
  have hmb_le : |mb| ≤ CM := by
    rw [hmbdef]
    exact hmub w hcls hXw hBw
  have hP1bd : Work.Spaces.HkNorm α 5 P1 ≤ Kl := by
    rw [hP1def]
    show Work.Spaces.HkNorm α 5 (fun z θ => -(Work.Coercivity.LGammaT α w z θ)) ≤ Kl
    have h1 : Work.Spaces.HkNorm α 5 (fun z θ => -(Work.Coercivity.LGammaT α w z θ))
        = Work.Spaces.HkNorm α 5 (Work.Coercivity.LGammaT α w) :=
      Work.FTS.EllipticEst.HkNorm_neg α 5 (Work.Coercivity.LGammaT α w)
    rw [h1]
    exact (hLGT hcls hXw hBw).2
  have hP2bd : Work.Spaces.HkNorm α 5 P2 ≤ CM * KAK := by
    rw [hP2def]
    have h1 : Work.Spaces.HkNorm α 5 (fun z θ => -mb * Work.Construction.AK α z θ)
        = |mb| * Work.Spaces.HkNorm α 5 (Work.Construction.AK α) := by
      simpa only [abs_neg] using
        (Work.FTS.EllipticEst.HkNorm_const_mul (α := α) (k := 5) (c := -mb)
          (f := Work.Construction.AK α)
          ((Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Construction.AK α)).mp
            (Work.FTS.StrongPersist.AK_smoothO α)))
    rw [h1]
    have h2 : |mb| * Work.Spaces.HkNorm α 5 (Work.Construction.AK α) ≤ CM * KAK :=
      mul_le_mul hmb_le hAK5bd (Work.Spaces.HkNorm_nonneg α 5 _) hCMnn
    exact h2
  have hP3bd : Work.Spaces.HkNorm α 5 P3 ≤ K0 := (hN0 hcls hXw hBw).2
  have hP4bd : Work.Spaces.HkNorm α 5 P4 ≤ KN := (hNb hcls hXw hBw hellw hell6 hstar6).2
  have hkapp : |muU + lamU + muU * lamU| ≤ 2 := by
    calc |muU + lamU + muU * lamU| ≤ |muU + lamU| + |muU * lamU| := abs_add_le _ _
      _ ≤ (|muU| + |lamU|) + |muU| * |lamU| :=
          add_le_add (abs_add_le _ _) (le_of_eq (abs_mul _ _))
      _ ≤ (1 / 2 + 1) + (1 / 2) * 1 :=
          add_le_add (add_le_add hmuUbd hlamUbd)
            (mul_le_mul hmuUbd hlamUbd (abs_nonneg _) (by norm_num))
      _ ≤ 2 := by norm_num
  have hP5bd : Work.Spaces.HkNorm α 5 P5 ≤ Kst := by
    rw [hP5eq]
    have hsum := Work.FTS.GalFields.RHS.HkNorm_add_le_open α 5 hα0
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-muU) hwsmo)
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-(muU + lamU + muU * lamU)) hDzsmo)
      (Work.FTS.LocData.HkMem_const_mul α 5 (-muU) hw5)
      (Work.FTS.LocData.HkMem_const_mul α 5 (-(muU + lamU + muU * lamU)) hDz5)
    have hc1 : Work.Spaces.HkNorm α 5 (fun z θ => (-muU) * w z θ)
        = |muU| * Work.Spaces.HkNorm α 5 w := by
      simpa only [abs_neg] using
        (Work.FTS.EllipticEst.HkNorm_const_mul (α := α) (k := 5) (c := -muU) (f := w)
          ((Work.FTS.EllipticEst.smoothOpen_iff_forall w).mp hwsmo))
    have hc2 : Work.Spaces.HkNorm α 5
          (fun z θ => (-(muU + lamU + muU * lamU)) * Work.Spaces.Dz w z θ)
        = |muU + lamU + muU * lamU| * Work.Spaces.HkNorm α 5 (Work.Spaces.Dz w) := by
      simpa only [abs_neg] using
        (Work.FTS.EllipticEst.HkNorm_const_mul (α := α) (k := 5)
          (c := -(muU + lamU + muU * lamU)) (f := Work.Spaces.Dz w)
          ((Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.Dz w)).mp hDzsmo))
    refine le_trans hsum ?_
    rw [hc1, hc2]
    have hbr : |muU| * Work.Spaces.HkNorm α 5 w
          + |muU + lamU + muU * lamU| * Work.Spaces.HkNorm α 5 (Work.Spaces.Dz w)
        ≤ (1 / 2) * max Ce 0 + 2 * max Ce 0 :=
      add_le_add
        (mul_le_mul hmuUbd (le_trans hXw5 (le_max_left _ _))
          (Work.Spaces.HkNorm_nonneg α 5 w) (by norm_num))
        (mul_le_mul hkapp (le_trans hDz5bd (le_max_left _ _))
          (Work.Spaces.HkNorm_nonneg α 5 (Work.Spaces.Dz w)) (by norm_num))
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
  have hA2mem : Work.Spaces.HkMem α 5 A2 :=
    Work.FTS.EllipticEst.RPFresh.HkMem_add_open α 5 hP2smo hP3smo hP2mem hP3mem
  have hA3mem : Work.Spaces.HkMem α 5 A3 :=
    Work.FTS.EllipticEst.RPFresh.HkMem_add_open α 5 hA2smo hP4smo hA2mem hP4mem
  have hA4mem : Work.Spaces.HkMem α 5 A4 :=
    Work.FTS.EllipticEst.RPFresh.HkMem_add_open α 5 hP1smo hA3smo hP1mem hA3mem
  have hA5mem : Work.Spaces.HkMem α 5 A5 :=
    Work.FTS.EllipticEst.RPFresh.HkMem_add_open α 5 hA4smo hP5smo hA4mem hP5mem
  refine ⟨by rw [hsplit]; exact hA5mem, ?_⟩
  rw [hsplit]
  have hb1 : Work.Spaces.HkNorm α 5 A5
      ≤ 2 * (Work.Spaces.HkNorm α 5 A4 + Work.Spaces.HkNorm α 5 P5) :=
    Work.FTS.GalFields.RHS.HkNorm_add_le_open α 5 hα0 hA4smo hP5smo hA4mem hP5mem
  have hb2 : Work.Spaces.HkNorm α 5 A4
      ≤ 2 * (Work.Spaces.HkNorm α 5 P1 + Work.Spaces.HkNorm α 5 A3) :=
    Work.FTS.GalFields.RHS.HkNorm_add_le_open α 5 hα0 hP1smo hA3smo hP1mem hA3mem
  have hb3 : Work.Spaces.HkNorm α 5 A3
      ≤ 2 * (Work.Spaces.HkNorm α 5 A2 + Work.Spaces.HkNorm α 5 P4) :=
    Work.FTS.GalFields.RHS.HkNorm_add_le_open α 5 hα0 hA2smo hP4smo hA2mem hP4mem
  have hb4 : Work.Spaces.HkNorm α 5 A2
      ≤ 2 * (Work.Spaces.HkNorm α 5 P2 + Work.Spaces.HkNorm α 5 P3) :=
    Work.FTS.GalFields.RHS.HkNorm_add_le_open α 5 hα0 hP2smo hP3smo hP2mem hP3mem
  have e4 : Work.Spaces.HkNorm α 5 A2 ≤ 2 * (CM * KAK + K0) := by linarith [hb4, hP2bd, hP3bd]
  have e3 : Work.Spaces.HkNorm α 5 A3 ≤ 2 * (2 * (CM * KAK + K0) + KN) := by
    linarith [hb3, e4, hP4bd]
  have e2 : Work.Spaces.HkNorm α 5 A4 ≤ 2 * (Kl + 2 * (2 * (CM * KAK + K0) + KN)) := by
    linarith [hb2, hP1bd, e3]
  have e1 : Work.Spaces.HkNorm α 5 A5
      ≤ 2 * (2 * (Kl + 2 * (2 * (CM * KAK + K0) + KN)) + Kst) := by
    linarith [hb1, e2, hP5bd]
  linarith [e1, hKl.le, hK0.le, hKN.le, hKstnn, hCMnn, hKAKnn]

end Work.FTS.StrongEps.H5
