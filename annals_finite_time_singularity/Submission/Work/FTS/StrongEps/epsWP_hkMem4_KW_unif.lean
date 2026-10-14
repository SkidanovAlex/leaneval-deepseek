import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundR
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS_RegExport.RXT.Sys.pth_vop_slot_bd
import Submission.Work.FTS_RegExport.THL.cs7_rop_split
import Submission.Work.FTS_RegExport.THL.vopPert_theta_holder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `StrongEps/epsWP_hkMem4_KW_unif.lean` — the `ℋ⁴`-size of `epsWP`, uniform in the objects

The sibling `epsWP_hkMem4_bnd(_unif)` bounds the `ℋ⁴`-size of the projected scheme's right-hand
side `epsWP α ρ ε Φs E g s`, but its constant is *obtained after* the stream function `Φs` and the
elliptic solution operator `E` (they occur as implicit parameters of the block estimates
`ClassCRHS.HkMemXnN`, `epsWP_mubar_bound`, …), so it is only formally a function of them.

The present statement extracts the constant *first*: a single `KW` dominates `Xn α (epsWP …)` for
every `Φs`, `E`, horizon `T`, family `g`, scale `ε` and slice `s ∈ [0,T]`, as soon as the
interface hypotheses (the star package with its *numeric* constant `Cs`, the elliptic packages with
`Ce`, `MuLamOK`, the class-`C` small ball and the `ℋ⁶`-size bound `B`) hold.  The constancy is
*proved*, not assumed: all the numeric ingredients (`ClassCRHS.HkMemXnLGammaT`,
`ClassCRHS.HkMemXnN0`, `HkMemXnN_unif`, `OpenPkg.l12zero_field`, `Nonlinear.Pieces.rak_bound`) are
`Φs`/`E`-free, and they are consumed by the five-block assembly of the level-four chapter.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The `ℋ⁴`-size of `epsWP` with a constant chosen before `Φs`, `E`, `T`, `g`, `ε`** (and with
the `ℋ⁶`-size hypothesis carrying its own constant `B`, independent of the elliptic constant
`Ce`). -/
theorem epsWP_hkMem4_KW_unif {α C₀ B Ce Cs : ℝ} {ρ : ℝ × ℝ → ℝ} (hα : α ∈ Set.Ioc 0 1) :
    ∃ KW : ℝ, 0 < KW ∧
      ∀ (T : ℝ) (Φs : Fn) (E : Fn → Fn) (g : Fam) (ε : ℝ),
        (∀ u : Fn, Work.FTS.ClassC.ClassC α u →
          Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧
            Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
        Work.FTS.VocabO2.StarPkgo2 α Cs Φs →
        MuLamOK α C₀ Φs E →
        (∀ s ∈ Set.Icc 0 T, Work.FTS.ClassC.ClassC α
          (slice (JfamP ρ ε g) s)) →
        (∀ s ∈ Set.Icc 0 T, Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) s) ≤ C₀ * α ^ 2) →
        (∀ s ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α (slice (JfamP ρ ε g) s) ≤ B) →
        ∀ s ∈ Set.Icc 0 T,
          Work.FTS.EllipticEst.SmoothOpen (epsWP α ρ ε Φs E g s) ∧
            Work.Spaces.HkMem α 4 (epsWP α ρ ε Φs E g s) ∧
            Work.FTS.Nonlin.Xn α (epsWP α ρ ε Φs E g s) ≤ KW := by
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  -- ## the `Φs`/`E`-free block constants
  obtain ⟨Kl, hKl, hLGT⟩ := ClassCRHS.HkMemXnLGammaT (α := α) hα (C₀ := C₀) (B := B)
  obtain ⟨K0, hK0, hN0⟩ := ClassCRHS.HkMemXnN0 (α := α) hα (C₀ := C₀) (B := B)
  obtain ⟨KN, hKN, hN⟩ := ClassCRHS.HkMemXnN_unif (α := α) hα (C₀ := C₀) (B := B)
    (Ce := Ce) (Cs := Cs)
  obtain ⟨CZ, hCZ, hCZbd⟩ := Work.FTS.OpenPkg.l12zero_field
  obtain ⟨KAK, hKAK, hra⟩ := Work.FTS.Nonlinear.Pieces.rak_bound
  have hAKmem : Work.Spaces.HkMem α 4 (Work.Construction.AK α) :=
    Work.FTS.NonlinRows.HkMem_AK α hα0 hα1
  have hAKsmo : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.AK α) :=
    Work.FTS.StrongPersist.AK_smoothO α
  have hAKbd : Work.FTS.Nonlin.Xn α (Work.Construction.AK α) ≤ KAK := hra hα0 hα1
  -- ## the constants
  set CM : ℝ := CZ * (K0 + KN) + 1 with hCMdef
  have hCM : 0 < CM := by
    rw [hCMdef]
    have h1 : 0 ≤ CZ * (K0 + KN) := mul_nonneg hCZ.le (by linarith [hK0.le, hKN.le])
    linarith
  set Lam : ℝ := 2 * CM * KAK + 1 with hLamdef
  set Kst : ℝ := 2 * ((1 / 2) * max (C₀ * α ^ 2) 0 + 2 * max B 0) + 1 with hKstdef
  have hLamnn : 0 ≤ Lam := by rw [hLamdef]; positivity
  have hKstnn : 0 ≤ Kst := by rw [hKstdef]; positivity
  have hKW : 0 < 16 * (Kl + Lam + K0 + KN + Kst) + 1 := by
    linarith [hKl, hLamnn, hK0, hKN, hKstnn]
  refine ⟨16 * (Kl + Lam + K0 + KN + Kst) + 1, hKW, ?_⟩
  intro T Φs E g ε hEll hstar hml hC hb4 hb6 s hs
  set w : Fn := slice (JfamP ρ ε g) s with hwdef
  have hcls : Work.FTS.ClassC.ClassC α w := hC s hs
  have hXw : Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 := hb4 s hs
  have hBw : Work.Spaces.HkNorm α 6 w ≤ B := hb6 s hs
  have hwsmo : Work.FTS.EllipticEst.SmoothOpen w := hcls.reg
  have hw7 : Work.Spaces.HkMem α 7 w := hcls.mem
  have hw6 : Work.Spaces.HkMem α 6 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hwsmo 6 (by norm_num) hw7
  have hw5 : Work.Spaces.HkMem α 5 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hwsmo 5 (by norm_num) hw7
  have hw4 : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hwsmo 4 (by norm_num) hw7
  have hDzsmo : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz w) := hwsmo.Dz
  have hDz4 : Work.Spaces.HkMem α 4 (Work.Spaces.Dz w) :=
    Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α 4 hwsmo hw5
  have hXn5 : Work.FTS.GalFields.Xn5 α w ≤ B :=
    le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (α := α) (k := 6) (k' := 5)
      (by norm_num) hw6) hBw
  have hDzbd : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz w) ≤ B :=
    le_trans (Work.FTS.GalFields.Xn_Dz_le_Xn5 hα0 hwsmo hw5) hXn5
  have hellw : Work.FTS.VocabO.EllPkgGo α Ce w (E w) := (hEll w hcls).1
  obtain ⟨hmuOK, hlamOK⟩ := hml w hcls hXw
  obtain ⟨_, _, hLGTsmo, hN0smo, hNsmo⟩ :=
    ClassCRHS.SmoothOpenRHS hα0 hα1 hcls hellw hstar
  have hFtau : Work.Construction.Ftau α (JfamP ρ ε g) s
      = Work.Construction.Ftot α w := rfl
  have hPsis : slice (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ ε g)) s
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
    (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ ε g))
    (JfamP ρ ε g) s with hmuUdef
  set lamU : ℝ := Work.FTS.Galerkin.lamDyn α
    (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ ε g))
    (JfamP ρ ε g) s with hlamUdef
  set P5 : Fn := Work.Construction.Nstar muU lamU w with hP5def
  set A2 : Fn := fun z θ => P2 z θ + P3 z θ with hA2def
  set A3 : Fn := fun z θ => A2 z θ + P4 z θ with hA3def
  set A4 : Fn := fun z θ => P1 z θ + A3 z θ with hA4def
  set A5 : Fn := fun z θ => A4 z θ + P5 z θ with hA5def
  have hmuUbd : |muU| ≤ 1 / 2 := hmuOK
  have hlamUbd : |lamU| ≤ 1 := hlamOK
  -- ### the identification of `epsWP` with the block sum
  have hsplit : epsWP α ρ ε Φs E g s = A5 := by
    funext z θ
    simp only [epsWP, Work.FTS.Galerkin.dynLin, Work.FTS.Galerkin.dynRHS,
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
  -- ### the `μ̄`-coefficient at the *explicit* constant `CM`
  have hN0Q : Work.FTS.VocabO.HQo α 4
      (Work.Construction.N0 α (Work.Construction.Ftot α w) w) :=
    ⟨hN0smo, (hN0 (w := w) hcls hXw hBw).1⟩
  have hN1Q : Work.FTS.VocabO.HQo α 4
      (Work.Construction.N α (Work.Construction.Ftot α w)
        (fun z θ => Φs z θ + E w z θ)) :=
    ⟨hNsmo, (hN (w := w) (Φg := E w) hcls hXw hBw hellw hstar).1⟩
  have hmble : |mb| ≤ CM := by
    rw [hmbdef]
    have hmb : Work.Construction.mubar
        (Work.Construction.N0 α (Work.Construction.Ftot α w) w)
        (Work.Construction.N α (Work.Construction.Ftot α w)
          (fun z θ => Φs z θ + E w z θ))
        = Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α w) w) 0
          + Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α w)
              (fun z θ => Φs z θ + E w z θ)) 0 := rfl
    rw [hmb, hCMdef]
    have hL0 := hCZbd α hα0 hα1 _ hN0Q
    have hL1 := hCZbd α hα0 hα1 _ hN1Q
    have hK0b := (hN0 (w := w) hcls hXw hBw).2
    have hKNb := (hN (w := w) (Φg := E w) hcls hXw hBw hellw hstar).2
    have hstep : |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α w) w) 0|
        + |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α w)
            (fun z θ => Φs z θ + E w z θ)) 0| ≤ CZ * K0 + CZ * KN :=
      add_le_add (le_trans hL0 (mul_le_mul_of_nonneg_left hK0b hCZ.le))
        (le_trans hL1 (mul_le_mul_of_nonneg_left hKNb hCZ.le))
    refine le_trans (abs_add_le _ _) ?_
    nlinarith [hstep, hCZ.le, hK0.le, hKN.le]
  -- ### the bounds of the blocks
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
      mul_le_mul hmble hAKbd (Work.Spaces.HkNorm_nonneg α 4 _) hCM.le
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
        ≤ (1 / 2) * max (C₀ * α ^ 2) 0 + 2 * max B 0 :=
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
  have hmem : Work.Spaces.HkMem α 4 (epsWP α ρ ε Φs E g s) := by
    rw [hsplit]; exact hA5mem
  have hbd : Work.FTS.Nonlin.Xn α (epsWP α ρ ε Φs E g s)
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
    have hb4' : Work.FTS.Nonlin.Xn α A2
        ≤ 2 * (Work.FTS.Nonlin.Xn α P2 + Work.FTS.Nonlin.Xn α P3) :=
      Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα0 hP2smo hP3smo hP2mem hP3mem
    have e4 : Work.FTS.Nonlin.Xn α A2 ≤ 2 * (Lam + K0) := by linarith [hb4', hP2bd, hP3bd]
    have e3 : Work.FTS.Nonlin.Xn α A3 ≤ 2 * (2 * (Lam + K0) + KN) := by
      linarith [hb3, e4, hP4bd]
    have e2 : Work.FTS.Nonlin.Xn α A4 ≤ 2 * (Kl + 2 * (2 * (Lam + K0) + KN)) := by
      linarith [hb2, hP1bd, e3]
    have e1 : Work.FTS.Nonlin.Xn α A5
        ≤ 2 * (2 * (Kl + 2 * (2 * (Lam + K0) + KN)) + Kst) := by
      linarith [hb1, e2, hP5bd]
    linarith [e1, hKl.le, hLamnn, hK0.le, hKN.le, hKstnn]
  exact ⟨by rw [hsplit]; exact hA5smo, hmem, hbd⟩

end Work.FTS.StrongEps
