/-
# `SharpAux/HonTerms/Part1` — the five `g'`-side terms

The five monomials `TRB, TUB, TVB, TDB, TEB` of `SharpAux/HonestTermsBound`, in each of which the
`|g'|`-carrying factor is the one priced by `(1 + |g|_{ℋ⁵} + |g'|_{ℋ⁵})`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.GalFields.RHS.SharpAux.HonTerms.Base
import Submission.Work.FTS.CoercivityFix.E2Bound.HkMem_dth_of_RegQ_ge
import Submission.Work.FTS.CoercivityFix.QuadPorts.RegQ_dz
import Submission.Work.FTS.LocDataExt.Monotone
import Submission.Work.FTS.StrongLWP.Basic
import Submission.Work.FTS.GalFields.Norm.Basic
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.RHS.SharpAux.HonTerms

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem part1 {α α₂ Ci Ce Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {EllSol : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hell : ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.Nonlin.GalClass α g →
      Work.FTS.VocabO.EllPkgGo α Ce g (EllSol g))
    (hα : 0 < α) (hαα₂ : α ≤ α₂) :
    ∃ K : ℝ, 0 < K ∧ ∀ {g g' h : Work.FTS.Galerkin.Fn},
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.GalClass α g' →
      Work.FTS.Nonlin.GalClass α h → α ≤ 1 →
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TRB α EllSol g' h) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TRB α EllSol g' h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TRB α EllSol g' h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TUB α EllSol g' h) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TUB α EllSol g' h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TUB α EllSol g' h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TVB α EllSol g' h) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TVB α EllSol g' h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TVB α EllSol g' h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TDB α g' h) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TDB α g' h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TDB α g' h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TEB α g' h) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TEB α g' h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TEB α g' h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) := by
  have hCi : 0 < Ci := hN.pos.1
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  obtain ⟨Cang, hCangpos, hangmul0⟩ := Work.FTS.StrongPersist.L3Rhs.ang_mul_HkSq_le 4
  obtain ⟨Bsin, hBsinpos, -, hBsinle, hBsinIt⟩ :=
    Work.FTS.Nonlinear.Pieces.RNP.RNP24.angProfile_sinSq
  have hc1 : 0 ≤ Ci * α ^ (-(1 / 2 : ℝ)) * max Ce 0 := by positivity
  have hc2 : 0 ≤ Ci * α ^ (-(1 / 2 : ℝ)) * α * max Ce 0 := by positivity
  have hc3 : 0 ≤ Ci * α ^ (-(1 / 2 : ℝ)) * Ci := by positivity
  have hc4 : 0 ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Real.sqrt (Cang * Bsin ^ 2) * Ci) := by
    positivity
  set K : ℝ := 1 + 4 * (Ci * α ^ (-(1 / 2 : ℝ)) * max Ce 0)
      + 2 * (Ci * α ^ (-(1 / 2 : ℝ)) * α * max Ce 0)
      + (Ci * α ^ (-(1 / 2 : ℝ))) * Ci
      + (Ci * α ^ (-(1 / 2 : ℝ))) * (Real.sqrt (Cang * Bsin ^ 2) * Ci) with hK
  have hKpos : 0 < K := by rw [hK]; linarith [hc1, hc2, hc3, hc4]
  refine ⟨K, hKpos, ?_⟩
  intro g g' h hg hg' hh hα1
  have hgS : Work.FTS.EllipticEst.SmoothOpen g :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad hg.reg.1
  have hhS : Work.FTS.EllipticEst.SmoothOpen h :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad hh.reg.1
  have hh4 : Work.Spaces.HkMem α 4 h := Work.FTS.OpenPkg.galClass_HkMem4 hh
  have hg5 : Work.Spaces.HkMem α 5 g := Work.FTS.OpenPkg.galClass_HkMem5 hg
  have hg'5 : Work.Spaces.HkMem α 5 g' := Work.FTS.OpenPkg.galClass_HkMem5 hg'
  have hh5 : Work.Spaces.HkMem α 5 h := Work.FTS.OpenPkg.galClass_HkMem5 hh
  have hXg' : Work.FTS.Nonlin.Xn α g' ≤ Work.FTS.GalFields.Xn5 α g' :=
    Work.FTS.StrongLWP.HkNorm_mono_of_mem (by norm_num) hg'5
  have hXh : Work.FTS.Nonlin.Xn α h ≤ Work.FTS.GalFields.Xn5 α h :=
    Work.FTS.StrongLWP.HkNorm_mono_of_mem (by norm_num) hh5
  have hng : (0 : ℝ) ≤ Work.FTS.GalFields.Xn5 α g := Work.Spaces.HkNorm_nonneg α 5 g
  have hng' : (0 : ℝ) ≤ Work.FTS.GalFields.Xn5 α g' := Work.Spaces.HkNorm_nonneg α 5 g'
  have hnh : (0 : ℝ) ≤ Work.FTS.GalFields.Xn5 α h := Work.Spaces.HkNorm_nonneg α 5 h
  have hDthhS : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth h) := hhS.Dth
  have hDzhS : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz h) := hhS.Dz
  have hDthh4 : Work.Spaces.HkMem α 4 (Work.Spaces.Dth h) :=
    Work.FTS.CoercivityFix.E2Bound.HkMem_dth_of_RegQ_ge α 4 (by linarith)
      (Work.FTS.LocDataExt.RegQ_mono (by norm_num) hh.reg)
  have hDzh4 : Work.Spaces.HkMem α 4 (Work.Spaces.Dz h) :=
    Work.FTS.CoercivityFix.QuadPorts.HkMem_Dz_quad α 4 hh.reg.1 hh5
  have hDthhXn : Work.FTS.Nonlin.Xn α (Work.Spaces.Dth h) ≤ Work.FTS.GalFields.Xn5 α h :=
    Work.FTS.GalFields.Xn_Dth_le_Xn5 hα hh5
  have hDzhXn : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz h) ≤ Work.FTS.GalFields.Xn5 α h :=
    Work.FTS.GalFields.Xn_Dz_le_Xn5 hα hhS hh5
  have hCe_g' : ∀ {F : Fn}, Work.FTS.Nonlin.Xn α F ≤ Ce * Work.FTS.Nonlin.Xn α g' →
      Work.FTS.Nonlin.Xn α F
        ≤ max Ce 0 * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g') := by
    intro F hF
    exact le_trans hF (le_trans
      (mul_le_mul_of_nonneg_right (le_max_left Ce 0) (Work.Spaces.HkNorm_nonneg α 4 g'))
      (mul_le_mul_of_nonneg_left (by linarith [hXg', hng, hng']) (le_max_right Ce 0)))
  have hCi_g' : ∀ {F : Fn}, Work.FTS.Nonlin.Xn α F ≤ Ci * Work.FTS.Nonlin.Xn α g' →
      Work.FTS.Nonlin.Xn α F
        ≤ Ci * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g') := by
    intro F hF
    exact le_trans hF (mul_le_mul_of_nonneg_left (by linarith [hXg', hng, hng']) (le_of_lt hCi))
  have hRg'S : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.Rop α (Sharp.Zgof α EllSol g') z θ) := (hell g' hg').R.1.1
  have hRg'4 : Work.Spaces.HkMem α 4
      (fun z θ => Work.Construction.Rop α (Sharp.Zgof α EllSol g') z θ) := (hell g' hg').R.1.2
  have hRg'X : Work.FTS.Nonlin.Xn α
      (fun z θ => Work.Construction.Rop α (Sharp.Zgof α EllSol g') z θ)
      ≤ max Ce 0 * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g') :=
    hCe_g' (hell g' hg').R.2
  have hUg'S : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.Uop α (Sharp.Zgof α EllSol g') z θ / Work.Construction.s2 θ) :=
    (hell g' hg').U.1.1
  have hUg'4 : Work.Spaces.HkMem α 4
      (fun z θ => Work.Construction.Uop α (Sharp.Zgof α EllSol g') z θ / Work.Construction.s2 θ) :=
    (hell g' hg').U.1.2
  have hUg'X : Work.FTS.Nonlin.Xn α
      (fun z θ => Work.Construction.Uop α (Sharp.Zgof α EllSol g') z θ / Work.Construction.s2 θ)
      ≤ max Ce 0 * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g') :=
    hCe_g' (hell g' hg').U.2
  have hVg'S : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.Vop (Sharp.Zgof α EllSol g') z θ) := (hell g' hg').V.1.1
  have hVg'4 : Work.Spaces.HkMem α 4
      (fun z θ => Work.Construction.Vop (Sharp.Zgof α EllSol g') z θ) := (hell g' hg').V.1.2
  have hVg'X : Work.FTS.Nonlin.Xn α
      (fun z θ => Work.Construction.Vop (Sharp.Zgof α EllSol g') z θ)
      ≤ max Ce 0 * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g') :=
    hCe_g' (hell g' hg').V.2
  have hFKg' := hN.fkH α hIoc g' (Work.FTS.OpenPkg.galClass_HQo4 hg') hg'.l12
  have hFKg'Sm : Work.FTS.EllipticEst.SmoothOpen
      (fun z _ => Work.Construction.FK g' z) :=
    Work.FTS.NonlinRows.AuxFK.smoothOpen_FK_radial hα hα1 hg'.reg.1
      (Work.FTS.OpenPkg.galClass_HkMem4 hg') hg'.l12
      (hell g' hg').smooth (hell g' hg').V.1.1
  have hFKg'X : Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK g' z)
      ≤ Ci * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g') :=
    hCi_g' hFKg'.2
  obtain ⟨hnegm_g', hnegs_g'⟩ :=
    (hangmul0 α hα hα1) negSinSq Bsin hBsinpos negSinSq_smooth
      (fun θ hθ => hBsinle θ hθ) (fun i hi1 hi4 θ hθ => hBsinIt i hi1 hi4 θ hθ)
      (fun z _ => Work.Construction.FK g' z) hFKg'Sm hFKg'.1
  obtain ⟨hsinFKg'S, hsinFKg'mem, hsinFKg'Xn⟩ :=
    sinSq_mul hCangpos hBsinpos hFKg'Sm hnegm_g' hnegs_g'
  have hsinFKg'X : Work.FTS.Nonlin.Xn α
      (fun z θ => Work.FTS.GalFields.RHS.Sharp.sinSq θ * Work.Construction.FK g' z)
      ≤ (Real.sqrt (Cang * Bsin ^ 2) * Ci)
          * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g') := by
    refine le_trans hsinFKg'Xn ?_
    calc Real.sqrt (Cang * Bsin ^ 2)
          * Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK g' z)
        ≤ Real.sqrt (Cang * Bsin ^ 2)
            * (Ci * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')) :=
          mul_le_mul_of_nonneg_left hFKg'X (Real.sqrt_nonneg _)
      _ = (Real.sqrt (Cang * Bsin ^ 2) * Ci)
            * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g') := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `TRB = 2·(Rop(Φ̃_{g'})·h)`
    obtain ⟨hS1, hM1, hX1⟩ :=
      honest_mul hN hα hαα₂
        (F := fun z θ => Work.Construction.Rop α (Sharp.Zgof α EllSol g') z θ) (U := h)
        hRg'S hhS hRg'4 hh4 (A := max Ce 0) (B := 1) (c := 2)
        (le_max_right Ce 0) (by norm_num) hRg'X (by rw [one_mul]; exact hXh)
    refine ⟨hS1, hM1, ?_⟩
    rw [show |(2 : ℝ)| = 2 from by norm_num] at hX1
    calc Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TRB α EllSol g' h)
        ≤ 2 * (Ci * α ^ (-(1 / 2 : ℝ)) * max Ce 0 * 1
            * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
            * Work.FTS.GalFields.Xn5 α h) := hX1
      _ = (2 * (Ci * α ^ (-(1 / 2 : ℝ)) * max Ce 0))
            * ((1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) := by ring
      _ ≤ K * ((1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) := by
            refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (by linarith [hng, hng']) hnh)
            rw [hK]; nlinarith [hc1, hc2, hc3, hc4]
      _ = K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h := by ring
  · -- `TUB = -2·((U(Φ̃_{g'})/s2)·D_θh)`
    obtain ⟨hS2, hM2, hX2⟩ :=
      honest_mul hN hα hαα₂
        (F := fun z θ => Work.Construction.Uop α (Sharp.Zgof α EllSol g') z θ
          / Work.Construction.s2 θ)
        (U := Work.Spaces.Dth h)
        hUg'S hDthhS hUg'4 hDthh4 (A := max Ce 0) (B := 1) (c := -2)
        (le_max_right Ce 0) (by norm_num) hUg'X (by rw [one_mul]; exact hDthhXn)
    refine ⟨hS2, hM2, ?_⟩
    rw [show |(-(2 : ℝ))| = 2 from by rw [abs_neg]; norm_num] at hX2
    calc Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TUB α EllSol g' h)
        ≤ 2 * (Ci * α ^ (-(1 / 2 : ℝ)) * max Ce 0 * 1
            * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
            * Work.FTS.GalFields.Xn5 α h) := hX2
      _ = (2 * (Ci * α ^ (-(1 / 2 : ℝ)) * max Ce 0))
            * ((1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) := by ring
      _ ≤ K * ((1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) := by
            refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (by linarith [hng, hng']) hnh)
            rw [hK]; nlinarith [hc1, hc2, hc3, hc4]
      _ = K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h := by ring
  · -- `TVB = -2α·(V(Φ̃_{g'})·D_zh)`
    obtain ⟨hS3, hM3, hX3⟩ :=
      honest_mul hN hα hαα₂
        (F := fun z θ => Work.Construction.Vop (Sharp.Zgof α EllSol g') z θ)
        (U := Work.Spaces.Dz h)
        hVg'S hDzhS hVg'4 hDzh4 (A := max Ce 0) (B := 1) (c := -(2 * α))
        (le_max_right Ce 0) (by norm_num) hVg'X (by rw [one_mul]; exact hDzhXn)
    refine ⟨hS3, hM3, ?_⟩
    rw [show |(-(2 * α))| = 2 * α from by rw [abs_neg]; exact abs_of_nonneg (by linarith)] at hX3
    calc Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TVB α EllSol g' h)
        ≤ 2 * α * (Ci * α ^ (-(1 / 2 : ℝ)) * max Ce 0 * 1
            * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
            * Work.FTS.GalFields.Xn5 α h) := hX3
      _ = (2 * α * (Ci * α ^ (-(1 / 2 : ℝ)) * max Ce 0))
            * ((1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) := by ring
      _ ≤ K * ((1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) := by
            refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (by linarith [hng, hng']) hnh)
            rw [hK]; nlinarith [hc1, hc2, hc3, hc4]
      _ = K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h := by ring
  · -- `TDB = -(1/2)·(FK(g')·D_θh)`
    obtain ⟨hS4, hM4, hX4⟩ :=
      honest_mul hN hα hαα₂
        (F := fun z _ => Work.Construction.FK g' z) (U := Work.Spaces.Dth h)
        hFKg'Sm hDthhS hFKg'.1 hDthh4 (A := Ci) (B := 1) (c := -(1 / 2))
        (le_of_lt hCi) (by norm_num) hFKg'X (by rw [one_mul]; exact hDthhXn)
    refine ⟨hS4, hM4, ?_⟩
    rw [show |(-(1 / 2 : ℝ))| = 1 / 2 from by rw [abs_neg]; norm_num] at hX4
    calc Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TDB α g' h)
        ≤ 1 / 2 * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci * 1
            * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
            * Work.FTS.GalFields.Xn5 α h) := hX4
      _ = ((1 / 2) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci))
            * ((1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) := by ring
      _ ≤ K * ((1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) := by
            refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (by linarith [hng, hng']) hnh)
            rw [hK]; nlinarith [hc1, hc2, hc3, hc4]
      _ = K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h := by ring
  · -- `TEB = -1·((sin²θ·FK(g'))·h)`
    obtain ⟨hS5, hM5, hX5⟩ :=
      honest_mul hN hα hαα₂
        (F := fun z θ => Work.FTS.GalFields.RHS.Sharp.sinSq θ * Work.Construction.FK g' z)
        (U := h)
        hsinFKg'S hhS hsinFKg'mem hh4
        (A := Real.sqrt (Cang * Bsin ^ 2) * Ci) (B := 1) (c := -1)
        (mul_nonneg (Real.sqrt_nonneg _) (le_of_lt hCi)) (by norm_num) hsinFKg'X
        (by rw [one_mul]; exact hXh)
    refine ⟨hS5, hM5, ?_⟩
    rw [show |(-(1 : ℝ))| = 1 from by rw [abs_neg]; norm_num] at hX5
    calc Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TEB α g' h)
        ≤ 1 * (Ci * α ^ (-(1 / 2 : ℝ)) * (Real.sqrt (Cang * Bsin ^ 2) * Ci) * 1
            * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
            * Work.FTS.GalFields.Xn5 α h) := hX5
      _ = ((Ci * α ^ (-(1 / 2 : ℝ))) * (Real.sqrt (Cang * Bsin ^ 2) * Ci))
            * ((1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) := by ring
      _ ≤ K * ((1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) := by
            refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (by linarith [hng, hng']) hnh)
            rw [hK]; nlinarith [hc1, hc2, hc3, hc4]
      _ = K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h := by ring

end Work.FTS.GalFields.RHS.SharpAux.HonTerms
