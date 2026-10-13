/-
# `CCSharp/HonTermsC/Part2C` — the five `h`-side terms at the `ClassC` level

The `ClassC`-port of `Work.FTS.GalFields.RHS.SharpAux.HonTerms.part2`: the five monomials
`TRD, TUD, TVD, TDD, TED` of `CCSharp.HonestTermsBoundC`, in each of which the `|h|`-carrying
factor is written first, with the three `GalClass` hypotheses replaced by `ClassC` (and the
`SmoothQuad`/`RegQ`-extraction replaced by the open-quadrant extraction lemmas of
`CCSharp/Base.lean`).  The proof is the original one verbatim apart from the extraction block.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.EpsRLX.CCSharp.HonTermsC.Part1C
import Submission.Work.FTS.GalFields.RHS.SharpAux.HonTerms.Base
import Submission.Work.FTS.StrongEps.EpsRLX.CCSharp.Base
import Submission.Work.FTS.GalFields.Norm.Basic
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.StrongPersist.L3Rhs.c2m_mul_HkSq_le
import Submission.Work.FTS.Nonlinear.Pieces.RNP.RNP24.angProfile_sinSq
import Submission.Work.FTS.Nonlinear.Open.Row25Aux
import Submission.Work.FTS.Nonlinear.Pieces.Basic
import Submission.Work.FTS.EllipticEst.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX.CCSharp.HonTermsC

open Work.FTS.Galerkin (Fn)
open Work.FTS.GalFields.RHS.SharpAux.HonTerms

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem Part2C {α α₂ Ci Ce Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {EllSol : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hEll : ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g →
      Work.FTS.VocabO.EllPkgGo α Ce g (EllSol g))
    (hα : 0 < α) (hαα₂ : α ≤ α₂) :
    ∃ K : ℝ, 0 < K ∧ ∀ {g g' h : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α g → Work.FTS.ClassC.ClassC α g' →
      Work.FTS.ClassC.ClassC α h → α ≤ 1 →
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TRD α EllSol g h) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TRD α EllSol g h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TRD α EllSol g h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TUD α EllSol g h) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TUD α EllSol g h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TUD α EllSol g h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TVD α EllSol g h) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TVD α EllSol g h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TVD α EllSol g h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TDD α g h) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TDD α g h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TDD α g h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TED α g h) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TED α g h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TED α g h)
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
  have hgS : Work.FTS.EllipticEst.SmoothOpen g := hg.reg
  have hhS : Work.FTS.EllipticEst.SmoothOpen h := hh.reg
  have hh4 : Work.Spaces.HkMem α 4 h := cMem hh (k := 4) (by norm_num)
  have hg5 : Work.Spaces.HkMem α 5 g := cMem hg (k := 5) (by norm_num)
  have hg'5 : Work.Spaces.HkMem α 5 g' := cMem hg' (k := 5) (by norm_num)
  have hh5 : Work.Spaces.HkMem α 5 h := cMem hh (k := 5) (by norm_num)
  have hXg : Work.FTS.Nonlin.Xn α g ≤ Work.FTS.GalFields.Xn5 α g :=
    Work.FTS.StrongLWP.HkNorm_mono_of_mem (by norm_num) hg5
  have hXh : Work.FTS.Nonlin.Xn α h ≤ Work.FTS.GalFields.Xn5 α h :=
    Work.FTS.StrongLWP.HkNorm_mono_of_mem (by norm_num) hh5
  have hng : (0 : ℝ) ≤ Work.FTS.GalFields.Xn5 α g := Work.Spaces.HkNorm_nonneg α 5 g
  have hng' : (0 : ℝ) ≤ Work.FTS.GalFields.Xn5 α g' := Work.Spaces.HkNorm_nonneg α 5 g'
  have hnh : (0 : ℝ) ≤ Work.FTS.GalFields.Xn5 α h := Work.Spaces.HkNorm_nonneg α 5 h
  have hDthgS : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth g) := hgS.Dth
  have hDzgS : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz g) := hgS.Dz
  have hDthg4 : Work.Spaces.HkMem α 4 (Work.Spaces.Dth g) :=
    Work.FTS.IPGen.HkMem_Dth_le (k := 4) (by linarith) hg.reg (cMem hg (k := 5) (by norm_num))
  have hDzg4 : Work.Spaces.HkMem α 4 (Work.Spaces.Dz g) :=
    Work.FTS.IPGen.HkMem_Dz_le (k := 4) hg.reg (cMem hg (k := 5) (by norm_num))
  have hDthgXn : Work.FTS.Nonlin.Xn α (Work.Spaces.Dth g) ≤ Work.FTS.GalFields.Xn5 α g :=
    Work.FTS.GalFields.Xn_Dth_le_Xn5 hα hg5
  have hDzgXn : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz g) ≤ Work.FTS.GalFields.Xn5 α g :=
    Work.FTS.GalFields.Xn_Dz_le_Xn5 hα hgS hg5
  have hCe_h : ∀ {F : Fn}, Work.FTS.Nonlin.Xn α F ≤ Ce * Work.FTS.Nonlin.Xn α h →
      Work.FTS.Nonlin.Xn α F ≤ max Ce 0 * Work.FTS.GalFields.Xn5 α h := by
    intro F hF
    exact le_trans hF (le_trans
      (mul_le_mul_of_nonneg_right (le_max_left Ce 0) (Work.Spaces.HkNorm_nonneg α 4 h))
      (mul_le_mul_of_nonneg_left hXh (le_max_right Ce 0)))
  have hCi_h : ∀ {F : Fn}, Work.FTS.Nonlin.Xn α F ≤ Ci * Work.FTS.Nonlin.Xn α h →
      Work.FTS.Nonlin.Xn α F ≤ Ci * Work.FTS.GalFields.Xn5 α h := by
    intro F hF
    exact le_trans hF (mul_le_mul_of_nonneg_left hXh (le_of_lt hCi))
  have hRhS : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.Rop α (Work.FTS.GalFields.RHS.Sharp.Dof α EllSol h) z θ) :=
    (hEll h hh).R.1.1
  have hRh4 : Work.Spaces.HkMem α 4
      (fun z θ => Work.Construction.Rop α (Work.FTS.GalFields.RHS.Sharp.Dof α EllSol h) z θ) :=
    (hEll h hh).R.1.2
  have hRhX : Work.FTS.Nonlin.Xn α
      (fun z θ => Work.Construction.Rop α (Work.FTS.GalFields.RHS.Sharp.Dof α EllSol h) z θ)
      ≤ max Ce 0 * Work.FTS.GalFields.Xn5 α h := hCe_h (hEll h hh).R.2
  have hUhS : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.Uop α (Work.FTS.GalFields.RHS.Sharp.Dof α EllSol h) z θ
        / Work.Construction.s2 θ) :=
    (hEll h hh).U.1.1
  have hUh4 : Work.Spaces.HkMem α 4
      (fun z θ => Work.Construction.Uop α (Work.FTS.GalFields.RHS.Sharp.Dof α EllSol h) z θ
        / Work.Construction.s2 θ) :=
    (hEll h hh).U.1.2
  have hUhX : Work.FTS.Nonlin.Xn α
      (fun z θ => Work.Construction.Uop α (Work.FTS.GalFields.RHS.Sharp.Dof α EllSol h) z θ
        / Work.Construction.s2 θ)
      ≤ max Ce 0 * Work.FTS.GalFields.Xn5 α h := hCe_h (hEll h hh).U.2
  have hVhS : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.Vop (Work.FTS.GalFields.RHS.Sharp.Dof α EllSol h) z θ) :=
    (hEll h hh).V.1.1
  have hVh4 : Work.Spaces.HkMem α 4
      (fun z θ => Work.Construction.Vop (Work.FTS.GalFields.RHS.Sharp.Dof α EllSol h) z θ) :=
    (hEll h hh).V.1.2
  have hVhX : Work.FTS.Nonlin.Xn α
      (fun z θ => Work.Construction.Vop (Work.FTS.GalFields.RHS.Sharp.Dof α EllSol h) z θ)
      ≤ max Ce 0 * Work.FTS.GalFields.Xn5 α h := hCe_h (hEll h hh).V.2
  have hFKh := hN.fkH α hIoc h (cHQo hh) hh.l12
  have hFKhSm : Work.FTS.EllipticEst.SmoothOpen
      (fun z _ => Work.Construction.FK h z) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_FKw_of_classC hh
  have hFKhX : Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK h z)
      ≤ Ci * Work.FTS.GalFields.Xn5 α h := hCi_h hFKh.2
  obtain ⟨hnegm_h, hnegs_h⟩ :=
    (hangmul0 α hα hα1) negSinSq Bsin hBsinpos negSinSq_smooth
      (fun θ hθ => hBsinle θ hθ) (fun i hi1 hi4 θ hθ => hBsinIt i hi1 hi4 θ hθ)
      (fun z _ => Work.Construction.FK h z) hFKhSm hFKh.1
  obtain ⟨hsinFKhS, hsinFKhmem, hsinFKhXn⟩ :=
    sinSq_mul hCangpos hBsinpos hFKhSm hnegm_h hnegs_h
  have hsinFKhX : Work.FTS.Nonlin.Xn α
      (fun z θ => Work.FTS.GalFields.RHS.Sharp.sinSq θ * Work.Construction.FK h z)
      ≤ (Real.sqrt (Cang * Bsin ^ 2) * Ci) * Work.FTS.GalFields.Xn5 α h := by
    refine le_trans hsinFKhXn ?_
    calc Real.sqrt (Cang * Bsin ^ 2)
          * Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK h z)
        ≤ Real.sqrt (Cang * Bsin ^ 2) * (Ci * Work.FTS.GalFields.Xn5 α h) :=
          mul_le_mul_of_nonneg_left hFKhX (Real.sqrt_nonneg _)
      _ = (Real.sqrt (Cang * Bsin ^ 2) * Ci) * Work.FTS.GalFields.Xn5 α h := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `TRD = 2·(Rop(Φ̃_h)·g)`
    obtain ⟨hS6, hM6, hX6⟩ :=
      honest_mul_swap hN hα hαα₂ (g := g) (g' := g') (h := h)
        (F := fun z θ => Work.Construction.Rop α (Work.FTS.GalFields.RHS.Sharp.Dof α EllSol h) z θ)
        (U := g)
        hRhS hgS hRh4 (cMem hg (k := 4) (by norm_num))
        (A := 1) (B := max Ce 0) (c := 2)
        (by norm_num) (le_max_right Ce 0)
        (by rw [one_mul]; linarith [hXg, hng, hng']) hRhX
    refine ⟨hS6, hM6, ?_⟩
    rw [show |(2 : ℝ)| = 2 from by norm_num] at hX6
    calc Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TRD α EllSol g h)
        ≤ 2 * (Ci * α ^ (-(1 / 2 : ℝ)) * 1 * max Ce 0
            * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
            * Work.FTS.GalFields.Xn5 α h) := hX6
      _ = (2 * (Ci * α ^ (-(1 / 2 : ℝ)) * max Ce 0))
            * ((1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) := by ring
      _ ≤ K * ((1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) := by
            refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (by linarith [hng, hng']) hnh)
            rw [hK]; nlinarith [hc1, hc2, hc3, hc4]
      _ = K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h := by ring
  · -- `TUD = -2·((U(Φ̃_h)/s2)·D_θg)`
    obtain ⟨hS7, hM7, hX7⟩ :=
      honest_mul_swap hN hα hαα₂ (g := g) (g' := g') (h := h)
        (F := fun z θ => Work.Construction.Uop α (Work.FTS.GalFields.RHS.Sharp.Dof α EllSol h) z θ
          / Work.Construction.s2 θ)
        (U := Work.Spaces.Dth g)
        hUhS hDthgS hUh4 hDthg4 (A := 1) (B := max Ce 0) (c := -2)
        (by norm_num) (le_max_right Ce 0)
        (by rw [one_mul]; linarith [hDthgXn, hng, hng']) hUhX
    refine ⟨hS7, hM7, ?_⟩
    rw [show |(-(2 : ℝ))| = 2 from by rw [abs_neg]; norm_num] at hX7
    calc Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TUD α EllSol g h)
        ≤ 2 * (Ci * α ^ (-(1 / 2 : ℝ)) * 1 * max Ce 0
            * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
            * Work.FTS.GalFields.Xn5 α h) := hX7
      _ = (2 * (Ci * α ^ (-(1 / 2 : ℝ)) * max Ce 0))
            * ((1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) := by ring
      _ ≤ K * ((1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) := by
            refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (by linarith [hng, hng']) hnh)
            rw [hK]; nlinarith [hc1, hc2, hc3, hc4]
      _ = K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h := by ring
  · -- `TVD = -2α·(V(Φ̃_h)·D_zg)`
    obtain ⟨hS8, hM8, hX8⟩ :=
      honest_mul_swap hN hα hαα₂ (g := g) (g' := g') (h := h)
        (F := fun z θ => Work.Construction.Vop (Work.FTS.GalFields.RHS.Sharp.Dof α EllSol h) z θ)
        (U := Work.Spaces.Dz g)
        hVhS hDzgS hVh4 hDzg4 (A := 1) (B := max Ce 0) (c := -(2 * α))
        (by norm_num) (le_max_right Ce 0)
        (by rw [one_mul]; linarith [hDzgXn, hng, hng']) hVhX
    refine ⟨hS8, hM8, ?_⟩
    rw [show |(-(2 * α))| = 2 * α from by rw [abs_neg]; exact abs_of_nonneg (by linarith)] at hX8
    calc Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TVD α EllSol g h)
        ≤ 2 * α * (Ci * α ^ (-(1 / 2 : ℝ)) * 1 * max Ce 0
            * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
            * Work.FTS.GalFields.Xn5 α h) := hX8
      _ = (2 * α * (Ci * α ^ (-(1 / 2 : ℝ)) * max Ce 0))
            * ((1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) := by ring
      _ ≤ K * ((1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) := by
            refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (by linarith [hng, hng']) hnh)
            rw [hK]; nlinarith [hc1, hc2, hc3, hc4]
      _ = K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h := by ring
  · -- `TDD = -(1/2)·(FK(h)·D_θg)`
    obtain ⟨hS9, hM9, hX9⟩ :=
      honest_mul_swap hN hα hαα₂ (g := g) (g' := g') (h := h)
        (F := fun z _ => Work.Construction.FK h z) (U := Work.Spaces.Dth g)
        hFKhSm hDthgS hFKh.1 hDthg4 (A := 1) (B := Ci) (c := -(1 / 2))
        (by norm_num) (le_of_lt hCi)
        (by rw [one_mul]; linarith [hDthgXn, hng, hng']) hFKhX
    refine ⟨hS9, hM9, ?_⟩
    rw [show |(-(1 / 2 : ℝ))| = 1 / 2 from by rw [abs_neg]; norm_num] at hX9
    calc Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TDD α g h)
        ≤ 1 / 2 * (Ci * α ^ (-(1 / 2 : ℝ)) * 1 * Ci
            * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
            * Work.FTS.GalFields.Xn5 α h) := hX9
      _ = ((1 / 2) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci))
            * ((1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) := by ring
      _ ≤ K * ((1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) := by
            refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (by linarith [hng, hng']) hnh)
            rw [hK]; nlinarith [hc1, hc2, hc3, hc4]
      _ = K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h := by ring
  · -- `TED = -1·((sin²θ·FK(h))·g)`
    obtain ⟨hS10, hM10, hX10⟩ :=
      honest_mul_swap hN hα hαα₂ (g := g) (g' := g') (h := h)
        (F := fun z θ => Work.FTS.GalFields.RHS.Sharp.sinSq θ * Work.Construction.FK h z)
        (U := g)
        hsinFKhS hgS hsinFKhmem (cMem hg (k := 4) (by norm_num))
        (A := 1) (B := Real.sqrt (Cang * Bsin ^ 2) * Ci)
        (c := -1) (by norm_num) (mul_nonneg (Real.sqrt_nonneg _) (le_of_lt hCi))
        (by rw [one_mul]; linarith [hXg, hng, hng']) hsinFKhX
    refine ⟨hS10, hM10, ?_⟩
    rw [show |(-(1 : ℝ))| = 1 from by rw [abs_neg]; norm_num] at hX10
    calc Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TED α g h)
        ≤ 1 * (Ci * α ^ (-(1 / 2 : ℝ)) * 1 * (Real.sqrt (Cang * Bsin ^ 2) * Ci)
            * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
            * Work.FTS.GalFields.Xn5 α h) := hX10
      _ = ((Ci * α ^ (-(1 / 2 : ℝ))) * (Real.sqrt (Cang * Bsin ^ 2) * Ci))
            * ((1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) := by ring
      _ ≤ K * ((1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) := by
            refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (by linarith [hng, hng']) hnh)
            rw [hK]; nlinarith [hc1, hc2, hc3, hc4]
      _ = K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h := by ring

end Work.FTS.StrongEps.EpsRLX.CCSharp.HonTermsC
