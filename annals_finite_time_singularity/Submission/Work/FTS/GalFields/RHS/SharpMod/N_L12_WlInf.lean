/-
# `SharpMod/N_L12_WlInf` — the ten `𝒲^{4,∞}`-priced term bounds of the difference of `N`

The pointwise telescoping (`SharpAux/Core`, `SharpAux/Identity`)

`N α (F_*+g) (Φ_s+EllSol g) - N α (F_*+g') (Φ_s+EllSol g') = Σ_{i<20} T_i`

splits the twenty monomials of `SharpAux/Defs` into ten whose *first* factor is priced by the
`𝒲^{4,∞}`-norm (`Sharp.TRA`, `TUA`, `TVA`, `TRC`, `TUC`, `TVC`, `TDA`, `TDC`, `TEA`, `TEC`) and
ten whose two factors are both `ℋ⁴`-honest.  This file proves the first bundle: for each of the
ten monomials `T`,

  `SmoothOpen T ∧ HkMem α 4 T ∧ Xn α T ≤ K·(1 + |g|_{ℋ⁵} + |g'|_{ℋ⁵})·|h|_{ℋ⁵}`

on the Galerkin class, with a single constant `K` depending only on `α, Φs, Ci, Ce, Cs` — never
on `g, g', h`.

Each monomial is `a·(f·u)` with `f` a `𝒲^{4,∞}`-coefficient (`StarH/UsPhi/Vstar α Φs` via the
`RW`/`UsW`/`VW` fields of `StarPkgo2`; `F_*`, `D_θF_*`, `D_zF_*`; `FK(F_*) = 2α·hKer`), `u` an
honest `ℋ⁴`-function (`z/(1+z)·h`, `D_θh`, `D_zh`, `FK h`, `sin²θ·h`, `sin²θ·FK h`, or one of the
`Φ̃_h`-outputs of the elliptic package `hell`), and `a` a scalar.  The product rule
`Sharp.Xn_mul_wlInf` prices `f·u`; the five bookkeeping lemmas
(`Xn_le_Xn5_of_mem5`, `wlProd_bound`, `sinSq_mul_honest`, `maxScale_le`, `shape_le`) live in the
sibling module `N_L12_WlInfAux` (imported below), which keeps this file under the build guard's
size limit.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.GalFields.RHS.SharpMod.N_L12_WlInfAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.RHS.SharpMod

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

theorem N_L12_WlInf {α α₂ Ci Ce Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {EllSol : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hell : ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.Nonlin.GalClass α g →
      Work.FTS.VocabO.EllPkgGo α Ce g (EllSol g))
    (hα : 0 < α) (hαα₂ : α ≤ α₂) :
    ∃ K : ℝ, 0 < K ∧ ∀ {g g' h : Work.FTS.Galerkin.Fn},
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.GalClass α g' →
      Work.FTS.Nonlin.GalClass α h → α ≤ 1 →
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TRA α Φs h) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TRA α Φs h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TRA α Φs h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TUA α Φs h) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TUA α Φs h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TUA α Φs h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TVA α Φs h) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TVA α Φs h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TVA α Φs h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TRC α EllSol h) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TRC α EllSol h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TRC α EllSol h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TUC α EllSol h) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TUC α EllSol h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TUC α EllSol h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TVC α EllSol h) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TVC α EllSol h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TVC α EllSol h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TDA α h) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TDA α h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TDA α h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TDC α h) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TDC α h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TDC α h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TEA α h) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TEA α h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TEA α h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TEC α h) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TEC α h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TEC α h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) := by
  -- the fixed constants of the chapter
  obtain ⟨Cφ, hCφpos, hCφ⟩ := Work.FTS.NonlinRows.NRow10aux.mul_phi_Hk
  obtain ⟨B, hBpos, hBSI, hBbnd, hBdth⟩ :=
    Work.FTS.Nonlinear.Pieces.RNP.RNP24.angProfile_sinSq
  obtain ⟨_cF, _hF, hFstarW⟩ := Work.FTS.Nonlin.Fstar_W
  obtain ⟨_cD, _hD, hDthFstarW⟩ := Work.FTS.Nonlin.DthFstar_W
  obtain ⟨_cZ, _hZ, hDzFstarW⟩ := Work.FTS.Nonlin.DzFstar_W
  -- the ten amplitudes
  set A1 : ℝ := |(2 : ℝ)| * (Ci * α ^ (-(1 / 2 : ℝ))
    * Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.StarH α Φs) * Cφ) with hA1
  set A2 : ℝ := |(-2 : ℝ)| * (Ci * α ^ (-(1 / 2 : ℝ))
    * Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.UsPhi α Φs) * 1) with hA2
  set A3 : ℝ := |(-(2 * α))| * (Ci * α ^ (-(1 / 2 : ℝ))
    * Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.Vstar α Φs) * 1) with hA3
  set A4 : ℝ := |(2 : ℝ)| * (Ci * α ^ (-(1 / 2 : ℝ))
    * Work.Spaces.WlInf α 4 (Work.Construction.Fstar α) * max Ce 0) with hA4
  set A5 : ℝ := |(-2 : ℝ)| * (Ci * α ^ (-(1 / 2 : ℝ))
    * Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.DthFstar α) * max Ce 0) with hA5
  set A6 : ℝ := |(-(2 * α))| * (Ci * α ^ (-(1 / 2 : ℝ))
    * Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.DzFstar α) * max Ce 0) with hA6
  set A7 : ℝ := |(-(1 / 2 : ℝ))| * (Ci * α ^ (-(1 / 2 : ℝ))
    * Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.Fkstar α) * 1) with hA7
  set A8 : ℝ := |(-(1 / 2 : ℝ))| * (Ci * α ^ (-(1 / 2 : ℝ))
    * Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.DthFstar α) * Ci) with hA8
  set A9 : ℝ := |(-1 : ℝ)| * (Ci * α ^ (-(1 / 2 : ℝ))
    * Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.Fkstar α) * (B * Ci * 1)) with hA9
  set A10 : ℝ := |(-1 : ℝ)| * (Ci * α ^ (-(1 / 2 : ℝ))
    * Work.Spaces.WlInf α 4 (Work.Construction.Fstar α) * (B * Ci * Ci)) with hA10
  set K : ℝ := 1 + (|A1| + |A2| + |A3| + |A4| + |A5| + |A6| + |A7| + |A8| + |A9| + |A10|)
    with hK
  have hKpos : 0 < K := by
    rw [hK]
    linarith [abs_nonneg A1, abs_nonneg A2, abs_nonneg A3, abs_nonneg A4, abs_nonneg A5,
      abs_nonneg A6, abs_nonneg A7, abs_nonneg A8, abs_nonneg A9, abs_nonneg A10]
  have hA1K : A1 ≤ K := by
    rw [hK]
    linarith [le_abs_self A1, abs_nonneg A2, abs_nonneg A3, abs_nonneg A4, abs_nonneg A5,
      abs_nonneg A6, abs_nonneg A7, abs_nonneg A8, abs_nonneg A9, abs_nonneg A10]
  have hA2K : A2 ≤ K := by
    rw [hK]
    linarith [le_abs_self A2, abs_nonneg A1, abs_nonneg A3, abs_nonneg A4, abs_nonneg A5,
      abs_nonneg A6, abs_nonneg A7, abs_nonneg A8, abs_nonneg A9, abs_nonneg A10]
  have hA3K : A3 ≤ K := by
    rw [hK]
    linarith [le_abs_self A3, abs_nonneg A1, abs_nonneg A2, abs_nonneg A4, abs_nonneg A5,
      abs_nonneg A6, abs_nonneg A7, abs_nonneg A8, abs_nonneg A9, abs_nonneg A10]
  have hA4K : A4 ≤ K := by
    rw [hK]
    linarith [le_abs_self A4, abs_nonneg A1, abs_nonneg A2, abs_nonneg A3, abs_nonneg A5,
      abs_nonneg A6, abs_nonneg A7, abs_nonneg A8, abs_nonneg A9, abs_nonneg A10]
  have hA5K : A5 ≤ K := by
    rw [hK]
    linarith [le_abs_self A5, abs_nonneg A1, abs_nonneg A2, abs_nonneg A3, abs_nonneg A4,
      abs_nonneg A6, abs_nonneg A7, abs_nonneg A8, abs_nonneg A9, abs_nonneg A10]
  have hA6K : A6 ≤ K := by
    rw [hK]
    linarith [le_abs_self A6, abs_nonneg A1, abs_nonneg A2, abs_nonneg A3, abs_nonneg A4,
      abs_nonneg A5, abs_nonneg A7, abs_nonneg A8, abs_nonneg A9, abs_nonneg A10]
  have hA7K : A7 ≤ K := by
    rw [hK]
    linarith [le_abs_self A7, abs_nonneg A1, abs_nonneg A2, abs_nonneg A3, abs_nonneg A4,
      abs_nonneg A5, abs_nonneg A6, abs_nonneg A8, abs_nonneg A9, abs_nonneg A10]
  have hA8K : A8 ≤ K := by
    rw [hK]
    linarith [le_abs_self A8, abs_nonneg A1, abs_nonneg A2, abs_nonneg A3, abs_nonneg A4,
      abs_nonneg A5, abs_nonneg A6, abs_nonneg A7, abs_nonneg A9, abs_nonneg A10]
  have hA9K : A9 ≤ K := by
    rw [hK]
    linarith [le_abs_self A9, abs_nonneg A1, abs_nonneg A2, abs_nonneg A3, abs_nonneg A4,
      abs_nonneg A5, abs_nonneg A6, abs_nonneg A7, abs_nonneg A8, abs_nonneg A10]
  have hA10K : A10 ≤ K := by
    rw [hK]
    linarith [le_abs_self A10, abs_nonneg A1, abs_nonneg A2, abs_nonneg A3, abs_nonneg A4,
      abs_nonneg A5, abs_nonneg A6, abs_nonneg A7, abs_nonneg A8, abs_nonneg A9]
  refine ⟨K, hKpos, ?_⟩
  intro g g' h hg hg' hh hα1
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  have hYh : 0 ≤ Work.FTS.GalFields.Xn5 α h := Real.sqrt_nonneg _
  -- the `GalClass` facts about the difference datum `h`
  have hPhS : Work.FTS.EllipticEst.SmoothOpen h :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad hh.reg.1
  have hPh5 : Work.Spaces.HkMem α 5 h := Work.FTS.OpenPkg.galClass_HkMem5 hh
  have hPhQ : Work.FTS.VocabO.HQo α 4 h := Work.FTS.OpenPkg.galClass_HQo4 hh
  have hXh : Work.FTS.Nonlin.Xn α h ≤ Work.FTS.GalFields.Xn5 α h := Xn_le_Xn5_of_mem5 hPh5
  -- ## the coefficient atoms
  have hStarH_sm : Work.FTS.EllipticEst.SmoothOpen
      (Work.FTS.GalFields.RHS.Sharp.StarH α Φs) :=
    Work.FTS.NonlinRows.NRow10aux.starH_smoothOpen hα hα1 hstar.toStarPkgo
  have hStarH_mem : Work.Spaces.WlInfMem α 4 (Work.FTS.GalFields.RHS.Sharp.StarH α Φs) :=
    hstar.RW.1
  have hfields := Work.FTS.PhiStar.CoreAux.fields_smooth hα hα1 hstar.toStarPkgo.smooth
  have hUs_sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.UsPhi α Φs) :=
    hfields.2.2.2.2.1
  have hUs_mem : Work.Spaces.WlInfMem α 4 (Work.FTS.GalFields.RHS.Sharp.UsPhi α Φs) :=
    hstar.UsW.1
  have hVs_sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.Vstar α Φs) :=
    hfields.2.2.1
  have hVs_mem : Work.Spaces.WlInfMem α 4 (Work.FTS.GalFields.RHS.Sharp.Vstar α Φs) :=
    hstar.VW.1
  have hFstar_sm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  have hFstar_mem : Work.Spaces.WlInfMem α 4 (Work.Construction.Fstar α) :=
    (hFstarW α hα hα1).1
  have hDthF_sm : Work.FTS.EllipticEst.SmoothOpen
      (Work.FTS.GalFields.RHS.Sharp.DthFstar α) :=
    Work.FTS.EllipticEst.SmoothOpen.Dth hFstar_sm
  have hDthF_mem : Work.Spaces.WlInfMem α 4 (Work.FTS.GalFields.RHS.Sharp.DthFstar α) :=
    (hDthFstarW α hα hα1).1
  have hDzF_sm : Work.FTS.EllipticEst.SmoothOpen
      (Work.FTS.GalFields.RHS.Sharp.DzFstar α) :=
    Work.FTS.EllipticEst.SmoothOpen.Dz hFstar_sm
  have hDzF_mem : Work.Spaces.WlInfMem α 4 (Work.FTS.GalFields.RHS.Sharp.DzFstar α) :=
    (hDzFstarW α hα hα1).1
  have hFk_sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.Fkstar α) := by
    show Work.FTS.EllipticEst.SmoothOpen (fun z _ => 2 * α * Work.Spaces.hKer z)
    refine Work.FTS.NonlinRows.smoothOpen_radial
      (r := fun z : ℝ => 2 * α * Work.Spaces.hKer z) ?_
    intro n
    have hker : ContDiffOn ℝ n (fun z : ℝ => Work.Spaces.hKer z) (Set.Ioi 0) := by
      simp only [Work.Spaces.hKer_apply]
      exact contDiffOn_id.div
        (((contDiffOn_const (c := (1 : ℝ)) (s := Set.Ioi 0)).add
          (contDiffOn_id (𝕜 := ℝ) (s := Set.Ioi 0))).pow 2)
        (fun z hz => pow_ne_zero 2 (by have hz' : (0 : ℝ) < z := hz; linarith))
    exact (contDiffOn_const (𝕜 := ℝ) (c := 2 * α) (s := Set.Ioi 0)).mul hker
  have hFk_mem : Work.Spaces.WlInfMem α 4 (Work.FTS.GalFields.RHS.Sharp.Fkstar α) :=
    (Work.FTS.Nonlinear.Pieces.RNP.hKerConstWlInf α (2 * α)).1
  -- ## the honest atoms
  have hDth_sm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth h) :=
    Work.FTS.EllipticEst.SmoothOpen.Dth hPhS
  have hDth_mem : Work.Spaces.HkMem α 4 (Work.Spaces.Dth h) :=
    Work.FTS.IPGen.HkMem_Dth_le (by linarith : -(1 / 10 : ℝ) ≤ α) hPhS hPh5
  have hDth_bnd : Work.FTS.Nonlin.Xn α (Work.Spaces.Dth h) ≤ 1 * Work.FTS.GalFields.Xn5 α h := by
    rw [one_mul]
    exact Work.FTS.GalFields.Xn_Dth_le_Xn5 hα hPh5
  have hDz_sm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz h) :=
    Work.FTS.EllipticEst.SmoothOpen.Dz hPhS
  have hDz_mem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz h) :=
    Work.FTS.IPGen.HkMem_Dz_le hPhS hPh5
  have hDz_bnd : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz h) ≤ 1 * Work.FTS.GalFields.Xn5 α h := by
    rw [one_mul]
    exact Work.FTS.GalFields.Xn_Dz_le_Xn5 hα hPhS hPh5
  have hpf_sm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.FTS.GalFields.RHS.Sharp.pfac z * h z θ) :=
    Work.FTS.NonlinRows.smoothOpen_mul
      Work.FTS.NonlinRows.NRow10aux.phiSelf_smoothOpen hPhS
  have hpf_mem : Work.Spaces.HkMem α 4
      (fun z θ => Work.FTS.GalFields.RHS.Sharp.pfac z * h z θ) := by
    simpa only [Work.FTS.GalFields.RHS.Sharp.pfac] using (hCφ hα hα1 hPhQ).1
  have hpf_bnd : Work.FTS.Nonlin.Xn α
      (fun z θ => Work.FTS.GalFields.RHS.Sharp.pfac z * h z θ)
      ≤ Cφ * Work.FTS.GalFields.Xn5 α h := by
    have h1 : Work.FTS.Nonlin.Xn α (fun z θ => z / (1 + z) * h z θ)
        ≤ Cφ * Work.FTS.Nonlin.Xn α h := (hCφ hα hα1 hPhQ).2
    have h2 : Cφ * Work.FTS.Nonlin.Xn α h ≤ Cφ * Work.FTS.GalFields.Xn5 α h :=
      mul_le_mul_of_nonneg_left hXh (le_of_lt hCφpos)
    simpa only [Work.FTS.GalFields.RHS.Sharp.pfac] using le_trans h1 h2
  have hFKh_sm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.FK h z) :=
    Work.FTS.GalFields.RHS.smoothOpen_FK_of_pkg_gal hα hα1 hh hPhS
      hstar.toStarPkgo.smooth (hell h hh).smooth (hell h hh) hstar
  have hFKh_mem : Work.Spaces.HkMem α 4 (fun z _ => Work.Construction.FK h z) :=
    (hN.fkH α hIoc h hPhQ hh.l12).1
  have hFKh_bnd : Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK h z)
      ≤ Ci * Work.FTS.GalFields.Xn5 α h :=
    le_trans (hN.fkH α hIoc h hPhQ hh.l12).2
      (mul_le_mul_of_nonneg_left hXh (le_of_lt hN.pos.1))
  -- ## the `Φ̃_h`-atoms (the elliptic outputs of `hell`)
  have hRop_sm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Rop α (Work.FTS.GalFields.RHS.Sharp.Dof α EllSol h)) :=
    (hell h hh).R.1.1
  have hRop_mem : Work.Spaces.HkMem α 4
      (Work.Construction.Rop α (Work.FTS.GalFields.RHS.Sharp.Dof α EllSol h)) :=
    (hell h hh).R.1.2
  have hRop_bnd : Work.FTS.Nonlin.Xn α
      (Work.Construction.Rop α (Work.FTS.GalFields.RHS.Sharp.Dof α EllSol h))
      ≤ max Ce 0 * Work.FTS.GalFields.Xn5 α h :=
    maxScale_le (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hYh (hell h hh).R.2 hXh
  have hUop_sm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.Uop α (Work.FTS.GalFields.RHS.Sharp.Dof α EllSol h) z θ
        / Work.Construction.s2 θ) := (hell h hh).U.1.1
  have hUop_mem : Work.Spaces.HkMem α 4
      (fun z θ => Work.Construction.Uop α (Work.FTS.GalFields.RHS.Sharp.Dof α EllSol h) z θ
        / Work.Construction.s2 θ) := (hell h hh).U.1.2
  have hUop_bnd : Work.FTS.Nonlin.Xn α
      (fun z θ => Work.Construction.Uop α (Work.FTS.GalFields.RHS.Sharp.Dof α EllSol h) z θ
        / Work.Construction.s2 θ) ≤ max Ce 0 * Work.FTS.GalFields.Xn5 α h :=
    maxScale_le (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hYh (hell h hh).U.2 hXh
  have hVop_sm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Vop (Work.FTS.GalFields.RHS.Sharp.Dof α EllSol h)) :=
    (hell h hh).V.1.1
  have hVop_mem : Work.Spaces.HkMem α 4
      (Work.Construction.Vop (Work.FTS.GalFields.RHS.Sharp.Dof α EllSol h)) :=
    (hell h hh).V.1.2
  have hVop_bnd : Work.FTS.Nonlin.Xn α
      (Work.Construction.Vop (Work.FTS.GalFields.RHS.Sharp.Dof α EllSol h))
      ≤ max Ce 0 * Work.FTS.GalFields.Xn5 α h :=
    maxScale_le (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hYh (hell h hh).V.2 hXh
  -- ## the two `sin²θ`-atoms
  obtain ⟨hSqHsm, hSqHmem, hSqHbd⟩ := sinSq_mul_honest hN hα hαα₂ hBpos hBSI hBbnd hBdth
    hPhS hPhQ.2 (Bu := 1) (by rw [one_mul]; exact hXh)
  obtain ⟨hSqFsm, hSqFmem, hSqFbd⟩ := sinSq_mul_honest hN hα hαα₂ hBpos hBSI hBbnd hBdth
    hFKh_sm hFKh_mem (Bu := Ci) hFKh_bnd
  -- ## the ten term bounds
  obtain ⟨hTRAsm, hTRAmem, hTRAbd⟩ := wlProd_bound hN hα hαα₂ hStarH_sm hStarH_mem
    hpf_sm hpf_mem
    (le_rfl : Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.StarH α Φs)
      ≤ Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.StarH α Φs)) hpf_bnd (2 : ℝ)
  have hTRA : Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TRA α Φs h)
      ≤ A1 * Work.FTS.GalFields.Xn5 α h := by
    rw [hA1]
    exact hTRAbd
  obtain ⟨hTUAsm, hTUAmem, hTUAbd⟩ := wlProd_bound hN hα hαα₂ hUs_sm hUs_mem
    hDth_sm hDth_mem
    (le_rfl : Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.UsPhi α Φs)
      ≤ Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.UsPhi α Φs)) hDth_bnd (-2 : ℝ)
  have hTUA : Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TUA α Φs h)
      ≤ A2 * Work.FTS.GalFields.Xn5 α h := by
    rw [hA2]
    exact hTUAbd
  obtain ⟨hTVAsm, hTVAmem, hTVAbd⟩ := wlProd_bound hN hα hαα₂ hVs_sm hVs_mem
    hDz_sm hDz_mem
    (le_rfl : Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.Vstar α Φs)
      ≤ Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.Vstar α Φs)) hDz_bnd (-(2 * α))
  have hTVA : Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TVA α Φs h)
      ≤ A3 * Work.FTS.GalFields.Xn5 α h := by
    rw [hA3]
    exact hTVAbd
  obtain ⟨hTRCsm, hTRCmem, hTRCbd⟩ := wlProd_bound hN hα hαα₂ hFstar_sm hFstar_mem
    hRop_sm hRop_mem
    (le_rfl : Work.Spaces.WlInf α 4 (Work.Construction.Fstar α)
      ≤ Work.Spaces.WlInf α 4 (Work.Construction.Fstar α)) hRop_bnd (2 : ℝ)
  have hTRC : Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TRC α EllSol h)
      ≤ A4 * Work.FTS.GalFields.Xn5 α h := by
    rw [hA4]
    exact hTRCbd
  obtain ⟨hTUCsm, hTUCmem, hTUCbd⟩ := wlProd_bound hN hα hαα₂ hDthF_sm hDthF_mem
    hUop_sm hUop_mem
    (le_rfl : Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.DthFstar α)
      ≤ Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.DthFstar α)) hUop_bnd (-2 : ℝ)
  have hTUC : Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TUC α EllSol h)
      ≤ A5 * Work.FTS.GalFields.Xn5 α h := by
    rw [hA5]
    exact hTUCbd
  obtain ⟨hTVCsm, hTVCmem, hTVCbd⟩ := wlProd_bound hN hα hαα₂ hDzF_sm hDzF_mem
    hVop_sm hVop_mem
    (le_rfl : Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.DzFstar α)
      ≤ Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.DzFstar α)) hVop_bnd (-(2 * α))
  have hTVC : Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TVC α EllSol h)
      ≤ A6 * Work.FTS.GalFields.Xn5 α h := by
    rw [hA6]
    exact hTVCbd
  obtain ⟨hTDAsm, hTDAmem, hTDAbd⟩ := wlProd_bound hN hα hαα₂ hFk_sm hFk_mem
    hDth_sm hDth_mem
    (le_rfl : Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.Fkstar α)
      ≤ Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.Fkstar α)) hDth_bnd (-(1 / 2))
  have hTDA : Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TDA α h)
      ≤ A7 * Work.FTS.GalFields.Xn5 α h := by
    rw [hA7]
    exact hTDAbd
  obtain ⟨hTDCsm, hTDCmem, hTDCbd⟩ := wlProd_bound hN hα hαα₂ hDthF_sm hDthF_mem
    hFKh_sm hFKh_mem
    (le_rfl : Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.DthFstar α)
      ≤ Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.DthFstar α)) hFKh_bnd (-(1 / 2))
  have hTDC : Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TDC α h)
      ≤ A8 * Work.FTS.GalFields.Xn5 α h := by
    rw [hA8]
    exact hTDCbd
  obtain ⟨hTEAsm, hTEAmem, hTEAbd⟩ := wlProd_bound hN hα hαα₂ hFk_sm hFk_mem
    hSqHsm hSqHmem
    (le_rfl : Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.Fkstar α)
      ≤ Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.Fkstar α)) hSqHbd (-1 : ℝ)
  have hTEA : Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TEA α h)
      ≤ A9 * Work.FTS.GalFields.Xn5 α h := by
    rw [hA9]
    exact hTEAbd
  obtain ⟨hTECsm, hTECmem, hTECbd⟩ := wlProd_bound hN hα hαα₂ hFstar_sm hFstar_mem
    hSqFsm hSqFmem
    (le_rfl : Work.Spaces.WlInf α 4 (Work.Construction.Fstar α)
      ≤ Work.Spaces.WlInf α 4 (Work.Construction.Fstar α)) hSqFbd (-1 : ℝ)
  have hTEC : Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TEC α h)
      ≤ A10 * Work.FTS.GalFields.Xn5 α h := by
    rw [hA10]
    exact hTECbd
  -- ## the assembly
  have hK0 : 0 ≤ K := le_of_lt hKpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨hTRAsm, hTRAmem, le_trans hTRA (shape_le hK0 hA1K)⟩
  · exact ⟨hTUAsm, hTUAmem, le_trans hTUA (shape_le hK0 hA2K)⟩
  · exact ⟨hTVAsm, hTVAmem, le_trans hTVA (shape_le hK0 hA3K)⟩
  · exact ⟨hTRCsm, hTRCmem, le_trans hTRC (shape_le hK0 hA4K)⟩
  · exact ⟨hTUCsm, hTUCmem, le_trans hTUC (shape_le hK0 hA5K)⟩
  · exact ⟨hTVCsm, hTVCmem, le_trans hTVC (shape_le hK0 hA6K)⟩
  · exact ⟨hTDAsm, hTDAmem, le_trans hTDA (shape_le hK0 hA7K)⟩
  · exact ⟨hTDCsm, hTDCmem, le_trans hTDC (shape_le hK0 hA8K)⟩
  · exact ⟨hTEAsm, hTEAmem, le_trans hTEA (shape_le hK0 hA9K)⟩
  · exact ⟨hTECsm, hTECmem, le_trans hTEC (shape_le hK0 hA10K)⟩

end Work.FTS.GalFields.RHS.SharpMod
