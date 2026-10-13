/-
# `H5/AtomsW5` — the `𝒲^{5,∞}`-priced atoms of the level-`5` `N`-block

The twenty pieces of `N α (F_*+w) (Φs+Φg)` pair a `𝒲^{5,∞}`-priced factor (the three star
coefficients and the four fixed profiles `F_*`, `D_θF_*`, `D_zF_*`, `-2α hKer`) with an
`ℋ⁵`-honest one, or two `ℋ⁵`-honest ones.  This file supplies the `𝒲^{5,∞}` data:
`SmoothOpen` together with `WlInfMem α 5` and a bound on `WlInf α 5`, for

* the three star coefficients `((z+1)/z)ℛ(Φ̃_*)`, `((z+1)/z)𝒰(Φ̃_*)/sin 2θ`, `((z+1)/z)𝒱(Φ̃_*)`
  (from the level-six star fields of `StarPkg6` by monotonicity of `WlInf`); the constant may
  depend on `Cs6` and `α` but not on `Φs`;
* the fixed profiles `F_*` (`StrongPersist.Fstar_W6`), `D_θF_*` (`DthFstar_W6`), `D_zF_*`
  (`DzFstar_W6`) and `-2α hKer` (`H5.hKerConstWlInf_l`),

all by `6 → 5` (resp. level-free) monotonicity.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FTS.StrongEps.H5.WlInfMem_mono
import Submission.Work.FTS.StrongEps.H5.hKerConstWlInf_l
import Submission.Work.FTS.StrongPersist.Fstar_W6
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.DzFstar_W6
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnNAux
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.LocData.SmoothQuad_Fstar

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5.Atoms

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The three star coefficients -/

/-- **The three star coefficients at level `5`**, as `𝒲^{5,∞}`-valued atoms.  The constant may
depend on `Cs6` and `α`, but not on `Φs`. -/
theorem WAtomsStar5 : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {Cs6 : ℝ},
    ∃ a : ℝ, 0 < a ∧ ∀ {Φs : Fn}, Work.FTS.StrongPersist.StarPkg6 α Cs6 Φs →
      (Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z
          * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ) ∧
        Work.Spaces.WlInfMem α 5 (fun z θ => (z + 1) / z
          * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ) ∧
        Work.Spaces.WlInf α 5 (fun z θ => (z + 1) / z
          * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ) ≤ a) ∧
      (Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z
          * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
            / Work.Construction.s2 θ)) ∧
        Work.Spaces.WlInfMem α 5 (fun z θ => (z + 1) / z
          * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
            / Work.Construction.s2 θ)) ∧
        Work.Spaces.WlInf α 5 (fun z θ => (z + 1) / z
          * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
            / Work.Construction.s2 θ)) ≤ a) ∧
      (Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z
          * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ) ∧
        Work.Spaces.WlInfMem α 5 (fun z θ => (z + 1) / z
          * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ) ∧
        Work.Spaces.WlInf α 5 (fun z θ => (z + 1) / z
          * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ) ≤ a) := by
  intro α hαI Cs6
  have hα0 : 0 < α := hαI.1
  have hα1 : α ≤ 1 := hαI.2
  refine ⟨|Cs6 * α| + 1, by positivity, fun {Φs} hstar => ?_⟩
  have hsw : Work.FTS.VocabO.StarPkgo α Cs6 Φs := hstar.toStarPkgo2.toStarPkgo
  have h1 := Work.FTS.StrongPersist.StarPkg6.RW6_mem hstar
  have h1b := Work.FTS.StrongPersist.StarPkg6.RW6_bd hstar
  have h2 := Work.FTS.StrongPersist.StarPkg6.UszW6_mem hstar
  have h2b := Work.FTS.StrongPersist.StarPkg6.UszW6_bd hstar
  have h3 := Work.FTS.StrongPersist.StarPkg6.VzW6_mem hstar
  have h3b := Work.FTS.StrongPersist.StarPkg6.VzW6_bd hstar
  obtain ⟨h1m, h1l⟩ := WlInfMem_mono (α := α) (l := 6) (l' := 5) (by norm_num) h1
  obtain ⟨h2m, h2l⟩ := WlInfMem_mono (α := α) (l := 6) (l' := 5) (by norm_num) h2
  obtain ⟨h3m, h3l⟩ := WlInfMem_mono (α := α) (l := 6) (l' := 5) (by norm_num) h3
  have hCs : Cs6 * α ≤ |Cs6 * α| + 1 := by linarith [le_abs_self (Cs6 * α)]
  exact ⟨⟨Work.FTS.StrongEps.ClassCRHS.smoothOpen_Rs_of_star hα0 hα1 hsw, h1m,
      le_trans (le_trans h1l h1b) hCs⟩,
    ⟨Work.FTS.StrongEps.ClassCRHS.smoothOpen_Us_of_star hα0 hα1 hsw, h2m,
      le_trans (le_trans h2l h2b) hCs⟩,
    ⟨Work.FTS.StrongEps.ClassCRHS.smoothOpen_Vs_of_star hα0 hα1 hsw, h3m,
      le_trans (le_trans h3l h3b) hCs⟩⟩

/-! ## The four fixed profiles -/

/-- **The four fixed `𝒲^{5,∞}`-priced profiles at level `5`.** -/
theorem WAtomsFixed5 : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 →
    ∃ a : ℝ, 0 < a ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) ∧
        Work.Spaces.WlInfMem α 5 (Work.Construction.Fstar α) ∧
        Work.Spaces.WlInf α 5 (Work.Construction.Fstar α) ≤ a) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth (Work.Construction.Fstar α)) ∧
        Work.Spaces.WlInfMem α 5 (Work.Spaces.Dth (Work.Construction.Fstar α)) ∧
        Work.Spaces.WlInf α 5 (Work.Spaces.Dth (Work.Construction.Fstar α)) ≤ a) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz (Work.Construction.Fstar α)) ∧
        Work.Spaces.WlInfMem α 5 (Work.Spaces.Dz (Work.Construction.Fstar α)) ∧
        Work.Spaces.WlInf α 5 (Work.Spaces.Dz (Work.Construction.Fstar α)) ≤ a) ∧
      (Work.FTS.EllipticEst.SmoothOpen (fun z _ => (-(2 * α)) * Work.Spaces.hKer z) ∧
        Work.Spaces.WlInfMem α 5 (fun z _ => (-(2 * α)) * Work.Spaces.hKer z) ∧
        Work.Spaces.WlInf α 5 (fun z _ => (-(2 * α)) * Work.Spaces.hKer z) ≤ a) := by
  intro α hαI
  have hα0 : 0 < α := hαI.1
  have hα1 : α ≤ 1 := hαI.2
  obtain ⟨C1, hC1, hF⟩ := Work.FTS.StrongPersist.Fstar_W6
  obtain ⟨C2, hC2, hDF⟩ := Work.FTS.StrongPersist.DthFstar_W6
  obtain ⟨C3, hC3, hDZ⟩ := Work.FTS.StrongPersist.DzFstar_W6
  obtain ⟨C4, hC4, hK⟩ := hKerConstWlInf_l 5
  obtain ⟨hFm, hFl⟩ := hF α hα0 hα1
  obtain ⟨hDFm, hDFl⟩ := hDF α hα0 hα1
  obtain ⟨hDZm, hDZl⟩ := hDZ α hα0 hα1
  obtain ⟨hKm, hKl⟩ := hK α (-(2 * α))
  obtain ⟨hF5m, hF5l⟩ := WlInfMem_mono (α := α) (l := 6) (l' := 5) (by norm_num) hFm
  obtain ⟨hDF5m, hDF5l⟩ := WlInfMem_mono (α := α) (l := 6) (l' := 5) (by norm_num) hDFm
  obtain ⟨hDZ5m, hDZ5l⟩ := WlInfMem_mono (α := α) (l := 6) (l' := 5) (by norm_num) hDZm
  have hFsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.EllipticEst.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  have h1nn : 0 ≤ C1 * α := mul_nonneg hC1.le hα0.le
  have h2nn : 0 ≤ C2 * α ^ 2 := mul_nonneg hC2.le (sq_nonneg α)
  have h3nn : 0 ≤ C3 * α := mul_nonneg hC3.le hα0.le
  have h4nn : 0 ≤ C4 * |-(2 * α)| := mul_nonneg hC4.le (abs_nonneg _)
  refine ⟨C1 * α + C2 * α ^ 2 + C3 * α + C4 * |-(2 * α)| + 1, by linarith, ?_, ?_, ?_, ?_⟩
  · exact ⟨hFsm, hF5m, le_trans hF5l (by linarith)⟩
  · exact ⟨hFsm.Dth, hDF5m, le_trans hDF5l (by linarith)⟩
  · exact ⟨hFsm.Dz, hDZ5m, le_trans hDZ5l (by linarith)⟩
  · exact ⟨Work.FTS.StrongEps.ClassCRHS.smoothOpen_FKneg α, hKm, le_trans hKl (by linarith)⟩

end Work.FTS.StrongEps.H5.Atoms
