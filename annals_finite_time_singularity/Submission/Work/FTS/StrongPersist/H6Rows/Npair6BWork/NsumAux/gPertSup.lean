/-
Copyright: work module for the Elgindi finite-time singularity project.

# `NsumAux/gPertSup` — the three `(perturbed coefficient)·(star slot)` pieces of the `N`-row

The piece `nsP2 = 2·ℛ(Φ̃_f)·F_*` of the level-six `N`-row, bounded in the target shape
`C·α^{-10}·(1+|Ce|+|Cs|)^4·(1+M)^4·(1+HkSq α 6 f)`.

Route: `NsumG.pertPricesNsumG3` (PROVED, guard-compliant) supplies the three `CoefData`'s with the
sharp prices `C0 α^{-1/2}(1+|Ce|)(1+M)`, `2(1+|Ce|)M`, `2(1+|Ce|)HkNorm α 6 f`; `NsumG.fstarDat`
supplies the `SmoothOpen`/`WlInfMem`/price data of the star slots `F_*, D_θF_*, D_zF_*`; the row
`rowCoefSup` gives `C α^{-3}(1+KQ)(1+K0+K4+K6)(1+M)(1+HkNorm α 6 f)`, which the arithmetic lemma
`NsumG.arithNsumG3Sup` converts into the target shape.

This module is the guard-compliant replacement for the three `rowCoefSup` conjuncts of
`NsumG.nsumG3` (whose file exceeds the workspace `maxHeartbeats` limit and therefore cannot be
imported by anything).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.NDefs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowCoefSup
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.fstarDat
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumG.pertPricesNsumG3
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumG.arithNsumG3Sup

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumAux

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-- **The `nsP2 = 2·ℛ(Φ̃_f)·F_*` piece.** -/
theorem nsP2Bound (Ce : ℝ) : ∃ C : ℝ, 0 < C ∧
    ∀ α ∈ Set.Ioc 0 1, ∀ (g Φ : Fam) (τ M Cs : ℝ) (E : Fn → Fn) (Φs : Fn)
      (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      0 ≤ τ →
      Work.FTS.StrongPersist.L6Ctx (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1)
        α M Ce Cs E Φs g Φ τ →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b
          (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsP2 α (slice g τ)
            (E (slice g τ))) (slice g τ)|
        ≤ C * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
            * (1 + Work.Spaces.HkSq α 6 (slice g τ)) := by
  obtain ⟨Csup, hCsuppos, hrowSup⟩ := rowCoefSup
  obtain ⟨Cf, hCfpos, hfst⟩ := fstarDat
  obtain ⟨C0p, C1p, hC0p, hC1p, hprices⟩ := Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumG.pertPricesNsumG3
  refine ⟨16 * (1 + Cf) * (1 + C0p + 2 + 2) * Csup + 1, by positivity, ?_⟩
  intro α hαIoc g Φ τ M Cs E Φs a b ρ hτ hctx hab hleaf
  have hα0 : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  set f : Fn := slice g τ with hf
  set F : Fn := E (slice g τ) with hF
  -- ## the context data
  have hgo : Work.FTS.VocabO.EllPkgGo α Ce f F := hctx.hell.hgo
  have hKk : Work.FTS.StrongPersist.EllPkgK α 6 Ce f F := hctx.hell.hell
  have hbdd : Work.FTS.Nonlin.Xn α f ≤ M := hctx.hbdd
  have hM0 : (0 : ℝ) ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hbdd
  have hQ4 : Work.FTS.VocabO.HQo α 4 f :=
    ⟨hctx.hreg.reg.1,
      Work.FTS.OpenPkg.HkMem_mono_open hctx.hreg.reg.1 4 (by norm_num) hctx.hreg.reg.2⟩
  have hdat : Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M :=
    Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.datData_of_H6Adm hctx.hreg hctx.h7 hctx.hbdd
  obtain ⟨hcd2, -, -, -, -⟩ := hprices α hαIoc Ce M f F hQ4 hbdd hgo hKk
  obtain ⟨hFsm, -, -, hFmem, hFle, -, -, -, -, -⟩ := hfst α hαIoc
  have hH0 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
  have hSq0 : (0 : ℝ) ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hSH : Work.Spaces.HkSq α 6 f = (Work.Spaces.HkNorm α 6 f) ^ 2 :=
    (Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 f)).symm
  -- ## the row
  have hrow := hrowSup α hαIoc
    (fun z θ => 2 * Work.Construction.Rop α (Work.Construction.PhiTil α f F) z θ)
    (Work.Construction.Fstar α) f
    (C0p * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M))
    (2 * (1 + |Ce|) * M) (2 * (1 + |Ce|) * Work.Spaces.HkNorm α 6 f) (Cf * α) M a b ρ
    hcd2 hdat hFsm hFmem hFle hab hleaf
  have har := Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumG.arithNsumG3Sup
    (Cs := Cs) (S := Work.Spaces.HkSq α 6 f) (H := Work.Spaces.HkNorm α 6 f)
    (X := |Work.FTS.TransportS.slotPairing ρ a b
      (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsP2 α f F) f|)
    (kq := Cf) (k0 := C0p) (k4 := 2) (k6 := 2) (KQ := Cf * α)
    (K0 := C0p * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M))
    (K4 := 2 * (1 + |Ce|) * M) (K6 := 2 * (1 + |Ce|) * Work.Spaces.HkNorm α 6 f)
    hrow hα0 hα1 hCsuppos.le hSH hH0 hSq0 hCfpos.le hC0p.le (by norm_num) (by norm_num)
    (by positivity) (by positivity) (by positivity) hM0 (le_of_eq rfl) (le_of_eq rfl)
    (le_of_eq rfl) (le_of_eq rfl)
  refine har.trans ?_
  have hrest : (0 : ℝ) ≤ α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
      * (1 + Work.Spaces.HkSq α 6 f) := by positivity
  have hcle : 16 * (1 + Cf) * (1 + C0p + 2 + 2) * Csup ≤ 16 * (1 + Cf) * (1 + C0p + 2 + 2) * Csup + 1 :=
    by linarith
  calc 16 * (1 + Cf) * (1 + C0p + 2 + 2) * Csup * α ^ (-(10 : ℝ))
        * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4 * (1 + Work.Spaces.HkSq α 6 f)
      = (16 * (1 + Cf) * (1 + C0p + 2 + 2) * Csup) * (α ^ (-(10 : ℝ))
          * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
          * (1 + Work.Spaces.HkSq α 6 f)) := by ring
    _ ≤ (16 * (1 + Cf) * (1 + C0p + 2 + 2) * Csup + 1) * (α ^ (-(10 : ℝ))
          * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
          * (1 + Work.Spaces.HkSq α 6 f)) := mul_le_mul_of_nonneg_right hcle hrest
    _ = (16 * (1 + Cf) * (1 + C0p + 2 + 2) * Csup + 1) * α ^ (-(10 : ℝ))
          * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4 * (1 + Work.Spaces.HkSq α 6 f) := by ring

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumAux
