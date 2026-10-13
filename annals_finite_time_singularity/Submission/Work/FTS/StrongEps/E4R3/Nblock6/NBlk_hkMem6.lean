import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.Route
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.Defs
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnNDefs
import Submission.Work.FTS.StrongPersist.H6Row6.nsum_split6
import Submission.Work.FTS.StrongPersist.H6Row6.NS6.Pieces
import Submission.Work.FTS.StrongPersist.N6.Prod6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.fk_hkMem
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.SmHm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Nblock6.NBlk_hkMem6` — the twenty pieces of the `N`-block are honest in `ℋ⁶`

For every level-six datum `(w, Φs, Φg)` of the E4 node (`ClassC α w`, `Xn α w ≤ C₀ α²`,
`w` vanishing off the open quadrant, `EllPkgGo α Ce w Φg`, `ClassC.EllPkgK α 6 Ce w Φg`,
`StarPkg6 α Cs Φs`) and every `k < 20`, the `k`-th product-form piece
`ClassCRHS.NBlk α w Φs Φg k` of the nonlinear term is honest in `ℋ⁶`.

## The route

The twenty pieces `NBlk α w Φs Φg k` are — up to the permutation `NBlkPerm` of the two
factors of each piece and the two elementary `(z+1)/z`-shifts (valid on the open quadrant,
where `z ≠ 0`) — literally the twenty pieces `pcs α w Φg Φs k` of the **level-six `N`-row**
(`H6Rows.Npair6SupAux.nsP0 … nsP19`), whose `ℋ⁶`-honesty and `C⁶`-regularity on the open
quadrant is the *proved* statement `H6Row6.NS6.pieces`, from the bundled level-six data
`H6Row6.NS6.Data α Ce Cs w Φg Φs`.

We assemble that data from the hypotheses of the task:

* `SmoothOpen w`, `HkMem α 7 w`, `L₁₂(w)(0) = 0` are fields of `ClassC α w`;
* `HkMem α 6 w` is the level-descent of `HkMem α 7 w` (`OpenPkg.HkMem_mono_open`);
* `H6Adm α w` is `StrongEps.H6Adm_of_classC_of_eqzero` (the off-quadrant vanishing);
* `SmoothOpen Φg` is `EllPkgGo.smooth`, `SmoothOpen Φs` is `StarPkg6.smooth`;
* `StrongPersist.EllPkgK α 6 Ce w Φg` is the repackaging of `ClassC.EllPkgK α 6 Ce w Φg`
  (`Apriori4Proofs.blocks.N_aux.ellPkgK_toStrongPersist`);
* `HkMem α 6 (FK w)` is `Npair6BWork.fk_hkMem`;
* the `ℋ⁶ × ℋ⁶` product rule is the unconditional level-six product rule of
  `StrongPersist.N6.prod_field_of6` (its two analytic inputs `prod_majorant6`, `exc_bound6`
  are proved for every `α ∈ (0,1]`, so no smallness threshold is needed).

All the analytic work (the pricing of the elliptic/star coefficients, the `FK`-slots, the
`𝒲^{6,∞}`-product rules) is inside `NS6.pieces`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/

namespace Work.FTS.StrongEps.E4R3.Nblock6

open Work.FTS.Galerkin (Fn)
open Work.FTS.StrongPersist.H6Rows.Npair6SupAux

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The permutation of the twenty pieces that matches the product forms `ClassCRHS.NBlk`
(ordered `N1gg, N1gs, …, N5ss`) with the level-six row pieces `H6Row6.pcs` (ordered
`nsP0, …, nsP19`): within each block of four the two factors are swapped
(`k ↦ 3−k` for `k mod 4 ∈ {0,1}`, `k ↦ 5−k` for `k mod 4 ∈ {2,3}`). -/
def NBlkPerm : ℕ → ℕ
  | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0
  | 4 => 7 | 5 => 6 | 6 => 5 | 7 => 4
  | 8 => 11 | 9 => 10 | 10 => 9 | 11 => 8
  | 12 => 15 | 13 => 14 | 14 => 13 | 15 => 12
  | 16 => 19 | 17 => 18 | 18 => 17 | _ => 16

/-- **The `NBlk` pieces are the level-six row pieces, up to the permutation `NBlkPerm`.**

On the open quadrant the two product forms agree: the only differences are the order of the
two factors, the association of the scalar, and the `(z+1)/z` / `z/(1+z)` shifts of the star
pieces (an identity on `z ≠ 0`), plus `FK F_* = α·2z/(1+z)² = 2α·hKer` for the `(F_*,K)`-slot. -/
theorem NBlk_eq_pcs_piece {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (w Φs Φg : Fn)
    (k : ℕ) (hk : k < 20) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k z θ
        = Work.FTS.StrongPersist.H6Row6.pcs α w Φg Φs (NBlkPerm k) z θ := by
  intro z θ hzθ
  have hz : z ≠ 0 := ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hzθ).1
  have h1z : (1 : ℝ) + z ≠ 0 := by
    have h2 := (Work.FTS.EllipticEst.mem_Q0.mp hzθ).1
    positivity
  interval_cases k <;>
    · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.StrongPersist.H6Row6.pcs, NBlkPerm,
        nsP0, nsP1, nsP2, nsP3, nsP4, nsP5, nsP6, nsP7, nsP8, nsP9, nsP10, nsP11,
        nsP12, nsP13, nsP14, nsP15, nsP16, nsP17, nsP18, nsP19,
        coefR1, coefR2, coefU1, coefU2, coefV1, coefV2, coefKs, coefKf,
        slotFs, slotTs, slotZs, slotTf, slotZf, angSin2,
        Work.FTS.Nonlin.PhiTg, Work.FTS.Nonlin.PhiTs, Work.FTS.VocabO2.PhiTs,
        Work.Spaces.hKer, Work.FTS.Nonlin.FK_Fstar hα hα1]
      try field_simp
      try ring

theorem NBlk_hkMem6 : ∀ C₀ Ce Cs : ℝ, ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ (Φs w Φg : ℝ → ℝ → ℝ),
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → w z θ = 0) →
    Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
    Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
    ∀ k ∈ Finset.range 20, Work.Spaces.HkMem α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k) := by
  intro C₀ Ce Cs α hαI Φs w Φg hw hXw hzero hgo hK hstar k hk
  obtain ⟨hα0, hα1⟩ := Set.mem_Ioc.mp hαI
  have hklt : k < 20 := Finset.mem_range.mp hk
  -- ## the level-six slice data
  have hmem6w : Work.Spaces.HkMem α 6 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 6 (by norm_num) hw.mem
  have hkfm : Work.Spaces.HkMem α 6 (fun z (_ : ℝ) => Work.Construction.FK w z) :=
    Work.FTS.StrongPersist.H6Rows.Npair6BWork.fk_hkMem α ⟨hα0, hα1⟩ w hw.reg hmem6w
  have hadm : Work.FTS.StrongPersist.H6Adm α w :=
    Work.FTS.StrongEps.H6Adm_of_classC_of_eqzero hw hzero
  -- ## the unconditional level-six product rule
  have hmul : ∀ u v : Fn, Work.FTS.EllipticEst.SmoothOpen u →
      Work.Spaces.HkMem α 6 u → Work.FTS.EllipticEst.SmoothOpen v → Work.Spaces.HkMem α 6 v →
      Work.Spaces.HkMem α 6 (fun z θ => u z θ * v z θ) := by
    obtain ⟨C, hC, hCpr⟩ := Work.FTS.StrongPersist.N6.prod_field_of6
      Work.FTS.StrongPersist.N6.prod_majorant6 Work.FTS.StrongPersist.N6.exc_bound6
    intro u v hus hum hvs hvm
    exact (hCpr α hα0 hα1 u v ⟨hus, hum⟩ ⟨hvs, hvm⟩).1
  have D : Work.FTS.StrongPersist.H6Row6.NS6.Data α Ce Cs w Φg Φs :=
    ⟨hα0, hα1, hw.reg, hmem6w, hw.mem, hgo.smooth, hstar.smooth, hw.l12, hstar,
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.ellPkgK_toStrongPersist hK,
      hkfm, hadm, hmul⟩
  -- ## transfer the membership along the piece identity
  have hk20 : NBlkPerm k < 20 := by interval_cases k <;> decide
  exact Work.FTS.StrongPersist.H6Pair6Aux.HkMem_congr_Qd
    (fun z θ hzθ => (NBlk_eq_pcs_piece hα0 hα1 w Φs Φg k hklt z θ hzθ).symm)
    (Work.FTS.StrongPersist.H6Row6.NS6.pieces D (NBlkPerm k) hk20).2

end Work.FTS.StrongEps.E4R3.Nblock6
