/-
# `FTS/Open2/Compat` — the compatibility API of the `StarPkgo2` migration

The migration changes the *hypotheses* of the N4 output and of the N5 interfaces from `StarPkgo`
to the strictly stronger `StarPkgo2`.  Two directions of transfer are therefore available, and
this module records them so that a caller holding data from either side of the migration can feed
the other:

* `pairData2_of_pairData'` — the **old** pairing data `OpenPkg.PairData'` (produced by the
  delivered `OpenPkg.pairing_bound_open`) can feed the **new** N5 chain: `PairData2.bound` asks
  for more (`StarPkgo2`) than `PairData'.bound` (`StarPkgo`), so the old datum is *stronger* and
  transfers by composition with `StarPkgo2.toStarPkgo`;
* `aprioriFields2_of_aprioriFields'` — the same for the four a-priori fields, which carry no
  star-package field at all (the two structures have the same field list).

The opposite direction (`PairData2 → PairData'`) is not available and is not a defect of the
formalisation: `PairData2.bound` is a statement about *more* data, so it does not imply the
weaker-hypothesis statement `PairData'.bound`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Open2.Defs2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Open2

open Work.FTS.Nonlin
open Work.FTS.VocabO
open Work.FTS.Galerkin (Fn Fam slice galFun galField coeffOf IsSolOn IsGalFam ConvLocUnif)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The old pairing data feeds the new chain**: `OpenPkg.PairData' → Open2.PairData2`, by
composing the `bound` field with the inheritance `StarPkgo2 → StarPkgo`. -/
theorem pairData2_of_pairData' {IP : ℝ → Fn → Fn → ℝ} {CcN Ce Cs α₄ : ℝ}
    (h : Work.FTS.OpenPkg.PairData' IP CcN Ce Cs α₄) : PairData2 IP CcN Ce Cs α₄ :=
  ⟨h.hCcN, h.hα₄, fun α hα hα₄ g Φs Φg hgal hstar hell hX =>
    h.bound α hα hα₄ g Φs Φg hgal hstar.toStarPkgo hell hX⟩

/-- **The old a-priori fields feed the new chain**: `OpenPkg.AprioriFields' → Open2.AprioriFields2`
(the two have the same field list — no star-package field occurs in either). -/
theorem aprioriFields2_of_aprioriFields' {IP : ℝ → Fn → Fn → ℝ}
    {α C₀ clo cc CcN Ce Cs : ℝ} {φ : ℕ → Fn} {Φs : Fn} {EllSol : Fn → Fn} {g₀ : Fn}
    (h : Work.FTS.OpenPkg.AprioriFields' IP α C₀ clo cc CcN Ce Cs φ Φs EllSol g₀) :
    AprioriFields2 IP α C₀ clo cc CcN Ce Cs φ Φs EllSol g₀ :=
  ⟨h.hInit, h.hCoeffBound, h.hProfileBdd, h.hLimBound⟩

/-- **The old per-piece table feeds the new assembly**: `OpenPkg.RowInputs' → Open2.RowInputs2'`
for `α ≤ 1` and `0 ≤ C`.  The two tables have the same field list except that `RowInputs'` asks
for row 16 at the *stronger* rate `√α·X³`; for `α ≤ 1` this implies the rate `X³` of
`RowInputs2'`, so every field transfers. -/
theorem rowInputs2_of_rowInputs {IP : ℝ → Fn → Fn → ℝ} {α C : ℝ} {g Φs Φg : Fn}
    (hα1 : α ≤ 1) (hC0 : 0 ≤ C)
    (h : Work.FTS.OpenPkg.RowInputs' IP α C g Φs Φg) : RowInputs2' IP α C g Φs Φg := by
  have hsq : Real.sqrt α ≤ 1 := Real.sqrt_le_one.mpr hα1
  have hX0 : (0 : ℝ) ≤ Xn α g ^ 3 := pow_nonneg (Work.Spaces.HkNorm_nonneg α 4 g) 3
  refine
    { reg4 := h.reg4, r1 := h.r1, r2 := h.r2, r3 := h.r3, r4 := h.r4, r5 := h.r5, r6 := h.r6,
      r7 := h.r7, r8 := h.r8, r9 := h.r9, r10 := h.r10, r11 := h.r11, r12 := h.r12,
      r13 := h.r13, r14 := h.r14, r15 := h.r15,
      r16 := ⟨h.r16.1, le_trans h.r16.2 (by
        simpa using mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsq hX0) hC0)⟩,
      r17 := h.r17, r18 := h.r18, r19 := h.r19, r20 := h.r20, r21 := h.r21, r22 := h.r22,
      r23 := h.r23, r24 := h.r24, r25 := h.r25, r26 := h.r26, rak := h.rak, rl0 := h.rl0,
      rl1 := h.rl1, rl2 := h.rl2, hN0 := h.hN0, hN := h.hN, hNs := h.hNs, hkN0 := h.hkN0,
      hkN := h.hkN, hkDz := h.hkDz }

end Work.FTS.Open2
