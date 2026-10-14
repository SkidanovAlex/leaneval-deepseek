import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.MinImports
import Submission.Work.FTS.StrongEps.E4R3.RawE6Aux.Jeps_IP6_transfer_aux
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Nblock6.Route =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Nblock6.Route` — the route, for the four `N_b6_*` pieces of the `N`-block

This module has no declarations: it exists so that the delegated lemmas
`Nblock6.N_b6_gg`, `N_b6_star`, `N_b6_rad`, `N_b6_five` (files
`Submission/Work/FTS/StrongEps/E4R3/Nblock6/*.lean`) can import it and see the route.

**Full route notes:** `Submission/Work/FTS/StrongEps/E4R3/NOTES_N_b6_route.md` (read it first;
it is a sibling of the target file `E4R3/sixthChapterBF_leaf.lean`).  Also relevant:
`Submission/Work/FTS/StrongEps/E4R3/Apriori4Proofs/blocks/N_aux/NOTES_N_BData.md` and
`.../N_aux/Aux/NOTES_analysis_b6.md` (the older, α-free analysis — its blocked cases `(M1)/(M2)`
are *not* blocked for the per-α constants asked for here).

## What the four lemmas are for

They are the level-`6` semi-tame bounds of the four groups of the twenty pieces
`ClassCRHS.NBlk α w Φs Φg k` of `N α (Ftot α w) (Φs + Φg)`.  Their consumer is the per-`α`
assembly of `S2` (the semi-tame estimate `EpsWPSemitame.epsWP_semitame`), which is in turn the
single hypothesis of the proved L-A inequality `E4R4.rawE6_ineq_flow`, which with
`E4R5.rawE6_deriv_of_flow` + `E4R4.gronwall_absorb` yields the level-six chapter
`Work.FTS.StrongEps.E4R3.sixthChapterBF_leaf`.

**`∃ K` is deliberately placed after `∀ α ∈ Ioc 0 1`** (so `K` may depend on `α`): the
`ε`-uniform Grönwall of the chapter only needs the constant to be independent of `w, Φs, Φg,
ε`, and the paper's `(γ-1)^{-1} = 10/α` losses (Lemma `infinity_separated`) are then affordable.
Do **not** try to make `K` α-free (that is the blocked `N_aux.N_b6`, see §5 of the route notes);
do **not** touch any file other than your own.

## Sketch (details in the notes)

* decompose `N = Σ_{k<20} NBlk k` on the open quadrant (`ClassCRHS.HkMemXnNIdent` /
  `ClassCRHS.nb_data`); sum bounded by `20 ·` max (`HkSq`-subadditivity, `GalFields.RHS.HkSum`);
* for a piece `A·P` expand `D^σ(A·P) = Σ_{a+b=σ} C (D^aA)(D^bP)`, `|σ| ≤ 6`, and bound each term
  **jointly** w.r.t. the weight of the product slot:
  - `a = 0`: the coefficient is sup-priced on the `α²`-small `ℋ⁴`-data (Agmon at level 4,
    `H6Pair6Aux.RowNAgmon`; `TransportS.sup_dz_le_hk`; `TransportS.T2SupB2.mixed_pointwise_le_Xn`)
    and the second factor's slot (of order `≤ 7`) is energy-priced;
  - `a ≥ 1`: one side is sup-priced (order `≤ 2` of the atoms: α-uniform for the mixed slots,
    `α^{-1/2}` for the pure ones) and the other is energy-priced at `HkSq α 6`; when the two
    weights do not match (all `θ`-derivatives on one side, the other side's slot pure), use the
    paper's device — the `θ`-device (sharp integral form: `H6Pair6Aux.sinWeight_hardy`; needs the
    slot to vanish at `θ = 0`, automatic for every *mixed* slot since `D_θ` carries `sin 2θ`) and
    the `z`-device (`TransportS.SupDzAux.half_line_window_bound`, `RXA1w.AgmonZ.agmonZ_weight`
    or a fresh `sup_z |u|² ≤ C∫_z (D_z u)² 𝑤²`) — splitting
    `∫_θ∫_z X² Y² ρ² ≤ (∫_θ sup_z Y² s^{-γ})(∫_z sup_θ X² 𝑤²)` and taking the `(γ-1)^{-1}` loss,
    which the per-`α` constant absorbs;
* `rad` / `five`: the coefficients `FK w`, `FK F_*`, `α·hKer`, `F_*` are **radial**; move the
  bounded angular factor (`sin²θ`, or nothing) onto the second factor and use
  `N0Aux.Maj6Split.radialMaj6_split` (or `RawE6Aux/radialTame6.lean`), with
  `Blo := C α^{-1/2}`·`ℋ⁴`-price and `Bhi := C α^{-1/2}`·`ℋ⁶`-price of the radial factor;
* `star`: use the `𝒲^{6,∞}` product rule (`H6Rows.wprod6`,
  `H6Rows.Npair6SupAux.hknorm_mul_of_WlInf6_cd6`) — `α^{-1/2}·WlInf α 6` is `≤ Cs α` on the star
  atoms (`StarPkg6`) and `≤ C α` on the fixed ones, hence `α`-small.

## Already proved and reusable (do not redo)

`smoothOpen_blkN`, `hkMem_blkN` (`N_aux/SmHm.lean`); the weak↔strong vanishing reductions
(`N_aux/ztrunc_*.lean`, `N_aux/ZTrunc.lean`, `N_aux/SmHm.lean`); the whole level-4 estimate
`N_b4` (`N_aux/N_b4*.lean`); the fixed-atom prices (`Nonlinear.FstarPkg`,
`H5.fixed_atoms5`, `ClassCRHS/StarAtoms*.lean`).
-/

namespace Work.FTS.StrongEps.E4R3.Nblock6

end Work.FTS.StrongEps.E4R3.Nblock6
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Nblock6.Stmts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Nblock6.Stmts` — the four group statements of the `N`-block and the membership statement

The hypothesis types of the delegated level-six lemmas `Nblock6.N_b6_gg`, `N_b6_star`,
`N_b6_rad`, `N_b6_five` and of the per-piece membership `Nblock6.NBlk_hkMem6`.  They are
`abbrev`s whose bodies are the statements verbatim, so the delegated lemmas are accepted
definitionally.  See `Submission/Work/FTS/StrongEps/E4R3/NOTES_N_b6_route.md` and
`Nblock6.Route` for the route.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Nblock6

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The level-six bound statement of the `gg`-group (`NBlk 0, 4, 8`). -/
abbrev GGStmt : Prop :=
  ∀ C₀ Ce Cs : ℝ, ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∃ K : ℝ, 0 < K ∧
    ∀ (Φs w Φg : ℝ → ℝ → ℝ),
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → w z θ = 0) →
    Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
    Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
    (Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 0)
        ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2) ∧
    (Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 4)
        ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2) ∧
    (Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 8)
        ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2)

/-- The level-six bound statement of the star group (`NBlk 1,2,3,5,6,7,9,10,11`). -/
abbrev StarStmt : Prop :=
  ∀ C₀ Ce Cs : ℝ, ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∃ K : ℝ, 0 < K ∧
    ∀ (Φs w Φg : ℝ → ℝ → ℝ),
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → w z θ = 0) →
    Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
    Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
    (∀ k ∈ ({1, 2, 3, 5, 6, 7, 9, 10, 11} : Finset ℕ),
      Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)
        ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2)

/-- The level-six bound statement of the radial group (`NBlk 12,13,14,15`). -/
abbrev RadStmt : Prop :=
  ∀ C₀ Ce Cs : ℝ, ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∃ K : ℝ, 0 < K ∧
    ∀ (Φs w Φg : ℝ → ℝ → ℝ),
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → w z θ = 0) →
    Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
    Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
    (∀ k ∈ ({12, 13, 14, 15} : Finset ℕ),
      Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)
        ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2)

/-- The level-six bound statement of the `N₅` group (`NBlk 16,17,18,19`). -/
abbrev FiveStmt : Prop :=
  ∀ C₀ Ce Cs : ℝ, ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∃ K : ℝ, 0 < K ∧
    ∀ (Φs w Φg : ℝ → ℝ → ℝ),
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → w z θ = 0) →
    Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
    Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
    (∀ k ∈ ({16, 17, 18, 19} : Finset ℕ),
      Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)
        ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2)

/-- The level-six membership of each of the twenty pieces. -/
abbrev MemStmt : Prop :=
  ∀ C₀ Ce Cs : ℝ, ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ (Φs w Φg : ℝ → ℝ → ℝ),
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → w z θ = 0) →
    Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
    Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
    ∀ k ∈ Finset.range 20,
      Work.Spaces.HkMem α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)


/-- The level-six bound of the single piece `NBlk 0`. -/
abbrev P0Stmt : Prop :=
  ∀ C₀ Ce Cs : ℝ, ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∃ K : ℝ, 0 < K ∧
    ∀ (Φs w Φg : ℝ → ℝ → ℝ),
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → w z θ = 0) →
    Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
    Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
    Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 0)
      ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2

/-- The level-six bound of the two pieces `NBlk 4` and `NBlk 8` (the `Uop`/`Vop` pieces, whose
second factor is a *slot* of `w` of order one above the norm). -/
abbrev P48Stmt : Prop :=
  ∀ C₀ Ce Cs : ℝ, ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∃ K : ℝ, 0 < K ∧
    ∀ (Φs w Φg : ℝ → ℝ → ℝ),
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → w z θ = 0) →
    Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
    Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
    (Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 4)
        ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2) ∧
    (Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 8)
        ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2)

end Work.FTS.StrongEps.E4R3.Nblock6
end
end
