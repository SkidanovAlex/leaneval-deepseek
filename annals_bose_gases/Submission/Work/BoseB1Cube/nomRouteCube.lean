import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.countWindowOfNominal
import Submission.Work.BoseB1Cube.slidingGoodCube
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.nomRouteCube` — the **loop-free FS route** to
# `Work.BoseB1Cube.CubeCrudeBand`, at FS's own nominal spelling

Holder of `Submission/Work/BoseB1Cube/cubeCrudeBand_holds.lean`.  **Read
`FINDING_cubeCrudeBand_session5.md` §9/§9bis/§11 and `FINDING_nomRouteCube.md` first.**

## What this module is

`FINDING_cubeCrudeBand_session5.md` §9 records a **loop** in the chapter's ledger:

    CubePerBox (smooth spelling) ⟸ dense arm ⟸ alive row ⟸ hcount ⟸ CountWindow
      ⟸ AprioriUnif ⟸ CubePerBox (smooth spelling),

which is why the frozen residual `Work.BoseB1Cube.CubeBandArmDensePos` (the `sorry` of
`cubePerBox_holds.lean`) has been stuck while all of its pieces are proved.  §9bis/§11 record the
repair: FS's own proof (`final_v2.tex` l.4070–4200) runs on `thm:smallbox` in the **nominal
(=`n/|B|`) spelling** — no count window, no `hcount`, no `(R1)/(R2)` — and their `eq:appsliding`
integration domain is `goodSet` **only** (the outer band `cube ∖ goodSet` never enters).

This module assembles that route with the pieces already on disk:

* `Work.BoseB1Cube.slidingGoodCube` — FS `eq:appsliding` at the cube cutoff (**PROVED**);
* `Work.BoseB1Cube.countWindowOfNominal` — FS l.4050–4200 (the convexity `U`-argument and the
  arithmetic) (**PROVED**);
* `Work.BoseB1Cube.PerBoxFNom` — FS `thm:smallbox` in the nominal spelling (`NominalPerBox.lean`).

and it *names* the single remaining analytic input:

* **`PerBoxFNomSlots`** — FS `thm:smallbox` (`final_v2.tex:3907`) at the sliding box `B(u)`,
  nominal spelling, at the two chemical-potential slots `μp = μ` and `μp = 4μ` that FS use
  (`eq:appsliding` + `eq:badset`).  This is delegated as
  `Submission.Work.BoseB1Cube.nominalPerBoxRow`.

The two theorems of record below are

* `countWindow_of_perBoxFNomSlots : SlidingGoodCube ∧ PerBoxFNomSlots ⟹ CountWindow`;
* **`cubeCrudeBand_of_perBoxFNomSlots : PerBoxFNomSlots ⟹ CubeCrudeBand v h`** — the assigned node
  of this file, from FS's theorem alone (no `cubePerBox_holds`, no band, no loop);

and the *slot-doubling* arithmetic that shows the two slots are **one** statement up to a two-line
`ψ`-comparison:

* `psiWeight_four_le` — `ψ(1,4μ,t) ≤ 4ψ(1,μ,t) + 12μ²` exactly (the difference clears to `3t² ≥ 0`);
* `perBoxFNom_slots_of_row` — the row at the slot `μ` for `c₁ ≤ 5/2` gives **both** rows at the
  common constants `(min (c₁/4) (5/2), max C 1)`, modulo the *integral* form of the `ψ`-comparison
  (`PsiWeightFourIntegral`, delegated as `Submission.Work.BoseB1Cube.psiWeight_integral_four_le`).

## Why the `μp = 4μ` slot matters (and why it is *free*)

`nomLedger.lean`'s `ledgerNom` — and hence `countWindowOfNominal` — only ever *uses* the slot
`μp = μ` (the `hperAll … μ (Or.inl rfl)` calls in its proof); the `μp = 4μ` disjunct is carried in
the statement because it is FS's `m(u)μ` slot bookkeeping (`eq:appsliding`).  The doubling above
shows the disjunct costs nothing: the `F`-weight at `4μ` is at most `4×` that at `μ` plus `12μ²`,
so the *same* row at a quarter of `c₁` serves both slots.  This is FS's `eq:badset` step in the
only form in which it is needed here.

## The import-cycle obstruction (recorded for the lead)

`NominalPerBox.lean`, `countWindowOfNominal.lean` and `slidingGoodCube.lean` all import
`cubeCrudeBand_holds.lean` (they need `Work.BoseB1Cube.CountWindow`), so the route assembled here
**cannot** be imported into `cubeCrudeBand_holds.lean` itself.  Re-pointing the assigned file at
this route therefore needs the one-line refactor recorded in `FINDING_nomRouteCube.md` §4 (move
`def CountWindow` to a lower module) — until then the assigned file keeps its `cubePerBox_holds`
body, and the route below is the *second, loop-free* proof of the same statement.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The `ψ`-comparison at the doubled slot -/

/-- `Work.SmallBoxSliding.psiWeight` is nonnegative on the physical range. -/
theorem psiWeight_nonneg' {μ t : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) :
    0 ≤ Work.SmallBoxSliding.psiWeight 1 μ t := by
  have h1 : (0 : ℝ) < 1 + t * μ⁻¹ := by positivity
  rw [Work.SmallBoxSliding.psiWeight]
  exact div_nonneg (mul_nonneg zero_le_one (sq_nonneg _)) h1.le

/-- `Work.SmallBoxSliding.psiWeight 1 μ t = μ (t − μ)²/(t + μ)` on the physical range. -/
theorem psiWeight_canonical {μ t : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) :
    Work.SmallBoxSliding.psiWeight 1 μ t = μ * (t - μ) ^ 2 / (t + μ) := by
  have hden : (0 : ℝ) < 1 + t * μ⁻¹ := by positivity
  have hB : t + μ ≠ 0 := by positivity
  unfold Work.SmallBoxSliding.psiWeight
  rw [one_mul, div_eq_div_iff (ne_of_gt hden) hB]
  field_simp
  ring

/-- **FS's `eq:badset` arithmetic at the doubled chemical-potential slot**: for `t ≥ 0`, `μ > 0`,

    `ψ(1, 4μ, t) ≤ 4 ψ(1, μ, t) + 12 μ² ,      ψ(c,μ,t) = c (t−μ)²/(1 + t/μ) .

Equivalently `ψ(1,μ,t) − ¼ψ(1,4μ,t) ≥ −3μ²`; after clearing the positive denominators
`(t+μ)(t+4μ)` the difference is exactly `3t² ≥ 0`. -/
theorem psiWeight_four_le {μ t : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) :
    Work.SmallBoxSliding.psiWeight 1 (4 * μ) t
      ≤ 4 * Work.SmallBoxSliding.psiWeight 1 μ t + 12 * μ ^ 2 := by
  have hμ4 : (0 : ℝ) < 4 * μ := by linarith
  have hA : (0 : ℝ) < t + 4 * μ := by linarith
  have hB : (0 : ℝ) < t + μ := by linarith
  have hA' : t + 4 * μ ≠ 0 := ne_of_gt hA
  have hB' : t + μ ≠ 0 := ne_of_gt hB
  rw [psiWeight_canonical hμ4 ht, psiWeight_canonical hμ ht]
  have hkey : 16 * μ / (t + 4 * μ) ≤ 3 + μ / (t + μ) := by
    have h1 : (3 : ℝ) + μ / (t + μ) = (3 * t + 4 * μ) / (t + μ) := by
      field_simp
      ring
    rw [h1]
    have h2 : (3 * t + 4 * μ) / (t + μ) - 16 * μ / (t + 4 * μ)
        = 3 * t ^ 2 / ((t + 4 * μ) * (t + μ)) := by
      field_simp
      ring
    have h3 : 0 ≤ (3 * t + 4 * μ) / (t + μ) - 16 * μ / (t + 4 * μ) := by
      rw [h2]
      exact div_nonneg (by positivity) (le_of_lt (mul_pos hA hB))
    linarith [h3]
  have e1 : (4 * μ) * (t - 4 * μ) ^ 2 / (t + 4 * μ)
      = 4 * μ * t - 48 * μ ^ 2 + 256 * μ ^ 3 / (t + 4 * μ) := by
    field_simp
    ring
  have e2 : 4 * (μ * (t - μ) ^ 2 / (t + μ)) + 12 * μ ^ 2
      = 4 * μ * t + 16 * μ ^ 3 / (t + μ) := by
    field_simp
    ring
  rw [e1, e2]
  have h3 : 256 * μ ^ 3 / (t + 4 * μ) - 16 * μ ^ 3 / (t + μ)
      = 16 * μ ^ 2 * (16 * μ / (t + 4 * μ) - μ / (t + μ)) := by
    field_simp
    ring
  have h4 : 16 * μ ^ 2 * (16 * μ / (t + 4 * μ) - μ / (t + μ)) ≤ 16 * μ ^ 2 * 3 :=
    mul_le_mul_of_nonneg_left (by linarith [hkey]) (by positivity)
  linarith [h3, h4]

/-! ## 2. The named inputs -/

/-- **FS `thm:smallbox` at the sliding box `B(u)`, nominal (indicator-count) spelling, at the two
chemical-potential slots `μp = μ` and `μp = 4μ`** — FS's `eq:appsliding` (`m(u) = 1`) plus
`eq:badset` (the layer `m(u) = 4`) uses of `thm:smallbox`, with one pair of constants for all `μ`,
`n`, states and `u ∈ goodSet`.  By §1 the `4μ` half is *implied* by the `μ` half at a quarter of
`c₁` (`perBoxFNom_slots_of_row`), so this is FS's theorem verbatim up to two lines of `ψ`-arithmetic.

This is the single analytic residual of the FS route to `CubeCrudeBand`; delegated as
`Submission.Work.BoseB1Cube.nominalPerBoxRow`. -/
def PerBoxFNomSlots (v : E3 → ℝ) (h : ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ →
        ∀ μp : ℝ, (μp = μ ∨ μp = 4 * μ) →
          PerBoxFNom v h R c₁ C μp μ n Φ u

/-- **The single-slot (slot `μ`) form of the same row** — FS's `thm:smallbox` read only on the
`m(u) = 1` set `I₋`.  Strictly weaker than `PerBoxFNomSlots`; the two are equivalent modulo
`PsiWeightFourIntegral` by `perBoxFNomSlots_of_slotMu`. -/
def PerBoxFNomMu (v : E3 → ℝ) (h : ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ →
        PerBoxFNom v h R c₁ C μ μ n Φ u

/-- **The integral form of the doubled-slot `ψ`-comparison** — the one (elementary) analytic input
the slot-doubling needs.  Delegated as `Submission.Work.BoseB1Cube.psiWeight_integral_four_le`;
`psiWeight_four_le` is its pointwise core. -/
def PsiWeightFourIntegral : Prop :=
  ∀ (ℓ d μ : ℝ) (u : E3) (n : ℕ) (Φ : X n → ℝ),
    0 < ℓ → 0 < d → 0 < μ → 0 < Work.SmallBoxSliding.boxMass ℓ d u → Continuous Φ →
      (∫ x in abox n ℓ, (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 (4 * μ)
          (boxIndCount ℓ d u x / Work.SmallBoxSliding.boxMass ℓ d u))
        ≤ 4 * (∫ x in abox n ℓ, (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ
              (boxIndCount ℓ d u x / Work.SmallBoxSliding.boxMass ℓ d u))
          + 12 * μ ^ 2 * (∫ x in abox n ℓ, (Φ x) ^ 2)

/-! ## 3. The count window and the assigned node from the nominal per-box row -/

/-- **FS `thm:aprioriHLambda` at the nominal spelling, from FS's own two ingredients.**
The localisation `SlidingGoodCube` (FS `eq:appsliding`) plus the per-box row `PerBoxFNomSlots` give
the a-priori count window (`Work.BoseB1Cube.CountWindow`) — FS l.4050–4200, whose convexity and
arithmetic bodies are the PROVED `nomLedger`/`nomCountAbsorb`/`nomCountArith`. -/
theorem countWindow_of_perBoxFNomSlots {v : E3 → ℝ} (h : ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < a v)
    (hS : SlidingGoodCube v h) (hN : PerBoxFNomSlots v h R) : CountWindow v h :=
  countWindowOfNominal h hv hv1 hvrad hR hv_supp hav hS hN

/-- **THE NODE OF THIS MODULE: `CubeCrudeBand` from FS's nominal per-box row.**

`SlidingGoodCube` is PROVED (`Work.BoseB1Cube.slidingGoodCube`), so this theorem turns the assigned
statement `Work.BoseB1Cube.CubeCrudeBand v h` into the *single* analytic input `PerBoxFNomSlots`
(FS `thm:smallbox` at the nominal spelling) — with **no** reference to `CubePerBox`, to the dense
arm, to `hcount` or to the outer band, i.e. with no loop. -/
theorem cubeCrudeBand_of_perBoxFNomSlots {v : E3 → ℝ} (h : ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < a v)
    (hN : PerBoxFNomSlots v h R) : CubeCrudeBand v h :=
  cubeCrudeBand_of_countWindow hv hv1 hvrad hR hv_supp hav
    (countWindow_of_perBoxFNomSlots h hv hv1 hvrad hR hv_supp hav
      (slidingGoodCube h hv hv1 hvrad hR hv_supp hav) hN)

/-! ## 4. The slot doubling: the `4μ` row follows from the `μ` row -/

/-- **The slot doubling.**  From the nominal per-box row at the slot `μ` with `c₁ ≤ 5/2`, the
*same* state satisfies the row at **both** slots `μ` and `4μ` at the common constants
`(min (c₁/4) (5/2), max C 1)`.

Quantitatively: the `4μ`-row's `F`-term is `(c₁/4)·W·A₄` with `A₄ ≤ 4A + 12μ²N`
(`PsiWeightFourIntegral` + `psiWeight_four_le`), the `−½(4μ)²W N` term is `4×` more negative than
the hypothesis' `−½μ²WN`, and the error bracket grows from `C` to `max C 1`, so the hypothesis'
left-hand side dominates the goal's. -/
theorem perBoxFNom_slots_of_row {v : E3 → ℝ} {h : ScatSol v} {R c₁ C μ : ℝ} {n : ℕ}
    (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) {u : E3}
    (hint : PsiWeightFourIntegral) (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hℓ : 0 < sideAt μ (a v)) (hd : 0 < (paramsAt μ (a v)).d)
    (hV : 0 < Work.SmallBoxSliding.boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u)
    (hμ : 0 < μ) (hav : 0 ≤ a v) (hc₁ : 0 ≤ c₁) (hc₁2 : c₁ ≤ 5 / 2) (hC : 0 ≤ C)
    (hrow : PerBoxFNom v h R c₁ C μ μ n Φ u) :
    PerBoxFNom v h R (min (c₁ / 4) (5 / 2)) (max C 1) μ μ n Φ u ∧
    PerBoxFNom v h R (min (c₁ / 4) (5 / 2)) (max C 1) (4 * μ) μ n Φ u := by
  unfold PerBoxFNom at hrow ⊢
  unfold Work.BoseBoxFix.normB Work.BoseKinLoc.sqNormB at hrow ⊢
  set W : ℝ := Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
    (paramsAt μ (a v)).d u with hWdef
  set χ : ℝ := Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
    (paramsAt μ (a v)).d u with hχdef
  set N : ℝ := ∫ x in abox n (sideAt μ (a v)), ((Φ : X n → ℝ) x) ^ 2 with hNdef
  set A : ℝ := ∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2 *
    Work.SmallBoxSliding.psiWeight 1 μ
      (boxIndCount (sideAt μ (a v)) (paramsAt μ (a v)).d u x
        / Work.SmallBoxSliding.boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u) with hAdef
  set A4 : ℝ := ∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2 *
    Work.SmallBoxSliding.psiWeight 1 (4 * μ)
      (boxIndCount (sideAt μ (a v)) (paramsAt μ (a v)).d u x
        / Work.SmallBoxSliding.boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u) with hA4def
  set Γ : ℝ := (R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
    + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) with hΓdef
  have hW0 : 0 ≤ W := by
    rw [hWdef]
    exact w1MassB_nonneg h hv hvrad hR hv_supp hℓ hd u
  have hN0 : 0 ≤ N := by
    rw [hNdef]
    exact integral_nonneg fun x => sq_nonneg _
  have hχ0 : 0 ≤ χ := by
    rw [hχdef]
    exact Work.SmallBoxSliding.chiMass_nonneg _ _ _ u
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    refine integral_nonneg fun x => mul_nonneg (sq_nonneg _) ?_
    exact psiWeight_nonneg' hμ (div_nonneg (boxIndCount_nonneg _ _ _ _) hV.le)
  have hA40 : 0 ≤ A4 := by
    rw [hA4def]
    refine integral_nonneg fun x => mul_nonneg (sq_nonneg _) ?_
    exact psiWeight_nonneg' (by linarith) (div_nonneg (boxIndCount_nonneg _ _ _ _) hV.le)
  have hΓ0 : 0 ≤ Γ := by
    rw [hΓdef]
    refine add_nonneg (sq_nonneg _) ?_
    refine mul_nonneg (pow_nonneg ?_ 3) (Real.rpow_nonneg (by positivity) _)
    rw [Work.BoseFixB1.KB_eq_fsXp μ (a v)]
    exact Work.BoseBox.fsXp_nonneg (t := μ * (a v) ^ 3) (c := -6) (mul_nonneg hμ.le (pow_nonneg hav 3))
  have hkey : A4 ≤ 4 * A + 12 * μ ^ 2 * N := by
    rw [hA4def, hAdef, hNdef]
    exact hint (sideAt μ (a v)) (paramsAt μ (a v)).d μ u n (Φ : X n → ℝ)
      hℓ hd hμ hV (Φ.contDiff.continuous)
  have h4 : min (c₁ / 4) (5 / 2) ≤ c₁ / 4 := min_le_left _ _
  have h4nn : 0 ≤ min (c₁ / 4) (5 / 2) := le_min (by linarith) (by norm_num)
  have hC4C : C ≤ max C 1 := le_max_left C 1
  have hC41 : (1 : ℝ) ≤ max C 1 := le_max_right C 1
  have hC40 : 0 ≤ max C 1 := le_trans hC hC4C
  have hWA : 0 ≤ W * A := mul_nonneg hW0 hA0
  have hWA4 : 0 ≤ W * A4 := mul_nonneg hW0 hA40
  have hH1 : 0 ≤ μ ^ 2 * (a v) * Γ * χ * N :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) hav) hΓ0) hχ0) hN0
  have hH2 : 0 ≤ μ * (a v) * N := mul_nonneg (mul_nonneg hμ.le hav) hN0
  have maxid : max (max C 1) 1 = max C 1 := max_eq_left (le_max_right C 1)
  constructor
  · -- the `μ` row at `(min (c₁/4) (5/2), max C 1)`: only the `min` and the `max` move
    have h1 : min (c₁ / 4) (5 / 2) * (W * A) ≤ c₁ * (W * A) :=
      mul_le_mul_of_nonneg_right (by linarith [h4, hc₁]) hWA
    have h2 : C * (μ ^ 2 * (a v) * Γ * χ * N + μ * (a v) * N)
        ≤ max C 1 * (μ ^ 2 * (a v) * Γ * χ * N + μ * (a v) * N) :=
      mul_le_mul_of_nonneg_right hC4C (add_nonneg hH1 hH2)
    linarith [hrow, h1, h2]
  · -- the `4μ` row at the same constants
    have hstep : min (c₁ / 4) (5 / 2) * (W * A4)
        ≤ c₁ * (W * A) + 3 * c₁ * (μ ^ 2 * (W * N)) := by
      have h1 : min (c₁ / 4) (5 / 2) * (W * A4) ≤ (c₁ / 4) * (W * A4) :=
        mul_le_mul_of_nonneg_right h4 hWA4
      have h2 : (c₁ / 4) * (W * A4) ≤ (c₁ / 4) * (W * (4 * A + 12 * μ ^ 2 * N)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hkey hW0) (by linarith)
      have h3 : (c₁ / 4) * (W * (4 * A + 12 * μ ^ 2 * N))
          = c₁ * (W * A) + 3 * c₁ * (μ ^ 2 * (W * N)) := by ring
      linarith [h1, h2, h3.le, h3.ge]
    have h3 : 3 * c₁ * (μ ^ 2 * (W * N)) - 8 * (μ ^ 2 * (W * N)) ≤ -(1 / 2) * (μ ^ 2 * (W * N)) := by
      have hWN : 0 ≤ μ ^ 2 * (W * N) := mul_nonneg (sq_nonneg μ) (mul_nonneg hW0 hN0)
      nlinarith [hWN, hc₁2]
    have h4' : C * (μ ^ 2 * (a v) * Γ * χ * N + μ * (a v) * N)
        ≤ max C 1 * (16 * (μ ^ 2 * (a v) * Γ * χ * N) + 4 * (μ * (a v) * N)) := by
      have b1 : C * (μ ^ 2 * (a v) * Γ * χ * N) ≤ max C 1 * (16 * (μ ^ 2 * (a v) * Γ * χ * N)) := by
        calc C * (μ ^ 2 * (a v) * Γ * χ * N)
            ≤ max C 1 * (μ ^ 2 * (a v) * Γ * χ * N) := mul_le_mul_of_nonneg_right hC4C hH1
          _ ≤ max C 1 * (16 * (μ ^ 2 * (a v) * Γ * χ * N)) :=
              mul_le_mul_of_nonneg_left (by linarith) hC40
      have b2 : C * (μ * (a v) * N) ≤ max C 1 * (4 * (μ * (a v) * N)) := by
        calc C * (μ * (a v) * N) ≤ max C 1 * (μ * (a v) * N) := mul_le_mul_of_nonneg_right hC4C hH2
          _ ≤ max C 1 * (4 * (μ * (a v) * N)) :=
              mul_le_mul_of_nonneg_left (by linarith) hC40
      have expand : C * (μ ^ 2 * (a v) * Γ * χ * N + μ * (a v) * N)
          = C * (μ ^ 2 * (a v) * Γ * χ * N) + C * (μ * (a v) * N) := by ring
      have expand2 : max C 1 * (16 * (μ ^ 2 * (a v) * Γ * χ * N) + 4 * (μ * (a v) * N))
          = max C 1 * (16 * (μ ^ 2 * (a v) * Γ * χ * N)) + max C 1 * (4 * (μ * (a v) * N)) := by
        ring
      rw [expand, expand2]
      linarith [b1, b2]
    have hp : min (c₁ / 4) (5 / 2) * (W * A4) - 1 / 2 * (4 * μ) ^ 2 * W * N
        - max C 1 * ((4 * μ) ^ 2 * (a v) * Γ * χ * N + (4 * μ) * (a v) * N)
        ≤ c₁ * (W * A) - 1 / 2 * μ ^ 2 * W * N
          - C * (μ ^ 2 * (a v) * Γ * χ * N + μ * (a v) * N) := by
      have e1 : ((4 : ℝ) ^ 2) * (μ ^ 2 * (W * N)) = 16 * (μ ^ 2 * (W * N)) := by ring
      have hX : (4 * μ) ^ 2 * (a v) * Γ * χ * N = 16 * (μ ^ 2 * (a v) * Γ * χ * N) := by ring
      have hY : (4 * μ) * (a v) * N = 4 * (μ * (a v) * N) := by ring
      have hZ : (1 / 2 : ℝ) * (4 * μ) ^ 2 * W * N = 8 * (μ ^ 2 * (W * N)) := by ring
      rw [hX, hY, hZ]
      linarith [hstep, h3, h4']
    linarith [hp, hrow]

/-- **`PerBoxFNomSlots` from `PerBoxFNomMu`** — the two slots are one statement
(`perBoxFNom_slots_of_row` applied to the row weakened to `c₁₀ = min c₁ (5/2)`, `C₀ = max C 1`). -/
theorem perBoxFNomSlots_of_slotMu {v : E3 → ℝ} (h : ScatSol v) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hint : PsiWeightFourIntegral) (hMu : PerBoxFNomMu v h R) : PerBoxFNomSlots v h R := by
  obtain ⟨ε₀, c₁, C, hε₀, hc₁, hC, hrow⟩ := hMu
  refine ⟨ε₀, min (min c₁ (5 / 2) / 4) (5 / 2), max C 1, hε₀, ?_, ?_, ?_⟩
  · exact lt_min (by positivity) (by norm_num)
  · exact le_trans hC (le_max_left C 1)
  · intro μ hAdm n Φ u hu μp hμp
    have hℓ : 0 < sideAt μ (a v) := Work.BoseFixB1.adm_ell_pos hAdm
    have hd : 0 < (paramsAt μ (a v)).d := Work.BoseFixB1.adm_d_pos hAdm
    have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
    have hV : 0 < Work.SmallBoxSliding.boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u :=
      Work.BoseFixB1.boxMass_pos_of_goodSet hℓ hd hμ hu
    have hc10 : 0 ≤ min c₁ (5 / 2) := le_min hc₁.le (by norm_num)
    have hc125 : min c₁ (5 / 2) ≤ 5 / 2 := min_le_right c₁ (5 / 2)
    have hmax : max (max C 1) 1 = max C 1 := max_eq_left (le_max_right C 1)
    -- the source row weakened to `(min c₁ (5/2), max C 1)`
    have hrow' : PerBoxFNom v h R (min c₁ (5 / 2)) (max C 1) μ μ n Φ u := by
      have hsrc := hrow μ hAdm n Φ u hu
      unfold PerBoxFNom at hsrc ⊢
      unfold Work.BoseBoxFix.normB Work.BoseKinLoc.sqNormB at hsrc ⊢
      set W : ℝ := Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u with hWdef
      set χ : ℝ := Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u with hχdef
      set N : ℝ := ∫ x in abox n (sideAt μ (a v)), ((Φ : X n → ℝ) x) ^ 2 with hNdef
      set A : ℝ := ∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2 *
        Work.SmallBoxSliding.psiWeight 1 μ
          (boxIndCount (sideAt μ (a v)) (paramsAt μ (a v)).d u x
            / Work.SmallBoxSliding.boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u) with hAdef
      set Γ : ℝ := (R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
        + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) with hΓdef
      have hW0 : 0 ≤ W := by
        rw [hWdef]
        exact w1MassB_nonneg h hv hvrad hR hv_supp hℓ hd u
      have hN0 : 0 ≤ N := by
        rw [hNdef]
        exact integral_nonneg fun x => sq_nonneg _
      have hA0 : 0 ≤ A := by
        rw [hAdef]
        refine integral_nonneg fun x => mul_nonneg (sq_nonneg _) ?_
        exact psiWeight_nonneg' hμ (div_nonneg (boxIndCount_nonneg _ _ _ _) hV.le)
      have hΓ0 : 0 ≤ Γ := by
        rw [hΓdef]
        refine add_nonneg (sq_nonneg _) ?_
        refine mul_nonneg (pow_nonneg ?_ 3)
          (Real.rpow_nonneg (mul_nonneg hμ.le
            (pow_nonneg (Work.BoseFixB1.adm_a_pos hAdm).le 3)) _)
        rw [Work.BoseFixB1.KB_eq_fsXp μ (a v)]
        exact Work.BoseBox.fsXp_nonneg (t := μ * (a v) ^ 3) (c := -6)
          (mul_nonneg hμ.le (pow_nonneg (Work.BoseFixB1.adm_a_pos hAdm).le 3))
      have hχ0 : 0 ≤ χ := by
        rw [hχdef]
        exact Work.SmallBoxSliding.chiMass_nonneg _ _ _ u
      have h1 : min c₁ (5 / 2) * (W * A) ≤ c₁ * (W * A) :=
        mul_le_mul_of_nonneg_right (min_le_left c₁ (5 / 2)) (mul_nonneg hW0 hA0)
      have hH1 : 0 ≤ μ ^ 2 * (a v) * Γ * χ * N :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ)
          (Work.BoseFixB1.adm_a_pos hAdm).le) hΓ0) hχ0) hN0
      have hH2 : 0 ≤ μ * (a v) * N :=
        mul_nonneg (mul_nonneg hμ.le (Work.BoseFixB1.adm_a_pos hAdm).le) hN0
      have h2 : C * (μ ^ 2 * (a v) * Γ * χ * N + μ * (a v) * N)
          ≤ max C 1 * (μ ^ 2 * (a v) * Γ * χ * N + μ * (a v) * N) :=
        mul_le_mul_of_nonneg_right (le_max_left C 1) (add_nonneg hH1 hH2)
      linarith [hsrc, h1, h2]
    have hpair := perBoxFNom_slots_of_row (Φ := Φ) (u := u) hint hv hvrad hR hv_supp hℓ hd hV hμ
      (Work.BoseFixB1.adm_a_pos hAdm).le hc10 hc125 (le_trans hC (le_max_left C 1)) hrow'
    rw [hmax] at hpair
    rcases hμp with h' | h'
    · subst h'
      exact hpair.1
    · subst h'
      exact hpair.2

/-- **The assigned node via the nominal route, from FS's `thm:smallbox` at the slot `μ` alone.** -/
theorem cubeCrudeBand_of_perBoxFNomMu {v : E3 → ℝ} (h : ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < a v)
    (hint : PsiWeightFourIntegral) (hMu : PerBoxFNomMu v h R) : CubeCrudeBand v h :=
  cubeCrudeBand_of_perBoxFNomSlots h hv hv1 hvrad hR hv_supp hav
    (perBoxFNomSlots_of_slotMu h hv hvrad hR hv_supp hint hMu)

/-- **The strong node implies the weak one** (its `μp = μ` instance) — with `perBoxFNomSlots_of_slotMu`
the two forms of FS's nominal per-box row are equivalent. -/
theorem perBoxFNomMu_of_slots {v : E3 → ℝ} (h : ScatSol v) {R : ℝ}
    (hS : PerBoxFNomSlots v h R) : PerBoxFNomMu v h R := by
  obtain ⟨ε₀, c₁, C, hε₀, hc₁, hC, hrow⟩ := hS
  exact ⟨ε₀, c₁, C, hε₀, hc₁, hC,
    fun μ hAdm n Φ u hu => hrow μ hAdm n Φ u hu μ (Or.inl rfl)⟩

end Work.BoseB1Cube
