import ChallengeDeps
import Submission.Work.AprioriCount.cubeDenseAliveRow
import Submission.Work.BoseB1Cube.inBoxRoute
import Submission.Work.BoseFixB1.MDelta.defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.cubeInBoxSplit` — the split of the in-box row (A4) into its
# **window** half and its **grouping** half

Read `Submission/Work/BoseB1Cube/FINDING_cubeDensePos_session10.md` §6 and
`sources/boseDCF/bose_deadrow_cubicfree.md` §A for the design.

**Why this file exists.**  After A2 is proved (`Work.BoseB1Cube.cubePerBox_of_inBoxCubeRow`), the
whole remaining content of `Work.BoseB1Cube.CubePerBox` is the single Prop
`Work.BoseB1Cube.InBoxCubeRow v h R` (A4): the row `PerBoxFCube` for **in-box, normalised**
`BoxState`s at *every* `n` and every density.  FS's own proof of that statement is a two-part
argument, and the split is by the *count*:

* **the window half** (`InBoxCubeRowWindow`, this file): `n ≤ Cn·μ·|B(u)|` for a prescribed `Cn ≥ 1`.
  This is FS's per-`n''`-group estimate; the route is the PROVED sliding rung
  `Work.BoseFixB1S.sbWordCube_ge_a0Main_add_boxA2` (the *payment*, in this chapter's own cone, see
  `LowCountWindowAllJCube.lean:412`) plus the PROVED payment `a0A2PaymentAdm_holds` plus the
  **windowed `MΔ`-payer Bogoliubov port** `Work.BoseB1Cube.WindowedMDeltaPortAll`
  (`windowedMDeltaPort.lean`), the credit `½(M₂/V²)Pc`-slot, the free gap coefficient
  (`Work.BoseFixB1S.gapAbsorbB1`) and the fibre/`F` rows.  ⚠ The port is the one input that is
  *not* on disk yet (delegated: `Work.BoseB1Cube.windowedMDeltaPortHolds`);
* **the grouping half** (`InBoxCubeRowLarge`, this file): `n > Cn·μ·|B(u)|`.  FS's
  `n = m·n' + n''` decomposition, i.e. the PROVED cube descent
  `Work.BoseB1Cube.sbWordCube_descent_atSizes` fed by the state-independent per-size bounds
  `Work.BoseB1Cube.CubeSmallNArb` (items 1–2) and the crude `F`-row
  (`Work.BoseFixB1B.flatFterm_le_mu_sq_add`).  The only non-disk input here is `CubeSmallNArb` itelf
  (the honest residual of the chapter's *per-size* form of `thm:smallbox`), which is why
  `InBoxCubeRowLarge` carries it as a **hypothesis**.

**The assembly** `inBoxCubeRow_of_window_large` below is PROVED: it is a pure case split on
`n ⋚ Cn·μ|B(u)|` in which the two halves' constants are merged by `min`/`max` through the PROVED
monotonicity `Work.BoseB1Cube.perBoxFCube_mono`.  The half-constants are merged so that *both*
halves are used at the *same* window constant `Cn` (taken from `InBoxCubeRowLarge`, which asks for
`Cn ≥ 2`): the window half is instantiated at that `Cn` (its `∀ Cn ≥ 1` quantifier) and the grouping
half at its own.

**Consequences.**  `InBoxCubeRowWindow ∧ InBoxCubeRowLarge ⟹ InBoxCubeRow ⟹ CubePerBox` (the last
step being the PROVED A2).  So the chapter rests on exactly two nodes:
`InBoxCubeRowWindow` (needs only the windowed port) and `CubeSmallNArb` (the per-size bounds).

**Cone note.**  This module is in the chapter's cone (`exclFunOpAux` side); it must NOT import
`Submission.Work.BoseFixB1B.sbWordCube_ge_meanFieldRow` or `…MDelta.meanFieldRowBox_of_mDeltaPort`
(their cones contain `Work.BoseFixB1S.boxQCount_eq_sum_compT`, whose `goodState_finset_sum` /
`boxPInd_const_mul` are duplicates of declarations in `exclFunOpAux` / `boxCountsScaleB1`), see
`NOTE_dupGoodState_repair_scope.md`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **(A4-window)** The in-box row in the **count window** `n ≤ Cn·μ|B(u)|`, for a *prescribed*
`Cn ≥ 1` (`∀ Cn, 1 ≤ Cn → ∃ ε₀ c₁ C …`): the weakenings that FS's per-`n''`-group estimate needs.
-/
def InBoxCubeRowWindow (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∀ Cn : ℝ, 1 ≤ Cn → ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
        (n : ℝ) ≤ Cn * μ * Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ
              (_root_.BoseGases.a v)) (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u →
        (∀ᵐ x ∂(MeasureTheory.volume.restrict
            (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
          (Φ : Submission.BoseGases.X n → ℝ) x ≠ 0 →
            ∀ i : Fin n, x i ∈ Submission.BoseGases.dlBox
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) →
        (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2) = 1 →
        Work.BoseFixB1S.PerBoxFCube v h R c₁ C μ n Φ u

/-- **(A3) The in-box variance row** — ⚠ **THIS PROP IS FALSE AS STATED; DO NOT USE IT.**
Keep for the record only: its delegated prover refuted it (`FINDING_inBoxVarRow_session2.md`,
`FINDING_odRowToInBox_FALSE.md`).  The exact identity behind it is
`κ²·bVar = odPairSum + odDiag`, and the two-mode family
`Φ = (f₀^{⊗n} + f₁^{⊗n})/√2` (`f₀` the box condensate, `f₁` a bump at the *deepest* point of a cap
of the box against the `‖z‖ = ℓ/2` face, available in `goodSet` with penetration depth
`h ≤ μ^{-1/3}`) makes `odPairSum ≍ n² sup_Aχ²/4` while the RHS only allows `Cv·Ξ·ω·n(N+ν)` with
`ω = κ/V`; the conclusion needs `∫_A χ² ≥ V·sup_A χ²/(2CvΞ)`, which fails for *every* fixed `Cv`
at boxes whose overlap with the plateau of `chiScale ℓ` is small (the corpus's `chiBase` is an
opaque `Classical.choice`, so the transition shell is unbounded below).  It was stated (in the
design `sources/boseDCF/bose_deadrow_cubicfree.md` §A, as `Work.C46Design.InBoxVarRow`) with the
false side claim "`κ/V` is bounded on `goodSet`".

The F-column of the window half must therefore be paid otherwise (the pointwise `𝔉 = ∫Φ²ψ(t)`
demands the *sharp* variance row `flatVar ≤ (S/V)²N + Cχ(Ξ/κ)²(Sν+ν²)` of
`FINDING_cubeDensePos_session10.md` §5 (R1), or the pair sum `Ps` — see
`FINDING_cubePerBox_session11.md` §6). -/
def InBoxVarRow (v : E3 → ℝ) (h : Work.UBB.ScatSol v) : Prop :=
  ∃ ε₀ Cv : ℝ, 0 < ε₀ ∧ 0 ≤ Cv ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.AprioriCount.bSide v μ)) (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.AprioriCount.bSide v μ)
              (Work.AprioriCount.bRatio v μ) μ →
        (∀ᵐ x ∂(MeasureTheory.volume.restrict
            (Submission.BoseGases.abox n (Work.AprioriCount.bSide v μ))),
          (Φ : Submission.BoseGases.X n → ℝ) x ≠ 0 →
            ∀ i : Fin n, x i ∈ Work.AprioriCount.bA v μ u) →
        Work.AprioriCount.bVar v μ (Φ : Submission.BoseGases.X n → ℝ) u
          ≤ Cv * Work.AprioriCount.chiSqBound v μ
              * (((n : ℝ) / Work.AprioriCount.bV v μ u)
                    * Work.AprioriCount.bN v μ n (Φ : Submission.BoseGases.X n → ℝ)
                  + ((n : ℝ) / Work.AprioriCount.bV v μ u + 1 / Work.AprioriCount.bKap v μ u)
                    * Work.AprioriCount.bNu v μ (Φ : Submission.BoseGases.X n → ℝ) u)
              / Work.AprioriCount.bKap v μ u

/-- **(A4-large)** The in-box row **above the count window** `Cn·μ|B(u)| < n`, with `Cn ≥ 2`.
It is proved from the state-independent per-size bounds `Work.BoseB1Cube.CubeSmallNArbEx` (FS's
`e_B(n,μ') ≥ (1/18)μ'(n/|B|)∬w₁` at the block sizes — the honest residual of the *grouping* step)
plus the PROVED cube descent `Work.BoseB1Cube.sbWordCube_descent_atSizes` and the crude `F`-row; see
`inBoxCubeRowLarge_of_smallNArb` below, which carries `CubeSmallNArbEx` as a hypothesis (so this
`Prop` itself is unconditional). -/
def InBoxCubeRowLarge (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ Cn c₁ C : ℝ, 2 ≤ Cn ∧ 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
        Cn * μ * Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u < (n : ℝ) →
        (∀ᵐ x ∂(MeasureTheory.volume.restrict
            (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
          (Φ : Submission.BoseGases.X n → ℝ) x ≠ 0 →
            ∀ i : Fin n, x i ∈ Submission.BoseGases.dlBox
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) →
        (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2) = 1 →
        Work.BoseFixB1S.PerBoxFCube v h R c₁ C μ n Φ u

/-- **THE ASSEMBLY (PROVED)**: the two halves of A4, at one and the same window constant `Cn`,
give the in-box row at *every* count.  The constants are merged by `min`/`max`
(`c₁ := min c₁W c₁L`, `C := max CW CL`, `ε₀ := min εW εL`) through the PROVED monotonicity
`Work.BoseB1Cube.perBoxFCube_mono` — smaller `c₁` and larger `C` only weaken the row — and the case
split is the total order `n ≤ Cn·μ|B(u)|` or `n > Cn·μ|B(u)|`. -/
theorem inBoxCubeRow_of_window_large {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v)
    (hW : InBoxCubeRowWindow v h R) (hL : InBoxCubeRowLarge v h R) :
    InBoxCubeRow v h R := by
  obtain ⟨εL, Cn, c₁L, CL, hCn2, hεL, hc₁L, hCL, hrowL⟩ := hL
  have hCn1 : (1 : ℝ) ≤ Cn := le_trans (by norm_num) hCn2
  obtain ⟨εW, c₁W, CW, hεW, hc₁W, hCW, hrowW⟩ := hW Cn hCn1
  refine ⟨min εL εW, min c₁L c₁W, max CL CW, lt_min hεL hεW,
    lt_min hc₁L hc₁W, le_max_of_le_left hCL, ?_⟩
  intro μ hAdm n Φ u hu hin hnorm
  have hAdmL : Work.BoseBoxFix.Adm v εL μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdmW : Work.BoseBoxFix.Adm v εW μ := Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
  rcases le_or_gt ((n : ℝ))
      (Cn * μ * Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) with hle | hlt
  · refine perBoxFCube_mono Φ u (min_le_right _ _) (le_max_right _ _)
      (perBoxCubeFWeight_nonneg h hv hvrad hR hv_supp hAdmW Φ u)
      (perBoxCubeErr_nonneg hAdmW (le_of_lt (Work.BoseFixB1.adm_a_pos hAdmW)) Φ u) ?_
    exact hrowW μ hAdmW n Φ u hu hle hin hnorm
  · refine perBoxFCube_mono Φ u (min_le_left _ _) (le_max_left _ _)
      (perBoxCubeFWeight_nonneg h hv hvrad hR hv_supp hAdmL Φ u)
      (perBoxCubeErr_nonneg hAdmL (le_of_lt (Work.BoseFixB1.adm_a_pos hAdmL)) Φ u) ?_
    exact hrowL μ hAdmL n Φ u hu hlt hin hnorm

end Work.BoseB1Cube
