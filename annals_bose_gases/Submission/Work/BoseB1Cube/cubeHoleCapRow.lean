import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.CubeRows
import Submission.Work.BoseB1Cube.chiSmallB_tBwordKinInd_le_tBdiagFormInd
import Submission.Work.BoseB1Cube.flatPairMass_sub_w1MassB_ge_const_mul
import Submission.Work.BoseB1Cube.slotPoincare_dlBox
import Submission.Work.BoseFixB1.q1CrossW1csLocalised
import Submission.Work.BoseFixB1S.capCountPackAeB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory
open scoped BigOperators

set_option maxHeartbeats 1600000

namespace Work.BoseB1Cube

/-!
## The exact residual of the target (`FINDING_cubeHoleCapRow.md`)

`cubeHoleCapRow` is the "hole row" of the cube flat band in the **currency of the demand**: its
left-hand side is `½W₁(τ²‖Φ‖² + Var) − μW₁τ‖Φ‖² + μ·fibSum` (the mean-field demand minus the
chemical line) and its only state-dependent payer on the right is the `‖p‖²`-weighted **Dirichlet
word** `tBdiagFormInd … (·)²`; the remaining rows (`C·flatErrB`, `flatSlackB`) are the arithmetic
slack, and the last row `μ(a v)(boxQCount + normB)` is a *nonnegative* allowance.

`CubeHoleDRow` below is the same inequality with that last (nonnegative) row deleted.  It is
therefore **strictly stronger** than the target, it is what the razor analysis of
`FINDING_cubeHoleCapRow.md` (and `FINDING_cubeBandHole.md` §7(c)) identifies as the honest
residual, and the passage `CubeHoleDRow ⟹ cubeHoleCapRow` is the one-line monotonicity proved
below.  So the whole content of the target is the sharp hole/capacity row `CubeHoleDRow` — the
cube-cutoff form of FS `lm:appinteractionestimate` for *pair-dead* states (equivalently of the
fleet's `Work.BoseFixB1S.mfSharpHoleKinPaysB1` / `Work.Analysis.HoleVoidCost.
holeVoidCostCountQuadGood`).
-/

/-! ### The algebraic core of the target (the razor bookkeeping)

The target's left-hand side minus the allowance `flatSlackB` is, *identically* and for arbitrary
reals, `A·(N·(μ(τ−μ)²/(8(τ+μ)) − μ²/2) + V·μ²/(2(τ+μ)²)) + μ·F`; at the razor `τ = μ` the bracket
collapses to `V/8 − μ²N/2`.  The two lemmas below are the reusable form of the arithmetic recorded
in `FINDING_cubeHoleCapRow.md` §3 (the `(1/2)`, `(1/8)` and `4·(1/8)` coefficients are those of
`Work.BoseFixB1.Up.flatSlackB`; the hypothesis `s + m ≠ 0` is needed because Lean's division is
total — at `s = −m` the two sides genuinely differ). -/

/-- **The flat-branch identity.**  With `A = W₁`, `s = flatTau`, `m = μ`, `N = normB`,
`V = flatVar`, `F = flatFibSum` this says

    `demand − flatSlackB = A·(N·(m(s−m)²/(8(s+m)) − m²/2) + V·m²/(2(s+m)²)) + m·F`,

i.e. the mean-field demand minus the chemical line, after the slack, is the *quadratic* remainder
`A·N·m(τ−μ)²/(8(τ+μ))` (vanishing at the razor) plus the variance row plus the fibre row. -/
theorem flatDemand_sub_slack (A s m N V F : ℝ) (h : s + m ≠ 0) :
    ((1 / 2) * A * (s ^ 2 * N + V) - m * A * s * N + m * F)
        - A * ((s - m) ^ 2 * N * (1 / 2 - (1 / 8) * m / (s + m))
            + V * (1 / 2 - 4 * (1 / 8) * m ^ 2 / (s + m) ^ 2))
      = A * (N * (m * (s - m) ^ 2 / (8 * (s + m)) - m ^ 2 / 2)
          + V * m ^ 2 / (2 * (s + m) ^ 2)) + m * F := by
  have h2 : (s + m) ^ 2 ≠ 0 := pow_ne_zero 2 h
  field_simp
  ring

/-- **The usable upper bound of the identity** (the shape a ledger consumes): for nonnegative data
the remainder is at most `m·F + (A/8)·m(s+m)N + A·V/2` — the *fibre* row, the *quadratic* row at
its worst rate, and the *variance* row at its worst rate. -/
theorem flatDemand_sub_slack_le (A s m N V F : ℝ) (hA : 0 ≤ A) (hs : 0 ≤ s) (hm : 0 < m)
    (hN : 0 ≤ N) (hV : 0 ≤ V) :
    ((1 / 2) * A * (s ^ 2 * N + V) - m * A * s * N + m * F)
        - A * ((s - m) ^ 2 * N * (1 / 2 - (1 / 8) * m / (s + m))
            + V * (1 / 2 - 4 * (1 / 8) * m ^ 2 / (s + m) ^ 2))
      ≤ m * F + (A / 8) * m * (s + m) * N + A * V / 2 := by
  have hsm : 0 < s + m := by linarith
  have hne : s + m ≠ 0 := ne_of_gt hsm
  rw [flatDemand_sub_slack A s m N V F hne]
  have hsq : (s - m) ^ 2 ≤ (s + m) ^ 2 := by nlinarith [mul_nonneg hs hm.le]
  have hsqm : m ^ 2 ≤ (s + m) ^ 2 := by nlinarith [mul_nonneg hs hm.le]
  have h1 : m * (s - m) ^ 2 / (8 * (s + m)) ≤ m * (s + m) / 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_left hsq hm.le]
  have h2 : V * m ^ 2 / (2 * (s + m) ^ 2) ≤ V / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_left hsqm hV]
  have key : N * (m * (s - m) ^ 2 / (8 * (s + m)) - m ^ 2 / 2) ≤ N * (m * (s + m) / 8) := by
    have hh : m * (s - m) ^ 2 / (8 * (s + m)) - m ^ 2 / 2 ≤ m * (s + m) / 8 := by
      nlinarith [h1, sq_nonneg m]
    exact mul_le_mul_of_nonneg_left hh hN
  have h3 : A * (N * (m * (s - m) ^ 2 / (8 * (s + m)) - m ^ 2 / 2))
      ≤ A * (N * (m * (s + m) / 8)) := mul_le_mul_of_nonneg_left key hA
  have h4 : A * (V * m ^ 2 / (2 * (s + m) ^ 2)) ≤ A * (V / 2) :=
    mul_le_mul_of_nonneg_left h2 hA
  have h5 : A * (N * (m * (s - m) ^ 2 / (8 * (s + m)) - m ^ 2 / 2)
        + V * m ^ 2 / (2 * (s + m) ^ 2)) + m * F
      ≤ A * (N * (m * (s + m) / 8) + V / 2) + m * F := by linarith
  have h6 : A * (N * (m * (s + m) / 8) + V / 2) = (A / 8) * m * (s + m) * N + A * V / 2 := by ring
  linarith [h5, h6.le, h6.ge]

/-- **The gap-free hole row**: the target's inequality with the nonnegative allowance row
`μ(a v)(boxQCount + normB)` deleted.  Strictly stronger than `cubeHoleCapRow`
(`boxQCount ≥ 0` by `Work.BoseFixB1S.boxQCount_nonneg`, `normB ≥ 0` by
`Work.BoseFixB1.normB_nonneg`, `μ > 0` and `a v > 0` on `Adm`). -/
def CubeHoleDRow (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : EuclideanSpace ℝ (Fin 3)),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) μ →
        ‖((Work.BoseFixB1.pL v μ) * (Work.BoseFixB1.pD v μ)) • u‖
            < (Work.BoseFixB1.pL v μ) / 2
              + (Work.BoseFixB1.pL v μ) * (Work.BoseFixB1.pD v μ) / 2 →
        Work.BoseFixB1.flatPairSum v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ≤ 0 →
        (1 / 2) * Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u
            * (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ^ 2
                * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
              + Work.BoseFixB1.Up.flatVar v μ (Φ : Submission.BoseGases.X n → ℝ) u)
          - μ * Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u
              * Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
              * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
          + μ * Work.BoseFixB1.flatFibSum h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
        ≤ Work.UBBInputs8.tBdiagFormInd (Work.BoseFixB1.pL v μ)
              (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
              (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
              (Submission.BoseGases.chiSmallB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u)
              (fun r : ℝ => r ^ 2) (Φ : Submission.BoseGases.X n → ℝ)
          + C * Work.BoseFixB1.Up.flatErrB v R μ (Φ : Submission.BoseGases.X n → ℝ) u
          + Work.BoseFixB1.Up.flatSlackB v h μ (Φ : Submission.BoseGases.X n → ℝ) u

/-- **`CubeHoleDRow` implies the target**: the deleted row `μ(a v)(boxQCount + normB)` is
nonnegative (positivity of `Adm`: `0 < μ`, `0 < a v` of `Work.BoseFixB1.adm_a_pos`; the two state
functionals are nonnegative). -/
theorem cubeHoleCapRow_of_DRow {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R : ℝ} (hrow : CubeHoleDRow v h R) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) μ →
          ‖((Work.BoseFixB1.pL v μ) * (Work.BoseFixB1.pD v μ)) • u‖
              < (Work.BoseFixB1.pL v μ) / 2
                + (Work.BoseFixB1.pL v μ) * (Work.BoseFixB1.pD v μ) / 2 →
          Work.BoseFixB1.flatPairSum v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ≤ 0 →
          (1 / 2) * Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u
              * (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                    (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ^ 2
                  * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
                + Work.BoseFixB1.Up.flatVar v μ (Φ : Submission.BoseGases.X n → ℝ) u)
            - μ * Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u
                * Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                    (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
                * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
            + μ * Work.BoseFixB1.flatFibSum h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
          ≤ Work.UBBInputs8.tBdiagFormInd (Work.BoseFixB1.pL v μ)
                (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                (Submission.BoseGases.chiSmallB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u)
                (fun r : ℝ => r ^ 2) (Φ : Submission.BoseGases.X n → ℝ)
            + C * Work.BoseFixB1.Up.flatErrB v R μ (Φ : Submission.BoseGases.X n → ℝ) u
            + Work.BoseFixB1.Up.flatSlackB v h μ (Φ : Submission.BoseGases.X n → ℝ) u
            + μ * (_root_.BoseGases.a v)
                * (Work.BoseFixB1S.boxQCount
                      (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                      (Work.BoseFixB1.pL v μ)
                      (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                      (Φ : Submission.BoseGases.X n → ℝ)
                  + Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)) := by
  obtain ⟨ε₀, C, hε₀, hC, hbody⟩ := hrow
  refine ⟨ε₀, C, hε₀, hC, ?_⟩
  intro μ hAdm n Φ u hu hcorner hpair
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have ha : 0 < _root_.BoseGases.a v := Work.BoseFixB1.adm_a_pos hAdm
  have hQ : 0 ≤ Work.BoseFixB1S.boxQCount
      (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
      (Work.BoseFixB1.pL v μ)
      (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
      (Φ : Submission.BoseGases.X n → ℝ) :=
    Work.BoseFixB1S.boxQCount_nonneg _ _ _ _
  have hN : 0 ≤ Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) :=
    Work.BoseFixB1.normB_nonneg Φ
  have hnn : 0 ≤ μ * (_root_.BoseGases.a v)
      * (Work.BoseFixB1S.boxQCount
            (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
            (Work.BoseFixB1.pL v μ)
            (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
            (Φ : Submission.BoseGases.X n → ℝ)
        + Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)) :=
    mul_nonneg (mul_nonneg hμ.le ha.le) (add_nonneg hQ hN)
  exact le_trans (hbody μ hAdm n Φ u hu hcorner hpair) (by linarith [hnn])

/-- **The honest residual in the *spectral* currency** — the target's inequality with the Dirichlet
word `D` replaced by the *cut-off* spectral word `cubeSpectral = tBwordKinInd … (sbCut μ (a v))`
(i.e. `fsKinCoeff` in place of `‖·‖²`), with the nonnegative allowance row deleted.

By the PROVED `Work.BoseB1Cube.chiSmallB_tBwordKinInd_le_tBdiagFormInd` the spectral word is
dominated by the Dirichlet word, so this row is *strictly stronger* than `CubeHoleDRow` (hence
than the target), and it is exactly the residual the requester's own analysis identifies as the
honest one (`FINDING_cubeBandHole.md` §7(c): the demand's functionals on the left, no lossy
Dirichlet→spectral bridge).  A prover who establishes it gets the target for free. -/
def CubeHoleSpecRow (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : EuclideanSpace ℝ (Fin 3)),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) μ →
        ‖((Work.BoseFixB1.pL v μ) * (Work.BoseFixB1.pD v μ)) • u‖
            < (Work.BoseFixB1.pL v μ) / 2
              + (Work.BoseFixB1.pL v μ) * (Work.BoseFixB1.pD v μ) / 2 →
        Work.BoseFixB1.flatPairSum v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ≤ 0 →
        (1 / 2) * Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u
            * (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ^ 2
                * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
              + Work.BoseFixB1.Up.flatVar v μ (Φ : Submission.BoseGases.X n → ℝ) u)
          - μ * Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u
              * Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
              * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
          + μ * Work.BoseFixB1.flatFibSum h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
        ≤ Work.BoseFixB1B.cubeSpectral v μ (Φ : Submission.BoseGases.X n → ℝ) u
          + C * Work.BoseFixB1.Up.flatErrB v R μ (Φ : Submission.BoseGases.X n → ℝ) u
          + Work.BoseFixB1.Up.flatSlackB v h μ (Φ : Submission.BoseGases.X n → ℝ) u

/-- **The spectral row gives the Dirichlet row** — the `chiSmallB` symbol monotonicity
`cubeSpectral ≤ D` (`Work.BoseB1Cube.chiSmallB_tBwordKinInd_le_tBdiagFormInd`), applied with the
sliding parameters (`Adm` supplies `0 < ℓ`, `0 < d`, `0 < μ`, `0 < a v`, hence `0 ≤ sbCut μ (a v)`,
and `M = mValue = 48 ≥ 4` is the hard-wired regularity). -/
theorem cubeHoleDRow_of_specRow {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R : ℝ} (hrow : CubeHoleSpecRow v h R) : CubeHoleDRow v h R := by
  obtain ⟨ε₀, C, hε₀, hC, hbody⟩ := hrow
  refine ⟨ε₀, C, hε₀, hC, ?_⟩
  intro μ hAdm n Φ u hu hcorner hpair
  have hℓ : 0 < Work.BoseFixB1.pL v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < Work.BoseFixB1.pD v μ := Work.BoseFixB1.adm_d_pos hAdm
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have hav : 0 < _root_.BoseGases.a v := Work.BoseFixB1.adm_a_pos hAdm
  have hc : 0 ≤ Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v) :=
    (Work.BoseFixB1S.sbCut_pos hμ hav).le
  have hM : 4 ≤ Work.BoseFixB1.pM v μ := by
    simp only [Work.BoseFixB1.pM]
    rw [Work.BoseFixB1.M_eq_mValue]
    norm_num [Work.BoseBox.mValue]
  have hmono := Work.BoseB1Cube.chiSmallB_tBwordKinInd_le_tBdiagFormInd
    (M := Work.BoseFixB1.pM v μ) hM hℓ hd hc u
    (V := Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
    (N := n) (Φ := (Φ : Submission.BoseGases.X n → ℝ)) Φ.contDiff
  have hspec : Work.BoseFixB1B.cubeSpectral v μ (Φ : Submission.BoseGases.X n → ℝ) u
      ≤ Work.UBBInputs8.tBdiagFormInd (Work.BoseFixB1.pL v μ)
          (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
          (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
          (Submission.BoseGases.chiSmallB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u)
          (fun r : ℝ => r ^ 2) (Φ : Submission.BoseGases.X n → ℝ) := by
    simpa only [Work.BoseFixB1B.cubeSpectral, Work.BoseFixB1.bA, Work.BoseFixB1.bV,
      Work.BoseFixB1.bSide, Work.BoseFixB1.bD, Work.BoseFixB1.bM] using hmono
  exact le_trans (hbody μ hAdm n Φ u hu hcorner hpair) (by linarith [hspec])

/-- **The target from the spectral hole row** (composition of the two reductions above). -/
theorem cubeHoleCapRow_of_specRow {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R : ℝ} (hrow : CubeHoleSpecRow v h R) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) μ →
          ‖((Work.BoseFixB1.pL v μ) * (Work.BoseFixB1.pD v μ)) • u‖
              < (Work.BoseFixB1.pL v μ) / 2
                + (Work.BoseFixB1.pL v μ) * (Work.BoseFixB1.pD v μ) / 2 →
          Work.BoseFixB1.flatPairSum v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ≤ 0 →
          (1 / 2) * Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u
              * (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                    (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ^ 2
                  * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
                + Work.BoseFixB1.Up.flatVar v μ (Φ : Submission.BoseGases.X n → ℝ) u)
            - μ * Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u
                * Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                    (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
                * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
            + μ * Work.BoseFixB1.flatFibSum h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
          ≤ Work.UBBInputs8.tBdiagFormInd (Work.BoseFixB1.pL v μ)
                (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                (Submission.BoseGases.chiSmallB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u)
                (fun r : ℝ => r ^ 2) (Φ : Submission.BoseGases.X n → ℝ)
            + C * Work.BoseFixB1.Up.flatErrB v R μ (Φ : Submission.BoseGases.X n → ℝ) u
            + Work.BoseFixB1.Up.flatSlackB v h μ (Φ : Submission.BoseGases.X n → ℝ) u
            + μ * (_root_.BoseGases.a v)
                * (Work.BoseFixB1S.boxQCount
                      (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                      (Work.BoseFixB1.pL v μ)
                      (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                      (Φ : Submission.BoseGases.X n → ℝ)
                  + Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)) :=
  cubeHoleCapRow_of_DRow (cubeHoleDRow_of_specRow hrow)

/-! ## Session 3: the ledger is discharged down to the `χ`-count cap

The material above this point (sessions 1–2) records the target's exact residual and the pair-dead
void structure.  From here on the file develops, and proves,

* `CubeHoleChiCount` — the **single** state-level input the target needs (a.e. at most `C₀`
  particles in the support of the cutoff);
* the three state-level bounds the ledger consumes (`scount_le_of_chiCount`,
  `fibSum_le_of_chiCount`, `flatT2_le_of_chiCount`) and the pure-real razor arithmetic
  (`holeCapArith`);
* **`cubeHoleCapRow_of_chiCount`** — the target from the cap, with explicit fixed constants;
* **`cubeHoleCapRow_of_nullZero`** — the target when the zero set of `v` is null (the hard-core /
  positive-bump case), where the cap holds with `C₀ = 1`.

⚠ The cap is **FALSE** in general (the shell/cluster family), so it must not be re-filed as a
free-standing lemma: see `FINDING_cubeHoleCapRow_session3.md` §§3–4.  The remaining content of the
target is the *Dirichlet/capacity* row `(DROW)` of that note, the cube-cutoff pair-dead form of FS
`lm:appinteractionestimate`.  **The target itself is TRUE; do not `declare_false`.** -/

/-! ## The pair-dead structure: the a.e. void and the sharp count cap

The hypothesis `flatPairSum ≤ 0` of the target is **not** a soft sign condition, and this section
records its exact quantitative content (both lemmas are assemblies of PROVED corpus facts).

* Since `0 ≤ v` makes the localised pair kernel pointwise nonnegative (`wSmallPair_nonneg`), the
  hypothesis forces the pair integrand to vanish, hence a.e. on the support of the state every two
  particles in the support of the cutoff sit at a distance where `v` vanishes — the *void
  structure* (`pairVoidAeB1`).
* If in addition `v ≠ 0` a.e. on a ball of radius `r ≤ R`, that void is a *separation*: the
  particles in the cutoff's support are `r`-separated and their number is Lipschitz
  (`capCountPackAeB1`):

      `Σᵢ ∫ Φ² 1_{supp χ}(xᵢ) ≤ 64·((ℓd)³/r³)·‖Φ‖²`.

This is the only structural input the pair-dead branch has; it is what replaces the missing count
window of the flat arm, and it is the reason the pair-dead branch can be attacked at all. -/

/-- **The pointwise sup bound of the cube cutoff** (non-absolute form):
`χ ≤ chiSupAbs·chiSmallDecay M`. -/
theorem chiSmallB_le_supDecay {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ}
    (u x : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.chiSmallB M ℓ d u x
      ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M := by
  refine (le_abs_self _).trans ?_
  refine (Work.SmallBoxSliding.abs_chiSmallB_le (M := M) hM u x).trans ?_
  have h2 : Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)
      ≤ Submission.BoseGases.chiSmallDecay M := by
    have h := Submission.BoseGases.chiSmall_decay_coord_le_decay (M := M) hM ((ℓ * d)⁻¹ • x - u)
    rwa [abs_of_nonneg (Submission.BoseGases.chiSmall_nonneg M _)] at h
  exact mul_le_mul_of_nonneg_left h2 Submission.BoseGases.chiSupAbs_nonneg

/-- **The absolute pointwise sup bound of the cube cutoff**: `|χ| ≤ chiSupAbs·chiSmallDecay M`. -/
theorem chiSmallB_abs_le_sup {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ}
    (u x : EuclideanSpace ℝ (Fin 3)) :
    |Submission.BoseGases.chiSmallB M ℓ d u x|
      ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M := by
  rw [abs_of_nonneg (Submission.BoseGases.chiSmallB_nonneg M ℓ d u x)]
  exact chiSmallB_le_supDecay hM u x

/-- **The a.e. void structure of the pair-dead branch** (corpus form).  From `0 ≤ v`, `MemLp v 1`
and the regime `R ≤ ℓd/16`, `R ≤ ℓ·chiR0`, the hypothesis `flatPairSum ≤ 0` forces, a.e. on the
support of the state, every pair of particles in the cutoff's support to have vanishing potential. -/
theorem pairDead_voidAe {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR16 : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    {u : EuclideanSpace ℝ (Fin 3)} {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ)
    (hpair : Work.BoseFixB1.flatPairSum v M ℓ d u Φ ≤ 0) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
      Φ x ≠ 0 → ∀ i j : Fin n, i ≠ j →
        Submission.BoseGases.chiSmallB M ℓ d u (x i) * v (x i - x j)
          * Submission.BoseGases.chiSmallB M ℓ d u (x j) = 0 :=
  Work.BoseFixB1S.pairVoidAeB1 h hv hv1 hR hv_supp hM hℓ hd hR16 hRχ
    (fun z hz => by
      have hc := Submission.BoseGases.convScale_ge_half_ball (ℓ := ℓ) hℓ hR.le hRχ hz
      simpa only [Submission.BoseGases.convScale] using hc)
    hΦc (le_antisymm hpair (Work.BoseFixB1.pairSum_nonneg hv u Φ))

/-- **The sharp count cap of the pair-dead branch** (corpus form): when `v` is nonzero a.e. on a
ball of radius `r ≤ R`, the `r`-separation of the cutoff's support caps the weighted particle
count by `64·((ℓd)³/r³)·‖Φ‖²`. -/
theorem pairDead_chiCountCap {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (hrR : r ≤ R)
    (hball : ∀ᵐ z ∂(MeasureTheory.volume.restrict
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r)), v z ≠ 0)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR16 : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    {u : EuclideanSpace ℝ (Fin 3)} {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ)
    (hpair : Work.BoseFixB1.flatPairSum v M ℓ d u Φ ≤ 0) :
    ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
        (Function.support (Submission.BoseGases.chiSmallB M ℓ d u)).indicator
          (fun _ => (1 : ℝ)) (x i)
      ≤ 64 * ((ℓ * d) ^ 3 / r ^ 3) * ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 :=
  Work.BoseFixB1S.capCountPackAeB1 h hv hv1 hR hr hrR hball hv_supp hM hℓ hd hR16 hRχ
    (fun z hz => by
      have hc := Submission.BoseGases.convScale_ge_half_ball (ℓ := ℓ) hℓ hR.le hRχ hz
      simpa only [Submission.BoseGases.convScale] using hc)
    hΦc (le_antisymm hpair (Work.BoseFixB1.pairSum_nonneg hv u Φ))

/-- **The pair-dead void structure at the sliding parameters** (the target's own quantifier
shape): there is a diluteness threshold `ε₀ > 0` such that at every admissible `μ`, every box
state whose pair sum is `≤ 0` satisfies the a.e. void identity of `pairDead_voidAe`.  The regime
hypotheses of the corpus statement are produced from `Adm` by shrinking `ε₀`
(`Work.BoseFixB1.regime_sideAt_ge`). -/
theorem pairDead_voidAe_sliding {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          Work.BoseFixB1.flatPairSum v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ≤ 0 →
          ∀ᵐ x ∂(MeasureTheory.volume.restrict
              (Submission.BoseGases.abox n (Work.BoseFixB1.pL v μ))),
            Φ x ≠ 0 → ∀ i j : Fin n, i ≠ j →
              Submission.BoseGases.chiSmallB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u (x i)
                * v (x i - x j)
                * Submission.BoseGases.chiSmallB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                    (Work.BoseFixB1.pD v μ) u (x j) = 0 := by
  obtain ⟨ε₁, hε₁, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨ε₁, hε₁, ?_⟩
  intro μ hAdm n Φ u hpair
  obtain ⟨h16, hχ⟩ := hreg μ (Work.BoseFixB1.adm_mu_pos hAdm) hAdm.2.1
  have hM : 1 ≤ Work.BoseFixB1.pM v μ := by
    simp only [Work.BoseFixB1.pM]
    rw [Work.BoseFixB1.M_eq_mValue]
    norm_num [Work.BoseBox.mValue]
  refine pairDead_voidAe h hv hv1 hR hv_supp hM (Work.BoseFixB1.adm_ell_pos hAdm)
    (Work.BoseFixB1.adm_d_pos hAdm) h16 hχ Φ.contDiff.continuous hpair

/-- **The sharp count cap at the sliding parameters** (the target's own quantifier shape), under
the extra hypothesis that `v` does not vanish a.e. on a ball of radius `r ≤ R`. -/
theorem pairDead_chiCountCap_sliding {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (hrR : r ≤ R)
    (hball : ∀ᵐ z ∂(MeasureTheory.volume.restrict
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r)), v z ≠ 0)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          Work.BoseFixB1.flatPairSum v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ≤ 0 →
          (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.pL v μ), (Φ x) ^ 2 *
              (Function.support (Submission.BoseGases.chiSmallB (Work.BoseFixB1.pM v μ)
                (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)).indicator
                (fun _ => (1 : ℝ)) (x i))
            ≤ 64 * ((Work.BoseFixB1.pL v μ * Work.BoseFixB1.pD v μ) ^ 3 / r ^ 3)
                * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
  obtain ⟨ε₁, hε₁, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨ε₁, hε₁, ?_⟩
  intro μ hAdm n Φ u hpair
  obtain ⟨h16, hχ⟩ := hreg μ (Work.BoseFixB1.adm_mu_pos hAdm) hAdm.2.1
  have hM : 1 ≤ Work.BoseFixB1.pM v μ := by
    simp only [Work.BoseFixB1.pM]
    rw [Work.BoseFixB1.M_eq_mValue]
    norm_num [Work.BoseBox.mValue]
  have hcap := pairDead_chiCountCap h hv hv1 hR hr hrR hball hv_supp hM
    (Work.BoseFixB1.adm_ell_pos hAdm) (Work.BoseFixB1.adm_d_pos hAdm) h16 hχ
    Φ.contDiff.continuous hpair
  -- rewrite the two box integrals as `normB` and the side as `pL`
  simpa only [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB, Work.BoseFixB1.pL,
    Work.BoseFixB1.pM, Work.BoseFixB1.pD] using hcap

/-! ## The `Q`-half of the Dirichlet row of the target

The whole analytic content of the target is the row `aμ·S ≲ D + μ(a v)(Q+N) + C·flatErrB`
(`FINDING_cubeHoleCapRow_session2.md` §2–§3), where `S = Σᵢ∫Φ²χ²(xᵢ)` is the state's `χ²`-content.
`S` splits by `1_A Φ = P_iΦ + Q_iΦ`: the **excited half** `S_Q = Σᵢ∫(χ·Q_{B,i}Φ)²` is paid by the
Dirichlet slot alone, through the two PROVED bricks

* `Work.BoseB1Cube.cubeKinPeel` — the cube-window Dirichlet identity
  `D = Σᵢ∫Σ_k(∂_{kcDir}(χ·Q_{B,i}IndΦ))²`, and
* `Work.BoseB1Cube.slotPoincare_dlBox` — the slot Friedrichs/Poincaré inequality on the small box.

The lemma below is their sum; the flat half needs the graded row
(`Work.BoseB1Cube.meanGradientGradedCube`) and the price term `wD_cube`, see the FINDING §5bis. -/

/-- **The excited `χ`-content is paid by the Dirichlet slot**:
`Σᵢ∫(χ·Q_{B,i}IndΦ)² ≤ 4(ℓd)²gradConst²·D` at `M ≥ 4`. -/
theorem cubeHoleQContent_le_dirichlet {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) {M : ℕ} (hM : 4 ≤ M) {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        (Submission.BoseGases.chiSmallB M ℓ d u (x i)
          * Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2)
      ≤ 4 * (ℓ * d) ^ 2 * Work.Analysis.HoleVoidCost.gradConst ^ 2
        * Work.UBBInputs8.tBdiagFormInd ℓ (Submission.BoseGases.dlBox ℓ d u)
            (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.chiSmallB M ℓ d u) (fun r : ℝ => r ^ 2) Φ := by
  rw [Work.BoseB1Cube.cubeKinPeel (u := u) (V := Work.SmallBoxSliding.boxMass ℓ d u) (M := M)
    hℓ hd hM hΦ]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  exact Work.BoseB1Cube.slotPoincare_dlBox hℓ hd u (M := M) (by omega) hΦ i



local notation "E3" => EuclideanSpace ℝ (Fin 3)

#check @Submission.BoseGases.abox_compact
#check @Submission.BoseGases.abox_measurable
#check @MeasureTheory.self_mem_ae_restrict
#check @Integrable.mul_bdd
#check @Finset.card_le_one
#check @Work.BoseFixB1S.integrableOn_sq_abox
#check @Work.BoseFixB1S.integrableOn_sq_indicator_abox
#check @Work.BoseFixB1.nCountB
#check @EuclideanSpace.norm_sq_eq
#check @Work.BoseFixB1.pairSum_nonneg

/-- A point of the cube `acube ℓ` has norm at most `√3 ℓ / 2`. -/
theorem norm_le_of_mem_acube {ℓ : ℝ} (hℓ : 0 < ℓ) {y : E3}
    (hy : y ∈ Submission.BoseGases.acube ℓ) : ‖y‖ ≤ Real.sqrt 3 * ℓ / 2 := by
  have hc : ∀ m : Fin 3, ‖y.ofLp m‖ ≤ ℓ / 2 := by
    intro m
    have h := (Submission.BoseGases.mem_acube_iff ℓ y).mp hy m
    rw [Set.mem_Icc] at h
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [h.1], h.2⟩
  have h2 : ‖y‖ ^ 2 ≤ (Real.sqrt 3 * ℓ / 2) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ m : Fin 3, ‖y.ofLp m‖ ^ 2
        ≤ ∑ _m : Fin 3, (ℓ / 2) ^ 2 := by
          refine Finset.sum_le_sum (fun m _ => ?_)
          exact pow_le_pow_left₀ (norm_nonneg _) (hc m) 2
      _ = 3 * (ℓ / 2) ^ 2 := by simp
      _ = (Real.sqrt 3 * ℓ / 2) ^ 2 := by
          have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
          nlinarith [h3]
  have h := sq_le_sq.mp h2
  rwa [abs_of_nonneg (norm_nonneg _),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sqrt 3 * ℓ / 2)] at h

/-- **The pair-dead structure with a null zero set.**  If the zero set of `v` is null, then on the
pair-dead branch a.e. configuration carries at most one particle in the support of the cutoff: the
pairwise products `χ(x i)·χ(x j)` vanish. -/
theorem pairDead_chiPairs_zero {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hZ : (MeasureTheory.volume : MeasureTheory.Measure E3) {z : E3 | v z = 0} = 0)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR16 : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (hden : ∀ z : E3, ‖z‖ ≤ R →
      1 / 2 ≤ Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi
        (ℓ⁻¹ • z))
    {u : E3} {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ)
    (hpair : Work.BoseFixB1.flatPairSum v M ℓ d u Φ ≤ 0) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
      Φ x ≠ 0 → ∀ i j : Fin n, i ≠ j →
        Submission.BoseGases.chiSmallB M ℓ d u (x i)
          * Submission.BoseGases.chiSmallB M ℓ d u (x j) = 0 := by
  classical
  have hpair0 : Work.BoseFixB1.pairSum v M ℓ d u Φ = 0 :=
    le_antisymm hpair (Work.BoseFixB1.pairSum_nonneg hv u Φ)
  have hvoid := Work.BoseFixB1S.pairVoidAeB1 h hv hv1 hR hv_supp hM hℓ hd hR16 hRχ hden hΦc hpair0
  -- a radius larger than the diameter of the box
  set r : ℝ := Real.sqrt 3 * ℓ + 1 with hrdef
  have hZ0 : (MeasureTheory.volume : MeasureTheory.Measure E3)
      ({z : E3 | v z = 0} ∩ Metric.ball (0 : E3) r) = 0 :=
    measure_mono_null Set.inter_subset_left hZ
  -- on the box every pair distance is `< r`
  have hdist : ∀ x : Submission.BoseGases.X n, x ∈ Submission.BoseGases.abox n ℓ →
      ∀ i j : Fin n, dist (x i) (x j) < r := by
    intro x hx i j
    have hi : ‖x i‖ ≤ Real.sqrt 3 * ℓ / 2 :=
      norm_le_of_mem_acube hℓ (((Submission.BoseGases.mem_abox_iff n ℓ x).mp hx) i)
    have hj : ‖x j‖ ≤ Real.sqrt 3 * ℓ / 2 :=
      norm_le_of_mem_acube hℓ (((Submission.BoseGases.mem_abox_iff n ℓ x).mp hx) j)
    have hsub : dist (x i) (x j) ≤ Real.sqrt 3 * ℓ := by
      rw [dist_eq_norm]
      calc ‖x i - x j‖ ≤ ‖x i‖ + ‖x j‖ := norm_sub_le _ _
        _ ≤ Real.sqrt 3 * ℓ := by linarith
    dsimp only [r]
    linarith
  have hin : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
      x ∈ Submission.BoseGases.abox n ℓ :=
    MeasureTheory.self_mem_ae_restrict (Submission.BoseGases.abox_measurable n ℓ)
  -- a.e. no pair difference lies in the zero set
  have hsepae : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
      ∀ i j : Fin n, i ≠ j → v (x i - x j) ≠ 0 := by
    have hall : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
        ∀ p : Fin n × Fin n, p.1 ≠ p.2 → v (x p.1 - x p.2) ≠ 0 := by
      rw [Filter.eventually_all]
      intro p
      by_cases hp : p.1 = p.2
      · exact Filter.Eventually.of_forall (fun x hne => (hne hp).elim)
      · filter_upwards
          [Work.BoseFixB1S.ae_pair_v_ne_zero (v := v) (ℓ := ℓ) hZ0 (i := p.1) (j := p.2) hp,
            hin] with x hx hxbox
        intro _
        exact hx (hdist x hxbox p.1 p.2)
    filter_upwards [hall] with x hx i j hij
    exact hx (i, j) hij
  filter_upwards [hvoid, hsepae] with x hvanish hne
  intro hΦne i j hij
  have h1 := hvanish hΦne i j hij
  have h2 := hne i j hij
  rcases mul_eq_zero.mp h1 with h1' | h1'
  · rcases mul_eq_zero.mp h1' with h1'' | h1''
    · rw [h1'', zero_mul]
    · exact absurd h1'' h2
  · rw [h1', mul_zero]

/-- If all pairwise products of `χ := chiSmallB M ℓ d u` vanish at the configuration `x`, then the
weighted count `∑_i χ(x i)²` is at most `supχ² = (chiSupAbs·chiSmallDecay M)²`: at most one
particle sits in the support of `χ`. -/
theorem chiSq_sum_le_of_pairs {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} {u : E3} {n : ℕ}
    {x : Submission.BoseGases.X n}
    (hpairs : ∀ i j : Fin n, i ≠ j →
      Submission.BoseGases.chiSmallB M ℓ d u (x i)
        * Submission.BoseGases.chiSmallB M ℓ d u (x j) = 0) :
    ∑ i : Fin n, (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2
      ≤ (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2 := by
  classical
  set χ : E3 → ℝ := Submission.BoseGases.chiSmallB M ℓ d u with hχdef
  set supχ : ℝ := Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M with hsupdef
  have hsupnn : 0 ≤ supχ ^ 2 := sq_nonneg _
  have hterm : ∀ i : Fin n, (χ (x i)) ^ 2 ≤ supχ ^ 2 := by
    intro i
    have h := chiSmallB_abs_le_sup (M := M) hM (ℓ := ℓ) (d := d) u (x i)
    have h' : |χ (x i)| ≤ supχ := by rw [hχdef, hsupdef]; exact h
    calc (χ (x i)) ^ 2 = |χ (x i)| ^ 2 := (sq_abs _).symm
      _ ≤ supχ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h' 2
  set S : Finset (Fin n) := Finset.univ.filter (fun i => χ (x i) ≠ 0) with hS
  have hcard : S.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hab
    have ha' : χ (x a) ≠ 0 := (Finset.mem_filter.mp ha).2
    have hb' : χ (x b) ≠ 0 := (Finset.mem_filter.mp hb).2
    exact mul_ne_zero ha' hb' (hpairs a b hab)
  have hzero : ∀ i : Fin n, i ∉ S → (χ (x i)) ^ 2 = 0 := by
    intro i hi
    have : ¬ (χ (x i) ≠ 0) := fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
    rw [not_not] at this
    rw [this]; ring
  rcases Nat.eq_zero_or_pos S.card with h0 | hpos
  · -- no particle in the support
    have : ∀ i : Fin n, (χ (x i)) ^ 2 = 0 := by
      intro i
      refine hzero i ?_
      intro hi
      rw [Finset.card_eq_zero] at h0
      rw [h0] at hi
      exact Finset.notMem_empty i hi
    simp [this, hsupnn]
  · -- exactly one particle in the support
    obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp (by omega : S.card = 1)
    have hsingle : ∀ i : Fin n, i ≠ i₀ → (χ (x i)) ^ 2 = 0 := by
      intro i hi
      refine hzero i ?_
      rw [hi₀]
      simp [hi]
    calc ∑ i : Fin n, (χ (x i)) ^ 2 = (χ (x i₀)) ^ 2 :=
          Finset.sum_eq_single i₀ (fun i _ hi => hsingle i hi) (by simp)
      _ ≤ supχ ^ 2 := hterm i₀

/-- If all pairwise products of `χ` vanish at `x`, then at most one particle lies in the support
of `χ`: the indicator sum is at most `1`. -/
theorem count_indicator_sum_le_one {M : ℕ} {ℓ d : ℝ} {u : E3} {n : ℕ}
    {x : Submission.BoseGases.X n}
    (hpairs : ∀ i j : Fin n, i ≠ j →
      Submission.BoseGases.chiSmallB M ℓ d u (x i)
        * Submission.BoseGases.chiSmallB M ℓ d u (x j) = 0) :
    (∑ i : Fin n,
        (Function.support (Submission.BoseGases.chiSmallB M ℓ d u)).indicator
          (fun _ => (1 : ℝ)) (x i)) ≤ 1 := by
  classical
  have h1 : (∑ i : Fin n,
        (Function.support (Submission.BoseGases.chiSmallB M ℓ d u)).indicator
          (fun _ => (1 : ℝ)) (x i))
      = ((Finset.univ.filter (fun i : Fin n =>
          x i ∈ Function.support (Submission.BoseGases.chiSmallB M ℓ d u))).card : ℝ) := by
    rw [← Finset.sum_boole (fun i : Fin n =>
      x i ∈ Function.support (Submission.BoseGases.chiSmallB M ℓ d u)) Finset.univ]
    exact Finset.sum_congr rfl (fun i _ => by rw [Set.indicator_apply])
  rw [h1]
  have hcard : (Finset.univ.filter (fun i : Fin n =>
      x i ∈ Function.support (Submission.BoseGases.chiSmallB M ℓ d u))).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hab
    have ha' : Submission.BoseGases.chiSmallB M ℓ d u (x a) ≠ 0 :=
      (Finset.mem_filter.mp ha).2
    have hb' : Submission.BoseGases.chiSmallB M ℓ d u (x b) ≠ 0 :=
      (Finset.mem_filter.mp hb).2
    exact mul_ne_zero ha' hb' (hpairs a b hab)
  exact_mod_cast hcard

/-! ### The `χ`-count cap and the target -/

/-- **The `χ`-count cap of the pair-dead branch**: a.e. on the support of the state at most `C₀`
particles lie in the support of the cutoff, uniformly in `μ` and in the state.  This is the
residual the target's ledger consumes (see `FINDING_cubeHoleCapRow_session3.md`). -/
def CubeHoleChiCount (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ C₀ : ℝ, 0 < ε₀ ∧ 0 ≤ C₀ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) μ →
        ‖((Work.BoseFixB1.pL v μ) * (Work.BoseFixB1.pD v μ)) • u‖
            < (Work.BoseFixB1.pL v μ) / 2
              + (Work.BoseFixB1.pL v μ) * (Work.BoseFixB1.pD v μ) / 2 →
        Work.BoseFixB1.flatPairSum v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ≤ 0 →
        ∀ᵐ x ∂(MeasureTheory.volume.restrict
            (Submission.BoseGases.abox n (Work.BoseFixB1.pL v μ))),
          (Φ : Submission.BoseGases.X n → ℝ) x ≠ 0 →
          (∑ i : Fin n,
            (Function.support (Submission.BoseGases.chiSmallB (Work.BoseFixB1.pM v μ)
              (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)).indicator
              (fun _ => (1 : ℝ)) (x i)) ≤ C₀

/-- **The count cap holds when the zero set of `v` is null**: then pair-deadness forces at most one
particle into the support of the cutoff, a.e. -/
theorem cubeHoleChiCount_of_nullZero {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v)
    (hZ : (MeasureTheory.volume : MeasureTheory.Measure E3) {z : E3 | v z = 0} = 0) :
    CubeHoleChiCount v h R := by
  obtain ⟨ε₁, hε₁, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨ε₁, 1, hε₁, zero_le_one, ?_⟩
  intro μ hAdm n Φ u hu hcorner hpair
  obtain ⟨h16, hχ⟩ := hreg μ (Work.BoseFixB1.adm_mu_pos hAdm) hAdm.2.1
  have hM : 1 ≤ Work.BoseFixB1.pM v μ := by
    simp only [Work.BoseFixB1.pM]
    rw [Work.BoseFixB1.M_eq_mValue]
    norm_num [Work.BoseBox.mValue]
  have hae := pairDead_chiPairs_zero (v := v) h hv hv1 hR hv_supp hZ hM
    (Work.BoseFixB1.adm_ell_pos hAdm) (Work.BoseFixB1.adm_d_pos hAdm) h16 hχ
    (fun z hz => by
      have hc := Submission.BoseGases.convScale_ge_half_ball (ℓ := Work.BoseFixB1.pL v μ)
        (Work.BoseFixB1.adm_ell_pos hAdm) hR.le hχ hz
      simpa only [Submission.BoseGases.convScale] using hc)
    Φ.contDiff.continuous hpair
  filter_upwards [hae] with x hx hΦne
  exact count_indicator_sum_le_one (hx hΦne)



/-- The pointwise square of the cutoff is dominated by `supχ²` times the indicator of its support. -/
theorem chi_sq_le_sup_mul_indicator {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} {u : E3} (z : E3) :
    (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2
      ≤ (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2
        * (Function.support (Submission.BoseGases.chiSmallB M ℓ d u)).indicator
            (fun _ => (1 : ℝ)) z := by
  by_cases hz : Submission.BoseGases.chiSmallB M ℓ d u z = 0
  · rw [hz, Set.indicator_of_notMem (by simpa [Function.mem_support] using hz)]
    simp
  · rw [Set.indicator_of_mem (Function.mem_support.mpr hz), mul_one]
    have h := chiSmallB_abs_le_sup (M := M) hM (ℓ := ℓ) (d := d) u z
    calc (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2
        = |Submission.BoseGases.chiSmallB M ℓ d u z| ^ 2 := (sq_abs _).symm
      _ ≤ (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h 2


/-! ### The three state-level bounds consumed by the ledger -/

/-- **The `χ²`-content bound**: the a.e. count cap bounds `flatScountB` by `supχ²·C₀·‖Φ‖²`. -/
theorem scount_le_of_chiCount {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) {u : E3} {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hcount : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
      Φ x ≠ 0 → (∑ i : Fin n,
        (Function.support (Submission.BoseGases.chiSmallB M ℓ d u)).indicator
          (fun _ => (1 : ℝ)) (x i)) ≤ C₀) :
    Work.BoseFixB1.flatScountB M ℓ d u Φ
      ≤ (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2 * C₀
        * ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 := by
  set supχ2 : ℝ := (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2
    with hsup
  have hsupnn : 0 ≤ supχ2 := by rw [hsup]; positivity
  have hpt : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
      (Φ x) ^ 2 * Work.BoseFixB1.nCountB M ℓ d u x ≤ (Φ x) ^ 2 * (supχ2 * C₀) := by
    filter_upwards [hcount] with x hx
    by_cases hΦ : Φ x = 0
    · rw [hΦ]; simp
    · have h1 : Work.BoseFixB1.nCountB M ℓ d u x ≤ supχ2 * C₀ := by
        rw [Work.BoseFixB1.nCountB]
        calc ∑ i : Fin n, (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2
            ≤ ∑ i : Fin n, supχ2 *
                (Function.support (Submission.BoseGases.chiSmallB M ℓ d u)).indicator
                  (fun _ => (1 : ℝ)) (x i) := by
              refine Finset.sum_le_sum (fun i _ => ?_)
              rw [hsup]
              exact chi_sq_le_sup_mul_indicator hM (x i)
          _ = supχ2 * ∑ i : Fin n,
                (Function.support (Submission.BoseGases.chiSmallB M ℓ d u)).indicator
                  (fun _ => (1 : ℝ)) (x i) := by rw [Finset.mul_sum]
          _ ≤ supχ2 * C₀ := mul_le_mul_of_nonneg_left (hx hΦ) hsupnn
      exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  have hint : Integrable (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 * (supχ2 * C₀))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)) :=
    (Work.BoseFixB1S.integrableOn_sq_abox hℓ hΦc).mul_const _
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _)
      (by rw [Work.BoseFixB1.nCountB]; exact Finset.sum_nonneg (fun i _ => sq_nonneg _))))
    hint hpt
  rw [Work.BoseFixB1.flatScountB]
  calc ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 * Work.BoseFixB1.nCountB M ℓ d u x
      ≤ ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 * (supχ2 * C₀) := hmono
    _ = supχ2 * C₀ * ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 := by
        rw [MeasureTheory.integral_mul_const]
        ring

/-- The fibre constant at box regularity `M` (independent of `ℓ`, `d`, `u`), times `8π`; the actual
fibre bound carries one extra factor `(a v)`. -/
noncomputable def KfibC (M : ℕ) : ℝ :=
  (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
    * ((2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
        / Work.SmallBoxSliding.smallConvLower M) * (8 * Real.pi))

theorem KfibC_nonneg (M : ℕ) : 0 ≤ KfibC M := by
  rw [KfibC]
  have h1 : 0 ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M :=
    mul_nonneg Submission.BoseGases.chiSupAbs_nonneg (Submission.BoseGases.chiSmallDecay_nonneg _)
  have h2 : 0 < Work.SmallBoxSliding.smallConvLower M := Work.SmallBoxSliding.smallConvLower_pos M
  positivity

/-- **The fibre bound**: the uniform fibre bound and the a.e. count cap give
`flatFibSum ≤ (KfibC M·(a v))·C₀·‖Φ‖²`. -/
theorem fibSum_le_of_chiCount {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) (hR16 : R ≤ ℓ * d / 16)
    (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0) (u : E3) {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hav : 0 ≤ _root_.BoseGases.a v)
    (hcount : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
      Φ x ≠ 0 → (∑ i : Fin n,
        (Function.support (Submission.BoseGases.chiSmallB M ℓ d u)).indicator
          (fun _ => (1 : ℝ)) (x i)) ≤ C₀) :
    Work.BoseFixB1.flatFibSum h M ℓ d u Φ
      ≤ KfibC M * _root_.BoseGases.a v * C₀
        * ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 := by
  set Kf : ℝ := KfibC M * _root_.BoseGases.a v with hKf
  have hKfnn : 0 ≤ Kf := by
    rw [hKf]; exact mul_nonneg (KfibC_nonneg M) hav
  have hnonneg : ∀ z : E3,
      0 ≤ Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z :=
    fun z => Work.BoseFixB1.q1cw1_w1Fibre_nonneg hv_supp hR hv hvrad h u z
  have habs : ∀ z : E3,
      |Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z| ≤ Kf := by
    intro z
    have h1 := Work.BoseFixB1.wSmall1Pair_fibre_abs_le (v := v) (R0 := R) hv_supp hR hv hvrad h
      hM hℓ hd hR16 hRχ u z
    have h1' : (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
          * ((2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
              / Work.SmallBoxSliding.smallConvLower M) * (8 * Real.pi * _root_.BoseGases.a v))
        = Kf := by rw [hKf, KfibC]; ring
    rw [← h1']
    simpa only [Submission.BoseGases.w1Fibre, Submission.BoseGases.wSmall1Pair] using h1
  have hzero : ∀ z : E3, Submission.BoseGases.chiSmallB M ℓ d u z = 0 →
      Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z = 0 := by
    intro z hz
    rw [Submission.BoseGases.w1Fibre]
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall (fun y => ?_))
    show Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) z y = 0
    rw [Submission.BoseGases.wSmallPair, hz]
    exact mul_eq_zero_of_left (zero_mul _) _
  have hpt : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
      (Φ x) ^ 2 * (∑ i : Fin n,
          Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
        ≤ (Φ x) ^ 2 * (Kf * C₀) := by
    filter_upwards [hcount] with x hx
    by_cases hΦ : Φ x = 0
    · rw [hΦ]; simp
    · have hsum : (∑ i : Fin n,
            Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
          ≤ Kf * (∑ i : Fin n,
              (Function.support (Submission.BoseGases.chiSmallB M ℓ d u)).indicator
                (fun _ => (1 : ℝ)) (x i)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum (fun i _ => ?_)
        by_cases hi : Submission.BoseGases.chiSmallB M ℓ d u (x i) = 0
        · rw [hzero (x i) hi,
            Set.indicator_of_notMem (by simpa [Function.mem_support] using hi)]
          simp
        · rw [Set.indicator_of_mem (Function.mem_support.mpr hi), mul_one]
          exact le_trans (le_abs_self _) (habs (x i))
      refine mul_le_mul_of_nonneg_left (le_trans hsum ?_) (sq_nonneg _)
      exact mul_le_mul_of_nonneg_left (hx hΦ) hKfnn
  have hint : Integrable (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 * (Kf * C₀))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)) :=
    (Work.BoseFixB1S.integrableOn_sq_abox hℓ hΦc).mul_const _
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _)
      (Finset.sum_nonneg (fun i _ => hnonneg (x i)))))
    hint hpt
  have hflat : Work.BoseFixB1.flatFibSum h M ℓ d u Φ
      = ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 * (∑ i : Fin n,
          Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)) :=
    rfl
  rw [hflat]
  calc ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 * (∑ i : Fin n,
          Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
      ≤ ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 * (Kf * C₀) := hmono
    _ = KfibC M * _root_.BoseGases.a v * C₀
          * ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 := by
        rw [MeasureTheory.integral_mul_const, hKf]
        ring

/-- `nCountB` is continuous in the configuration. -/
theorem continuous_nCountB (M : ℕ) (ℓ d : ℝ) (u : E3) {n : ℕ} :
    Continuous (fun x : Submission.BoseGases.X n => Work.BoseFixB1.nCountB M ℓ d u x) := by
  rw [show (fun x : Submission.BoseGases.X n => Work.BoseFixB1.nCountB M ℓ d u x)
      = fun x => ∑ i : Fin n, (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2 from rfl]
  exact continuous_finsetSum _ (fun i _ =>
    ((Work.BoseFixB1.continuous_chiSmallB M ℓ d u).comp (continuous_apply i)).pow 2)

/-- **The variance bound**: the a.e. count cap bounds the second moment of the smooth density. -/
theorem flatT2_le_of_chiCount {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) {u : E3} {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hcount : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
      Φ x ≠ 0 → (∑ i : Fin n,
        (Function.support (Submission.BoseGases.chiSmallB M ℓ d u)).indicator
          (fun _ => (1 : ℝ)) (x i)) ≤ C₀) :
    (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
        (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u) ^ 2)
      ≤ (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2 * C₀
          / Work.SmallBoxSliding.chiMass M ℓ d u
        * (Work.BoseFixB1.flatScountB M ℓ d u Φ / Work.SmallBoxSliding.chiMass M ℓ d u) := by
  set supχ2 : ℝ := (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2
    with hsup
  set κ : ℝ := Work.SmallBoxSliding.chiMass M ℓ d u with hκ
  have hsupnn : 0 ≤ supχ2 := by rw [hsup]; positivity
  have hκnn : 0 ≤ κ := by rw [hκ, Work.SmallBoxSliding.chiMass]; exact integral_nonneg (fun z => sq_nonneg _)
  have hpt : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
      (Φ x) ^ 2 * (Work.BoseFixB1.nCountB M ℓ d u x / κ) ^ 2
        ≤ (Φ x) ^ 2 * ((supχ2 * C₀ / κ) * (Work.BoseFixB1.nCountB M ℓ d u x / κ)) := by
    filter_upwards [hcount] with x hx
    by_cases hΦ : Φ x = 0
    · rw [hΦ]; simp
    · have hnc : Work.BoseFixB1.nCountB M ℓ d u x ≤ supχ2 * C₀ := by
        rw [Work.BoseFixB1.nCountB]
        calc ∑ i : Fin n, (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2
            ≤ ∑ i : Fin n, supχ2 *
                (Function.support (Submission.BoseGases.chiSmallB M ℓ d u)).indicator
                  (fun _ => (1 : ℝ)) (x i) := by
              refine Finset.sum_le_sum (fun i _ => ?_)
              rw [hsup]
              exact chi_sq_le_sup_mul_indicator hM (x i)
          _ = supχ2 * ∑ i : Fin n,
                (Function.support (Submission.BoseGases.chiSmallB M ℓ d u)).indicator
                  (fun _ => (1 : ℝ)) (x i) := by rw [Finset.mul_sum]
          _ ≤ supχ2 * C₀ := mul_le_mul_of_nonneg_left (hx hΦ) hsupnn
      have hncnn : 0 ≤ Work.BoseFixB1.nCountB M ℓ d u x := by
        rw [Work.BoseFixB1.nCountB]; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
      have h1 : Work.BoseFixB1.nCountB M ℓ d u x / κ ≤ (supχ2 * C₀) / κ :=
        div_le_div_of_nonneg_right hnc hκnn
      have h2 : (Work.BoseFixB1.nCountB M ℓ d u x / κ) * (Work.BoseFixB1.nCountB M ℓ d u x / κ)
          ≤ ((supχ2 * C₀) / κ) * (Work.BoseFixB1.nCountB M ℓ d u x / κ) :=
        mul_le_mul_of_nonneg_right h1 (div_nonneg hncnn hκnn)
      calc (Φ x) ^ 2 * (Work.BoseFixB1.nCountB M ℓ d u x / κ) ^ 2
          = (Φ x) ^ 2 * ((Work.BoseFixB1.nCountB M ℓ d u x / κ)
              * (Work.BoseFixB1.nCountB M ℓ d u x / κ)) := by ring
        _ ≤ (Φ x) ^ 2 * (((supχ2 * C₀) / κ) * (Work.BoseFixB1.nCountB M ℓ d u x / κ)) :=
            mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  have hcont : ContinuousOn (fun x : Submission.BoseGases.X n =>
      (Φ x) ^ 2 * ((supχ2 * C₀ / κ) * (Work.BoseFixB1.nCountB M ℓ d u x / κ)))
      (Submission.BoseGases.abox n ℓ) :=
    ((hΦc.pow 2).mul (continuous_const.mul
      ((continuous_nCountB M ℓ d u).div_const κ))).continuousOn
  have hint : Integrable (fun x : Submission.BoseGases.X n =>
      (Φ x) ^ 2 * ((supχ2 * C₀ / κ) * (Work.BoseFixB1.nCountB M ℓ d u x / κ)))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)) :=
    ContinuousOn.integrableOn_compact (Submission.BoseGases.abox_compact n hℓ) hcont
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))) hint hpt
  have hstep1 : (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
        ((supχ2 * C₀ / κ) * (Work.BoseFixB1.nCountB M ℓ d u x / κ)))
      = (supχ2 * C₀ / κ) * ∫ x in Submission.BoseGases.abox n ℓ,
          (Φ x) ^ 2 * (Work.BoseFixB1.nCountB M ℓ d u x / κ) := by
    rw [← MeasureTheory.integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))
  have hstep2 : (∫ x in Submission.BoseGases.abox n ℓ,
        (Φ x) ^ 2 * (Work.BoseFixB1.nCountB M ℓ d u x / κ))
      = Work.BoseFixB1.flatScountB M ℓ d u Φ / κ := by
    have h1 : (∫ x in Submission.BoseGases.abox n ℓ,
          (Φ x) ^ 2 * (Work.BoseFixB1.nCountB M ℓ d u x / κ))
        = (1 / κ) * ∫ x in Submission.BoseGases.abox n ℓ,
            (Φ x) ^ 2 * Work.BoseFixB1.nCountB M ℓ d u x := by
      rw [← MeasureTheory.integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))
    rw [h1, Work.BoseFixB1.flatScountB]
    ring
  rw [hstep1, hstep2] at hmono
  rw [hκ] at hmono
  calc (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
        (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u) ^ 2)
      ≤ (supχ2 * C₀ / Work.SmallBoxSliding.chiMass M ℓ d u)
          * (Work.BoseFixB1.flatScountB M ℓ d u Φ / Work.SmallBoxSliding.chiMass M ℓ d u) := hmono
    _ = (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2 * C₀
          / Work.SmallBoxSliding.chiMass M ℓ d u
        * (Work.BoseFixB1.flatScountB M ℓ d u Φ / Work.SmallBoxSliding.chiMass M ℓ d u) := by
        rw [hsup]

/-- **The arithmetic core of the hole row.**  With the three state-level inputs
`W₁ ≤ Cw·a·κ`, `Fv ≤ (supχ²·C₀/κ)·(τN)`, `Fs ≤ Kc·a·C₀·N` and the count cap `S ≤ supχ²·C₀·N`
the razor remainder `W₁N[μ(τ−μ)²/(8(τ+μ)) − μ²/2] + W₁Fvμ²/(2(τ+μ)²) + μFs` is at most
`(Cw·supχ²·C₀·(9/8) + Kc·C₀ + 1)·(a·μ·N)`. -/
theorem holeCapArith {W₁ τ μ N Fv Fs κ S a Cw supχ2 C₀ Kc : ℝ}
    (hμ : 0 < μ) (hN : 0 ≤ N) (hW : 0 ≤ W₁) (hκ : 0 ≤ κ) (hS : 0 ≤ S)
    (hFv : 0 ≤ Fv) (ha : 0 ≤ a) (hχ2 : 0 ≤ supχ2) (hC₀ : 0 ≤ C₀) (hCw : 0 ≤ Cw)
    (hKc : 0 ≤ Kc) (hτ : 0 ≤ τ)
    (hτN : τ * N ≤ (1 / κ) * S)
    (hSN : S ≤ supχ2 * C₀ * N)
    (hWle : W₁ ≤ Cw * a * κ)
    (hFvle : Fv ≤ supχ2 * C₀ / κ * (τ * N))
    (hFsle : Fs ≤ Kc * a * C₀ * N) :
    W₁ * N * (μ * (τ - μ) ^ 2 / (8 * (τ + μ)) - μ ^ 2 / 2)
      + W₁ * Fv * μ ^ 2 / (2 * (τ + μ) ^ 2) + μ * Fs
    ≤ (Cw * supχ2 * C₀ * (9 / 8) + Kc * C₀ + 1) * (a * μ * N) := by
  have hτμ : 0 < τ + μ := by linarith
  have hWκ : W₁ / κ ≤ Cw * a := by
    rcases eq_or_lt_of_le hκ with h0 | h0
    · rw [← h0, div_zero]; exact mul_nonneg hCw ha
    · rw [div_le_iff₀ h0]; nlinarith [hWle]
  have hscr : 0 ≤ supχ2 * C₀ := mul_nonneg hχ2 hC₀
  -- the bracket is bounded by `μτ/8`
  have hbracket : μ * (τ - μ) ^ 2 / (8 * (τ + μ)) - μ ^ 2 / 2 ≤ μ * τ / 8 := by
    have h1 : (0 : ℝ) < 8 * (τ + μ) := by linarith
    rw [div_sub_div _ _ h1.ne' (by norm_num : (2 : ℝ) ≠ 0),
      div_le_div_iff₀ (mul_pos h1 (by norm_num)) (by norm_num : (0 : ℝ) < 8)]
    nlinarith [hμ, hτ]
  -- term 1
  have hT1 : W₁ * N * (μ * (τ - μ) ^ 2 / (8 * (τ + μ)) - μ ^ 2 / 2)
      ≤ Cw * supχ2 * C₀ * (1 / 8) * (a * μ * N) := by
    have h1 : W₁ * N * (μ * (τ - μ) ^ 2 / (8 * (τ + μ)) - μ ^ 2 / 2)
        ≤ W₁ / 8 * μ * (τ * N) := by
      have he : W₁ * N * (μ * τ / 8) = W₁ / 8 * μ * (τ * N) := by ring
      rw [← he]
      refine mul_le_mul_of_nonneg_left hbracket ?_
      exact mul_nonneg hW hN
    have h3 : W₁ / 8 * μ * (τ * N) ≤ W₁ / 8 * μ * ((1 / κ) * S) := by
      refine mul_le_mul_of_nonneg_left hτN ?_
      positivity
    have h4 : W₁ / 8 * μ * ((1 / κ) * S) ≤ Cw * a * μ * S / 8 := by
      have he : W₁ / 8 * μ * ((1 / κ) * S) = (W₁ / κ) * (μ * S / 8) := by ring
      have he2 : Cw * a * μ * S / 8 = (Cw * a) * (μ * S / 8) := by ring
      rw [he, he2]
      exact mul_le_mul_of_nonneg_right hWκ (by positivity)
    have h6 : Cw * a * μ * S / 8 ≤ Cw * supχ2 * C₀ * (1 / 8) * (a * μ * N) := by
      have he : Cw * a * μ * S / 8 = (Cw * a * μ / 8) * S := by ring
      have he2 : Cw * supχ2 * C₀ * (1 / 8) * (a * μ * N) = (Cw * a * μ / 8) * (supχ2 * C₀ * N) := by
        ring
      rw [he, he2]
      exact mul_le_mul_of_nonneg_left hSN (by positivity)
    linarith [h1, h3, h4, h6]
  -- term 2
  have hT2 : W₁ * Fv * μ ^ 2 / (2 * (τ + μ) ^ 2) ≤ Cw * supχ2 * C₀ * (1 / 2) * (a * μ * N) := by
    have h1 : W₁ * Fv * μ ^ 2 / (2 * (τ + μ) ^ 2)
        ≤ W₁ / κ * (supχ2 * C₀) * (μ ^ 2 * (τ * N) / (2 * (τ + μ) ^ 2)) := by
      have he : W₁ * Fv * μ ^ 2 / (2 * (τ + μ) ^ 2)
          = Fv * (W₁ * μ ^ 2 / (2 * (τ + μ) ^ 2)) := by ring
      have he2 : W₁ / κ * (supχ2 * C₀) * (μ ^ 2 * (τ * N) / (2 * (τ + μ) ^ 2))
          = (supχ2 * C₀ / κ * (τ * N)) * (W₁ * μ ^ 2 / (2 * (τ + μ) ^ 2)) := by ring
      rw [he, he2]
      exact mul_le_mul_of_nonneg_right hFvle (by positivity)
    have h3 : μ ^ 2 * (τ * N) / (2 * (τ + μ) ^ 2) ≤ μ * N / 2 := by
      have hbase : μ ^ 2 * τ ≤ μ * (τ + μ) ^ 2 := by nlinarith [hμ, hτ, sq_nonneg τ]
      have h4 := mul_le_mul_of_nonneg_right hbase hN
      rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
      nlinarith [h4]
    have h5 : W₁ / κ * (supχ2 * C₀) * (μ * N / 2) ≤ Cw * supχ2 * C₀ * (1 / 2) * (a * μ * N) := by
      have he : W₁ / κ * (supχ2 * C₀) * (μ * N / 2) = W₁ / κ * (supχ2 * C₀ * (μ * N / 2)) := by ring
      have he2 : Cw * supχ2 * C₀ * (1 / 2) * (a * μ * N) = (Cw * a) * (supχ2 * C₀ * (μ * N / 2)) := by
        ring
      rw [he, he2]
      exact mul_le_mul_of_nonneg_right hWκ (by positivity)
    have h4 : W₁ / κ * (supχ2 * C₀) * (μ ^ 2 * (τ * N) / (2 * (τ + μ) ^ 2))
        ≤ W₁ / κ * (supχ2 * C₀) * (μ * N / 2) :=
      mul_le_mul_of_nonneg_left h3 (mul_nonneg (div_nonneg hW hκ) hscr)
    linarith [h1, h4, h5]
  have hT3 : μ * Fs ≤ Kc * C₀ * (a * μ * N) := by
    have h1 : μ * Fs ≤ μ * (Kc * a * C₀ * N) := mul_le_mul_of_nonneg_left hFsle hμ.le
    have h2 : μ * (Kc * a * C₀ * N) = Kc * C₀ * (a * μ * N) := by ring
    linarith [h1, h2.le, h2.ge]
  have htot : W₁ * N * (μ * (τ - μ) ^ 2 / (8 * (τ + μ)) - μ ^ 2 / 2)
      + W₁ * Fv * μ ^ 2 / (2 * (τ + μ) ^ 2) + μ * Fs
      ≤ (Cw * supχ2 * C₀ * (1 / 8) + Cw * supχ2 * C₀ * (1 / 2) + Kc * C₀) * (a * μ * N) := by
    nlinarith [hT1, hT2, hT3]
  have hconst : (Cw * supχ2 * C₀ * (1 / 8) + Cw * supχ2 * C₀ * (1 / 2) + Kc * C₀) * (a * μ * N)
      ≤ (Cw * supχ2 * C₀ * (9 / 8) + Kc * C₀ + 1) * (a * μ * N) := by
    have h1 : Cw * supχ2 * C₀ * (1 / 8) + Cw * supχ2 * C₀ * (1 / 2) + Kc * C₀
        ≤ Cw * supχ2 * C₀ * (9 / 8) + Kc * C₀ + 1 := by
      have h5 : 0 ≤ Cw * supχ2 * C₀ * (5 / 8) := by positivity
      nlinarith [h5]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  linarith [htot, hconst]

/-- `tBdiagFormInd` is nonnegative when the symbol is. -/
theorem tBdiagFormInd_nonneg' {a : ℝ} (ha : 0 < a) {A : Set E3} {volA : ℝ} (χ : E3 → ℝ)
    {F : ℝ → ℝ} (hF : ∀ r : ℝ, 0 ≤ F r) {N : ℕ} (Ψ : Submission.BoseGases.X N → ℝ) :
    0 ≤ Work.UBBInputs8.tBdiagFormInd a A volA χ F Ψ := by
  rw [Work.UBBInputs8.tBdiagFormInd]
  refine Finset.sum_nonneg (fun i _ => ?_)
  refine mul_nonneg (by positivity) ?_
  refine integral_nonneg (fun p => ?_)
  refine mul_nonneg (hF ‖p‖) ?_
  refine mul_nonneg (by positivity) ?_
  exact integral_nonneg (fun x => sq_nonneg _)

/-- If `∫ Φ² = 0` then `Φ` vanishes a.e. -/
theorem ae_zero_of_sq_integral_eq_zero {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ)
    (h : ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 = 0) :
    Φ =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)] 0 := by
  have h1 : (fun x : Submission.BoseGases.X n => (Φ x) ^ 2)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg (f := fun x => (Φ x) ^ 2)
      (fun x => sq_nonneg _) (Work.BoseFixB1S.integrableOn_sq_abox hℓ hΦc)).mp h
  filter_upwards [h1] with x hx
  exact pow_eq_zero_iff (by norm_num : (1 : ℕ) ≠ 0) |>.mp (by simpa using hx)

theorem flatFibSum_eq_zero_of_ae_zero {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {M : ℕ} {ℓ d : ℝ}
    (u : E3) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (hae : Φ =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)] 0) :
    Work.BoseFixB1.flatFibSum h M ℓ d u Φ = 0 := by
  rw [Work.BoseFixB1.flatFibSum]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hae] with x hx
  have hx0 : Φ x = 0 := hx
  rw [hx0]; simp

theorem flatScountB_eq_zero_of_ae_zero {M : ℕ} {ℓ d : ℝ} (u : E3) {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ}
    (hae : Φ =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)] 0) :
    Work.BoseFixB1.flatScountB M ℓ d u Φ = 0 := by
  rw [Work.BoseFixB1.flatScountB]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hae] with x hx
  have hx0 : Φ x = 0 := hx
  rw [hx0]; simp

theorem flatT2_eq_zero_of_ae_zero {v : E3 → ℝ} {μ : ℝ} {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (u : E3)
    (hae : Φ =ᵐ[MeasureTheory.volume.restrict
      (Submission.BoseGases.abox n (Work.BoseFixB1.pL v μ))] 0) :
    Work.BoseFixB1.Up.flatT2 v μ Φ u = 0 := by
  rw [Work.BoseFixB1.Up.flatT2]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hae] with x hx
  have hx0 : Φ x = 0 := hx
  rw [hx0]; simp

/-- **The target from the `χ`-count cap.** -/
theorem cubeHoleCapRow_of_chiCount {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v)
    (hcap : CubeHoleChiCount v h R) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : E3),
          u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) μ →
          ‖((Work.BoseFixB1.pL v μ) * (Work.BoseFixB1.pD v μ)) • u‖
              < (Work.BoseFixB1.pL v μ) / 2
                + (Work.BoseFixB1.pL v μ) * (Work.BoseFixB1.pD v μ) / 2 →
          Work.BoseFixB1.flatPairSum v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ≤ 0 →
          (1 / 2) * Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u
              * (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                    (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ^ 2
                  * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
                + Work.BoseFixB1.Up.flatVar v μ (Φ : Submission.BoseGases.X n → ℝ) u)
            - μ * Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u
                * Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                    (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
                * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
            + μ * Work.BoseFixB1.flatFibSum h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
          ≤ Work.UBBInputs8.tBdiagFormInd (Work.BoseFixB1.pL v μ)
                (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                (Submission.BoseGases.chiSmallB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u)
                (fun r : ℝ => r ^ 2) (Φ : Submission.BoseGases.X n → ℝ)
            + C * Work.BoseFixB1.Up.flatErrB v R μ (Φ : Submission.BoseGases.X n → ℝ) u
            + Work.BoseFixB1.Up.flatSlackB v h μ (Φ : Submission.BoseGases.X n → ℝ) u
            + μ * (_root_.BoseGases.a v)
                * (Work.BoseFixB1S.boxQCount
                      (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                      (Work.BoseFixB1.pL v μ)
                      (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                      (Φ : Submission.BoseGases.X n → ℝ)
                  + Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)) := by
  obtain ⟨ε₁, C₀, hε₁, hC₀, hbody⟩ := hcap
  obtain ⟨ε₂, Cw, hε₂, hCw, hWreg⟩ :=
    Work.BoseFixB1.w1MassB_le_const_mul_chiMass_regime (v := v) h hv hvrad hR hv_supp
  obtain ⟨ε₃, hε₃, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  set supχ2 : ℝ := (Submission.BoseGases.chiSupAbs *
      Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue) ^ 2 with hsupχ2def
  have hsupχ2nn : 0 ≤ supχ2 := by rw [hsupχ2def]; positivity
  set Kc : ℝ := KfibC Work.BoseBox.mValue with hKcdef
  have hKcnn : 0 ≤ Kc := by rw [hKcdef]; exact KfibC_nonneg _
  set Cval : ℝ := Cw * supχ2 * C₀ * (9 / 8) + Kc * C₀ + 1 with hCvaldef
  have hCvalnn : 0 ≤ Cval := by rw [hCvaldef]; positivity
  refine ⟨min ε₁ (min ε₂ ε₃), Cval, by positivity, hCvalnn, ?_⟩
  intro μ hAdm n Φ u hu hcorner hpair
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have hℓ : 0 < Work.BoseFixB1.pL v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < Work.BoseFixB1.pD v μ := Work.BoseFixB1.adm_d_pos hAdm
  have ha : 0 < _root_.BoseGases.a v := Work.BoseFixB1.adm_a_pos hAdm
  have hM1 : 1 ≤ Work.BoseFixB1.pM v μ := by
    simp only [Work.BoseFixB1.pM]; rw [Work.BoseFixB1.M_eq_mValue]
    norm_num [Work.BoseBox.mValue]
  have hAdm₁ : Work.BoseBoxFix.Adm v ε₁ μ :=
    ⟨hAdm.1, le_trans hAdm.2.1 (min_le_left _ _), hAdm.2.2⟩
  have hAdm₂ : Work.BoseBoxFix.Adm v ε₂ μ :=
    ⟨hAdm.1, le_trans hAdm.2.1 (le_trans (min_le_right _ _) (min_le_left _ _)), hAdm.2.2⟩
  have hAdm₃ : Work.BoseBoxFix.Adm v ε₃ μ :=
    ⟨hAdm.1, le_trans hAdm.2.1 (le_trans (min_le_right _ _) (min_le_right _ _)), hAdm.2.2⟩
  obtain ⟨h16, hχ⟩ := hreg μ hμ hAdm₃.2.1
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  have hMeq : Work.BoseFixB1.pM v μ = Work.BoseBox.mValue := by
    simp only [Work.BoseFixB1.pM]; exact Work.BoseFixB1.M_eq_mValue μ (_root_.BoseGases.a v)
  -- the local abbreviations
  set W₁ : ℝ := Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
    (Work.BoseFixB1.pD v μ) u with hW₁def
  set τ : ℝ := Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
    (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) with hτdef
  set Nr : ℝ := Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) with hNrdef
  set Fv : ℝ := Work.BoseFixB1.Up.flatVar v μ (Φ : Submission.BoseGases.X n → ℝ) u with hFvdef
  set Fs : ℝ := Work.BoseFixB1.flatFibSum h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
    (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) with hFsdef
  set Sχ : ℝ := Work.BoseFixB1.flatScountB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
    (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) with hSχdef
  set κχ : ℝ := Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
    (Work.BoseFixB1.pD v μ) u with hκχdef
  set er : ℝ := Work.BoseFixB1.Up.flatErrB v R μ (Φ : Submission.BoseGases.X n → ℝ) u with herdef
  set sl : ℝ := Work.BoseFixB1.Up.flatSlackB v h μ (Φ : Submission.BoseGases.X n → ℝ) u with hsldef
  set Dχ : ℝ := Work.UBBInputs8.tBdiagFormInd (Work.BoseFixB1.pL v μ)
    (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
    (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
    (Submission.BoseGases.chiSmallB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) u) (fun r : ℝ => r ^ 2) (Φ : Submission.BoseGases.X n → ℝ) with hDχdef
  set Qχ : ℝ := Work.BoseFixB1S.boxQCount
    (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
    (Work.BoseFixB1.pL v μ)
    (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
    (Φ : Submission.BoseGases.X n → ℝ) with hQχdef
  -- the count cap
  have hcount := hbody μ hAdm₁ n Φ u hu hcorner hpair
  -- state-level bounds
  have hSle : Sχ ≤ supχ2 * C₀ * Nr := by
    have h1 := scount_le_of_chiCount (M := Work.BoseFixB1.pM v μ) hM1 hℓ hΦc hC₀ hcount
    rw [hSχdef, hNrdef, hsupχ2def, hMeq]
    exact h1
  have hFsle : Fs ≤ Kc * _root_.BoseGases.a v * C₀ * Nr := by
    have h1 := fibSum_le_of_chiCount (v := v) h hv hvrad hR hv_supp (M := Work.BoseFixB1.pM v μ)
      hM1 hℓ hd h16 hχ u hΦc hC₀ ha.le hcount
    rw [hFsdef, hNrdef, hKcdef, hMeq]
    exact h1
  have hWle : W₁ ≤ Cw * _root_.BoseGases.a v * κχ := by
    have h1 := hWreg μ hAdm₂ u
    rw [hW₁def, hκχdef, hMeq]
    exact h1
  have hSnn : 0 ≤ Sχ := by
    rw [hSχdef, Work.BoseFixB1.flatScountB]
    exact integral_nonneg (fun x => mul_nonneg (sq_nonneg _)
      (by rw [Work.BoseFixB1.nCountB]; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)))
  have hκnn : 0 ≤ κχ := by
    rw [hκχdef, Work.SmallBoxSliding.chiMass]
    exact integral_nonneg (fun z => sq_nonneg _)
  have hWnn : 0 ≤ W₁ := by
    rw [hW₁def]
    exact Work.BoseFixB1.w1MassB_nonneg h hv hvrad hR hv_supp hℓ hd u
  have hNnn : 0 ≤ Nr := by rw [hNrdef]; exact Work.BoseFixB1.normB_nonneg _
  have hFvnn : 0 ≤ Fv := by
    by_cases hN0 : Nr = 0
    · have hae := ae_zero_of_sq_integral_eq_zero (ℓ := Work.BoseFixB1.pL v μ) hℓ hΦc
        (by show Nr = 0; exact hN0)
      have h1 := flatT2_eq_zero_of_ae_zero (v := v) (μ := μ) u hae
      have h2 : Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) = 0 := by
        rw [Work.BoseFixB1.flatTau]
        have hm : Work.BoseFixB1.flatMass (Work.BoseFixB1.pL v μ)
            (Φ : Submission.BoseGases.X n → ℝ) = 0 := hN0
        rw [hm]; ring
      rw [hFvdef, Work.BoseFixB1.Up.flatVar, h1, h2]
      have h0 : Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) = Nr := hNrdef.symm
      rw [h0]; norm_num
    · rw [hFvdef]
      exact Work.BoseFixB1.Up.flatVar_nonneg hΦc
        (lt_of_le_of_ne hNnn (Ne.symm hN0)) u
  have hτnn : 0 ≤ τ := by
    rw [hτdef, Work.BoseFixB1.flatTau]
    exact div_nonneg hSnn (mul_nonneg hκnn hNnn)
  have hAe : Nr = 0 → Φ =ᵐ[MeasureTheory.volume.restrict
      (Submission.BoseGases.abox n (Work.BoseFixB1.pL v μ))] 0 := by
    intro h0
    exact ae_zero_of_sq_integral_eq_zero hℓ hΦc (by show Nr = 0; exact h0)
  have hτNeq : τ * Nr = (1 / κχ) * Sχ := by
    by_cases hN0 : Nr = 0
    · have hS0 := flatScountB_eq_zero_of_ae_zero (M := Work.BoseFixB1.pM v μ)
        (ℓ := Work.BoseFixB1.pL v μ) (d := Work.BoseFixB1.pD v μ) u (hAe hN0)
      rw [hN0, mul_zero, hSχdef, hS0]; ring
    · rw [hτdef, Work.BoseFixB1.flatTau, hSχdef, hκχdef, hNrdef]
      have hMx2 : Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
          = Work.BoseFixB1.flatMass (Work.BoseFixB1.pL v μ)
              (Φ : Submission.BoseGases.X n → ℝ) := rfl
      rw [hMx2]
      have hMx : Work.BoseFixB1.flatMass (Work.BoseFixB1.pL v μ)
          (Φ : Submission.BoseGases.X n → ℝ) ≠ 0 := by
        rw [← hMx2, ← hNrdef]; exact hN0
      by_cases hκ0 : Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ)
          (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u = 0
      · rw [hκ0]; ring
      · field_simp
  have hFvle : Fv ≤ supχ2 * C₀ / κχ * (τ * Nr) := by
    have h1 := flatT2_le_of_chiCount (M := Work.BoseFixB1.pM v μ) hM1 hℓ hΦc hC₀ hcount
    have hsupχ2eq : (Submission.BoseGases.chiSupAbs *
        Submission.BoseGases.chiSmallDecay (Work.BoseFixB1.pM v μ)) ^ 2 = supχ2 := by
      rw [hsupχ2def, hMeq]
    rw [hsupχ2eq] at h1
    have h2 : Fv ≤ Work.BoseFixB1.Up.flatT2 v μ (Φ : Submission.BoseGases.X n → ℝ) u := by
      rw [hFvdef, Work.BoseFixB1.Up.flatVar]
      have h3 : 0 ≤ Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ^ 2
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) :=
        mul_nonneg (sq_nonneg _) (by rw [← hNrdef]; exact hNnn)
      linarith
    have h4 : Work.BoseFixB1.Up.flatT2 v μ (Φ : Submission.BoseGases.X n → ℝ) u
        = ∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.pL v μ), (Φ x) ^ 2 *
            (Work.BoseFixB1.nCountB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u x / Work.SmallBoxSliding.chiMass
                (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u) ^ 2 :=
      rfl
    have h5 : Work.BoseFixB1.Up.flatT2 v μ (Φ : Submission.BoseGases.X n → ℝ) u
        ≤ (supχ2 * C₀ / κχ) * (τ * Nr) := by
      have h6 : Work.BoseFixB1.flatScountB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
            / Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u = τ * Nr := by
        rw [hτNeq, hκχdef, hSχdef]; ring
      have h7 : (supχ2 * C₀ / κχ) * (τ * Nr)
          = (supχ2 * C₀) / Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ)
              (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u
            * (Work.BoseFixB1.flatScountB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
              / Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u) := by
        rw [hκχdef, ← h6]
      rw [h4, h7]
      exact h1
    exact le_trans h2 h5
  have hident : ((1 / 2) * W₁ * (τ ^ 2 * Nr + Fv) - μ * W₁ * τ * Nr + μ * Fs) - sl
      = W₁ * (Nr * (μ * (τ - μ) ^ 2 / (8 * (τ + μ)) - μ ^ 2 / 2)
          + Fv * μ ^ 2 / (2 * (τ + μ) ^ 2)) + μ * Fs := by
    have h1 := flatDemand_sub_slack W₁ τ μ Nr Fv Fs (by positivity : τ + μ ≠ 0)
    have hslack : sl = W₁ * ((τ - μ) ^ 2 * Nr * (1 / 2 - (1 / 8) * μ / (τ + μ))
        + Fv * (1 / 2 - 4 * (1 / 8) * μ ^ 2 / (τ + μ) ^ 2)) := by
      rw [hsldef]; rfl
    rwa [← hslack] at h1
  have harith := holeCapArith (W₁ := W₁) (τ := τ) (μ := μ) (N := Nr) (Fv := Fv) (Fs := Fs)
    (κ := κχ) (S := Sχ) (a := _root_.BoseGases.a v) (Cw := Cw) (supχ2 := supχ2) (C₀ := C₀)
    (Kc := Kc) hμ hNnn hWnn hκnn hSnn hFvnn ha.le hsupχ2nn hC₀ hCw hKcnn hτnn hτNeq.le hSle hWle
    hFvle hFsle
  have hCval : Cw * supχ2 * C₀ * (9 / 8) + Kc * C₀ + 1 = Cval := by rw [hCvaldef]
  rw [hCval] at harith
  -- the error bracket dominates `a·μ·N`
  have her_ge : _root_.BoseGases.a v * μ * Nr ≤ er := by
    rw [herdef, Work.BoseFixB1.Up.flatErrB]
    have hKB : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 := by
      refine pow_nonneg ?_ 3
      show 0 ≤ Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-6)
      exact Work.BoseBox.fsXp_nonneg (by positivity)
    have hprod : 0 ≤ μ ^ 2 * (_root_.BoseGases.a v) *
        ((R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v) *
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
          + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
            * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) *
        Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
      refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) ha.le) ?_) ?_) ?_
      · exact add_nonneg (sq_nonneg _) (mul_nonneg hKB (Real.rpow_nonneg (by positivity) _))
      · exact hκnn
      · exact hNnn
    linarith [hprod]
  have her0 : 0 ≤ er := le_trans (mul_nonneg (mul_nonneg ha.le hμ.le) hNnn) her_ge
  have hCval1 : 1 ≤ Cval := by
    rw [hCvaldef]
    have h0 : 0 ≤ Cw * supχ2 * C₀ * (9 / 8) + Kc * C₀ := by positivity
    linarith
  have hCe : _root_.BoseGases.a v * μ * Nr ≤ Cval * er := by
    have h1 : (1 : ℝ) * er ≤ Cval * er := mul_le_mul_of_nonneg_right hCval1 her0
    linarith [her_ge, h1]
  have hDnn : 0 ≤ Dχ := by
    rw [hDχdef]
    exact tBdiagFormInd_nonneg' hℓ _ (fun r => sq_nonneg r) _
  have hQnn : 0 ≤ Qχ := by
    rw [hQχdef]
    exact Work.BoseFixB1S.boxQCount_nonneg _ _ _ _
  have hgoal : (1 / 2) * W₁ * (τ ^ 2 * Nr + Fv) - μ * W₁ * τ * Nr + μ * Fs
      ≤ Dχ + Cval * er + sl + μ * (_root_.BoseGases.a v) * (Qχ + Nr) := by
    have h4 : μ * (_root_.BoseGases.a v) * (Qχ + Nr) ≥ 0 := by
      refine mul_nonneg (mul_nonneg hμ.le ha.le) (add_nonneg hQnn hNnn)
    have hident' : ((1 / 2) * W₁ * (τ ^ 2 * Nr + Fv) - μ * W₁ * τ * Nr + μ * Fs) - sl
        = W₁ * Nr * (μ * (τ - μ) ^ 2 / (8 * (τ + μ)) - μ ^ 2 / 2)
          + W₁ * Fv * μ ^ 2 / (2 * (τ + μ) ^ 2) + μ * Fs := by
      rw [hident]; ring
    have hT : W₁ * Nr * (μ * (τ - μ) ^ 2 / (8 * (τ + μ)) - μ ^ 2 / 2)
        + W₁ * Fv * μ ^ 2 / (2 * (τ + μ) ^ 2) + μ * Fs ≤ Cval * er :=
      le_trans harith (mul_le_mul_of_nonneg_left her_ge hCvalnn)
    linarith [hident', hT, hDnn, h4]
  exact hgoal

/-- **The diluteness identity of the razor.**  At FS's parameters, `μ·(a v)·(ℓ·d)²` is the ninth
power of the small parameter `X = (μ(a v)³)^{1/323}`.  This is the comparison that makes the tiny
slots (`μ(a v)(ℓd)² = X⁹ → 0`) usable, and it is the numerical input any consumer of
`cubeHoleCapRow_of_chiCount` needs (e.g. to pay the `Q`-half of the Dirichlet row through the
PROVED `Work.BoseB1Cube.cubeHoleQContent_le_dirichlet`: `4·μ(a v)(ℓd)²·gradConst² ≤ 1` for small
diluteness, since `X⁹ → 0`). -/
theorem mu_av_mul_pL_pD_sq {v : E3 → ℝ} {μ : ℝ} (hμ : 0 < μ)
    (hav : 0 < _root_.BoseGases.a v) :
    μ * (_root_.BoseGases.a v) * (Work.BoseFixB1.pL v μ * Work.BoseFixB1.pD v μ) ^ 2
      = Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 9 := by
  have ha := hav
  have hμa : 0 < μ * _root_.BoseGases.a v := mul_pos hμ ha
  have ht : 0 < μ * (_root_.BoseGases.a v) ^ 3 := by positivity
  -- unfold `pL`, `pD` and `paramsAt`
  have hL : Work.BoseFixB1.pL v μ
      = Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-(3 / 2 : ℝ))
        * (μ * (_root_.BoseGases.a v)) ^ (-(1 / 2 : ℝ)) := rfl
  have hD : Work.BoseFixB1.pD v μ = Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 6 := rfl
  -- `(μa)^{-1/2})^2 = (μa)^{-1}`
  have hsq : ((μ * _root_.BoseGases.a v) ^ (-(1 / 2 : ℝ))) ^ 2 = (μ * _root_.BoseGases.a v)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hμa.le,
      show (-(1 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  -- `Kl^2 · d^2 = X^9`
  have hKl : (Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-(3 / 2 : ℝ))) ^ 2
      = Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-3) := by
    rw [← Real.rpow_natCast, Work.BoseBox.fsXp_rpow ht.le (-(3 / 2 : ℝ)) ((2 : ℕ) : ℝ)]
    congr 1
    norm_num
  have hd : (Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 6) ^ 2
      = Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 12 := by
    rw [← Real.rpow_natCast, Work.BoseBox.fsXp_rpow ht.le 6 ((2 : ℕ) : ℝ)]
    congr 1
    norm_num
  have hprod : Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-3)
      * Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 12
      = Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 9 := by
    rw [Work.BoseBox.fsXp_mul ht]
    congr 1
    norm_num
  have hfin : μ * _root_.BoseGases.a v
      * (Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-3)
          * (μ * _root_.BoseGases.a v)⁻¹
          * Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 12)
      = Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-3)
        * Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 12 := by
    field_simp
  rw [hL, hD, mul_pow, mul_pow, hsq, hKl, hd, hfin, hprod]

/-- **The excited (`Q`) half of the Dirichlet row is paid by the slot Dirichlet word.**  From the
PROVED `cubeHoleQContent_le_dirichlet` (`Σᵢ∫(χ·Q_{B,i}Ind Φ)² ≤ 4(ℓd)²gradConst²·D`) and the
diluteness identity `μ(a v)(ℓd)² = X⁹` (`mu_av_mul_pL_pD_sq`), the whole excited χ-content is paid
by `D` — with the razor margin `4μ(a v)(ℓd)²gradConst² = 4X⁹gradConst² ≤ 1`.

Hence in the residual `(DROW)` of `FINDING_cubeHoleCapRow_session3.md` §4 only the **flat** half of
`Sχ = χ`-content (and the cross term, which reduces to it by Cauchy–Schwarz) is still missing. -/
theorem qHalf_le_dirichlet {v : E3 → ℝ} {μ : ℝ} {n : ℕ} (hμ : 0 < μ)
    (hav : 0 < _root_.BoseGases.a v) (hℓ : 0 < Work.BoseFixB1.pL v μ)
    (hd : 0 < Work.BoseFixB1.pD v μ)
    (hdil : Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 9
      * (4 * Work.Analysis.HoleVoidCost.gradConst ^ 2) ≤ 1)
    {u : E3} {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    μ * (_root_.BoseGases.a v) * (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n
        (Work.BoseFixB1.pL v μ),
        (Submission.BoseGases.chiSmallB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u (x i)
          * Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u)
              (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
              i Φ x) ^ 2)
      ≤ Work.UBBInputs8.tBdiagFormInd (Work.BoseFixB1.pL v μ)
          (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
          (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
          (Submission.BoseGases.chiSmallB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u) (fun r : ℝ => r ^ 2) Φ := by
  have hM4 : 4 ≤ Work.BoseFixB1.pM v μ := by
    simp only [Work.BoseFixB1.pM]
    rw [Work.BoseFixB1.M_eq_mValue]
    norm_num [Work.BoseBox.mValue]
  have hQ := cubeHoleQContent_le_dirichlet (M := Work.BoseFixB1.pM v μ) hℓ hd u hM4 hΦ
  have hDnn : 0 ≤ Work.UBBInputs8.tBdiagFormInd (Work.BoseFixB1.pL v μ)
      (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
      (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
      (Submission.BoseGases.chiSmallB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
        (Work.BoseFixB1.pD v μ) u) (fun r : ℝ => r ^ 2) Φ :=
    tBdiagFormInd_nonneg' hℓ _ (fun r => sq_nonneg r) _
  have hkey : μ * (_root_.BoseGases.a v)
        * (4 * (Work.BoseFixB1.pL v μ * Work.BoseFixB1.pD v μ) ^ 2
            * Work.Analysis.HoleVoidCost.gradConst ^ 2) ≤ 1 := by
    rw [show μ * (_root_.BoseGases.a v)
          * (4 * (Work.BoseFixB1.pL v μ * Work.BoseFixB1.pD v μ) ^ 2
              * Work.Analysis.HoleVoidCost.gradConst ^ 2)
        = (μ * (_root_.BoseGases.a v) * (Work.BoseFixB1.pL v μ * Work.BoseFixB1.pD v μ) ^ 2)
          * (4 * Work.Analysis.HoleVoidCost.gradConst ^ 2) by ring,
        mu_av_mul_pL_pD_sq hμ hav]
    exact hdil
  calc μ * (_root_.BoseGases.a v) * (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n
          (Work.BoseFixB1.pL v μ),
          (Submission.BoseGases.chiSmallB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u (x i)
            * Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u)
                (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                i Φ x) ^ 2)
      ≤ μ * (_root_.BoseGases.a v)
          * (4 * (Work.BoseFixB1.pL v μ * Work.BoseFixB1.pD v μ) ^ 2
              * Work.Analysis.HoleVoidCost.gradConst ^ 2
              * Work.UBBInputs8.tBdiagFormInd (Work.BoseFixB1.pL v μ)
                  (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                  (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                  (Submission.BoseGases.chiSmallB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                    (Work.BoseFixB1.pD v μ) u) (fun r : ℝ => r ^ 2) Φ) :=
        mul_le_mul_of_nonneg_left hQ (by positivity)
    _ = (μ * (_root_.BoseGases.a v)
          * (4 * (Work.BoseFixB1.pL v μ * Work.BoseFixB1.pD v μ) ^ 2
              * Work.Analysis.HoleVoidCost.gradConst ^ 2))
        * Work.UBBInputs8.tBdiagFormInd (Work.BoseFixB1.pL v μ)
            (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
            (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
            (Submission.BoseGases.chiSmallB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u) (fun r : ℝ => r ^ 2) Φ := by ring
    _ ≤ 1 * Work.UBBInputs8.tBdiagFormInd (Work.BoseFixB1.pL v μ)
            (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
            (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
            (Submission.BoseGases.chiSmallB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u) (fun r : ℝ => r ^ 2) Φ :=
        mul_le_mul_of_nonneg_right hkey hDnn
    _ = Work.UBBInputs8.tBdiagFormInd (Work.BoseFixB1.pL v μ)
            (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
            (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
            (Submission.BoseGases.chiSmallB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u) (fun r : ℝ => r ^ 2) Φ := one_mul _

/-- **The target when the zero set of `v` is null** (the "hard-core" / positive-bump case):
then pair-deadness forces at most one particle into the support of the cutoff, so the `χ`-count cap
holds with `C₀ = 1`, and the ledger of `cubeHoleCapRow_of_chiCount` applies. -/
theorem cubeHoleCapRow_of_nullZero {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v)
    (hZ : (MeasureTheory.volume : MeasureTheory.Measure E3) {z : E3 | v z = 0} = 0) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : E3),
          u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) μ →
          ‖((Work.BoseFixB1.pL v μ) * (Work.BoseFixB1.pD v μ)) • u‖
              < (Work.BoseFixB1.pL v μ) / 2
                + (Work.BoseFixB1.pL v μ) * (Work.BoseFixB1.pD v μ) / 2 →
          Work.BoseFixB1.flatPairSum v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ≤ 0 →
          (1 / 2) * Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u
              * (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                    (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ^ 2
                  * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
                + Work.BoseFixB1.Up.flatVar v μ (Φ : Submission.BoseGases.X n → ℝ) u)
            - μ * Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u
                * Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                    (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
                * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
            + μ * Work.BoseFixB1.flatFibSum h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
          ≤ Work.UBBInputs8.tBdiagFormInd (Work.BoseFixB1.pL v μ)
                (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                (Submission.BoseGases.chiSmallB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u)
                (fun r : ℝ => r ^ 2) (Φ : Submission.BoseGases.X n → ℝ)
            + C * Work.BoseFixB1.Up.flatErrB v R μ (Φ : Submission.BoseGases.X n → ℝ) u
            + Work.BoseFixB1.Up.flatSlackB v h μ (Φ : Submission.BoseGases.X n → ℝ) u
            + μ * (_root_.BoseGases.a v)
                * (Work.BoseFixB1S.boxQCount
                      (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                      (Work.BoseFixB1.pL v μ)
                      (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                      (Φ : Submission.BoseGases.X n → ℝ)
                  + Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)) :=
  cubeHoleCapRow_of_chiCount h hv hv1 hvrad hR hv_supp hav
    (cubeHoleChiCount_of_nullZero h hv hv1 hvrad hR hv_supp hav hZ)



/-! ### The pair-row residual: the target's content in the flat-ledger budget form

`CubeHolePairRow` below is the target with two **monotone** replacements on the left
(`w1MassB ↦ flatPairMass ≥ w1MassB`, and the row `−flatPairSum ≥ 0` kept in) and the two
nonnegative rows `D = tBdiagFormInd` and `μ(a v)·normB` deleted from the right.  It is therefore
*strictly stronger* than the target, and `cubeHoleCapRow_of_pairRow` below proves that the target
follows from it.  Conversely it is *exactly* the row the corpus's flat ledger produces: in the
budget `hbud` of `Work.BoseFixB1.Up.perBoxF_of_ledger_kin` (resp.
`Work.BoseFixB1S.perBoxF_of_ledger_kin`) the two deviation slots, instantiated at their tight values

    Efib  := μ·flatFibSum − μ·W₁·τ·‖Φ‖² ,     Epair := ½·flatPairMass·(τ²‖Φ‖² + flatVar) − flatPairSum

make the fibre row `hfib` and the pair row `hpair` *equalities*; so the whole content of the ledger
is its budget row, i.e. `CubeHolePairRow`.

Why this form.  The pair-deadness hypothesis `flatPairSum ≤ 0` is not a soft sign condition:
`wSmallPair ≥ 0` pointwise (from `0 ≤ v`), so it forces `Φ` to vanish a.e. off the pair-dead set
(`Work.BoseB1Cube.pairDead_voidAe_sliding`), and it lets the whole `−flatPairSum` row be discarded.
What remains is the demand-side inequality whose only state-dependent payers are the Dirichlet word
`D` and the excited count `Q = boxQCount`.  By the razor identity (`flatDemand_sub_slack`) and
`W₁ ≤ Cw·(a v)·κ`, it is equivalent — up to the fixed constant `9π` and the fibre deviation — to the
**excess-density row**

    c·(a v)·μ·(flatScountB − κ·μ·normB)  ≤  D + μ(a v)·boxQCount + C·flatErrB ,

i.e. *the smooth window density above the chemical potential `μ` must be paid by the Dirichlet word
or by the excited count*.  This is the cube-cutoff, pair-dead form of FS `lm:appinteractionestimate`
and of the fleet's `Work.BoseFixB1S.mfSharpHoleKinPaysB1` /
`Work.Analysis.HoleVoidCost.holeVoidCostCountQuadGood`.

`CubeHoleChiCount` (session 3's residual) is **false** in general (shell/cluster family), so the pair
row below is the honest replacement.  See `FINDING_cubeHoleCapRow_session4.md`. -/

/-- **The pair-row residual.**  See the section docstring: the target's left-hand side with
`w1MassB ↦ flatPairMass` and `−flatPairSum` kept in, and with the nonnegative rows
`tBdiagFormInd` / `μ(a v)·normB` deleted from the right.  Strictly stronger than the target, and
sufficient for it (`cubeHoleCapRow_of_pairRow`). -/
def CubeHolePairRow (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) μ →
        ‖((Work.BoseFixB1.pL v μ) * (Work.BoseFixB1.pD v μ)) • u‖
            < (Work.BoseFixB1.pL v μ) / 2
              + (Work.BoseFixB1.pL v μ) * (Work.BoseFixB1.pD v μ) / 2 →
        Work.BoseFixB1.flatPairSum v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ≤ 0 →
        μ * Work.BoseFixB1.flatFibSum h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
        - μ * Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u
            * Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
        + (1 / 2) * Work.BoseFixB1.flatPairMass v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u
            * (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ^ 2
                * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
              + Work.BoseFixB1.Up.flatVar v μ (Φ : Submission.BoseGases.X n → ℝ) u)
        - Work.BoseFixB1.flatPairSum v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
      ≤ C * Work.BoseFixB1.Up.flatErrB v R μ (Φ : Submission.BoseGases.X n → ℝ) u
        + Work.BoseFixB1.Up.flatSlackB v h μ (Φ : Submission.BoseGases.X n → ℝ) u
        + μ * (_root_.BoseGases.a v)
            * Work.BoseFixB1S.boxQCount
                (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                (Work.BoseFixB1.pL v μ)
                (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                (Φ : Submission.BoseGases.X n → ℝ)

theorem cubeHoleCapRow_of_pairRow {v : E3 → ℝ} {h : Work.UBB.ScatSol v}
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v) (hrow : CubeHolePairRow v h R) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : E3),
          u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) μ →
          ‖((Work.BoseFixB1.pL v μ) * (Work.BoseFixB1.pD v μ)) • u‖
              < (Work.BoseFixB1.pL v μ) / 2
                + (Work.BoseFixB1.pL v μ) * (Work.BoseFixB1.pD v μ) / 2 →
          Work.BoseFixB1.flatPairSum v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ≤ 0 →
          (1 / 2) * Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u
              * (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                    (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ^ 2
                  * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
                + Work.BoseFixB1.Up.flatVar v μ (Φ : Submission.BoseGases.X n → ℝ) u)
            - μ * Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u
                * Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                    (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
                * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
            + μ * Work.BoseFixB1.flatFibSum h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
          ≤ Work.UBBInputs8.tBdiagFormInd (Work.BoseFixB1.pL v μ)
                (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                (Submission.BoseGases.chiSmallB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u)
                (fun r : ℝ => r ^ 2) (Φ : Submission.BoseGases.X n → ℝ)
            + C * Work.BoseFixB1.Up.flatErrB v R μ (Φ : Submission.BoseGases.X n → ℝ) u
            + Work.BoseFixB1.Up.flatSlackB v h μ (Φ : Submission.BoseGases.X n → ℝ) u
            + μ * (_root_.BoseGases.a v)
                * (Work.BoseFixB1S.boxQCount
                      (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                      (Work.BoseFixB1.pL v μ)
                      (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                      (Φ : Submission.BoseGases.X n → ℝ)
                  + Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)) := by
  obtain ⟨ε₁, c₀, hε₁, hc₀, hkey⟩ :=
    flatPairMass_sub_w1MassB_ge_const_mul (v := v) h hv hv1 hvrad hR hv_supp hav
  obtain ⟨ε₂, C, hε₂, hC, hbody⟩ := hrow
  refine ⟨min ε₁ ε₂, C, by positivity, hC, ?_⟩
  intro μ hAdm n Φ u hu hcorner hpair
  have hAdm₁ : Work.BoseBoxFix.Adm v ε₁ μ :=
    ⟨hAdm.1, le_trans hAdm.2.1 (min_le_left _ _), hAdm.2.2⟩
  have hAdm₂ : Work.BoseBoxFix.Adm v ε₂ μ :=
    ⟨hAdm.1, le_trans hAdm.2.1 (min_le_right _ _), hAdm.2.2⟩
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have ha : 0 < _root_.BoseGases.a v := Work.BoseFixB1.adm_a_pos hAdm
  have hℓ : 0 < Work.BoseFixB1.pL v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < Work.BoseFixB1.pD v μ := Work.BoseFixB1.adm_d_pos hAdm
  set W₁ : ℝ := Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) u with hW₁
  set W₂ : ℝ := Work.BoseFixB1.flatPairMass v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) u with hW₂
  set τ : ℝ := Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) with hτ
  set Nr : ℝ := Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) with hNr
  set V : ℝ := Work.BoseFixB1.Up.flatVar v μ (Φ : Submission.BoseGases.X n → ℝ) u with hV
  set Fs : ℝ := Work.BoseFixB1.flatFibSum h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) with hFs
  set Ps : ℝ := Work.BoseFixB1.flatPairSum v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) with hPs
  set Qχ : ℝ := Work.BoseFixB1S.boxQCount
      (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
      (Work.BoseFixB1.pL v μ)
      (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
      (Φ : Submission.BoseGases.X n → ℝ) with hQχ
  set Dχ : ℝ := Work.UBBInputs8.tBdiagFormInd (Work.BoseFixB1.pL v μ)
      (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
      (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
      (Submission.BoseGases.chiSmallB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
        (Work.BoseFixB1.pD v μ) u) (fun r : ℝ => r ^ 2)
      (Φ : Submission.BoseGases.X n → ℝ) with hDχ
  set er : ℝ := Work.BoseFixB1.Up.flatErrB v R μ (Φ : Submission.BoseGases.X n → ℝ) u with her
  set sl : ℝ := Work.BoseFixB1.Up.flatSlackB v h μ (Φ : Submission.BoseGases.X n → ℝ) u with hsl
  -- the row
  have hrowb : μ * Fs - μ * W₁ * τ * Nr + (1 / 2) * W₂ * (τ ^ 2 * Nr + V) - Ps
      ≤ C * er + sl + μ * (_root_.BoseGases.a v) * Qχ := hbody μ hAdm₂ n Φ u hu hcorner hpair
  -- W₁ ≤ W₂
  have hW1nn : 0 ≤ W₁ := by
    rw [hW₁]
    exact Work.BoseFixB1.w1MassB_nonneg h hv hvrad hR hv_supp hℓ hd u
  have hkeyu := hkey μ hAdm₁ u
  have hWle : W₁ ≤ W₂ := by
    have h2 : (1 + c₀) * W₁ = W₁ + c₀ * W₁ := by ring
    nlinarith [hkeyu, mul_nonneg hc₀.le hW1nn]
  have hNnn : 0 ≤ Nr := by
    rw [hNr]; exact Work.BoseFixB1.normB_nonneg (Φ : Submission.BoseGases.X n → ℝ)
  have hQnn : 0 ≤ Qχ := by rw [hQχ]; exact Work.BoseFixB1S.boxQCount_nonneg _ _ _ _
  -- X ≥ 0
  have hXeq : τ ^ 2 * Nr + V = Work.BoseFixB1.Up.flatT2 v μ (Φ : Submission.BoseGases.X n → ℝ) u := by
    rw [hV, hτ, hNr, Work.BoseFixB1.Up.flatVar]; ring
  have hXnn : 0 ≤ τ ^ 2 * Nr + V := by
    rw [hXeq, Work.BoseFixB1.Up.flatT2]
    exact integral_nonneg fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hDnn : 0 ≤ Dχ := by
    rw [hDχ]
    exact tBdiagFormInd_nonneg' hℓ _ (fun r => sq_nonneg r) (Φ : Submission.BoseGases.X n → ℝ)
  have hPs : Ps ≤ 0 := hpair
  have step1 : (1 / 2) * W₁ * (τ ^ 2 * Nr + V) ≤ (1 / 2) * W₂ * (τ ^ 2 * Nr + V) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hWle (by norm_num : (0:ℝ) ≤ 1 / 2)) hXnn
  have step2 : (1 / 2) * W₂ * (τ ^ 2 * Nr + V) - μ * W₁ * τ * Nr + μ * Fs
      ≤ C * er + sl + μ * (_root_.BoseGases.a v) * Qχ := by linarith [hrowb, hPs]
  have step3 : C * er + sl + μ * (_root_.BoseGases.a v) * Qχ
      ≤ Dχ + C * er + sl
        + μ * (_root_.BoseGases.a v) * (Qχ + Nr) := by
    have h1 : 0 ≤ μ * (_root_.BoseGases.a v) * Nr :=
      mul_nonneg (mul_nonneg hμ.le ha.le) hNnn
    linarith
  have key : (1 / 2) * W₁ * (τ ^ 2 * Nr + V) - μ * W₁ * τ * Nr + μ * Fs
      ≤ Dχ + C * er + sl + μ * (_root_.BoseGases.a v) * (Qχ + Nr) := by linarith [step1, step2, step3]
  rw [hW₁, hτ, hNr, hV, hFs, hQχ, hDχ, her, hsl] at key
  exact key

/-! ### The two named inputs of the pair row (the residual of the node)

`flatFib_row_adm` (`Submission/Work/BoseFixB1S/flatFibDeviationB1.lean` §8) discharges the whole
fibre-deviation row `μ·(flatFibSum − W₁·flatTau·normB)` at the target's vocabulary from **three**
inputs: a uniform bound `D` on `|fibDelta|`, the *count comparison* `boxFlatCount ≤ Cs·(τκN)`, and
the two *state-free ratio* inputs `(64/7)CsDκ ≤ W₁`, `32CsDκ ≤ W₂−W₁`.  The two `def`s below package
those inputs (`CubeHoleFibInputs`) and the demand row that absorbs what is left
(`CubeHoleDemandRow`): its left-hand side collects every demand-side scale the razor and the fibre
arithmetic produce — the `μ`-scale `(9/8)(W₁/κ)μS`, the `τ`-scale `2πc₀(W₁/κ)τS` of the pair-
condensate surplus that `fibRowArith` spends, the variance row, and the kinetic slot
`(2D/a − 1)μaQ` that exceeds the target's allowance — and its right-hand side is the target's own
`tBdiagFormInd + μ(a v)(boxQCount + normB) + C·flatErrB`.  See
`FINDING_cubeHoleCapRow_session4.md` §§1–3 for the derivation, the numerical checks on the spread
and concentrated product families, and the two bookkeeping caveats (the χ-dead collar, and the
double use of `flatSlackB`).

The expected assembly is `CubeHoleDemandRow + CubeHoleFibInputs ⟹ CubeHolePairRow`; it is *not*
landed here. -/

/-- **The demand row of the cube-hole branch** (see the section docstring). -/
def CubeHoleDemandRow (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ c c' c'' C : ℝ, 0 < ε₀ ∧ 0 < c ∧ 0 ≤ c' ∧ 0 ≤ c'' ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) μ →
        ‖((Work.BoseFixB1.pL v μ) * (Work.BoseFixB1.pD v μ)) • u‖
            < (Work.BoseFixB1.pL v μ) / 2
              + (Work.BoseFixB1.pL v μ) * (Work.BoseFixB1.pD v μ) / 2 →
        Work.BoseFixB1.flatPairSum v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ≤ 0 →
        c * (_root_.BoseGases.a v)
            * (μ + Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ))
            * Work.BoseFixB1.flatScountB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
          + c' * (_root_.BoseGases.a v)
              * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u
              * Work.BoseFixB1.Up.flatVar v μ (Φ : Submission.BoseGases.X n → ℝ) u
          + c'' * μ * (_root_.BoseGases.a v)
              * Work.BoseFixB1S.boxQCount
                  (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                  (Work.BoseFixB1.pL v μ)
                  (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                  (Φ : Submission.BoseGases.X n → ℝ)
        ≤ Work.UBBInputs8.tBdiagFormInd (Work.BoseFixB1.pL v μ)
              (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
              (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
              (Submission.BoseGases.chiSmallB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u)
              (fun r : ℝ => r ^ 2) (Φ : Submission.BoseGases.X n → ℝ)
          + μ * (_root_.BoseGases.a v)
              * (Work.BoseFixB1S.boxQCount
                    (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                    (Work.BoseFixB1.pL v μ)
                    (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                    (Φ : Submission.BoseGases.X n → ℝ)
                + Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
          + C * Work.BoseFixB1.Up.flatErrB v R μ (Φ : Submission.BoseGases.X n → ℝ) u

/-- **A local copy of the fibre-deviation kernel** `Work.BoseFixB1S.fibDelta`
(`Submission/Work/BoseFixB1S/flatFibDeviationB1.lean`), reproduced here because that module cannot
be imported into this cone: its cone contains `Work.BoseFixB1S.boxConstCalibB1`, which duplicates
`Work.BoseFixB1S.pairMass_eq_setIntegral` already declared by `Work.BoseFixB1S.boxPairValue` in
this file's cone.  The two are definitionally equal (`rfl`). -/
noncomputable def holeFibDelta {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (M : ℕ) (ℓ d : ℝ) (u : E3) :
    E3 → ℝ :=
  fun z => Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z
    - (Work.BoseFixB1.w1MassB h M ℓ d u / Work.SmallBoxSliding.chiMass M ℓ d u)
        * (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2

/-- **The three state-level inputs of the fibre row** (`flatFib_row_adm`'s hypotheses). -/
def CubeHoleFibInputs (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (_R : ℝ) : Prop :=
  ∃ ε₀ D Cs : ℝ, 0 < ε₀ ∧ 0 ≤ D ∧ 0 ≤ Cs ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) μ →
        ‖((Work.BoseFixB1.pL v μ) * (Work.BoseFixB1.pD v μ)) • u‖
            < (Work.BoseFixB1.pL v μ) / 2
              + (Work.BoseFixB1.pL v μ) * (Work.BoseFixB1.pD v μ) / 2 →
        (∀ z : E3, |holeFibDelta h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u z| ≤ D)
          ∧ Work.BoseFixB1S.boxFlatCount
                (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                (Work.BoseFixB1.pL v μ)
                (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                (Φ : Submission.BoseGases.X n → ℝ)
              ≤ Cs * Work.BoseFixB1.flatScountB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
          ∧ (64 / 7) * Cs * D
                * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                    (Work.BoseFixB1.pD v μ) u
              ≤ Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u
          ∧ 32 * Cs * D
                * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                    (Work.BoseFixB1.pD v μ) u
              ≤ Work.BoseFixB1.flatPairMass v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u
                - Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                    (Work.BoseFixB1.pD v μ) u

theorem cubeHoleCapRow {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) μ →
          ‖((Work.BoseFixB1.pL v μ) * (Work.BoseFixB1.pD v μ)) • u‖
              < (Work.BoseFixB1.pL v μ) / 2
                + (Work.BoseFixB1.pL v μ) * (Work.BoseFixB1.pD v μ) / 2 →
          Work.BoseFixB1.flatPairSum v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ≤ 0 →
          (1 / 2) * Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u
              * (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                    (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ^ 2
                  * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
                + Work.BoseFixB1.Up.flatVar v μ (Φ : Submission.BoseGases.X n → ℝ) u)
            - μ * Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u
                * Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                    (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
                * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
            + μ * Work.BoseFixB1.flatFibSum h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
          ≤ Work.UBBInputs8.tBdiagFormInd (Work.BoseFixB1.pL v μ)
                (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                (Submission.BoseGases.chiSmallB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u)
                (fun r : ℝ => r ^ 2) (Φ : Submission.BoseGases.X n → ℝ)
            + C * Work.BoseFixB1.Up.flatErrB v R μ (Φ : Submission.BoseGases.X n → ℝ) u
            + Work.BoseFixB1.Up.flatSlackB v h μ (Φ : Submission.BoseGases.X n → ℝ) u
            + μ * (_root_.BoseGases.a v)
                * (Work.BoseFixB1S.boxQCount
                      (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                      (Work.BoseFixB1.pL v μ)
                      (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                      (Φ : Submission.BoseGases.X n → ℝ)
                  + Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)) := by sorry

end Work.BoseB1Cube
