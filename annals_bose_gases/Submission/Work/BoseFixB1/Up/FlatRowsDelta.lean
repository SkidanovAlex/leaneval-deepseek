import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.Up.FlatRows
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1.Up.FlatRowsDelta` — the **Δ-augmented** split residual

`Work.BoseFixB1.Up.FlatRowsSplit` (`Up/FlatRows.lean`) demands the two band deviation rows

    (fib)  μ(flatFibSum − W₁·τ·‖Φ‖²) ≤ C₁·flatErrB + K₁μ(a v)n₊ ,
    (PQ₂)  ½W₂(τ²N + V) − flatPairSum ≤ C₂·flatErrB + flatSlackB + K₂μ(a v)n₊ .

The corpus's own audit (`FINDING_flatZeroExact.md` §1 and the docstring of
`BoseFixB1B/flatPair_row_allowance.lean`) records that the *budget* of the sharp ledger is **too
strong** on boxes that only *graze* the ball `‖x‖ ≤ ℓ/2` (there `W₁ ≪ W₂`): the diagonal correction
`Epair = ½W₂·χMass⁻²·S₄` carries `W₂` while the slack is spent at weight `W₁`, and the correct row
adds the **pair-condensate surplus**

    Δ := ½(W₂ − W₁)(τ²N + V)          (W₂ = flatPairMass, W₁ = w1MassB, ≥ 0).

This module defines `FlatRowsSplitDelta` — `FlatRowsSplit` with `Δ` added to the `(PQ₂)` row — and
proves that it is *strictly weaker* than `FlatRowsSplit` (as `Δ ≥ 0`, `flatPairMass_mono`-free: it
is `½·(W₂−W₁)·(·) ≥ 0` by `w1MassB_le_flatPairMassB1` and `0 ≤ τ²N + V`).  The assembly
`FlatRowsSplitDelta ⟹ FlatFreeResidual` goes through the Δ-augmented ledger
`Work.BoseFixB1.Up.perBoxF_of_ledger_delta` (this cone) in place of `perBoxF_of_ledger_kin`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1.Up

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-- **The flat branch split into its two deviation rows, with the pair-condensate surplus `Δ`.**
This is `Up.FlatRowsSplit` verbatim except that the `(PQ₂)` row's right-hand side carries the extra
nonnegative term

    Δ = ½·(flatPairMass − w1MassB)·(flatTau²·normB + flatVar) ,

which is the mean-field surplus of `½W₂(τ²N+V)` over what the fibre/`F`-rows consume; the sharp
ledger's budget is only correct *with* this term (`FINDING_flatZeroExact.md` §1). -/
def FlatRowsSplitDelta (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) :
    Prop :=
  ∃ ε₀ γ C₁ C₂ K₁ K₂ : ℝ, 0 < ε₀ ∧ 0 < γ ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ 0 ≤ K₁ ∧ 0 ≤ K₂ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : EuclideanSpace ℝ (Fin 3)),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
        ¬ IsThinBox v h μ u →
        nPlusB v μ u n (Φ : Submission.BoseGases.X n → ℝ)
            < γ * (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
        (μ * (Work.BoseFixB1.flatFibSum h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
              - Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                    (Work.BoseFixB1.pD v μ) u
                  * Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                      (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
                  * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
            ≤ C₁ * flatErrB v R μ (Φ : Submission.BoseGases.X n → ℝ) u
              + K₁ * μ * (_root_.BoseGases.a v) * nPlusB v μ u n
                  (Φ : Submission.BoseGases.X n → ℝ))
        ∧ ((1 / 2) * Work.BoseFixB1.flatPairMass v (Work.BoseFixB1.pM v μ)
                  (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u
                * (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                      (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ^ 2
                    * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
                  + flatVar v μ (Φ : Submission.BoseGases.X n → ℝ) u)
              - Work.BoseFixB1.flatPairSum v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
            ≤ C₂ * flatErrB v R μ (Φ : Submission.BoseGases.X n → ℝ) u
              + flatSlackB v h μ (Φ : Submission.BoseGases.X n → ℝ) u
              + (1 / 2)
                  * (Work.BoseFixB1.flatPairMass v (Work.BoseFixB1.pM v μ)
                        (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u
                      - Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                          (Work.BoseFixB1.pD v μ) u)
                  * (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                        (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ^ 2
                      * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
                    + flatVar v μ (Φ : Submission.BoseGases.X n → ℝ) u)
              + K₂ * μ * (_root_.BoseGases.a v) * nPlusB v μ u n
                  (Φ : Submission.BoseGases.X n → ℝ))

/-
**Strictness.**  `FlatRowsSplitDelta` is *strictly weaker* than `FlatRowsSplit`: the added term

    Δ = ½·(W₂ − W₁)·(τ²‖Φ‖² + flatVar)

is nonnegative because `W₂ = flatPairMass ≥ w1MassB = W₁` (the PROVED Born gap
`Work.BoseFixB1S.w1MassB_le_flatPairMassB1`, which needs exactly the target's own
`hv`/`hvrad`/`hv1`/`hv_supp` data plus the regime facts of `Work.BoseFixB1.regime_sideAt_ge`)
and `τ²‖Φ‖² + flatVar ≥ 0` (`0 ≤ τ`, `0 ≤ ‖Φ‖²`, `flatVar_nonneg`).  Hence every consumer of
`FlatRowsSplit` may be re-pointed at `FlatRowsSplitDelta` *for free*, and the assembly
`FlatRowsSplitDelta ⟹ FlatFreeResidual` is the sharper residual of the chapter.
-/

/-- **The Δ-augmented split residual is implied by the corpus's `FlatRowsSplit`** — the added term
`Δ = ½(W₂−W₁)(τ²‖Φ‖² + flatVar)` is nonnegative (`w1MassB_le_flatPairMassB1` for `W₁ ≤ W₂`, at a
smaller `ε₀` supplied by `regime_sideAt_ge`; `0 ≤ τ²‖Φ‖² + flatVar` by `flatTau_nonneg`,
`normB_nonneg`, `flatVar_nonneg`).  Hence `FlatRowsSplitDelta` is the *strictly weaker* residual:
every `FlatRowsSplit`-consumer may be re-pointed at it for free. -/
theorem flatRowsSplitDelta_of_flatRowsSplit {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : Work.UBB.ScatSol v} {R : ℝ} (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v)
    (hsp : FlatRowsSplit v h R) : FlatRowsSplitDelta v h R := by
  obtain ⟨ε₀, γ, C₁, C₂, K₁, K₂, hε₀, hγ, hC₁, hC₂, hK₁, hK₂, H⟩ := hsp
  obtain ⟨εr, hεr, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨min ε₀ εr, γ, C₁, C₂, K₁, K₂, lt_min hε₀ hεr, hγ, hC₁, hC₂, hK₁, hK₂, ?_⟩
  intro μ hAdm n Φ u hu hthin hband
  have hAdm₀ : Work.BoseBoxFix.Adm v ε₀ μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdm_r : Work.BoseBoxFix.Adm v εr μ := Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
  obtain ⟨hfib, hpair⟩ := H μ hAdm₀ n Φ u hu hthin hband
  refine ⟨hfib, ?_⟩
  have hμ : 0 < μ := hAdm.1
  have hℓ : 0 < Work.BoseFixB1.pL v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < Work.BoseFixB1.pD v μ := Work.BoseFixB1.adm_d_pos hAdm
  have hM1 : 1 ≤ Work.BoseFixB1.pM v μ := by
    change 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
    rw [Work.BoseFixB1.M_eq_mValue]; norm_num [Work.BoseBox.mValue]
  obtain ⟨hR16, hRχ⟩ := hreg μ hAdm_r.1 hAdm_r.2.1
  have hW12 : Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) u
      ≤ Work.BoseFixB1.flatPairMass v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u :=
    Work.BoseFixB1S.w1MassB_le_flatPairMassB1 (v := v) h hv hvrad hv1 hR hv_supp hM1 hℓ hd hR16 hRχ u
  have hΔnn : 0 ≤ (1 / 2)
      * (Work.BoseFixB1.flatPairMass v (Work.BoseFixB1.pM v μ)
            (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u
          - Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u)
      * (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ^ 2
          * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
        + flatVar v μ (Φ : Submission.BoseGases.X n → ℝ) u) := by
    refine mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (add_nonneg ?_ ?_)
    · exact mul_nonneg (sq_nonneg _) (normB_nonneg _)
    · have hNpos : 0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
        have hn0 : 0 ≤ nPlusB v μ u n (Φ : Submission.BoseGases.X n → ℝ) :=
          nPlusB_nonneg v μ u n (Φ : Submission.BoseGases.X n → ℝ)
        have h2 : 0 < γ * (n : ℝ) * Work.BoseBoxFix.normB v μ n
            (Φ : Submission.BoseGases.X n → ℝ) := lt_of_le_of_lt hn0 hband
        rcases lt_or_ge (0 : ℝ) (n : ℝ) with hp | hle
        · exact pos_of_mul_pos_right h2 (le_of_lt (mul_pos hγ hp))
        · exfalso
          have hz : (n : ℝ) = 0 := le_antisymm hle (Nat.cast_nonneg n)
          simp only [hz, mul_zero, zero_mul] at h2
          exact absurd h2 (lt_irrefl (0 : ℝ))
      exact flatVar_nonneg Φ.contDiff.continuous hNpos u
  linarith [hpair, hΔnn]

/-- **The kinetic-aware, Δ-augmented flat residual** — the weakest residual of the chapter.

This is `Up.FlatRows` verbatim except for its **budget row**: the payers are

    C·flatErrB + flatSlackB + Δ + sbKin ,      Δ := ½(W₂−W₁)(τ²‖Φ‖² + flatVar) ,

i.e. the *whole* kinetic word `sbKin` is made available (with `P := sbKin`, the Δ-ledger's
`hkin : P ≤ sbKin` is `le_rfl`), instead of only its `ε_T`-gap half `K₂μ(a v)n₊` as in `FlatRows` /
`FlatRowsSplit(Delta)`.  Since `K₂μ(a v)n₊ ≤ sbKin` (`Up.sbKin_ge_K2_mu_av_nPlus`), this budget is
*implied* by the `FlatRowsSplit`-based one, so the residual is strictly weaker.

**Why it is the right shape.**  On the correlation-hole / Jastrow states (the family every
refutation attempt uses) the pair energy is suppressed *exactly* — the state is supported away from
`supp w_B` — so the pair row in the `FlatRowsSplitDelta` spelling fails: `½W₂X − flatPairSum ≈ ½W₂X`
while `CerrN + W₁slack + K₂μ(a v)n₊ = o(½W₂X)` as the diluteness `t = μ(a v)³ → 0` (see
`FINDING_flatFreeResidual_session2.md` §2's table).  The *same* family, however, has a large
**spectral** word: its in-box profile has holes of radius `ρ₀ ≥ R + smear` and transition width
`w ≲ ρ₀ − R − smear`, so `∫|∇(χ_BΦ)|² ≈ n_in·4πρ₀²/w` and the PROVED spectral comparison
(`Work.BoseFixB1S.mfSpecGeSharpDivDirichletB1`) gives
`sbKin ≳ 4πρ₀²n_in/w − ℓd ≫ ½W₂X = 4π μ(a v)·n_in·(μ·…)`.  So the *only* payer that can close the
flat branch is the full `sbKin`, and this residual is the statement that it does. -/
def FlatRowsDeltaKin (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ γ C : ℝ, 0 < ε₀ ∧ 0 < γ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : EuclideanSpace ℝ (Fin 3)),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
        ¬ IsThinBox v h μ u →
        nPlusB v μ u n (Φ : Submission.BoseGases.X n → ℝ)
            < γ * (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
        ∃ Efib Epair : ℝ,
          (μ * Work.BoseFixB1.flatFibSum h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
              ≤ μ * Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                    (Work.BoseFixB1.pD v μ) u
                  * Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                      (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
                  * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) + Efib)
          ∧ ((1 / 2) * Work.BoseFixB1.flatPairMass v (Work.BoseFixB1.pM v μ)
                  (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u
                * (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                      (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ^ 2
                    * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
                  + flatVar v μ (Φ : Submission.BoseGases.X n → ℝ) u)
              ≤ Work.BoseFixB1.flatPairSum v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                    (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) + Epair)
          ∧ Efib + Epair
              ≤ C * flatErrB v R μ (Φ : Submission.BoseGases.X n → ℝ) u
                + flatSlackB v h μ (Φ : Submission.BoseGases.X n → ℝ) u
                + (1 / 2)
                    * (Work.BoseFixB1.flatPairMass v (Work.BoseFixB1.pM v μ)
                          (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u
                        - Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                            (Work.BoseFixB1.pD v μ) u)
                    * (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                          (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ^ 2
                        * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
                      + flatVar v μ (Φ : Submission.BoseGases.X n → ℝ) u)
                + Work.BoseFixB1.sbKin (v := v) μ (Work.BoseFixB1.pM v μ) u
                    (Φ : Submission.BoseGases.X n → ℝ)

/-! ## The **joint** residual vs. splitting the two deviations

A word of warning, discovered while filing the split forms: **splitting the fibre and pair
deviations is a dead end**, and no future session should re-file it.

On a product family `Φ = Π(g + β f)` with `g = 1_B`-flat and `β → 0` one has, with
`FibDev := flatFibSum − W₁(τ‖Φ‖²)` and `PairDev := ½W₂(τ²‖Φ‖²+V) − flatPairSum`,

* `Q_{B,i}Φ = β·1_B(f − ⟨f⟩)` for every `i`, hence `n₊ = Θ(β²n)` and **`sbKin = Θ(β²n)`**
  (both its `ε_T`-gap and its spectral half are *quadratic* in the excited part), while
* `FibDev` has a *linear* term `(n/Z)·2β∫_B fδ`, `δ = fib − (W₁/κ)χ²`, `∫δ = 0`, and `PairDev` a
  linear term of the *same magnitude and opposite sign*.

So each deviation *individually* is `Θ(βn)` — not payable by anything `Θ(β²n)` or state-free — while
their **sum** is `O(β²)`.  The corpus's `FlatRowsSplit` (and any split spelling, including the
`FlatFibKin`/`FlatPairKin` pair that was tried and withdrawn here) is therefore *too strong*: it is
refuted by this family for every constant as `β → 0`, `n → ∞`.  The residual must be stated
**jointly** (existential `Efib`, `Epair`, or — equivalently, see below — directly in terms of the
word), which is exactly the shape of `FlatRows` and of `FlatRowsDeltaKin`. -/

/-- **The kinetic-aware, Δ-augmented flat residual in *word* form** — the residual of
`FlatRowsDeltaKin`, with the two deviation rows eliminated by the identity
`sbWord = sbKin − μ·flatFibSum + flatPairSum`:

    in the band `n₊ < γ n ‖Φ‖²`,
    `sbWord ≥ ½W₂(τ²‖Φ‖² + V) − μ·W₁·τ·‖Φ‖² − C·flatErrB − flatSlackB − Δ` ,

with `Δ = ½(W₂−W₁)(τ²‖Φ‖²+V)` the pair-condensate surplus.  This is *equivalent* to
`FlatRowsDeltaKin` (see `flatRowsDeltaKin_of_flatWordKin`), but it is a single inequality about the
word, with no existential quantifiers — the shape a prover of the flat branch should attack. -/
def FlatWordKin (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ γ C : ℝ, 0 < ε₀ ∧ 0 < γ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : EuclideanSpace ℝ (Fin 3)),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
        ¬ IsThinBox v h μ u →
        nPlusB v μ u n (Φ : Submission.BoseGases.X n → ℝ)
            < γ * (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
        (1 / 2) * Work.BoseFixB1.flatPairMass v (Work.BoseFixB1.pM v μ)
              (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u
            * (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ^ 2
                * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
              + flatVar v μ (Φ : Submission.BoseGases.X n → ℝ) u)
          - μ * Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u
              * Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
              * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
          - C * flatErrB v R μ (Φ : Submission.BoseGases.X n → ℝ) u
          - flatSlackB v h μ (Φ : Submission.BoseGases.X n → ℝ) u
          - (1 / 2)
              * (Work.BoseFixB1.flatPairMass v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u
                - Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                    (Work.BoseFixB1.pD v μ) u)
              * (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                    (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ^ 2
                  * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
                + flatVar v μ (Φ : Submission.BoseGases.X n → ℝ) u)
        ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ)

/-- **The word form implies the row form.**  Take the two deviations themselves as the errors
`Efib`, `Epair` (the rows then hold with equality) and use the identity
`Efib + Epair = sbKin − μW₁τ‖Φ‖² + ½W₂(τ²‖Φ‖²+V) − sbWord`, together with `sbKin ≥ 0`. -/
theorem flatRowsDeltaKin_of_flatWordKin {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R : ℝ} (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v)
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v)
    (hw : FlatWordKin v h R) : FlatRowsDeltaKin v h R := by
  obtain ⟨ε₀, γ, C, hε₀, hγ, hC, H⟩ := hw
  obtain ⟨εr, hεr, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨min ε₀ εr, γ, C, lt_min hε₀ hεr, hγ, hC, ?_⟩
  intro μ hAdm n Φ u hu hthin hband
  have hAdm₀ : Work.BoseBoxFix.Adm v ε₀ μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdm_r : Work.BoseBoxFix.Adm v εr μ := Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
  obtain ⟨hR16, hRχ⟩ := hreg μ hAdm_r.1 hAdm_r.2.1
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  have hword := H μ hAdm₀ n Φ u hu hthin hband
  have hsplit := sbPot_split (v := v) (h := h) (R := R) hv_supp hR hv hvrad hv1 hAdm_r hΦc u hR16 hRχ
  refine ⟨μ * (Work.BoseFixB1.flatFibSum h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
        - Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u
            * Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)),
    (1 / 2) * Work.BoseFixB1.flatPairMass v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
        (Work.BoseFixB1.pD v μ) u
      * (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ^ 2
          * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
        + flatVar v μ (Φ : Submission.BoseGases.X n → ℝ) u)
    - Work.BoseFixB1.flatPairSum v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
        (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ), ?_, ?_, ?_⟩
  · exact le_of_eq (by ring)
  · exact le_of_eq (by ring)
  · -- the budget, from the word inequality
    have hkey : μ * (Work.BoseFixB1.flatFibSum h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
        - Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u
            * Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
      + ((1 / 2) * Work.BoseFixB1.flatPairMass v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u
          * (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ^ 2
              * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
            + flatVar v μ (Φ : Submission.BoseGases.X n → ℝ) u)
        - Work.BoseFixB1.flatPairSum v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ))
      = Work.BoseFixB1.sbKin (v := v) μ (Work.BoseFixB1.pM v μ) u (Φ : Submission.BoseGases.X n → ℝ)
        + ((1 / 2) * Work.BoseFixB1.flatPairMass v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u
            * (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ^ 2
                * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
              + flatVar v μ (Φ : Submission.BoseGases.X n → ℝ) u)
          - μ * Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u
              * Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
              * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
          - Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ)) := by
      rw [Work.BoseFixB1.sbWord, hsplit]
      simp only [Work.BoseFixB1.flatFibSum, fibSum, Work.BoseFixB1.flatPairSum, pairSum]
      ring
    linarith [hkey, hword]

end Work.BoseFixB1.Up
