import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.Up.FlatRowsDelta
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1.Up.flatWordKinDense` — the **regime split** of the flat arm, and the
dense case as its own (strictly weaker) residual

`Work.BoseFixB1.Up.FlatWordKin` (`Up/FlatRowsDelta.lean`) is the single residual of the flat arm:

    in the band `n₊ < γ n ‖Φ‖²` on good, non-thin sliding boxes,
    `½W₂(τ²‖Φ‖² + V) − μW₁τ‖Φ‖² − C·flatErrB − flatSlackB − Δ ≤ sbWord`,                      (R)

with `W₁ = w1MassB`, `W₂ = flatPairMass`, `τ = flatTau`, `N = normB`, `V = flatVar`,
`Δ = ½(W₂−W₁)(τ²N+V)`, `flatSlackB = Up.flatSlackB`.  This file **does not assume** (R): it names
its two regime cases and **proves** that they compose back to (R).

## Why the split is by the *density*

`Up.flatSlack_delta_identity` (proved in `Up/flatSlackIdentity.lean`) shows that at the simplified
slack `W₁((7/16)N(τ−μ)² + V/4)` — which `up.flatSlackB` dominates, since
`1/2 − c₁μ/(τ+μ) ≥ 7/16` and `1/2 − 4c₁μ²/(τ+μ)² ≥ 1/4` for `τ ≥ 0`, `c₁ = 1/16` — (R) is exactly

    `sbWord ≥ W₁·(V/4 + N(τ−μ)²/16 − μ²N/2) − C·flatErrB` ,                                (★)

whose right-hand side grows like `τ²N`.  At the *reference* density `τ = μ` the comparison term is
exactly `W₁V/4` (the Born-gap balance), so:

* **dense** (`μ ≤ τ`): the pair-condensate energy `½W₂(τ²N+V)` supplies a headroom of order `τ²N`
  (at `τ = μ` the gap `W₂ − W₁` balances (★) exactly), which is what the losses of the localised
  pairing estimate (`boxA2`, the `boxPairBlock` cross terms, the `(n−1)Q` defects of the crude
  projected row) have to be absorbed by;
* **dilute** (`τ < μ`): the headroom is gone, and the fibre deviation `μ(flatFibSum − W₁τN)` is what
  has to be controlled.

`Δ` and `flatSlackB` are both `≤` the headroom, and neither is interchangeable between the regimes,
which is why the split must be on `τ` (and not on `n₊`, on `N`, or on the box geometry).

The two cases share the same `FlatWordLe` spelling and the same four-constant shape, so
`flatWordKin_of_dense_dilute` (proved here) glues them with `min ε₀`, `min γ`, `max C` for a
**fixed** split point `K` (the glue takes `K` as a parameter, so the split point is a design
choice: the dense case is easier and the dilute case harder as `K` grows).

## Status

* `flatWordLe_mono` and `flatWordKin_of_dense_dilute` are **proved**, `sorry`-free;
* `FlatWordKinDense` / `FlatWordKinDilute` are the two **named residuals** (definitions only).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1.Up

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The word-level flat inequality** `(R)` at FS's parameters, as a predicate of the state and the
error constant `C`.  Isolating it lets the two regime cases share one spelling. -/
def FlatWordLe (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R μ : ℝ)
    {n : ℕ} (Φ : X n → ℝ) (u : E3) (C : ℝ) : Prop :=
  (1 / 2) * Work.BoseFixB1.flatPairMass v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
        (Work.BoseFixB1.pD v μ) u
      * (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u Φ ^ 2
          * Work.BoseBoxFix.normB v μ n Φ
        + flatVar v μ Φ u)
    - μ * Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u
        * Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u Φ
        * Work.BoseBoxFix.normB v μ n Φ
    - C * flatErrB v R μ Φ u
    - flatSlackB v h μ Φ u
    - (1 / 2)
        * (Work.BoseFixB1.flatPairMass v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u
            - Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u)
        * (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u Φ ^ 2
            * Work.BoseBoxFix.normB v μ n Φ
          + flatVar v μ Φ u)
  ≤ Work.BoseFixB1.sbWord h μ u Φ

/-- The error bracket `flatErrB` is nonnegative at an admissible point, so `FlatWordLe` is monotone
in its error constant — this is what lets the glue take `max C₁ C₂`. -/
theorem flatErrB_nonneg {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R μ : ℝ} {n : ℕ} {Φ : X n → ℝ}
    {u : E3} {ε : ℝ} (hAdm : Work.BoseBoxFix.Adm v ε μ) :
    0 ≤ flatErrB v R μ Φ u := by
  have hμ : 0 < μ := hAdm.1
  have ha : 0 < _root_.BoseGases.a v := Work.BoseFixB1.adm_a_pos hAdm
  have hχ : 0 ≤ Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) u := Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
  have hN : 0 ≤ Work.BoseBoxFix.normB v μ n Φ := Work.BoseFixB1.normB_nonneg _
  rw [flatErrB]
  refine add_nonneg ?_ ?_
  · refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) ha.le) ?_) hχ) hN
    refine add_nonneg (sq_nonneg _) ?_
    refine mul_nonneg (pow_nonneg (le_of_lt (Work.BoseFixB1.paramsAt_KB_pos hAdm)) 3) ?_
    exact Real.rpow_nonneg (mul_nonneg hμ.le (pow_nonneg ha.le 3)) _
  · exact mul_nonneg (mul_nonneg hμ.le ha.le) hN

/-- Monotonicity of `FlatWordLe` in the error constant. -/
theorem flatWordLe_mono {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R μ : ℝ} {n : ℕ} {Φ : X n → ℝ}
    {u : E3} {C C' : ℝ} {ε : ℝ} (hAdm : Work.BoseBoxFix.Adm v ε μ) (hC : C ≤ C')
    (hle : FlatWordLe v h R μ Φ u C) : FlatWordLe v h R μ Φ u C' := by
  have hfE := flatErrB_nonneg (h := h) (R := R) (μ := μ) (Φ := Φ) (u := u) hAdm
  have : C * flatErrB v R μ Φ u ≤ C' * flatErrB v R μ Φ u :=
    mul_le_mul_of_nonneg_right hC hfE
  unfold FlatWordLe at hle ⊢
  linarith

/-- **The dense case of the flat residual** at the split point `K`: `FlatWordKin`'s statement with
the extra hypothesis `K μ ≤ τ` (the state's mean smooth density in the box is at least `K` times the
reference density).  Strictly weaker than `FlatWordKin`; this is where the pair-condensate energy
`½W₂(τ²N+V)` — hence the headroom of (★)'s right-hand side — grows like `τ²N`. -/
def FlatWordKinDense (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R K : ℝ) : Prop :=
  ∃ ε₀ γ C : ℝ, 0 < ε₀ ∧ 0 < γ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v)))
        (u : E3),
        u ∈ goodSet (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) μ →
        ¬ IsThinBox v h μ u →
        nPlusB v μ u n (Φ : X n → ℝ)
            < γ * (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) →
        K * μ ≤ Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u (Φ : X n → ℝ) →
        FlatWordLe v h R μ (Φ : X n → ℝ) u C

/-- **The dilute case of the flat residual** at the same split point `K`: the complementary regime
`τ < K μ`.  Stated for symmetry and for the glue; not part of the current delegation. -/
def FlatWordKinDilute (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R K : ℝ) : Prop :=
  ∃ ε₀ γ C : ℝ, 0 < ε₀ ∧ 0 < γ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v)))
        (u : E3),
        u ∈ goodSet (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) μ →
        ¬ IsThinBox v h μ u →
        nPlusB v μ u n (Φ : X n → ℝ)
            < γ * (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) →
        Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u (Φ : X n → ℝ) < K * μ →
        FlatWordLe v h R μ (Φ : X n → ℝ) u C

/-- **The glue.**  At a fixed split point `K` the two cases exhaust the states, so they compose back
to `FlatWordKin`: take `min ε₀`, `min γ` and `max C` and split on `K μ ≤ τ`.  Hence the residual
may be attacked case by case, and the split point is a free design choice. -/
theorem flatWordKin_of_dense_dilute {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R K : ℝ}
    (hD : FlatWordKinDense v h R K) (hd : FlatWordKinDilute v h R K) :
    FlatWordKin v h R := by
  obtain ⟨ε₁, γ₁, C₁, hε₁, hγ₁, hC₁, hpr₁⟩ := hD
  obtain ⟨ε₂, γ₂, C₂, hε₂, hγ₂, hC₂, hpr₂⟩ := hd
  refine ⟨min ε₁ ε₂, min γ₁ γ₂, max C₁ C₂, lt_min hε₁ hε₂, lt_min hγ₁ hγ₂,
    le_max_of_le_left hC₁, fun μ hA n Φ u hg ht hb => ?_⟩
  have hA₁ : Work.BoseBoxFix.Adm v ε₁ μ := Work.BoseFixB1.Adm.mono hA (min_le_left _ _)
  have hA₂ : Work.BoseBoxFix.Adm v ε₂ μ := Work.BoseFixB1.Adm.mono hA (min_le_right _ _)
  have hN : 0 ≤ Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) := Work.BoseFixB1.normB_nonneg _
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hb₁ : nPlusB v μ u n (Φ : X n → ℝ)
      < γ₁ * (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) :=
    lt_of_lt_of_le hb (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_le_left γ₁ γ₂) hn) hN)
  have hb₂ : nPlusB v μ u n (Φ : X n → ℝ)
      < γ₂ * (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) :=
    lt_of_lt_of_le hb (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_le_right γ₁ γ₂) hn) hN)
  by_cases hcase : K * μ ≤ Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ)
      (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u (Φ : X n → ℝ)
  · exact flatWordLe_mono hA₁ (le_max_left _ _) (hpr₁ μ hA₁ n Φ u hg ht hb₁ hcase)
  · push_neg at hcase
    exact flatWordLe_mono hA₂ (le_max_right _ _) (hpr₂ μ hA₂ n Φ u hg ht hb₂ hcase)

end Work.BoseFixB1.Up
