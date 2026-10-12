import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.perBoxF_flat
import Submission.Work.BoseFixB1S.psiWeightVarianceFrowB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1S

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The pure-real core -/

/-- **The arithmetic core of the sharp flat-branch ledger.**  For `0 < μ`, `0 < c₁ ≤ 1/8` and
`τ, I, V ≥ 0`,

    c₁·(I·F(τ) + 4μ²V/(τ+μ)²) + μτI ≤ ½τ²I + ½V + ½μ²I ,      F(τ) = μ(τ−μ)²/(τ+μ) .

After multiplying by `(τ+μ)² > 0` the difference of the two sides is

    I·(τ−μ)²·(τ+μ)·(½(τ+μ) − c₁μ) + V·(½(τ+μ)² − 4c₁μ²) ≥ 0 ,

using `c₁μ ≤ (1/8)μ ≤ ½(τ+μ)` and `4c₁μ² ≤ ½μ² ≤ ½(τ+μ)²` for `c₁ ≤ 1/8`, `τ ≥ 0`. -/
theorem flatArithSharpCore {μ c₁ τ I V : ℝ} (hμ : 0 < μ) (hc₁ : 0 < c₁) (hc₁8 : c₁ ≤ 1 / 8)
    (hτ : 0 ≤ τ) (hI : 0 ≤ I) (hV : 0 ≤ V) :
    c₁ * (I * (μ * (τ - μ) ^ 2 / (τ + μ)) + 4 * μ ^ 2 * V / (τ + μ) ^ 2) + μ * τ * I
      ≤ (1 / 2) * τ ^ 2 * I + (1 / 2) * V + (1 / 2) * μ ^ 2 * I := by
  have hτμ : 0 < τ + μ := by linarith
  have hτμ2 : 0 < (τ + μ) ^ 2 := by positivity
  have hA : 0 ≤ 1 / 2 * (τ + μ) - c₁ * μ := by
    have h1 : c₁ * μ ≤ (1 / 8) * μ := mul_le_mul_of_nonneg_right hc₁8 hμ.le
    nlinarith [h1, hτ, hμ]
  have hB : 0 ≤ 1 / 2 * (τ + μ) ^ 2 - 4 * c₁ * μ ^ 2 := by
    have h1 : 4 * c₁ * μ ^ 2 ≤ 4 * (1 / 8) * μ ^ 2 := by nlinarith [hc₁8, sq_nonneg μ]
    nlinarith [h1, hτμ, hμ, sq_nonneg τ]
  have hnn : 0 ≤ I * ((τ - μ) ^ 2 * (τ + μ) * (1 / 2 * (τ + μ) - c₁ * μ))
      + V * (1 / 2 * (τ + μ) ^ 2 - 4 * c₁ * μ ^ 2) :=
    add_nonneg (mul_nonneg hI (mul_nonneg (mul_nonneg (sq_nonneg _) hτμ.le) hA))
      (mul_nonneg hV hB)
  have hmain : I * ((τ - μ) ^ 2 * (τ + μ) * (1 / 2 * (τ + μ) - c₁ * μ))
      + V * (1 / 2 * (τ + μ) ^ 2 - 4 * c₁ * μ ^ 2)
      = (τ + μ) ^ 2 * ((1 / 2 * τ ^ 2 * I + (1 / 2) * V + (1 / 2) * μ ^ 2 * I)
        - (c₁ * (I * (μ * (τ - μ) ^ 2 / (τ + μ)) + 4 * μ ^ 2 * V / (τ + μ) ^ 2)
            + μ * τ * I)) := by
    field_simp
    ring
  rw [hmain] at hnn
  have hD : 0 ≤ (1 / 2 * τ ^ 2 * I + (1 / 2) * V + (1 / 2) * μ ^ 2 * I)
      - (c₁ * (I * (μ * (τ - μ) ^ 2 / (τ + μ)) + 4 * μ ^ 2 * V / (τ + μ) ^ 2)
          + μ * τ * I) := by
    have h' : 0 ≤ ((1 / 2 * τ ^ 2 * I + (1 / 2) * V + (1 / 2) * μ ^ 2 * I)
        - (c₁ * (I * (μ * (τ - μ) ^ 2 / (τ + μ)) + 4 * μ ^ 2 * V / (τ + μ) ^ 2)
            + μ * τ * I)) * (τ + μ) ^ 2 := by
      rw [mul_comm]; exact hnn
    exact nonneg_of_mul_nonneg_left h' hτμ2
  linarith [hD]

/-! ## 2. The sharp flat-branch ledger -/

/-- **The budget term of `perBoxF_of_ledger_sharp`, in the `flatErr` form.**  The ledger's `hbud`
slot is stated in the *unfolded* form of `PerBoxF`'s error term (so that `linarith` can use it);
this identity converts a bound `Efib + Epair ≤ C * flatErr … * N (+ slack)` into that form:

    `rw [Work.BoseFixB1S.flatErr_mul_eq] at hbud`.

(The right-hand side is `C·(μ²(a v)Γ·χ-mass·N + μ(a v)N)` with
`Γ = (R/(ℓd))² + K_B³(μ(a v)³)^{1/2}` — i.e. exactly the error bracket of `PerBoxF`.) -/
theorem flatErr_mul_eq {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R C μ : ℝ}
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) :
    C * Work.BoseFixB1.flatErr v R (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) μ u
        * Work.BoseBoxFix.normB v μ n Φ
      = C * (μ ^ 2 * (_root_.BoseGases.a v)
            * ((R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
                  * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
                + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                  * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
            * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
            * Work.BoseBoxFix.normB v μ n Φ
          + μ * (_root_.BoseGases.a v) * Work.BoseBoxFix.normB v μ n Φ) := by
  rw [Work.BoseFixB1.flatErr]
  ring

/-- **The sharp flat-branch ledger of `PerBoxF`.**  At FS's parameters, the inputs

* `(Fsharp)` `Fterm ≤ N·F(τ) + (4μ²/(τ+μ)²)·V` — the *sharp* `F`-row
  (`F_weight_le_mean_add_var_sharpB1` composed with `psiWeight_one_eq'`), with `V` the state's
  `t`-variance,
* `(fib)`    `μ·fibSum ≤ μW₁τN + Efib`,
* `(PQ₂)`    `½W₂(τ²N + V) ≤ pairSum + Epair` — the **quadratic mean-field pair row**, with
  `W₂ = ∬wSmallPair(·,·;v)`,
* the budget `Efib + Epair + (the arithmetic slack)` ≤ `C·(μ²(a v)Γ·χ-mass·N + μ(a v)N)`, i.e.
  the pair row's error is only required to be covered *after* the slack
  `W₁·[(τ−μ)²N(½ − c₁μ/(τ+μ)) + V(½ − 4c₁μ²/(τ+μ)²)]` left over by `flatArithSharpCore` (the
  plain budget `Efib + Epair ≤ C·flatErr·N` is the special case obtained by dropping the
  nonnegative slack — this matters because the pair row's error is *linear* in the particle
  number while `flatErr` is not),

together with the proved split `sbPot = −μfibSum + pairSum`, `sbKin ≥ 0`, `W₁ ≤ W₂`,
`μ, τ, N, W₁, V ≥ 0` and `0 < c₁ ≤ 1/8`, imply `PerBoxF v h R c₁ C μ n Φ u`.

The pair input is *quadratic* in the density (it is the mean-field value `½W₂∫Φ²t²` of the pair
energy), and the `V`-term of the sharp `F`-row is paid by the `V`-term of `(PQ₂)` with the exact
coefficient comparison `8c₁μ²/(τ+μ)² ≤ W₂/W₁`.  Nothing is lost at `τ = μ`, `W₂ = W₁`, `V = 0`. -/
theorem perBoxF_of_ledger_sharp {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    {R C μ c₁ : ℝ} {n : ℕ}
    {Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))}
    {u : EuclideanSpace ℝ (Fin 3)} {Efib Epair V : ℝ}
    (hμ : 0 < μ) (hc₁ : 0 < c₁) (hc₁8 : c₁ ≤ 1 / 8)
    (hN : 0 ≤ Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
    (hW1 : 0 ≤ Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
        (Work.BoseFixB1.pD v μ) u)
    (hW12 : Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
        (Work.BoseFixB1.pD v μ) u
      ≤ Work.BoseFixB1.flatPairMass v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u)
    (hτ : 0 ≤ Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
        (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ))
    (hV : 0 ≤ V)
    (hF : Work.BoseFixB1.flatFterm (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) μ u (Φ : Submission.BoseGases.X n → ℝ)
        ≤ Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
            * (μ * (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) - μ) ^ 2
                / (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) + μ))
          + 4 * μ ^ 2
              / (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) + μ) ^ 2
            * V)
    (hfib : μ * Work.BoseFixB1.flatFibSum h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
        ≤ μ * Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u
            * Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) + Efib)
    (hpair : (1 / 2) * Work.BoseFixB1.flatPairMass v (Work.BoseFixB1.pM v μ)
            (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u
          * (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ^ 2
              * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) + V)
        ≤ Work.BoseFixB1.flatPairSum v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) + Epair)
    (hsplit : Work.BoseFixB1.sbPot h μ u (Φ : Submission.BoseGases.X n → ℝ)
      = -(μ * Work.BoseFixB1.flatFibSum h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ))
        + Work.BoseFixB1.flatPairSum v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ))
    (hkin : 0 ≤ Work.BoseFixB1.sbKin (v := v) μ (Work.BoseFixB1.pM v μ) u
        (Φ : Submission.BoseGases.X n → ℝ))
    (hbud : Efib + Epair
      ≤ C * (μ ^ 2 * (_root_.BoseGases.a v)
            * ((R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
                  * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
                + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                  * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
            * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
          + μ * (_root_.BoseGases.a v)
              * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
        + Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u
          * ((Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) - μ) ^ 2
              * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
              * (1 / 2 - c₁ * μ
                  / (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                      (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) + μ))
            + V * (1 / 2 - 4 * c₁ * μ ^ 2
                / (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                    (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) + μ) ^ 2))) :
    Work.BoseFixB1.PerBoxF v h R c₁ C μ n Φ u := by
  rw [Work.BoseFixB1.PerBoxF, Work.BoseFixB1.sbWord, hsplit]
  have hFb_eq : (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ
          (Work.BoseFixB1.nCountB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u x
            / Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u))
      = Work.BoseFixB1.flatFterm (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) μ u (Φ : Submission.BoseGases.X n → ℝ) := rfl
  rw [hFb_eq]
  set I : ℝ := Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) with hIdef
  set τ : ℝ := Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) with hτdef
  set W₁ : ℝ := Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) u with hW₁def
  set W₂ : ℝ := Work.BoseFixB1.flatPairMass v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) u with hW₂def
  set Fb : ℝ := Work.BoseFixB1.flatFterm (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) μ u (Φ : Submission.BoseGases.X n → ℝ) with hFbdef
  set Fs : ℝ := Work.BoseFixB1.flatFibSum h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) with hFsdef
  set Ps : ℝ := Work.BoseFixB1.flatPairSum v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) with hPsdef
  -- the arithmetic core at `(τ, I, V)`
  have hcore : c₁ * (I * (μ * (τ - μ) ^ 2 / (τ + μ)) + 4 * μ ^ 2 * V / (τ + μ) ^ 2) + μ * τ * I
      ≤ (1 / 2) * τ ^ 2 * I + (1 / 2) * V + (1 / 2) * μ ^ 2 * I :=
    flatArithSharpCore hμ hc₁ hc₁8 hτ hN hV
  -- scale by `W₁ ≤ W₂`, keeping the arithmetic slack
  have hslackid : W₁ * ((1 / 2) * τ ^ 2 * I + (1 / 2) * V + (1 / 2) * μ ^ 2 * I)
      - W₁ * (c₁ * (I * (μ * (τ - μ) ^ 2 / (τ + μ)) + 4 * μ ^ 2 * V / (τ + μ) ^ 2)
          + μ * τ * I)
      = W₁ * ((τ - μ) ^ 2 * I * (1 / 2 - c₁ * μ / (τ + μ))
          + V * (1 / 2 - 4 * c₁ * μ ^ 2 / (τ + μ) ^ 2)) := by
    have hτμ : τ + μ ≠ 0 := by positivity
    field_simp
    ring
  have hscaled : c₁ * W₁ * (I * (μ * (τ - μ) ^ 2 / (τ + μ)) + 4 * μ ^ 2 * V / (τ + μ) ^ 2)
        + μ * W₁ * τ * I
      ≤ (1 / 2) * W₂ * (τ ^ 2 * I + V) + (1 / 2) * μ ^ 2 * W₁ * I
        - W₁ * ((τ - μ) ^ 2 * I * (1 / 2 - c₁ * μ / (τ + μ))
            + V * (1 / 2 - 4 * c₁ * μ ^ 2 / (τ + μ) ^ 2)) := by
    have hτ2V : 0 ≤ τ ^ 2 * I + V := by positivity
    have h1 : c₁ * W₁ * (I * (μ * (τ - μ) ^ 2 / (τ + μ)) + 4 * μ ^ 2 * V / (τ + μ) ^ 2)
          + μ * W₁ * τ * I
        = W₁ * (c₁ * (I * (μ * (τ - μ) ^ 2 / (τ + μ)) + 4 * μ ^ 2 * V / (τ + μ) ^ 2)
            + μ * τ * I) := by ring
    have h6 : (1 / 2) * W₁ * (τ ^ 2 * I + V) ≤ (1 / 2) * W₂ * (τ ^ 2 * I + V) :=
      mul_le_mul_of_nonneg_right (by linarith [hW12]) hτ2V
    have h7 : W₁ * ((1 / 2) * τ ^ 2 * I + (1 / 2) * V + (1 / 2) * μ ^ 2 * I)
        = (1 / 2) * W₁ * (τ ^ 2 * I + V) + (1 / 2) * μ ^ 2 * W₁ * I := by ring
    have h8 : W₁ * (c₁ * (I * (μ * (τ - μ) ^ 2 / (τ + μ)) + 4 * μ ^ 2 * V / (τ + μ) ^ 2)
            + μ * τ * I)
        = (1 / 2) * W₁ * (τ ^ 2 * I + V) + (1 / 2) * μ ^ 2 * W₁ * I
          - W₁ * ((τ - μ) ^ 2 * I * (1 / 2 - c₁ * μ / (τ + μ))
              + V * (1 / 2 - 4 * c₁ * μ ^ 2 / (τ + μ) ^ 2)) := by
      rw [h7] at hslackid
      linarith [hslackid]
    have h4 : W₁ * (c₁ * (I * (μ * (τ - μ) ^ 2 / (τ + μ)) + 4 * μ ^ 2 * V / (τ + μ) ^ 2)
            + μ * τ * I)
        ≤ (1 / 2) * W₂ * (τ ^ 2 * I + V) + (1 / 2) * μ ^ 2 * W₁ * I
          - W₁ * ((τ - μ) ^ 2 * I * (1 / 2 - c₁ * μ / (τ + μ))
              + V * (1 / 2 - 4 * c₁ * μ ^ 2 / (τ + μ) ^ 2)) := by
      rw [h8]
      linarith [h6]
    linarith [h1, h4]
  have hF' : c₁ * W₁ * Fb
      ≤ c₁ * W₁ * (I * (μ * (τ - μ) ^ 2 / (τ + μ)) + 4 * μ ^ 2 * V / (τ + μ) ^ 2) := by
    have h := mul_le_mul_of_nonneg_left hF (mul_nonneg hc₁.le hW1)
    have heq : c₁ * W₁ * (I * (μ * (τ - μ) ^ 2 / (τ + μ)) + 4 * μ ^ 2 / (τ + μ) ^ 2 * V)
        = c₁ * W₁ * (I * (μ * (τ - μ) ^ 2 / (τ + μ)) + 4 * μ ^ 2 * V / (τ + μ) ^ 2) := by
      ring
    rwa [heq] at h
  have hpair' : (1 / 2) * W₂ * (τ ^ 2 * I + V) - Epair ≤ Ps := by linarith [hpair]
  linarith [hF', hscaled, hfib, hpair', hbud, hkin]

end Work.BoseFixB1S
