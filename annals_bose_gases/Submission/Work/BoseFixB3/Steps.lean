import ChallengeDeps
import Submission.Work.BoseFixB3.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixB3.Steps` — the five steps of FS §7 `eq:ReduceQ3`

This module **names** the five statements that the proof of FS
`lem:Q3-splitting1` (`Papers/fournais_solovej/final_v2.tex` ll. 1488–1548)
splits into, in the chapter's own vocabulary (`Defs.lean`).  The assembly
`nodeB3B_of_steps` (`Assembly.lean`) derives the LEAD-FROZEN
`Work.BoseBoxFix.NodeB3B` from exactly these five, with no other input.

The chain (FS `eq:pq'pp-sf` → `eq:ReduceQ3`), with `ℓ = sideAt μ (a v)`,
`P = paramsAt μ (a v)`, `w₁ = wLoc ℓ (g₀ v h) 0`, `w = wLoc ℓ v 0`,
`ω = omC w₀`, `κ = (P.d²ℓ)⁻¹`, and `Ψ := (Φ : X n → ℝ)`:

1. `B3SplitRoot` — `q3word = q3lowWord + q3barWord` (FS: `𝒬₃^ren − Q̃₃^{(1)}`
   is the `Q̄_L`-part);
2. `B3CSRoot` — `cl:advQ3sch` with `Q' = Q̄_L` plus `eq:QLs_giveNplusH`
   (`ΣQ̄_LQ̄_L^* ≤ n₊^H`), after absorbing `εn₊` into `(b/200)ℓ⁻²n₊`:
   `q3bar + ¼q4 + (b/200)ℓ⁻²n₊ + q3omWord ≥ −Kℓ⁻²K_ℓ⁴n₊^H`;
3. `B3HAbsorbRoot` — the `con:eTdK` absorption of that `n₊^H` error into the
   positive `(b/200)ε_T(dℓ)⁻²n₊^H` term of `eq:ReduceQ3`; a **parameter**
   statement (it is true because at FS's choice `d²K_ℓ⁴ = X⁶ ≪ X^{23/4} = ε_T`);
4. `B3ConvRoot` — `lem:Convolution`: `−q3omWord ≥ −q3convWord − K μ²aℓ³(R²/ℓ²)‖Φ‖²`;
5. `B3EpsRoot` — FS's `ε₂`-Cauchy–Schwarz with `ε₂ = (K_ℓK_L)^{-2M̃}`,
   `M−1 ≤ 2M̃ ≤ M`:
   `−q3convWord ≥ −Kμ²aℓ³d^{2(M-1)}‖Φ‖² − (b/200)ε_T(dℓ)⁻²n₊^H`.

The `n₊^H` budget of `eq:ReduceQ3` is `(b/100)ε_T(dℓ)⁻²n₊^H`, split into the
two `(b/200)` halves used by (3) and (5); the `(b/100)ℓ⁻²n₊` budget is split
into the `(b/200)` half moved into `B3CSRoot` and the remaining half.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixB3

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseKinLoc
open Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 0. `Adm` monotonicity and the concrete parameter values -/

lemma Adm.mono {v : ℝ³ → ℝ} {ε ε' μ : ℝ} (h : Adm v ε μ) (hε : ε ≤ ε') : Adm v ε' μ :=
  ⟨h.1, le_trans h.2.1 hε, h.2.2⟩

/-- The concrete parameter block is FS's `fsParams` at the diluteness `μ(a v)³`. -/
lemma patAt_eq (μ a : ℝ) : patAt μ a = fsParams (μ * a ^ 3) := rfl

lemma patAt_b (μ a : ℝ) : (patAt μ a).b = bValue := rfl

lemma patAt_M (μ a : ℝ) : (patAt μ a).M = mValue := rfl

lemma patAt_d (μ a : ℝ) : (patAt μ a).d = fsXp (μ * a ^ 3) 6 := rfl

lemma patAt_eT (μ a : ℝ) : (patAt μ a).eT = fsXp (μ * a ^ 3) (23 / 4) := rfl

lemma patAt_Kl (μ a : ℝ) : (patAt μ a).Kl = fsXp (μ * a ^ 3) (-(3 / 2)) := rfl

/-- `bValue` is the positive universal gap coefficient `b = 1/16`. -/
lemma bValue_pos : 0 < bValue := by norm_num [bValue]

/-! ## 1. The five steps -/

/-- **Step 1** (FS §7, the definition of `Q_L`): the renormalised `3Q` word splits
into its low-momentum part `Q̃₃^{(1)}` (the frozen `Work.BoseBoxFix.q3lowWord`)
and the complementary part `q3barWord` built from `Q̄_L = Q(1−f_L)`. -/
def B3SplitRoot (v : ℝ³ → ℝ) (h : ScatSol v) (fc : LowCut) : Prop :=
  ∀ (μ : ℝ) (n : ℕ) (Φ : BoxState n (ellAt μ (a v))),
    q3word (ellAt μ (a v)) (w1At μ (a v) v h) (Φ : X n → ℝ)
      = q3lowWord fc (kapAt μ (a v)) (ellAt μ (a v)) (w1At μ (a v) v h) (Φ : X n → ℝ)
        + q3barWord fc (kapAt μ (a v)) (ellAt μ (a v)) (w1At μ (a v) v h) (Φ : X n → ℝ)

/-- **Step 2** (FS `cl:advQ3sch` with `Q' = Q̄_{L}`, `ε = cK_ℓ⁻²`, plus
`eq:QLs_giveNplusH` — this is FS `eq:pq'pp-sf`): the `Q̄_L`-part of the `3Q`
term together with `¼𝒬₄^ren`, the `(b/200)ℓ⁻²n₊` half-budget and the
`ω`-pairing word dominates `−Kℓ⁻²K_ℓ⁴n₊^H`.

The only hypothesis on the state is FS `eq:apriorinn+` *through* `n ≤ 2μℓ³`
(which is all FS use); there is no lowness, spectral or symmetry condition. -/
def B3CSRoot (v : ℝ³ → ℝ) (h : ScatSol v) (R : ℝ) (fc : LowCut) : Prop :=
  ∃ K ε₀ : ℝ, 0 ≤ K ∧ 0 < ε₀ ∧ ∀ (μ : ℝ), Adm v ε₀ μ →
    ∀ (n : ℕ) (Φ : BoxState n (ellAt μ (a v))),
      (n : ℝ) ≤ 2 * μ * ellAt μ (a v) ^ 3 →
      q3barWord fc (kapAt μ (a v)) (ellAt μ (a v)) (w1At μ (a v) v h) (Φ : X n → ℝ)
        + (1 / 4) * q4word (ellAt μ (a v)) (wAt μ (a v) v) (omAt h) (Φ : X n → ℝ)
        + (patAt μ (a v)).b / 200 * (ellAt μ (a v)) ^ (-2 : ℤ)
            * cnPlus (ellAt μ (a v)) (Φ : X n → ℝ)
        + q3omWord fc (kapAt μ (a v)) (ellAt μ (a v)) (w1At μ (a v) v h) (omAt h)
            (Φ : X n → ℝ)
      ≥ - K * (ellAt μ (a v)) ^ (-2 : ℤ) * (patAt μ (a v)).Kl ^ 4
          * nPlusHB (ellAt μ (a v)) (patAt μ (a v)).d (Φ : X n → ℝ)

/-- **Step 3** (FS `con:eTdK`): the `n₊^H` error `Kℓ⁻²K_ℓ⁴n₊^H` of step 2 is
dominated by the positive `(b/200)ε_T(dℓ)⁻²n₊^H` half-budget of `eq:ReduceQ3`.

This is a statement about FS's parameters only (no state, no `n`): it holds
because at `fsParams t` one has `d²K_ℓ⁴ = t^{1938/323}` and
`ε_T = t^{1857.25/323}`. -/
def B3HAbsorbRoot (v : ℝ³ → ℝ) : Prop :=
  ∀ C : ℝ, 0 ≤ C → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Adm v ε₀ μ →
    C * (patAt μ (a v)).d ^ 2 * (patAt μ (a v)).Kl ^ 4
      ≤ (patAt μ (a v)).b / 200 * (patAt μ (a v)).eT

/-- **Step 4** (FS `lem:Convolution`, the display after `eq:pq'pp-sf`):
the `ω`-pairing word is bounded by the convolution word with FS's error
`a n²ℓ⁻³(R²/ℓ²)`. -/
def B3ConvRoot (v : ℝ³ → ℝ) (h : ScatSol v) (R : ℝ) (fc : LowCut) : Prop :=
  ∃ K ε₀ : ℝ, 0 ≤ K ∧ 0 < ε₀ ∧ ∀ μ : ℝ, Adm v ε₀ μ →
    ∀ (n : ℕ) (Φ : BoxState n (ellAt μ (a v))),
      (n : ℝ) ≤ 2 * μ * ellAt μ (a v) ^ 3 →
      - q3omWord fc (kapAt μ (a v)) (ellAt μ (a v)) (w1At μ (a v) v h) (omAt h)
          (Φ : X n → ℝ)
        ≥ - q3convWord fc (kapAt μ (a v)) (ellAt μ (a v)) (convI (ellAt μ (a v)) v h)
              (Φ : X n → ℝ)
          - K * μ ^ 2 * a v * ellAt μ (a v) ^ 3
              * (R ^ 2 / ellAt μ (a v) ^ 2) * normB v μ n (Φ : X n → ℝ)

/-- **Step 5** (FS's `ε₂`-Cauchy–Schwarz, `ε₂ = (K_ℓK_L)^{-2M̃}` with
`M−1 ≤ 2M̃ ≤ M`): the convolution word dominates the `eq:ReduceQ3` error
`Kμ²aℓ³d^{2(M-1)}‖Φ‖²` up to the positive
`(b/200)ε_T(dℓ)⁻²n₊^H` half-budget. -/
def B3EpsRoot (v : ℝ³ → ℝ) (h : ScatSol v) (fc : LowCut) : Prop :=
  ∃ K ε₀ : ℝ, 0 ≤ K ∧ 0 < ε₀ ∧ ∀ μ : ℝ, Adm v ε₀ μ →
    ∀ (n : ℕ) (Φ : BoxState n (ellAt μ (a v))),
      (n : ℝ) ≤ 2 * μ * ellAt μ (a v) ^ 3 →
      - q3convWord fc (kapAt μ (a v)) (ellAt μ (a v)) (convI (ellAt μ (a v)) v h)
          (Φ : X n → ℝ)
        ≥ - K * μ ^ 2 * a v * ellAt μ (a v) ^ 3
              * (patAt μ (a v)).d ^ (2 * ((patAt μ (a v)).M - 1))
              * normB v μ n (Φ : X n → ℝ)
          - (patAt μ (a v)).b / 200 * (patAt μ (a v)).eT
              * ((patAt μ (a v)).d * ellAt μ (a v)) ^ (-2 : ℤ)
              * nPlusHB (ellAt μ (a v)) (patAt μ (a v)).d (Φ : X n → ℝ)

end Work.BoseFixB3
