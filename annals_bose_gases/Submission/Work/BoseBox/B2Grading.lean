import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBox.boxWordBddBelow_of_LHYBox
import Submission.Work.BoseBox.cWordIntegrable
import Submission.Work.BoseBox.perStateBox_of_LHYBox_compareBox
import Submission.Work.BoseBox.rayl_decomp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBox.B2Grading` — node `B2`: FS §6 `lem:LocMatrices` as a *replacement*, with the
absorption **proved**

## The shape of the node

FS's §6 (`lem:LocMatrices`, quoted from Lieb–Solovej's *localization of large
matrices*) does **not** state a bound on the box word: it states the existence of
a *replacement state* which

* has the same norm,
* is again a *low* state (at a threshold `J'` slightly below the hypothesis
  threshold `J` — the freedom `J` vs `J'` is exactly what FS use: "the freedom to
  take `J < K_B³` will be used in Lemma~`lem:LocMatrices`"),
* has the excited count `n₊` inside the matrix window `𝓜 = K_M(μa³)^{-1/4}`,
* and whose word exceeds the original word only by the Lieb–Solovej error
  `K K_𝓜^{-2} μ²ℓ³ (μa³)^{1/2}` (times the squared norm).

This module *names* that statement (`NodeB2g`, its two threshold arguments `J`
and `J'` being the hypothesis/conclusion thresholds) and **proves** the
composition with the restricted-class bound `NodeRestricted` and with the
arithmetic of `Windows.lean`:

* `boxBound_of_grading` — `NodeB2g` + `NodeRestricted` at `J'` give the box bound
  for all low states at `J`, with the *error coefficient raised by one*
  (`C ↦ C+1`): the Lieb–Solovej error is exactly the first unit of `Λ`'s error
  coefficient (`exists_lsError_le_slack`);
* `LHYBox_of_grading` — with the `B0` dichotomy, the same data give FS
  `thm:LHY-Box` at the shifted constant: `LHYBox v h η₀ (C+1)`.

The mechanism is the absorption `Λ(a,C+1) = Λ(a,C) − 4πaμ²(μa³)^{1/2+η₀}`
(`Lambda_add_one`): the Lieb–Solovej loss `K(μa³)^{1/2}/𝓜²` is *dominated* by
`4πa(μa³)^{1/2+η₀}` for small diluteness, because `𝓜^{-2} = (μa³)^{327/646}`
beats `(μa³)^{1/2}` by `(μa³)^{4/646}`.

## What is *not* here

The content of `NodeB2g` itself — the `n₊`-grading of the box word, the
Lieb–Solovej matrix theorem (`Work.UBBInputs3.ls_localisation_band2`, proved), the
`eq:dvapriori` bound on the first two off-diagonals and the recombination with the
a-priori `n₊`-window (`nPlusWindow_le_bigM`) — is node `B2` proper and is a
*named* hypothesis here, not an axiom: a caller who closes `NodeB2g` obtains the
box theorem with no further input from this module.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseBox


open Filter Metric MeasureTheory
open _root_.BoseGases
open Submission.BoseGases
open Work.UBB

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## 1. The node -/

/-- **`B2` — FS §6 `lem:LocMatrices` at the decoupled parameters, in its
*replacement* form.**

For every *low* state `Φ` (in the sense of the a-priori threshold `J`, FS
`eq:aprioriPsi`) at small diluteness, there is a state `Φ'` with

* the same centred-box norm,
* again low, at the threshold `J'`,
* excited count inside the matrix window `𝓜 = bigM(μa³)^{1/4}` (FS
  `eq:LocalizedNPlus`: `1_{[0,𝓜]}(n₊)Φ' = Φ'`, expressed as the quadratic-form
  inequality `n₊ ≤ 𝓜‖Φ'‖²`),
* and word exceeding `Φ`'s by at most
  `K·μ²ℓ³·(μa³)^{1/2}𝓜^{-2}·‖Φ‖²` — FS `eq:EnergyBound`, with the constant `∫v`
  of the paper absorbed into the free `K` (a fixed potential has a fixed `∫v`).

The hypothesis threshold is `J` (the *low* class of the input state) and the
conclusion threshold is `J'` with `J < J'`: low-at-`J'` is the *weaker* condition,
because `Θ(A,J,ρ) = −4πρ²A(1 − J√(ρA³))` is increasing in `J`.  The replacement's
shifted energy equals the original's plus the Lieb–Solovej error, so it is low
only at the *raised* threshold `J + err/(4π a μ²ℓ³√(μa³))` — this is exactly FS's
remark that the freedom to take `J < K_B³` will be used in `lem:LocMatrices` (the
raised threshold must still be `≤ K_B³`, which holds for small `μa³` since
`K_B³ = (μa³)^{-18/323} → ∞`).  The statement is therefore instantiable for every
`J' > J`: `𝓜^{-2} = (μa³)^{327/646} → 0`, so any fixed positive gap `J' − J` pays
the error. -/
def NodeB2g (v : ℝ³ → ℝ) (h : ScatSol v) (J J' : ℝ) : Prop :=
  ∃ K ε₀ : ℝ, 0 ≤ K ∧ 0 < ε₀ ∧
    ∀ μ : ℝ, 0 < μ → μ * (a v) ^ 3 ≤ ε₀ →
      ParamsOK (paramsAt μ (a v)) (μ * (a v) ^ 3) →
      ∀ n : ℕ, ∀ Φ : CSBox n (sideAt μ (a v)),
        IsLow (paramsAt μ (a v)) μ v h J n Φ →
        ∃ Φ' : CSBox n (sideAt μ (a v)),
          IsLow (paramsAt μ (a v)) μ v h J' n Φ'
          ∧ norm2N n (sideAt μ (a v)) (Φ' : X n → ℝ)
              = norm2N n (sideAt μ (a v)) (Φ : X n → ℝ)
          ∧ boxWordU n (sideAt μ (a v)) μ (paramsAt μ (a v)).d (paramsAt μ (a v)).s
                (paramsAt μ (a v)).eT (paramsAt μ (a v)).b v h 0 (Φ' : X n → ℝ)
              ≤ boxWordU n (sideAt μ (a v)) μ (paramsAt μ (a v)).d (paramsAt μ (a v)).s
                  (paramsAt μ (a v)).eT (paramsAt μ (a v)).b v h 0 (Φ : X n → ℝ)
                + K * μ ^ 2 * sideAt μ (a v) ^ 3
                    / bigM (paramsAt μ (a v)) (a v) μ ^ 2
                    * norm2N n (sideAt μ (a v)) (Φ : X n → ℝ)
          ∧ SpectralNPlusLe (sideAt μ (a v)) (bigM (paramsAt μ (a v)) (a v) μ)
              (Φ' : X n → ℝ)

/-! ## 2. The composition: the grading plus the restricted bound give the box bound -/

/-- **`B2` composed with `NodeRestricted`.**  The replacement state of `NodeB2g`
is restricted (`n₊ ≤ 𝓜`) and low at `J'`, so `NodeRestricted` applies to it; the
Lieb–Solovej error is absorbed by raising the target's error coefficient from `C`
to `C + 1` (`exists_lsError_le_slack`).  The result is the box bound for *all*
low states at the hypothesis threshold `J`.

No hypothesis on `J`, `J'` beyond `0 ≤ C`, `0 ≤ η₀ < 1/2` and `0 < a v` is
needed: the size condition `μa³ ≤ ε₀` is produced by the two inputs and the
absorption, so this step is where FS's parameter choice does its work. -/
theorem boxBound_of_grading {v : ℝ³ → ℝ} {h : ScatSol v} {J J' η₀ C : ℝ}
    (hav : 0 < a v) (hC : 0 ≤ C) (hη₀ : 0 ≤ η₀) (hη₂ : η₀ < 2 / 323) (hJ'pos : 0 < J')
    (hg : NodeB2g v h J J') (hr : NodeRestricted v h J' η₀ C) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ μ : ℝ, 0 < μ → μ * (a v) ^ 3 ≤ ε₀ →
        ParamsOK (paramsAt μ (a v)) (μ * (a v) ^ 3) →
        ∀ n : ℕ, ∀ Φ : CSBox n (sideAt μ (a v)),
          IsLow (paramsAt μ (a v)) μ v h J n Φ →
          BoxBound (paramsAt μ (a v)) μ v h η₀ (C + 1) n Φ := by
  obtain ⟨K, ε₁, hK0, hε₁, hg'⟩ := hg
  obtain ⟨ε₂, hε₂, habs⟩ := exists_lsError_le_slack (a := a v) hav hη₀ hη₂ hK0
  obtain ⟨ε₄, hε₄, hr'⟩ := hr
  refine ⟨min (J' ^ (-(323 / 18 : ℝ))) (min ε₁ (min ε₂ (min 1 ε₄))),
    lt_min (Real.rpow_pos_of_pos hJ'pos _)
      (lt_min hε₁ (lt_min hε₂ (lt_min one_pos hε₄))), ?_⟩
  intro μ hμ hle hpar n Φ hlow
  have ht0 : μ * (a v) ^ 3 ≤ J' ^ (-(323 / 18 : ℝ)) := le_trans hle (min_le_left _ _)
  have ht1 : μ * (a v) ^ 3 ≤ ε₁ :=
    le_trans hle (le_trans (min_le_right _ _) (min_le_left _ _))
  have ht2 : μ * (a v) ^ 3 ≤ ε₂ :=
    le_trans hle (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _)))
  have ht3 : μ * (a v) ^ 3 ≤ 1 :=
    le_trans hle (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have ht4 : μ * (a v) ^ 3 ≤ ε₄ :=
    le_trans hle (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
  have ht : 0 < μ * (a v) ^ 3 := by positivity
  obtain ⟨Φ', hlow', hnorm', hword', hplus'⟩ := hg' μ hμ ht1 hpar n Φ hlow
  have hguardJ' : J' ≤ (paramsAt μ (a v)).KB ^ 3 := KB_cube_ge hμ hav hJ'pos ht0
  have hrestr' : BoxBound (paramsAt μ (a v)) μ v h η₀ C n Φ' :=
    hr' μ hμ ht4 hpar hguardJ' n Φ' hlow' hplus'
  -- the absorption
  have hab := habs μ hμ ht2
  have hμ2 : 0 ≤ μ ^ 2 := sq_nonneg μ
  have hℓ3 : 0 ≤ sideAt μ (a v) ^ 3 := pow_nonneg (boxSide_pos hμ hav
    (fsXp_pos ht)).le 3
  have hmb : 0 ≤ bigM (paramsAt μ (a v)) (a v) μ ^ 2 := sq_nonneg _
  have hN : 0 ≤ norm2N n (sideAt μ (a v)) (Φ : X n → ℝ) := by
    dsimp [norm2N]
    exact integral_nonneg (fun x => sq_nonneg _)
  have herr : K * μ ^ 2 * sideAt μ (a v) ^ 3
          / bigM (paramsAt μ (a v)) (a v) μ ^ 2
          * norm2N n (sideAt μ (a v)) (Φ : X n → ℝ)
      ≤ 4 * π * (a v) * μ ^ 2 * sideAt μ (a v) ^ 3
        * (μ * (a v) ^ 3) ^ (1 / 2 + η₀) * norm2N n (sideAt μ (a v)) (Φ : X n → ℝ) := by
    have h1 : K / bigM (paramsAt μ (a v)) (a v) μ ^ 2
        ≤ 4 * π * (a v) * (μ * (a v) ^ 3) ^ (1 / 2 + η₀) := hab
    have hstep : K * μ ^ 2 * sideAt μ (a v) ^ 3
          / bigM (paramsAt μ (a v)) (a v) μ ^ 2
          * norm2N n (sideAt μ (a v)) (Φ : X n → ℝ)
        = (K / bigM (paramsAt μ (a v)) (a v) μ ^ 2)
          * (μ ^ 2 * sideAt μ (a v) ^ 3 * norm2N n (sideAt μ (a v)) (Φ : X n → ℝ)) := by
      ring
    have hstep2 : 4 * π * (a v) * (μ * (a v) ^ 3) ^ (1 / 2 + η₀)
          * (μ ^ 2 * sideAt μ (a v) ^ 3 * norm2N n (sideAt μ (a v)) (Φ : X n → ℝ))
        = 4 * π * (a v) * μ ^ 2 * sideAt μ (a v) ^ 3
          * (μ * (a v) ^ 3) ^ (1 / 2 + η₀) * norm2N n (sideAt μ (a v)) (Φ : X n → ℝ) := by
      ring
    rw [hstep, ← hstep2]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  -- the constant shift
  have hshift : Lambda (a v) (C + 1) η₀ μ
      = Lambda (a v) C η₀ μ - 4 * π * μ ^ 2 * (a v) * (μ * (a v) ^ 3) ^ (1 / 2 + η₀) :=
    Lambda_add_one _ _ _ _
  -- conclude
  have hgoal : sideAt μ (a v) ^ 3 * Lambda (a v) (C + 1) η₀ μ
        * norm2N n (sideAt μ (a v)) (Φ : X n → ℝ)
      ≤ boxWordU n (sideAt μ (a v)) μ (paramsAt μ (a v)).d (paramsAt μ (a v)).s
          (paramsAt μ (a v)).eT (paramsAt μ (a v)).b v h 0 (Φ : X n → ℝ) := by
    have hbase : sideAt μ (a v) ^ 3 * Lambda (a v) C η₀ μ
        * norm2N n (sideAt μ (a v)) (Φ' : X n → ℝ)
        ≤ boxWordU n (sideAt μ (a v)) μ (paramsAt μ (a v)).d (paramsAt μ (a v)).s
            (paramsAt μ (a v)).eT (paramsAt μ (a v)).b v h 0 (Φ' : X n → ℝ) := hrestr'
    rw [hnorm'] at hbase
    rw [hshift]
    nlinarith [hbase, hword', herr, hN]
  exact hgoal

/-! ## 3. The assembly: the grading data give FS `thm:LHY-Box` -/

/-- **`B8` with `B2` in its replacement form**: `NodeB2g` + `NodeRestricted` +
the `B0` dichotomy give FS `thm:LHY-Box` at the shifted error coefficient
`C + 1`.  (`NodeB1` is *not* an input here: the a-priori windows are consumed
inside the proof of the grading node `NodeB2g` itself, exactly as in FS, where
`thm:aprioribounds` precedes and feeds §6.) -/
theorem LHYBox_of_grading {v : ℝ³ → ℝ} {h : ScatSol v} {J J' η₀ C : ℝ}
    (hlhy : lhyC ≤ J) (hav : 0 < a v) (hC : 0 ≤ C) (hη₀ : 0 ≤ η₀) (hη₂ : η₀ < 2 / 323)
    (hJ'pos : 0 < J') (hg : NodeB2g v h J J') (hr : NodeRestricted v h J' η₀ C) :
    LHYBox v h η₀ (C + 1) := by
  obtain ⟨ε₀, hε₀, hbb⟩ := boxBound_of_grading hav hC hη₀ hη₂ hJ'pos hg hr
  have hC1 : 0 ≤ C + 1 := by linarith
  refine ⟨min ε₀ 1, lt_min hε₀ one_pos, ?_⟩
  intro μ hμ hsmall hpar n Φ
  have hsmall' : μ * (a v) ^ 3 ≤ ε₀ := le_trans hsmall (min_le_left _ _)
  have hKl : 0 < (paramsAt μ (a v)).Kl := by
    dsimp [paramsAt, fsParams, fsXp]
    exact Real.rpow_pos_of_pos (by positivity) _
  rcases nodeB0_dichotomy hlhy hC1 hη₀ hμ hav hKl Φ with hlow | hbox
  · exact hbb μ hμ hsmall' hpar n Φ hlow
  · exact hbox

/-! ## 4. The pressure-level corollary -/

/-- **The audit's `G` target from the grading data**: `NodeB2g` + `NodeRestricted`
+ `CompareBox` give `HBoxG` at the shifted constant, through the proved
`G`-node reduction (`HBoxG_of_perStateBox`) and the `C`+`B` assembly
(`perStateBox_of_LHYBox_compareBox_of_av_nonneg`). -/
theorem HBoxG_of_grading {v : ℝ³ → ℝ} {h : ScatSol v} {J J' η₀ η C : ℝ}
    (hlhy : lhyC ≤ J) (hav : 0 < a v) (hC : 0 ≤ C) (hη₀ : 0 ≤ η₀) (hη₂ : η₀ < 2 / 323)
    (hJ'pos : 0 < J')
    (hpar : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ParamsOK (fsParams t) t)
    (hg : NodeB2g v h J J') (hr : NodeRestricted v h J' η₀ C)
    (hcmp : ∀ᶠ ρ in nhdsWithin (0 : ℝ) (Set.Ioi 0), CompareBox v h ρ) :
    HBoxG v η₀ (C + 1 + 1) :=
  HBoxG_of_perStateBox
    (perStateBox_of_LHYBox_compareBox_of_av_nonneg (v := v) h (by linarith) hav.le
      hpar (LHYBox_of_grading hlhy hav hC hη₀ hη₂ hJ'pos hg hr) hcmp)

end Work.BoseBox
