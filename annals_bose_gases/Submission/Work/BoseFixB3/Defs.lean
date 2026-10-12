import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFix.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixB3/Defs` — Node D6, FS §7 `lem:Q3-splitting1`

The vocabulary of Fournais–Solovej §7 (`sec:3Q`, ll. 1448–1548 of
`Papers/fournais_solovej/final_v2.tex`): the momentum splitting of the
renormalised `3Q` term and the two cut-off words the proof of
`eq:ReduceQ3` needs beyond the LEAD-FROZEN `Submission/Work/BoseBoxFix/Defs.lean`
vocabulary (`Work.BoseBoxFix.NodeB3B` and its ingredients `lowMult`,
`lowSlot`, `q3lowWord`, `nPlusHB`).

## What FS §7 says

*Low/high momentum split.*  With `f ∈ C^∞` monotone, `f = 1` on `(−∞,1]`,
`f = 0` on `[2,∞)` (`Work.BoseBoxFix.LowCut`) and `f_L(s) = f(s/(K_L√(μa)))`,
the choice `K_L√(μa) = (d²ℓ)⁻¹` (`eq:KL_d`) gives `κ := (d²ℓ)⁻¹` and

  `Q_L = Q f_L(√−Δ)`,   `Q̄_L = Q (1 − f_L(√−Δ))`.

`highMult`/`highSlot` below are the corpus rendering of the **complementary**
multiplier `1 − f_L`: `highMult fc κ ℓ ψ x = ψ x − lowMult fc κ ℓ ψ x`, so that
the split of the `3Q` word is the pointwise identity
`ψ = lowMult … ψ + highMult … ψ` (see `Steps.lean`, `B3SplitRoot`).

*The extra words.*  `q3barWord` is the `Q̄_L`-part of `𝒬₃^ren`,

  `2 Σ_{i≠j} ⟨Q̄_{L,j}P_iΦ, w₁(x_i,x_j) Q_jQ_iΦ⟩`,

`q3omWord` is the `ω`-pairing FS obtain from the identity `eq:3Qto4Q`
`Q_jQ_i = B − ω(x_i−x_j)(P_jP_i+P_jQ_i+Q_jP_i)`,

  `2 Σ_{i≠j} ⟨Q̄_{L,j}P_iΦ, w₁(x_i,x_j) ω(x_i−x_j) P_jP_iΦ⟩`,

and `q3convWord` is FS's `Iℓ⁻³(n₀ Σ_j Q̄_{L,j} χ_Λ² P_j + h.c.)` produced by
`lem:Convolution`, with `I = ∫W₁ω`.

## Conventions

* `ℓ = sideAt μ (a v)`, `P = paramsAt μ (a v)`, `κ = (P.d²ℓ)⁻¹` — the
  abbreviations `ellAt`, `patAt`, `kapAt` reproduce the terms verbatim.
* everything is a **box-restricted** integral over `abox n ℓ`, so the
  whole-space/`CSBox` defect recorded in `BOSE_BOXNODES_LEAD.md` §1 cannot occur.
* the states are `Work.BoseKinLoc.BoxState n ℓ` (smooth, symmetric, nonzero, no
  support condition).
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixB3

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseKinLoc
open Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The parameter abbreviations (verbatim the terms in `NodeB3B`) -/

/-- FS `eq:def_ell`'s box side `ℓ = K_ℓ(μa)^{-1/2}` at FS's parameters. -/
def ellAt (μ : ℝ) (a : ℝ) : ℝ := sideAt μ a

/-- FS's parameter block at diluteness `μa³` (`Work.BoseBox.paramsAt`). -/
def patAt (μ : ℝ) (a : ℝ) : FSParams := paramsAt μ a

/-- FS `eq:KL_d`: the low-momentum cut-off `κ = K_L√(μa) = (d²ℓ)⁻¹`; the
frozen `NodeB3B` uses exactly this for `Q_L = Q f(√−Δ/κ)`. -/
def kapAt (μ : ℝ) (a : ℝ) : ℝ := ((paramsAt μ a).d ^ 2 * sideAt μ a)⁻¹

/-- FS's localised kernel `w_{1,0} = χ_Λ(x) W₁(x−y) χ_Λ(y)` at `u = 0`. -/
def w1At (μ : ℝ) (a : ℝ) (v : ℝ³ → ℝ) (h : ScatSol v) : ℝ³ → ℝ³ → ℝ :=
  wLoc (sideAt μ a) (g0 v h) 0

/-- FS's localised pair kernel `w_0(x,y) = χ_Λ(x) W(x−y) χ_Λ(y)`. -/
def wAt (μ : ℝ) (a : ℝ) (v : ℝ³ → ℝ) : ℝ³ → ℝ³ → ℝ :=
  wLoc (sideAt μ a) v 0

/-- FS's scattering solution `ω = w₀`, as a two-variable kernel. -/
def omAt {v : ℝ³ → ℝ} (h : ScatSol v) : ℝ³ → ℝ³ → ℝ := omC (Classical.choose h)

/-- `I := ∫W₁(y)ω(y) dy`, the convolution constant of `lem:Convolution`'s
application (`W₁ = wScaled ℓ (g₀ v h)`). -/
def convI (ℓ : ℝ) (v : ℝ³ → ℝ) (h : ScatSol v) : ℝ :=
  ∫ y : ℝ³, wScaled ℓ (g0 v h) y * Classical.choose h y

/-! ## 2. The complementary multiplier `1 − f_L` -/

/-- FS `sec:3Q`: `(1 − f_L)(ψ) = ψ − f_L(ψ)`, with `f_L` the corpus's
`lowMult` (the `p`-convention Fourier multiplier restricted to the box). -/
def highMult (fc : LowCut) (κ ℓ : ℝ) (ψ : ℝ³ → ℝ) (x : ℝ³) : ℝ :=
  ψ x - lowMult fc κ ℓ ψ x

/-- The slot-`j` lift of `highMult`: `(1 − f_L)` applied to the slot-`j` fibre. -/
def highSlot (fc : LowCut) (κ ℓ : ℝ) {n : ℕ} (j : Fin n) (Φ : X n → ℝ)
    (x : X n) : ℝ :=
  Φ x - lowSlot fc κ ℓ j Φ x

/-- The defining pointwise split `ψ = f_Lψ + (1−f_L)ψ`. -/
lemma low_add_high (fc : LowCut) (κ ℓ : ℝ) (ψ : ℝ³ → ℝ) (x : ℝ³) :
    lowMult fc κ ℓ ψ x + highMult fc κ ℓ ψ x = ψ x := by
  simp only [highMult]; ring

/-- The defining pointwise slot split `Φ = f_LΦ + (1−f_L)Φ`. -/
lemma lowSlot_add_highSlot (fc : LowCut) (κ ℓ : ℝ) {n : ℕ} (j : Fin n)
    (Φ : X n → ℝ) (x : X n) :
    lowSlot fc κ ℓ j Φ x + highSlot fc κ ℓ j Φ x = Φ x := by
  simp only [highSlot]; ring

/-- `highSlot` only depends on the slot-`j` fibre of its argument (as the
corpus's `lowSlot` does), so it agrees on functions with equal fibres. -/
lemma highSlot_congr {fc : LowCut} {κ ℓ : ℝ} {n : ℕ} {j : Fin n}
    {Φ Ψ : X n → ℝ} (hfib : ∀ x : X n, (fun z => Φ (Function.update x j z))
      = fun z => Ψ (Function.update x j z)) (x : X n) :
    highSlot fc κ ℓ j Φ x = highSlot fc κ ℓ j Ψ x := by
  have h1 : lowSlot fc κ ℓ j Φ x = lowSlot fc κ ℓ j Ψ x := by
    simp only [lowSlot, hfib x]
  have h2 : Φ x = Ψ x := by
    have := congrFun (hfib x) (x j)
    simpa [Function.update_self] using this
  simp only [highSlot, h1, h2]

/-! ## 2b. The slot-operator calculus

FS's `P_i`, `Q_i`, `Q_{L,i}`, `Q̄_{L,i}` are all *slot operators*: one-body
operators applied to the slot-`i` fibre of an `N`-body state.  `slotLift` is the
common lift, and `lowSlot`/`highSlot` are its instances for the two halves of the
momentum splitting.  This is the vocabulary in which FS `cl:advQ3sch`
(`eq:pq'pp`) is stated for a general `Q'` (`Q' = Q̄_L` in the application). -/

/-- The slot-`i` lift of a one-body operator `T`:
`(T_iΦ)(x) = T(Φ∘update x i)(x i)`. -/
def slotLift (T : (ℝ³ → ℝ) → (ℝ³ → ℝ)) {n : ℕ} (i : Fin n) (Φ : X n → ℝ)
    (x : X n) : ℝ :=
  T (fibre n i Φ x) (x i)

/-- `slotLift` is the corpus's `lowSlot` for `T = f_L`. -/
lemma slotLift_lowMult (fc : LowCut) (κ ℓ : ℝ) {n : ℕ} (i : Fin n)
    (Φ : X n → ℝ) (x : X n) :
    slotLift (lowMult fc κ ℓ) i Φ x = lowSlot fc κ ℓ i Φ x := rfl

/-- The fibre of a state at its own slot recovers the state. -/
lemma fibre_update_self {n : ℕ} (i : Fin n) (Φ : X n → ℝ) (x : X n) :
    fibre n i Φ x (x i) = Φ x := by
  simp [fibre, Function.update_self]

/-- `slotLift` is `highSlot` for `T = 1 − f_L`. -/
lemma slotLift_highMult (fc : LowCut) (κ ℓ : ℝ) {n : ℕ} (i : Fin n)
    (Φ : X n → ℝ) (x : X n) :
    slotLift (highMult fc κ ℓ) i Φ x = highSlot fc κ ℓ i Φ x := by
  have hx : Function.update x i (x i) = x := Function.update_eq_self i x
  simp only [slotLift, highMult, highSlot, lowSlot, fibre, hx]
  rfl

/-- `slotLift` of a pointwise-additive `T` is additive in the state. -/
lemma slotLift_add {T : (ℝ³ → ℝ) → (ℝ³ → ℝ)}
    (hT : ∀ ψ φ x, T (ψ + φ) x = T ψ x + T φ x) {n : ℕ} (i : Fin n)
    (Φ Ψ : X n → ℝ) (x : X n) :
    slotLift T i (Φ + Ψ) x = slotLift T i Φ x + slotLift T i Ψ x := by
  simp only [slotLift, fibre]
  exact hT _ _ _

/-! ## 3. The `Q̄_L`-part of the `3Q` word and the two auxiliary words -/

/-- **The `Q̄_L`-part of `𝒬₃^ren`**, i.e. `𝒬₃^ren − Q̃₃^{(1)}` where
`Q̃₃^{(1)}` is the frozen `q3lowWord`:

`2 Σ_{i≠j} ∫ Q̄_{L,j}(P_iΦ) · (Q_jQ_iΦ) · w₁(x_i,x_j)`.

(`Q̄_{L,j} = (1−f_L)Q_j`; the factor `2` carries the Hermitian conjugate of
FS `eq:DefQ3`.) -/
def q3barWord (fc : LowCut) (κ ℓ : ℝ) (w1 : ℝ³ → ℝ³ → ℝ) {n : ℕ}
    (Φ : X n → ℝ) : ℝ :=
  2 * ∑ p ∈ pairSet n, ∫ x in abox n ℓ,
    highSlot fc κ ℓ p.2 (aP ℓ p.1 (aQ ℓ p.2 Φ)) x * aQ ℓ p.2 (aQ ℓ p.1 Φ) x
      * w1 (x p.1) (x p.2)

/-- **FS's `ω`-pairing word** `2 Σ_{i≠j} ∫ Q̄_{L,j}(P_iΦ)·w₁(x_i,x_j)ω(x_i−x_j)·P_jP_iΦ`,
the remainder term of FS `eq:pq'pp-sf` after `eq:3Qto4Q`. -/
def q3omWord (fc : LowCut) (κ ℓ : ℝ) (w1 ω : ℝ³ → ℝ³ → ℝ) {n : ℕ}
    (Φ : X n → ℝ) : ℝ :=
  2 * ∑ p ∈ pairSet n, ∫ x in abox n ℓ,
    highSlot fc κ ℓ p.2 (aP ℓ p.1 Φ) x * aP ℓ p.2 (aP ℓ p.1 Φ) x
      * w1 (x p.1) (x p.2) * ω (x p.1) (x p.2)

/-- **FS's `Iℓ⁻³(n₀Σ_j Q̄_{L,j}χ_Λ²P_j + h.c.)` word** produced by
`lem:Convolution` (`χ_Λ = chiU ℓ 0`). -/
def q3convWord (fc : LowCut) (κ ℓ I : ℝ) {n : ℕ} (Φ : X n → ℝ) : ℝ :=
  I * ℓ ^ (-3 : ℤ) * ∑ i : Fin n, ∑ j : Fin n, ∫ x in abox n ℓ,
    aP ℓ i Φ x
      * highSlot fc κ ℓ j (fun y => chiU ℓ 0 (y j) ^ 2 * aP ℓ j Φ y) x

/-- The `Q̄_L`-mass `Σ_i ∫ |Q̄_{L,i}(Q_iΦ)|²` whose domination by `nPlusHB` is
FS `eq:QLs_giveNplusH`. -/
def highMass (fc : LowCut) (κ ℓ : ℝ) {n : ℕ} (Φ : X n → ℝ) : ℝ :=
  ∑ i : Fin n, ∫ x in abox n ℓ, (highSlot fc κ ℓ i (aQ ℓ i Φ) x) ^ 2

/-- The radial Fourier multiplier `F(√−Δ)` on the box `acube ℓ`, in the corpus's
`p`-convention (`kinFT`; `lowMult fc κ ℓ` is the instance `F = fc.f ∘ (·/κ)`):
extension by zero off the box, multiplication by `F(‖p‖)`, inverse transform at
`x` (real part). -/
def multOn (F : ℝ → ℝ) (ℓ : ℝ) (ψ : ℝ³ → ℝ) (x : ℝ³) : ℝ :=
  ((((2 * π) ^ 3)⁻¹ : ℝ) * ∫ p : ℝ³, Complex.exp (Complex.I * (inner ℝ p x : ℂ)) *
      ((F ‖p‖ : ℝ) : ℂ) *
        Submission.BoseGases.kinFT (fun z : ℝ³ => (((acube ℓ).indicator ψ z : ℝ) : ℂ)) p).re

/-! ## 3b. FS's localised kernels at `u = 0` are the corpus's `wPair`

The corpus's `wPair ℓ h x y = chiScale ℓ x · wScaled ℓ h (x−y) · chiScale ℓ y`
*already* carries the two `χ_Λ` factors, and `chiScale ℓ = chiU ℓ 0`.  Hence
`wLoc ℓ h 0 = wPair ℓ h = wPairC ℓ h`: the kernels of FS §7 are exactly the
corpus's `wPairC`, so **every proved lemma about `q3word ℓ (wPairC ℓ …)`,
`q4word ℓ (wPairC ℓ v) (omC w₀)` and their Cauchy–Schwarz estimates
(`Submission/Work/FSGroupQWords.lean`, `Submission/Work/QCrossQuarter.lean`)
applies verbatim to the §7 words of this chapter.** -/

lemma chiU_zero_eq_chiScale (ℓ : ℝ) (x : ℝ³) : chiU ℓ 0 x = chiScale ℓ x := by
  simp [chiU, chiScale, sub_zero]

lemma wLoc_zero_eq_wPair (ℓ : ℝ) (h : ℝ³ → ℝ) : wLoc ℓ h 0 = wPair ℓ h := by
  funext x y
  simp [wLoc, wPair, chiU, chiScale, sub_zero]

lemma wPairC_eq_wPair (ℓ : ℝ) (h : ℝ³ → ℝ) : wPairC ℓ h = wPair ℓ h := rfl

/-- FS's `w_{1,0}` is the corpus's `wPairC (g₀ v h)`. -/
lemma w1At_eq (μ a : ℝ) (v : ℝ³ → ℝ) (h : ScatSol v) :
    w1At μ a v h = wPairC (sideAt μ a) (g0 v h) := by
  rw [w1At, wLoc_zero_eq_wPair, wPairC_eq_wPair]

/-- FS's `w_0` is the corpus's `wPairC v`. -/
lemma wAt_eq (μ a : ℝ) (v : ℝ³ → ℝ) :
    wAt μ a v = wPairC (sideAt μ a) v := by
  rw [wAt, wLoc_zero_eq_wPair, wPairC_eq_wPair]

/-! ## 4. The AM–GM core of FS `eq:3Qto4Q` / `cl:advQ3sch`

The pointwise inequality that drives FS's Cauchy–Schwarz pairing of the `3Q` term
with the `4Q` square (`qcross_d13_pair_quarter` in the corpus, `Submission/Work/QCrossQuarter.lean`,
is its `w₁ = wPairC(g₀)`, `w = wPairC(v)` instance).  It is pure real arithmetic
and is stated here so that the Cauchy–Schwarz steps of §7 (`B3CSRoot`) can cite a
single budget instead of re-deriving the constants. -/

/-- **FS's `cl:advQ3sch` AM–GM budget.**  With `|ω| ≤ 1`, `0 ≤ W ≤ wt` and
`QQ := BB − ω·SS` (FS `eq:3Qto4Q`), the product of the `3Q`-pair amplitude with
the `4Q`-pair bracket is dominated by the `4Q` square plus the two mass terms:

`|F|·|QQ|·W ≤ (9/2)·F²·W + (1/2)·SS²·W + (1/16)·BB²·wt`.

The constants are FS's (the AM–GM `|F||BB| ≤ 4F² + (1/16)BB²` and
`|F||SS| ≤ (1/2)F² + (1/2)SS²`). -/
theorem amgm_budget {ω W wt F SS BB : ℝ} (hω : |ω| ≤ 1) (hW : 0 ≤ W) (hWwt : W ≤ wt) :
    |F| * |BB - ω * SS| * W
      ≤ (9 / 2) * F ^ 2 * W + (1 / 2) * SS ^ 2 * W + (1 / 16) * BB ^ 2 * wt := by
  have hBB : |BB - ω * SS| ≤ |BB| + |SS| := by
    calc |BB - ω * SS| = |BB + -(ω * SS)| := by rw [sub_eq_add_neg]
      _ ≤ |BB| + |-(ω * SS)| := abs_add_le _ _
      _ = |BB| + |ω * SS| := by rw [abs_neg]
      _ = |BB| + |ω| * |SS| := by rw [abs_mul]
      _ ≤ |BB| + 1 * |SS| := by
          have := mul_le_mul_of_nonneg_right hω (abs_nonneg SS)
          linarith
      _ = |BB| + |SS| := by ring
  have h1 : |F| * |BB| ≤ 4 * F ^ 2 + (1 / 16) * BB ^ 2 := by
    nlinarith [sq_nonneg (2 * |F| - |BB| / 4), abs_nonneg F, abs_nonneg BB,
      sq_abs F, sq_abs BB]
  have h2 : |F| * |SS| ≤ (1 / 2) * F ^ 2 + (1 / 2) * SS ^ 2 := by
    nlinarith [sq_nonneg (|F| - |SS|), abs_nonneg F, abs_nonneg SS, sq_abs F, sq_abs SS]
  have h3 : |F| * (|BB| + |SS|) * W
      ≤ (9 / 2) * F ^ 2 * W + (1 / 2) * SS ^ 2 * W + (1 / 16) * BB ^ 2 * W := by
    have h4 : |F| * (|BB| + |SS|) * W = (|F| * |BB|) * W + (|F| * |SS|) * W := by ring
    rw [h4]
    have e1 : (|F| * |BB|) * W ≤ (4 * F ^ 2 + (1 / 16) * BB ^ 2) * W :=
      mul_le_mul_of_nonneg_right h1 hW
    have e2 : (|F| * |SS|) * W ≤ ((1 / 2) * F ^ 2 + (1 / 2) * SS ^ 2) * W :=
      mul_le_mul_of_nonneg_right h2 hW
    linarith
  have h5 : (1 / 16) * BB ^ 2 * W ≤ (1 / 16) * BB ^ 2 * wt := by
    have : (0 : ℝ) ≤ (1 / 16) * BB ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left hWwt this
  calc |F| * |BB - ω * SS| * W
      ≤ |F| * (|BB| + |SS|) * W := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBB (abs_nonneg F)) hW
    _ ≤ (9 / 2) * F ^ 2 * W + (1 / 2) * SS ^ 2 * W + (1 / 16) * BB ^ 2 * W := h3
    _ ≤ (9 / 2) * F ^ 2 * W + (1 / 2) * SS ^ 2 * W + (1 / 16) * BB ^ 2 * wt := by
        linarith

/-! ## 5. Trivial positivity API -/

lemma cnPlus_nonneg {n : ℕ} {ℓ : ℝ} (Φ : X n → ℝ) : 0 ≤ cnPlus ℓ Φ :=
  Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg (aQ ℓ i Φ x)

/-- `indU` is a `0/1`-valued indicator. -/
lemma indU_nonneg (ℓ : ℝ) (u x : ℝ³) : 0 ≤ indU ℓ u x :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) x

lemma nPlusHB_nonneg {n : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (Φ : X n → ℝ) : 0 ≤ nPlusHB ℓ d Φ := by
  have h1 : (0 : ℝ) ≤ ℓ ^ (-3 : ℤ) := zpow_nonneg hℓ.le _
  refine mul_nonneg h1 (Finset.sum_nonneg fun i _ => integral_nonneg fun x => ?_)
  refine mul_nonneg (indU_nonneg ℓ 0 (x i)) ?_
  simpa [Work.BoseKinLoc.momForm] using momForm_nonneg (ℓ := ℓ) (d := d) 0
    (Work.BoseKinLoc.fibre n i Φ x)

lemma q4word_nonneg' {n : ℕ} {ℓ : ℝ} {w om : ℝ³ → ℝ³ → ℝ} (hℓ : 0 < ℓ) (hw : ∀ x y, 0 ≤ w x y)
    (Φ : X n → ℝ) : 0 ≤ q4word ℓ w om Φ := q4_nonneg hℓ hw

end Work.BoseFixB3
