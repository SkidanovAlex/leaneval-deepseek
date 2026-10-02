/-
# ZeroFreeTables — HBLemma8_8_proof

**Target.**  `Work.ZeroFreeTables.HBLemma8_8` (Heath-Brown 1992, Lemma 8.8, in the `λ₁`-floor form):

`∀ ε > 0, ∀ lamS > 0, ∃ q₀, ∀ q ≥ q₀, ∀ χ₁ ρ₁ (real, real, IsMin1WideAt 10, lamS ≤ λ₁, λ₁ ≤ 1),`
`Lam2Bound χ₁ ((12/11 - ε)·log(1/λ₁)) ∧ (λ₁ < 696/1000 → Lam2Bound χ₁ (745/1000))`.

## The argument

`εp := min ε (1/100)`, `εe := εp/100` (engine slack), `A := 11/24 + 4εe`, `Λ := log(1/lamS)`,
`K := (12/11)Λ + 2`.

Let `ρ` be a zero of `χ ∉ {χ₁,χ₁⁻¹}` with `λ(ρ) < (12/11 - εp)·log(1/λ₁) =: c`, and let
`(χ₂,ρ₂)` be the §6 second pair (`PairParam K`), so `λ₂ := λ(ρ₂) ≤ λ(ρ)`.

* **`λ₁ ≥ 696/1000`:** `λ(ρ) ≥ λ₁ ≥ 0.696` while `log(1/λ₁) ≤ 1/λ₁ - 1 ≤ 1000/696 - 1`, so
  `(12/11 - εp)·log(1/λ₁) ≤ 0.48 < 0.696`.
* **`797/10000 ≤ λ₁ < 696/1000`:** the Table 7 row cover (`Table7RowCover`) picks a row `p` with
  `λ₁ ≤ p.1` and `(12/11)·log(1/λ₁) ≤ p.2`, and `HBTable7_proof` gives `Lam2Bound χ₁ p.2`.
* **`λ₁ < 797/10000`, `λ₂ ≤ 15344/1000`:** `TentRowCover` picks a tent row `p = (X,b,c)`; the row
  certificate `TentRowCerts` together with the sharp criterion of `TentExtract` gives
  `tentFive X A b c < 0`, and monotonicity plus the five-term engine `TentFiveEngine` at the
  row's width contradict `0 ≤ tentFive X A λ₁ λ₂`.
* **`λ₂ > 15344/1000`:** with `2^j ≤ λ₂ < 2^{j+1}` (`j ≤ J := ⌈K⌉ + 2`), the dyadic widths
  `X j = 11/12 + 8εe + 2^{-j}` together with the crude criterion of `TentExtract` contradict
  `λ₂ < c`; the arithmetic input is `HB88DyadicArith`.

In both tent cases the `χ₁`-window hypothesis of the engine is supplied by `chi1Window_of_T23`:
for a real `χ₁` with real exceptional zero `ρ₁` and `λ₁ ≤ 2/5`, HB's Tables 2 and 3
(`HBTable2and3`) give `λ(u) ≥ (3/2)·log(1/λ₁) ≥ (12/11 - εp)·log(1/λ₁)` for every other zero `u`
of `χ₁` in the working region `|Im u| ≤ 1`.

The engine instantiations are the five row widths `{6/5, 23/20, 11/10, 21/20, 1}` and the dyadic
family (finite, bounded by `J`), all in the five-term flavour.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.HB88TentDefs
import Submission.Work.ZeroFreeTables.HB88TentIf
import Submission.Work.ZeroFreeTables.HBTable7_proof
import Submission.Work.ZeroFreeTables.HBTable7_of_count
import Submission.Work.ZeroFreeTables.HBTable2and3_all
import Submission.Work.ZeroFreeTables.PairParam_of_count
import Submission.Work.ZeroFreeTables.OtherLamCountLeK_all
import Submission.Work.ZeroFreeTables.row_contra_degenerate_weak
import Submission.Work.ZeroFreeTables.L52HypBoth
import Submission.Work.ZeroFreeTables.T7Cert
import Submission.Work.ZeroFreeTables.TentExtract
import Submission.Work.ZeroFreeTables.TentFiveEngine
import Submission.Work.ZeroFreeTables.TentRowCerts
import Submission.Work.ZeroFreeTables.TentRowCover
import Submission.Work.ZeroFreeTables.Table7RowCover
import Submission.Work.ZeroFreeTables.maximalityAt
import Submission.Work.ZeroFreeTables.TentRowsProps
import Submission.Work.ZeroFreeTables.HB88DyadicArith_proof
import Submission.Work.LinnikAreas.LFunction_eq_zero_of_zeroMult
import Submission.Work.LinnikAreas.OtherCharRepel.zeroMultStripPos

open DirichletCharacter Complex
open scoped Classical BigOperators

set_option maxHeartbeats 4000000

noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-! ## The second conjunct, from Table 7 -/

/-- **The second conjunct of HB Lemma 8.8**: `λ₁ < 0.696 → Lam2Bound χ₁ 0.745`, from Heath-Brown's
Table 7 (`HBTable7_proof`, sorry-free) at its row `(0.745, 0.745)`. -/
theorem HB88_second_conjunct :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 → lamOf q ρ₁ < 696 / 1000 →
        Lam2Bound χ₁ (745 / 1000) := by
  obtain ⟨q₀, hq₀⟩ := HBTable7_proof
  refine ⟨q₀, fun q hq _ χ₁ ρ₁ hmin hsq him hlt => ?_⟩
  have hp : ((745 / 1000 : ℝ), (745 / 1000 : ℝ)) ∈ tableR hbTable7 := by
    simp [tableR, hbTable7]
  refine lam2Bound_mono (hq₀ q hq χ₁ ρ₁ hmin hsq him hlt _ hp ?_) le_rfl
  linarith

/-! ## The five-term configuration at a fixed width -/

/-- **Unbundling of `TentFiveBodyAt`**: given the engine's conclusion at width `X` and the §6
second-pair data (ball minimality `hball`), assemble the shape used by the `Lam2Bound` argument.
The three maximalities `hmaxA`, `hmaxB`, `hmaxD` come from `hball` via `maxOfBallAux`; `hmaxC`
(the `χ₁`-window) is a hypothesis. -/
theorem fiveConfigUnbundle {q : ℕ} [NeZero q] (X A εe δ : ℝ) (hlogq : 0 < Real.log (q : ℝ))
    (hbody : TentFiveBodyAt X A εe δ q)
    (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ) (hmin : IsMin1WideAt 10 χ₁ ρ₁)
    (hsq : χ₁ * χ₁ = 1) (him : ρ₁.im = 0)
    (χ₂ : DirichletCharacter ℂ q) (ρ₂ : ℂ) [NeZero χ₁.conductor] [NeZero χ₂.conductor]
    (hχ₂ne1 : χ₂ ≠ 1) (hχ₂χ₁ : χ₂ ≠ χ₁) (hχ₂inv : χ₂ ≠ χ₁⁻¹)
    (hzm2 : zeroMult χ₂ ρ₂ ≠ 0) (hβ₂pos : 0 < ρ₂.re)
    (hball : ∀ (ψ : DirichletCharacter ℂ q) (u : ℂ), ψ ≠ 1 → ψ ≠ χ₁ → ψ ≠ χ₁⁻¹ →
      zeroMult ψ u ≠ 0 → |u.im| ≤ 2 * |ρ₂.im| + 1 → lamOf q ρ₂ ≤ lamOf q u)
    (hγ : |ρ₂.im| + 1 ≤ 10 * Real.log (q : ℝ))
    (hzero₁ : DirichletCharacter.LFunction χ₁ ((ρ₁.re : ℂ)) = 0)
    (hzero₂ : DirichletCharacter.LFunction χ₂ (((ρ₂.re : ℂ)) + ((ρ₂.im : ℂ)) * Complex.I) = 0)
    (hdivC : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|ρ₂.im| + 2))) ((ρ₁.re : ℂ)) ≠ 0)
    (hdivD : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₂.primitiveCharacter)
        (Metric.closedBall 0 (|ρ₂.im| + 2))) (((ρ₂.re : ℂ)) + ((ρ₂.im : ℂ)) * Complex.I) ≠ 0)
    (hd₁ : |1 - ρ₁.re| ≤ δ) (hd₂ : |1 - ρ₂.re| ≤ δ)
    (hpt₁ : |1 - ρ₁.re| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ))
    (hpt₂ : |1 - ρ₂.re| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ))
    (hwin : ∀ u : ℂ, DirichletCharacter.LFunction χ₁.primitiveCharacter u = 0 →
      |u.im| ≤ 1 → u = ((ρ₁.re : ℂ)) ∨ u.re ≤ ρ₂.re)
    (H₁ : Commons.NumberTheory.Linnik.L52Hyp χ₁ (1/8) εe δ)
    (H₂ : Commons.NumberTheory.Linnik.L52Hyp χ₂ (1/6) εe δ)
    (H₃ : Commons.NumberTheory.Linnik.L52Hyp (χ₁ * χ₂) (1/6) εe δ)
    (H₄ : Commons.NumberTheory.Linnik.L52Hyp (χ₁ * χ₂⁻¹) (1/6) εe δ) :
    0 ≤ tentFive X A (Real.log (q : ℝ) * (1 - ρ₁.re)) (Real.log (q : ℝ) * (1 - ρ₂.re)) := by
  have hχ₁ne1 : χ₁ ≠ 1 := hmin.1.1.1
  have hχ₁inv : χ₁⁻¹ = χ₁ := inv_eq_of_mul_eq_one_right hsq
  have hχ₁χ₂ne1 : χ₁ * χ₂ ≠ 1 := by
    intro h
    have h2 : χ₂ = χ₁⁻¹ := by
      have h3 : χ₁⁻¹ * (χ₁ * χ₂) = χ₁⁻¹ * 1 := by rw [h]
      rwa [← mul_assoc, inv_mul_cancel, one_mul, mul_one] at h3
    exact hχ₂χ₁ (by rw [h2, hχ₁inv])
  have hχ₁χ₂'a : χ₁ * χ₂ ≠ χ₁ := by
    intro h
    exact hχ₂ne1 (mul_left_cancel (show χ₁ * χ₂ = χ₁ * 1 by rw [h, mul_one]))
  have hχ₁χ₂'b : χ₁ * χ₂ ≠ χ₁⁻¹ := by rw [hχ₁inv]; exact hχ₁χ₂'a
  have hχ₂'invne1 : χ₂⁻¹ ≠ 1 := inv_ne_one.mpr hχ₂ne1
  have hχ₁χ₂'ne1 : χ₁ * χ₂⁻¹ ≠ 1 := by
    intro h
    have h2 : χ₂⁻¹ = χ₁⁻¹ := by
      have h3 : χ₁⁻¹ * (χ₁ * χ₂⁻¹) = χ₁⁻¹ * 1 := by rw [h]
      rwa [← mul_assoc, inv_mul_cancel, one_mul, mul_one] at h3
    exact hχ₂χ₁ (inv_inj.mp h2)
  have hχ₁χ₂'na : χ₁ * χ₂⁻¹ ≠ χ₁ := by
    intro h
    exact hχ₂'invne1 (mul_left_cancel (show χ₁ * χ₂⁻¹ = χ₁ * 1 by rw [h, mul_one]))
  have hχ₁χ₂'nb : χ₁ * χ₂⁻¹ ≠ χ₁⁻¹ := by rw [hχ₁inv]; exact hχ₁χ₂'na
  haveI : NeZero (χ₁ * χ₂).conductor := ⟨(χ₁ * χ₂).conductor_ne_zero⟩
  haveI : NeZero (χ₁ * χ₂⁻¹).conductor := ⟨(χ₁ * χ₂⁻¹).conductor_ne_zero⟩
  have hmaxA : ∀ u : ℂ, DirichletCharacter.LFunction (χ₁ * χ₂).primitiveCharacter u = 0 →
      |u.im| ≤ |ρ₂.im| + 1 → u.re ≤ ρ₂.re :=
    maxOfBallAux χ₁ ρ₂ hlogq hβ₂pos hball (χ₁ * χ₂) hχ₁χ₂ne1 hχ₁χ₂'a hχ₁χ₂'b
  have hmaxB : ∀ u : ℂ, DirichletCharacter.LFunction (χ₁ * χ₂⁻¹).primitiveCharacter u = 0 →
      |u.im| ≤ |ρ₂.im| + 1 → u.re ≤ ρ₂.re :=
    maxOfBallAux χ₁ ρ₂ hlogq hβ₂pos hball (χ₁ * χ₂⁻¹) hχ₁χ₂'ne1 hχ₁χ₂'na hχ₁χ₂'nb
  have hmaxD : ∀ u : ℂ, DirichletCharacter.LFunction χ₂.primitiveCharacter u = 0 →
      |u.im| ≤ |ρ₂.im| + 1 → u.re ≤ ρ₂.re :=
    maxOfBallAux χ₁ ρ₂ hlogq hβ₂pos hball χ₂ hχ₂ne1 hχ₂χ₁ hχ₂inv
  exact hbody χ₁ χ₂ hχ₁ne1 hχ₂ne1 hχ₂χ₁ hχ₁χ₂ne1 hχ₁χ₂'ne1 hd₁ hd₂ hγ hpt₁ hpt₂ hzero₁ hzero₂
    hmaxA hmaxB hwin hmaxD hdivC hdivD H₁ H₂ H₃ H₄

/-! ## The `χ₁`-window at height 1, from HB's Tables 2 and 3 -/

/-- **The `χ₁`-window.**  For a real character `χ₁` with a real exceptional zero `ρ₁`
(`IsMin1WideAt 10`, `λ₁ ≤ 2/5`), every *other* zero `u` of `χ₁` with `|Im u| ≤ 1` satisfies
`λ(u) ≥ (12/11 - ε)·log(1/λ₁)`.

This is the ε-free line `λ(u) ≥ (3/2)·log(1/λ₁)` of HB's Tables 2 and 3
(`Work.ZeroFreeTables.HBTable2and3_all`, the second conjunct at `λ₁ ≤ 2/5`), which dominates
`(12/11 - ε)·log(1/λ₁)` for `ε ≤ 1/100`. -/
theorem chi1Window_of_T23 (ε lamS : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 100) (hlamS : 0 < lamS) :
    ∃ qW : ℕ, ∀ q : ℕ, qW ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 →
      lamS ≤ lamOf q ρ₁ → lamOf q ρ₁ ≤ 2 / 5 →
      ∀ u : ℂ, zeroMult χ₁ u ≠ 0 → |u.im| ≤ 1 → u ≠ ρ₁ →
        (12 / 11 - ε) * Real.log (1 / lamOf q ρ₁) ≤ lamOf q u := by
  obtain ⟨q23, h23⟩ := HBTable2and3_all ε hε0 lamS hlamS
  refine ⟨q23, fun q hq _ χ₁ ρ₁ hmin hsq him hlamS' h25 u hzu himu hne => ?_⟩
  have hχ1 : χ₁ ≠ 1 := hmin.1.1.1
  have hconj : starRingEnd ℂ ρ₁ = ρ₁ := by
    refine Complex.ext ?_ ?_ <;> simp [Complex.conj_re, Complex.conj_im, him]
  have hbound : max ((3 / 2) * Real.log (1 / lamOf q ρ₁)) (1294 / 1000 : ℝ) ≤ lamOf q u :=
    (h23 q hq χ₁ ρ₁ hmin hsq him hlamS').2 h25 u ⟨hχ1, hzu, himu⟩ hne
      (fun _ => by rw [hconj]; exact hne)
  have hkey : (12 / 11 - ε) * Real.log (1 / lamOf q ρ₁)
      ≤ max ((3 / 2) * Real.log (1 / lamOf q ρ₁)) (1294 / 1000 : ℝ) := by
    rcases lt_or_ge (Real.log (1 / lamOf q ρ₁)) 0 with hL | hL
    · have h2 : (12 / 11 - ε) * Real.log (1 / lamOf q ρ₁) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) hL.le
      exact le_trans h2 (le_trans (by norm_num) (le_max_right _ _))
    · exact le_trans (mul_le_mul_of_nonneg_right (by linarith) hL) (le_max_left _ _)
  exact le_trans hkey hbound

/-! ## The main body -/

/-- **The main body of HB Lemma 8.8** (first conjunct), conditional on the `χ₁`-window
(`chi1Window_of_T23`), the Table 7 row cover (`Table7RowCover`), the tent row table sanity
(`TentRowsProps`) and the dyadic arithmetic (`HB88DyadicArith`). -/
theorem HB88_main_of
    (ε' lamS' : ℝ) (hε'0 : 0 < ε') (hε'1 : ε' ≤ 1 / 100) (hlamS' : 0 < lamS')
    (QW : ℕ)
    (hWin : ∀ q : ℕ, QW ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 →
      lamS' ≤ lamOf q ρ₁ → lamOf q ρ₁ ≤ 2 / 5 →
      ∀ u : ℂ, zeroMult χ₁ u ≠ 0 → |u.im| ≤ 1 → u ≠ ρ₁ →
        (12 / 11 - ε') * Real.log (1 / lamOf q ρ₁) ≤ lamOf q u)
    (hTable7 : ∀ lam1 : ℝ, 797 / 10000 ≤ lam1 → lam1 ≤ 696 / 1000 →
      ∃ p ∈ tableR hbTable7, lam1 ≤ p.1 ∧ (12 / 11) * Real.log (1 / lam1) ≤ p.2)
    (hRows : ∀ p : ℝ × ℝ × ℝ, p ∈ tentRows →
      p.1 ∈ ([6 / 5, 23 / 20, 11 / 10, 21 / 20, 1] : List ℝ) ∧ 0 < p.1 ∧ 0 ≤ p.2.1 ∧
        0 < p.2.2 ∧ A₀ < p.1 / 2)
    (hDya : ∀ (εe ε' L lam2 : ℝ) (j : ℕ), 0 < εe → 8 * εe ≤ ε' / 2 → 0 < ε' → ε' ≤ 1 / 100 →
      0 < L → lam2 / (12 / 11 - ε') ≤ L → (2 : ℝ) ^ j ≤ lam2 → lam2 < (2 : ℝ) ^ (j + 1) →
      15344 / 1000 ≤ lam2 →
      Real.exp (-L) < 1 / (2 : ℝ) ^ (j + 1) * lam2 ^ 2 *
        Real.exp (-((11 / 12 + 8 * εe + 1 / (2 : ℝ) ^ j) * lam2))) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 → lamS' ≤ lamOf q ρ₁ →
      Lam2Bound χ₁ ((12 / 11 - ε') * Real.log (1 / lamOf q ρ₁)) := by
  classical
  set εe : ℝ := ε' / 100 with hεedef
  have hεe0 : 0 < εe := by rw [hεedef]; linarith
  have hεe4 : 8 * εe ≤ 1 / 12 := by rw [hεedef]; linarith
  have hεe8 : 8 * εe ≤ ε' / 2 := by rw [hεedef]; linarith
  set A : ℝ := 11 / 24 + 4 * εe with hAdef
  have hA0 : A ≤ A₀ := by rw [hAdef, A₀, hεedef]; linarith
  obtain ⟨δ, hδ0, hδ1, qL, hL52⟩ := L52HypBoth εe hεe0
  obtain ⟨q5a, h5a⟩ := TentFiveEngine (6 / 5 : ℝ) εe δ (by norm_num) hεe0 hδ0 hδ1
  obtain ⟨q5b, h5b⟩ := TentFiveEngine (23 / 20 : ℝ) εe δ (by norm_num) hεe0 hδ0 hδ1
  obtain ⟨q5c, h5c⟩ := TentFiveEngine (11 / 10 : ℝ) εe δ (by norm_num) hεe0 hδ0 hδ1
  obtain ⟨q5d, h5d⟩ := TentFiveEngine (21 / 20 : ℝ) εe δ (by norm_num) hεe0 hδ0 hδ1
  obtain ⟨q5e, h5e⟩ := TentFiveEngine (1 : ℝ) εe δ (by norm_num) hεe0 hδ0 hδ1
  set Kv : ℝ := max ((12 / 11) * Real.log (1 / lamS')) 1 + 2 with hKvdef
  have hKv1 : (1 : ℝ) ≤ Kv := by
    rw [hKvdef]
    have := le_max_right ((12 / 11) * Real.log (1 / lamS')) 1
    linarith
  have hKvpos : 0 < Kv := lt_of_lt_of_le one_pos hKv1
  have hKvle : (12 / 11) * Real.log (1 / lamS') ≤ Kv := by
    rw [hKvdef]
    have := le_max_left ((12 / 11) * Real.log (1 / lamS')) 1
    linarith
  obtain ⟨Qpair, hpair⟩ := PairParam_of_count Kv hKvpos (OtherLamCountLeK_all Kv hKvpos)
  have hdyfam : ∀ j : ℕ, ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      TentFiveBodyAt (11 / 12 + 8 * εe + 1 / (2 : ℝ) ^ j) A εe δ q := fun j =>
    TentFiveEngine _ εe δ (by positivity) hεe0 hδ0 hδ1
  set J : ℕ := Nat.ceil Kv + 2 with hJdef
  have hdyU : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ j ≤ J,
      TentFiveBodyAt (11 / 12 + 8 * εe + 1 / (2 : ℝ) ^ j) A εe δ q := by
    have hall : ∀ N : ℕ, ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ j ≤ N,
        TentFiveBodyAt (11 / 12 + 8 * εe + 1 / (2 : ℝ) ^ j) A εe δ q := by
      intro N
      induction N with
      | zero =>
        obtain ⟨q₀, hq₀⟩ := hdyfam 0
        exact ⟨q₀, fun q hq j hj => by rw [Nat.le_zero.mp hj]; exact hq₀ q hq⟩
      | succ n ih =>
        obtain ⟨q₁, hq₁⟩ := ih
        obtain ⟨q₂, hq₂⟩ := hdyfam (n + 1)
        refine ⟨max q₁ q₂, fun q hq j hj => ?_⟩
        rcases Nat.lt_or_eq_of_le hj with h | h
        · exact hq₁ q (le_trans (le_max_left _ _) hq) j (Nat.lt_succ_iff.mp h)
        · rw [h]; exact hq₂ q (le_trans (le_max_right _ _) hq)
    exact hall J
  obtain ⟨qdy, hdy⟩ := hdyU
  obtain ⟨QT7, hT7⟩ := HBTable7_proof
  obtain ⟨qδ, hthδ⟩ := exists_log_mul_ge Kv δ hδ0
  obtain ⟨qpt, hthpt⟩ := exists_sqrt_loglog_ge Kv
  set Q : ℕ := Qpair + QT7 + qL + QW + q5a + q5b + q5c + q5d + q5e + qdy + 3 + qδ + qpt with hQdef
  have hQpair_ : Qpair ≤ Q := by rw [hQdef]; omega
  have hQT7_ : QT7 ≤ Q := by rw [hQdef]; omega
  have hqL_ : qL ≤ Q := by rw [hQdef]; omega
  have hQW_ : QW ≤ Q := by rw [hQdef]; omega
  have hq5a_ : q5a ≤ Q := by rw [hQdef]; omega
  have hq5b_ : q5b ≤ Q := by rw [hQdef]; omega
  have hq5c_ : q5c ≤ Q := by rw [hQdef]; omega
  have hq5d_ : q5d ≤ Q := by rw [hQdef]; omega
  have hq5e_ : q5e ≤ Q := by rw [hQdef]; omega
  have hqdy_ : qdy ≤ Q := by rw [hQdef]; omega
  have hQ3_ : 3 ≤ Q := by rw [hQdef]; omega
  have hqδ_ : qδ ≤ Q := by rw [hQdef]; omega
  have hqpt_ : qpt ≤ Q := by rw [hQdef]; omega
  refine ⟨Q, ?_⟩
  intro q hq _inst χ₁ ρ₁ hmin hsq him hlam1S
  have hqpair : Qpair ≤ q := le_trans hQpair_ hq
  have hqT7 : QT7 ≤ q := le_trans hQT7_ hq
  have hqL52 : qL ≤ q := le_trans hqL_ hq
  have hqW : QW ≤ q := le_trans hQW_ hq
  have hq5a' : q5a ≤ q := le_trans hq5a_ hq
  have hq5b' : q5b ≤ q := le_trans hq5b_ hq
  have hq5c' : q5c ≤ q := le_trans hq5c_ hq
  have hq5d' : q5d ≤ q := le_trans hq5d_ hq
  have hq5e' : q5e ≤ q := le_trans hq5e_ hq
  have hqdy' : qdy ≤ q := le_trans hqdy_ hq
  have hq3 : 3 ≤ q := le_trans hQ3_ hq
  have hq2 : 2 ≤ q := by omega
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hqδ' : qδ ≤ q := le_trans hqδ_ hq
  have hqpt' : qpt ≤ q := le_trans hqpt_ hq
  have hδb : (12 / 11) * Real.log (1 / lamS') ≤ δ * Real.log (q : ℝ) :=
    le_trans hKvle (hthδ q hqδ')
  have hptb : (12 / 11) * Real.log (1 / lamS') ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) :=
    le_trans hKvle (hthpt q hqpt')
  -- the five-term engine bodies at the row widths
  have hRowBody : ∀ X ∈ ([6 / 5, 23 / 20, 11 / 10, 21 / 20, 1] : List ℝ),
      TentFiveBodyAt X A εe δ q := by
    intro X hX
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl | rfl | rfl | rfl
    · exact h5a q hq5a'
    · exact h5b q hq5b'
    · exact h5c q hq5c'
    · exact h5d q hq5d'
    · exact h5e q hq5e'
  intro χ ρ hZ hχne hχneInv
  by_contra hcon
  rw [not_le] at hcon
  have hχ1ne1 : χ₁ ≠ 1 := hmin.1.1.1
  have hzm1 : zeroMult χ₁ ρ₁ ≠ 0 := hmin.1.1.2.1
  have hχne1 : χ ≠ 1 := hZ.1
  have hzmρ : zeroMult χ ρ ≠ 0 := hZ.2.1
  have himρ : |ρ.im| ≤ 1 := hZ.2.2
  have hstrip1 := Work.LinnikAreas.OtherCharRepel.zeroMultStripPos hq2 hχ1ne1 hzm1
  have hstripρ := Work.LinnikAreas.OtherCharRepel.zeroMultStripPos hq2 hχne1 hzmρ
  have hlam1pos : 0 < lamOf q ρ₁ := hstrip1.2.2
  have hlam1nn : 0 ≤ lamOf q ρ₁ := hlam1pos.le
  have hlamρpos : 0 < lamOf q ρ := hstripρ.2.2
  have hlam1_le : lamOf q ρ₁ ≤ lamOf q ρ := hmin.2 χ ρ hχne1 hzmρ (le_trans himρ (by norm_num))
  by_cases hbig : (696 / 1000 : ℝ) ≤ lamOf q ρ₁
  · -- the large case
    by_cases hbig1 : (1 : ℝ) ≤ lamOf q ρ₁
    · -- `λ₁ ≥ 1`: the target is non-positive
      have hLnon : Real.log (1 / lamOf q ρ₁) ≤ 0 :=
        Real.log_nonpos (by positivity) (by rw [div_le_one hlam1pos]; linarith)
      have htarget : (12 / 11 - ε') * Real.log (1 / lamOf q ρ₁) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) hLnon
      exact absurd (le_trans htarget hlamρpos.le) (not_le.mpr hcon)
    · -- `0.696 ≤ λ₁ < 1`
      have hLnn : 0 ≤ Real.log (1 / lamOf q ρ₁) := by
        apply Real.log_nonneg
        rw [le_div_iff₀ hlam1pos]
        linarith
      have htarget : (12 / 11 - ε') * Real.log (1 / lamOf q ρ₁) ≤ 696 / 1000 := by
        have h1 : Real.log (1 / lamOf q ρ₁) ≤ 1 / lamOf q ρ₁ - 1 :=
          Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 / lamOf q ρ₁)
        have h2 : 1 / lamOf q ρ₁ ≤ 1000 / 696 := by
          rw [div_le_div_iff₀ hlam1pos (by norm_num)]
          linarith only [hbig]
        have h3 : (12 / 11 - ε') * Real.log (1 / lamOf q ρ₁) ≤ (12 / 11) * (1000 / 696 - 1) := by
          have h4 : Real.log (1 / lamOf q ρ₁) ≤ 1000 / 696 - 1 := by linarith
          nlinarith only [hLnn, h4, hε'0]
        linarith
      exact absurd (le_trans htarget (le_trans hbig hlam1_le)) (not_le.mpr hcon)
  · have hmid : lamOf q ρ₁ < 696 / 1000 := not_le.mp hbig
    by_cases hmid2 : (797 / 10000 : ℝ) ≤ lamOf q ρ₁
    · -- the middle range: Table 7
      have hLnn : 0 ≤ Real.log (1 / lamOf q ρ₁) := Real.log_nonneg (by
        rw [le_div_iff₀ hlam1pos]
        linarith [le_of_lt hmid])
      obtain ⟨p, hp, hlp, hcp⟩ := hTable7 (lamOf q ρ₁) hmid2 (le_of_lt hmid)
      have hrow := hT7 q hqT7 χ₁ ρ₁ hmin hsq him hmid p hp hlp
      have htarget : (12 / 11 - ε') * Real.log (1 / lamOf q ρ₁) ≤ p.2 := by
        have h1 : (12 / 11 - ε') * Real.log (1 / lamOf q ρ₁)
            ≤ (12 / 11) * Real.log (1 / lamOf q ρ₁) := mul_le_mul_of_nonneg_right (by linarith) hLnn
        linarith
      have hrowp : p.2 ≤ lamOf q ρ := hrow χ ρ hZ hχne hχneInv
      exact absurd (le_trans htarget hrowp) (not_le.mpr hcon)
    · -- the small case
      have hsmall : lamOf q ρ₁ < 797 / 10000 := not_le.mp hmid2
      have hLpos : 0 < Real.log (1 / lamOf q ρ₁) := by
        apply Real.log_pos
        rw [lt_div_iff₀ hlam1pos]
        linarith
      have hLnn : 0 ≤ Real.log (1 / lamOf q ρ₁) := hLpos.le
      have hLleΛ : Real.log (1 / lamOf q ρ₁) ≤ Real.log (1 / lamS') := by
        apply Real.log_le_log (by positivity)
        exact one_div_le_one_div_of_le hlamS' hlam1S
      have hlamρlt : lamOf q ρ < (12 / 11) * Real.log (1 / lamOf q ρ₁) := by
        nlinarith only [hcon, hLnn, hε'0]
      have hlamρltK : lamOf q ρ < (12 / 11) * Real.log (1 / lamS') + 2 := by
        nlinarith only [hlamρlt, hLleΛ]
      have hlam1lt696 : lamOf q ρ₁ < 696 / 1000 := by linarith
      have hlamρltKv : lamOf q ρ < Kv := by rw [hKvdef]; linarith
      obtain ⟨χ₂, ρ₂, hχ₂ne1, hχ₂χ₁, hχ₂inv, hzm2, hl2ρ, hγ₂, hball⟩ :=
        hpair q hqpair χ₁ ρ₁ χ ρ hmin hsq him hlam1lt696 hZ hχne hχneInv hlamρltKv
      have hl2lt' : lamOf q ρ₂ < (12 / 11 - ε') * Real.log (1 / lamOf q ρ₁) :=
        lt_of_le_of_lt hl2ρ hcon
      have hstrip2 := Work.LinnikAreas.OtherCharRepel.zeroMultStripPos hq2 hχ₂ne1 hzm2
      have hβ₂pos : 0 < ρ₂.re := hstrip2.1
      have hl2nn : 0 ≤ lamOf q ρ₂ := le_of_lt hstrip2.2.2
      -- the point `ρ₁.re` as a complex number
      have hptrho1 : ((ρ₁.re : ℂ)) = ρ₁ := by
        refine Complex.ext ?_ ?_ <;> simp [him]
      have hptrho2 : (((ρ₂.re : ℂ)) + ((ρ₂.im : ℂ)) * Complex.I) = ρ₂ := by
        refine Complex.ext ?_ ?_ <;> simp
      have hsq_mul : χ₁ * χ₁ = 1 := by simpa [pow_two] using hsq
      -- the `χ₁`-window
      have hwin : ∀ u : ℂ, DirichletCharacter.LFunction χ₁.primitiveCharacter u = 0 →
          |u.im| ≤ 1 → u = ((ρ₁.re : ℂ)) ∨ u.re ≤ ρ₂.re := by
        intro u hu himu
        by_cases hcase : u = ((ρ₁.re : ℂ))
        · exact Or.inl hcase
        refine Or.inr ?_
        by_cases h0 : u.re ≤ 0
        · linarith [hβ₂pos, h0]
        push_neg at h0
        by_cases h1 : u.re < 1
        · have hzu : zeroMult χ₁ u ≠ 0 :=
            zeroMult_ne_zero_of_LFunction_zero χ₁ hχ1ne1 hu h0 h1
          have hune : u ≠ ρ₁ := by rw [← hptrho1]; exact hcase
          have hlu := hWin q hqW χ₁ ρ₁ hmin hsq him hlam1S (by linarith [hsmall])
            u hzu himu hune
          exact re_le_of_lamOf_le hlogq (le_of_lt (lt_of_lt_of_le hl2lt' hlu))
        · push_neg at h1
          exact absurd hu (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ₁.primitiveCharacter
            (Or.inl (Work.LinnikAreas.OtherCharRepel.primitiveCharacter_ne_one χ₁ hχ1ne1)) h1)
      -- the plumbing shared by both branches
      have hzero₁ : DirichletCharacter.LFunction χ₁ ((ρ₁.re : ℂ)) = 0 := by
        have hzm : zeroMult χ₁ ((ρ₁.re : ℂ)) ≠ 0 := by rw [hptrho1]; exact hzm1
        exact Work.LinnikAreas.LFunction_eq_zero_of_zeroMult χ₁ hχ1ne1 hstrip1.1 hstrip1.2.1 hzm
      have hzero₂ : DirichletCharacter.LFunction χ₂ (((ρ₂.re : ℂ)) + ((ρ₂.im : ℂ)) * Complex.I) = 0 := by
        rw [hptrho2]
        exact LFunction_eq_zero_of_zeroMult_complex χ₂ hχ₂ne1 hstrip2.1 hstrip2.2.1 hzm2
      have hγ : |ρ₂.im| + 1 ≤ 10 * Real.log (q : ℝ) := by linarith [abs_nonneg ρ₂.im]
      have hδb' : (12 / 11 - ε') * Real.log (1 / lamOf q ρ₁) ≤ δ * Real.log (q : ℝ) := by
        have h2 : (12 / 11 - ε') * Real.log (1 / lamOf q ρ₁)
            ≤ (12 / 11) * Real.log (1 / lamOf q ρ₁) :=
          mul_le_mul_of_nonneg_right (by linarith) hLnn
        have h3 : (12 / 11) * Real.log (1 / lamOf q ρ₁) ≤ (12 / 11) * Real.log (1 / lamS') :=
          mul_le_mul_of_nonneg_left hLleΛ (by norm_num)
        linarith [hδb]
      have hptb' : (12 / 11 - ε') * Real.log (1 / lamOf q ρ₁)
          ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := by
        have h2 : (12 / 11 - ε') * Real.log (1 / lamOf q ρ₁)
            ≤ (12 / 11) * Real.log (1 / lamOf q ρ₁) :=
          mul_le_mul_of_nonneg_right (by linarith) hLnn
        have h3 : (12 / 11) * Real.log (1 / lamOf q ρ₁) ≤ (12 / 11) * Real.log (1 / lamS') :=
          mul_le_mul_of_nonneg_left hLleΛ (by norm_num)
        linarith [hptb]
      have hlam1δ : lamOf q ρ₁ ≤ δ * Real.log (q : ℝ) :=
        le_trans hlam1_le (le_of_lt (lt_of_lt_of_le hcon hδb'))
      have hlam1pt : lamOf q ρ₁ ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) :=
        le_trans hlam1_le (le_of_lt (lt_of_lt_of_le hcon hptb'))
      have hlam2δ : lamOf q ρ₂ ≤ δ * Real.log (q : ℝ) := le_trans (le_of_lt hl2lt') hδb'
      have hlam2pt : lamOf q ρ₂ ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) :=
        le_trans (le_of_lt hl2lt') hptb'
      have hd₁ : |1 - ρ₁.re| ≤ δ := by
        have h1 : (1 - ρ₁.re) * Real.log (q : ℝ) ≤ δ * Real.log (q : ℝ) := by
          rw [← lamOf]; exact hlam1δ
        have h2 : 1 - ρ₁.re ≤ δ := (mul_le_mul_iff_of_pos_right hlogq).mp h1
        rw [abs_of_nonneg (by linarith [hstrip1.2.1])]
        exact h2
      have hd₂ : |1 - ρ₂.re| ≤ δ := by
        have h1 : (1 - ρ₂.re) * Real.log (q : ℝ) ≤ δ * Real.log (q : ℝ) := by
          rw [← lamOf]; exact hlam2δ
        have h2 : 1 - ρ₂.re ≤ δ := (mul_le_mul_iff_of_pos_right hlogq).mp h1
        rw [abs_of_nonneg (by linarith [hstrip2.2.1])]
        exact h2
      have hpt₁ : |1 - ρ₁.re| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) := by
        have h1 : (1 - ρ₁.re) * Real.log (q : ℝ) ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := by
          rw [← lamOf]; exact hlam1pt
        rw [abs_of_nonneg (by linarith [hstrip1.2.1]), le_div_iff₀ hlogq]
        linarith
      have hpt₂ : |1 - ρ₂.re| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) := by
        have h1 : (1 - ρ₂.re) * Real.log (q : ℝ) ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := by
          rw [← lamOf]; exact hlam2pt
        rw [abs_of_nonneg (by linarith [hstrip2.2.1]), le_div_iff₀ hlogq]
        linarith
      haveI : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
      haveI : NeZero χ₂.conductor := ⟨χ₂.conductor_ne_zero⟩
      have hdivC : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
          (Metric.closedBall 0 (|ρ₂.im| + 2))) ((ρ₁.re : ℂ)) ≠ 0 := by
        rw [hptrho1]
        refine divisor_ne_zero_of_zeroMult χ₁ hχ1ne1 ?_ hzm1
        rw [Metric.mem_closedBall, dist_zero_right]
        have h2 : ‖ρ₁‖ ^ 2 = ρ₁.re ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]; simp [him]; ring
        have h3 : ρ₁.re ^ 2 ≤ 1 := by nlinarith only [hstrip1.1, hstrip1.2.1]
        have h4 : ‖ρ₁‖ ^ 2 ≤ (|ρ₂.im| + 2) ^ 2 := by
          have h5 : (1 : ℝ) ≤ (|ρ₂.im| + 2) ^ 2 := by nlinarith only [abs_nonneg ρ₂.im]
          linarith [h2, h3, h5]
        rw [← Real.sqrt_sq (norm_nonneg ρ₁), ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ |ρ₂.im| + 2)]
        exact Real.sqrt_le_sqrt h4
      have hdivD : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₂.primitiveCharacter)
          (Metric.closedBall 0 (|ρ₂.im| + 2))) (((ρ₂.re : ℂ)) + ((ρ₂.im : ℂ)) * Complex.I) ≠ 0 := by
        rw [hptrho2]
        refine divisor_ne_zero_of_zeroMult χ₂ hχ₂ne1 ?_ hzm2
        rw [Metric.mem_closedBall, dist_zero_right]
        have h2 : ‖ρ₂‖ ^ 2 = ρ₂.re ^ 2 + ρ₂.im ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]; ring
        have h3 : ρ₂.re ^ 2 ≤ 1 := by nlinarith only [hstrip2.1, hstrip2.2.1]
        have h4 : ‖ρ₂‖ ^ 2 ≤ (|ρ₂.im| + 2) ^ 2 := by
          have h5 : ρ₂.im ^ 2 = |ρ₂.im| ^ 2 := by rw [sq_abs]
          have h6 : (|ρ₂.im| + 2) ^ 2 = |ρ₂.im| ^ 2 + (4 * |ρ₂.im| + 4) := by ring
          nlinarith only [abs_nonneg ρ₂.im, h2, h3, h5, h6]
        rw [← Real.sqrt_sq (norm_nonneg ρ₂), ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ |ρ₂.im| + 2)]
        exact Real.sqrt_le_sqrt h4
      have hχ₁χ₂ne1 : χ₁ * χ₂ ≠ 1 := by
        intro h
        refine hχ₂inv ?_
        have h' := congrArg (fun x : DirichletCharacter ℂ q => χ₁⁻¹ * x) h
        rwa [mul_one, ← mul_assoc, inv_mul_cancel, one_mul] at h'
      have hχ₁χ₂'ne1 : χ₁ * χ₂⁻¹ ≠ 1 := by
        intro h
        refine hχ₂χ₁ ?_
        have h' := congrArg (fun x : DirichletCharacter ℂ q => χ₁⁻¹ * x) h
        rw [mul_one, ← mul_assoc, inv_mul_cancel, one_mul] at h'
        exact inv_inj.mp h'
      have hχ₁χ₂'a : χ₁ * χ₂ ≠ χ₁ := by
        intro h
        exact hχ₂ne1 (mul_left_cancel (show χ₁ * χ₂ = χ₁ * 1 by rw [h, mul_one]))
      have hχ₁χ₂'b : χ₁ * χ₂ ≠ χ₁⁻¹ := by
        intro h
        exact hχ₂ne1 (by
          have h' := congrArg (fun x : DirichletCharacter ℂ q => χ₁ * x) h
          rw [← mul_assoc, mul_inv_cancel, hsq_mul, one_mul] at h'
          exact h')
      have hχ₁χ₂'na : χ₁ * χ₂⁻¹ ≠ χ₁ := by
        intro h
        exact hχ₂ne1 (inv_eq_one.mp (by
          have h' := congrArg (fun x : DirichletCharacter ℂ q => χ₁ * x) h
          rw [← mul_assoc, hsq_mul, one_mul] at h'
          exact h'))
      have hχ₁χ₂'nb : χ₁ * χ₂⁻¹ ≠ χ₁⁻¹ := by
        intro h
        exact hχ₂ne1 (inv_eq_one.mp (by
          have h' := congrArg (fun x : DirichletCharacter ℂ q => χ₁ * x) h
          rw [← mul_assoc, mul_inv_cancel, hsq_mul, one_mul] at h'
          exact h'))
      haveI : NeZero (χ₁ * χ₂).conductor := ⟨(χ₁ * χ₂).conductor_ne_zero⟩
      haveI : NeZero (χ₁ * χ₂⁻¹).conductor := ⟨(χ₁ * χ₂⁻¹).conductor_ne_zero⟩
      have hH1 : Commons.NumberTheory.Linnik.L52Hyp χ₁ (1 / 8) εe δ :=
        (hL52 q hqL52 χ₁ hχ1ne1).2 hsq
      have hH2 : Commons.NumberTheory.Linnik.L52Hyp χ₂ (1 / 6) εe δ :=
        (hL52 q hqL52 χ₂ hχ₂ne1).1
      have hH3 : Commons.NumberTheory.Linnik.L52Hyp (χ₁ * χ₂) (1 / 6) εe δ :=
        (hL52 q hqL52 (χ₁ * χ₂) hχ₁χ₂ne1).1
      have hH4 : Commons.NumberTheory.Linnik.L52Hyp (χ₁ * χ₂⁻¹) (1 / 6) εe δ :=
        (hL52 q hqL52 (χ₁ * χ₂⁻¹) hχ₁χ₂'ne1).1
      have hmaxA : ∀ u : ℂ, DirichletCharacter.LFunction (χ₁ * χ₂).primitiveCharacter u = 0 →
          |u.im| ≤ |ρ₂.im| + 1 → u.re ≤ ρ₂.re :=
        maxOfBallAux χ₁ ρ₂ hlogq hβ₂pos hball (χ₁ * χ₂) hχ₁χ₂ne1 hχ₁χ₂'a hχ₁χ₂'b
      have hmaxB : ∀ u : ℂ, DirichletCharacter.LFunction (χ₁ * χ₂⁻¹).primitiveCharacter u = 0 →
          |u.im| ≤ |ρ₂.im| + 1 → u.re ≤ ρ₂.re :=
        maxOfBallAux χ₁ ρ₂ hlogq hβ₂pos hball (χ₁ * χ₂⁻¹) hχ₁χ₂'ne1 hχ₁χ₂'na hχ₁χ₂'nb
      have hmaxD : ∀ u : ℂ, DirichletCharacter.LFunction χ₂.primitiveCharacter u = 0 →
          |u.im| ≤ |ρ₂.im| + 1 → u.re ≤ ρ₂.re :=
        maxOfBallAux χ₁ ρ₂ hlogq hβ₂pos hball χ₂ hχ₂ne1 hχ₂χ₁ hχ₂inv
      by_cases hsmall2 : lamOf q ρ₂ ≤ 15344 / 1000
      · -- the tent row table
        have hcover := TentRowCover (lamOf q ρ₁) (lamOf q ρ₂) hlam1pos (le_of_lt hsmall)
          (by first | nlinarith only [hl2lt', hLnn, hε'0] | nlinarith [hcon, hLnn, hε'0]) hsmall2
        obtain ⟨p, hp, hl1p, hl2p⟩ := hcover
        obtain ⟨hWmem, hXpos, hb0, hc0, hA2'⟩ := hRows p hp
        have hA2 : A < p.1 / 2 := lt_of_le_of_lt hA0 hA2'
        have hcert : tentFive p.1 A p.2.1 p.2.2 < 0 := by
          have hsh := TentRowCerts p hp
          simp only [TentRowCert] at hsh
          have h3 : (0 : ℝ) < p.2.2 ^ 3 := by positivity
          have hle : p.1 * (p.1 / 2 - A₀) * p.2.2 ^ 3 ≤ p.1 * (p.1 / 2 - A) * p.2.2 ^ 3 := by
            have h1 : p.1 / 2 - A₀ ≤ p.1 / 2 - A := by linarith [hA0]
            have h2 : 0 ≤ p.1 * p.2.2 ^ 3 := by positivity
            nlinarith only [h1, h2, hXpos, h3]
          exact (TentExtract p.1 A hXpos hA2).2.2.1 p.2.1 p.2.2 hb0 hc0 (lt_of_lt_of_le hsh hle)
        have heng := fiveConfigUnbundle (q := q) p.1 A εe δ hlogq (hRowBody p.1 hWmem) χ₁ ρ₁ hmin hsq_mul
          him χ₂ ρ₂ hχ₂ne1 hχ₂χ₁ hχ₂inv hzm2 hβ₂pos hball hγ hzero₁ hzero₂ hdivC hdivD hd₁ hd₂
          hpt₁ hpt₂ hwin hH1 hH2 hH3 hH4
        have hmono := (TentExtract p.1 A hXpos hA2).2.2.2.2.1 (lamOf q ρ₁) (lamOf q ρ₂) p.2.1 p.2.2
          hlam1nn hl1p hl2p
        rw [show Real.log (q : ℝ) * (1 - ρ₁.re) = lamOf q ρ₁ by rw [lamOf]; ring,
          show Real.log (q : ℝ) * (1 - ρ₂.re) = lamOf q ρ₂ by rw [lamOf]; ring] at heng
        exact absurd (le_trans heng hmono) (not_le.mpr hcert)
      · -- the dyadic family
        have hl21 : (1 : ℝ) ≤ lamOf q ρ₂ := by linarith
        set j : ℕ := Nat.log 2 ⌊lamOf q ρ₂⌋₊ with hjdef
        have hfloorpos : 0 < ⌊lamOf q ρ₂⌋₊ := Nat.floor_pos.mpr (by linarith)
        have hj1 : (2 : ℝ) ^ j ≤ lamOf q ρ₂ := by
          rw [hjdef]
          have h := Nat.pow_log_le_self 2 hfloorpos.ne'
          have h2 : ((⌊lamOf q ρ₂⌋₊ : ℕ) : ℝ) ≤ lamOf q ρ₂ := Nat.floor_le (by linarith)
          calc (2 : ℝ) ^ Nat.log 2 ⌊lamOf q ρ₂⌋₊
              = ((2 ^ Nat.log 2 ⌊lamOf q ρ₂⌋₊ : ℕ) : ℝ) := (Nat.cast_pow 2 _).symm
            _ ≤ ((⌊lamOf q ρ₂⌋₊ : ℕ) : ℝ) := by exact_mod_cast h
            _ ≤ lamOf q ρ₂ := h2
        have hj2 : lamOf q ρ₂ < (2 : ℝ) ^ (j + 1) := by
          rw [hjdef]
          have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊lamOf q ρ₂⌋₊
          have h2 : lamOf q ρ₂ < ((⌊lamOf q ρ₂⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
          have h3 : ((⌊lamOf q ρ₂⌋₊ : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ (Nat.log 2 ⌊lamOf q ρ₂⌋₊ + 1) := by
            have h4 : (⌊lamOf q ρ₂⌋₊ + 1 : ℕ) ≤ 2 ^ (Nat.log 2 ⌊lamOf q ρ₂⌋₊ + 1) :=
              Nat.succ_le_of_lt h
            calc ((⌊lamOf q ρ₂⌋₊ : ℕ) : ℝ) + 1 = ((⌊lamOf q ρ₂⌋₊ + 1 : ℕ) : ℝ) := by push_cast; ring
              _ ≤ ((2 ^ (Nat.log 2 ⌊lamOf q ρ₂⌋₊ + 1) : ℕ) : ℝ) := by exact_mod_cast h4
              _ = (2 : ℝ) ^ (Nat.log 2 ⌊lamOf q ρ₂⌋₊ + 1) := Nat.cast_pow 2 _
          linarith
        have hjJ : j ≤ J := by
          rw [hjdef, hJdef]
          have hKv2 : (12 / 11) * Real.log (1 / lamS') + 2 ≤ Kv := by
            rw [hKvdef]
            have := le_max_left ((12 / 11) * Real.log (1 / lamS')) 1
            linarith
          have hlamK : lamOf q ρ₂ ≤ Kv :=
            le_trans (le_of_lt (lt_of_le_of_lt hl2ρ hlamρltK)) hKv2
          have hceil : ((⌊lamOf q ρ₂⌋₊ : ℕ) : ℝ) ≤ ((Nat.ceil Kv : ℕ) : ℝ) := by
            have hl : ((⌊lamOf q ρ₂⌋₊ : ℕ) : ℝ) ≤ lamOf q ρ₂ := Nat.floor_le hstrip2.2.2.le
            have hc : Kv ≤ ((Nat.ceil Kv : ℕ) : ℝ) := Nat.le_ceil Kv
            linarith
          have h10 : ⌊lamOf q ρ₂⌋₊ ≤ Nat.ceil Kv := by exact_mod_cast hceil
          have h11 : Nat.log 2 ⌊lamOf q ρ₂⌋₊ ≤ ⌊lamOf q ρ₂⌋₊ := Nat.log_le_self 2 _
          omega
        set Xd : ℝ := 11 / 12 + 8 * εe + 1 / (2 : ℝ) ^ j with hXd
        have hXpos : 0 < Xd := by rw [hXd]; positivity
        have hA2 : A < Xd / 2 := by
          rw [hXd, hAdef]
          have h2 : (11 / 12 + 8 * εe + 1 / (2 : ℝ) ^ j) / 2 - (11 / 24 + 4 * εe)
              = 1 / (2 : ℝ) ^ (j + 1) := by
            rw [show (1 : ℝ) / (2 : ℝ) ^ (j + 1) = 1 / (2 : ℝ) ^ j / 2 by
              rw [pow_succ]; ring]
            ring
          have h3 : (0 : ℝ) < 1 / (2 : ℝ) ^ (j + 1) := by positivity
          linarith
        have hsplit : Xd / 2 - A = 1 / (2 : ℝ) ^ (j + 1) := by
          rw [hXd, hAdef]; field_simp; ring
        have hcert : tentFive Xd A (lamOf q ρ₁) (lamOf q ρ₂) < 0 := by
          have hcrude := (TentExtract Xd A hXpos hA2).1 (lamOf q ρ₁) (lamOf q ρ₂)
            hlam1nn hstrip2.2.2
          have hkey : lamOf q ρ₁ < 1 / (2 : ℝ) ^ (j + 1) * (lamOf q ρ₂) ^ 2 *
              Real.exp (-(Xd * lamOf q ρ₂)) := by
            have hLc : lamOf q ρ₂ / (12 / 11 - ε') ≤ Real.log (1 / lamOf q ρ₁) := by
              rw [div_le_iff₀ (by linarith : (0 : ℝ) < 12 / 11 - ε'), mul_comm]
              exact le_of_lt hl2lt'
            have h := hDya εe ε' (Real.log (1 / lamOf q ρ₁)) (lamOf q ρ₂) j hεe0 hεe8 hε'0 hε'1
              hLpos hLc hj1 hj2 (le_of_lt (not_le.mp hsmall2))
            have hexp : Real.exp (-(Real.log (1 / lamOf q ρ₁))) = lamOf q ρ₁ := by
              rw [Real.exp_neg, Real.exp_log (by positivity : (0 : ℝ) < 1 / lamOf q ρ₁), one_div,
                inv_inv]
            rw [hexp] at h
            simpa [hXd] using h
          have h3 : lamOf q ρ₁ * Xd * Real.exp (Xd * lamOf q ρ₂) / (lamOf q ρ₂) ^ 2
              < Xd * (Xd / 2 - A) := by
            rw [hsplit]
            have hpos2 : 0 < (lamOf q ρ₂) ^ 2 := by positivity
            have hstep : lamOf q ρ₁ * Real.exp (Xd * lamOf q ρ₂)
                < 1 / (2 : ℝ) ^ (j + 1) * (lamOf q ρ₂) ^ 2 := by
              have hmul := mul_lt_mul_of_pos_right hkey (Real.exp_pos (Xd * lamOf q ρ₂))
              have heq : Real.exp (-(Xd * lamOf q ρ₂)) * Real.exp (Xd * lamOf q ρ₂) = 1 := by
                rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
              rw [mul_assoc ((1 : ℝ) / (2 : ℝ) ^ (j + 1) * (lamOf q ρ₂) ^ 2)
                (Real.exp (-(Xd * lamOf q ρ₂))) (Real.exp (Xd * lamOf q ρ₂)), heq, mul_one] at hmul
              exact hmul
            rw [div_lt_iff₀ hpos2]
            have hh := mul_lt_mul_of_pos_left hstep hXpos
            linarith [hh]
          rw [tentFive]
          linarith [hcrude, h3]
        have hbody := hdy q hqdy' j hjJ
        have heng := fiveConfigUnbundle (q := q) Xd A εe δ hlogq hbody χ₁ ρ₁ hmin hsq_mul him χ₂ ρ₂
          hχ₂ne1 hχ₂χ₁ hχ₂inv hzm2 hβ₂pos hball hγ hzero₁ hzero₂ hdivC hdivD hd₁ hd₂ hpt₁ hpt₂
          hwin hH1 hH2 hH3 hH4
        rw [show Real.log (q : ℝ) * (1 - ρ₁.re) = lamOf q ρ₁ by rw [lamOf]; ring,
          show Real.log (q : ℝ) * (1 - ρ₂.re) = lamOf q ρ₂ by rw [lamOf]; ring] at heng
        exact absurd heng (not_le.mpr hcert)

/-! ## The target -/

theorem HBLemma8_8_proof : Work.ZeroFreeTables.HBLemma8_8 := by
  intro ε hε lamS hlamS
  set ε' : ℝ := min ε (1 / 100) with hε'def
  have hε'0 : 0 < ε' := lt_min hε (by norm_num)
  have hε'1 : ε' ≤ 1 / 100 := min_le_right _ _
  have hε'le : ε' ≤ ε := min_le_left _ _
  obtain ⟨qW, hWin⟩ := chi1Window_of_T23 ε' lamS hε'0 hε'1 hlamS
  obtain ⟨q₁, h₁⟩ := HB88_main_of ε' lamS hε'0 hε'1 hlamS qW hWin Table7RowCover
    (fun p hp => TentRowsProps p hp) HB88DyadicArith_proof
  obtain ⟨q₂, h₂⟩ := HB88_second_conjunct
  refine ⟨max (max q₁ q₂) 3, ?_⟩
  intro q hq _inst χ₁ ρ₁ hmin hsq him hlamS1 hlam1le1
  have hq₁ : q₁ ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have hq₂ : q₂ ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hq3 : 3 ≤ q := le_trans (le_max_right _ _) hq
  have hq2 : 2 ≤ q := by omega
  have hstrip := Work.LinnikAreas.OtherCharRepel.zeroMultStripPos hq2 hmin.1.1.1 hmin.1.1.2.1
  have hLnn : 0 ≤ Real.log (1 / lamOf q ρ₁) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hstrip.2.2]
    linarith
  refine ⟨lam2Bound_mono (h₁ q hq₁ χ₁ ρ₁ hmin hsq him hlamS1)
    (mul_le_mul_of_nonneg_right (by linarith) hLnn), ?_⟩
  exact h₂ q hq₂ χ₁ ρ₁ hmin hsq him

end Work.ZeroFreeTables
