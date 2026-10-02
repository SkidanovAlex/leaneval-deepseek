import Mathlib
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.LinnikAreas.DhRepel.dhTrianglePtH
import Submission.Work.LinnikContract.API.isZ_lambda_nonneg

namespace Work.ZeroFreeTables

/-!
# `HB63_TestFn`: HB Lemma 6.3 at the level of an abstract test function

This is Heath-Brown's *Lemma 6.3* (the two-point `F`-inequality of §6 of
*Zero-free regions for Dirichlet L-functions, and the least prime in an arithmetic
progression*, PLMS **64** (1992) 265–338), stated for an arbitrary test function
`T : TestFn` (i.e. an `f` satisfying Conditions 1 and 2 of §§5–7 together with its
Laplace transform) rather than for a particular one.

The analytic content is entirely in `Commons.NumberTheory.Linnik.lemma6_3_fullH`
(the free-box-height form of Lemma 6.3, proved in
`Submission/Work/LinnikAreas/DhRepel/dhTrianglePtH.lean`); the statement below is
that lemma with the triangle test function replaced by `T.f`, the two numerical
hypotheses `T.x₀ > 0`, `T.f_bound` read off `T`, and the conclusion rewritten in
the vocabulary of `Work.LinnikContract` (`lamOf`).

The two side conditions `β₁ ≤ 1`, `ρ'.re ≤ 1` that `lemma6_3_fullH` carries are
*not* hypotheses here: they follow from `hdiv₁`/`hdiv'` (which say that `β₁` and
`ρ'` are zeros of the completed `L`-function of the primitive character inducing
`χ`) together with the critical-strip theorem — see
`hb63_re_lt_one_of_LFunction_zero`.
-/

/-- The primitive character inducing a non-principal character is non-principal. -/
private lemma hb63_primitiveCharacter_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : χ.primitiveCharacter ≠ 1 := by
  intro h1
  refine hχ ?_
  rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h1]
  exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level

/-- A zero of the ordinary `L`-function of a non-principal character has real part `< 1`. -/
private lemma hb63_re_lt_one_of_LFunction_zero {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) {u : ℂ} (hu : DirichletCharacter.LFunction χ u = 0) : u.re < 1 := by
  by_contra h
  exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (not_lt.mp h)) hu

theorem HB63_TestFn (T : Work.ZeroFreeTables.TestFn) :
    ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ c : ℝ,
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      ∀ [NeZero q] (χ : DirichletCharacter ℂ q)
      (hχ : χ ≠ 1) (hreal : χ ^ 2 = 1) [NeZero χ.conductor] {β₁ : ℝ} {ρ' : ℂ}
      (hβ₁ : |1 - β₁| ≤ δ) (hβ' : |1 - ρ'.re| ≤ δ)
      {Hb : ℝ} (hHb : |ρ'.im| + δ ≤ Hb) (hγ10 : |ρ'.im| ≤ 10 * Real.log (q : ℝ))
      (hβ₁pt : |1 - β₁| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ))
      (hρ'pt : |1 - ρ'.re| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ))
      (hdiv₁ : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
          (Metric.closedBall 0 (|ρ'.im| + 2))) (β₁ : ℂ) ≠ 0)
      (hdiv' : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
          (Metric.closedBall 0 (|ρ'.im| + 2))) ρ' ≠ 0)
      (hne : ρ' ≠ (β₁ : ℂ))
      (hmult₁ : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
          (Metric.closedBall 0 (|ρ'.im| + 2))) (β₁ : ℂ) = 1)
      (hmax : ∀ u : ℂ, DirichletCharacter.LFunction χ.primitiveCharacter u = 0 →
          |u.im| ≤ Hb → u = (β₁ : ℂ) ∨ u.re ≤ ρ'.re)
      (hrect₁ : Work.LinnikContract.lamOf q (β₁ : ℂ) ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3)
      (hrect' : Work.LinnikContract.lamOf q ρ' ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3)
      (H : Commons.NumberTheory.Linnik.L52Hyp χ c ε δ),
      0 ≤ 2 * (∫ t in (0:ℝ)..T.x₀, Real.exp ((Work.LinnikContract.lamOf q ρ') * t) * T.f t)
        - 2 * (∫ t in (0:ℝ)..T.x₀, Real.exp ((Work.LinnikContract.lamOf q ρ' - Work.LinnikContract.lamOf q (β₁ : ℂ)) * t) * T.f t)
        - (∫ t in (0:ℝ)..T.x₀, T.f t) + (2 * c + 4 * ε) * T.f 0 := by
  intro ε hε δ hδ0 hδ1 c
  obtain ⟨B, hB0, hBnd⟩ := T.f_bound
  obtain ⟨q₀, hq₀⟩ := Commons.NumberTheory.Linnik.lemma6_3_fullH T.x₀ B c T.x₀_pos hB0
    (f := T.f) T.f_cont T.f_supp T.f_diff hBnd T.f0_pos T.f_nonneg
    (fun z hz => by simpa only [← T.Fc_spec z] using T.Fc_re_nonneg z hz)
    (ε := ε) hε (δ := δ) hδ0 hδ1
  refine ⟨q₀, ?_⟩
  intro q hq inst χ hχ hreal instc β₁ ρ' hβ₁ hβ' Hb hHb hγ10 hβ₁pt hρ'pt hdiv₁ hdiv' hne hmult₁
    hmax hrect₁ hrect' H
  have hχ' : χ.primitiveCharacter ≠ 1 := hb63_primitiveCharacter_ne_one hχ
  -- the two `re < 1` facts for the zeros, via the critical strip
  have hβ₁lo : 1 - δ ≤ β₁ := by have := (abs_le.mp hβ₁).2; linarith
  have hβ₁hi : β₁ ≤ 1 + δ := by have := (abs_le.mp hβ₁).1; linarith
  have hβ₁pos : 0 < β₁ := by linarith
  have hρ'lo : 1 - δ ≤ ρ'.re := by have := (abs_le.mp hβ').2; linarith
  have hρ'pos : 0 < ρ'.re := by linarith
  have hmem₁ : (β₁ : ℂ) ∈ Metric.closedBall (0 : ℂ) (|ρ'.im| + 2) := by
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> [linarith [abs_nonneg ρ'.im]; linarith [abs_nonneg ρ'.im]]
  have hmem' : ρ' ∈ Metric.closedBall (0 : ℂ) (|ρ'.im| + 2) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    refine le_trans (Complex.norm_le_abs_re_add_abs_im ρ') ?_
    have h1 : |ρ'.re| ≤ 2 := by
      rw [abs_le]
      exact ⟨by linarith [hρ'lo], by linarith [(abs_le.mp hβ').1, hδ1]⟩
    linarith [abs_nonneg ρ'.im]
  have hL₁ : DirichletCharacter.LFunction χ.primitiveCharacter (β₁ : ℂ) = 0 :=
    Commons.NumberTheory.Linnik.LFunction_eq_zero_of_divisor_completedL_ne_zero
      χ.primitiveCharacter hχ' hmem₁ (by simpa using hβ₁pos) hdiv₁
  have hL' : DirichletCharacter.LFunction χ.primitiveCharacter ρ' = 0 :=
    Commons.NumberTheory.Linnik.LFunction_eq_zero_of_divisor_completedL_ne_zero
      χ.primitiveCharacter hχ' hmem' (by simpa using hρ'pos) hdiv'
  have hβ₁le : β₁ ≤ 1 := (hb63_re_lt_one_of_LFunction_zero hχ' hL₁).le
  have hρ'le : ρ'.re ≤ 1 := (hb63_re_lt_one_of_LFunction_zero hχ' hL').le
  -- the `λ`-form of the rectangle hypotheses
  have hrect₁' : Real.log (q : ℝ) * (1 - β₁)
      ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 := by
    rw [Work.LinnikContract.lamOf, Complex.ofReal_re] at hrect₁
    rw [mul_comm]; exact hrect₁
  have hrect'' : Real.log (q : ℝ) * (1 - ρ'.re)
      ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 := by
    rw [Work.LinnikContract.lamOf] at hrect'
    rw [mul_comm]; exact hrect'
  have h := hq₀ hq χ hχ (by simpa only [pow_two] using hreal) hβ₁ hβ' hβ₁le hρ'le
    (Hh := Hb) hHb hγ10 hβ₁pt hρ'pt
    hdiv₁ (by rw [Complex.re_add_im]; exact hdiv') (by rw [Complex.re_add_im]; exact hne)
    hmult₁ hmax hrect₁' hrect'' H
  -- rewrite the conclusion of Lemma 6.3 into the shape of the statement
  have heq1 : (∫ t in (0:ℝ)..T.x₀,
        Real.exp (Real.log (q : ℝ) * (1 - ρ'.re) * t) * T.f t)
      = ∫ t in (0:ℝ)..T.x₀, Real.exp ((Work.LinnikContract.lamOf q ρ') * t) * T.f t := by
    apply intervalIntegral.integral_congr
    intro t ht
    simp only
    rw [Work.LinnikContract.lamOf]
    congr 2
    ring
  have heq2 : (∫ t in (0:ℝ)..T.x₀,
        Real.exp (-(Real.log (q : ℝ) * (1 - β₁) - Real.log (q : ℝ) * (1 - ρ'.re)) * t)
          * T.f t)
      = ∫ t in (0:ℝ)..T.x₀,
          Real.exp ((Work.LinnikContract.lamOf q ρ' - Work.LinnikContract.lamOf q (β₁ : ℂ)) * t)
            * T.f t := by
    apply intervalIntegral.integral_congr
    intro t ht
    simp only
    rw [Work.LinnikContract.lamOf, Work.LinnikContract.lamOf, Complex.ofReal_re]
    congr 2
    ring
  have heq4 : T.f 0 * (2 * c + 4 * ε) = (2 * c + 4 * ε) * T.f 0 := by ring
  rw [heq1, heq2, heq4] at h
  linarith only [h]

end Work.ZeroFreeTables
