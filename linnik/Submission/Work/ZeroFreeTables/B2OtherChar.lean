import Mathlib
import Submission.Work.ZeroFreeTables.API
import Submission.Work.ZeroFreeTables.hbLemma6_2_engine
import Submission.Work.ZeroFreeTables.testFn7_1
import Submission.Work.ZeroFreeTables.TestFn_F_antitone
import Submission.Work.ZeroFreeTables.TestFn_F_eq_integral
import Submission.Work.ZeroFreeTables.l52HypConvexityFixed
import Submission.Work.LinnikAreas.l31free.lemma3_1_free_gen
import Submission.Work.LinnikAreas.l31free.LFunction_bound_half_of_convexity
/-
# ZeroFreeTables — B2OtherChar

**The "other character" half of Heath-Brown 1992, Theorem 1** (D. R. Heath-Brown,
*Zero-free regions for Dirichlet L-functions, and the least prime in an arithmetic
progression*, PLMS (3) **64** (1992), 265-338, p. 3), in the form in which
`Work.ZeroFreeTables.HBTheorem1_second` consumes it:

> Let `(χ₁, ρ₁)` be the exceptional pair in the real case: `χ₁ ^ 2 = 1`, `ρ₁` real,
> `λ₁ = lamOf q ρ₁ < 348/1000`, and `λ₁` minimal among the non-principal zeros of
> height `≤ 10` (`IsMin1WideAt 10 χ₁ ρ₁`).  Then **no** other character `χ ≠ χ₁` has
> a zero `ρ` of the working region (`IsZ`, i.e. `|Im ρ| ≤ 1`) with `λ(ρ) < 348/1000`.

## The proof

The analytic input is Heath-Brown Lemma 6.2, in the engine form
`Work.ZeroFreeTables.hbLemma6_2_engine`:

`0 ≤ F(-λ₁) - F(0) - F(λ₂ - λ₁) + f(0)·3(c + ε)`,

for any test function `f` satisfying Conditions 1 and 2 whose Laplace transform is
`F` (`TestFn`), provided the log-derivative/window hypothesis `L52Hyp χ c ε δ` holds for
every non-principal `χ` mod `q`, `q ≥ q₀`.

* The hypothesis `L52Hyp` is supplied by `Work.ZeroFreeTables.l52HypConvexityFixed`
  (HB Lemma 3.1 fed with the *convexity* bound `LFunction_bound_half_of_convexity`,
  i.e. `φ = 1/2`, constant `1/4 + 10⁻⁶`, a single window radius `δ` for all characters).
  This is why the argument does not need Burgess.
* The test function is HB Lemma 7.1 optimal function at `θ = π/4` and `λ = 348/1000`
  (`Work.ZeroFreeTables.testFn7_1`): `F(0) = 4(1 - π/4)²`, `F(-λ) = 5 - 3π/2`,
  `f(0) = 2λ(π - 3)`.
* By HB section 7, `F(-λ₁) - F(λ₂ - λ₁) = ∫₀^{x₀} e^{λ₁t}(1 - e^{-λ₂t})f`, and
  `λ₁ ≤ λ₂ ≤ 348/1000` (minimality of `λ₁`, and the hypothesis on `λ₂`), so this is at
  most `F(-348/1000) - F(0)` (`b2_F_neg_sub_le`); hence
  `0 ≤ F(-348/1000) - 2F(0) + 3(c+ε)f(0)`.
* That expression equals `-3 + (5/2)π - π²/2 + (261/125)(c+ε)(π - 3)`, which is `< 0`
  for `c + ε ≤ 26/100` (`b2_num`, from `Real.pi_gt_d6`/`Real.pi_lt_d6`); here
  `c + ε = 1/4 + 10⁻⁶ + 10⁻³`.  Contradiction.

Note that the constants are exactly those for which the argument closes: with the
Burgess input (`φ = 1/3`, `3c = 1/2`) the margin is `0.032`, with convexity
(`φ = 1/2`, `3c = 3/4`) it is `0.007`; the numerical step is stated with the round
number `κ ≤ 26/100` on the coefficient of `f(0)`, which is what a reader of section 7
of the paper should verify.

All imported modules are sorry-free and axiom-clean.
-/

open DirichletCharacter Complex
open scoped Classical BigOperators

noncomputable section
namespace Work.ZeroFreeTables

/-- Comparison of the two `F`-terms of HB's Lemma 6.2 with the values at the top of
the `λ`-range. -/
private theorem b2_F_neg_sub_le (T : Work.ZeroFreeTables.TestFn) {lam1 lam2 lamT : ℝ}
    (h1 : 0 ≤ lam1) (h12 : lam1 ≤ lam2) (h2T : lam2 ≤ lamT) :
    T.F (-lam1) - T.F (lam2 - lam1) ≤ T.F (-lamT) - T.F 0 := by
  have hx0 : (0:ℝ) ≤ T.x₀ := le_of_lt T.x₀_pos
  have hint2 : ∀ c : ℝ, IntervalIntegrable (fun t : ℝ => Real.exp (-(c * t)) * T.f t)
      MeasureTheory.volume (0:ℝ) T.x₀ := by
    intro c
    refine ContinuousOn.intervalIntegrable_of_Icc hx0 ?_
    exact (((Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg))).continuousOn).mul
      (T.f_cont.mono (fun t ht => ht.1))
  rw [Work.ZeroFreeTables.TestFn_F_eq_integral T (-lam1),
      Work.ZeroFreeTables.TestFn_F_eq_integral T (lam2 - lam1),
      Work.ZeroFreeTables.TestFn_F_eq_integral T (-lamT),
      Work.ZeroFreeTables.TestFn_F_eq_integral T 0]
  rw [← intervalIntegral.integral_sub (hint2 (-lam1)) (hint2 (lam2 - lam1)),
      ← intervalIntegral.integral_sub (hint2 (-lamT)) (hint2 0)]
  refine intervalIntegral.integral_mono_on hx0
    ((hint2 (-lam1)).sub (hint2 (lam2 - lam1))) ((hint2 (-lamT)).sub (hint2 0)) ?_
  intro t ht
  have ht0 : 0 ≤ t := ht.1
  have h2nn : 0 ≤ lam2 := le_trans h1 h12
  have hfac : 0 ≤ 1 - Real.exp (-(lam2 * t)) := by
    have hle : Real.exp (-(lam2 * t)) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by nlinarith [ht0, h2nn])
    linarith
  have h12' : Real.exp (lam1 * t) ≤ Real.exp (lam2 * t) :=
    Real.exp_le_exp.mpr (by nlinarith [h12, ht0])
  have h2T' : Real.exp (lam2 * t) ≤ Real.exp (lamT * t) :=
    Real.exp_le_exp.mpr (by nlinarith [h2T, ht0])
  have hE2Ed : Real.exp (lam2 * t) * Real.exp (-(lam2 * t)) = 1 := by
    rw [← Real.exp_add, show lam2 * t + -(lam2 * t) = 0 by ring, Real.exp_zero]
  have key : Real.exp (lam1 * t) * (1 - Real.exp (-(lam2 * t))) * T.f t
      ≤ (Real.exp (lamT * t) - 1) * T.f t := by
    calc Real.exp (lam1 * t) * (1 - Real.exp (-(lam2 * t))) * T.f t
        ≤ Real.exp (lam2 * t) * (1 - Real.exp (-(lam2 * t))) * T.f t :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h12' hfac) (T.f_nonneg t)
      _ = (Real.exp (lam2 * t) - 1) * T.f t := by rw [mul_sub, hE2Ed, mul_one]
      _ ≤ (Real.exp (lamT * t) - 1) * T.f t :=
          mul_le_mul_of_nonneg_right (by linarith) (T.f_nonneg t)
  have hL : Real.exp (-(-lam1 * t)) = Real.exp (lam1 * t) := by
    rw [show -(-lam1 * t) = lam1 * t by ring]
  have hM : Real.exp (-((lam2 - lam1) * t))
      = Real.exp (lam1 * t) * Real.exp (-(lam2 * t)) := by
    rw [show -((lam2 - lam1) * t) = lam1 * t + (-(lam2 * t)) by ring, Real.exp_add]
  have hR : Real.exp (-(-lamT * t)) = Real.exp (lamT * t) := by
    rw [show -(-lamT * t) = lamT * t by ring]
  have hZ : Real.exp (-(0 * t)) = 1 := by
    rw [show -(0 * t) = 0 by ring, Real.exp_zero]
  calc Real.exp (-(-lam1 * t)) * T.f t - Real.exp (-((lam2 - lam1) * t)) * T.f t
      = Real.exp (lam1 * t) * (1 - Real.exp (-(lam2 * t))) * T.f t := by
        rw [hL, hM]; ring
    _ ≤ (Real.exp (lamT * t) - 1) * T.f t := key
    _ = Real.exp (-(-lamT * t)) * T.f t - Real.exp (-(0 * t)) * T.f t := by
        rw [hR, hZ]; ring

/-- The numerical core, with the values of HB Lemma 7.1's test function at
`θ = π/4`, `λ = 348/1000`. -/
private theorem b2_num (T : Work.ZeroFreeTables.TestFn)
    (hFneg : T.F (-((348:ℝ)/1000)) = 2 * Real.tan (Real.pi/4) ^ 2 + 3
      - 3 * (Real.pi/4) * Real.tan (Real.pi/4) - 3 * (Real.pi/4) * (Real.tan (Real.pi/4))⁻¹)
    (hF0 : T.F 0 = 2 * (1 + Real.tan (Real.pi/4) ^ 2) * (1 - (Real.pi/4) * (Real.tan (Real.pi/4))⁻¹) ^ 2)
    (hf0 : T.f 0 = (348:ℝ)/1000 * (1 + Real.tan (Real.pi/4) ^ 2)
      * ((Real.pi/4) * Real.tan (Real.pi/4) + 3 * (Real.pi/4) * (Real.tan (Real.pi/4))⁻¹ - 3))
    {κ : ℝ} (hκ : κ ≤ (26:ℝ)/100) :
    T.F (-((348:ℝ)/1000)) - T.F 0 - T.F 0 + T.f 0 * (3 * κ) < 0 := by
  rw [hFneg, hF0, hf0, Real.tan_pi_div_four]
  have hnum : -3 + (5/2) * Real.pi - Real.pi^2 / 2 + (261/125) * κ * (Real.pi - 3) < 0 := by
    nlinarith [Real.pi_gt_d6, Real.pi_lt_d6]
  norm_num at hnum ⊢
  linarith [hnum]

theorem B2OtherChar : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ χ : DirichletCharacter ℂ q) (ρ₁ ρ : ℂ),
    Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 →
    Work.LinnikContract.lamOf q ρ₁ < (348 : ℝ) / 1000 →
    Work.LinnikContract.IsZ χ ρ → χ ≠ χ₁ →
    Work.LinnikContract.lamOf q ρ < (348 : ℝ) / 1000 → False := by
  obtain ⟨δ, hδ0, hδ1, q₀L, hL52⟩ := Work.ZeroFreeTables.l52HypConvexityFixed
  have hθ0 : 0 < Real.pi / 4 := by positivity
  have hθ1 : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hlampos : (0:ℝ) < (348:ℝ)/1000 := by norm_num
  obtain ⟨T, -, hTf0, hTF0, hTFneg⟩ :=
    Work.ZeroFreeTables.testFn7_1 (Real.pi/4) ((348:ℝ)/1000) hθ0 hθ1 hlampos
  have hεpos : (0:ℝ) < (1:ℝ)/1000 := by norm_num
  obtain ⟨q₀E, hE⟩ := Work.ZeroFreeTables.hbLemma6_2_engine T
    ((1:ℝ)/4 + 1/1000000) ((1:ℝ)/1000) δ hεpos hδ0 hδ1
  refine ⟨max q₀E (max q₀L 2), ?_⟩
  intro q hq hNq χ₁ χ ρ₁ ρ hm hsq him hl1 hZ hne hl2
  haveI : NeZero q := hNq
  have hqE : q₀E ≤ q := le_trans (le_max_left _ _) hq
  have hqL : q₀L ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hq
  have hZ1 : Work.LinnikContract.IsZ χ₁ ρ₁ := hm.1.1
  have hχ1ne : χ₁ ≠ 1 := hZ1.1
  have hχne : χ ≠ 1 := hZ.1
  have hχ1inv : χ₁⁻¹ = χ₁ := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hsq)
  have hne2 : χ ≠ χ₁⁻¹ := by rw [hχ1inv]; exact hne
  have hβ1 : 0 < ρ₁.re ∧ ρ₁.re < 1 := by
    haveI hcon1 : NeZero χ₁.conductor := ⟨DirichletCharacter.conductor_ne_zero χ₁⟩
    exact Work.ZeroFreeTables.re_mem_Ioo_of_zeroMult χ₁ hχ1ne hZ1.2.1
  have hlogq : 0 ≤ Real.log (q:ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  have hlam1def : Work.LinnikContract.lamOf q ρ₁ = (1 - ρ₁.re) * Real.log (q:ℝ) := rfl
  have hlam2def : Work.LinnikContract.lamOf q ρ = (1 - ρ.re) * Real.log (q:ℝ) := rfl
  have hlam1nn : 0 ≤ Work.LinnikContract.lamOf q ρ₁ := by
    rw [hlam1def]; exact mul_nonneg (by linarith [hβ1.2]) hlogq
  have h12 : Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q ρ :=
    hm.2 χ ρ hχne hZ.2.1 (by have := hZ.2.2; linarith)
  have hlam1_1 : Work.LinnikContract.lamOf q ρ₁ ≤ 1 := by linarith
  have hlam2_1 : Work.LinnikContract.lamOf q ρ ≤ 1 := by linarith
  have hengine := hE q hqE χ₁ χ ρ₁ ρ
    (fun (χ' : DirichletCharacter ℂ q) (hinst : NeZero χ'.conductor) (hχ' : χ' ≠ 1) =>
      hL52 q hqL χ' hχ' ((1:ℝ)/1000) hεpos (by norm_num))
    hm hZ1 hZ hχ1ne hχne hne hne2 hlam1_1 hlam2_1
  have hcomp : T.F (-(Work.LinnikContract.lamOf q ρ₁))
      - T.F (Work.LinnikContract.lamOf q ρ - Work.LinnikContract.lamOf q ρ₁)
      ≤ T.F (-((348:ℝ)/1000)) - T.F 0 :=
    b2_F_neg_sub_le (lam1 := Work.LinnikContract.lamOf q ρ₁)
      (lam2 := Work.LinnikContract.lamOf q ρ) (lamT := (348:ℝ)/1000) T hlam1nn h12 (by linarith)
  have hnum : T.F (-((348:ℝ)/1000)) - T.F 0 - T.F 0
      + T.f 0 * (3 * (((1:ℝ)/4 + 1/1000000) + (1:ℝ)/1000)) < 0 :=
    b2_num (κ := ((1:ℝ)/4 + 1/1000000) + (1:ℝ)/1000) T hTFneg hTF0 hTf0 (by norm_num)
  have hfin : 0 ≤ T.F (-((348:ℝ)/1000)) - T.F 0 - T.F 0
      + T.f 0 * (3 * (((1:ℝ)/4 + 1/1000000) + (1:ℝ)/1000)) := by
    linarith [hengine, hcomp]
  linarith [hfin, hnum]

end Work.ZeroFreeTables
