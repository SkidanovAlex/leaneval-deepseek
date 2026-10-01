import Mathlib
import Submission.Work.LinnikAreas.Setup
import Submission.Work.ZeroDensity.Jutila.kernelSumHalf
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip

namespace Work.ZeroDensity.Jutila

open DirichletCharacter Complex
open scoped Classical BigOperators

set_option maxHeartbeats 2000000

/-!
# Linnik's density lemma (Jutila's Lemma 8), with an explicit absolute constant

`linnikDensityLemma` is the form of Jutila's Lemma 8 (*On Linnik's constant*, Math. Scand. 41
(1977), Lemma 8) needed by the near-line part of the far-zero reduction: the number of zeros of
`L(·, χ)` in the square `σ ≤ Re ρ ≤ 1`, `|Im ρ - T| ≤ (1-σ)/2`, counted with multiplicity, is at
most `C·((1-σ)·log(q(T+1)) + 1)` for an absolute constant `C`.

The proof proceeds by the classical Hadamard partial fraction, in the form already available in
this workspace (`Work.ZeroDensity.Jutila.kernelSumHalf`):

* `kernelSumHalf` bounds `Σ_ρ ord(ρ)·Re (1/(1+λ+iT-ρ))` by `1/λ + (1/2)log N + (1/2)log(2+T) + 4`
  for the primitive character `ψ` of level `N` and `λ = 1-σ > 0`;
* `kernelReLower` lower-bounds each summand of that sum coming from a zero of the box by
  `4/(17λ)`, so the box count is at most `(17λ/4)` times the kernel sum;
* `boxCountArith` is the elementary arithmetic converting
  `17/4 + (17λ/8)(log N + log(T+2)) + 17λ` into `64·(λ log(N(T+1)) + 1)`;
* `primitiveCharacterConductor` reduces a general non-principal `χ mod q` to its primitive
  character (of conductor `N | q`, so that `log N ≤ log q`).
-/

/-- Pointwise form of `Re (1/((a : ℂ) + iT - u))`. -/
private lemma one_div_sub_re_explicit (a T : ℝ) (u : ℂ) :
    (1 / (((a : ℝ) : ℂ) + Complex.I * (T : ℂ) - u)).re
      = (a - u.re) / ((a - u.re) ^ 2 + (T - u.im) ^ 2) := by
  have hzre : (((a : ℝ) : ℂ) + Complex.I * (T : ℂ) - u).re = a - u.re := by simp
  have hzim : (((a : ℝ) : ℂ) + Complex.I * (T : ℂ) - u).im = T - u.im := by simp
  rw [one_div, Complex.inv_re, Complex.normSq_apply, hzre, hzim]
  ring

/-- The primitive character inducing `χ` is non-trivial, and its level `χ.conductor` divides
(hence is at most) the level `q`.  All four facts are immediate from Mathlib's
`DirichletCharacter` API; they are packaged here because the main argument needs them
together. -/
theorem primitiveCharacterConductor {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (χ_ne_one : χ ≠ 1) :
    χ.primitiveCharacter ≠ 1 ∧ χ.conductor ∣ q ∧ 1 ≤ χ.conductor ∧ χ.conductor ≤ q := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  refine ⟨?_, χ.conductor_dvd_level, Nat.pos_of_ne_zero χ.conductor_ne_zero, ?_⟩
  · intro h
    have hp : (χ.primitiveCharacter).conductor = χ.conductor :=
      (DirichletCharacter.isPrimitive_def χ.primitiveCharacter).mp χ.primitiveCharacter_isPrimitive
    rw [h, DirichletCharacter.conductor_one] at hp
    exact χ_ne_one ((DirichletCharacter.eq_one_iff_conductor_eq_one (χ := χ)).mpr hp.symm)
  · exact Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level

/-- Elementary kernel bound: if `λ ≤ a - Re u ≤ 2λ` and `|Im u - T| ≤ λ/2` with `λ > 0`, then
`Re (1/(a + iT - u)) ≥ 4/(17λ)`.  Indeed `Re (1/(a+iT-u)) = (a-Re u)/((a-Re u)² + (T-Im u)²)`,
and over the box the numerator is `≥ λ` while the denominator is `≤ (2λ)² + (λ/2)² = 17λ²/4`. -/
theorem kernelReLower {a T lam : ℝ} (hlam : 0 < lam) {u : ℂ}
    (hu1 : lam ≤ a - u.re) (hu2 : a - u.re ≤ 2 * lam) (hu3 : |u.im - T| ≤ lam / 2) :
    4 / (17 * lam) ≤ (1 / (((a : ℝ) : ℂ) + Complex.I * (T : ℂ) - u)).re := by
  rw [one_div_sub_re_explicit]
  set x : ℝ := a - u.re with hx
  set y : ℝ := T - u.im with hy
  have hx1 : lam ≤ x := hu1
  have hx2 : x ≤ 2 * lam := hu2
  have hx0 : 0 < x := lt_of_lt_of_le hlam hx1
  have hy2 : y ^ 2 ≤ (lam / 2) ^ 2 := by
    have hy' : |y| ≤ lam / 2 := by
      rw [hy, abs_sub_comm]
      exact hu3
    have h := abs_le.mp hy'
    nlinarith [h.1, h.2]
  have hx2' : x ^ 2 ≤ (2 * lam) ^ 2 := pow_le_pow_left₀ (le_of_lt hx0) hx2 2
  have hden_le : x ^ 2 + y ^ 2 ≤ 17 * lam ^ 2 / 4 := by
    have h1 : (2 * lam) ^ 2 = 4 * lam ^ 2 := by ring
    have h2 : (lam / 2) ^ 2 = lam ^ 2 / 4 := by ring
    linarith [hx2', hy2, h1, h2]
  have hden_pos : 0 < x ^ 2 + y ^ 2 := by nlinarith [sq_nonneg y, hx0]
  rw [le_div_iff₀ hden_pos]
  have hkey : (4 / (17 * lam)) * (17 * lam ^ 2 / 4) = lam := by
    have hl : lam ≠ 0 := ne_of_gt hlam
    field_simp
  calc (4 / (17 * lam)) * (x ^ 2 + y ^ 2) ≤ (4 / (17 * lam)) * (17 * lam ^ 2 / 4) := by
        apply mul_le_mul_of_nonneg_left hden_le
        positivity
    _ = lam := hkey
    _ ≤ x := hx1

/-- Elementary arithmetic: with `λ ≥ 0`, `1 ≤ N ≤ q`, `2 ≤ q` and `T ≥ 1`,
`17/4 + (17λ/8)(log N + log(T+2)) + 17λ ≤ 64(λ log(q(T+1)) + 1)`. -/
theorem boxCountArith {lam N q T : ℝ} (hlam : 0 ≤ lam) (hN : 1 ≤ N) (hNq : N ≤ q)
    (hq : 2 ≤ q) (hT : 1 ≤ T) :
    17 / 4 + (17 * lam / 8) * (Real.log N + Real.log (2 + T)) + 17 * lam
      ≤ 64 * (lam * Real.log (q * (T + 1)) + 1) := by
  have hNpos : (0 : ℝ) < N := by linarith
  have hqpos : (0 : ℝ) < q := by linarith
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hTp1 : (0 : ℝ) < T + 1 := by linarith
  set L : ℝ := Real.log (q * (T + 1)) with hL
  have hlogN : Real.log N ≤ Real.log q := Real.log_le_log hNpos hNq
  have hlogq0 : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hLsplit : L = Real.log q + Real.log (T + 1) := by
    rw [hL, Real.log_mul (ne_of_gt hqpos) (ne_of_gt hTp1)]
  have hlog2T : Real.log (2 + T) ≤ 2 * Real.log (T + 1) := by
    have h1 : 2 + T ≤ 2 * (T + 1) := by linarith
    have h2 : Real.log (2 + T) ≤ Real.log (2 * (T + 1)) := Real.log_le_log (by linarith) h1
    rw [Real.log_mul (by norm_num) (ne_of_gt hTp1)] at h2
    have h3 : Real.log 2 ≤ Real.log (T + 1) := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hL4 : 68 / 239 ≤ L := by
    have h4 : Real.log 4 ≤ L := by
      rw [hL]
      have hmul : (4 : ℝ) ≤ q * (T + 1) := by
        nlinarith [mul_le_mul hq (by linarith : (2 : ℝ) ≤ T + 1) (by norm_num) (by linarith)]
      exact Real.log_le_log (by norm_num : (0 : ℝ) < 4) hmul
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    have h2 : (68 : ℝ) / 239 ≤ 2 * Real.log 2 := by
      have h := Real.log_two_gt_d9
      nlinarith
    calc 68 / 239 ≤ 2 * Real.log 2 := h2
      _ = Real.log 4 := hlog4.symm
      _ ≤ L := h4
  have hlogsum : Real.log N + Real.log (2 + T) ≤ 2 * L := by
    rw [hLsplit]
    linarith [hlogN, hlog2T, hlogq0]
  have h1 : (17 * lam / 8) * (Real.log N + Real.log (2 + T)) ≤ (17 * lam / 8) * (2 * L) :=
    mul_le_mul_of_nonneg_left hlogsum (by linarith)
  have h17 : 17 * lam ≤ ((239 : ℝ) / 4) * L * lam := by
    have hL' : 17 ≤ ((239 : ℝ) / 4) * L := by nlinarith [hL4]
    calc 17 * lam ≤ ((239 : ℝ) / 4) * L * lam := mul_le_mul_of_nonneg_right hL' hlam
      _ = (239 : ℝ) / 4 * L * lam := by ring
  have hfinal : 17 / 4 + (17 * lam / 8) * (2 * L) + 17 * lam ≤ 64 * (lam * L + 1) := by
    nlinarith [h17, hlam]
  calc 17 / 4 + (17 * lam / 8) * (Real.log N + Real.log (2 + T)) + 17 * lam
      ≤ 17 / 4 + (17 * lam / 8) * (2 * L) + 17 * lam := by linarith
    _ ≤ 64 * (lam * L + 1) := hfinal
    _ = 64 * (lam * Real.log (q * (T + 1)) + 1) := by rw [hL]

/-- Bookkeeping step of the proof: the multiplicity-weighted count of the zeros of the completed
`L`-function of a primitive non-trivial `ψ` in the box `σ ≤ Re ρ ≤ 1`, `|Im ρ - T| ≤ (1-σ)/2` is
at most `(17(1-σ)/4)` times the divisor-weighted sum of the kernel `Re (1/(1+λ+iT-ρ))` over the
ball of radius `2(T+2)` (`λ = 1-σ`).

Every zero of the ball lies in the open strip `0 < Re < 1`, so the summand of that kernel is
non-negative, and a zero of the box contributes at least `4/(17λ)` by `kernelReLower`. -/
private lemma boxSum_le_kernelSum {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (hψ : ψ ≠ 1)
    (hψprim : ψ.IsPrimitive) {σ T : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hT : 1 ≤ T) :
    (∑ᶠ ρ : ℂ, if analyticOrderNatAt (completedLFunction ψ) ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧
        |ρ.im - T| ≤ (1 - σ) / 2 then (analyticOrderNatAt (completedLFunction ψ) ρ : ℝ) else 0)
      ≤ (17 * (1 - σ) / 4) * (∑ᶠ u : ℂ,
          (((MeromorphicOn.divisor (completedLFunction ψ) (Metric.closedBall 0 (2 * (T + 2)))) u : ℤ) : ℝ) *
            (1 / (((1 + (1 - σ) : ℝ) : ℂ) + Complex.I * (T : ℂ) - u)).re) := by
  classical
  have hdiff : Differentiable ℂ (completedLFunction ψ) :=
    DirichletCharacter.differentiable_completedLFunction hψ
  have hAn : AnalyticOnNhd ℂ (completedLFunction ψ) (Metric.closedBall 0 (2 * (T + 2))) :=
    Commons.Analysis.Complex.analyticOnNhd_closedBall_of_differentiable hdiff _
  -- every zero in the box lies in the ball
  have huball : ∀ u : ℂ, analyticOrderNatAt (completedLFunction ψ) u ≠ 0 → σ ≤ u.re →
      u.re ≤ 1 → |u.im - T| ≤ (1 - σ) / 2 → u ∈ Metric.closedBall (0 : ℂ) (2 * (T + 2)) := by
    intro u hord hσu hu1 him
    have hzu : completedLFunction ψ u = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero hord
    have hstrip := Commons.NumberTheory.DirichletCharacter.zerosInStrip ψ hψ hψprim u hzu
    rw [Metric.mem_closedBall, dist_zero_right]
    have himabs : |u.im| ≤ T + 1 / 2 := by
      have hTabs : |T| = T := abs_of_nonneg (by linarith)
      calc |u.im| = |(u.im - T) + T| := by ring_nf
        _ ≤ |u.im - T| + |T| := abs_add_le _ _
        _ ≤ (1 - σ) / 2 + T := by rw [hTabs]; linarith
        _ ≤ T + 1 / 2 := by linarith
    have hrere : |u.re| ≤ 1 := abs_le.mpr ⟨by linarith [hstrip.1.le], hu1⟩
    calc ‖u‖ ≤ |u.re| + |u.im| := Complex.norm_le_abs_re_add_abs_im u
      _ ≤ 1 + (T + 1 / 2) := by linarith
      _ ≤ 2 * (T + 2) := by linarith
  -- the pointwise domination
  have hpoint : ∀ u : ℂ,
      (if analyticOrderNatAt (completedLFunction ψ) u ≠ 0 ∧ σ ≤ u.re ∧ u.re ≤ 1 ∧
          |u.im - T| ≤ (1 - σ) / 2 then (analyticOrderNatAt (completedLFunction ψ) u : ℝ) else 0)
        ≤ (17 * (1 - σ) / 4) *
            ((((MeromorphicOn.divisor (completedLFunction ψ) (Metric.closedBall 0 (2 * (T + 2)))) u : ℤ) : ℝ) *
              (1 / (((1 + (1 - σ) : ℝ) : ℂ) + Complex.I * (T : ℂ) - u)).re) := by
    intro u
    by_cases hbox : analyticOrderNatAt (completedLFunction ψ) u ≠ 0 ∧ σ ≤ u.re ∧ u.re ≤ 1 ∧
        |u.im - T| ≤ (1 - σ) / 2
    · rw [if_pos hbox]
      obtain ⟨hord, hσu, hu1, him⟩ := hbox
      have hzu : completedLFunction ψ u = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero hord
      have hstrip := Commons.NumberTheory.DirichletCharacter.zerosInStrip ψ hψ hψprim u hzu
      have hlampos : 0 < 1 - σ := by
        rcases lt_or_ge (0 : ℝ) (1 - σ) with hpos | hnonpos
        · exact hpos
        · exfalso
          have h0 : (1 : ℝ) - σ = 0 := le_antisymm hnonpos (by linarith)
          have hure : u.re = 1 := le_antisymm hu1 (by linarith [h0, hσu])
          linarith [hstrip.2, hure]
      have hDval : (MeromorphicOn.divisor (completedLFunction ψ)
            (Metric.closedBall 0 (2 * (T + 2)))) u = ↑(analyticOrderNatAt (completedLFunction ψ) u) :=
        Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast hAn (huball u hord hσu hu1 him)
      have hcast : (((analyticOrderNatAt (completedLFunction ψ) u : ℤ) : ℝ)) =
          ((analyticOrderNatAt (completedLFunction ψ) u : ℕ) : ℝ) := by simp
      rw [hDval, hcast]
      have hk : 4 / (17 * (1 - σ)) ≤
          (1 / (((1 + (1 - σ) : ℝ) : ℂ) + Complex.I * (T : ℂ) - u)).re := by
        refine kernelReLower (a := 1 + (1 - σ)) (T := T) (lam := 1 - σ) hlampos ?_ ?_ ?_
        · have : (((1 + (1 - σ) : ℝ) : ℂ) + Complex.I * (T : ℂ) - u).re = 1 + (1 - σ) - u.re := by
            simp
          linarith
        · have : (((1 + (1 - σ) : ℝ) : ℂ) + Complex.I * (T : ℂ) - u).re = 1 + (1 - σ) - u.re := by
            simp
          linarith
        · exact him
      have hkey : (17 * (1 - σ) / 4) *
          ((analyticOrderNatAt (completedLFunction ψ) u : ℝ) * (4 / (17 * (1 - σ)))) =
            (analyticOrderNatAt (completedLFunction ψ) u : ℝ) := by
        have hne : (1 : ℝ) - σ ≠ 0 := ne_of_gt hlampos
        field_simp
      calc ((analyticOrderNatAt (completedLFunction ψ) u : ℝ))
          = (17 * (1 - σ) / 4) *
              ((analyticOrderNatAt (completedLFunction ψ) u : ℝ) * (4 / (17 * (1 - σ)))) :=
                hkey.symm
        _ ≤ (17 * (1 - σ) / 4) *
              ((analyticOrderNatAt (completedLFunction ψ) u : ℝ) *
                (1 / (((1 + (1 - σ) : ℝ) : ℂ) + Complex.I * (T : ℂ) - u)).re) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hk (by positivity)) (by linarith)
    · rw [if_neg hbox]
      apply mul_nonneg (by linarith)
      by_cases hDu : (MeromorphicOn.divisor (completedLFunction ψ)
          (Metric.closedBall 0 (2 * (T + 2)))) u = 0
      · rw [hDu]; simp
      · have hzu := Commons.Analysis.Complex.zero_of_divisor_ne_zero hAn hDu
        have hstrip := Commons.NumberTheory.DirichletCharacter.zerosInStrip ψ hψ hψprim u hzu
        have hk : 0 ≤ (1 / (((1 + (1 - σ) : ℝ) : ℂ) + Complex.I * (T : ℂ) - u)).re := by
          rw [one_div_sub_re_explicit]
          have h1 : 0 < 1 + (1 - σ) - u.re := by linarith [hstrip.2, hσ1]
          have h2 : 0 < (1 + (1 - σ) - u.re) ^ 2 + (T - u.im) ^ 2 := by
            nlinarith [sq_nonneg (T - u.im), h1]
          exact div_nonneg h1.le h2.le
        exact mul_nonneg (Int.cast_nonneg ((MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn) u)) hk
  -- finite supports and the finsum comparison
  have hDfin : (Function.support (fun u : ℂ =>
      ((((MeromorphicOn.divisor (completedLFunction ψ)
        (Metric.closedBall 0 (2 * (T + 2)))) u : ℤ) : ℝ)))).Finite :=
    ((MeromorphicOn.divisor (completedLFunction ψ)
      (Metric.closedBall 0 (2 * (T + 2)))).finiteSupport
        (isCompact_closedBall (0 : ℂ) (2 * (T + 2)))).subset (by
          intro u hu
          rw [Function.mem_support] at hu ⊢
          intro h0
          exact hu (by rw [h0, Int.cast_zero]))
  have hfsF : Function.HasFiniteSupport (fun u : ℂ =>
      if analyticOrderNatAt (completedLFunction ψ) u ≠ 0 ∧ σ ≤ u.re ∧ u.re ≤ 1 ∧
        |u.im - T| ≤ (1 - σ) / 2 then (analyticOrderNatAt (completedLFunction ψ) u : ℝ) else 0) :=
    hDfin.subset (by
      intro u hu
      rw [Function.mem_support] at hu ⊢
      intro hDu
      apply hu
      rw [if_neg]
      rintro ⟨hord, hσu, hu1, him⟩
      have hDval := Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast hAn
        (huball u hord hσu hu1 him)
      rw [hDval] at hDu
      exact hord (by simpa using hDu))
  have hfsG : Function.HasFiniteSupport (fun u : ℂ => (17 * (1 - σ) / 4) *
      ((((MeromorphicOn.divisor (completedLFunction ψ) (Metric.closedBall 0 (2 * (T + 2)))) u : ℤ) : ℝ) *
        (1 / (((1 + (1 - σ) : ℝ) : ℂ) + Complex.I * (T : ℂ) - u)).re)) :=
    hDfin.subset (by
      intro u hu
      rw [Function.mem_support] at hu ⊢
      intro hDu
      exact hu (by rw [hDu]; ring))
  have h1 := finsum_le_finsum' hfsF hfsG hpoint
  have h2 : (∑ᶠ u : ℂ, (17 * (1 - σ) / 4) *
      ((((MeromorphicOn.divisor (completedLFunction ψ) (Metric.closedBall 0 (2 * (T + 2)))) u : ℤ) : ℝ) *
        (1 / (((1 + (1 - σ) : ℝ) : ℂ) + Complex.I * (T : ℂ) - u)).re))
      = (17 * (1 - σ) / 4) * (∑ᶠ u : ℂ,
          ((((MeromorphicOn.divisor (completedLFunction ψ) (Metric.closedBall 0 (2 * (T + 2)))) u : ℤ) : ℝ) *
            (1 / (((1 + (1 - σ) : ℝ) : ℂ) + Complex.I * (T : ℂ) - u)).re)) := by
    rw [← mul_finsum]
  exact le_trans h1 (le_of_eq h2)

/-- **Linnik's density lemma** (Jutila (1977), Lemma 8), form with an absolute constant:
for every non-principal Dirichlet character `χ` mod `q` and all `0 ≤ σ ≤ 1`, `T ≥ 1`, the
multiplicity-weighted number of zeros of the completed `L`-function of the primitive character
inducing `χ` in the square `σ ≤ Re ρ ≤ 1`, `|Im ρ - T| ≤ (1-σ)/2` is at most
`64·((1-σ)·log(q(T+1)) + 1)`. -/
theorem linnikDensityLemma :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q]
      (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ σ T : ℝ, 0 ≤ σ → σ ≤ 1 → 1 ≤ T →
      (∑ᶠ ρ : ℂ, if Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧
          |ρ.im - T| ≤ (1 - σ) / 2 then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0)
        ≤ C * ((1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1) := by
  refine ⟨64, by norm_num, ?_⟩
  intro q hq qne χ hχ σ T hσ0 hσ1 hT
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  obtain ⟨hψne, hdiv, hcon1, hconq⟩ := primitiveCharacterConductor χ hχ
  have hzero : ∀ ρ : ℂ, Work.LinnikContract.zeroMult χ ρ =
      analyticOrderNatAt (completedLFunction χ.primitiveCharacter) ρ := fun ρ => rfl
  have hconv : (∑ᶠ ρ : ℂ, if Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧
        |ρ.im - T| ≤ (1 - σ) / 2 then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0)
      = (∑ᶠ ρ : ℂ, if analyticOrderNatAt (completedLFunction χ.primitiveCharacter) ρ ≠ 0 ∧
          σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im - T| ≤ (1 - σ) / 2 then
          (analyticOrderNatAt (completedLFunction χ.primitiveCharacter) ρ : ℝ) else 0) := by
    simp only [hzero]
  rw [hconv]
  have hprim : (χ.primitiveCharacter).IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hbk := boxSum_le_kernelSum (N := χ.conductor) (ψ := χ.primitiveCharacter) hψne hprim
    hσ0 hσ1 hT
  rcases lt_or_ge (0 : ℝ) (1 - σ) with hpos | hnonpos
  · have hs1 : 1 < 1 + (1 - σ) := by linarith
    have hs3 : 1 + (1 - σ) ≤ 3 := by linarith
    have hks := kernelSumHalf (N := χ.conductor) (χ := χ.primitiveCharacter) hψne hprim
      (σ := 1 + (1 - σ)) (τ := T) hs1 hs3 (2 * (T + 2))
    have hstep : (∑ᶠ ρ : ℂ, if analyticOrderNatAt (completedLFunction χ.primitiveCharacter) ρ ≠ 0 ∧
          σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im - T| ≤ (1 - σ) / 2 then
          (analyticOrderNatAt (completedLFunction χ.primitiveCharacter) ρ : ℝ) else 0)
        ≤ (17 * (1 - σ) / 4) * (1 / ((1 + (1 - σ)) - 1) + 1 / 2 * Real.log ((χ.conductor : ℝ)) +
            1 / 2 * Real.log (2 + |T|) + 4) :=
      le_trans hbk (mul_le_mul_of_nonneg_left hks (by linarith))
    have hTabs : |T| = T := abs_of_nonneg (by linarith)
    have hstep2 : (17 * (1 - σ) / 4) * (1 / ((1 + (1 - σ)) - 1) +
          1 / 2 * Real.log ((χ.conductor : ℝ)) + 1 / 2 * Real.log (2 + |T|) + 4)
        = 17 / 4 + (17 * (1 - σ) / 8) * (Real.log ((χ.conductor : ℝ)) + Real.log (2 + T)) +
            17 * (1 - σ) := by
      rw [hTabs]
      have h1 : (1 + (1 - σ)) - 1 = 1 - σ := by ring
      rw [h1]
      field_simp
      ring
    have hcon1r : (1 : ℝ) ≤ (χ.conductor : ℝ) := by exact_mod_cast hcon1
    have hconqr : (χ.conductor : ℝ) ≤ (q : ℝ) := by exact_mod_cast hconq
    have hqr : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have harith := boxCountArith (lam := 1 - σ) (N := (χ.conductor : ℝ)) (q := (q : ℝ)) (T := T)
      (by linarith) hcon1r hconqr hqr hT
    linarith [hstep, hstep2, harith]
  · have h0 : (1 : ℝ) - σ = 0 := le_antisymm hnonpos (by linarith)
    have hLHS0 : (∑ᶠ ρ : ℂ, if analyticOrderNatAt (completedLFunction χ.primitiveCharacter) ρ ≠ 0 ∧
          σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im - T| ≤ (1 - σ) / 2 then
          (analyticOrderNatAt (completedLFunction χ.primitiveCharacter) ρ : ℝ) else 0) ≤ 0 := by
      simpa [h0] using hbk
    have hRHS : 64 * ((1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1) = 64 := by
      rw [h0]; ring
    linarith [hLHS0, hRHS]

end Work.ZeroDensity.Jutila
