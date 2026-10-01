/-
# `LinnikAreas2.PsiSieve2` — Graham's `ψ`-sieve (HB (11.13)), in this area's `ψ`-vocabulary

A copy of `Submission/Work/LinnikAreas2/graham_psi_sieve.lean`, with

* the `ψ`-vocabulary of `LinnikAreas2.PsiDefs2` instead of `Density4.psi_defs` (the module
  `Density4.psi_defs` imports the module `Density4.sum_log_div_le`, whose name collides with the
  lemma `Density4.sum_log_div_le` of the `ZeroDensity/Jutila` branch, so it cannot share an
  environment with the `θ`-sieve);
* the easy case `cz_easy_case_of` taken from `LinnikAreas2.BzCrossEasy` instead of
  `Jutila.BzCrossAux` (whose cone contains the currently non-building `BzCross.czHarmDecay`);
* the declarations placed in the namespace `Work.LinnikAreas2.PsiSieve2`, so that this module and
  the original `graham_psi_sieve` may coexist;
* the final theorem `graham_psi_sieve` removed: it is the instantiation of `graham_psi_sieve_of`
  with the seven analytic inputs and is done in the assembly.

Everything else is verbatim.
-/
import Mathlib
import Submission.Work.LinnikAreas.Density4.Defs
import Submission.Work.LinnikAreas2.PsiDefs2
import Submission.Work.ZeroDensity.Jutila.grahamDefs
import Submission.Work.ZeroDensity.Jutila.grahamCrossAssembly
import Submission.Work.LinnikAreas2.BzCrossEasy
import Submission.Work.ZeroDensity.Jutila.BzCross.BzCrossDefs
import Submission.Work.ZeroDensity.Jutila.mixedSelbergDefs
import Submission.Work.ZeroDensity.Jutila.MsqDiag
import Submission.Work.ZeroDensity.Jutila.MsqSelErr
import Submission.Work.ZeroDensity.Jutila.grahamBilinearReindex
import Submission.Work.LinnikAreas.Density4.sum_mu_sq_div_totient_sharp
import Submission.Work.LinnikAreas.Density4.natDiv_cast_mul_le
import Submission.Work.LinnikAreas.Density4.SelbergDefs
import Submission.Work.ZeroDensity.Jutila.BzApplyPrimePowReal
import Submission.Work.ZeroDensity.Jutila.ThetaSubIdEffectivePNT
import Submission.Work.LinnikAreas.Density4.prime_log_sum_repr
import Submission.Work.LinnikAreas.Density4.interval_integrable_theta_div
set_option maxHeartbeats 1000000

namespace Work.LinnikAreas2.PsiSieve2

open Work.LinnikAreas2

open Finset
open scoped BigOperators

noncomputable section

/-! ## The `ψ`-mollifier sum is the difference of two truncated von Mangoldt sums

`Work.LinnikAreas.Density4.psiM U V d = μ(d)` for `d ≤ U`, `μ(d)·log(V/d)/log(V/U)` for
`U < d ≤ V`, and `0` for `d > V` (HB (11.6)); `Work.ZeroDensity.Jutila.Lz z n` is the truncated
von Mangoldt sum `Σ_{d ∣ n, d ≤ z} μ(d)·log(z/d)` with a *real* cutoff.  Splitting the divisor
sum at `U` and at `V` gives, for every `n`, `log(V/U)·Σ_{d ∣ n} ψ_d = Lz_V(n) − Lz_U(n)`. -/

theorem psiM_sum_mul_log (U V : ℝ) (hU : 0 < U) (hUV : U < V) (n : ℕ) :
    Real.log (V / U) * (∑ d ∈ n.divisors, Work.LinnikAreas.Density4.psiM U V d)
      = Work.ZeroDensity.Jutila.Lz V n - Work.ZeroDensity.Jutila.Lz U n := by
  have hV : 0 < V := lt_trans hU hUV
  have hlogpos : 0 < Real.log (V / U) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hU]; simpa using hUV
  have hlogne : Real.log (V / U) ≠ 0 := ne_of_gt hlogpos
  -- the two sides, as sums over `n.divisors` of an explicit term
  have hLzV : Work.ZeroDensity.Jutila.Lz V n
      = ∑ d ∈ n.divisors,
          (if (d : ℝ) ≤ V then (ArithmeticFunction.moebius d : ℝ) * Real.log (V / (d : ℝ)) else 0) := by
    rw [Work.ZeroDensity.Jutila.Lz, Finset.sum_filter]
  have hLzU : Work.ZeroDensity.Jutila.Lz U n
      = ∑ d ∈ n.divisors,
          (if (d : ℝ) ≤ U then (ArithmeticFunction.moebius d : ℝ) * Real.log (U / (d : ℝ)) else 0) := by
    rw [Work.ZeroDensity.Jutila.Lz, Finset.sum_filter]
  have hlogsub : ∀ d ∈ n.divisors, ((d : ℝ) ≤ U →
      Real.log (V / (d : ℝ)) - Real.log (U / (d : ℝ)) = Real.log (V / U)) := by
    intro d hd hdU
    have hd0 : (0 : ℝ) < (d : ℝ) := by
      have := Nat.pos_of_mem_divisors hd
      exact_mod_cast this
    rw [← Real.log_div (ne_of_gt (by positivity : (0:ℝ) < V / (d:ℝ))) (ne_of_gt (by positivity : (0:ℝ) < U / (d:ℝ)))]
    congr 1
    field_simp
  -- termwise comparison
  rw [hLzV, hLzU, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Work.LinnikAreas.Density4.psiM]
  by_cases hdU : (d : ℝ) ≤ U
  · rw [if_pos hdU, if_pos (le_trans hdU hUV.le), if_pos hdU]
    rw [← mul_sub, hlogsub d hd hdU]
    ring
  · rw [if_neg hdU]
    by_cases hdV : (d : ℝ) ≤ V
    · rw [if_pos hdV, if_pos hdV, if_neg hdU]
      field_simp
      ring
    · rw [if_neg hdV, if_neg hdV, if_neg hdU]
      ring

/-- Squared form of `psiM_sum_mul_log`. -/
theorem psiSq_mul_log_sq (U V : ℝ) (hU : 0 < U) (hUV : U < V) (n : ℕ) :
    Real.log (V / U) ^ 2 * Work.LinnikAreas2.psiSq U V n
      = (Work.ZeroDensity.Jutila.Lz V n - Work.ZeroDensity.Jutila.Lz U n) ^ 2 := by
  have h := psiM_sum_mul_log U V hU hUV n
  rw [Work.LinnikAreas2.psiSq, ← h]
  ring


/-! ## The sharp Selberg quadratic form

`Work.ZeroDensity.Jutila.Msq w y = Σ_{d ≤ w, e ≤ y} selW_w(d)·selW_y(e)/lcm(d,e)` diagonalizes (`MsqDiag`) into
`Σ_{δ ≤ ⌊w⌋₊} (μ(δ)²φ(δ)/δ²)·Θ(w/δ,δ)·Θ(y/δ,δ)`, and `MsqSelErr` compares that sum with the
Mertens sum `Σ_{δ ≤ ⌊w⌋₊} μ(δ)²/φ(δ) = log w + O(1)` (`sum_mu_sq_div_totient_sharp`).  Hence the
sharp bound with the leading constant `1`. -/

theorem Msq_le_log_add_const : ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ), 1 ≤ w → w ≤ y →
    Work.ZeroDensity.Jutila.Msq w y ≤ Real.log w + C := by
  obtain ⟨Ce, hCe, hE⟩ := Work.ZeroDensity.Jutila.MsqSelErr
  obtain ⟨Cm, hCm, hM⟩ := Work.LinnikAreas.Density4.sum_mu_sq_div_totient_sharp
  refine ⟨Ce + Cm, by linarith, fun w y hw hwy => ?_⟩
  have hw0 : 0 < w := by linarith
  have hW1 : 1 ≤ ⌊w⌋₊ := Nat.le_floor (by exact_mod_cast hw)
  have hWw : (⌊w⌋₊ : ℝ) ≤ w := Nat.floor_le hw0.le
  have hdiag := Work.ZeroDensity.Jutila.MsqDiag w y hw hwy
  have herr := hE w y ⌊w⌋₊ hw hwy hWw hW1
  have hsum := hM ⌊w⌋₊ hW1
  have hlog : Real.log (⌊w⌋₊ : ℝ) ≤ Real.log w := Real.log_le_log (by positivity) hWw
  have h3 : Work.ZeroDensity.Jutila.Msq w y - (∑ δ ∈ Finset.Icc 1 ⌊w⌋₊,
      ((ArithmeticFunction.moebius δ : ℝ)^2)/(Nat.totient δ : ℝ)) ≤ Ce := by
    rw [hdiag]; exact (abs_le.mp herr).2
  linarith [h3, hsum, hlog]

/-! ## The elementary bounds on the Selberg weights -/

/-- `|selW z d| ≤ log(z/d)` for `1 ≤ d ≤ z`. -/
theorem abs_selW_le_log (z : ℝ) (hz : 1 ≤ z) (d : ℕ) (hd1 : 1 ≤ d) (hdz : (d : ℝ) ≤ z) :
    |Work.ZeroDensity.Jutila.selW z d| ≤ Real.log (z / (d : ℝ)) := by
  have hzpos : 0 < z := by linarith
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
  have hge1 : 1 ≤ z / (d : ℝ) := by rw [le_div_iff₀ hdpos, one_mul]; exact hdz
  have hlog : 0 ≤ Real.log (z / (d : ℝ)) := Real.log_nonneg hge1
  have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
    have h := ArithmeticFunction.abs_moebius_le_one (n := d)
    rw [← Int.cast_abs]
    exact_mod_cast h
  rw [Work.ZeroDensity.Jutila.selW]
  show |(ArithmeticFunction.moebius d : ℝ) * Real.log (z / (d : ℝ))|
      ≤ Real.log (z / (d : ℝ))
  rw [abs_mul]
  calc |(ArithmeticFunction.moebius d : ℝ)| * |Real.log (z / (d : ℝ))|
      ≤ 1 * |Real.log (z / (d : ℝ))| := mul_le_mul_of_nonneg_right hmu (abs_nonneg _)
    _ = Real.log (z / (d : ℝ)) := by rw [one_mul, abs_of_nonneg hlog]

/-- `Lz z n` as a sum over the integer cutoff `⌊z⌋₊`. -/
theorem Lz_eq_filter_floor (z : ℝ) (hz : 0 ≤ z) (n : ℕ) :
    Work.ZeroDensity.Jutila.Lz z n
      = ∑ d ∈ n.divisors.filter (fun d : ℕ => d ≤ ⌊z⌋₊), Work.ZeroDensity.Jutila.selW z d := by
  rw [Work.ZeroDensity.Jutila.Lz]
  refine Finset.sum_congr ?_ (fun d hd => ?_)
  · ext d
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hd, hdz⟩
      exact ⟨hd, Nat.le_floor (by exact_mod_cast hdz)⟩
    · rintro ⟨hd, hdfl⟩
      have h1 : (d : ℝ) ≤ (⌊z⌋₊ : ℝ) := by exact_mod_cast hdfl
      have h2 : (⌊z⌋₊ : ℝ) ≤ z := Nat.floor_le hz
      exact ⟨hd, le_trans h1 h2⟩
  · rw [Work.ZeroDensity.Jutila.selW]

/-- Floor comparison: `⌊N/l⌋ ≤ N/l ≤ ⌊N/l⌋ + 1`. -/
theorem floorDiv_bounds (N l : ℕ) (hl : 0 < l) :
    ((N / l : ℕ) : ℝ) ≤ (N : ℝ) / (l : ℝ)
      ∧ (N : ℝ) / (l : ℝ) - ((N / l : ℕ) : ℝ) ≤ 1 := by
  have h1 : ((N / l : ℕ) : ℝ) = (⌊(N : ℝ) / (l : ℝ)⌋₊ : ℝ) := by
    rw [Nat.floor_div_natCast, Nat.floor_natCast]
  constructor
  · rw [h1]; exact Nat.floor_le (by positivity)
  · rw [h1]
    have h := Nat.lt_floor_add_one ((N : ℝ) / (l : ℝ))
    linarith

/-- Bilinear reindexing of the divisor sums: `Σ_{n ≤ N}(Σ_{d|n,d≤W}A d)(Σ_{e|n,e≤E}B e)
= Σ_{d ≤ W, e ≤ E} A d B e ⌊N/lcm(d,e)⌋`. -/
theorem bilinear_reindex (W E : ℕ) (A B : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (∑ d ∈ n.divisors.filter (fun d => d ≤ W), A d)
        * (∑ e ∈ n.divisors.filter (fun e => e ≤ E), B e))
      = ∑ d ∈ Finset.Icc 1 W, ∑ e ∈ Finset.Icc 1 E,
          A d * B e * ((N / Nat.lcm d e : ℕ) : ℝ) :=
  Work.ZeroDensity.Jutila.grahamBilinearReindex W E A B N


/-! ## The cross estimate for the Möbius correction `Bz` from the `S₃` model estimates -/

/-- **The `Bz`-cross estimate (hard range) from the five `S₃` inputs.** -/
theorem bzCross_hard_of
    (hCrossEq : ∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N : ℝ) →
      (∑ n ∈ Finset.Icc 1 N, Work.ZeroDensity.Jutila.Bz w n * Work.ZeroDensity.Jutila.Bz y n)
        = Work.ZeroDensity.Jutila.czCross w y N)
    (hCont : ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N : ℝ) →
      |Work.ZeroDensity.Jutila.czModelCont w y N
        - (N : ℝ) * Real.log ((N : ℝ) / y)| ≤ C * (N : ℝ))
    (hB : ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N : ℝ) →
      |Work.ZeroDensity.Jutila.czModelB w y N| ≤ C * (N : ℝ))
    (hFloor : ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N : ℝ) →
      |Work.ZeroDensity.Jutila.czModelFloor w y N
        - Work.ZeroDensity.Jutila.czModelCont w y N| ≤ C * (N : ℝ))
    (hAbel : ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N : ℝ) →
      |Work.ZeroDensity.Jutila.czCross w y N
        - (Work.ZeroDensity.Jutila.czModelFloor w y N
            - Work.ZeroDensity.Jutila.czModelB w y N)| ≤ C * (N : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ), 1 ≤ w → w ≤ y → ∀ N : ℕ, y ≤ (N : ℝ) →
      (N : ℝ) < w * y →
      |(∑ n ∈ Finset.Icc 1 N, Work.ZeroDensity.Jutila.Bz w n * Work.ZeroDensity.Jutila.Bz y n)
        - (N : ℝ) * Real.log ((N : ℝ) / y)| ≤ C * (N : ℝ) := by
  obtain ⟨C₁, hC₁, hc⟩ := hCont
  obtain ⟨C₂, hC₂, hb⟩ := hB
  obtain ⟨C₃, hC₃, hf⟩ := hFloor
  obtain ⟨C₄, hC₄, ha⟩ := hAbel
  refine ⟨C₁ + C₂ + C₃ + C₄, by positivity, fun w y hw hwy N hyN _ => ?_⟩
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have heq := hCrossEq w y N hw hwy hyN
  have e1 := hc w y N hw hwy hyN
  have e2 := hb w y N hw hwy hyN
  have e3 := hf w y N hw hwy hyN
  have e4 := ha w y N hw hwy hyN
  have h1 := abs_le.mp e1
  have h2 := abs_le.mp e2
  have h3 := abs_le.mp e3
  have h4 := abs_le.mp e4
  rw [heq, abs_le]
  refine ⟨?_, ?_⟩ <;> nlinarith [hNnn, hC₁.le, hC₂.le, hC₃.le, hC₄.le]

/-- **The full `Bz`-cross estimate** (both ranges): the hard range from the model estimates and
the easy range `w·y ≤ N` from the exact reindexing + the floor comparison (`cz_easy_case_of`). -/
theorem bzCross_of
    (hCrossEq : ∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N : ℝ) →
      (∑ n ∈ Finset.Icc 1 N, Work.ZeroDensity.Jutila.Bz w n * Work.ZeroDensity.Jutila.Bz y n)
        = Work.ZeroDensity.Jutila.czCross w y N)
    (hCont : ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N : ℝ) →
      |Work.ZeroDensity.Jutila.czModelCont w y N
        - (N : ℝ) * Real.log ((N : ℝ) / y)| ≤ C * (N : ℝ))
    (hB : ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N : ℝ) →
      |Work.ZeroDensity.Jutila.czModelB w y N| ≤ C * (N : ℝ))
    (hFloor : ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N : ℝ) →
      |Work.ZeroDensity.Jutila.czModelFloor w y N
        - Work.ZeroDensity.Jutila.czModelCont w y N| ≤ C * (N : ℝ))
    (hAbel : ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N : ℝ) →
      |Work.ZeroDensity.Jutila.czCross w y N
        - (Work.ZeroDensity.Jutila.czModelFloor w y N
            - Work.ZeroDensity.Jutila.czModelB w y N)| ≤ C * (N : ℝ))
    (hMul : ∃ C : ℝ, 0 < C ∧ ∀ (z : ℝ), 1 ≤ z → ∀ N : ℕ, z ≤ (N : ℝ) →
      |(∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n
          * Work.ZeroDensity.Jutila.Bz z n)
        + (N : ℝ) * Real.log ((N : ℝ) / z)| ≤ C * (N : ℝ))
    (hEasy : ∃ C : ℝ, 0 < C ∧ ∀ (z₁ z₂ : ℝ), 1 ≤ z₁ → z₁ ≤ z₂ → ∀ N : ℕ, z₂ ≤ (N : ℝ) →
      |(∑ n ∈ Finset.Icc 1 N, Work.ZeroDensity.Jutila.Lz z₁ n
          * Work.ZeroDensity.Jutila.Lz z₂ n) - (N : ℝ) * Real.log z₁|
        ≤ C * ((N : ℝ) + z₁ * z₂)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ), 1 ≤ w → w ≤ y → ∀ N : ℕ, y ≤ (N : ℝ) →
      |(∑ n ∈ Finset.Icc 1 N, Work.ZeroDensity.Jutila.Bz w n * Work.ZeroDensity.Jutila.Bz y n)
        - (N : ℝ) * Real.log ((N : ℝ) / y)| ≤ C * (N : ℝ) := by
  obtain ⟨C₅, hC₅, hhard⟩ := bzCross_hard_of hCrossEq hCont hB hFloor hAbel
  obtain ⟨C₆, hC₆, heasy⟩ := Work.LinnikAreas2.cz_easy_case_of hEasy hMul
  refine ⟨max C₅ C₆, lt_max_of_lt_left hC₅, fun w y hw hwy N hyN => ?_⟩
  by_cases hcase : w * y ≤ (N : ℝ)
  · have h := heasy w y hw hwy N hyN hcase
    have hC : C₆ * (N : ℝ) ≤ max C₅ C₆ * (N : ℝ) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    linarith
  · have hcase' : (N : ℝ) < w * y := lt_of_not_ge hcase
    have h := hhard w y hw hwy N hyN hcase'
    have hC : C₅ * (N : ℝ) ≤ max C₅ C₆ * (N : ℝ) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    linarith

/-- **Graham's two-sided asymptotic estimate for the real-cutoff cross moment**, from the four
inputs of `grahamCrossTwoSided_of`. -/
theorem lzCross_two_of
    (hBzCross : ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ), 1 ≤ w → w ≤ y → ∀ N : ℕ, y ≤ (N : ℝ) →
      |(∑ n ∈ Finset.Icc 1 N, Work.ZeroDensity.Jutila.Bz w n * Work.ZeroDensity.Jutila.Bz y n)
        - (N : ℝ) * Real.log ((N : ℝ) / y)| ≤ C * (N : ℝ))
    (hMul : ∃ C : ℝ, 0 < C ∧ ∀ (z : ℝ), 1 ≤ z → ∀ N : ℕ, z ≤ (N : ℝ) →
      |(∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n
          * Work.ZeroDensity.Jutila.Bz z n)
        + (N : ℝ) * Real.log ((N : ℝ) / z)| ≤ C * (N : ℝ))
    (hEasy : ∃ C : ℝ, 0 < C ∧ ∀ (z₁ z₂ : ℝ), 1 ≤ z₁ → z₁ ≤ z₂ → ∀ N : ℕ, z₂ ≤ (N : ℝ) →
      |(∑ n ∈ Finset.Icc 1 N, Work.ZeroDensity.Jutila.Lz z₁ n
          * Work.ZeroDensity.Jutila.Lz z₂ n) - (N : ℝ) * Real.log z₁|
        ≤ C * ((N : ℝ) + z₁ * z₂)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ), 1 < w → w ≤ y → ∀ N : ℕ, y ≤ (N : ℝ) →
      |(∑ n ∈ Finset.Icc 1 N, Work.ZeroDensity.Jutila.Lz w n
          * Work.ZeroDensity.Jutila.Lz y n) - (N : ℝ) * Real.log w| ≤ C * (N : ℝ) :=
  Work.ZeroDensity.Jutila.grahamCrossTwoSided_of hEasy
    Work.ZeroDensity.Jutila.vonMangoldtSqEval_here hMul hBzCross

/-- **The diagonal `Bz`-square bound** `Σ_{n ≤ N} Bz_z(n)² ≤ N·log(N/z) + C·N`. -/
theorem bzSq_le_of
    (hLz : ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ), 1 < w → w ≤ y → ∀ N : ℕ, y ≤ (N : ℝ) →
      |(∑ n ∈ Finset.Icc 1 N, Work.ZeroDensity.Jutila.Lz w n
          * Work.ZeroDensity.Jutila.Lz y n) - (N : ℝ) * Real.log w| ≤ C * (N : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : ℝ), 1 < z → ∀ N : ℕ, z ≤ (N : ℝ) →
      (∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Bz z n) ^ 2)
        ≤ (N : ℝ) * Real.log ((N : ℝ) / z) + C * (N : ℝ) := by
  obtain ⟨C₁, hC₁, hLz⟩ := hLz
  obtain ⟨C₂, hC₂, hsq⟩ := Work.ZeroDensity.Jutila.vonMangoldtSqEval_here
  refine ⟨3 * C₁ + C₂ + 8, by positivity, fun z hz N hzN => ?_⟩
  have hz1 : 1 ≤ z := le_of_lt hz
  have hzpos : 0 < z := by linarith
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ (N : ℝ) := le_trans (le_of_lt hz) hzN
    exact_mod_cast this
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hΛ : ∀ n : ℕ, 2 ≤ n → Work.ZeroDensity.Jutila.Lz (N : ℝ) n
      = ArithmeticFunction.vonMangoldt n + Work.ZeroDensity.Jutila.Bz (N : ℝ) n :=
    fun n hn => Work.ZeroDensity.Jutila.Lz_eq_vonMangoldt_add_Bz (z := (N : ℝ)) hNpos hn
  have hBzN : ∀ n : ℕ, (n : ℝ) ≤ (N : ℝ) → Work.ZeroDensity.Jutila.Bz N n = 0 :=
    fun n hn => Work.ZeroDensity.Jutila.Bz_eq_zero_of_le hNpos.le hn
  have hpt : ∀ n ∈ Finset.Icc 2 N, (Work.ZeroDensity.Jutila.Bz z n) ^ 2
      = (Work.ZeroDensity.Jutila.Lz z n - ArithmeticFunction.vonMangoldt n) ^ 2 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have h := Work.ZeroDensity.Jutila.Lz_eq_vonMangoldt_add_Bz (z := z) hzpos hn.1
    rw [h]; ring
  -- split off the `n = 1` term
  have hI : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hBz1 : Work.ZeroDensity.Jutila.Bz z 1 = 0 := Work.ZeroDensity.Jutila.Bz_one_eq_zero hz1
  have hLz1 : Work.ZeroDensity.Jutila.Lz z 1 = Real.log z :=
    Work.ZeroDensity.Jutila.Lz_one_eq z hz1
  have hLzN1 : Work.ZeroDensity.Jutila.Lz N 1 = Real.log (N : ℝ) :=
    Work.ZeroDensity.Jutila.Lz_one_eq (N : ℝ) hN1'
  have hsplit : (∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Bz z n) ^ 2)
      = ∑ n ∈ Finset.Icc 2 N,
          (Work.ZeroDensity.Jutila.Lz z n - ArithmeticFunction.vonMangoldt n) ^ 2 := by
    rw [hI, Finset.sum_insert (by simp), hBz1, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add]
    exact Finset.sum_congr rfl hpt
  have hsplit2 : (∑ n ∈ Finset.Icc 1 N,
        (Work.ZeroDensity.Jutila.Lz z n - ArithmeticFunction.vonMangoldt n) ^ 2)
      = (Real.log z) ^ 2
        + ∑ n ∈ Finset.Icc 2 N,
            (Work.ZeroDensity.Jutila.Lz z n - ArithmeticFunction.vonMangoldt n) ^ 2 := by
    rw [hI, Finset.sum_insert (by simp)]
    have : ArithmeticFunction.vonMangoldt 1 = 0 := ArithmeticFunction.vonMangoldt_apply_one
    rw [hLz1, this, sub_zero]
  -- expand the square on `Icc 1 N`
  have hexp : (∑ n ∈ Finset.Icc 1 N,
        (Work.ZeroDensity.Jutila.Lz z n - ArithmeticFunction.vonMangoldt n) ^ 2)
      = (∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Lz z n) ^ 2)
        - 2 * (∑ n ∈ Finset.Icc 1 N,
            Work.ZeroDensity.Jutila.Lz z n * ArithmeticFunction.vonMangoldt n)
        + (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n) ^ 2) := by
    calc (∑ n ∈ Finset.Icc 1 N,
          (Work.ZeroDensity.Jutila.Lz z n - ArithmeticFunction.vonMangoldt n) ^ 2)
        = ∑ n ∈ Finset.Icc 1 N,
            ((Work.ZeroDensity.Jutila.Lz z n) ^ 2
              - (2 * (Work.ZeroDensity.Jutila.Lz z n * ArithmeticFunction.vonMangoldt n)
                  - (ArithmeticFunction.vonMangoldt n) ^ 2)) :=
          Finset.sum_congr rfl (fun n _ => by ring)
      _ = (∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Lz z n) ^ 2)
            - ∑ n ∈ Finset.Icc 1 N,
                (2 * (Work.ZeroDensity.Jutila.Lz z n * ArithmeticFunction.vonMangoldt n)
                  - (ArithmeticFunction.vonMangoldt n) ^ 2) := by
          rw [Finset.sum_sub_distrib]
      _ = (∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Lz z n) ^ 2)
            - (2 * (∑ n ∈ Finset.Icc 1 N,
                  Work.ZeroDensity.Jutila.Lz z n * ArithmeticFunction.vonMangoldt n)
              - (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n) ^ 2)) := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = (∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Lz z n) ^ 2)
            - 2 * (∑ n ∈ Finset.Icc 1 N,
                  Work.ZeroDensity.Jutila.Lz z n * ArithmeticFunction.vonMangoldt n)
            + (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n) ^ 2) := by ring
  -- identify `Σ Lz_z · Λ` with `Σ Lz_z · Lz_N` minus the `n = 1` term
  have hLzΛ : (∑ n ∈ Finset.Icc 1 N,
        Work.ZeroDensity.Jutila.Lz z n * ArithmeticFunction.vonMangoldt n)
      = (∑ n ∈ Finset.Icc 1 N, Work.ZeroDensity.Jutila.Lz z n * Work.ZeroDensity.Jutila.Lz N n)
        - Real.log z * Real.log (N : ℝ) := by
    have hcongr : (∑ n ∈ Finset.Icc 1 N,
          Work.ZeroDensity.Jutila.Lz z n * ArithmeticFunction.vonMangoldt n)
        = ∑ n ∈ Finset.Icc 1 N,
            (Work.ZeroDensity.Jutila.Lz z n * Work.ZeroDensity.Jutila.Lz N n
              - (if n = 1 then Real.log z * Real.log (N : ℝ) else 0)) := by
      refine Finset.sum_congr rfl (fun n hn => ?_)
      rw [Finset.mem_Icc] at hn
      by_cases hn1 : n = 1
      · subst hn1; rw [if_pos rfl, hLz1, hLzN1, ArithmeticFunction.vonMangoldt_apply_one]; ring
      · rw [if_neg hn1]
        have h2 : 2 ≤ n := by omega
        have hle : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn.2
        have hΛn : ArithmeticFunction.vonMangoldt n = Work.ZeroDensity.Jutila.Lz (N : ℝ) n := by
          rw [hΛ n h2, hBzN n hle, add_zero]
        rw [hΛn]; ring
    rw [hcongr, Finset.sum_sub_distrib]
    have hsingle : (∑ n ∈ Finset.Icc 1 N, (if n = 1 then Real.log z * Real.log (N : ℝ) else 0))
        = Real.log z * Real.log (N : ℝ) := by
      refine Finset.sum_eq_single 1 ?_ ?_
      · intro b hb hb1
        rw [if_neg hb1]
      · intro h1
        exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, hN1⟩) h1
    rw [hsingle]
  -- the bounds
  have hdiag := hLz z z hz le_rfl N hzN
  have hcross := hLz z (N : ℝ) hz hzN N le_rfl
  have hsqb := hsq N hN1
  have hlog := Work.ZeroDensity.Jutila.log_sq_le_four_mul N hN1
  have hd1 := abs_le.mp hdiag
  have hd2 := abs_le.mp hcross
  have hd3 := abs_le.mp hsqb
  have hlogdiv : Real.log ((N : ℝ) / z) = Real.log (N : ℝ) - Real.log z :=
    Real.log_div (ne_of_gt hNpos) (ne_of_gt hzpos)
  have hdiagsq : (∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Lz z n) ^ 2)
      ≤ (N : ℝ) * Real.log z + C₁ * (N : ℝ) := by
    have heq : (∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Lz z n) ^ 2)
        = (∑ n ∈ Finset.Icc 1 N, Work.ZeroDensity.Jutila.Lz z n * Work.ZeroDensity.Jutila.Lz z n) :=
      Finset.sum_congr rfl (fun n _ => by ring)
    rw [heq]; linarith [hd1.2]
  -- assemble: `Σ Bz² = Σ_{Icc 2 N}(Lz−Λ)² = Σ_{Icc 1 N}(Lz−Λ)² − (log z)²`
  have hB : (∑ n ∈ Finset.Icc 1 N,
        (Work.ZeroDensity.Jutila.Lz z n - ArithmeticFunction.vonMangoldt n) ^ 2)
      = (Real.log z) ^ 2 + (∑ n ∈ Finset.Icc 2 N,
        (Work.ZeroDensity.Jutila.Lz z n - ArithmeticFunction.vonMangoldt n) ^ 2) := hsplit2
  have hlogsq : 0 ≤ Real.log z := Real.log_nonneg hz1
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1'
  have hlogz_le : Real.log z ≤ Real.log (N : ℝ) := Real.log_le_log hzpos hzN
  have hlogmul : 2 * Real.log z * Real.log (N : ℝ) ≤ 8 * (N : ℝ) := by
    nlinarith [hlog, hlogz_le, hlogsq, hlogN0]
  have hmid : (∑ n ∈ Finset.Icc 1 N,
        (Work.ZeroDensity.Jutila.Lz z n - ArithmeticFunction.vonMangoldt n) ^ 2)
      ≤ (N : ℝ) * Real.log z + C₁ * (N : ℝ)
        - 2 * ((N : ℝ) * Real.log z - C₁ * (N : ℝ))
        + (N : ℝ) * Real.log (N : ℝ) + C₂ * (N : ℝ)
        + 2 * Real.log z * Real.log (N : ℝ) := by
    linarith [hdiagsq, hLzΛ, hd2.1, hd3.2, hexp]
  have hfinal : (∑ n ∈ Finset.Icc 2 N,
        (Work.ZeroDensity.Jutila.Lz z n - ArithmeticFunction.vonMangoldt n) ^ 2)
      ≤ (N : ℝ) * Real.log ((N : ℝ) / z) + (3 * C₁ + C₂ + 8) * (N : ℝ) := by
    have hlogzsq : (0:ℝ) ≤ (Real.log z) ^ 2 := sq_nonneg _
    rw [hlogdiv]
    nlinarith [hB, hmid, hlogmul, hlogzsq]
  rw [hsplit]
  exact hfinal

/-! ## The difference-square bound for the truncated von Mangoldt sums -/

theorem lzDiff_le_of
    (hLz : ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ), 1 < w → w ≤ y → ∀ N : ℕ, y ≤ (N : ℝ) →
      |(∑ n ∈ Finset.Icc 1 N, Work.ZeroDensity.Jutila.Lz w n
          * Work.ZeroDensity.Jutila.Lz y n) - (N : ℝ) * Real.log w| ≤ C * (N : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ), 1 < w → w ≤ y → ∀ N : ℕ, y ≤ (N : ℝ) →
      (∑ n ∈ Finset.Icc 1 N,
          (Work.ZeroDensity.Jutila.Lz y n - Work.ZeroDensity.Jutila.Lz w n) ^ 2)
        ≤ (N : ℝ) * Real.log (y / w) + C * (N : ℝ) := by
  obtain ⟨C₁, hC₁, hLz⟩ := hLz
  refine ⟨4 * C₁, by positivity, fun w y hw hwy N hyN => ?_⟩
  have hwpos : 0 < w := by linarith
  have hypos : 0 < y := lt_of_lt_of_le hwpos hwy
  have hyw : y ≤ (N : ℝ) := hyN
  have hdw := hLz w w hw le_rfl N (le_trans hwy hyN)
  have hdy := hLz y y (lt_of_lt_of_le hw hwy) le_rfl N hyN
  have hcr := hLz w y hw hwy N hyN
  have e1 := abs_le.mp hdw
  have e2 := abs_le.mp hdy
  have e3 := abs_le.mp hcr
  have hdiagW : (∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Lz w n) ^ 2)
      = (∑ n ∈ Finset.Icc 1 N, Work.ZeroDensity.Jutila.Lz w n
          * Work.ZeroDensity.Jutila.Lz w n) := Finset.sum_congr rfl (fun n _ => by ring)
  have hdiagY : (∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Lz y n) ^ 2)
      = (∑ n ∈ Finset.Icc 1 N, Work.ZeroDensity.Jutila.Lz y n
          * Work.ZeroDensity.Jutila.Lz y n) := Finset.sum_congr rfl (fun n _ => by ring)
  have hpt : (∑ n ∈ Finset.Icc 1 N,
        (Work.ZeroDensity.Jutila.Lz y n - Work.ZeroDensity.Jutila.Lz w n) ^ 2)
      = (∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Lz y n) ^ 2)
        + (∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Lz w n) ^ 2)
        - 2 * (∑ n ∈ Finset.Icc 1 N, Work.ZeroDensity.Jutila.Lz w n
            * Work.ZeroDensity.Jutila.Lz y n) := by
    have h1 : (∑ n ∈ Finset.Icc 1 N,
          (Work.ZeroDensity.Jutila.Lz y n - Work.ZeroDensity.Jutila.Lz w n) ^ 2)
        = ∑ n ∈ Finset.Icc 1 N,
            ((Work.ZeroDensity.Jutila.Lz y n) ^ 2 + (Work.ZeroDensity.Jutila.Lz w n) ^ 2
              - 2 * (Work.ZeroDensity.Jutila.Lz w n * Work.ZeroDensity.Jutila.Lz y n)) :=
      Finset.sum_congr rfl (fun n _ => by ring)
    rw [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  have hlogdiv : Real.log (y / w) = Real.log y - Real.log w :=
    Real.log_div (ne_of_gt hypos) (ne_of_gt hwpos)
  rw [hpt, hdiagW, hdiagY, hlogdiv]
  nlinarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2]

/-! ## The target, from the seven analytic inputs -/

theorem graham_psi_sieve_of
    (hCrossEq : ∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N : ℝ) →
      (∑ n ∈ Finset.Icc 1 N, Work.ZeroDensity.Jutila.Bz w n * Work.ZeroDensity.Jutila.Bz y n)
        = Work.ZeroDensity.Jutila.czCross w y N)
    (hCont : ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N : ℝ) →
      |Work.ZeroDensity.Jutila.czModelCont w y N
        - (N : ℝ) * Real.log ((N : ℝ) / y)| ≤ C * (N : ℝ))
    (hB : ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N : ℝ) →
      |Work.ZeroDensity.Jutila.czModelB w y N| ≤ C * (N : ℝ))
    (hFloor : ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N : ℝ) →
      |Work.ZeroDensity.Jutila.czModelFloor w y N
        - Work.ZeroDensity.Jutila.czModelCont w y N| ≤ C * (N : ℝ))
    (hAbel : ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N : ℝ) →
      |Work.ZeroDensity.Jutila.czCross w y N
        - (Work.ZeroDensity.Jutila.czModelFloor w y N
            - Work.ZeroDensity.Jutila.czModelB w y N)| ≤ C * (N : ℝ))
    (hMul : ∃ C : ℝ, 0 < C ∧ ∀ (z : ℝ), 1 ≤ z → ∀ N : ℕ, z ≤ (N : ℝ) →
      |(∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n
          * Work.ZeroDensity.Jutila.Bz z n)
        + (N : ℝ) * Real.log ((N : ℝ) / z)| ≤ C * (N : ℝ))
    (hEasy : ∃ C : ℝ, 0 < C ∧ ∀ (z₁ z₂ : ℝ), 1 ≤ z₁ → z₁ ≤ z₂ → ∀ N : ℕ, z₂ ≤ (N : ℝ) →
      |(∑ n ∈ Finset.Icc 1 N, Work.ZeroDensity.Jutila.Lz z₁ n
          * Work.ZeroDensity.Jutila.Lz z₂ n) - (N : ℝ) * Real.log z₁|
        ≤ C * ((N : ℝ) + z₁ * z₂))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ (u v : ℝ), 0 < u → u < v → ∃ C₁ : ℝ, 0 < C₁ ∧
    ∀ (L U V : ℝ), 0 < L → U = Real.exp (u * L) → V = Real.exp (v * L) →
      (∀ N : ℕ, U ≤ (N : ℝ) → (N : ℝ) ≤ V →
        Work.LinnikAreas2.psSum U V N
          ≤ (1 + ε) * (N : ℝ) * Real.log ((N : ℝ) / U) / (Real.log (V / U)) ^ 2
              + C₁ * (N : ℝ) / (Real.log (V / U)) ^ 2) ∧
      (∀ N : ℕ, V ≤ (N : ℝ) →
        Work.LinnikAreas2.psSum U V N
          ≤ (1 + ε) * (N : ℝ) / Real.log (V / U)
              + C₁ * (N : ℝ) / (Real.log (V / U)) ^ 2) := by
  have hBzCross := bzCross_of hCrossEq hCont hB hFloor hAbel hMul hEasy
  have hLzCross := lzCross_two_of hBzCross hMul hEasy
  obtain ⟨Cb, hCb, hbzSq⟩ := bzSq_le_of hLzCross
  obtain ⟨Cd, hCd, hdiff⟩ := lzDiff_le_of hLzCross
  intro u v hu huv
  set C₁ : ℝ := max (Cb + 4 * (v - u) ^ 2 / u ^ 2) Cd + 1 with hC₁def
  have hC₁pos : 0 < C₁ := by rw [hC₁def]; positivity
  refine ⟨C₁, hC₁pos, ?_⟩
  intro L U V hL hU hV
  have hUpos : 0 < U := by rw [hU]; exact Real.exp_pos _
  have hVpos : 0 < V := by rw [hV]; exact Real.exp_pos _
  have hUV : U < V := by
    rw [hU, hV]; exact Real.exp_lt_exp.mpr (by nlinarith)
  have hU1 : 1 < U := by
    rw [hU, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by nlinarith)
  have hlogVU : Real.log (V / U) = (v - u) * L := by
    rw [hV, hU, ← Real.exp_sub, Real.log_exp]; ring
  have hLpos : 0 < Real.log (V / U) := by rw [hlogVU]; nlinarith
  have hL2pos : 0 < (Real.log (V / U)) ^ 2 := by positivity
  have hCbin : Cb + 4 * (v - u) ^ 2 / u ^ 2 ≤ C₁ := by
    rw [hC₁def]; linarith [le_max_left (Cb + 4 * (v - u) ^ 2 / u ^ 2) Cd]
  have hCdin : Cd ≤ C₁ := by
    rw [hC₁def]; linarith [le_max_right (Cb + 4 * (v - u) ^ 2 / u ^ 2) Cd]
  have hpsi : ∀ n : ℕ, Work.LinnikAreas2.psiSq U V n
      = (Work.ZeroDensity.Jutila.Lz V n - Work.ZeroDensity.Jutila.Lz U n) ^ 2
          / (Real.log (V / U)) ^ 2 := by
    intro n
    have h := psiSq_mul_log_sq U V hUpos hUV n
    rw [eq_div_iff (ne_of_gt hL2pos)]
    linarith [h]
  have hBzU1 : Work.ZeroDensity.Jutila.Bz U 1 = 0 :=
    Work.ZeroDensity.Jutila.Bz_one_eq_zero (le_of_lt hU1)
  constructor
  · -- the range `U ≤ N ≤ V`
    intro N hUN hNV
    have hN1 : 1 ≤ N := by
      have : (1 : ℝ) ≤ (N : ℝ) := le_trans (le_of_lt hU1) hUN
      exact_mod_cast this
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hNnn : (0 : ℝ) ≤ (N : ℝ) := hNpos.le
    -- the pointwise description of `Lz_V − Lz_U` on `[1,N]`
    have hpt : ∀ n ∈ Finset.Icc 1 N,
        (Work.ZeroDensity.Jutila.Lz V n - Work.ZeroDensity.Jutila.Lz U n) ^ 2
          = (if n = 1 then (Real.log (V / U)) ^ 2
              else (Work.ZeroDensity.Jutila.Bz U n) ^ 2) := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      by_cases hn1 : n = 1
      · subst hn1
        rw [if_pos rfl, Work.ZeroDensity.Jutila.Lz_one_eq V (le_of_lt (lt_trans hU1 hUV)),
          Work.ZeroDensity.Jutila.Lz_one_eq U (le_of_lt hU1),
          ← Real.log_div (ne_of_gt hVpos) (ne_of_gt hUpos)]
      · rw [if_neg hn1]
        have h2 : 2 ≤ n := by omega
        have hnV : (n : ℝ) ≤ V := le_trans (by exact_mod_cast hn.2) hNV
        have hBzV : Work.ZeroDensity.Jutila.Bz V n = 0 :=
          Work.ZeroDensity.Jutila.Bz_eq_zero_of_le hVpos.le hnV
        have hLzV : Work.ZeroDensity.Jutila.Lz V n = ArithmeticFunction.vonMangoldt n := by
          rw [Work.ZeroDensity.Jutila.Lz_eq_vonMangoldt_add_Bz hVpos h2, hBzV, add_zero]
        have hLzU : Work.ZeroDensity.Jutila.Lz U n
            = ArithmeticFunction.vonMangoldt n + Work.ZeroDensity.Jutila.Bz U n :=
          Work.ZeroDensity.Jutila.Lz_eq_vonMangoldt_add_Bz hUpos h2
        rw [hLzV, hLzU]; ring
    have hI : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hsum1 : (∑ n ∈ Finset.Icc 1 N,
          (if n = 1 then (Real.log (V / U)) ^ 2
            else (Work.ZeroDensity.Jutila.Bz U n) ^ 2))
        = (Real.log (V / U)) ^ 2
          + ∑ n ∈ Finset.Icc 2 N, (Work.ZeroDensity.Jutila.Bz U n) ^ 2 := by
      rw [hI, Finset.sum_insert (by simp), if_pos rfl]
      congr 1
      refine Finset.sum_congr rfl (fun n hn => ?_)
      rw [if_neg]
      simp only [Finset.mem_Icc] at hn
      omega
    have hsum2 : (∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Bz U n) ^ 2)
        = ∑ n ∈ Finset.Icc 2 N, (Work.ZeroDensity.Jutila.Bz U n) ^ 2 := by
      rw [hI, Finset.sum_insert (by simp), hBzU1]
      norm_num
    have hsum3 : Work.LinnikAreas2.psSum U V N
        = 1 + (∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Bz U n) ^ 2)
            / (Real.log (V / U)) ^ 2 := by
      rw [Work.LinnikAreas2.psSum]
      have hstep : (∑ n ∈ Finset.Icc 1 N, Work.LinnikAreas2.psiSq U V n)
          = (∑ n ∈ Finset.Icc 1 N,
              (if n = 1 then (Real.log (V / U)) ^ 2
                else (Work.ZeroDensity.Jutila.Bz U n) ^ 2)) / (Real.log (V / U)) ^ 2 := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl (fun n hn => by rw [hpsi n, hpt n hn])
      rw [hstep, hsum1, hsum2, add_div, div_self (ne_of_gt hL2pos)]
    rw [hsum3]
    have hbz := hbzSq U hU1 N hUN
    have hlogNU : 0 ≤ Real.log ((N : ℝ) / U) :=
      Real.log_nonneg (by rw [one_le_div hUpos]; exact hUN)
    -- `L² ≤ (4/u²)·N`
    have hLsq : L ^ 2 ≤ (4 / u ^ 2) * (N : ℝ) := by
      have huL : 0 < u * L / 2 := by positivity
      have hexp_ge : u * L / 2 ≤ Real.exp (u * L / 2) := by
        linarith [Real.add_one_le_exp (u * L / 2)]
      have hexp2 : Real.exp (u * L / 2) * Real.exp (u * L / 2) = Real.exp (u * L) := by
        rw [← Real.exp_add]; ring_nf
      have h1 : (u * L / 2) ^ 2 ≤ Real.exp (u * L) := by
        calc (u * L / 2) ^ 2 = (u * L / 2) * (u * L / 2) := by ring
          _ ≤ Real.exp (u * L / 2) * Real.exp (u * L / 2) :=
              mul_le_mul hexp_ge hexp_ge huL.le (Real.exp_pos _).le
          _ = Real.exp (u * L) := hexp2
      have hexpN : Real.exp (u * L) ≤ (N : ℝ) := by rw [← hU]; exact hUN
      have hu2 : 0 < u ^ 2 := by positivity
      have hkey : u ^ 2 * L ^ 2 / 4 ≤ (N : ℝ) := by nlinarith [h1, hexpN, sq_nonneg (u * L)]
      have hkey' : u ^ 2 * L ^ 2 ≤ 4 * (N : ℝ) := by nlinarith [hkey, hu2]
      rw [show 4 / u ^ 2 * (N : ℝ) = (4 * (N : ℝ)) / u ^ 2 by ring, le_div_iff₀ hu2]
      nlinarith [hkey', mul_comm (u ^ 2) (L ^ 2)]
    have hεterm : 0 ≤ ε * (N : ℝ) * Real.log ((N : ℝ) / U) := by positivity
    have hbz := hbzSq U hU1 N hUN
    have hlogVUsq : (Real.log (V / U)) ^ 2 ≤ (4 * (v - u) ^ 2 / u ^ 2) * (N : ℝ) := by
      rw [hlogVU]
      have hvusq : (0:ℝ) ≤ (v - u) ^ 2 := sq_nonneg _
      have h1 : (v - u) ^ 2 * L ^ 2 ≤ (v - u) ^ 2 * ((4 / u ^ 2) * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hLsq hvusq
      have h2 : (v - u) ^ 2 * ((4 / u ^ 2) * (N : ℝ))
          = (4 * (v - u) ^ 2 / u ^ 2) * (N : ℝ) := by ring
      nlinarith [h1, h2]
    have hcN : (4 * (v - u) ^ 2 / u ^ 2) * (N : ℝ) ≤ C₁ * (N : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith [hCbin, hCb.le]) hNnn
    have hkey : (Real.log (V / U)) ^ 2
          + (∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Bz U n) ^ 2)
        ≤ (1 + ε) * (N : ℝ) * Real.log ((N : ℝ) / U) + C₁ * (N : ℝ) := by
      nlinarith [hbz, hlogVUsq, hcN, hεterm, hNnn]
    calc 1 + (∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Bz U n) ^ 2)
            / (Real.log (V / U)) ^ 2
        = ((Real.log (V / U)) ^ 2
            + (∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Bz U n) ^ 2))
            / (Real.log (V / U)) ^ 2 := by
          field_simp
      _ ≤ ((1 + ε) * (N : ℝ) * Real.log ((N : ℝ) / U) + C₁ * (N : ℝ))
            / (Real.log (V / U)) ^ 2 := div_le_div_of_nonneg_right hkey hL2pos.le
      _ = (1 + ε) * (N : ℝ) * Real.log ((N : ℝ) / U) / (Real.log (V / U)) ^ 2
            + C₁ * (N : ℝ) / (Real.log (V / U)) ^ 2 := by ring
  · -- the range `N ≥ V`
    intro N hVN
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      have : (0:ℝ) < V := hVpos
      linarith
    have hN1 : 1 ≤ N := by
      have : (1 : ℝ) ≤ (N : ℝ) := le_trans (le_of_lt hU1) (le_trans hUV.le hVN)
      exact_mod_cast this
    have hdiffb := hdiff U V hU1 hUV.le N hVN
    have hsum : Work.LinnikAreas2.psSum U V N
        = (∑ n ∈ Finset.Icc 1 N,
            (Work.ZeroDensity.Jutila.Lz V n - Work.ZeroDensity.Jutila.Lz U n) ^ 2)
          / (Real.log (V / U)) ^ 2 := by
      rw [Work.LinnikAreas2.psSum,
        Finset.sum_congr rfl (fun n _ => hpsi n), Finset.sum_div]
    rw [hsum]
    have h1 : (∑ n ∈ Finset.Icc 1 N,
          (Work.ZeroDensity.Jutila.Lz V n - Work.ZeroDensity.Jutila.Lz U n) ^ 2)
        ≤ (N : ℝ) * Real.log (V / U) + Cd * (N : ℝ) := hdiffb
    have hcN : Cd * (N : ℝ) ≤ C₁ * (N : ℝ) := mul_le_mul_of_nonneg_right hCdin (by positivity)
    have hkey : (∑ n ∈ Finset.Icc 1 N,
          (Work.ZeroDensity.Jutila.Lz V n - Work.ZeroDensity.Jutila.Lz U n) ^ 2)
        ≤ (1 + ε) * (N : ℝ) * Real.log (V / U) + C₁ * (N : ℝ) := by
      have hεNlog : 0 ≤ ε * (N : ℝ) * Real.log (V / U) := by
        have := le_of_lt hLpos
        have hNnn : (0:ℝ) ≤ (N : ℝ) := by
          have : (0:ℝ) < V := hVpos
          linarith
        positivity
      nlinarith [h1, hcN, hεNlog]
    calc (∑ n ∈ Finset.Icc 1 N,
          (Work.ZeroDensity.Jutila.Lz V n - Work.ZeroDensity.Jutila.Lz U n) ^ 2)
            / (Real.log (V / U)) ^ 2
        ≤ ((1 + ε) * (N : ℝ) * Real.log (V / U) + C₁ * (N : ℝ))
            / (Real.log (V / U)) ^ 2 := div_le_div_of_nonneg_right hkey hL2pos.le
      _ = (1 + ε) * (N : ℝ) / Real.log (V / U)
            + C₁ * (N : ℝ) / (Real.log (V / U)) ^ 2 := by
          rw [show (Real.log (V / U)) ^ 2 = Real.log (V / U) * Real.log (V / U) by ring]
          field_simp

/-- **Graham's `ψ`-sieve (HB (11.13), `ψ` case) from the two-sided `Lz` cross estimate alone.**

The seven-input version `graham_psi_sieve_of` first manufactures the two-sided `Lz` estimate
(`lzCross_two_of`) from five `Bz`-cross inputs and two further ones; everything after that point
depends on the `Lz` cross estimate only, so the sieve is stated here in terms of it.  This is the
form used by the assembly, fed by the *proved* `Work.ZeroDensity.Jutila.lzCross_est`
(`Submission/Work/ZeroDensity/Jutila/MsqSharpCrossLower.lean`), whose axioms are
`[propext, Classical.choice, Quot.sound]`. -/
theorem graham_psi_sieve_of_lz
    (hLzCross : ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ), 1 < w → w ≤ y → ∀ N : ℕ, y ≤ (N : ℝ) →
      |(∑ n ∈ Finset.Icc 1 N, Work.ZeroDensity.Jutila.Lz w n
          * Work.ZeroDensity.Jutila.Lz y n) - (N : ℝ) * Real.log w| ≤ C * (N : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ (u v : ℝ), 0 < u → u < v → ∃ C₁ : ℝ, 0 < C₁ ∧
    ∀ (L U V : ℝ), 0 < L → U = Real.exp (u * L) → V = Real.exp (v * L) →
      (∀ N : ℕ, U ≤ (N : ℝ) → (N : ℝ) ≤ V →
        Work.LinnikAreas2.psSum U V N
          ≤ (1 + ε) * (N : ℝ) * Real.log ((N : ℝ) / U) / (Real.log (V / U)) ^ 2
              + C₁ * (N : ℝ) / (Real.log (V / U)) ^ 2) ∧
      (∀ N : ℕ, V ≤ (N : ℝ) →
        Work.LinnikAreas2.psSum U V N
          ≤ (1 + ε) * (N : ℝ) / Real.log (V / U)
              + C₁ * (N : ℝ) / (Real.log (V / U)) ^ 2) := by
  obtain ⟨Cb, hCb, hbzSq⟩ := bzSq_le_of hLzCross
  obtain ⟨Cd, hCd, hdiff⟩ := lzDiff_le_of hLzCross
  intro u v hu huv
  set C₁ : ℝ := max (Cb + 4 * (v - u) ^ 2 / u ^ 2) Cd + 1 with hC₁def
  have hC₁pos : 0 < C₁ := by rw [hC₁def]; positivity
  refine ⟨C₁, hC₁pos, ?_⟩
  intro L U V hL hU hV
  have hUpos : 0 < U := by rw [hU]; exact Real.exp_pos _
  have hVpos : 0 < V := by rw [hV]; exact Real.exp_pos _
  have hUV : U < V := by
    rw [hU, hV]; exact Real.exp_lt_exp.mpr (by nlinarith)
  have hU1 : 1 < U := by
    rw [hU, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by nlinarith)
  have hlogVU : Real.log (V / U) = (v - u) * L := by
    rw [hV, hU, ← Real.exp_sub, Real.log_exp]; ring
  have hLpos : 0 < Real.log (V / U) := by rw [hlogVU]; nlinarith
  have hL2pos : 0 < (Real.log (V / U)) ^ 2 := by positivity
  have hCbin : Cb + 4 * (v - u) ^ 2 / u ^ 2 ≤ C₁ := by
    rw [hC₁def]; linarith [le_max_left (Cb + 4 * (v - u) ^ 2 / u ^ 2) Cd]
  have hCdin : Cd ≤ C₁ := by
    rw [hC₁def]; linarith [le_max_right (Cb + 4 * (v - u) ^ 2 / u ^ 2) Cd]
  have hpsi : ∀ n : ℕ, Work.LinnikAreas2.psiSq U V n
      = (Work.ZeroDensity.Jutila.Lz V n - Work.ZeroDensity.Jutila.Lz U n) ^ 2
          / (Real.log (V / U)) ^ 2 := by
    intro n
    have h := psiSq_mul_log_sq U V hUpos hUV n
    rw [eq_div_iff (ne_of_gt hL2pos)]
    linarith [h]
  have hBzU1 : Work.ZeroDensity.Jutila.Bz U 1 = 0 :=
    Work.ZeroDensity.Jutila.Bz_one_eq_zero (le_of_lt hU1)
  constructor
  · -- the range `U ≤ N ≤ V`
    intro N hUN hNV
    have hN1 : 1 ≤ N := by
      have : (1 : ℝ) ≤ (N : ℝ) := le_trans (le_of_lt hU1) hUN
      exact_mod_cast this
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hNnn : (0 : ℝ) ≤ (N : ℝ) := hNpos.le
    -- the pointwise description of `Lz_V − Lz_U` on `[1,N]`
    have hpt : ∀ n ∈ Finset.Icc 1 N,
        (Work.ZeroDensity.Jutila.Lz V n - Work.ZeroDensity.Jutila.Lz U n) ^ 2
          = (if n = 1 then (Real.log (V / U)) ^ 2
              else (Work.ZeroDensity.Jutila.Bz U n) ^ 2) := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      by_cases hn1 : n = 1
      · subst hn1
        rw [if_pos rfl, Work.ZeroDensity.Jutila.Lz_one_eq V (le_of_lt (lt_trans hU1 hUV)),
          Work.ZeroDensity.Jutila.Lz_one_eq U (le_of_lt hU1),
          ← Real.log_div (ne_of_gt hVpos) (ne_of_gt hUpos)]
      · rw [if_neg hn1]
        have h2 : 2 ≤ n := by omega
        have hnV : (n : ℝ) ≤ V := le_trans (by exact_mod_cast hn.2) hNV
        have hBzV : Work.ZeroDensity.Jutila.Bz V n = 0 :=
          Work.ZeroDensity.Jutila.Bz_eq_zero_of_le hVpos.le hnV
        have hLzV : Work.ZeroDensity.Jutila.Lz V n = ArithmeticFunction.vonMangoldt n := by
          rw [Work.ZeroDensity.Jutila.Lz_eq_vonMangoldt_add_Bz hVpos h2, hBzV, add_zero]
        have hLzU : Work.ZeroDensity.Jutila.Lz U n
            = ArithmeticFunction.vonMangoldt n + Work.ZeroDensity.Jutila.Bz U n :=
          Work.ZeroDensity.Jutila.Lz_eq_vonMangoldt_add_Bz hUpos h2
        rw [hLzV, hLzU]; ring
    have hI : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hsum1 : (∑ n ∈ Finset.Icc 1 N,
          (if n = 1 then (Real.log (V / U)) ^ 2
            else (Work.ZeroDensity.Jutila.Bz U n) ^ 2))
        = (Real.log (V / U)) ^ 2
          + ∑ n ∈ Finset.Icc 2 N, (Work.ZeroDensity.Jutila.Bz U n) ^ 2 := by
      rw [hI, Finset.sum_insert (by simp), if_pos rfl]
      congr 1
      refine Finset.sum_congr rfl (fun n hn => ?_)
      rw [if_neg]
      simp only [Finset.mem_Icc] at hn
      omega
    have hsum2 : (∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Bz U n) ^ 2)
        = ∑ n ∈ Finset.Icc 2 N, (Work.ZeroDensity.Jutila.Bz U n) ^ 2 := by
      rw [hI, Finset.sum_insert (by simp), hBzU1]
      norm_num
    have hsum3 : Work.LinnikAreas2.psSum U V N
        = 1 + (∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Bz U n) ^ 2)
            / (Real.log (V / U)) ^ 2 := by
      rw [Work.LinnikAreas2.psSum]
      have hstep : (∑ n ∈ Finset.Icc 1 N, Work.LinnikAreas2.psiSq U V n)
          = (∑ n ∈ Finset.Icc 1 N,
              (if n = 1 then (Real.log (V / U)) ^ 2
                else (Work.ZeroDensity.Jutila.Bz U n) ^ 2)) / (Real.log (V / U)) ^ 2 := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl (fun n hn => by rw [hpsi n, hpt n hn])
      rw [hstep, hsum1, hsum2, add_div, div_self (ne_of_gt hL2pos)]
    rw [hsum3]
    have hbz := hbzSq U hU1 N hUN
    have hlogNU : 0 ≤ Real.log ((N : ℝ) / U) :=
      Real.log_nonneg (by rw [one_le_div hUpos]; exact hUN)
    -- `L² ≤ (4/u²)·N`
    have hLsq : L ^ 2 ≤ (4 / u ^ 2) * (N : ℝ) := by
      have huL : 0 < u * L / 2 := by positivity
      have hexp_ge : u * L / 2 ≤ Real.exp (u * L / 2) := by
        linarith [Real.add_one_le_exp (u * L / 2)]
      have hexp2 : Real.exp (u * L / 2) * Real.exp (u * L / 2) = Real.exp (u * L) := by
        rw [← Real.exp_add]; ring_nf
      have h1 : (u * L / 2) ^ 2 ≤ Real.exp (u * L) := by
        calc (u * L / 2) ^ 2 = (u * L / 2) * (u * L / 2) := by ring
          _ ≤ Real.exp (u * L / 2) * Real.exp (u * L / 2) :=
              mul_le_mul hexp_ge hexp_ge huL.le (Real.exp_pos _).le
          _ = Real.exp (u * L) := hexp2
      have hexpN : Real.exp (u * L) ≤ (N : ℝ) := by rw [← hU]; exact hUN
      have hu2 : 0 < u ^ 2 := by positivity
      have hkey : u ^ 2 * L ^ 2 / 4 ≤ (N : ℝ) := by nlinarith [h1, hexpN, sq_nonneg (u * L)]
      have hkey' : u ^ 2 * L ^ 2 ≤ 4 * (N : ℝ) := by nlinarith [hkey, hu2]
      rw [show 4 / u ^ 2 * (N : ℝ) = (4 * (N : ℝ)) / u ^ 2 by ring, le_div_iff₀ hu2]
      nlinarith [hkey', mul_comm (u ^ 2) (L ^ 2)]
    have hεterm : 0 ≤ ε * (N : ℝ) * Real.log ((N : ℝ) / U) := by positivity
    have hbz := hbzSq U hU1 N hUN
    have hlogVUsq : (Real.log (V / U)) ^ 2 ≤ (4 * (v - u) ^ 2 / u ^ 2) * (N : ℝ) := by
      rw [hlogVU]
      have hvusq : (0:ℝ) ≤ (v - u) ^ 2 := sq_nonneg _
      have h1 : (v - u) ^ 2 * L ^ 2 ≤ (v - u) ^ 2 * ((4 / u ^ 2) * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hLsq hvusq
      have h2 : (v - u) ^ 2 * ((4 / u ^ 2) * (N : ℝ))
          = (4 * (v - u) ^ 2 / u ^ 2) * (N : ℝ) := by ring
      nlinarith [h1, h2]
    have hcN : (4 * (v - u) ^ 2 / u ^ 2) * (N : ℝ) ≤ C₁ * (N : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith [hCbin, hCb.le]) hNnn
    have hkey : (Real.log (V / U)) ^ 2
          + (∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Bz U n) ^ 2)
        ≤ (1 + ε) * (N : ℝ) * Real.log ((N : ℝ) / U) + C₁ * (N : ℝ) := by
      nlinarith [hbz, hlogVUsq, hcN, hεterm, hNnn]
    calc 1 + (∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Bz U n) ^ 2)
            / (Real.log (V / U)) ^ 2
        = ((Real.log (V / U)) ^ 2
            + (∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Bz U n) ^ 2))
            / (Real.log (V / U)) ^ 2 := by
          field_simp
      _ ≤ ((1 + ε) * (N : ℝ) * Real.log ((N : ℝ) / U) + C₁ * (N : ℝ))
            / (Real.log (V / U)) ^ 2 := div_le_div_of_nonneg_right hkey hL2pos.le
      _ = (1 + ε) * (N : ℝ) * Real.log ((N : ℝ) / U) / (Real.log (V / U)) ^ 2
            + C₁ * (N : ℝ) / (Real.log (V / U)) ^ 2 := by ring
  · -- the range `N ≥ V`
    intro N hVN
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      have : (0:ℝ) < V := hVpos
      linarith
    have hN1 : 1 ≤ N := by
      have : (1 : ℝ) ≤ (N : ℝ) := le_trans (le_of_lt hU1) (le_trans hUV.le hVN)
      exact_mod_cast this
    have hdiffb := hdiff U V hU1 hUV.le N hVN
    have hsum : Work.LinnikAreas2.psSum U V N
        = (∑ n ∈ Finset.Icc 1 N,
            (Work.ZeroDensity.Jutila.Lz V n - Work.ZeroDensity.Jutila.Lz U n) ^ 2)
          / (Real.log (V / U)) ^ 2 := by
      rw [Work.LinnikAreas2.psSum,
        Finset.sum_congr rfl (fun n _ => hpsi n), Finset.sum_div]
    rw [hsum]
    have h1 : (∑ n ∈ Finset.Icc 1 N,
          (Work.ZeroDensity.Jutila.Lz V n - Work.ZeroDensity.Jutila.Lz U n) ^ 2)
        ≤ (N : ℝ) * Real.log (V / U) + Cd * (N : ℝ) := hdiffb
    have hcN : Cd * (N : ℝ) ≤ C₁ * (N : ℝ) := mul_le_mul_of_nonneg_right hCdin (by positivity)
    have hkey : (∑ n ∈ Finset.Icc 1 N,
          (Work.ZeroDensity.Jutila.Lz V n - Work.ZeroDensity.Jutila.Lz U n) ^ 2)
        ≤ (1 + ε) * (N : ℝ) * Real.log (V / U) + C₁ * (N : ℝ) := by
      have hεNlog : 0 ≤ ε * (N : ℝ) * Real.log (V / U) := by
        have := le_of_lt hLpos
        have hNnn : (0:ℝ) ≤ (N : ℝ) := by
          have : (0:ℝ) < V := hVpos
          linarith
        positivity
      nlinarith [h1, hcN, hεNlog]
    calc (∑ n ∈ Finset.Icc 1 N,
          (Work.ZeroDensity.Jutila.Lz V n - Work.ZeroDensity.Jutila.Lz U n) ^ 2)
            / (Real.log (V / U)) ^ 2
        ≤ ((1 + ε) * (N : ℝ) * Real.log (V / U) + C₁ * (N : ℝ))
            / (Real.log (V / U)) ^ 2 := div_le_div_of_nonneg_right hkey hL2pos.le
      _ = (1 + ε) * (N : ℝ) / Real.log (V / U)
            + C₁ * (N : ℝ) / (Real.log (V / U)) ^ 2 := by
          rw [show (Real.log (V / U)) ^ 2 = Real.log (V / U) * Real.log (V / U) by ring]
          field_simp

/-- The seven-input form `graham_psi_sieve_of`, derived from `graham_psi_sieve_of_lz`. -/
theorem graham_psi_sieve_of_via_lz
    (hCrossEq : ∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N : ℝ) →
      (∑ n ∈ Finset.Icc 1 N, Work.ZeroDensity.Jutila.Bz w n * Work.ZeroDensity.Jutila.Bz y n)
        = Work.ZeroDensity.Jutila.czCross w y N)
    (hCont : ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N : ℝ) →
      |Work.ZeroDensity.Jutila.czModelCont w y N
        - (N : ℝ) * Real.log ((N : ℝ) / y)| ≤ C * (N : ℝ))
    (hB : ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N : ℝ) →
      |Work.ZeroDensity.Jutila.czModelB w y N| ≤ C * (N : ℝ))
    (hFloor : ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N : ℝ) →
      |Work.ZeroDensity.Jutila.czModelFloor w y N
        - Work.ZeroDensity.Jutila.czModelCont w y N| ≤ C * (N : ℝ))
    (hAbel : ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N : ℝ) →
      |Work.ZeroDensity.Jutila.czCross w y N
        - (Work.ZeroDensity.Jutila.czModelFloor w y N
            - Work.ZeroDensity.Jutila.czModelB w y N)| ≤ C * (N : ℝ))
    (hMul : ∃ C : ℝ, 0 < C ∧ ∀ (z : ℝ), 1 ≤ z → ∀ N : ℕ, z ≤ (N : ℝ) →
      |(∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n
          * Work.ZeroDensity.Jutila.Bz z n)
        + (N : ℝ) * Real.log ((N : ℝ) / z)| ≤ C * (N : ℝ))
    (hEasy : ∃ C : ℝ, 0 < C ∧ ∀ (z₁ z₂ : ℝ), 1 ≤ z₁ → z₁ ≤ z₂ → ∀ N : ℕ, z₂ ≤ (N : ℝ) →
      |(∑ n ∈ Finset.Icc 1 N, Work.ZeroDensity.Jutila.Lz z₁ n
          * Work.ZeroDensity.Jutila.Lz z₂ n) - (N : ℝ) * Real.log z₁|
        ≤ C * ((N : ℝ) + z₁ * z₂))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ (u v : ℝ), 0 < u → u < v → ∃ C₁ : ℝ, 0 < C₁ ∧
    ∀ (L U V : ℝ), 0 < L → U = Real.exp (u * L) → V = Real.exp (v * L) →
      (∀ N : ℕ, U ≤ (N : ℝ) → (N : ℝ) ≤ V →
        Work.LinnikAreas2.psSum U V N
          ≤ (1 + ε) * (N : ℝ) * Real.log ((N : ℝ) / U) / (Real.log (V / U)) ^ 2
              + C₁ * (N : ℝ) / (Real.log (V / U)) ^ 2) ∧
      (∀ N : ℕ, V ≤ (N : ℝ) →
        Work.LinnikAreas2.psSum U V N
          ≤ (1 + ε) * (N : ℝ) / Real.log (V / U)
              + C₁ * (N : ℝ) / (Real.log (V / U)) ^ 2) :=
  graham_psi_sieve_of_lz (lzCross_two_of (bzCross_of hCrossEq hCont hB hFloor hAbel hMul hEasy) hMul hEasy) ε hε

end

end Work.LinnikAreas2.PsiSieve2
