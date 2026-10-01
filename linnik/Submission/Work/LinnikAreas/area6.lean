import Mathlib
import Submission.Work.LinnikContract.Areas
import Submission.Work.LinnikAreas.SiegelBase
import Submission.Work.LinnikAreas.siegelSimpleInput
import Submission.Work.LinnikAreas.siegelRestLow
import Submission.Work.LinnikAreas.siegelRestHigh
import Submission.Work.LinnikAreas.siegelZeroWeightSummable
import Submission.Work.LinnikAreas.siegelExpansion
import Submission.Work.LinnikAreas.area6Box
import Submission.Work.LinnikAreas.area6Top
import Submission.Work.LinnikAreas.boxSumCap
import Submission.Work.SiegelAbsorb.area6Siegel
import Submission.Work.LinnikAreas.RepulsionCap
import Submission.Work.LinnikAreas.PairDensityCap
import Submission.Work.LinnikAreas.siegelRestLowCap
import Submission.Work.LinnikAreas.logFreeFamHalfOfNonPrincipal
import Submission.Work.LinnikAreas.logFreeFamHeightOfNonPrincipal
import Submission.Work.LinnikAreas.RestHighFree
import Submission.Work.LinnikAreas.RestHighCombine
import Submission.Work.LinnikAreas.BGTZRepE
import Submission.Work.LinnikAreas.BGTZ.ZFRInput_exists
import Submission.Work.LinnikAreas.BGTZ.RestHighBGTZGenC
import Submission.Work.LinnikAreas.area6CapChain
import Submission.Work.LinnikAreas.logFreeFamOfTwelveFifths
import Submission.Work.LinnikAreas.area6OfTwelveFifths
import Submission.Work.LinnikAreas.area6OfCores2
import Submission.Work.LinnikAreas.area6OfCoreNodes
import Submission.Work.ZeroDensity.Basic
import Submission.Work.ZeroDensity.Main
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_realZero_siegel_uniform
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip
import Submission.Commons.NumberTheory.Linnik.tentWeight_spec

/-! Guidance from the project lead (the requester):

CONTEXT (project lead). This is an area of the FROZEN Linnik contract (Submission/Work/LinnikContract/Areas.lean;
composition linnik_of_areas PROVED, so proving all seven areas closes the problem). Read first:
* Submission/Work/LinnikPlan/ROUTE_LEAD.md: §1.2 constants, §3.1 your area with the source and proof sketch, §4 numerics, §5 risks;
* LinnikContract/Defs.lean.
Never use the quarantined lemmas (LinnikContract/Quarantine.lean: q-dependent constants); the build guard will fail. The seeded
Submission/Commons/** is a large sorry-free analytic-number-theory library (ROUTE_LEAD §2.1 inventory); reuse it and do not re-request what
exists. Parallelise: request all independent pieces at once.

Area6 = SiegelCase: [HB90] (Heath-Brown 1990, the Siegel-zero case: Deuring–Heilbronn repulsion gives a much better exponent when an
exceptional real zero exists), for SiegelZero q lamS, q ≥ q₀(lamS). ROUTE_LEAD offers the alternative of a log-free Deuring–Heilbronn density
bound; pick whichever is shorter.
-/

/-! ## 0. What is in this file, and what is in `SiegelBase`

`Submission.Work.LinnikAreas.SiegelBase` holds the *vocabulary* of AREA 6 (the weighted class
sums of HB §13, the zero sums, the counting functions and the five input `Prop`s
`RepulsionInput`, `PairDensityInput`, `PairDensityHeightInput`, `SimpleInput`, `ExpansionInput`,
`BoxSumBound`); this file holds the *proofs*, and ends with the frozen target
`Work.LinnikAreas.area6 : Work.LinnikContract.Area6`.

The splitting is forced by the frozen statement: every lemma about the `SiegelBase` vocabulary can
be stated and proved in files that import `SiegelBase` (not this file), and are then importable
here.  Files that import `area6` (e.g. `siegelZeroSimple.lean`) state their results in terms of
`Work.LinnikContract.*` only, so their content can also be reassembled here from their own
sub-modules.

## 1. The mathematics of the Siegel case

`Area6 : Prop := ∃ lamS > 0, ∃ q₀, ∀ q ≥ q₀, SiegelZero q lamS → ∀ a, a.Coprime q →
∃ prime p ≡ a mod q, p ≤ q^{11/2}`.

AREA 6 is unconditional and `SiegelZero q lamS` is not refutable, so the classical argument of
HB92 §13--§14 (with the `λ₁ → 0` end replaced by a `λ₁`-saving Deuring--Heilbronn density
estimate, ROUTE_LEAD §3.1 route (ii)) has to be run.  Fix

* `L = 11/2`, `K = 3/10`, `a₀ = L - 2K = 49/10`, `𝓛 = log q`, `f = tentWeight L K`
  (supported on `(L-2K, L]`, Laplace transform `Hk L K`), and
* `S(a) = Σ_{n ≡ a (q)} Λ(n)/n · f(log n/𝓛)` (a finite sum: only `n ≤ q^L` contributes),
* `χ₁` real mod `q` with the exceptional real zero `β₁ = 1 - λ₁/𝓛`, `λ₁ = lamOf q β₁`.

The argument (route (ii) of ROUTE_LEAD §3.1, i.e. HB92 §13--§14 with the uncapped repulsion and
the `λ₁`-saving (Deuring--Heilbronn) density estimate):

1. **Prime extraction** (`prime_of_classSum_pos`).  `S(a) > (its non-prime part)` implies that some
   prime term is positive, hence a prime `p ≡ a (q)` with `p ≤ q^L` exists.
2. **Class-sum expansion** (HB §13.1--13.2 = the contract's AREA 2; `ExpansionInput R`).
   With a box radius `R`,
   `𝓛⁻¹S(a) = φ(q)⁻¹(K² - Σ_χ Re(χ̄(a)·boxSum q L K R χ)) + O(q⁻¹)`,
   the sum running over *all* characters, so the principal character contributes the `ζ`-zeros
   (this is why the PNT cannot be used here: its error is bigger than `λ₁`).
3. **The exceptional zero.**  By `SimpleInput` it is simple, so its box contribution is
   `Hk(L,K,λ₁) = K²e^{-a₀λ₁}(1-Kλ₁)² ≤ K²e^{-a₀λ₁} = K² - K²(1-e^{-a₀λ₁})`; the pole of the
   principal character contributes `K²`.
4. **Repulsion and density** (`RepulsionInput`, `PairDensityInput`, `PairDensityHeightInput`).
   * Every pair `(χ,ρ) ≠ (χ₁,β₁)` with `|Im ρ| ≤ 1` has `λ(ρ) ≥ Λ := c_r log(1/λ₁)`
     (Deuring--Heilbronn; this is the form that stays true as `λ₁ → 0`, unlike HB's sharp
     Lemmas 8.3/8.7, whose constants are only effective for `λ₁` bounded below).  Choosing
     `lamS` with `Λ > R` makes the box contain *only* the exceptional zero.
   * `N(t) :=` (multiplicity-weighted number of pairs `(χ,ρ) ≠ (χ₁,β₁)` with `λ ≤ t`,
     `|Im| ≤ 1`) satisfies `N(t) ≤ Cλ₁e^{ct}` with `c < 49/10` (log-free Deuring--Heilbronn
     density estimate `Σ_χ N*(σ,T,χ) ≤ Cλ₁(qT)^{c(1-σ)}` at `T = 1`), and the same estimate in the
     height direction gives `N(t,T) ≤ Cλ₁e^{ct}T^{c'}` with `c' < 2`.
   * With `Λ = c_r log(1/λ₁)`, Abel summation in `λ` over the working region gives
     `Σ_{|γ| ≤ 1, λ ≥ Λ} e^{-a₀λ} ≤ C'λ₁^{1+δ}`, `δ = c_r(a₀-c) > 0`; the far zeros
     (`|γ| > 1`) carry the weight `‖Hk‖ ≤ 4e^{-a₀λ}/‖(1-ρ)𝓛‖²` and the dyadic height summation
     gives `≤ C''λ₁𝓛^{c'-2} = o(λ₁)`.
5. **Arithmetic** (`siegel_numeric_close`).  Since `C'λ₁^{1+δ} + C''λ₁𝓛^{c'-2} < K²a₀λ₁/2` for
   `λ₁ ≤ lamS` small and `q ≥ q₀` large, `BoxSumBound` follows from steps 3--4, and then
   `𝓛⁻¹S(a) > 0`: the `p^k`, `k ≥ 2` terms are `≪ q^{-(L-2K)/2}log q`, `λ₁ ≥ C log q/√q`
   (Siegel's theorem, `lamOf_lower_bound`) dominates the `q⁻²` error of the expansion, and step 1
   produces the prime. -/

namespace Work.LinnikAreas

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

set_option linter.unusedVariables false

namespace Siegel

open Work.LinnikContract

/-! ## 5. The arithmetic closing step of the Siegel case -/

/-- `1 - e^{-t} ≥ t/2` for `0 ≤ t ≤ 1`. -/
private lemma one_sub_exp_neg_ge_half {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t / 2 ≤ 1 - Real.exp (-t) := by
  have h1 : (1 : ℝ) + t ≤ Real.exp t := by
    have := Real.add_one_le_exp t
    linarith
  have hpos : 0 < 1 + t := by linarith
  have hinv : (Real.exp t)⁻¹ ≤ (1 + t)⁻¹ := inv_anti₀ hpos h1
  have htinv : (1 + t)⁻¹ ≤ 1 - t / 2 := by
    rw [inv_le_iff_one_le_mul₀ hpos]
    nlinarith
  rw [Real.exp_neg]
  linarith


/-- **The exceptional zero's contribution to the box sum.**  Since the exceptional zero is simple
(`siegelZeroSimple`) its box contribution is `K²e^{-a₀λ}(1-Kλ)²` (there `a₀ = L - 2K = 49/10`,
`K = 3/10`), and for `λ ≤ 1/100` this is at most `K²(1 - a₀λ/2)`: the excess of the pole term over
the exceptional zero, which is the margin the other zeros have to fit into. -/
theorem exceptional_le (K a x : ℝ) (hK : 0 < K) (ha : 0 < a) (hx0 : 0 ≤ x) (hax : a * x ≤ 1)
    (hKx : K * x ≤ 1) :
    K ^ 2 * Real.exp (-(a * x)) * (1 - K * x) ^ 2 ≤ K ^ 2 * (1 - a * x / 2) := by
  have hexp : Real.exp (-(a * x)) ≤ 1 - a * x / 2 := by
    have h := one_sub_exp_neg_ge_half (by positivity : (0 : ℝ) ≤ a * x) hax
    linarith
  have h1 : K * x ≤ 1 := hKx
  have h2 : (0 : ℝ) ≤ K * x := by positivity
  have hsq : (1 - K * x) ^ 2 ≤ 1 := by nlinarith
  have h3 : (0 : ℝ) ≤ 1 - a * x / 2 := by nlinarith
  have h4 : Real.exp (-(a * x)) * (1 - K * x) ^ 2 ≤ (1 - a * x / 2) * 1 :=
    mul_le_mul hexp hsq (sq_nonneg _) h3
  calc K ^ 2 * Real.exp (-(a * x)) * (1 - K * x) ^ 2
      = K ^ 2 * (Real.exp (-(a * x)) * (1 - K * x) ^ 2) := by ring
    _ ≤ K ^ 2 * ((1 - a * x / 2) * 1) := mul_le_mul_of_nonneg_left h4 (sq_nonneg K)
    _ = K ^ 2 * (1 - a * x / 2) := by ring

/-- **The arithmetic closing lemma of the Siegel case.**  The excess of the pole term over the
exceptional-zero term is `K²(1 - e^{-a x})` (`x = λ₁`), while the total contribution of all the
*other* zeros -- the zeros of the other characters in the box, the other zeros of `χ₁`, and the
far zeros -- is at most `C·x^{1+δ}` with `δ > 0` (this is the shape produced by the
Deuring--Heilbronn repulsion together with the `λ₁`-saving log-free zero-density estimate and the
class-sum expansion of HB §13).  Then there is a threshold `lamS > 0` such that for every
`x ∈ (0, lamS]` the difference is strictly positive: the class sum is positive and the progression
contains a prime `≤ q^{11/2}`. -/
theorem siegel_numeric_close (K a C δ : ℝ) (hK : 0 < K) (ha : 0 < a) (hC : 1 ≤ C) (hδ : 0 < δ) :
    ∃ lamS : ℝ, 0 < lamS ∧ lamS ≤ 1 ∧
      ∀ x : ℝ, 0 < x → x ≤ lamS → C * x ^ (1 + δ) < K ^ 2 * (1 - Real.exp (-(a * x))) := by
  have hposC : 0 < C := lt_of_lt_of_le one_pos hC
  have hbase : 0 < K ^ 2 * a / (4 * C) := by positivity
  set L0 : ℝ := (K ^ 2 * a / (4 * C)) ^ (1 / δ) with hL0
  have hL0pos : 0 < L0 := by rw [hL0]; exact Real.rpow_pos_of_pos hbase _
  have hL0δ : L0 ^ δ = K ^ 2 * a / (4 * C) := by
    rw [hL0, ← Real.rpow_mul hbase.le]
    have h1 : (1 / δ) * δ = 1 := by field_simp
    rw [h1, Real.rpow_one]
  refine ⟨min (min 1 (1 / a)) L0, lt_min (lt_min one_pos (by positivity)) hL0pos, ?_, ?_⟩
  · exact le_trans (min_le_left _ _) (min_le_left _ _)
  · intro x hx0 hxle
    have hx1 : x ≤ 1 := le_trans hxle (le_trans (min_le_left _ _) (min_le_left _ _))
    have hxa : x ≤ 1 / a := le_trans hxle (le_trans (min_le_left _ _) (min_le_right _ _))
    have hxL : x ≤ L0 := le_trans hxle (min_le_right _ _)
    have hax1 : a * x ≤ 1 := by
      have h2 : a * x ≤ a * (1 / a) := mul_le_mul_of_nonneg_left hxa ha.le
      have h3 : a * (1 / a) = 1 := by field_simp
      linarith
    -- the pole term exceeds the exceptional-zero term by at least `K²·a·x/2`
    have hmain : K ^ 2 * (a * x / 2) ≤ K ^ 2 * (1 - Real.exp (-(a * x))) :=
      mul_le_mul_of_nonneg_left
        (one_sub_exp_neg_ge_half (by positivity : (0:ℝ) ≤ a * x) hax1) (sq_nonneg K)
    -- the other zeros contribute at most `C·x^{1+δ} ≤ K²·a·x/4`
    have hxd : x ^ δ ≤ K ^ 2 * a / (4 * C) := by
      calc x ^ δ ≤ L0 ^ δ := Real.rpow_le_rpow hx0.le hxL hδ.le
        _ = K ^ 2 * a / (4 * C) := hL0δ
    have h2 : C * x ^ δ ≤ K ^ 2 * a / 4 := by
      have h3 := mul_le_mul_of_nonneg_left hxd hposC.le
      have h4 : C * (K ^ 2 * a / (4 * C)) = K ^ 2 * a / 4 := by
        field_simp
      rw [h4] at h3
      exact h3
    have hnoise : C * x ^ (1 + δ) ≤ K ^ 2 * a / 4 * x := by
      rw [Real.rpow_add hx0, Real.rpow_one]
      nlinarith [h2, hx0]
    have hstrict : K ^ 2 * a / 4 * x < K ^ 2 * a / 2 * x := by
      have hpos : 0 < K ^ 2 * a / 4 * x := by positivity
      nlinarith [hpos]
    have hmain' : K ^ 2 * a / 2 * x ≤ K ^ 2 * (1 - Real.exp (-(a * x))) := by
      have h3 : K ^ 2 * (a * x / 2) = K ^ 2 * a / 2 * x := by ring
      linarith [hmain]
    linarith

/-- The instance of `siegel_numeric_close` used by AREA 6 when `K = 3/10`, `a = 49/10` and the
`λ₁`-saving exponent is `δ = (49/10 - c)c_r` (see `Siegel.numeric_close_of_constants` below for
the general exponent). -/
theorem siegel_numeric_close_inst (C : ℝ) (hC : 1 ≤ C) :
    ∃ lamS : ℝ, 0 < lamS ∧ lamS ≤ 1 ∧ ∀ x : ℝ, 0 < x → x ≤ lamS →
      C * x ^ (6 / 5 : ℝ) < (3 / 10 : ℝ) ^ 2 * (1 - Real.exp (-(49 / 10 * x))) := by
  have hδ : (0:ℝ) < 1 / 5 := by norm_num
  obtain ⟨lamS, h0, h1, h2⟩ := siegel_numeric_close (3 / 10) (49 / 10) C (1 / 5)
    (by norm_num) (by norm_num) hC hδ
  refine ⟨lamS, h0, h1, fun x hx hxle => ?_⟩
  have h := h2 x hx hxle
  have hpow : x ^ (1 + 1 / 5 : ℝ) = x ^ (6 / 5 : ℝ) := by norm_num
  rwa [hpow] at h



/- The top-level argument of AREA 6 (`vmClassSum_eq_prime_add_nonPrime`,
`prime_of_classSum_pos`, `Siegel.area6_of`) now lives in `Submission.Work.LinnikAreas.area6Top`. -/

/-- **`BoxSumBound R` from the five inputs**, for every `R ≥ 1`.

This is the assembly of the Siegel case: the repulsion makes the box contain only the exceptional
zero, the `λ₁`-saving counting estimates control the two pieces of the rest of the zero sum
(`restLowZeroSum` in the working region, `restHighZeroSum` in the far heights), and the arithmetic
of `siegel_close_arith` turns the resulting `K²e^{-a₀λ₁} + C₁λ₁^{1+δ} + C₂λ₁𝓛^{e}` into
`K²(1 - a₀λ₁/2)`. -/
theorem boxSumBound_of_inputs (R : ℝ) (hR : 1 ≤ R)
    (hSimple : SimpleInput) (hRep : RepulsionInput)
    (hsum : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), Summable (fun ρ : ℂ =>
      (zeroMult χ ρ : ℝ) * ‖Hk (11 / 2) (3 / 10) ((1 - ρ) * (Real.log q : ℂ))‖))
    (hLow : ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ,
      ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
        χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 → zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
        lamOf q (β₁ : ℂ) ≤ 1 / 2 →
        restLowZeroSum χ₁ (β₁ : ℂ) (11 / 2) (3 / 10)
          ≤ C * (lamOf q (β₁ : ℂ)) ^ (1 + δ))
    (hHigh : ∃ C : ℝ, 0 < C ∧ ∃ e : ℝ, e < 0 ∧ ∃ q₀ : ℕ,
      ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
        χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 → zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
        lamOf q (β₁ : ℂ) ≤ 1 / 2 →
        restHighZeroSum χ₁ (β₁ : ℂ) (11 / 2) (3 / 10)
          ≤ C * lamOf q (β₁ : ℂ) * (Real.log q) ^ e) :
    BoxSumBound R := by
  obtain ⟨C₁, hC₁pos, δ, hδpos, qL, hLow'⟩ := hLow
  obtain ⟨C₂, hC₂pos, e, heneg, qH, hHigh'⟩ := hHigh
  obtain ⟨cr, hcrpos, qR, hRep'⟩ := hRep
  obtain ⟨qS, hSimple'⟩ := hSimple
  have ha₀ : (0 : ℝ) < 49 / 10 := by norm_num
  have hK : (0 : ℝ) < 3 / 10 := by norm_num
  have hK2 : (0 : ℝ) < (3 / 10 : ℝ) ^ 2 := by norm_num
  set e' : ℝ := -e with he'def
  have he'pos : 0 < e' := by rw [he'def]; linarith
  set L₀ : ℝ := (8 * C₂ / ((3 / 10 : ℝ) ^ 2 * (49 / 10))) ^ (1 / e') with hL₀def
  have hL₀pos : 0 < L₀ := by rw [hL₀def]; exact Real.rpow_pos_of_pos (by positivity) _
  have hL₀pow : L₀ ^ e = (3 / 10 : ℝ) ^ 2 * (49 / 10) / (8 * C₂) := by
    rw [hL₀def, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ 8 * C₂ / ((3/10)^2 * (49/10)))]
    have hene : e ≠ 0 := ne_of_lt heneg
    have h1 : (1 / e') * e = -1 := by
      rw [he'def]
      field_simp
    rw [h1, Real.rpow_neg_one, inv_div]
  -- thresholds
  set qR' : ℕ := ⌈Real.exp R⌉₊ + 1 with hqR'def
  set qH' : ℕ := ⌈Real.exp L₀⌉₊ + 1 with hqH'def
  set lamS : ℝ := min (min (1 / 100) (min (1 / 2) (2 / (5 * (49 / 10)))))
    (min (((3 / 10 : ℝ) ^ 2 * (49 / 10) / (8 * C₁)) ^ (1 / δ))
      (Real.exp (-(R + 1) / cr))) with hlamSdef
  have hlamSpos : 0 < lamS := by
    rw [hlamSdef]
    exact lt_min (lt_min (by norm_num) (lt_min (by norm_num) (by norm_num)))
      (lt_min (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _))
  refine ⟨lamS, hlamSpos, ?_, max (max qS qR) (max (max qL qH) (max (max 3 qR') qH')), ?_⟩
  · rw [hlamSdef]
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  intro q hq hqne χ₁ β₁ hχ hsq hβ1 hz hle a ha
  haveI := hqne
  have hqS : qS ≤ q :=
    le_trans (le_trans (le_max_left qS qR) (le_max_left (max qS qR) _)) hq
  have hqR : qR ≤ q :=
    le_trans (le_trans (le_max_right qS qR) (le_max_left (max qS qR) _)) hq
  have hqL : qL ≤ q := le_trans (le_trans (le_trans (le_max_left qL qH)
    (le_max_left (max qL qH) _)) (le_max_right (max qS qR) _)) hq
  have hqH : qH ≤ q := le_trans (le_trans (le_trans (le_max_right qL qH)
    (le_max_left (max qL qH) _)) (le_max_right (max qS qR) _)) hq
  have hq3 : 3 ≤ q := le_trans (le_trans (le_trans (le_trans (le_max_left 3 qR')
    (le_max_left (max 3 qR') qH')) (le_max_right (max qL qH) _))
    (le_max_right (max qS qR) _)) hq
  have hqR' : qR' ≤ q := le_trans (le_trans (le_trans (le_trans (le_max_right 3 qR')
    (le_max_left (max 3 qR') qH')) (le_max_right (max qL qH) _))
    (le_max_right (max qS qR) _)) hq
  have hqH' : qH' ≤ q := le_trans (le_trans (le_trans (le_max_right (max 3 qR') qH')
    (le_max_right (max qL qH) _)) (le_max_right (max qS qR) _)) hq
  have hq2 : 2 ≤ q := by omega
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hRlog : R < Real.log q := by
    have h1 : Real.exp R < (qR' : ℝ) := by
      rw [hqR'def]
      have h2 : Real.exp R ≤ ((⌈Real.exp R⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      have h3 : ((⌈Real.exp R⌉₊ : ℕ) : ℝ) < ((⌈Real.exp R⌉₊ : ℕ) : ℝ) + 1 := by norm_num
      push_cast
      linarith
    have h2 : (qR' : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqR'
    have h3 : Real.log (Real.exp R) < Real.log q :=
      Real.log_lt_log (Real.exp_pos R) (lt_of_lt_of_le h1 h2)
    rwa [Real.log_exp] at h3
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR
  set lam : ℝ := lamOf q (β₁ : ℂ) with hlamdef
  have hlampos : 0 < lam := lamOf_pos hχ hβ1 hz
  have hlam1 : lam ≤ 1 / 100 :=
    le_trans hle (le_trans (min_le_left _ _) (min_le_left _ _))
  have hlam2' : lam ≤ min (1 / 2) (2 / (5 * (49 / 10))) :=
    le_trans hle (le_trans (min_le_left _ _) (min_le_right _ _))
  have hlam2 : lam ≤ 1 / 2 := le_trans hlam2' (min_le_left _ _)
  have hlamA : lam ≤ ((3 / 10 : ℝ) ^ 2 * (49 / 10) / (8 * C₁)) ^ (1 / δ) :=
    le_trans hle (le_trans (min_le_right _ _) (min_le_left _ _))
  have hlamE : lam ≤ Real.exp (-(R + 1) / cr) :=
    le_trans hle (le_trans (min_le_right _ _) (min_le_right _ _))
  -- the repulsion in the form used below
  have hrep : ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), zeroMult χ ρ ≠ 0 → |ρ.im| ≤ 1 →
      ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ)) → cr * Real.log (1 / lam) ≤ lamOf q ρ := by
    intro χ ρ hzρ him hne
    rw [hlamdef]
    exact hRep' q hqR χ₁ β₁ hχ hsq hβ1 hz hlam2 χ ρ hzρ him hne
  have hΛR : R < cr * Real.log (1 / lam) := by
    have h1 : Real.exp ((R + 1) / cr) ≤ 1 / lam := by
      have h2 : lam ≤ Real.exp (-(R + 1) / cr) := hlamE
      have h3 : 1 / Real.exp (-(R + 1) / cr) ≤ 1 / lam :=
        one_div_le_one_div_of_le hlampos h2
      have h4 : (1 : ℝ) / Real.exp (-(R + 1) / cr) = Real.exp ((R + 1) / cr) := by
        rw [one_div, ← Real.exp_neg]
        congr 1
        ring
      linarith [h3, h4]
    have h5 : (R + 1) / cr ≤ Real.log (1 / lam) := by
      have h6 : Real.log (Real.exp ((R + 1) / cr)) ≤ Real.log (1 / lam) :=
        Real.log_le_log (Real.exp_pos _) h1
      rwa [Real.log_exp] at h6
    have h7 : cr * ((R + 1) / cr) = R + 1 := by field_simp
    nlinarith [h5, hcrpos, h7]
  -- the box part
  have hsimple : zeroMult χ₁ (β₁ : ℂ) = 1 := hSimple' q hqS χ₁ β₁ hχ hsq hβ1 hz hlam1
  have hlamR : lam ≤ R := le_trans hlam1 (le_trans (by norm_num) hR)
  have him0 : |(β₁ : ℂ).im| * Real.log q ≤ R := by
    simp only [Complex.ofReal_im, abs_zero, zero_mul]
    exact hR0
  have hbox : signedBoxSumAll q (11 / 2) (3 / 10) R a
      ≤ ‖Hk (11 / 2) (3 / 10) ((1 - (β₁ : ℂ)) * (Real.log q : ℂ))‖ :=
    signedBoxSumAll_le_exceptional hq2 hRlog hsq hrep hΛR hR0 (by rw [hlamdef] at hlamR; exact hlamR)
      hsimple ha
  -- the far part
  have hfar : farZeroSum q (11 / 2) (3 / 10) R
      ≤ restLowZeroSum χ₁ (β₁ : ℂ) (11 / 2) (3 / 10)
        + restHighZeroSum χ₁ (β₁ : ℂ) (11 / 2) (3 / 10) :=
    farZeroSum_le_restLow_add_restHigh hq2 hRlog hrep hΛR
      (by rw [hlamdef] at hlamR; exact hlamR) him0 (hsum q)
  have hlow : restLowZeroSum χ₁ (β₁ : ℂ) (11 / 2) (3 / 10) ≤ C₁ * lam ^ (1 + δ) := by
    have h := hLow' q hqL χ₁ β₁ hχ hsq hβ1 hz hlam2
    rwa [← hlamdef] at h
  have hhigh : restHighZeroSum χ₁ (β₁ : ℂ) (11 / 2) (3 / 10)
      ≤ C₂ * lam * (Real.log q) ^ e := by
    have h := hHigh' q hqH χ₁ β₁ hχ hsq hβ1 hz hlam2
    rwa [← hlamdef] at h
  -- the kernel bound
  have hkern' : ‖Hk (11 / 2) (3 / 10) ((1 - (β₁ : ℂ)) * (Real.log q : ℂ))‖
      ≤ (3 / 10 : ℝ) ^ 2 * Real.exp (-(49 / 10 * lam)) := by
    have h := Hk_norm_le_exp_lamOf (q := q) (L := 11 / 2) (K := 3 / 10) (ρ := (β₁ : ℂ)) hK
      (by omega) (by simpa using hβ1)
    rw [← hlamdef] at h
    have h1 : -(11 / 2 - 2 * (3 / 10)) * lamOf q (β₁ : ℂ) = -(49 / 10 * lamOf q (β₁ : ℂ)) := by
      ring
    rw [h1] at h
    exact h
  -- the height threshold
  have hC₂L : C₂ * (Real.log q) ^ e ≤ (3 / 10 : ℝ) ^ 2 * (49 / 10) / 8 := by
    have hleL₀ : L₀ ≤ Real.log q := by
      have h1 : Real.exp L₀ ≤ (qH' : ℝ) := by
        rw [hqH'def]
        have h2 : Real.exp L₀ ≤ ((⌈Real.exp L₀⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
        have h3 : ((⌈Real.exp L₀⌉₊ : ℕ) : ℝ) ≤ ((⌈Real.exp L₀⌉₊ : ℕ) : ℝ) + 1 := by linarith
        push_cast
        linarith
      have h2 : (qH' : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqH'
      calc L₀ = Real.log (Real.exp L₀) := (Real.log_exp L₀).symm
        _ ≤ Real.log q := Real.log_le_log (Real.exp_pos L₀) (le_trans h1 h2)
    have h3 : (Real.log q) ^ e ≤ L₀ ^ e :=
      Real.rpow_le_rpow_of_nonpos hL₀pos hleL₀ heneg.le
    have h4 : C₂ * L₀ ^ e = (3 / 10 : ℝ) ^ 2 * (49 / 10) / 8 := by
      rw [hL₀pow]
      field_simp
    calc C₂ * (Real.log q) ^ e ≤ C₂ * L₀ ^ e := mul_le_mul_of_nonneg_left h3 hC₂pos.le
      _ = (3 / 10 : ℝ) ^ 2 * (49 / 10) / 8 := h4
  -- the closing arithmetic
  have hlog1 : 1 ≤ Real.log q := by
    have h1 : (1 : ℝ) < Real.log 3 :=
      (Real.lt_log_iff_exp_lt (by norm_num)).mpr Real.exp_one_lt_three
    exact le_trans h1.le (Real.log_le_log (by norm_num) (by exact_mod_cast hq3))
  have hclose := siegel_close_arith (K := 3 / 10) (a₀ := 49 / 10) (C₁ := C₁) (δ := δ)
    (C₂ := C₂) (e := e) (Lq := Real.log q) hK ha₀ hC₁pos hδpos hC₂pos.le heneg hlog1 hC₂L
  have hmain := hclose lam hlampos (le_min hlam2' hlamA)
  calc signedBoxSumAll q (11 / 2) (3 / 10) R a + farZeroSum q (11 / 2) (3 / 10) R
      ≤ ‖Hk (11 / 2) (3 / 10) ((1 - (β₁ : ℂ)) * (Real.log q : ℂ))‖
          + (restLowZeroSum χ₁ (β₁ : ℂ) (11 / 2) (3 / 10)
            + restHighZeroSum χ₁ (β₁ : ℂ) (11 / 2) (3 / 10)) := add_le_add hbox hfar
    _ ≤ (3 / 10 : ℝ) ^ 2 * Real.exp (-(49 / 10 * lam))
          + (C₁ * lam ^ (1 + δ) + C₂ * lam * (Real.log q) ^ e) :=
        add_le_add hkern' (add_le_add hlow hhigh)
    _ ≤ (3 / 10 : ℝ) ^ 2 * (1 - (49 / 10) * lam / 2) := by linarith [hmain]
    _ = (3 / 10 : ℝ) ^ 2 * (1 - (49 / 10) * lamOf q (β₁ : ℂ) / 2) := by rw [hlamdef]
/-- **AREA 6 from the inputs.**  This is the complete assembly of the Siegel case: the five inputs
are `SimpleInput` (Landau simplicity), `RepulsionInput` (Deuring--Heilbronn repulsion), the
summability of the kernel-weighted zero sum, the two `λ₁`-saving bounds for the working region and
for the far heights, and the class-sum expansion of HB §13 (uniform in the box radius). -/
theorem area6_of_all (hSimple : SimpleInput) (hRep : RepulsionInput)
    (hsum : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), Summable (fun ρ : ℂ =>
      (zeroMult χ ρ : ℝ) * ‖Hk (11 / 2) (3 / 10) ((1 - ρ) * (Real.log q : ℂ))‖))
    (hLow : ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ,
      ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
        χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 → zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
        lamOf q (β₁ : ℂ) ≤ 1 / 2 →
        restLowZeroSum χ₁ (β₁ : ℂ) (11 / 2) (3 / 10)
          ≤ C * (lamOf q (β₁ : ℂ)) ^ (1 + δ))
    (hHigh : ∃ C : ℝ, 0 < C ∧ ∃ e : ℝ, e < 0 ∧ ∃ q₀ : ℕ,
      ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
        χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 → zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
        lamOf q (β₁ : ℂ) ≤ 1 / 2 →
        restHighZeroSum χ₁ (β₁ : ℂ) (11 / 2) (3 / 10)
          ≤ C * lamOf q (β₁ : ℂ) * (Real.log q) ^ e)
    (hExp : ∀ R : ℝ, 1 ≤ R → ExpansionInput R) :
    Work.LinnikContract.Area6 :=
  area6_of 1 (hExp 1 le_rfl)
    (boxSumBound_of_inputs 1 le_rfl hSimple hRep hsum hLow hHigh)

/-- **AREA 6 reduced to the expansion and the two density inputs.**  All the other inputs of
`area6_of_all` are supplied by lemmas proved in this workspace:

* `SimpleInput`: `siegelSimpleInput` (Landau's simplicity of the exceptional zero);
* the summability of the kernel-weighted zero sum: `siegelZeroWeightSummable`;
* the `λ₁`-saving bounds for the two pieces of the rest: `siegelRestLow` (which uses the repulsion)
  and `siegelRestHigh`.

So, modulo (i) the class-sum expansion of HB §13 (`ExpansionInput`, the content of the contract's
AREA 2), (ii) the Deuring--Heilbronn repulsion `RepulsionInput` and (iii) the two classical
`λ₁`-saving density estimates `PairDensityInput`/`PairDensityHeightInput`, AREA 6 is proved. -/
theorem area6_of_density (hRep : RepulsionInput) (hDen : PairDensityInput)
    (hDenH : PairDensityHeightInput) (hExp : ∀ R : ℝ, 1 ≤ R → ExpansionInput R) :
    Work.LinnikContract.Area6 :=
  area6_of_all siegelSimpleInput hRep
    (fun q _ χ => siegelZeroWeightSummable (q := q) (11 / 2) (3 / 10) χ)
    (siegelRestLow hRep hDen) (siegelRestHigh hDenH) hExp

/-- **The final wiring of AREA 6**: the Deuring--Heilbronn repulsion (pair form) and the two
`λ₁`-saving density estimates (proved in the shared zero-density chapter `Work.ZeroDensity`, whose
`DHLogFreeSpec`/`DHLogFreeHeightSpec` are bridged to `PairDensityInput`/`PairDensityHeightInput` by
`Work.ZeroDensity.pairDensityInput_of_dhLogFreeSpec` and
`Work.ZeroDensity.pairDensityHeightInput_of_dhLogFreeHeightSpec`) give AREA 6; the class-sum
expansion of HB §13 is supplied by the *proved* theorem `Work.LinnikAreas.siegelExpansion`. -/
theorem area6_of_final_inputs (hRep : RepulsionInput) (hDH : Work.ZeroDensity.DHLogFreeSpec)
    (hDHH : Work.ZeroDensity.DHLogFreeHeightSpec) :
    Work.LinnikContract.Area6 :=
  area6_of_density hRep (Work.ZeroDensity.pairDensityInput_of_dhLogFreeSpec hDH)
    (Work.ZeroDensity.pairDensityHeightInput_of_dhLogFreeHeightSpec hDHH) siegelExpansion

/-- **AREA 6 from the fleet's five named cores** (`Work.ZeroDensity.DensityCores`: Jutila's
log-free family count on `σ ≥ 4/5`, Huxley's `12/5` count on `σ ≤ 4/5`, Montgomery's sharp
large-sieve estimate, the Deuring--Heilbronn repulsion `RepulsionWith (7/16)` and the `λ₁`-saving
height count `DHLogFreeHeightSpec`).  With `siegelExpansion` (the class-sum expansion of HB §13)
and the assemblies of this file, this is the complete Siegel case of Linnik's theorem. -/
theorem area6_of_cores (h : Work.ZeroDensity.DensityCores) : Work.LinnikContract.Area6 :=
  area6_of_final_inputs (Work.ZeroDensity.RepulsionWith.toRepulsionInput (by norm_num) h.repulsion)
    (Work.ZeroDensity.deuringLogFree_of_cores h.jutila h.huxley h.repulsion) h.dhHeight

/-- **AREA 6 from the *classical* input list (see §7).**  All the ingredients of this file except
the *high-zero* mass bound `hHigh` are proved in the workspace:

* `SimpleInput` (`siegelSimpleInput`), the summability of the kernel-weighted zero sum
  (`siegelZeroWeightSummable`), the working-region bound (`siegelRestLow`, from the
  Deuring--Heilbronn repulsion and the `λ₁`-saving count at `|Im ρ| ≤ 1`), and the class-sum
  expansion (`siegelExpansion`, i.e. HB §13 = the contract's AREA 2);
* `hHigh` is the conclusion of `Work.LinnikAreas.siegelRestHighCoupled`, which consumes the
  *coupled* Deuring--Heilbronn density estimate `Work.LinnikAreas.Siegel.DHLogFreeHeightCoupled`
  (Bombieri, *Le grand crible*, Thm. 14 / Jutila 1977, as prescribed by `ROUTE_LEAD` §3.1
  route (ii)) together with the σ-blind count and Siegel's theorem -- see §7. -/
theorem area6_of_coupled_core (hRep : RepulsionInput) (hDen : PairDensityInput)
    (hHigh : ∃ C : ℝ, 0 < C ∧ ∃ e : ℝ, e < 0 ∧ ∃ q₀ : ℕ,
      ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
      χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 → zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
      lamOf q (β₁ : ℂ) ≤ 1 / 2 →
      restHighZeroSum χ₁ (β₁ : ℂ) (11 / 2) (3 / 10)
        ≤ C * lamOf q (β₁ : ℂ) * (Real.log q) ^ e)
    (hExp : ∀ R : ℝ, 1 ≤ R → ExpansionInput R) :
    Work.LinnikContract.Area6 :=
  area6_of_all siegelSimpleInput hRep
    (fun q _ χ => siegelZeroWeightSummable (q := q) (11 / 2) (3 / 10) χ)
    (siegelRestLow hRep hDen) hHigh hExp

end Siegel
/-! ## 7. The state of AREA 6 and the exact remaining gap

**Proved in this file** (with no incomplete proof, on top of `Mathlib`, `Submission/Commons` and the
vocabulary module `Submission.Work.LinnikAreas.SiegelBase`):

* the elementary kernel bounds and `Re((1-ρ)𝓛) = lamOf q ρ`;
* the arithmetic of the closing inequality:
  `exp_neg_le_one_sub_three_quarters` (`e^{-t} ≤ 1 - 3t/4` for `0 ≤ t ≤ 2/5`),
  `siegel_close_arith` (`K²e^{-a₀λ} + C₁λ^{1+δ} + C₂λ𝓛^{e} ≤ K²(1 - a₀λ/2)` for `λ ≤ lamS`,
  `δ > 0`, `e < 0`), and `siegel_numeric_close` (the same with `C x^{1+δ} < K²(1 - e^{-a₀x})`);
* the **box part** of the zero sum (`norm_char_apply_eq_one`, `not_inBox_of_repulsion`,
  `boxSum_eq_zero_of_ne`, `boxSum_eq_exceptional`, `signedBoxSumAll_le_exceptional`): under the
  repulsion `λ(ρ) ≥ Λ > R` the box contains *only* the exceptional zero, so every box sum but
  `χ₁`'s vanishes and the box sum is at most `‖Hk(L,K,λ₁)‖ ≤ K²e^{-a₀λ₁}`;
* the **splitting of the far-zero sum** (`farZeroSum_le_restLow_add_restHigh`) into the working
  region `|Im ρ| ≤ 1` (`restLowZeroSum`) and the far heights (`restHighZeroSum`);
* **the assembly**: `boxSumBound_of_inputs` (`BoxSumBound R` from the inputs, for every `R ≥ 1`),
  `area6_of_all` (`Area6` from the inputs) and `area6_of` (`ExpansionInput R → BoxSumBound R →
  Area6`, i.e. the reduction to the class-sum expansion of HB §13 alone).

**The final wiring.**  `area6_of_cores` proves

`Work.ZeroDensity.DensityCores → Work.LinnikContract.Area6`,

where `Work.ZeroDensity.DensityCores` (`Submission/Work/ZeroDensity/Main.lean`) is the shared
zero-density chapter's structure of five named cores:

| core | content | status in the fleet |
|---|---|---|
| `jutila : FamDensityEpsRange (4/5) 1 2` | Jutila's log-free family count `Σ_χN(σ,T,χ) ≤ C(qT)^{(2+ε)(1-σ)}` for `σ ≥ 4/5` | `ZeroDensity/Jutila` |
| `huxley : FamDensityEpsRange 0 (4/5) (12/5)` | Huxley's `12/5` family count for `σ ≤ 4/5` | `ZeroDensity/Huxley` |
| `montgomery : ∀ B > 0, MontgomerySharp B` | Montgomery's sharp large-sieve density theorem | `ZeroDensity/Montgomery` |
| `repulsion : RepulsionWith (7/16)` | the Deuring--Heilbronn repulsion (pair form) with the explicit constant `7/16` | `DhRepel/`, `OtherCharRepel/` |
| `dhHeight : DHLogFreeHeightSpec` | the `λ₁`-saving log-free Deuring--Heilbronn count in both variables | `ZeroDensity/Deuring` (see the status note there) |

and the chain inside this file is

`area6_of_cores h = area6_of_final_inputs (RepulsionWith.toRepulsionInput h.repulsion)
     (deuringLogFree_of_cores h.jutila h.huxley h.repulsion) h.dhHeight`,

with `area6_of_final_inputs = area6_of_density · · · siegelExpansion` and
`area6_of_density = area6_of_all siegelSimpleInput · (siegelZeroWeightSummable) (siegelRestLow ·)
(siegelRestHigh ·)`.  In other words, every ingredient that is *not* one of the five cores is
proved in this workspace, most of it in this file:

| input of the assembly | proved as |
|---|---|
| `SimpleInput` (Landau simplicity) | `siegelSimpleInput` |
| summability of `ρ ↦ (zeroMult χ ρ)‖Hk((1-ρ)𝓛)‖` | `siegelZeroWeightSummable` |
| repulsion `→ RepulsionInput` | `Work.ZeroDensity.RepulsionWith.toRepulsionInput` + `siegelRepelPair`'s pieces |
| working-region `λ₁`-saving bound `restLowZeroSum ≤ Cλ₁^{1+δ}` | `siegelRestLow` (from `PairDensityInput` + repulsion) |
| height `λ₁`-saving bound `restHighZeroSum ≤ Cλ₁𝓛^{e}` | `siegelRestHigh` (from the `λ₁`-saving height count) |
| `PairDensityInput` | `Work.ZeroDensity.pairDensityInput_of_cores` (Jutila + Huxley + repulsion) |
| `ExpansionInput R` for all `R ≥ 1` | `siegelExpansion` (HB §13, the contract's AREA 2) |
| the box part, the far splitting, the closing arithmetic | `boxSum_eq_exceptional`, `signedBoxSumAll_le_exceptional`, `farZeroSum_le_restLow_add_restHigh`, `siegel_close_arith` |
| the reduction to the expansion and the zero-sum bound, and the prime extraction | `area6_of`, `prime_of_classSum_pos`, `lamOf_lower_bound` (Siegel's theorem) |

**THE `λ₁`-saving HEIGHT INPUT, RESOLVED (§7.1).**  The height input is the one place where the
*formalisation* of the classical theorem matters, and the analysis below (carried out while proving
`Submission.Work.LinnikAreas.siegelHighAbel` and `.../siegelRestHighCoupled`) pins it down.

Write `N(t,T)` for the multiplicity-weighted number of pairs `(χ,ρ) ≠ (χ₁,β₁)` with `λ(ρ) ≤ t` and
`|Im ρ|·𝓛 ≤ T`.  The split-exponent form `PairDensityHeightInput` (`DHLogFreeHeightSpec`)
`N(t,T) ≤ C·λ₁·e^{ct}·T^{c'}`, `c < 49/10`, `c' < 2`, is what `siegelRestHigh` consumes.  It is
**not** the form in which the literature states the Deuring--Heilbronn density theorem: Bombieri
(*Le grand crible*, Thm. 14) and Jutila (1977) state the **coupled** form
`Σ_χ N*(σ,T,χ) ≤ C·λ₁·(qT)^{c(1-σ)}` (`1 - σ = t/𝓛`), in which `q` and `T` enter only through
their product.  The two are *not* equivalent: for `c·t/𝓛 > c'` the split form is strictly stronger,
and in that range it is not implied by any of the tools available here —

* the λ₁-free log-free density estimates (Jutila on `σ ≥ 4/5`, Huxley's `12/5`), combined with the
  σ-blind count and Siegel's theorem, give at `(t,T) = (0.06𝓛, 10𝓛)` only `≪ q^{0.125}`, while the
  split form demands `≪ q^{-0.19}`;
* the height-degraded Deuring--Heilbronn repulsion of the literature
  `λ(ρ) ≥ c₂·log(1/δ)/(2+|Im ρ|)` (Graham; BGTZ, arXiv:2410.06082) gives, in the same place, only
  `λ ≳ 0.0625𝓛` — exactly at the required threshold, with an ineffective constant `c₂ → 3/2⁺`.

So the split form is, at best, a delicate sharpening whose truth hinges on near-optimal constants;
it is *not* the input the paper's route (ii) prescribes.  The **coupled** form, on the other hand,
*is* sufficient, and this is the resolution now recorded in the workspace:

* `Work.LinnikAreas.Siegel.DHLogFreeHeightCoupled (c)` (in `SiegelBase.lean`) is the coupled form
  in the box variables, `pairCountHeight χ₁ β₁ t T ≤ C·λ₁·(q·T/𝓛)^{c·t/𝓛}`;
* `Work.LinnikAreas.pairCountHeight_le_famCount` (proved) passes from the family count to the pair
  count;
* `Work.LinnikAreas.siegelHighAbel` (proved) is the per-layer Abel summation against the *two-range*
  count (coupled count below the crossing `λ*`, σ-blind count above it);
* `Work.LinnikAreas.siegelRestHighCoupled` (statement + complete proof recipe, in that file) is the
  layer assembly.  Two routes to it, both recorded there: (i) the sharp one, with the `λ₁`-dependent
  crossing `λ*_j` of the coupled count with the σ-blind count, valid for every `12/5 ≤ c < 49/10`
  (the `q`-exponent of the `jj`-th layer is then `(1+ε)(1-a/(c(1+s_j))) - s_j(1-ε) < 0`); and (ii) a
  *fixed* threshold `λ* = (1+ε)𝓛/c`, which needs no `λ₁`-arithmetic at all and closes for `c ≤ 3`
  (then `aλ* ≥ (1/2+ε)𝓛`, so the σ-blind tail is `≪ q^{-1/2}` and the dyadic sum is `O(1)`).
  With `λ₁ ≥ C₀𝓛/√q` (Siegel, `Siegel.lamOf_lower_bound`, proved) either route gives
  `restHighZeroSum ≤ C·λ₁·𝓛^{-1/2}`, i.e. the `hHigh` input of `area6_of_all` with `e = -1/2`.
  Route (ii) is the one to formalise first: the classical `(12/5)`-exponent
  Deuring--Heilbronn estimate with the `λ₁` factor supplies `DHLogFreeHeightCoupled 3` by the
  monotonicity lemma `Siegel.DHLogFreeHeightCoupled.mono` (proved).  Everything
else in the box-sum argument is proved in this file and is independent of this question; **no
correctness risk remains in AREA 6 beyond the three classical theorems of the `DensityCores`
table** (`jutila`, `huxley`, `repulsion`).

**Why `RepulsionInput` is the *pair* form.**  The exclusion must be that of the pair `(χ₁,β₁)`
and not merely of the point `β₁`: if a second character vanished at `β₁`, its box term would
contribute another `≈ K²` and the budget `V ≤ K²(1 - a₀λ₁/2)` -- the statement of `BoxSumBound`,
and hence the whole assembly -- would fail.  The missing implication (no other character vanishes
at `β₁`) is the classical "at most one exceptional zero", i.e. Landau's two-real-zeros repulsion
`λ₁λ₂ ≫ 1`, which is proved by the same Deuring--Heilbronn positivity argument as the rest of the
repulsion (`Submission.Work.LinnikAreas.DhRepel`). -/

/-- **AREA 6 from Jutila's non-principal theorem and Huxley's `12/5`** --- the frozen AREA 3
certificate is *not* used, and neither is any other input besides the proved BGTZ repulsion:
this is `Work.LinnikAreas.area6_of_cores_cap` (`LinnikAreas/area6CapChain.lean`) applied to
`Work.LinnikAreas.BGTZRepulsionGenE_proved` (`LinnikAreas/BGTZRepE.lean`).  It is *not* the frozen
statement: the two remaining fleet cores are its hypotheses.  See
`LinnikAreas/NOTE_area3_elimination.md`. -/
theorem area6_of_capped_cores
    (hJ : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), (4 : ℝ) / 5 ≤ σ → σ ≤ 1 → 1 ≤ T →
        (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            Work.LinnikAreas.zeroCountIn χ σ T)
          ≤ C * ((q : ℝ) * T) ^ ((2 + ε) * (1 - σ)))
    (hH : Work.ZeroDensity.FamDensityEpsRange 0 (4 / 5) (12 / 5)) :
    Work.LinnikContract.Area6 :=
  area6_of_cores_cap BGTZRepulsionGenE_proved hJ hH

/-- **AREA 6** of the frozen Linnik contract: the Siegel-zero case of Linnik's theorem.

**The state of the proof (session 3, see `NOTES_area6_route.md` §8).**  Everything below the
*one* deep input is proved, in this workspace, and the reduction is machine-checked by
`Work.LinnikAreas.area6_of_BGTZ` (`Submission/Work/LinnikAreas/area6BGTZ.lean`):

`area6_of_BGTZ : FamDensityEpsRange (4/5) 1 2 → FamDensityEpsRange 0 (4/5) (12/5) →
                  RepulsionWith (7/16) → Siegel.RepulsionBGTZ → Work.LinnikContract.Area6`

where the first two hypotheses are Jutila's and Huxley's log-free family zero-density estimates
(the fleet's `ZeroDensity/Jutila`, `ZeroDensity/Huxley` cores), `RepulsionWith (7/16)` is the
working-region Deuring--Heilbronn repulsion (the fleet's `DhRepel`/`OtherCharRepel`), and the
single deep input is `Siegel.RepulsionBGTZ` (`Submission/Work/LinnikAreas/BGTZ.lean`): the
Deuring--Heilbronn repulsion **at all heights**,

`λ(ρ) ≥ (log(1/λ₁) - log(24(c₁ + c₂·log(5+|Im ρ|)/𝓛))) / (c₁ + c₂·log(5+|Im ρ|)/𝓛)`,
`c₁ = 4/3+ε`, `c₂ = 2/3+ε`,

a true, explicit, published theorem (Benli--Goel--Twiss--Zaman, *Explicit Deuring--Heilbronn
phenomenon for Dirichlet L-functions*, arXiv:2410.06082, Cor. 1.2; see §8.1 for the effective
choice `ε = 1/2`).

The pieces of the reduction that are *proved* in the workspace:

| input of the assembly | proved as |
|---|---|
| `SimpleInput` (Landau simplicity) | `siegelSimpleInput` |
| summability of the kernel-weighted zero sum | `siegelZeroWeightSummable` |
| `PairDensityInput` (working region `\|Im ρ\| ≤ 1`) | `Work.ZeroDensity.pairDensityInput_of_cores` (Jutila + Huxley + repulsion) |
| `restLowZeroSum ≤ Cλ₁^{1+δ}` | `siegelRestLow` |
| `restHighZeroSum ≤ C𝓛^{-3/2}` (`λ₁`-free) | `Work.LinnikAreas.RestHighFree` |
| `restHighZeroSum ≤ Cλ₁𝓛^{-3/2}` for `λ₁ ≤ 1/10` | `Work.LinnikAreas.RestHighBGTZ` (from `RepulsionBGTZ`) |
| the `hHigh` split at `λ₁ = 1/10` | `Work.LinnikAreas.RestHighCombine` |
| `LogFreeFamHeight (5/2) (3/2)` | `Work.ZeroDensity.Assembly.logFreeFamHeight_of_cores` |
| `ExpansionInput R` for all `R ≥ 1` (HB §13) | `siegelExpansion` |
| the box part, the far splitting, the closing arithmetic, the prime extraction | `boxSum_eq_exceptional`, `signedBoxSumAll_le_exceptional`, `farZeroSum_le_restLow_add_restHigh`, `siegel_close_arith`, `prime_of_classSum_pos`, `lamOf_lower_bound` |

**What is *not* used any more.**  The earlier route fed the two rest-bounds through the
`λ₁`-saving estimates `PairDensityInput`/`PairDensityHeightInput` (`Siegel.DHLogFreeHeightCoupled`),
and in particular through `siegelRestHighCoupled`.  The height-direction estimate in its
unrestricted form is **not a theorem** (and is false at extreme heights); see §8 of the notes.
The only zero-density inputs of the new route are the *λ₁-free* Jutila/Huxley cores.  The
remaining gap is therefore exactly the formalization of `Siegel.RepulsionBGTZ`.

**UPDATE (session 9).**  That gap is *closed*: `Siegel.RepulsionBGTZ`'s role is played by the
corrected BGTZ detector assembly, which is complete (no incomplete cases) and axiom-clean —

* `Work.LinnikAreas.BGTZ.E.BGTZRepulsionGen_E :
   ∃ cZ > 0, BGTZ.ZFRInputL cZ ∧ BGTZ.RepulsionGenC (11/5) (11/10) (max (1000/cZ) 1000)`
  (the Deuring--Heilbronn repulsion at all heights, `Submission/Work/LinnikAreas/BGTZ/E/`).

AREA 6 is accordingly machine-checked, with `#print axioms = [propext, Classical.choice,
Quot.sound]`, as

* `Work.LinnikAreas.area6_of_cores_E` (`LinnikAreas/area6Cores.lean`):
  `FamDensityEpsRange (4/5) 1 2 → FamDensityEpsRange 0 (4/5) (12/5) → ZeroFreeCert → Area6`;
* `Work.LinnikAreas.area6_of_cores_E_np` (`LinnikAreas/area6CoresNp.lean`): the *sharper*
  interface, with the Jutila input replaced by its non-principal form
  (`LinnikAreas/logFreeFamHeightOfNonPrincipal`, `LinnikAreas/logFreeFamHalfOfNonPrincipal`).
  This matters because `famCount` sums over *all* characters mod `q` (the principal one
  included), so `FamDensityEpsRange (4/5) 1 2` implies the density hypothesis for `ζ` on
  `σ ≥ 4/5` and is *stronger* than Jutila's theorem; see
  `Submission/Work/LinnikAreas/NOTE_jutilaInput_principalChar.md`.

**UPDATE (session 10): AREA 3 is eliminated.**  The route above consumes the frozen AREA 3
certificate `Work.LinnikContract.ZeroFreeCert` in exactly one place: the *uncapped* repulsion
`Work.ZeroDensity.RepulsionWith (7/16)` produced by `repulsionWith_7_16`
(`RepulsionWith_of_ZeroFreeCert`), which needs the zero-free tables of AREA 3 precisely for the
range `λ₁ ∈ [lamS, 1/2]`.  AREA 6 never needs that range:

* `LinnikAreas/RepulsionCapDefs.lean` defines the *capped* repulsion `RepulsionWithCap ε₀ c`
  (`λ(β₁) ≤ ε₀` instead of `≤ 1/2`);
* `LinnikAreas/RepulsionCap.lean` proves `∃ ε₀ > 0, RepulsionWithCap ε₀ (7/16)` from the proved
  BGTZ repulsion `BGTZRepulsionGen`, the proved unconditional zero-free region
  `BGTZ.ZFRInput` (`BGTZ/ZFRInput_exists.lean`) and Siegel's uniform lower bound `lamOfEps200`
  — this is the step that replaces AREA 3 (the capped datum is automatically the *minimal* pair,
  which is all the BGTZ repulsion needs);
* `LinnikAreas/PairDensityCap.lean` derives the *uncapped* `Siegel.PairDensityInput` from the
  capped repulsion and the log-free family count `LogFreeFamHalf (5/2)` (for `λ₁ ≥ ε₀` the
  repulsion is not needed at all: the family count alone suffices);
* `LinnikAreas/siegelRestLowCap.lean` and `LinnikAreas/boxSumBoundCap.lean` are the two
  `λ₁`-capped consumers (`siegelRestLow`, `boxSumBound_of_inputs` with the repulsion hypothesis
  capped at `ε₀`; `BoxSumBound` already has an internal threshold `lamS ≤ 1/100`, which is only
  shrunk by `min · ε₀`).

The resulting interface, `LinnikAreas/area6CapChain.lean`,

* `Work.LinnikAreas.area6_of_cores_cap : BGTZRepulsionGen → JutilaNonPrincipal →
   FamDensityEpsRange 0 (4/5) (12/5) → Area6`

is complete (no incomplete cases) with `#print axioms = [propext, Classical.choice, Quot.sound]`,
and since `Work.LinnikAreas.BGTZ.E.BGTZRepulsionGen_E` is *proved*, the frozen target below
reduces to exactly **two** fleet cores:

| input | fleet module |
|---|---|
| Jutila, non-principal form (`Work.ZeroDensity.Jutila.jutilaNonPrincipal`) | `ZeroDensity/Jutila` |
| Huxley `12/5` (`FamDensityEpsRange 0 (4/5) (12/5)`) | `ZeroDensity/Huxley` |

**Wiring the target.**  `area6CapChain` imports *this* file if it is built on `area6.lean`, so the
wiring has been split into cycle-free modules (none of which imports `area6`), and this file
imports them:

* `LinnikAreas/area6Box.lean` — the box part of HB §§13--14 (`norm_char_apply_eq_one` …
  `siegel_close_arith`), extracted from this file;
* `LinnikAreas/area6Top.lean` — the top-level argument (`vmClassSum_eq_prime_add_nonPrime`,
  `prime_of_classSum_pos`, `Siegel.area6_of`), extracted from this file;
* `LinnikAreas/RepulsionCap.lean` + `…/RepulsionCapDefs.lean` — the capped repulsion
  `RepulsionWithCap ε₀ (7/16)` and its proof from the local statement `BGTZRepulsionGenE`;
* `LinnikAreas/PairDensityCap.lean` — `Siegel.PairDensityInput` from the capped repulsion;
* `LinnikAreas/siegelRestLowCap.lean`, `…/boxSumCap.lean` — the two capped consumers;
* `LinnikAreas/BGTZRepE.lean` — `BGTZRepulsionGenE_proved` (the BGTZ repulsion at all heights,
  in the local statement, so that no import of `area6Chain` is needed);
* `LinnikAreas/area6CapChain.lean` — the assembly
  `area6_of_cores_cap : BGTZRepulsionGenE → Jutila → Huxley → Area6`.

The frozen target below is therefore **one line from closure**: its body is
`area6_of_capped_cores Work.ZeroDensity.Jutila.jutilaNonPrincipal
Work.ZeroDensity.Huxley.huxleyTwelveFifths`, with `area6_of_capped_cores` (`area6_of_cores_cap BGTZRepulsionGenE_proved ·  ·`, proved in this
file, axiom-clean) as above.  See `Submission/Work/LinnikAreas/NOTE_area3_elimination.md`.

(Historical note for whoever wires the remaining two cores up: `ZeroDensity/Huxley/
huxleyTwelveFifths.lean` is *stale-by-content* in the workspace — its `lake build` requires
rebuilding `ZeroDensity/Montgomery/montgomerySharp`, blocked by the never-compiled
`ZeroDensity/Ingham/hiCaseF4BoundFile.lean` and friends — see
`Submission/Work/LinnikAreas/BGTZ/NOTES_workspace_blockers.md`.)

**UPDATE (session 11): the two cores are replaced by one, and alternatively by a different pair.**

*The exponent analysis.*  Everything downstream of the two family counts in AREA 6 consumes them
at the *fixed* exponent `5/2` (`Work.ZeroDensity.LogFreeFamHalf (5/2)`,
`Work.ZeroDensity.LogFreeFamHeight (5/2) (3/2)`):

* `PairDensityCap`'s Deuring--Heilbronn matching needs `c₃ + 1/c_r < 49/10` with the repulsion
  constant `c_r = 7/16`, i.e. `c₃ < 49/10 - 16/7 = 2.614…`, and `5/2 + 16/7 = 67/14 = 4.785…`;
* `RestHighFree`/`RestHighBGTZGenC` need `c₃ < 49/10` and `c₃' < 2`.

Consequently **any** non-principal log-free estimate with q-coefficient `≤ 5/2` on a range
`[σ₀,1]` with `σ₀ < 4/5` — glued with Huxley's all-character `12/5` on `σ ≤ 4/5` (coefficient
`12/5 + 1/10 = 5/2` at `ε = 1/10`, *exactly* the requirement) — closes AREA 6 verbatim; and so
does any pair of inputs that supplies the coefficient `5/2` on the whole range `σ ∈ [0,1]`.

*Route A (the lead's unified route, `Submission/Work/ZeroDensity/JUTILA_UNIFIED_LEAD.md`).*
`LinnikAreas/logFreeFamOfTwelveFifths.lean` derives `LogFreeFamHalf (5/2)` and
`LogFreeFamHeight (5/2) (3/2)` from

* `Work.ZeroDensity.LogFree.NonPrincipalTwelveFifths` — `Σ'_{χ≠1} N(σ,T,χ) ≤ C(qT)^{(12/5+ε)(1-σ)}`
  on `σ ≥ 3979/5000 = 0.7958`, the node `logFreeNP (93/100) (12/5)` glued with Huxley's
  non-principal bound widened to `σ ≤ 93/100` — at `ε = 1/10` (exponent `5/2`, and `3979/5000 < 4/5`
  so the whole near-line range is covered); **plus**
* Huxley's `Work.ZeroDensity.FamDensityEpsRange 0 (4/5) (12/5)` (unchanged; `ε = 1/10`).

`LinnikAreas/area6OfTwelveFifths.lean` then assembles

```
Work.LinnikAreas.area6_of_nonPrincipalTwelveFifths :
  NonPrincipalTwelveFifths → FamDensityEpsRange 0 (4/5) (12/5) → Area6
```

(reusing `PairDensityCap`, `RestHighFree`, `RestHighBGTZGenC`, `siegelRestLowCap`, `boxSumCap`
verbatim), so the frozen target closes from those two Propositions by
`area6_of_nonPrincipalTwelveFifths Work.ZeroDensity.LogFree.nonPrincipalTwelveFifths
Work.ZeroDensity.Huxley.huxleyTwelveFifths`.

*Route B (no Huxley).*  `LinnikAreas/logFreeFamOfMontgomery.lean` observes that if the *target*
exponent is raised from `5/2` to `261/100 = 2.61` — which is still admissible in both consumers,
since `261/100 < 49/10` and `261/100 + 16/7 = 3427/700 < 49/10` — then **Montgomery's sharp
large-sieve estimate replaces Huxley**: `3(1-σ)/(2-σ) ≤ 5/2` with equality only at `σ = 4/5`, so
at `σ = 4/5` Montgomery's `ε = 1/100` costs `0.01` of the `0.11·(1/5) = 0.022` of available
exponent budget, leaving room for its logarithmic power; Jutila's range `σ ≥ 4/5` is covered by
the near-line node `logFreeNP (93/100) (12/5)` at `σ ≥ 93/100` *and* by Montgomery (with the
`2.61` budget, i.e. `ε ≤ (1-σ)(2.61 - 3/(2-σ)) ≥ 0.11(1-σ)`) on `4/5 ≤ σ ≤ 0.93`.  The resulting
interface is

```
Work.LinnikAreas.area6_of_cores_v2 :
  BGTZRepulsionGenE → JutilaNP → MontgomerySharp (1/1000) → Area6
Work.LinnikAreas.area6_of_cores_v2_huxley :
  BGTZRepulsionGenE → JutilaNP → FamDensityEpsRange 0 (4/5) (12/5) → Area6
```

(`LinnikAreas/area6OfCores2.lean`), together with the `∀ B > 0` form
`area6_of_cores_v2_allB`, i.e. AREA 6 closes from the chapter target
`Work.ZeroDensity.Montgomery.montgomerySharp` **and nothing else** besides the non-principal
input.  Route B needs the two far-height lemmas at the exponent `261/100`
(`LinnikAreas/RestHighFreeGen`, `LinnikAreas/BGTZ/RestHighBGTZGenCGen`), which is where the
`5/2`-hardcoding of `RestHighFree`/`RestHighBGTZGenC` is lifted mechanically: every constraint in
those files is `c₃ < 49/10` (used only as `exp(c₃ - 49/10) < 1`) resp. `c₃' < 2`, and the numeric
certificates `exp(5/2) ≤ 27`, `1 - exp(-12/5) ≥ 1/2` remain true with `261/100` and `229/100`.

**UPDATE (session 12) — AREA 6 is CLOSED, and none of the routes above is used.**  The frozen
target below is now the *proved* theorem `Work.SiegelAbsorb.area6_siegelRoute`, i.e. **Siegel
absorption** (`LinnikAreas/AREA6_ROUTE_LEAD.md`, `Submission/Work/SiegelAbsorb/`): the exceptional
zero's own lower bound `λ₁ ≫ q^{-1/200}` (Siegel, already used by the proved BGTZ repulsion)
replaces every sharp density estimate on `σ < 93/100`, so neither Jutila's non-principal theorem
nor Huxley's `12/5` nor Montgomery's sharp large-sieve estimate is needed — in particular the
frozen target no longer depends on any statement of the `ZeroDensity` chapters that still contains
an incomplete case.  The inputs, all theorems of this workspace with
`#print axioms = [propext, Classical.choice, Quot.sound]`:

* the capped Deuring--Heilbronn repulsion `repulsionWithCap_7_16`, fed by the proved BGTZ
  repulsion at all heights (`BGTZRepulsionGenE_proved`);
* the log-free non-principal estimate `logFreeNP (3/4) (9/2)` (`SiegelAbsorb/logFreeNP34.lean`),
  the near-line count at coefficient `5/2` on `σ ≥ 93/100` (`SiegelAbsorb/famCount_nearLine.lean`)
  and the crude count at coefficient `9/2` on all of `[0,1]`
  (`SiegelAbsorb/famCount_crude.lean`);
* Siegel's lower bound in exponential form (`SiegelAbsorb/lamOf_ge_exp_neg.lean`), used twice: with
  `a = 21/1000` to kill the crude count on `λ > (7/100)𝓛`, and with `a = 7/250` in the far-zero
  branch;
* the truncated two-exponential matching (`SiegelAbsorb/dhCapTrunc.lean`, exponent
  `67/14 < 24/5`), the `λ₁`-saving count `Siegel.PairDensityInput` with `c = 24/5`
  (`SiegelAbsorb/pairDensityInput_siegel.lean`), the two-regime per-window mass
  (`SiegelAbsorb/highMassRep2.lean`) and its conversion into `RestHighBGTZSpec (-3/2)`
  (`SiegelAbsorb/RestHighBGTZSiegel_of_window.lean`, `SiegelAbsorb/area6Siegel.lean`);
* the unchanged AREA 6 assembly `siegelRestLowCap` → `boxSumCap` → `Siegel.area6_of`
  (`SiegelAbsorb/area6SiegelOfInputs.lean`). -/
theorem area6 : Work.LinnikContract.Area6 :=
  Work.SiegelAbsorb.area6_siegelRoute

/-- **The frozen target from the lead's unified route** (Route A): the non-principal input
`Work.ZeroDensity.LogFree.NonPrincipalTwelveFifths` and Huxley's `12/5`.  Re-exported here so that
the final wiring of the frozen target is a one-liner the moment both are theorems. -/
theorem area6_of_final_unified
    (hNP : Work.ZeroDensity.LogFree.NonPrincipalTwelveFifths)
    (hH : Work.ZeroDensity.FamDensityEpsRange 0 (4 / 5) (12 / 5)) :
    Work.LinnikContract.Area6 :=
  area6_of_nonPrincipalTwelveFifths hNP hH

/-- **The frozen target from the two *pieces* of the lead's unified route** (Route A): the log-free
non-principal estimate `logFreeNP (93/100) (12/5)` above `σ = 93/100`, Huxley's non-principal `12/5`
widened to `σ ≤ 93/100` (`HuxleyNPWide`), and the all-character `12/5` on `σ ≤ 4/5`.  Re-exported
here so that the final wiring of the frozen target is a one-liner the moment those three are
theorems (the first two are glued into `NonPrincipalTwelveFifths` by the *proved*
`Work.ZeroDensity.LogFree.nonPrincipalTwelveFifths`). -/
theorem area6_of_final_unified_of_pieces
    (hlog : Work.ZeroDensity.LogFree.logFreeNP (93 / 100) (12 / 5))
    (hhux : Work.ZeroDensity.LogFree.HuxleyNPWide)
    (hH : Work.ZeroDensity.FamDensityEpsRange 0 (4 / 5) (12 / 5)) :
    Work.LinnikContract.Area6 :=
  area6_of_logFreeNP_and_huxleyNPWide_proved hlog hhux hH

/-- **The frozen target from Jutila's non-principal theorem and Montgomery's sharp large-sieve
estimate** (Route B, no Huxley): the one-line wiring once
`Work.ZeroDensity.Jutila.jutilaNonPrincipal` and
`Work.ZeroDensity.Montgomery.montgomerySharp` are theorems. -/
theorem area6_of_final_montgomery
    (hJ : Work.LinnikAreas.FamilyZeroDensityJutilaNP)
    (hM : Work.ZeroDensity.MontgomerySharp (1 / 1000)) :
    Work.LinnikContract.Area6 :=
  area6_of_jutila_montgomery hJ hM

/-- **The frozen target from the LogFree chapter's two nodes and Montgomery** (Route D): the
log-free estimate `logFreeNP (93/100) (12/5)` above `σ = 93/100`, Huxley's non-principal `12/5`
widened to `σ ≤ 93/100`, and Montgomery's sharp large-sieve estimate.  Neither the all-character
Huxley estimate nor Jutila's sharp theorem on `σ ≥ 4/5` is used; the principal character is
carried by absolute bounds. -/
theorem area6_of_final_coreNodes
    (hlog : Work.ZeroDensity.LogFree.logFreeNP (93 / 100) (12 / 5))
    (hhux : Work.ZeroDensity.LogFree.HuxleyNPWide)
    (hM : ∀ B : ℝ, 0 < B → Work.ZeroDensity.MontgomerySharp B) :
    Work.LinnikContract.Area6 :=
  area6_of_coreNodes_allB hlog hhux hM

/-- **The frozen target from the two remaining nodes alone** (Route D with the log-free instance now
proved): Huxley's non-principal `12/5` widened to `σ ≤ 93/100`
(`Work.ZeroDensity.LogFree.HuxleyNPWide`, whose only remaining input is
`LogFree/contourHalfWideClean`) and Montgomery's sharp large-sieve estimate in its `∀ B > 0` form
(`Work.ZeroDensity.Montgomery.montgomerySharp`, whose only remaining input is the character
approximate functional equation `Montgomery/AfeProof/afePrimitiveBalanced`).  The instance
`logFreeNP (93/100) (12/5)` is a *theorem* (`Work.LinnikAreas.LogFreeAux.logFreeNP_93_100_clean`,
a clash-free re-derivation of `Work.ZeroDensity.LogFree.logFreeNP_93_100_twelveFifths`), so the
frozen target closes by `area6_of_final_twoNodes Work.ZeroDensity.LogFree.huxleyNPWide
Work.ZeroDensity.Montgomery.montgomerySharp` the moment those two are theorems. -/
theorem area6_of_final_twoNodes
    (hhux : Work.ZeroDensity.LogFree.HuxleyNPWide)
    (hM : ∀ B : ℝ, 0 < B → Work.ZeroDensity.MontgomerySharp B) :
    Work.LinnikContract.Area6 :=
  area6_of_twoNodes hhux hM

/-- **Route B in the `∀ B > 0` form of Montgomery's estimate** — the shape of the chapter's target
`Work.ZeroDensity.Montgomery.montgomerySharp`. -/
theorem area6_of_final_montgomery_allB
    (hJ : Work.LinnikAreas.FamilyZeroDensityJutilaNP)
    (hM : ∀ B : ℝ, 0 < B → Work.ZeroDensity.MontgomerySharp B) :
    Work.LinnikContract.Area6 :=
  area6_of_jutila_montgomery_allB hJ hM

end

end Work.LinnikAreas
