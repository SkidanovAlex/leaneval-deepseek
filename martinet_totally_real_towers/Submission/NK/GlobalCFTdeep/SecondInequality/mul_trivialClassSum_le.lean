import Mathlib
import Submission.NK.GlobalCFTdeep.SecondInequality.Defs
import Submission.NK.GlobalCFTdeep.SecondInequality.log_norm_eulerProduct_eq_tsum
import Submission.NK.GlobalCFTdeep.SecondInequality.tsum_log_norm_eulerFactor

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace NK.GlobalCFTdeep.SecondInequality

variable {K : Type*} [Field K] [NumberField K]

/-- **Summability of the logarithmic Euler factors.**  For `s > 1` the series
`∑_{𝔭 ∉ S} -log ‖1 - χ(b 𝔭) N𝔭^{-s}‖` converges: the Euler factors are `1 + O(N𝔭^{-s})`
(`summable_norm_eulerFactor_sub_one`) and `Summable.summable_log_norm_one_add` converts a
summable family of `‖f i - 1‖` into a summable family of `log ‖f i‖`. -/
theorem summable_negLogEulerFactor {B : Type*} [Group B] [Finite B] (b : PrimeIdeal K → B)
    (S : Finset (PrimeIdeal K)) (χ : B →* ℂˣ) {s : ℝ} (hs : 1 < s) :
    Summable (fun 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} => negLogEulerFactor b χ s 𝔭.1) := by
  have h := Summable.summable_log_norm_one_add
    (f := fun 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} => eulerFactor b χ s 𝔭.1 - 1)
    (summable_norm_eulerFactor_sub_one b S χ hs)
  have h1 : ∀ 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S}, 1 + (eulerFactor b χ s 𝔭.1 - 1)
      = eulerFactor b χ s 𝔭.1 := fun 𝔭 => by ring
  refine h.congr fun 𝔭 => ?_
  rw [h1 𝔭, negLogEulerFactor_eq_log_norm_eulerFactor]

/-- **The local inequality.**  For `s > 1` and a prime ideal `𝔭`, the contribution `|B| · N𝔭^{-s}`
of `𝔭` when its class is trivial is bounded by the sum over all characters of `B` of the
logarithmic Euler factors `-log ‖1 - χ(b 𝔭) N𝔭^{-s}‖`.

Indeed, `tsum_log_norm_eulerFactor` turns the character sum into
`-(|B| / f) · log (1 - x^f)` with `f = orderOf (b 𝔭)` and `x = N𝔭^{-s} ∈ (0, 1/2]`: for `f = 1`
this is `|B| · (-log (1 - x)) ≥ |B| · x` (as `-log (1-z) ≥ z`), and for `f ≥ 2` it is `≥ 0`. -/
theorem natCard_mul_ite_le_sum_negLogEulerFactor {B : Type*} [CommGroup B] [Fintype B]
    [DecidableEq B] (b : PrimeIdeal K → B) {s : ℝ} (hs : 1 < s) (𝔭 : PrimeIdeal K) :
    (Nat.card B : ℝ) * (if b 𝔭 = 1 then primeWeight s 𝔭 else 0) ≤
      ∑ χ : B →* ℂˣ, negLogEulerFactor b χ s 𝔭 := by
  classical
  have hsum_eq : (∑ χ : B →* ℂˣ, negLogEulerFactor b χ s 𝔭)
      = ∑ χ : B →* ℂˣ, Real.log ‖eulerFactor b χ s 𝔭‖ :=
    Finset.sum_congr rfl fun χ _ => negLogEulerFactor_eq_log_norm_eulerFactor b χ s 𝔭
  rw [hsum_eq, tsum_log_norm_eulerFactor b hs 𝔭]
  set x : ℝ := primeWeight s 𝔭 with hxdef
  have hxpos : 0 < x := primeWeight_pos s 𝔭
  have hxhalf : x ≤ 1 / 2 := primeWeight_le_half 𝔭 hs
  have hxlt : x < 1 := lt_of_le_of_lt hxhalf (by norm_num)
  by_cases hb : b 𝔭 = 1
  · rw [if_pos hb]
    have hf : orderOf (b 𝔭) = 1 := orderOf_eq_one_iff.mpr hb
    rw [hf, pow_one]
    simp only [Nat.cast_one, div_one]
    have hlog1 : Real.log (1 - x) ≤ -x := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 - x by linarith)
      linarith
    have hxle : x ≤ -Real.log (1 - x) := by linarith
    rw [show -(Nat.card B : ℝ) * Real.log (1 - x) = (Nat.card B : ℝ) * (-Real.log (1 - x))
      by ring]
    exact mul_le_mul_of_nonneg_left hxle (Nat.cast_nonneg _)
  · rw [if_neg hb, mul_zero]
    have hfpos : 0 < orderOf (b 𝔭) := orderOf_pos (b 𝔭)
    have hpow : x ^ orderOf (b 𝔭) < 1 := pow_lt_one₀ hxpos.le hxlt hfpos.ne'
    have hlog0 : Real.log (1 - x ^ orderOf (b 𝔭)) ≤ 0 :=
      Real.log_nonpos (by linarith) (by linarith [pow_nonneg hxpos.le (orderOf (b 𝔭))])
    have hC : (0 : ℝ) ≤ (Nat.card B : ℝ) / (orderOf (b 𝔭) : ℝ) :=
      div_nonneg (Nat.cast_nonneg _) (by positivity)
    rw [neg_mul]
    linarith [mul_nonpos_of_nonneg_of_nonpos hC hlog0]

/-- **Fubini for the character sum.**  For `s > 1` the finite sum over the characters of `B` of the
logarithms of the norms of the Euler products is the sum over the primes outside `S` of the finite
character sums of the logarithmic Euler factors.  Each inner series is summable
(`summable_negLogEulerFactor`), so this is `Summable.tsum_finsetSum`. -/
theorem sum_log_norm_eulerProduct_eq_tsum {B : Type*} [CommGroup B] [Fintype B]
    (b : PrimeIdeal K → B) (S : Finset (PrimeIdeal K)) {s : ℝ} (hs : 1 < s) :
    (∑ χ : B →* ℂˣ, Real.log ‖eulerProduct b S χ s‖) =
      ∑' 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S},
        ∑ χ : B →* ℂˣ, negLogEulerFactor b χ s 𝔭.1 := by
  have hsumm : ∀ χ : B →* ℂˣ, Summable (fun 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} =>
      negLogEulerFactor b χ s 𝔭.1) :=
    fun χ => summable_negLogEulerFactor b S χ hs
  have h1 : (∑ χ : B →* ℂˣ, Real.log ‖eulerProduct b S χ s‖)
      = ∑ χ ∈ Finset.univ, ∑' 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S},
          negLogEulerFactor b χ s 𝔭.1 :=
    Finset.sum_congr rfl fun χ _ => log_norm_eulerProduct_eq_tsum b S χ hs
  rw [h1, ← Summable.tsum_finsetSum (s := (Finset.univ : Finset (B →* ℂˣ)))
    (f := fun (χ : B →* ℂˣ) (𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S}) =>
      negLogEulerFactor b χ s 𝔭.1) (fun χ _ => hsumm χ)]

-- Module `Submission.NK.GlobalCFTdeep.SecondInequality.mul_trivialClassSum_le`, namespace
-- `NK.GlobalCFTdeep.SecondInequality`, importing
-- `Submission.NK.GlobalCFTdeep.SecondInequality.Defs`,
-- `...SecondInequality.log_norm_eulerProduct_eq_tsum` (which proves
-- `Real.log ‖∏'_{𝔭∉S} f 𝔭‖ = ∑'_{𝔭∉S} Real.log ‖f 𝔭‖` for the Euler product) and
-- `...SecondInequality.tsum_log_norm_eulerFactor` (the logarithmised local factor identity
-- `∑_{χ} Real.log ‖eulerFactor b χ s 𝔭‖ = -(|B|/orderOf (b 𝔭))·Real.log (1 - (N𝔭^{-s})^{orderOf (b 𝔭)})`).
--
-- MATHEMATICS (Milne, Class Field Theory, Chapter VI §4, the computation inside the proof of
-- Theorem 4.8).  Let `h = |B|`, `x 𝔭 = N𝔭^{-s}` and `f 𝔭 = orderOf (b 𝔭)`.  Then by the two
-- imports, for `1 < s`,
--   `∑_χ Real.log ‖L χ s‖ = ∑_χ ∑_{𝔭∉S} -Real.log ‖1 - χ(b𝔭) x𝔭‖
--                          = ∑_{𝔭∉S} (h/f 𝔭)·(-Real.log (1 - x𝔭^{f 𝔭}))`.
-- Every summand is `≥ 0` (as `x𝔭 ≤ 1/2`), so the finite `χ`-sum commutes with the `tsum` by
-- Tonelli (`Summable.tsum_finsetSum` plus nonnegativity); and for `f 𝔭 = 1` (equivalently
-- `b 𝔭 = 1`, since `orderOf g = 1 ↔ g = 1` in a group) the summand is
-- `h·(-Real.log (1 - x𝔭)) ≥ h·x𝔭` (`-Real.log (1 - z) ≥ z` on `[0,1)`).  The summands with
-- `f 𝔭 ≥ 2` are nonnegative and may be dropped.  Hence `h · trivialClassSum b S s ≤ ∑_χ Real.log ‖L χ s‖`,
-- i.e. the conclusion with `C = 0` (modulo the finite set `S`, excluded on both sides).
theorem mul_trivialClassSum_le {K : Type*} [Field K] [NumberField K] {B : Type*} [CommGroup B]
    [Fintype B] [DecidableEq B] (b : PrimeIdeal K → B) (S : Finset (PrimeIdeal K)) :
    ∃ C : ℝ, ∀ s : ℝ, 1 < s →
      (Nat.card B : ℝ) * trivialClassSum b S s ≤
        ∑ χ : B →* ℂˣ, Real.log ‖eulerProduct b S χ s‖ + C := by
  classical
  refine ⟨0, fun s hs => ?_⟩
  rw [add_zero]
  -- the dominating series `∑_𝔭 N𝔭^{-s}` is summable for `s > 1`
  have hbase : Summable (fun 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} => primeWeight s 𝔭.1) := by
    have h := (Commons.NumberTheory.NumberField.Set.summable_primeIdealZetaSum (K := K) hs).subtype
      (fun 𝔭 : PrimeIdeal K => 𝔭 ∉ S)
    exact h.congr (fun 𝔭 => (primeWeight_def s 𝔭.1).symm)
  -- the left hand side is summable
  have hsummL : Summable (fun 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} =>
      (Nat.card B : ℝ) * (if b 𝔭.1 = 1 then primeWeight s 𝔭.1 else 0)) := by
    refine Summable.of_nonneg_of_le (fun 𝔭 => ?_) (fun 𝔭 => ?_)
      (hbase.mul_left (Nat.card B : ℝ))
    · refine mul_nonneg (Nat.cast_nonneg _) ?_
      by_cases h : b 𝔭.1 = 1
      · rw [if_pos h]; exact primeWeight_nonneg s 𝔭.1
      · rw [if_neg h]
    · refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      by_cases h : b 𝔭.1 = 1
      · rw [if_pos h]
      · rw [if_neg h]; exact primeWeight_nonneg s 𝔭.1
  -- the right hand side is summable
  have hsummR : Summable (fun 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} =>
      ∑ χ : B →* ℂˣ, negLogEulerFactor b χ s 𝔭.1) := by
    refine Summable.congr
      (summable_sum (s := (Finset.univ : Finset (B →* ℂˣ)))
        (f := fun (χ : B →* ℂˣ) (𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S}) =>
          negLogEulerFactor b χ s 𝔭.1) (fun χ _ => summable_negLogEulerFactor b S χ hs)) ?_
    intro 𝔭
    rfl
  have hpt : ∀ 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S},
      (Nat.card B : ℝ) * (if b 𝔭.1 = 1 then primeWeight s 𝔭.1 else 0) ≤
        ∑ χ : B →* ℂˣ, negLogEulerFactor b χ s 𝔭.1 :=
    fun 𝔭 => natCard_mul_ite_le_sum_negLogEulerFactor b hs 𝔭.1
  calc (Nat.card B : ℝ) * trivialClassSum b S s
      = ∑' 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S},
          (Nat.card B : ℝ) * (if b 𝔭.1 = 1 then primeWeight s 𝔭.1 else 0) := by
        rw [trivialClassSum_def, tsum_mul_left]
    _ ≤ ∑' 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S},
          ∑ χ : B →* ℂˣ, negLogEulerFactor b χ s 𝔭.1 :=
        Summable.tsum_le_tsum hpt hsummL hsummR
    _ = ∑ χ : B →* ℂˣ, Real.log ‖eulerProduct b S χ s‖ :=
        (sum_log_norm_eulerProduct_eq_tsum b S hs).symm

end NK.GlobalCFTdeep.SecondInequality
