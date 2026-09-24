import Mathlib
import Submission.Commons.NumberTheory.Mertens.primeProduct_oneSubInvPred_log_tendsto_pos

open Filter Finset
open scoped BigOperators Topology

namespace Commons.NumberTheory.Chen

noncomputable section

/-! # Two-sided Mertens bound for `∏_{3 ≤ p ≤ z} (1 − 1/(p−1))`

For `3 ≤ z`, the singular-series product
`P z = ∏_{p prime, p ≠ 2, p ≤ ⌊z⌋₊} (1 − 1/(p−1))` satisfies
`c / log z ≤ P z ≤ C / log z` for two positive constants `c ≤ C`.

This follows from the one-sided asymptotic (Mertens-type) statement
`primeProduct_oneSubInvPred_log_tendsto_pos`: `log z · P z` tends to a positive
limit `L`.  Convergence gives the bounds for all large `z`; on the remaining
compact range `3 ≤ z ≤ Z` the product is piecewise constant in `⌊z⌋₊`, positive
and bounded, which gives the bounds there. -/

/-- `1 − 1/(p−1)`, the singular-series factor attached to an odd prime `p`. -/
private def ppFactor (p : ℕ) : ℝ := 1 - (1 : ℝ) / ((p : ℝ) - 1)

/-- The set of odd primes `≤ n`. -/
private def ppSet (n : ℕ) : Finset ℕ := (Nat.primesLE n).filter (fun p : ℕ => p ≠ 2)

/-- The product `∏_{3 ≤ p ≤ n} (1 − 1/(p−1))`, for `n : ℕ`. -/
private def ppProd (n : ℕ) : ℝ := ∏ p ∈ ppSet n, ppFactor p

/-- `log z · (product over odd primes ≤ ⌊z⌋₊)`. -/
private def ppLogMul (z : ℝ) : ℝ := Real.log z * ppProd (⌊z⌋₊)

private lemma three_le_of_mem_ppSet {n : ℕ} {p : ℕ} (hp : p ∈ ppSet n) : 3 ≤ p := by
  have hp' := (Finset.mem_filter.mp hp)
  have hpp : Nat.Prime p := (Nat.mem_primesLE.mp hp'.1).2
  have h2 : 2 ≤ p := Nat.Prime.two_le hpp
  omega

private lemma ppFactor_pos {p : ℕ} (hp : 3 ≤ p) : 0 < ppFactor p := by
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hx : (2 : ℝ) ≤ (p : ℝ) - 1 := by linarith
  have hx0 : 0 < (p : ℝ) - 1 := by linarith
  have hinv : 1 / ((p : ℝ) - 1) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hx
  have hlt : 1 / ((p : ℝ) - 1) < 1 := lt_of_le_of_lt hinv (by norm_num)
  unfold ppFactor
  linarith

private lemma ppFactor_nonneg {p : ℕ} (hp : 3 ≤ p) : 0 ≤ ppFactor p :=
  le_of_lt (ppFactor_pos hp)

private lemma ppFactor_le_one {p : ℕ} (hp : 3 ≤ p) : ppFactor p ≤ 1 := by
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hx0 : 0 < (p : ℝ) - 1 := by linarith
  have hnonneg : 0 ≤ (1 : ℝ) / ((p : ℝ) - 1) := by positivity
  unfold ppFactor
  linarith

private lemma ppProd_pos (n : ℕ) : 0 < ppProd n := by
  refine Finset.prod_pos ?_
  intro p hp
  exact ppFactor_pos (three_le_of_mem_ppSet hp)

private lemma ppProd_nonneg (n : ℕ) : 0 ≤ ppProd n := le_of_lt (ppProd_pos n)

private lemma ppProd_le_one (n : ℕ) : ppProd n ≤ 1 := by
  refine Finset.prod_le_one₀ ?_ ?_
  · intro p hp
    exact ppFactor_nonneg (three_le_of_mem_ppSet hp)
  · intro p hp
    exact ppFactor_le_one (three_le_of_mem_ppSet hp)

/-- The product is decreasing in `n`: adding more (odd prime) factors only
multiplies by numbers in `(0, 1]`. -/
private lemma ppProd_antitone {a b : ℕ} (hab : a ≤ b) : ppProd b ≤ ppProd a := by
  have hsub : ppSet a ⊆ ppSet b := by
    intro p hp
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_primesLE.mpr ⟨le_trans (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).1 hab,
          (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2⟩, (Finset.mem_filter.mp hp).2⟩
  have hsub' : ppSet b \ ppSet a ⊆ ppSet b := Finset.sdiff_subset
  have hprod_le_one : (∏ x ∈ ppSet b \ ppSet a, ppFactor x) ≤ 1 := by
    refine Finset.prod_le_one₀ ?_ ?_
    · intro x hx
      exact ppFactor_nonneg (three_le_of_mem_ppSet (hsub' hx))
    · intro x hx
      exact ppFactor_le_one (three_le_of_mem_ppSet (hsub' hx))
  have hprod := Finset.prod_sdiff (s₁ := ppSet a) (s₂ := ppSet b) (f := ppFactor) hsub
  calc
    ppProd b = (∏ x ∈ ppSet b \ ppSet a, ppFactor x) * ppProd a := by
      rw [ppProd, ppProd, ← hprod]
    _ ≤ 1 * ppProd a := by
      exact mul_le_mul_of_nonneg_right hprod_le_one (ppProd_nonneg a)
    _ = ppProd a := by simp

theorem twin_product_ratio :
    ∃ (c C : ℝ), 0 < c ∧ c ≤ C ∧ ∀ z : ℝ, 3 ≤ z →
      c / Real.log z ≤
        (∏ p ∈ (⌊z⌋₊.primesLE.filter (fun p => p ≠ 2)),
          (1 - (1 : ℝ) / ((p : ℝ) - 1))) ∧
        (∏ p ∈ (⌊z⌋₊.primesLE.filter (fun p => p ≠ 2)),
          (1 - (1 : ℝ) / ((p : ℝ) - 1))) ≤ C / Real.log z := by
  -- pull the one-sided asymptotic:  L > 0,  log z * P(z) → L
  have hmain : ∃ L : ℝ, 0 < L ∧ Tendsto ppLogMul atTop (nhds L) := by
    change ∃ L : ℝ, 0 < L ∧ Tendsto
        (fun z : ℝ => Real.log z * (∏ p ∈ (⌊z⌋₊.primesLE.filter (fun p : ℕ => p ≠ 2)),
          (1 - (1 : ℝ) / ((p : ℝ) - 1)))) atTop (nhds L)
    exact (Commons.NumberTheory.Mertens.primeProduct_oneSubInvPred_log_tendsto_pos)
  rcases hmain with ⟨L, hLpos, hTendsto⟩
  -- from convergence to L > 0 :  eventually  L/2 < f z  and  f z < 2L
  have hlow : ∀ᶠ z : ℝ in atTop, L / 2 < ppLogMul z := by
    have hc : Tendsto (fun z : ℝ => L / 2) atTop (𝓝 (L / 2)) := tendsto_const_nhds
    exact hc.eventually_lt hTendsto (by linarith)
  have hup : ∀ᶠ z : ℝ in atTop, ppLogMul z < 2 * L := by
    have hc : Tendsto (fun z : ℝ => 2 * L) atTop (𝓝 (2 * L)) := tendsto_const_nhds
    exact hTendsto.eventually_lt hc (by linarith)
  have hall : ∀ᶠ z : ℝ in atTop, 3 ≤ z ∧ L / 2 ≤ ppLogMul z ∧ ppLogMul z ≤ 2 * L := by
    filter_upwards [eventually_ge_atTop (3 : ℝ), hlow, hup] with z hz3 hlo hupz
    exact ⟨hz3, le_of_lt hlo, le_of_lt hupz⟩
  rcases (Filter.eventually_atTop.mp hall) with ⟨Z₀, hZ₀⟩
  let Z : ℝ := max Z₀ 3
  have hZge3 : 3 ≤ Z := le_max_right Z₀ 3
  have hZ₀Z : Z₀ ≤ Z := le_max_left Z₀ 3
  have hZ₀' : ∀ b : ℝ, Z ≤ b → 3 ≤ b ∧ L / 2 ≤ ppLogMul b ∧ ppLogMul b ≤ 2 * L := by
    intro b hb
    exact hZ₀ b (le_trans hZ₀Z hb)
  let N : ℕ := ⌊Z⌋₊
  let c : ℝ := min (L / 2) (Real.log 3 * ppProd N)
  let C : ℝ := max (2 * L) (Real.log Z)
  have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hc_pos : 0 < c := by
    unfold c
    apply lt_min
    · linarith
    · exact mul_pos hlog3pos (ppProd_pos N)
  have hc_le_C : c ≤ C := by
    calc
      c ≤ L / 2 := by exact min_le_left (L / 2) (Real.log 3 * ppProd N)
      _ ≤ 2 * L := by linarith
      _ ≤ C := by exact le_max_left (2 * L) (Real.log Z)
  -- two-sided bound  c ≤ log z * P(z) ≤ C  for all  z ≥ 3
  have hbounds : ∀ z : ℝ, 3 ≤ z → c ≤ ppLogMul z ∧ ppLogMul z ≤ C := by
    intro z hz
    by_cases hzZ : z ≤ Z
    · -- compact part:  3 ≤ z ≤ Z
      have hfz : ppLogMul z = Real.log z * ppProd (⌊z⌋₊) := by rfl
      have hpp_lower : ppProd N ≤ ppProd (⌊z⌋₊) := ppProd_antitone (Nat.floor_mono hzZ)
      have hlog_lower : Real.log 3 ≤ Real.log z := Real.log_le_log (by norm_num) hz
      have hmul_lower : Real.log 3 * ppProd N ≤ Real.log z * ppProd (⌊z⌋₊) := by
        exact mul_le_mul hlog_lower hpp_lower (ppProd_nonneg N) (le_of_lt (Real.log_pos (by linarith : (1 : ℝ) < z)))
      have hlogZ : 0 ≤ Real.log Z := le_of_lt (Real.log_pos (by linarith : (1 : ℝ) < Z))
      have hpp_le_one : ppProd (⌊z⌋₊) ≤ 1 := ppProd_le_one _
      have hlog_upper : Real.log z ≤ Real.log Z := Real.log_le_log (by linarith : (0 : ℝ) < z) hzZ
      have hmul_upper : Real.log z * ppProd (⌊z⌋₊) ≤ Real.log Z := by
        calc
          Real.log z * ppProd (⌊z⌋₊) ≤ Real.log Z * 1 := by
            exact mul_le_mul hlog_upper hpp_le_one (ppProd_nonneg _) hlogZ
          _ = Real.log Z := by simp
      constructor
      · calc
          c ≤ Real.log 3 * ppProd N := by exact min_le_right (L / 2) (Real.log 3 * ppProd N)
          _ ≤ Real.log z * ppProd (⌊z⌋₊) := hmul_lower
          _ = ppLogMul z := hfz.symm
      · calc
          ppLogMul z = Real.log z * ppProd (⌊z⌋₊) := hfz
          _ ≤ Real.log Z := hmul_upper
          _ ≤ C := by exact le_max_right (2 * L) (Real.log Z)
    · -- eventual part
      have hZz : Z ≤ z := le_of_lt (lt_of_not_ge hzZ)
      have hh := hZ₀' z hZz
      constructor
      · exact le_trans (by exact min_le_left (L / 2) (Real.log 3 * ppProd N)) hh.2.1
      · exact le_trans hh.2.2 (by exact le_max_left (2 * L) (Real.log Z))
  -- transfer to the ratio form in the statement
  refine ⟨c, C, hc_pos, hc_le_C, ?_⟩
  intro z hz
  have hlog : 0 < Real.log z := Real.log_pos (by linarith : (1 : ℝ) < z)
  have hb := hbounds z hz
  have hc_le_mul : c ≤ Real.log z * (∏ p ∈ (⌊z⌋₊.primesLE.filter (fun p => p ≠ 2)),
        (1 - (1 : ℝ) / ((p : ℝ) - 1))) := by
    simpa [ppLogMul, ppProd, ppSet, ppFactor, mul_comm] using hb.1
  have hmul_le_C : (∏ p ∈ (⌊z⌋₊.primesLE.filter (fun p => p ≠ 2)),
        (1 - (1 : ℝ) / ((p : ℝ) - 1))) * Real.log z ≤ C := by
    simpa [ppLogMul, ppProd, ppSet, ppFactor, mul_comm] using hb.2
  constructor
  · exact (div_le_iff₀ hlog).2 (by simpa [mul_comm] using hc_le_mul)
  · exact (le_div_iff₀ hlog).2 hmul_le_C

end

end Commons.NumberTheory.Chen
