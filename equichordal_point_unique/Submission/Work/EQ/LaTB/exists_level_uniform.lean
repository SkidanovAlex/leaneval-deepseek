import Mathlib
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.FanTri.fan_split2

namespace Work.EQ.LaTB

open Filter

/-- `eqLam a = (1 - a)/(1 + a)` is positive for `0 < a < 1`. -/
private lemma eqLam_pos_local {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 0 < Work.EQ.eqLam a := by
  rw [Work.EQ.eqLam]
  exact div_pos (by linarith) (by linarith)

/-- `eqLam a = (1 - a)/(1 + a)` is `< 1` for `0 < a < 1`. -/
private lemma eqLam_lt_one_local {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : Work.EQ.eqLam a < 1 := by
  rw [Work.EQ.eqLam]
  rw [div_lt_one (by linarith : (0 : ℝ) < 1 + a)]
  linarith

/-- **A common reading level for a whole sequence of parameters.**

Let `0 < r₁ < r₂` with `r₂/r₁ > 1/λ` (so the annulus `Ann r₁ r₂` has ratio bigger than `1/λ`,
`λ = eqLam a ∈ (0,1)`) and let `t : ℕ → ℝ` be a sequence of parameters with `r₁ ≤ t k` for all `k`
and `t k ≤ B` for all `k`.  Then, after passing to a subsequence, there is a *single* exponent
`N : ℕ` with `r₁ ≤ λ^N t k ≤ r₂` for all `k` in the subsequence.

Proof.  For a single `t ≥ r₁`, the sequence `λ^n t` (`n = 0, 1, 2, …`) decreases from `t ≥ r₁` to
`0`; let `N` be the least `n` with `λ^n t < r₂`.  If `N = 0` then `t ∈ [r₁, r₂]`; if `N ≥ 1` then
by minimality `λ^(N-1) t ≥ r₂`, so `λ^N t ≥ λ r₂ > r₁` because `r₂/r₁ > 1/λ` gives
`r₁ < λ r₂`.  Hence such an `N` exists for every `k`.  For the uniformity: any admissible exponent
satisfies `λ^N = (λ^N t k)/t k ≥ r₁/t k ≥ r₁/B > 0` and `λ^N ≤ r₂/t k ≤ r₂/r₁`, and the set of
exponents `n` with `λ^n` in a compact subset of `(0,∞)` is finite (as `λ^n → 0`); hence the
exponents take finitely many values and a subsequence makes them constant, e.g. via
`Work.EQ.FanTri.exists_const_subseq_of_finite` (`FanTri/fan_split.lean`) with
`T = {n : ℕ // n ≤ C}`. -/
theorem exists_level_uniform {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂) (hratio : 1 / Work.EQ.eqLam a < r₂ / r₁)
    (t : ℕ → ℝ) (ht : ∀ k, r₁ ≤ t k) (hB : ∃ B : ℝ, ∀ k, t k ≤ B) :
    ∃ N : ℕ, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ k, r₁ ≤ (Work.EQ.eqLam a) ^ N * t (ψ k) ∧ (Work.EQ.eqLam a) ^ N * t (ψ k) ≤ r₂ := by
  set lam := Work.EQ.eqLam a with hlam
  have hlam0 : 0 < lam := by rw [hlam]; exact eqLam_pos_local ha0 ha1
  have hlam1 : lam < 1 := by rw [hlam]; exact eqLam_lt_one_local ha0 ha1
  have hr₂ : 0 < r₂ := lt_trans hr₁ hr₁₂
  -- `r₂/r₁ > 1/λ` gives `r₁ < λ r₂`.
  have hlamr : r₁ < lam * r₂ := by
    have h1 : r₁ * (1 / lam) < r₁ * (r₂ / r₁) := mul_lt_mul_of_pos_left hratio hr₁
    have h2 : r₁ * (1 / lam) = r₁ / lam := by ring
    have h3 : r₁ * (r₂ / r₁) = r₂ := by field_simp
    rw [h2, h3] at h1
    have h4 : r₁ / lam * lam < r₂ * lam := mul_lt_mul_of_pos_right h1 hlam0
    have h5 : r₁ / lam * lam = r₁ := by field_simp
    rw [h5] at h4
    have h6 : r₂ * lam = lam * r₂ := by ring
    rwa [h6] at h4
  -- An upper bound `B > 0` for the sequence.
  obtain ⟨B, hBle⟩ := hB
  have hBpos : 0 < B := lt_of_lt_of_le hr₁ (le_trans (ht 0) (hBle 0))
  have hc : 0 < r₁ / B := div_pos hr₁ hBpos
  -- Choose `C` with `λ^C < r₁/B`; then no admissible exponent exceeds `C`.
  obtain ⟨C, hC⟩ : ∃ C : ℕ, lam ^ C < r₁ / B := by
    have htend := tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt hlam0) hlam1
    have hev : ∀ᶠ n : ℕ in atTop, lam ^ n < r₁ / B := (tendsto_order.1 htend).2 _ hc
    obtain ⟨a', ha'⟩ := eventually_atTop.1 hev
    exact ⟨a', ha' a' le_rfl⟩
  -- For each `k` there is an exponent `N k` (the least one) reading `t k` into `[r₁, r₂)`.
  have hex : ∀ k, ∃ n : ℕ, lam ^ n * t k < r₂ := by
    intro k
    have htend : Tendsto (fun n : ℕ => lam ^ n * t k) atTop (nhds 0) := by
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt hlam0) hlam1).mul_const (t k)
      simpa using h
    have hev : ∀ᶠ n : ℕ in atTop, lam ^ n * t k < r₂ := (tendsto_order.1 htend).2 r₂ hr₂
    obtain ⟨a', ha'⟩ := eventually_atTop.1 hev
    exact ⟨a', ha' a' le_rfl⟩
  have hspec : ∀ k, lam ^ (Nat.find (hex k)) * t k < r₂ := fun k => Nat.find_spec (hex k)
  have hmin : ∀ k m, m < Nat.find (hex k) → r₂ ≤ lam ^ m * t k := by
    intro k m hm
    exact not_lt.mp (Nat.find_min (hex k) hm)
  -- Lower bound: `λ^{N k} t k ≥ r₁`.
  have hlow : ∀ k, r₁ ≤ lam ^ (Nat.find (hex k)) * t k := by
    intro k
    rcases Nat.eq_zero_or_pos (Nat.find (hex k)) with h0 | hpos
    · rw [h0]; simp only [pow_zero, one_mul]; exact ht k
    · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      have hminj : r₂ ≤ lam ^ j * t k := hmin k j (by rw [hj]; exact Nat.lt_succ_self j)
      calc r₁ ≤ lam * r₂ := le_of_lt hlamr
        _ ≤ lam * (lam ^ j * t k) := mul_le_mul_of_nonneg_left hminj (le_of_lt hlam0)
        _ = lam ^ (Nat.find (hex k)) * t k := by rw [hj, pow_succ]; ring
  -- Uniform bound on the exponents.
  have hNle : ∀ k, Nat.find (hex k) ≤ C := by
    intro k
    by_contra hcon
    rw [not_le] at hcon
    have h1 : lam ^ (Nat.find (hex k)) ≤ lam ^ C :=
      pow_le_pow_of_le_one (le_of_lt hlam0) (le_of_lt hlam1) hcon.le
    have htk : 0 < t k := lt_of_lt_of_le hr₁ (ht k)
    have hstep : r₁ / t k ≤ lam ^ (Nat.find (hex k)) := by
      rw [div_le_iff₀ htk]; exact hlow k
    have hle : r₁ / B ≤ r₁ / t k := by
      rw [div_le_div_iff_of_pos_left hr₁ hBpos htk]; exact hBle k
    linarith
  -- Pigeonhole: finitely many exponents, so pass to a constant subsequence.
  haveI : Finite ↥(Set.Iic C) := (Set.finite_Iic C).to_subtype
  obtain ⟨t0, ψ, hψ, hconst⟩ := Work.EQ.FanTri.exists_const_subseq_of_finite
    (fun k => (⟨Nat.find (hex k), hNle k⟩ : ↥(Set.Iic C)))
  refine ⟨t0.val, ψ, hψ, fun k => ?_⟩
  have hNk : Nat.find (hex (ψ k)) = t0.val := congrArg Subtype.val (hconst k)
  have h1 := hlow (ψ k)
  have h2 := hspec (ψ k)
  rw [hNk] at h1 h2
  exact ⟨h1, le_of_lt h2⟩

end Work.EQ.LaTB
