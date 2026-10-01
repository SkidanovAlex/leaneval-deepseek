import Mathlib
import Submission.Work.ZeroFreeTables.P9.tsum_sq_mul_geometric_le

/-!
# `Work.ZeroFreeTables.P9.vonMangoldt_primePow_series_le`

For a prime `p`, a real `σ > 1` and `j ≤ 2`,

  `∑_{n : IsPrimePow n, n.minFac = p} Λ n · n^{-σ} · (log n)^j ≤ 12 (log p)^{j+1} / p`.

Since `n` is a prime power whose least prime factor is `p`, necessarily `n = p^k` with
`k ≥ 1` (`minFac_primePow_iff`); for such `n` the summand is

  `Λ(p^k) · (p^k)^{-σ} · (log(p^k))^j = (log p)^{j+1} · k^j · x^k`,   `x = p^{-σ}`,

so the series equals `(log p)^{j+1} · ∑_{k ≥ 1} k^j x^k`.  Now `p ≥ 2` and `σ > 1` give
`x ≤ 1/2`, and for `0 ≤ x ≤ 1/2` we have termwise domination by the `j = 2` series,

  `∑_{k ≥ 1} k^j x^k ≤ ∑_{k : ℕ} k^2 x^k = x(1+x)/(1-x)^3 ≤ 12 x`

(`tsum_sq_mul_geometric_le`).  Finally `12 x = 12 p^{-σ} ≤ 12 p^{-1}`.
-/

open scoped BigOperators

namespace Work.ZeroFreeTables.P9

/-- The summand `Λ n · n^{-σ} · (log n)^j`. -/
private noncomputable def vmTerm (σ : ℝ) (j : ℕ) (n : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * (Real.log (n : ℝ)) ^ j

/-- `((p : ℝ)^k)^(-σ) = ((p : ℝ)^(-σ))^k` for `p : ℕ`. -/
private lemma pow_rpow_neg (p : ℕ) (σ : ℝ) (k : ℕ) :
    (((p : ℝ) ^ k) ^ (-σ)) = ((p : ℝ) ^ (-σ)) ^ k := by
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  calc (((p : ℝ) ^ k) ^ (-σ))
      = (((p : ℝ) ^ (k : ℝ)) ^ (-σ)) := by rw [Real.rpow_natCast]
    _ = (p : ℝ) ^ ((k : ℝ) * (-σ)) := (Real.rpow_mul hp0 (k : ℝ) (-σ)).symm
    _ = (p : ℝ) ^ ((-σ) * (k : ℝ)) := by rw [mul_comm]
    _ = ((p : ℝ) ^ (-σ)) ^ (k : ℝ) := Real.rpow_mul hp0 (-σ) (k : ℝ)
    _ = ((p : ℝ) ^ (-σ)) ^ k := by rw [Real.rpow_natCast]

/-- `n` is a prime power whose least prime factor is `p` exactly when `n = p^k`, `k ≥ 1`. -/
private lemma minFac_primePow_iff (p n : ℕ) (hp : p.Prime) :
    (IsPrimePow n ∧ n.minFac = p) ↔ ∃ k : ℕ, 0 < k ∧ n = p ^ k := by
  constructor
  · rintro ⟨hpp, hmin⟩
    obtain ⟨q, k, hq, hk, hqk⟩ := (isPrimePow_def n).mp hpp
    have hq' : q.Prime := Nat.prime_iff.mpr hq
    have hminq : n.minFac = q := by
      rw [← hqk]
      exact hq'.pow_minFac hk.ne'
    have hqp : q = p := by
      rw [← hminq]
      exact hmin
    exact ⟨k, hk, by rw [← hqk, hqp]⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨(isPrimePow_def (p ^ k)).mpr ⟨p, k, hp.prime, hk, rfl⟩, hp.pow_minFac hk.ne'⟩

/-- For `j ≤ 2` and `0 ≤ x ≤ 1/2`: `∑_{k ≥ 1} k^j x^k ≤ 12 x`. -/
private lemma tsum_pos_pow_geometric_le (j : ℕ) (hj : j ≤ 2) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ≤ 1 / 2) :
    (∑' k : ℕ, (if 0 < k then (k : ℝ) ^ j * x ^ k else (0 : ℝ))) ≤ 12 * x := by
  have hx1 : ‖x‖ < 1 := by
    rw [Real.norm_of_nonneg hx0]
    linarith
  have hsum2 : Summable (fun k : ℕ => (k : ℝ) ^ 2 * x ^ k) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hx1
  have hle : ∀ k : ℕ, (if 0 < k then (k : ℝ) ^ j * x ^ k else (0 : ℝ)) ≤ (k : ℝ) ^ 2 * x ^ k := by
    intro k
    by_cases hk : 0 < k
    · rw [if_pos hk]
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hpw : (k : ℝ) ^ j ≤ (k : ℝ) ^ 2 := pow_le_pow_right₀ hk1 hj
      exact mul_le_mul_of_nonneg_right hpw (pow_nonneg hx0 k)
    · rw [if_neg hk]
      exact mul_nonneg (sq_nonneg (k : ℝ)) (pow_nonneg hx0 k)
  have hsumg : Summable (fun k : ℕ => if 0 < k then (k : ℝ) ^ j * x ^ k else (0 : ℝ)) :=
    Summable.of_nonneg_of_le (fun k => by
      by_cases hk : 0 < k
      · rw [if_pos hk]
        exact mul_nonneg (pow_nonneg (Nat.cast_nonneg k) j) (pow_nonneg hx0 k)
      · simp [hk]) hle hsum2
  calc (∑' k : ℕ, (if 0 < k then (k : ℝ) ^ j * x ^ k else (0 : ℝ)))
      ≤ ∑' k : ℕ, (k : ℝ) ^ 2 * x ^ k := Summable.tsum_le_tsum hle hsumg hsum2
    _ ≤ 12 * x := tsum_sq_mul_geometric_le hx0 hx

theorem vonMangoldt_primePow_series_le (p : ℕ) (hp : p.Prime) {σ : ℝ} (hσ : 1 < σ) (j : ℕ) (hj : j ≤ 2) : (∑' n : ℕ, if IsPrimePow n ∧ n.minFac = p then (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * (Real.log (n : ℝ)) ^ j else (0:ℝ)) ≤ 12 * (Real.log (p : ℝ)) ^ (j + 1) / (p : ℝ) := by
  classical
  change (∑' n : ℕ, (if IsPrimePow n ∧ n.minFac = p then vmTerm σ j n else (0 : ℝ)))
      ≤ 12 * (Real.log (p : ℝ)) ^ (j + 1) / (p : ℝ)
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
  have hpne : (p : ℝ) ≠ 0 := ne_of_gt hpR
  have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hp1
  -- `x = p^{-σ}` lies in `[0, 1/2]`
  have hx0 : (0 : ℝ) ≤ (p : ℝ) ^ (-σ) := Real.rpow_nonneg (le_of_lt hpR) (-σ)
  have hx_half : (p : ℝ) ^ (-σ) ≤ 1 / 2 := by
    have h₁ : (p : ℝ) ^ (-σ) ≤ (p : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    have h₂ : (p : ℝ) ^ (-1 : ℝ) ≤ (1 / 2 : ℝ) := by
      rw [Real.rpow_neg_one]
      have h3 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
      have hstep : (1 : ℝ) ≤ (1 / 2) * (p : ℝ) := by linarith
      have h := mul_le_mul_of_nonneg_right hstep (inv_nonneg.mpr (le_of_lt hpR))
      have hR : ((1 / 2 : ℝ) * (p : ℝ)) * (p : ℝ)⁻¹ = 1 / 2 := by
        rw [mul_assoc, mul_inv_cancel₀ hpne, mul_one]
      rw [hR, one_mul] at h
      exact h
    linarith
  -- the support of the series is `{p^k : k ≥ 1}`
  have hsupp : ∀ n : ℕ, (IsPrimePow n ∧ n.minFac = p) ↔ ∃ k : ℕ, 0 < k ∧ n = p ^ k :=
    fun n => minFac_primePow_iff p n hp
  let e : {k : ℕ // 0 < k} ≃ {n : ℕ // IsPrimePow n ∧ n.minFac = p} :=
    Equiv.ofBijective
      (fun k : {k : ℕ // 0 < k} =>
        (⟨p ^ (k : ℕ), (hsupp (p ^ (k : ℕ))).mpr ⟨(k : ℕ), k.2, rfl⟩⟩ :
          {n : ℕ // IsPrimePow n ∧ n.minFac = p}))
      ⟨fun a b hab => by
          have hab' : p ^ (a : ℕ) = p ^ (b : ℕ) := congrArg Subtype.val hab
          exact Subtype.ext (Nat.pow_right_injective hp.two_le hab'),
        fun n => by
          obtain ⟨k, hk, hkn⟩ := (hsupp n.val).mp n.2
          exact ⟨⟨k, hk⟩, Subtype.ext hkn.symm⟩⟩
  have hstep1b : (∑' n : ℕ, (if IsPrimePow n ∧ n.minFac = p then vmTerm σ j n else (0 : ℝ)))
      = ∑' n : ℕ, Set.indicator {n : ℕ | IsPrimePow n ∧ n.minFac = p} (vmTerm σ j) n :=
    tsum_congr (fun n => by
      by_cases h : IsPrimePow n ∧ n.minFac = p
      · rw [if_pos h,
          Set.indicator_of_mem (show n ∈ {n : ℕ | IsPrimePow n ∧ n.minFac = p} from h)]
      · rw [if_neg h,
          Set.indicator_of_notMem (show n ∉ {n : ℕ | IsPrimePow n ∧ n.minFac = p} from h)])
  have hstep1a : (∑' n : ℕ, Set.indicator {n : ℕ | IsPrimePow n ∧ n.minFac = p} (vmTerm σ j) n)
      = ∑' n : {n : ℕ // IsPrimePow n ∧ n.minFac = p}, vmTerm σ j n.val :=
    (tsum_subtype {n : ℕ | IsPrimePow n ∧ n.minFac = p} (vmTerm σ j)).symm
  have hstep1 := hstep1b.trans hstep1a
  have hstep2 : (∑' n : {n : ℕ // IsPrimePow n ∧ n.minFac = p}, vmTerm σ j n.val)
      = ∑' k : {k : ℕ // 0 < k}, vmTerm σ j (p ^ (k : ℕ)) := by
    rw [← Equiv.tsum_eq e
      (fun n : {n : ℕ // IsPrimePow n ∧ n.minFac = p} => vmTerm σ j n.val)]
    exact tsum_congr (fun k => by rfl)
  have hstep3b : (∑' k : ℕ, (if 0 < k then vmTerm σ j (p ^ k) else (0 : ℝ)))
      = ∑' k : ℕ, Set.indicator {k : ℕ | 0 < k} (fun k : ℕ => vmTerm σ j (p ^ k)) k :=
    tsum_congr (fun k => by
      by_cases h : 0 < k
      · rw [if_pos h, Set.indicator_of_mem (show k ∈ {k : ℕ | 0 < k} from h)]
      · rw [if_neg h, Set.indicator_of_notMem (show k ∉ {k : ℕ | 0 < k} from h)])
  have hstep3a : (∑' k : ℕ, Set.indicator {k : ℕ | 0 < k} (fun k : ℕ => vmTerm σ j (p ^ k)) k)
      = ∑' k : {k : ℕ // 0 < k}, vmTerm σ j (p ^ (k : ℕ)) :=
    (tsum_subtype {k : ℕ | 0 < k} (fun k : ℕ => vmTerm σ j (p ^ k))).symm
  have hstep3 := hstep3a.symm.trans hstep3b.symm
  -- value of the summand at `n = p^k`
  have hterm : ∀ k : ℕ, 0 < k → vmTerm σ j (p ^ k)
      = (Real.log (p : ℝ)) ^ (j + 1) * ((k : ℝ) ^ j * ((p : ℝ) ^ (-σ)) ^ k) := by
    intro k hk
    have hk0 : k ≠ 0 := hk.ne'
    have hvm : ArithmeticFunction.vonMangoldt (p ^ k) = Real.log (p : ℝ) := by
      rw [ArithmeticFunction.vonMangoldt_apply_pow (n := p) hk0,
        ArithmeticFunction.vonMangoldt_apply_prime hp]
    have hcast : ((p ^ k : ℕ) : ℝ) = (p : ℝ) ^ k := Nat.cast_pow p k
    have hlog : Real.log ((p : ℝ) ^ k) = (k : ℝ) * Real.log (p : ℝ) := Real.log_pow (p : ℝ) k
    unfold vmTerm
    rw [hvm, hcast, hlog, pow_rpow_neg p σ k, mul_pow, pow_succ]
    first | ring | ring_nf | ac_rfl
  have hsum_eq : (∑' n : ℕ, (if IsPrimePow n ∧ n.minFac = p then vmTerm σ j n else (0 : ℝ)))
      = ∑' k : ℕ, (if 0 < k then vmTerm σ j (p ^ k) else (0 : ℝ)) :=
    hstep1.trans (hstep2.trans hstep3)
  have hkey : (∑' k : ℕ, (if 0 < k then vmTerm σ j (p ^ k) else (0 : ℝ)))
      = (Real.log (p : ℝ)) ^ (j + 1) *
          (∑' k : ℕ, (if 0 < k then (k : ℝ) ^ j * ((p : ℝ) ^ (-σ)) ^ k else (0 : ℝ))) := by
    rw [← tsum_mul_left]
    refine tsum_congr (fun k => ?_)
    by_cases hk : 0 < k
    · simp only [if_pos hk]
      exact hterm k hk
    · simp only [if_neg hk]
      ring
  have hmain : (Real.log (p : ℝ)) ^ (j + 1) *
        (∑' k : ℕ, (if 0 < k then (k : ℝ) ^ j * ((p : ℝ) ^ (-σ)) ^ k else (0 : ℝ)))
      ≤ 12 * (Real.log (p : ℝ)) ^ (j + 1) / (p : ℝ) := by
    have hA := tsum_pos_pow_geometric_le j hj hx0 hx_half
    have hB : (Real.log (p : ℝ)) ^ (j + 1) *
        (∑' k : ℕ, (if 0 < k then (k : ℝ) ^ j * ((p : ℝ) ^ (-σ)) ^ k else (0 : ℝ)))
        ≤ (Real.log (p : ℝ)) ^ (j + 1) * (12 * ((p : ℝ) ^ (-σ))) :=
      mul_le_mul_of_nonneg_left hA (pow_nonneg hlogp (j + 1))
    have hC : (Real.log (p : ℝ)) ^ (j + 1) * (12 * ((p : ℝ) ^ (-σ)))
        ≤ 12 * (Real.log (p : ℝ)) ^ (j + 1) / (p : ℝ) := by
      have hxle : (p : ℝ) ^ (-σ) ≤ (p : ℝ)⁻¹ := by
        have h := Real.rpow_le_rpow_of_exponent_le hp1 (by linarith : -σ ≤ (-1 : ℝ))
        simpa [Real.rpow_neg_one] using h
      have h12 : 12 * ((p : ℝ) ^ (-σ)) ≤ 12 * (p : ℝ)⁻¹ := by linarith
      calc (Real.log (p : ℝ)) ^ (j + 1) * (12 * ((p : ℝ) ^ (-σ)))
          ≤ (Real.log (p : ℝ)) ^ (j + 1) * (12 * (p : ℝ)⁻¹) :=
            mul_le_mul_of_nonneg_left h12 (pow_nonneg hlogp (j + 1))
        _ = 12 * (Real.log (p : ℝ)) ^ (j + 1) / (p : ℝ) := by
            rw [div_eq_mul_inv]
            ring
    linarith
  calc (∑' n : ℕ, (if IsPrimePow n ∧ n.minFac = p then vmTerm σ j n else (0 : ℝ)))
      = ∑' k : ℕ, (if 0 < k then vmTerm σ j (p ^ k) else (0 : ℝ)) := hsum_eq
    _ = (Real.log (p : ℝ)) ^ (j + 1) *
          (∑' k : ℕ, (if 0 < k then (k : ℝ) ^ j * ((p : ℝ) ^ (-σ)) ^ k else (0 : ℝ))) := hkey
    _ ≤ 12 * (Real.log (p : ℝ)) ^ (j + 1) / (p : ℝ) := hmain

end Work.ZeroFreeTables.P9
