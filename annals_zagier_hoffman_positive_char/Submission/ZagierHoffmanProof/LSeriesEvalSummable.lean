import Submission.ZagierHoffmanProof.LSeriesEval

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open Polynomial PowerSeries Finset Filter
open scoped WithZero Topology

/-!
# Joint summability of the double family of the depth-one `L`-series

For `ψ` both small (`GIsSmall γ ψ`, `γ < 1`) and super-entire (`GSuperEntire γ ψ`) and any `c`, the
double family `(n,i) ↦ coeff n (ψ^{(i)}) · c^n` is summable.  This discharges the hypothesis
`hsum` of `LSeriesEval.evalSeriesGen_atL1Gen`.

The proof uses the cofinite criterion `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero`
and the valuation-ball basis `Valued.hasBasis_nhds_zero`: it suffices to show that the terms are
`< δ` outside a *finite* set.  With `B := v c` and `M ≥ 1` chosen so that `γ^M·B < 1` and
`γ^(Mq)·B < 1` (possible by `GammaArchimedean`; `M = 1` works when `B < 1`), and `a` the constant
of `GSuperEntire γ ψ` at that `M`, the estimates are

* (for `n ≥ N`, `i = 0`)     `v ≤ a·(γ^M·B)^n`,
* (for `n ≥ N`, `i ≥ 1`)     `v ≤ (a γ^(Mn))^(q^i)·B^n ≤ (a γ^(Mn))^q·B^n = a^q·(γ^(Mq)·B)^n`,
* (for `n < N`, `i ≥ I`)     `v ≤ γ^(q^i)·(1 ⊔ B^N)`,

so the bad set is contained in `{n < N} × {i < I}` (finite).
-/

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable [CompleteSpace K] [NonarchimedeanAddGroup K]

variable (q : ℕ) [FrobPow K q]

/-- **The joint summability of the double family `(n,i) ↦ coeff n (ψ^{(i)}) · c^n`.** -/
theorem summable_coeff_frobTwist_mul {γ : Γ₀} (hγ : γ < 1) (harch : GammaArchimedean Γ₀)
    (hq : 2 ≤ q) {ψ : PowerSeries K} (hsi : GIsSmall γ ψ) (hse : GSuperEntire γ ψ) (c : K) :
    Summable fun p : ℕ × ℕ =>
      PowerSeries.coeff p.1 (frobTwist (R := K) (p := q) p.2 ψ) * c ^ p.1 := by
  classical
  by_cases hψ0 : ψ = 0
  · rw [show (fun p : ℕ × ℕ => PowerSeries.coeff p.1 (frobTwist (R := K) (p := q) p.2 ψ) * c ^ p.1)
        = fun _ => (0 : K) from by funext p; simp [hψ0]]
    exact summable_zero
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero]
  rw [Filter.tendsto_def]
  intro U hU
  obtain ⟨u, huU⟩ := Valued.mem_nhds_zero.mp hU
  set δ : Γ₀ := MonoidWithZeroHom.ValueGroup₀.embedding
    (f := MonoidWithZeroHom.ofClass (Valued.v : Valuation K Γ₀)) (u.1) with hδdef
  have hδ0 : δ ≠ 0 := by
    rw [hδdef]
    intro hh
    refine Units.ne_zero u (MonoidWithZeroHom.ValueGroup₀.embedding_injective ?_)
    rw [hh, map_zero]
  set B : Γ₀ := Valued.v c with hBdef
  -- the valuation of the terms
  have hval : ∀ n i : ℕ, Valued.v (PowerSeries.coeff n (frobTwist (R := K) (p := q) i ψ) * c ^ n)
      = (Valued.v (PowerSeries.coeff n ψ)) ^ (q ^ i) * B ^ n := by
    intro n i
    rw [map_mul, frobTwist_coeff_v, map_pow, ← hBdef]
  -- a large `M ≥ 1`
  obtain ⟨M, hMle, hM1, hM2⟩ : ∃ M : ℕ, 1 ≤ M ∧ γ ^ M * B < 1 ∧ γ ^ (M * q) * B < 1 := by
    by_cases hB1 : B < 1
    · refine ⟨1, le_refl 1, ?_, ?_⟩
      · calc γ ^ 1 * B = γ * B := by rw [pow_one]
          _ ≤ 1 * B := mul_le_mul_of_nonneg_right hγ.le (zero_le)
          _ = B := one_mul B
          _ < 1 := hB1
      · rw [one_mul]
        calc γ ^ q * B ≤ 1 * B := mul_le_mul_of_nonneg_right (pow_le_one₀ (zero_le) hγ.le) (zero_le)
          _ = B := one_mul B
          _ < 1 := hB1
    · have hBpos : (0 : Γ₀) < B := lt_of_lt_of_le zero_lt_one (not_lt.mp hB1)
      have hBne : B ≠ 0 := ne_of_gt hBpos
      obtain ⟨m, hm⟩ := harch γ hγ (B⁻¹) (inv_ne_zero hBne)
      refine ⟨m + 1, by omega, ?_, ?_⟩
      · have h2 : γ ^ (m + 1) ≤ γ ^ m := pow_le_pow_of_le_one (zero_le) hγ.le (by omega)
        calc γ ^ (m + 1) * B < B⁻¹ * B :=
              mul_lt_mul_of_pos_right (lt_of_le_of_lt h2 hm) hBpos
          _ = 1 := inv_mul_cancel₀ hBne
      · have h2 : γ ^ ((m + 1) * q) ≤ γ ^ m := by
          refine pow_le_pow_of_le_one (zero_le) hγ.le ?_
          calc m ≤ m * q := Nat.le_mul_of_pos_right m (by omega)
            _ ≤ (m + 1) * q := Nat.mul_le_mul_right q (Nat.le_succ m)
        calc γ ^ ((m + 1) * q) * B < B⁻¹ * B :=
              mul_lt_mul_of_pos_right (lt_of_le_of_lt h2 hm) hBpos
          _ = 1 := inv_mul_cancel₀ hBne
  obtain ⟨a, ha⟩ := hse M
  have ha0 : a ≠ 0 := by
    intro h
    refine hψ0 (by
      ext n
      have h1 : Valued.v (PowerSeries.coeff n ψ) = 0 :=
        le_antisymm (by simpa [h] using ha n) (zero_le)
      exact (Valued.v.zero_iff).mp h1)
  have hapos : (0 : Γ₀) < a := lt_of_le_of_ne (zero_le) (Ne.symm ha0)
  -- `n1`: the coefficients are `≤ 1` beyond `n1`
  obtain ⟨n1, hn1⟩ : ∃ n1 : ℕ, ∀ n ≥ n1, a * γ ^ (M * n) ≤ 1 := by
    obtain ⟨k, hk⟩ := harch γ hγ (a⁻¹) (inv_ne_zero ha0)
    refine ⟨k, fun n hn => ?_⟩
    have hMn : k ≤ M * n := le_trans hn (Nat.le_mul_of_pos_left n (by omega))
    have h2 : γ ^ (M * n) ≤ γ ^ k := pow_le_pow_of_le_one (zero_le) hγ.le hMn
    have h3 : a * γ ^ (M * n) < a * a⁻¹ := mul_lt_mul_of_pos_left (lt_of_le_of_lt h2 hk) hapos
    rw [mul_inv_cancel₀ ha0] at h3
    exact le_of_lt h3
  -- `n2`: both estimates are below `δ`
  obtain ⟨n2, hn2⟩ : ∃ n2 : ℕ, ∀ n ≥ n2,
      a * (γ ^ M * B) ^ n < δ ∧ a ^ q * (γ ^ (M * q) * B) ^ n < δ := by
    obtain ⟨k1, hk1⟩ := harch (γ ^ M * B) hM1 (δ / a) (div_ne_zero hδ0 ha0)
    obtain ⟨k2, hk2⟩ := harch (γ ^ (M * q) * B) hM2 (δ / a ^ q)
      (div_ne_zero hδ0 (pow_ne_zero _ ha0))
    refine ⟨max k1 k2, fun n hn => ⟨?_, ?_⟩⟩
    · calc a * (γ ^ M * B) ^ n ≤ a * (γ ^ M * B) ^ k1 :=
            mul_le_mul_of_nonneg_left
              (pow_le_pow_of_le_one (zero_le) hM1.le (le_trans (le_max_left _ _) hn)) (zero_le)
        _ < a * (δ / a) := mul_lt_mul_of_pos_left hk1 hapos
        _ = δ := by rw [mul_comm, div_mul_cancel₀ δ ha0]
    · calc a ^ q * (γ ^ (M * q) * B) ^ n ≤ a ^ q * (γ ^ (M * q) * B) ^ k2 :=
            mul_le_mul_of_nonneg_left
              (pow_le_pow_of_le_one (zero_le) hM2.le (le_trans (le_max_right _ _) hn)) (zero_le)
        _ < a ^ q * (δ / a ^ q) := mul_lt_mul_of_pos_left hk2 (pow_pos hapos q)
        _ = δ := by rw [mul_comm, div_mul_cancel₀ δ (pow_ne_zero _ ha0)]
  -- ## the `n ≥ N` half
  have hN : ∀ n ≥ max n1 n2, ∀ i : ℕ,
      Valued.v (PowerSeries.coeff n (frobTwist (R := K) (p := q) i ψ) * c ^ n) < δ := by
    intro n hn i
    have hn1' : a * γ ^ (M * n) ≤ 1 := hn1 n (le_trans (le_max_left _ _) hn)
    have hn2' := hn2 n (le_trans (le_max_right _ _) hn)
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi
      rw [hval n 0, pow_zero, pow_one]
      calc Valued.v (PowerSeries.coeff n ψ) * B ^ n
          ≤ (a * γ ^ (M * n)) * B ^ n :=
            mul_le_mul_of_nonneg_right (ha n) (zero_le)
        _ = a * (γ ^ M * B) ^ n := by
            rw [mul_assoc, mul_pow, ← pow_mul]
        _ < δ := hn2'.1
    · rw [hval n i]
      have hb : (Valued.v (PowerSeries.coeff n ψ)) ^ (q ^ i) ≤ (a * γ ^ (M * n)) ^ (q ^ i) :=
        pow_le_pow_left₀ (zero_le) (ha n) _
      have hc : (a * γ ^ (M * n)) ^ (q ^ i) ≤ (a * γ ^ (M * n)) ^ q :=
        pow_le_pow_of_le_one (zero_le) hn1' (by
          calc q = q ^ 1 := (pow_one q).symm
            _ ≤ q ^ i := Nat.pow_le_pow_right (by omega) hi)
      have hd : (a * γ ^ (M * n)) ^ q * B ^ n = a ^ q * (γ ^ (M * q) * B) ^ n := by
        have e1 : (a * γ ^ (M * n)) ^ q = a ^ q * γ ^ (M * n * q) := by
          rw [mul_pow, ← pow_mul]
        have e2 : (γ ^ (M * q) * B) ^ n = γ ^ (M * q * n) * B ^ n := by
          rw [mul_pow, ← pow_mul]
        have hexp : M * n * q = M * q * n := by ring
        rw [e1, e2, hexp, mul_assoc]
      calc (Valued.v (PowerSeries.coeff n ψ)) ^ (q ^ i) * B ^ n
          ≤ (a * γ ^ (M * n)) ^ (q ^ i) * B ^ n := mul_le_mul_of_nonneg_right hb (zero_le)
        _ ≤ (a * γ ^ (M * n)) ^ q * B ^ n := mul_le_mul_of_nonneg_right hc (zero_le)
        _ = a ^ q * (γ ^ (M * q) * B) ^ n := hd
        _ < δ := hn2'.2
  -- ## the `i ≥ I` half for `n < N`
  set C : Γ₀ := (1 : Γ₀) ⊔ B ^ max n1 n2 with hCdef
  have hCpos : (0 : Γ₀) < C := lt_of_lt_of_le zero_lt_one le_sup_left
  have hCne : C ≠ 0 := ne_of_gt hCpos
  have hBmax : ∀ n ≤ max n1 n2, B ^ n ≤ C := by
    intro n hn
    by_cases hB1 : B ≤ 1
    · exact le_trans (pow_le_one₀ (zero_le) hB1) le_sup_left
    · exact le_trans (pow_le_pow_right₀ (le_of_lt (not_le.mp hB1)) hn) le_sup_right
  obtain ⟨I, hI⟩ : ∃ I : ℕ, ∀ i ≥ I, γ ^ (q ^ i) * C < δ := by
    obtain ⟨k, hk⟩ := harch γ hγ (δ / C) (div_ne_zero hδ0 hCne)
    refine ⟨k, fun i hi => ?_⟩
    have hqk : k ≤ q ^ i := by
      calc k ≤ q ^ k := le_of_lt (Nat.lt_pow_self (n := k) (by omega))
        _ ≤ q ^ i := Nat.pow_le_pow_right (by omega) hi
    calc γ ^ (q ^ i) * C ≤ γ ^ k * C :=
          mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (zero_le) hγ.le hqk) (zero_le)
      _ < (δ / C) * C := mul_lt_mul_of_pos_right hk hCpos
      _ = δ := div_mul_cancel₀ δ hCne
  have hIgood : ∀ n < max n1 n2, ∀ i ≥ I,
      Valued.v (PowerSeries.coeff n (frobTwist (R := K) (p := q) i ψ) * c ^ n) < δ := by
    intro n hn i hi
    rw [hval n i]
    have h1 : (Valued.v (PowerSeries.coeff n ψ)) ^ (q ^ i) ≤ γ ^ (q ^ i) :=
      pow_le_pow_left₀ (zero_le) (hsi n) _
    have h2 : B ^ n ≤ C := hBmax n (le_of_lt hn)
    calc (Valued.v (PowerSeries.coeff n ψ)) ^ (q ^ i) * B ^ n ≤ γ ^ (q ^ i) * C :=
          mul_le_mul h1 h2 (zero_le) (zero_le)
      _ < δ := hI i hi
  -- ## assembly
  have hS : ∀ᶠ p : ℕ × ℕ in cofinite,
      Valued.v (PowerSeries.coeff p.1 (frobTwist (R := K) (p := q) p.2 ψ) * c ^ p.1) < δ := by
    rw [Filter.eventually_cofinite]
    refine Set.Finite.subset ((Set.finite_Iio (max n1 n2)).prod (Set.finite_Iio I)) ?_
    intro p hp
    by_cases h1 : p.1 < max n1 n2
    · refine ⟨h1, ?_⟩
      by_contra h2c
      exact absurd (hIgood p.1 h1 p.2 (not_lt.mp h2c)) hp
    · exact absurd (hN p.1 (not_lt.mp h1) p.2) hp
  filter_upwards [hS] with p hp
  exact huU (by
    show Valued.v.restrict
      (PowerSeries.coeff p.1 (frobTwist (R := K) (p := q) p.2 ψ) * c ^ p.1) < (u : _)
    rw [Valuation.restrict_lt_iff_lt_embedding]
    exact hp)

section Unconditional

variable (q : ℕ) [FrobPow K q]

/-- **The depth-one `L`-series evaluated at a point** — unconditional form, with the joint
summability of `summable_coeff_frobTwist_mul` discharged (using `ψ := ω^s * 1` and
`GIsSmall.pow_add_one`; note `s ≥ 1` is needed because `GIsSmall γ 1` is false). -/
theorem evalSeriesGen_atL1Gen' {γ : Γ₀} (hγ : γ < 1) (harch : GammaArchimedean Γ₀)
    (hq : 2 ≤ q) {ω : PowerSeries K} (hsi : GIsSmall γ ω) (hse : GSuperEntire γ ω)
    (s : ℕ) (hs : 1 ≤ s) (c : K) :
    evalSeriesGen (atL1Gen q ω s (1 : PowerSeries K)) c
      = ∑' i : ℕ, (evalSeriesGen (frobTwist (R := K) (p := q) i ω) c) ^ s := by
  have hsi' : GIsSmall γ (ω ^ s * 1) := by
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hs) with ⟨k, rfl⟩
    simpa using hsi.pow_add_one hγ.le k
  have hse' : GSuperEntire γ (ω ^ s * 1) := by
    simpa using hse.pow hγ.le s
  exact evalSeriesGen_atL1Gen q hγ harch hq hse s hs c
    (summable_coeff_frobTwist_mul q hγ harch hq hsi' hse' c)

end Unconditional

end ZagierHoffmanPositiveChar
