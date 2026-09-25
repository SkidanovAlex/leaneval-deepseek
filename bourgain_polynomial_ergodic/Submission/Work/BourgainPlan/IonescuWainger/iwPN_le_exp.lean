import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.Defs

/-!
# `P_N ⊆ ℕ_{e^{N^ρ}}`

MST's multiplier set `P_N = {Q·w : Q | Q₀, w ∈ Π(ℙ_N) ∪ {1}}` (here `iwPN`) is contained in the
integers up to `e^{N^ρ}`.  Concretely we prove the slightly stronger `(q:ℝ) ≤ e^{N^ρ/2}`, which is
what the counting estimates of chapter (A) use.

The proof has two halves.

* **Number theory.**  Every `q ∈ iwPN ρ N` factors as `q = Q·w` with `Q ≤ Q₀ = (N₀!)^D` and
  `w ≤ N^{D·D}` (`D = ⌊2/ρ⌋+1`, `N₀ = ⌊N^{ρ/2}⌋+1`): the elements of `iwPiK D V k` are products of
  `k ≤ D` primes of `V ⊆ [0,N]` raised to exponents `≤ D`.  Since `N₀ ≤ 2N^{ρ/2}` and
  `(N₀!) ≤ N₀^{N₀}`, this gives `q ≤ (2N^{ρ/2})^{N₀D}·N^{D²}`.
* **Elementary analysis.**  Taking logarithms, `log q ≤ A·N^{ρ/2}·log N` for a constant
  `A > 0` depending on `ρ` only, and `A·N^{ρ/2}·log N ≤ N^ρ/2` as soon as
  `N ≥ (4A/(ρ/2))^{4/ρ}`; this is the classical fact that a power of `N` dominates `log N`, proved
  here from `log x ≤ x^t/t` (valid for `x ≥ 1`, `t > 0`) rather than from any asymptotic library.
-/

open Finset

namespace Work.BourgainPlan.IonescuWainger

/-! ### Combinatorial bound on `Π(V)` -/

/-- Elements of `iwPiK D V k` (products of `k` distinct primes of `V`, exponents in `{1,…,D}`) are
at most `N ^ (D*D)` when `V ⊆ [0,N]` and `k ≤ D`. -/
lemma iwPiK_le {D N k : ℕ} {V : Finset ℕ} (hV : ∀ p ∈ V, p ≤ N) (hN : 1 ≤ N) (hk : k ≤ D)
    {w : ℕ} (hw : w ∈ iwPiK D V k) : w ≤ N ^ (D * D) := by
  rw [iwPiK, Finset.mem_biUnion] at hw
  obtain ⟨t, ht, hw⟩ := hw
  rw [Finset.mem_filter, Finset.mem_powerset] at ht
  obtain ⟨htV, htcard⟩ := ht
  rw [Finset.mem_image] at hw
  obtain ⟨f, hf, rfl⟩ := hw
  simp only [Finset.mem_pi, Finset.mem_Icc] at hf
  calc
    ∏ p ∈ t.attach, (p : ℕ) ^ f p p.2
        ≤ ∏ _p ∈ t.attach, N ^ D := by
          apply Finset.prod_le_prod'
          intro p _
          have ht' : (p : ℕ) ∈ t := p.2
          have hpN : (p : ℕ) ≤ N := hV _ (htV ht')
          have hfD : f (p : ℕ) ht' ≤ D := (hf (p : ℕ) ht').2
          exact (Nat.pow_le_pow_left hpN _).trans (Nat.pow_le_pow_right (by omega) hfD)
    _ = (N ^ D) ^ k := by rw [Finset.prod_const, Finset.card_attach, htcard]
    _ ≤ (N ^ D) ^ D := pow_le_pow_right₀ (one_le_pow₀ hN) hk
    _ = N ^ (D * D) := by rw [pow_mul]

/-- Elements of `iwPi D V` (products of at most `D` distinct primes of `V`, exponents in
`{1,…,D}`) are at most `N ^ (D*D)` when `V ⊆ [0,N]`. -/
lemma iwPi_le {D N : ℕ} {V : Finset ℕ} (hV : ∀ p ∈ V, p ≤ N) (hN : 1 ≤ N)
    {w : ℕ} (hw : w ∈ iwPi D V) : w ≤ N ^ (D * D) := by
  rw [iwPi, Finset.mem_biUnion] at hw
  obtain ⟨k, hk, hw⟩ := hw
  exact iwPiK_le hV hN (Finset.mem_Icc.mp hk).2 hw

/-! ### Elementary analysis: `log N` against `N^t` -/

/-- For `x ≥ 1` and `t > 0`, `log x ≤ x^t / t`: write `x = (x^t)^{1/t}` and use `log y ≤ y`. -/
lemma log_le_rpow_div {x t : ℝ} (hx : 1 ≤ x) (ht : 0 < t) : Real.log x ≤ x ^ t / t := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hxt : 0 < x ^ t := Real.rpow_pos_of_pos hx0 t
  have heq : (x ^ t) ^ (1 / t) = x := by
    rw [← Real.rpow_mul (le_of_lt hx0), one_div, mul_inv_cancel₀ ht0, Real.rpow_one]
  calc Real.log x = (1 / t) * Real.log (x ^ t) := by
        rw [← Real.log_rpow hxt (1 / t), heq]
    _ ≤ (1 / t) * x ^ t := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith [Real.log_le_sub_one_of_pos hxt]
    _ = x ^ t / t := by ring

/-- For `a > 0` and `t > 0` there is `C ≥ 3` with `a * log N ≤ N^t` for every `N ≥ C`. -/
lemma exists_log_le_rpow (a t : ℝ) (ha : 0 < a) (ht : 0 < t) :
    ∃ C : ℝ, 3 ≤ C ∧ ∀ N : ℕ, C ≤ (N : ℝ) → a * Real.log N ≤ (N : ℝ) ^ t := by
  refine ⟨max 3 ((2 * a / t) ^ (2 / t)), le_max_left _ _, ?_⟩
  intro N hN
  have hNC : (2 * a / t) ^ (2 / t) ≤ (N : ℝ) := le_trans (le_max_right _ _) hN
  have hN1 : (1 : ℝ) ≤ N := by
    have : (3 : ℝ) ≤ N := le_trans (le_max_left _ _) hN
    linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have ht2 : 0 < t / 2 := by linarith
  have hbase : 0 < 2 * a / t := by positivity
  have hkey : 2 * a / t ≤ (N : ℝ) ^ (t / 2) := by
    have h1 : ((2 * a / t) ^ (2 / t)) ^ (t / 2) ≤ (N : ℝ) ^ (t / 2) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hbase.le _) hNC ht2.le
    have h2 : ((2 * a / t) ^ (2 / t)) ^ (t / 2) = 2 * a / t := by
      rw [← Real.rpow_mul hbase.le]
      have h2' : 2 / t * (t / 2) = 1 := by field_simp
      rw [h2', Real.rpow_one]
    simpa [h2] using h1
  have hlog : Real.log N ≤ 2 * (N : ℝ) ^ (t / 2) / t := by
    have h := log_le_rpow_div hN1 ht2
    have hdiv : (N : ℝ) ^ (t / 2) / (t / 2) = 2 * (N : ℝ) ^ (t / 2) / t := by field_simp
    rwa [hdiv] at h
  calc a * Real.log N ≤ a * (2 * (N : ℝ) ^ (t / 2) / t) := mul_le_mul_of_nonneg_left hlog ha.le
    _ = (2 * a / t) * (N : ℝ) ^ (t / 2) := by ring
    _ ≤ (N : ℝ) ^ (t / 2) * (N : ℝ) ^ (t / 2) :=
        mul_le_mul_of_nonneg_right hkey (Real.rpow_nonneg hN0.le _)
    _ = (N : ℝ) ^ t := by
        rw [← Real.rpow_add hN0, show t / 2 + t / 2 = t from by ring]

/-! ### The main bound -/

theorem iwPN_le_exp (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, C ≤ N → ∀ q : ℕ, q ∈ iwPN ρ N →
      (q : ℝ) ≤ Real.exp ((N : ℝ) ^ ρ / 2) := by
  set s : ℝ := ρ / 2 with hs_def
  have hs : 0 < s := by rw [hs_def]; linarith
  have hρeq : ρ = 2 * s := by rw [hs_def]; ring
  have hD1n : 1 ≤ iwDeg ρ := by rw [iwDeg]; omega
  have hD1 : (1 : ℝ) ≤ (iwDeg ρ : ℝ) := by exact_mod_cast hD1n
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set A : ℝ := 2 * (iwDeg ρ : ℝ) * (Real.log 2 + s) + (iwDeg ρ : ℝ) ^ 2 with hA_def
  have hApos : 0 < A := by
    rw [hA_def]
    have hsq : 1 ≤ (iwDeg ρ : ℝ) ^ 2 := one_le_pow₀ hD1
    have hprod : 0 < 2 * (iwDeg ρ : ℝ) * (Real.log 2 + s) := by positivity
    linarith
  obtain ⟨C, hC3, hC⟩ := exists_log_le_rpow (2 * A) s (by positivity) hs
  refine ⟨C, by linarith, ?_⟩
  intro N hN q hq
  have hN3 : (3 : ℝ) ≤ N := le_trans hC3 hN
  have hN3n : 3 ≤ N := by exact_mod_cast hN3
  have hN1n : 1 ≤ N := by omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1n
  have hN0 : (0 : ℝ) < N := by linarith
  have hL1 : 1 ≤ Real.log N := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (le_trans (le_of_lt Real.exp_one_lt_three) hN3)
    rwa [Real.log_exp] at h
  have hS1 : 1 ≤ (N : ℝ) ^ s := by
    have h := Real.rpow_le_rpow zero_le_one hN1 hs.le
    rwa [Real.one_rpow] at h
  have hSpos : 0 < (N : ℝ) ^ s := Real.rpow_pos_of_pos hN0 s
  have hkey : 2 * A * Real.log N ≤ (N : ℝ) ^ s := hC N hN
  -- split `q = Q * w`
  rw [iwPN, Finset.mem_biUnion] at hq
  obtain ⟨Q, hQ, hq⟩ := hq
  rw [Finset.mem_image] at hq
  obtain ⟨w, hw, rfl⟩ := hq
  rw [Nat.cast_mul]
  have hQle : (Q : ℝ) ≤ (iwQ0 ρ N : ℝ) := by exact_mod_cast Nat.divisor_le hQ
  have hQ0 : (iwQ0 ρ N : ℝ) ≤ (2 * (N : ℝ) ^ s) ^ (iwN0 ρ N * iwDeg ρ) := by
    have hfac : (((iwN0 ρ N).factorial : ℕ) : ℝ) ≤ ((iwN0 ρ N : ℕ) : ℝ) ^ (iwN0 ρ N) := by
      rw [← Nat.cast_pow]
      exact_mod_cast Nat.factorial_le_pow (iwN0 ρ N)
    have hN0r : ((iwN0 ρ N : ℕ) : ℝ) ≤ 2 * (N : ℝ) ^ s := by
      rw [iwN0]
      push_cast
      have h := Nat.floor_le (show (0 : ℝ) ≤ (N : ℝ) ^ s by positivity)
      linarith
    calc (iwQ0 ρ N : ℝ) = (((iwN0 ρ N).factorial : ℕ) : ℝ) ^ (iwDeg ρ) := by
          rw [iwQ0, Nat.cast_pow]
      _ ≤ (((iwN0 ρ N : ℕ) : ℝ) ^ (iwN0 ρ N)) ^ (iwDeg ρ) :=
          pow_le_pow_left₀ (by positivity) hfac _
      _ = ((iwN0 ρ N : ℕ) : ℝ) ^ (iwN0 ρ N * iwDeg ρ) := by rw [pow_mul]
      _ ≤ (2 * (N : ℝ) ^ s) ^ (iwN0 ρ N * iwDeg ρ) := pow_le_pow_left₀ (by positivity) hN0r _
  have hwle : (w : ℝ) ≤ (N : ℝ) ^ (iwDeg ρ * iwDeg ρ) := by
    rw [Finset.mem_union] at hw
    rcases hw with hw | hw
    · have hV : ∀ p ∈ iwPrimeSet (iwN0 ρ N) N, p ≤ N := by
        intro p hp
        rw [iwPrimeSet, Finset.mem_filter, Finset.mem_Icc] at hp
        exact hp.1.2
      have hnat := iwPi_le (D := iwDeg ρ) (V := iwPrimeSet (iwN0 ρ N) N) hV hN1n hw
      calc (w : ℝ) ≤ ((N ^ (iwDeg ρ * iwDeg ρ) : ℕ) : ℝ) := by exact_mod_cast hnat
        _ = (N : ℝ) ^ (iwDeg ρ * iwDeg ρ) := by rw [Nat.cast_pow]
    · rw [Finset.mem_singleton] at hw
      rw [hw]
      norm_num
      exact one_le_pow₀ hN1
  have hSsq : (N : ℝ) ^ ρ = ((N : ℝ) ^ s) ^ 2 := by
    rw [hρeq, show (2 : ℝ) * s = s * 2 from by ring, Real.rpow_mul hN0.le]
    exact Real.rpow_natCast _ 2
  have hmain : (2 * (N : ℝ) ^ s) ^ (iwN0 ρ N * iwDeg ρ) *
        (N : ℝ) ^ (iwDeg ρ * iwDeg ρ) ≤ Real.exp ((N : ℝ) ^ ρ / 2) := by
    rw [hSsq, ← Real.log_le_iff_le_exp (by positivity)]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
      Nat.cast_mul, Nat.cast_mul]
    have hlog2S : Real.log (2 * (N : ℝ) ^ s) = Real.log 2 + s * Real.log N := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hSpos), Real.log_rpow hN0 s]
    rw [hlog2S]
    have hL0 : 0 ≤ Real.log N := le_trans zero_le_one hL1
    have hc1 : ((iwN0 ρ N : ℝ) * (iwDeg ρ : ℝ)) * (Real.log 2 + s * Real.log N)
        ≤ (2 * (N : ℝ) ^ s * (iwDeg ρ : ℝ)) * ((Real.log 2 + s) * Real.log N) := by
      have h1 : (iwN0 ρ N : ℝ) * (iwDeg ρ : ℝ) ≤ 2 * (N : ℝ) ^ s * (iwDeg ρ : ℝ) := by
        have hN0r : ((iwN0 ρ N : ℕ) : ℝ) ≤ 2 * (N : ℝ) ^ s := by
          rw [iwN0]
          push_cast
          have h := Nat.floor_le (show (0 : ℝ) ≤ (N : ℝ) ^ s by positivity)
          linarith
        exact mul_le_mul_of_nonneg_right hN0r (by positivity)
      have h2 : Real.log 2 + s * Real.log N ≤ (Real.log 2 + s) * Real.log N := by
        nlinarith [hL1, hlog2.le, hs.le]
      have h3 : 0 ≤ Real.log 2 + s * Real.log N := by positivity
      exact mul_le_mul h1 h2 h3 (by positivity)
    have hc2 : ((iwDeg ρ : ℝ) * (iwDeg ρ : ℝ)) * Real.log N
        ≤ ((iwDeg ρ : ℝ) * (iwDeg ρ : ℝ) * (N : ℝ) ^ s) * Real.log N := by
      have hDn : 0 ≤ (iwDeg ρ : ℝ) * (iwDeg ρ : ℝ) := by positivity
      have h1 : (iwDeg ρ : ℝ) * (iwDeg ρ : ℝ) ≤ (iwDeg ρ : ℝ) * (iwDeg ρ : ℝ) * (N : ℝ) ^ s := by
        simpa using mul_le_mul_of_nonneg_left hS1 hDn
      exact mul_le_mul_of_nonneg_right h1 hL0
    have hsum : ((iwN0 ρ N : ℝ) * (iwDeg ρ : ℝ)) * (Real.log 2 + s * Real.log N)
          + ((iwDeg ρ : ℝ) * (iwDeg ρ : ℝ)) * Real.log N
        ≤ A * (N : ℝ) ^ s * Real.log N := by
      have h := add_le_add hc1 hc2
      have hA : (2 * (N : ℝ) ^ s * (iwDeg ρ : ℝ)) * ((Real.log 2 + s) * Real.log N)
            + ((iwDeg ρ : ℝ) * (iwDeg ρ : ℝ) * (N : ℝ) ^ s) * Real.log N
          = A * (N : ℝ) ^ s * Real.log N := by
        rw [hA_def]; ring
      linarith [h, hA]
    have hfin : A * (N : ℝ) ^ s * Real.log N ≤ ((N : ℝ) ^ s) ^ 2 / 2 := by
      have h := mul_le_mul_of_nonneg_right hkey (le_of_lt hSpos)
      have e1 : 2 * A * Real.log N * (N : ℝ) ^ s = 2 * (A * (N : ℝ) ^ s * Real.log N) := by ring
      have e2 : (N : ℝ) ^ s * (N : ℝ) ^ s = ((N : ℝ) ^ s) ^ 2 := by ring
      rw [e1, e2] at h
      linarith
    linarith [hsum, hfin]
  have hprod : (Q : ℝ) * (w : ℝ) ≤
      (2 * (N : ℝ) ^ s) ^ (iwN0 ρ N * iwDeg ρ) * (N : ℝ) ^ (iwDeg ρ * iwDeg ρ) :=
    mul_le_mul (hQle.trans hQ0) hwle (by positivity) (by positivity)
  exact hprod.trans hmain

end Work.BourgainPlan.IonescuWainger
