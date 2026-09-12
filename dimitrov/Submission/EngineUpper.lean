import Mathlib

/-!
# Engine U: Chebyshev-root limsup ≤ Fekete-root limsup (sequence level)

Pure real analysis over `ℕ`.  Given two positive sequences `t, m : ℕ → ℝ`
(interpret `t k` = Chebyshev number at size `k`, `m k` = Fekete number at
size `k`) satisfying for every `j ≥ 1`:

* `hsub` : submultiplicativity `t (a+b) ≤ t a * t b` (`a,b ≥ 1`);
* `hDL2` : `t j * m j ≤ m (j+1)`  (the "DL2" finitary comparison);
* `hm1`  : `m 1 = 1`;
* bounds: the root sequences
  `A n := (t (n+1))^(1/(n+1))` and `B n := (m (n+1))^(2/((n+1)*n))`
  are bounded above by positive constants `UA`, `UB`,

PROVE:

    limsup_n A n ≤ limsup_n B n

## Proof summary

The logarithmic Fekete-type estimate is provided by Mathlib's
`Subadditive.eventually_div_lt_of_div_lt` applied to the subadditive
sequence `logSeq t n := if n = 0 then 0 else log (t n)`
(subadditivity follows from the submultiplicativity of `t`):
for every `k ≥ 1` and `ε > 0`, eventually `A n ≤ (t k)^(1/k) + ε`.
With `L := limsup A` this gives `L ≤ (t k)^(1/k)` for every `k ≥ 1`
(`limsup_root_le_root`).

If `L ≤ 0` then `L ≤ 0 ≤ limsup B` (all `B n` are nonnegative).  If
`0 < L`, taking logarithms: `k · log L ≤ log (t k)` for every `k ≥ 1`.
Telescoping the DL2 comparison `log (t k) ≤ log (m (k+1)) - log (m k)`
over `k = 1, …, N` gives
`log (m (N+1)) ≥ ∑_{k≤N} log (t k) ≥ (∑ k) · log L = N(N+1)/2 · log L`.
Multiplying by the positive weight `2/((N+1)N)` yields
`log (B N) ≥ log L`, i.e. `B N ≥ L` for every `N ≥ 1`; hence
`L ≤ limsup B` (`Filter.le_limsup_of_frequently_le`).
-/

noncomputable section

open scoped Real Topology BigOperators
open Filter

namespace Submission.EngineUpper

/-- The logarithm of a positive sequence, extended by `0` at `0` (where the
submultiplicativity hypothesis does not apply). -/
def logSeq (t : ℕ → ℝ) : ℕ → ℝ := fun n => if n = 0 then 0 else Real.log (t n)

lemma logSeq_eq_log {t : ℕ → ℝ} {n : ℕ} (hn : n ≠ 0) : logSeq t n = Real.log (t n) := by
  simp [logSeq, hn]

/-- `logSeq t` is subadditive when `t` is submultiplicative on `ℕ ≥ 1`. -/
lemma log_subadditive {t : ℕ → ℝ}
    (ht0 : ∀ j : ℕ, 1 ≤ j → 0 < t j)
    (hsub : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → t (a + b) ≤ t a * t b) :
    Subadditive (logSeq t) := by
  intro m n
  by_cases hm0 : m = 0
  · subst m
    simp [logSeq]
  by_cases hn0 : n = 0
  · subst n
    simp [logSeq]
  have hmn1 : 1 ≤ m + n := by omega
  calc
    logSeq t (m + n) = Real.log (t (m + n)) := logSeq_eq_log (by omega)
    _ ≤ Real.log (t m * t n) := Real.log_le_log (ht0 (m + n) hmn1) (hsub m n (by omega) (by omega))
    _ = Real.log (t m) + Real.log (t n) :=
      Real.log_mul (ne_of_gt (ht0 m (by omega))) (ne_of_gt (ht0 n (by omega)))
    _ = logSeq t m + logSeq t n := by
      congr 1 <;> exact (logSeq_eq_log (by omega)).symm

lemma cast_add_one (n : ℕ) : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by
  simp

lemma root_pos {t : ℕ → ℝ} (ht0 : ∀ j : ℕ, 1 ≤ j → 0 < t j) (n : ℕ) :
    0 < (t (n + 1)) ^ (1 / ((n + 1 : ℝ))) := by
  exact Real.rpow_pos_of_pos (ht0 (n + 1) (by omega)) (1 / ((n + 1 : ℝ)))

/-- Fekete-type eventual estimate (upper): for every fixed `k ≥ 1` and
`ε > 0`, eventually `(t (n+1)) ^ (1/(n+1)) < (t k)^(1/k) + ε`. -/
lemma eventually_root_lt {t : ℕ → ℝ}
    (ht0 : ∀ j : ℕ, 1 ≤ j → 0 < t j)
    (hsub : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → t (a + b) ≤ t a * t b)
    (k : ℕ) (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, (t (n + 1)) ^ (1 / ((n + 1 : ℝ))) < (t k) ^ (1 / (k : ℝ)) + ε := by
  let Ak : ℝ := (t k) ^ (1 / (k : ℝ))
  have hAkpos : 0 < Ak := by
    exact Real.rpow_pos_of_pos (ht0 k hk) (1 / (k : ℝ))
  have hkposℝ : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  have hu : Subadditive (logSeq t) := log_subadditive ht0 hsub
  have hlog_eq : Real.log (t k) / (k : ℝ) = Real.log Ak := by
    dsimp [Ak]
    rw [Real.log_rpow (ht0 k hk)]
    field_simp [ne_of_gt hkposℝ]
  have hlt : Real.log Ak < Real.log (Ak + ε) :=
    Real.log_lt_log hAkpos (by linarith)
  have hterm : logSeq t k / (k : ℝ) < Real.log (Ak + ε) := by
    rw [logSeq_eq_log (by omega : k ≠ 0)]
    rw [hlog_eq]
    exact hlt
  have hev_p : ∀ᶠ p in atTop, logSeq t p / (p : ℝ) < Real.log (Ak + ε) := by
    exact hu.eventually_div_lt_of_div_lt (by omega : k ≠ 0) hterm
  have hev : ∀ᶠ n in atTop,
      logSeq t (n + 1) / ((n + 1 : ℝ)) < Real.log (Ak + ε) := by
    rcases (Filter.eventually_atTop.1 hev_p) with ⟨N, hN⟩
    refine Filter.eventually_atTop.2 ⟨N, ?_⟩
    intro n hnN
    have hp : logSeq t (n + 1) / (((n + 1 : ℕ) : ℝ)) < Real.log (Ak + ε) := hN (n + 1) (by omega)
    simpa [cast_add_one] using hp
  refine hev.mono ?_
  intro n hn
  have hn1 : 1 ≤ n + 1 := by omega
  have hAn_pos : 0 < (t (n + 1)) ^ (1 / ((n + 1 : ℝ))) := root_pos ht0 n
  have hlogSeq : logSeq t (n + 1) = Real.log (t (n + 1)) := logSeq_eq_log (by omega)
  have hlogA : Real.log ((t (n + 1)) ^ (1 / ((n + 1 : ℝ)))) =
      Real.log (t (n + 1)) / ((n + 1 : ℝ)) := by
    rw [Real.log_rpow (ht0 (n + 1) hn1)]
    field_simp [show ((n + 1 : ℕ) : ℝ) ≠ 0 by positivity]
  have hloglt : Real.log ((t (n + 1)) ^ (1 / ((n + 1 : ℝ)))) < Real.log (Ak + ε) := by
    rw [hlogA]
    simpa [hlogSeq] using hn
  have hlt : (t (n + 1)) ^ (1 / ((n + 1 : ℝ))) < Ak + ε := by
    have hAkεpos : 0 < Ak + ε := by linarith
    exact (Real.log_lt_log_iff hAn_pos hAkεpos).mp hloglt
  simpa [Ak] using hlt

/-- The limsup of the `t`-roots is no larger than any single root
`(t k)^(1/k)` (`k ≥ 1`): the Fekete (submultiplicative) estimate. -/
lemma limsup_root_le_root {t : ℕ → ℝ}
    (ht0 : ∀ j : ℕ, 1 ≤ j → 0 < t j)
    (hsub : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → t (a + b) ≤ t a * t b)
    (k : ℕ) (hk : 1 ≤ k) :
    Filter.limsup (fun n : ℕ => (t (n + 1)) ^ (1 / ((n + 1 : ℝ)))) Filter.atTop ≤ (t k) ^ (1 / (k : ℝ)) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  apply Filter.limsup_le_of_le
  · apply Filter.isCoboundedUnder_le_of_le atTop
    intro n
    exact le_of_lt (root_pos ht0 n)
  · exact (eventually_root_lt ht0 hsub k hk hε).mono (fun n h => le_of_lt h)

/-- Telescoping the DL2 comparison over `k = 1, …, N`:
`∑_{k=1}^{N} log (t k) ≤ log (m (N+1))` (using `m 1 = 1`). -/
lemma log_m_ge_sum_log_t {t m : ℕ → ℝ}
    (ht0 : ∀ j : ℕ, 1 ≤ j → 0 < t j) (hm0 : ∀ j : ℕ, 1 ≤ j → 0 < m j) (hm1 : m 1 = 1)
    (hDL2 : ∀ j : ℕ, 1 ≤ j → t j * m j ≤ m (j + 1)) (N : ℕ) :
    (∑ i ∈ Finset.range N, Real.log (t (i + 1))) ≤ Real.log (m (N + 1)) := by
  have hterm : ∀ i : ℕ, Real.log (t (i + 1)) ≤ Real.log (m (i + 2)) - Real.log (m (i + 1)) := by
    intro i
    have ht : 0 < t (i + 1) := ht0 (i + 1) (by omega)
    have hm1pos : 0 < m (i + 1) := hm0 (i + 1) (by omega)
    have hineq : t (i + 1) * m (i + 1) ≤ m (i + 2) := hDL2 (i + 1) (by omega)
    have hlogmul : Real.log (t (i + 1) * m (i + 1)) ≤ Real.log (m (i + 2)) :=
      Real.log_le_log (mul_pos ht hm1pos) hineq
    have hlogmul' : Real.log (t (i + 1)) + Real.log (m (i + 1)) ≤ Real.log (m (i + 2)) := by
      simpa [Real.log_mul (ne_of_gt ht) (ne_of_gt hm1pos)] using hlogmul
    linarith
  calc
    (∑ i ∈ Finset.range N, Real.log (t (i + 1)))
        ≤ ∑ i ∈ Finset.range N, (Real.log (m (i + 2)) - Real.log (m (i + 1))) := by
          exact Finset.sum_le_sum (fun i hi => hterm i)
    _ = Real.log (m (N + 1)) - Real.log (m 1) := by
      rw [Finset.sum_range_sub (fun j : ℕ => Real.log (m (j + 1)))]
    _ = Real.log (m (N + 1)) := by
      rw [hm1, Real.log_one]
      ring

/-- `∑_{i=0}^{N-1} (i+1) = N(N+1)/2`. -/
lemma sum_range_add_one (N : ℕ) :
    (∑ i ∈ Finset.range N, ((i : ℝ) + 1)) = (N : ℝ) * ((N : ℝ) + 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- **Engine U.**  For positive sequences `t, m` with submultiplicative `t`
and the DL2 comparison `t j * m j ≤ m (j+1)` (and `m 1 = 1`), the limsup of
the Chebyshev root numbers is at most the limsup of the Fekete root
numbers. -/
theorem cheb_root_le_fekete_root_of_positive {t m : ℕ → ℝ}
    (ht0 : ∀ j : ℕ, 1 ≤ j → 0 < t j)
    (hm0 : ∀ j : ℕ, 1 ≤ j → 0 < m j)
    (hm1 : m 1 = 1)
    (hsub : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → t (a + b) ≤ t a * t b)
    (hDL2 : ∀ j : ℕ, 1 ≤ j → t j * m j ≤ m (j + 1))
    {UA : ℝ} (hUA0 : 0 < UA)
    (hbdA : ∀ n : ℕ, (t (n + 1)) ^ (1 / ((n + 1 : ℝ))) ≤ UA)
    {UB : ℝ} (hUB0 : 0 < UB)
    (hbdB : ∀ n : ℕ, (m (n + 1)) ^ (2 / (((n + 1 : ℝ)) * (n : ℝ))) ≤ UB) :
    Filter.limsup (fun n : ℕ => (t (n + 1)) ^ (1 / ((n + 1 : ℝ)))) Filter.atTop
      ≤ Filter.limsup (fun n : ℕ => (m (n + 1)) ^ (2 / (((n + 1 : ℝ)) * (n : ℝ)))) Filter.atTop := by
  let A : ℕ → ℝ := fun n => (t (n + 1)) ^ (1 / ((n + 1 : ℝ)))
  let B : ℕ → ℝ := fun n => (m (n + 1)) ^ (2 / (((n + 1 : ℝ)) * (n : ℝ)))
  let L : ℝ := limsup A atTop
  change L ≤ limsup B atTop
  have hApos : ∀ n : ℕ, 0 < A n := by
    intro n
    exact root_pos ht0 n
  have hBpos : ∀ n : ℕ, 0 < B n := by
    intro n
    dsimp [B]
    exact Real.rpow_pos_of_pos (hm0 (n + 1) (by omega)) (2 / (((n + 1 : ℝ)) * (n : ℝ)))
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact Filter.le_limsup_of_frequently_le (f := atTop) (u := A) (a := 0)
      (Filter.Frequently.of_forall (fun n => le_of_lt (hApos n)))
      (Filter.isBoundedUnder_of (f := atTop) ⟨UA, fun n => hbdA n⟩)
  by_cases hLle0 : L ≤ 0
  · have h0_le_lsB : 0 ≤ limsup B atTop := by
      exact Filter.le_limsup_of_frequently_le (f := atTop) (u := B) (a := 0)
        (Filter.Frequently.of_forall (fun n => le_of_lt (hBpos n)))
        (Filter.isBoundedUnder_of (f := atTop) ⟨UB, fun n => hbdB n⟩)
    exact hLle0.trans h0_le_lsB
  · have hLpos : 0 < L := lt_of_not_ge hLle0
    have hstep2 : ∀ k : ℕ, 1 ≤ k → (k : ℝ) * Real.log L ≤ Real.log (t k) := by
      intro k hk
      have hroot : L ≤ (t k) ^ (1 / (k : ℝ)) := by
        simpa [L, A] using limsup_root_le_root ht0 hsub k hk
      have hlog : Real.log L ≤ Real.log ((t k) ^ (1 / (k : ℝ))) :=
        Real.log_le_log hLpos hroot
      have hkpos : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
      have hk0 : (k : ℝ) ≠ 0 := ne_of_gt hkpos
      calc
        (k : ℝ) * Real.log L ≤ (k : ℝ) * ((1 / (k : ℝ)) * Real.log (t k)) := by
          rw [Real.log_rpow (ht0 k hk)] at hlog
          exact mul_le_mul_of_nonneg_left hlog (le_of_lt hkpos)
        _ = Real.log (t k) := by
          rw [← mul_assoc]
          have hkk : (k : ℝ) * (1 / (k : ℝ)) = 1 := by field_simp [hk0]
          rw [hkk, one_mul]
    have hBge_all : ∀ n : ℕ, 1 ≤ n → L ≤ B n := by
      intro n hn
      have hnR : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hn)
      have hfac : 0 < ((n : ℝ) + 1) * (n : ℝ) := mul_pos (by linarith) hnR
      have hw : 0 < 2 / (((n : ℝ) + 1) * (n : ℝ)) := div_pos (by norm_num) hfac
      have htel : (∑ i ∈ Finset.range n, Real.log (t (i + 1))) ≤ Real.log (m (n + 1)) :=
        log_m_ge_sum_log_t ht0 hm0 hm1 hDL2 n
      have hper : ∀ i ∈ Finset.range n, ((i : ℝ) + 1) * Real.log L ≤ Real.log (t (i + 1)) := by
        intro i hi
        simpa [Nat.cast_add] using hstep2 (i + 1) (by omega)
      have hS : (∑ i ∈ Finset.range n, ((i : ℝ) + 1)) * Real.log L ≤
          (∑ i ∈ Finset.range n, Real.log (t (i + 1))) := by
        calc
          (∑ i ∈ Finset.range n, ((i : ℝ) + 1)) * Real.log L
              = ∑ i ∈ Finset.range n, (((i : ℝ) + 1) * Real.log L) := by
                rw [Finset.sum_mul]
          _ ≤ ∑ i ∈ Finset.range n, Real.log (t (i + 1)) := Finset.sum_le_sum hper
      have hwsum : (2 / (((n : ℝ) + 1) * (n : ℝ))) * (∑ i ∈ Finset.range n, ((i : ℝ) + 1)) = 1 := by
        rw [sum_range_add_one]
        field_simp [ne_of_gt hnR, show ((n : ℝ) + 1) ≠ 0 by linarith]
      have hwsum' : (2 / (((n : ℝ) + 1) * (n : ℝ))) *
          ((∑ i ∈ Finset.range n, ((i : ℝ) + 1)) * Real.log L) = Real.log L := by
        rw [← mul_assoc, hwsum, one_mul]
      have hwS : (2 / (((n : ℝ) + 1) * (n : ℝ))) * (∑ i ∈ Finset.range n, Real.log (t (i + 1))) ≤
          (2 / (((n : ℝ) + 1) * (n : ℝ))) * Real.log (m (n + 1)) := by
        exact mul_le_mul_of_nonneg_left htel (le_of_lt hw)
      have hmain : Real.log L ≤ (2 / (((n : ℝ) + 1) * (n : ℝ))) * Real.log (m (n + 1)) := by
        rw [← hwsum']
        exact (mul_le_mul_of_nonneg_left hS (le_of_lt hw)).trans hwS
      have hlogB_eq : Real.log (B n) = (2 / (((n : ℝ) + 1) * (n : ℝ))) * Real.log (m (n + 1)) := by
        dsimp [B]
        rw [Real.log_rpow (hm0 (n + 1) (by omega))]
      have hlogBge : Real.log L ≤ Real.log (B n) := by
        rw [hlogB_eq]
        exact hmain
      exact (Real.log_le_log_iff hLpos (hBpos n)).mp hlogBge
    have hBge_ev : ∀ᶠ n in atTop, L ≤ B n := by
      refine (eventually_ge_atTop 1).mono ?_
      intro n hn
      exact hBge_all n hn
    exact Filter.le_limsup_of_frequently_le (f := atTop) (u := B) (a := L)
      hBge_ev.frequently
      (Filter.isBoundedUnder_of (f := atTop) ⟨UB, fun n => hbdB n⟩)

end Submission.EngineUpper
