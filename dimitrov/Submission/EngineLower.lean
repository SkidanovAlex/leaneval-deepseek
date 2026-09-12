import Mathlib

/-!
# Engine L: Fekete-root limsup ≤ Chebyshev-root limsup (sequence level)

Pure real analysis over `ℕ`.  Given two positive sequences `t, m : ℕ → ℝ`
(interpret `t k` = Chebyshev number at size `k`, `m k` = Fekete number at
size `k`) satisfying for every `j ≥ 1`:

* `hDL1` : `m (j+1) ≤ (j+1) * t j * m j`  (the "DL1" finitary comparison);
* `hm1`  : `m 1 = 1`;
* bounds: the root sequences
  `A n := (t (n+1))^(1/(n+1))` and `B n := (m (n+1))^(2/((n+1)*n))`
  are bounded above by positive constants `UA`, `UB`,

PROVE:

    limsup_n B n ≤ limsup_n A n

i.e. `fekete_root_le_chebyshev_root` at the level of abstract sequences.

The proof is developed through the following helper lemmas:

* `dl1_log_diff` — the finitary comparison in logarithmic form;
* `log_m_le_bound` — telescoping over `k = 1..N`;
* `sum_log_le`, `sum_range_id_add_one` — elementary sum bounds;
* `log_t_eq`, `mul_sum_logt` — rewriting `Σ log (t (x+1))` as a weighted
  mean of `log (chebRoot t x)`;
* `sum_w_logA_le` — the head/tail split at the limsup-threshold `J`;
* `fekete_bound_log` — the master finitary bound
  `log (feketeRoot m N) ≤ log γ + o(1)`;
* asymptotic `tendsto` lemmas `tendsto_err` etc.
-/

noncomputable section

open scoped Real Topology BigOperators
open Filter

namespace Submission.EngineLower

/-- `A n = (t (n+1)) ^ (1/(n+1))` — the Chebyshev root number of size `n+1`. -/
private def chebRoot (t : ℕ → ℝ) (n : ℕ) : ℝ := t (n + 1) ^ (1 / ((n : ℝ) + 1))

/-- `B n = (m (n+1)) ^ (2/((n+1)*n))` — the Fekete root number of size `n+1`. -/
private def feketeRoot (m : ℕ → ℝ) (n : ℕ) : ℝ := m (n + 1) ^ (2 / (((n : ℝ) + 1) * (n : ℝ)))

/-- From `m (x+2) ≤ (x+2) * t (x+1) * m (x+1)` and positivity, the logarithmic
difference form. -/
private lemma dl1_log_diff {t m : ℕ → ℝ} (ht0 : ∀ j : ℕ, 1 ≤ j → 0 < t j)
    (hm0 : ∀ j : ℕ, 1 ≤ j → 0 < m j)
    (hDL1 : ∀ j : ℕ, 1 ≤ j → m (j + 1) ≤ (j + 1 : ℝ) * t j * m j) (x : ℕ) :
    Real.log (m (x + 2)) - Real.log (m (x + 1)) ≤ Real.log ((x : ℝ) + 2) + Real.log (t (x + 1)) := by
  have hx1 : 1 ≤ x + 1 := by omega
  have ht : 0 < t (x + 1) := ht0 (x + 1) hx1
  have hm1 : 0 < m (x + 1) := hm0 (x + 1) hx1
  have hm2 : 0 < m (x + 2) := hm0 (x + 2) (by omega)
  have h := hDL1 (x + 1) hx1
  have hcast : (↑(x + 1) : ℝ) + 1 = (x : ℝ) + 2 := by
    rw [Nat.cast_add]; ring_nf
  rw [hcast] at h
  have hdiv : m (x + 2) / m (x + 1) ≤ ((x : ℝ) + 2) * t (x + 1) := by
    exact (div_le_iff₀ hm1).2 h
  have hlogle := Real.log_le_log (div_pos hm2 hm1) hdiv
  have hlogdiv : Real.log (m (x + 2) / m (x + 1)) = Real.log (m (x + 2)) - Real.log (m (x + 1)) :=
    Real.log_div (ne_of_gt hm2) (ne_of_gt hm1)
  have hpos2 : 0 < (x : ℝ) + 2 := by positivity
  have hlogmul : Real.log (((x : ℝ) + 2) * t (x + 1)) = Real.log ((x : ℝ) + 2) + Real.log (t (x + 1)) :=
    Real.log_mul (ne_of_gt hpos2) (ne_of_gt ht)
  rw [hlogdiv, hlogmul] at hlogle
  exact hlogle

/-- Telescoping the DL1 logarithmic inequalities:
`log (m (N+1)) ≤ Σ_{x<N} log (x+2) + Σ_{x<N} log (t (x+1))`. -/
private lemma log_m_le_bound {t m : ℕ → ℝ} (ht0 : ∀ j : ℕ, 1 ≤ j → 0 < t j)
    (hm0 : ∀ j : ℕ, 1 ≤ j → 0 < m j)
    (hm1 : m 1 = 1)
    (hDL1 : ∀ j : ℕ, 1 ≤ j → m (j + 1) ≤ (j + 1 : ℝ) * t j * m j) (N : ℕ) :
    Real.log (m (N + 1)) ≤ (∑ x ∈ Finset.range N, Real.log ((x : ℝ) + 2)) +
      (∑ x ∈ Finset.range N, Real.log (t (x + 1))) := by
  have htel : (∑ x ∈ Finset.range N, (Real.log (m (x + 2)) - Real.log (m (x + 1)))) =
      Real.log (m (N + 1)) - Real.log (m 1) := by
    simpa using (Finset.sum_range_sub (fun y : ℕ => Real.log (m (y + 1))) N)
  have hsum := Finset.sum_le_sum (s := Finset.range N) (fun x hx => dl1_log_diff (t := t) (m := m) ht0 hm0 hDL1 x)
  rw [htel] at hsum
  have hlogm1 : Real.log (m 1) = 0 := by rw [hm1, Real.log_one]
  rw [hlogm1] at hsum
  rw [Finset.sum_add_distrib] at hsum
  simpa using hsum

/-- `Σ_{x<N} (x+1) = N (N+1) / 2` in reals. -/
private lemma sum_range_id_add_one (N : ℕ) :
    (∑ x ∈ Finset.range N, ((x : ℝ) + 1)) = (N : ℝ) * ((N : ℝ) + 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      rw [Nat.cast_add]
      ring_nf

/-- For `N ≥ 1` the weights `2 (x+1)/((N+1) N)` sum to one. -/
private lemma weight_sum_eq_one (N : ℕ) (hN : 1 ≤ N) :
    (2 / (((N : ℝ) + 1) * (N : ℝ))) * (∑ x ∈ Finset.range N, ((x : ℝ) + 1)) = 1 := by
  rw [sum_range_id_add_one]
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℕ) < 1) hN))
  field_simp [hN0]

/-- Crude bound on the factorial part: `Σ_{x<N} log (x+2) ≤ N log (N+1)`. -/
private lemma sum_log_le (N : ℕ) :
    (∑ x ∈ Finset.range N, Real.log ((x : ℝ) + 2)) ≤ (N : ℝ) * Real.log ((N : ℝ) + 1) := by
  by_cases hN : N = 0
  · subst N; simp
  · have hle : ∀ x ∈ Finset.range N, Real.log ((x : ℝ) + 2) ≤ Real.log ((N : ℝ) + 1) := by
      intro x hx
      have hxlt : x < N := Finset.mem_range.mp hx
      apply Real.log_le_log
      · positivity
      · have hn : x + 2 ≤ N + 1 := by omega
        exact_mod_cast hn
    have hsum := Finset.sum_le_sum (s := Finset.range N) hle
    have hc : (∑ x ∈ Finset.range N, Real.log ((N : ℝ) + 1)) = (N : ℝ) * Real.log ((N : ℝ) + 1) := by
      rw [Finset.sum_const]
      simp [nsmul_eq_mul]
    simpa [hc] using hsum

/-- `log (t (x+1)) = (x+1) * log (A x)` with `A x = (t (x+1))^(1/(x+1))`. -/
private lemma log_t_eq (t : ℕ → ℝ) (ht0 : ∀ j : ℕ, 1 ≤ j → 0 < t j) (x : ℕ) :
    Real.log (t (x + 1)) = ((x : ℝ) + 1) * Real.log (chebRoot t x) := by
  have hx1 : 1 ≤ x + 1 := by omega
  have ht : 0 < t (x + 1) := ht0 (x + 1) hx1
  have hlr := Real.log_rpow ht (1 / ((x : ℝ) + 1))
  have hxne : (x : ℝ) + 1 ≠ 0 := by positivity
  have h1 : Real.log (t (x + 1)) = ((x : ℝ) + 1) * ((1 / ((x : ℝ) + 1)) * Real.log (t (x + 1))) := by
    field_simp [hxne]
  rw [← hlr] at h1
  exact h1

/-- Reparametrisation of the `t`-logarithm sum as a weighted mean of `log A`. -/
private lemma mul_sum_logt {t : ℕ → ℝ} (ht0 : ∀ j : ℕ, 1 ≤ j → 0 < t j) (N : ℕ) :
    (2 / (((N : ℝ) + 1) * (N : ℝ))) * (∑ x ∈ Finset.range N, Real.log (t (x + 1)))
      = (∑ x ∈ Finset.range N, ((2 / (((N : ℝ) + 1) * (N : ℝ))) * ((x : ℝ) + 1)) * Real.log (chebRoot t x)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [log_t_eq (t := t) ht0 x]
  ring

/-- Weighted mean bound: with non-negative weights `w`, the weighted average
of `log A` is at most `log γ` plus a head-correction whose coefficient is the
`w`-mass of the indices `< J` (all of which are bounded by `UA`). -/
private lemma sum_w_logA_le {A : ℕ → ℝ} {UA γ : ℝ} {J : ℕ}
    (hApos : ∀ n : ℕ, 0 < A n)
    (hbdA : ∀ n : ℕ, A n ≤ UA)
    (hAγ : ∀ n : ℕ, J ≤ n → A n < γ)
    (w : ℕ → ℝ) (hw : ∀ x : ℕ, 0 ≤ w x)
    (N : ℕ) :
    (∑ x ∈ Finset.range N, w x * Real.log (A x))
      ≤ (∑ x ∈ Finset.range N, w x) * Real.log γ
        + (∑ x ∈ Finset.range J, w x) * |Real.log UA - Real.log γ| := by
  let D : ℝ := |Real.log UA - Real.log γ|
  have hD : 0 ≤ D := abs_nonneg _
  let head : Finset ℕ := (Finset.range N).filter (fun x => ¬ J ≤ x)
  let tail : Finset ℕ := (Finset.range N).filter (fun x => J ≤ x)
  have hsplit : (∑ x ∈ Finset.range N, w x * Real.log (A x))
      = (∑ x ∈ head, w x * Real.log (A x)) + (∑ x ∈ tail, w x * Real.log (A x)) := by
    dsimp [head, tail]
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.range N) (p := fun x : ℕ => J ≤ x)
      (f := fun x : ℕ => w x * Real.log (A x))]
    ac_rfl
  have hsub_union : (∑ x ∈ Finset.range N, w x) = (∑ x ∈ head, w x) + (∑ x ∈ tail, w x) := by
    dsimp [head, tail]
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.range N) (p := fun x : ℕ => J ≤ x)
      (f := fun x : ℕ => w x)]
    ac_rfl
  have hhead : (∑ x ∈ head, w x * Real.log (A x)) ≤ (∑ x ∈ head, w x) * (Real.log γ + D) := by
    have hper : ∀ x ∈ head, w x * Real.log (A x) ≤ w x * (Real.log γ + D) := by
      intro x hx
      have hw0 : 0 ≤ w x := hw x
      have hA0 : 0 < A x := hApos x
      have hxJ : x < J := (not_le.mp (Finset.mem_filter.mp hx).2)
      have hltUA : Real.log (A x) ≤ Real.log UA := Real.log_le_log hA0 (hbdA x)
      have hDle : Real.log UA ≤ Real.log γ + D := by
        have hsub : Real.log UA - Real.log γ ≤ D := by
          dsimp [D]
          exact le_abs_self _
        linarith
      have hb : Real.log (A x) ≤ Real.log γ + D := le_trans hltUA hDle
      exact mul_le_mul_of_nonneg_left hb hw0
    have hs := Finset.sum_le_sum (s := head) hper
    rwa [← Finset.sum_mul (s := head) (f := w) (a := Real.log γ + D)] at hs
  have htail : (∑ x ∈ tail, w x * Real.log (A x)) ≤ (∑ x ∈ tail, w x) * Real.log γ := by
    have hper : ∀ x ∈ tail, w x * Real.log (A x) ≤ w x * Real.log γ := by
      intro x hx
      have hw0 : 0 ≤ w x := hw x
      have hA0 : 0 < A x := hApos x
      have hxJ : J ≤ x := (Finset.mem_filter.mp hx).2
      have hlt : Real.log (A x) < Real.log γ := Real.log_lt_log hA0 (hAγ x hxJ)
      exact mul_le_mul_of_nonneg_left (le_of_lt hlt) hw0
    have hs := Finset.sum_le_sum (s := tail) hper
    rwa [← Finset.sum_mul (s := tail) (f := w) (a := Real.log γ)] at hs
  have hle1 : (∑ x ∈ Finset.range N, w x * Real.log (A x))
      ≤ (∑ x ∈ head, w x) * (Real.log γ + D) + (∑ x ∈ tail, w x) * Real.log γ := by
    rw [hsplit]
    exact add_le_add hhead htail
  have hsubset : head ⊆ Finset.range J := by
    intro x hx
    exact Finset.mem_range.mpr (not_le.mp (Finset.mem_filter.mp hx).2)
  have hheadle : (∑ x ∈ head, w x) ≤ (∑ x ∈ Finset.range J, w x) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun i hi hnot => hw i)
  have hfin : (∑ x ∈ head, w x) * (Real.log γ + D) + (∑ x ∈ tail, w x) * Real.log γ
      ≤ (∑ x ∈ Finset.range N, w x) * Real.log γ + (∑ x ∈ Finset.range J, w x) * D := by
    have hsub' : (∑ x ∈ head, w x) + (∑ x ∈ tail, w x) = (∑ x ∈ Finset.range N, w x) := hsub_union.symm
    have hring : (∑ x ∈ head, w x) * (Real.log γ + D) + (∑ x ∈ tail, w x) * Real.log γ
        = (∑ x ∈ Finset.range N, w x) * Real.log γ + (∑ x ∈ head, w x) * D := by
      rw [← hsub']
      ring
    rw [hring]
    exact add_le_add_right (mul_le_mul_of_nonneg_right hheadle hD) _
  exact le_trans hle1 hfin

/-- The master finitary bound: for `N ≥ 1`, `log (B N) ≤ log γ + o(1)` where
the `o(1)` is `2 log(N+1)/(N+1) + |log UA - log γ|·J(J+1)/((N+1)N)`. -/
private lemma fekete_bound_log {t m : ℕ → ℝ} (ht0 : ∀ j : ℕ, 1 ≤ j → 0 < t j)
    (hm0 : ∀ j : ℕ, 1 ≤ j → 0 < m j)
    (hm1 : m 1 = 1)
    (hDL1 : ∀ j : ℕ, 1 ≤ j → m (j + 1) ≤ (j + 1 : ℝ) * t j * m j)
    {UA γ : ℝ} {J : ℕ}
    (hbdA : ∀ n : ℕ, chebRoot t n ≤ UA)
    (hAγ : ∀ n : ℕ, J ≤ n → chebRoot t n < γ)
    (N : ℕ) (hN : 1 ≤ N) :
    Real.log (feketeRoot m N)
      ≤ Real.log γ + 2 * Real.log ((N : ℝ) + 1) / ((N : ℝ) + 1)
        + |Real.log UA - Real.log γ| * ((J : ℝ) * ((J : ℝ) + 1)) / (((N : ℝ) + 1) * (N : ℝ)) := by
  let cN : ℝ := 2 / (((N : ℝ) + 1) * (N : ℝ))
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hN)
  have hden : 0 < ((N : ℝ) + 1) * (N : ℝ) := by positivity
  have hcN : 0 < cN := by
    dsimp [cN]
    exact div_pos (by norm_num) hden
  have hw : ∀ x : ℕ, 0 ≤ cN * ((x : ℝ) + 1) := fun x => mul_nonneg (le_of_lt hcN) (by positivity)
  have hApos : ∀ n : ℕ, 0 < chebRoot t n := by
    intro n
    have ht : 0 < t (n + 1) := ht0 (n + 1) (by omega)
    dsimp [chebRoot]
    exact Real.rpow_pos_of_pos ht _
  have hlm := log_m_le_bound (t := t) (m := m) ht0 hm0 hm1 hDL1 N
  have hlr : Real.log (feketeRoot m N) = cN * Real.log (m (N + 1)) := by
    dsimp [feketeRoot, cN]
    rw [Real.log_rpow (hm0 (N + 1) (by omega))]
  have hlmul : cN * Real.log (m (N + 1)) ≤ cN * ((∑ x ∈ Finset.range N, Real.log ((x : ℝ) + 2)) +
      (∑ x ∈ Finset.range N, Real.log (t (x + 1)))) := by
    exact mul_le_mul_of_nonneg_left hlm (le_of_lt hcN)
  have hsplitmul : cN * ((∑ x ∈ Finset.range N, Real.log ((x : ℝ) + 2)) +
      (∑ x ∈ Finset.range N, Real.log (t (x + 1))))
      = cN * (∑ x ∈ Finset.range N, Real.log ((x : ℝ) + 2)) +
        cN * (∑ x ∈ Finset.range N, Real.log (t (x + 1))) := by ring
  have hterm1 : cN * (∑ x ∈ Finset.range N, Real.log ((x : ℝ) + 2)) ≤
      2 * Real.log ((N : ℝ) + 1) / ((N : ℝ) + 1) := by
    have hs := sum_log_le N
    have hle := mul_le_mul_of_nonneg_left hs (le_of_lt hcN)
    have hcalc : cN * ((N : ℝ) * Real.log ((N : ℝ) + 1)) = 2 * Real.log ((N : ℝ) + 1) / ((N : ℝ) + 1) := by
      dsimp [cN]
      field_simp [ne_of_gt hNpos]
    calc
      cN * (∑ x ∈ Finset.range N, Real.log ((x : ℝ) + 2)) ≤ cN * ((N : ℝ) * Real.log ((N : ℝ) + 1)) := hle
      _ = 2 * Real.log ((N : ℝ) + 1) / ((N : ℝ) + 1) := hcalc
  have hmul2 : cN * (∑ x ∈ Finset.range N, Real.log (t (x + 1))) ≤ Real.log γ
      + |Real.log UA - Real.log γ| * ((J : ℝ) * ((J : ℝ) + 1)) / (((N : ℝ) + 1) * (N : ℝ)) := by
    have hwsum := sum_w_logA_le (A := chebRoot t) (hApos := hApos) (hbdA := hbdA)
      (hAγ := hAγ) (w := fun x => cN * ((x : ℝ) + 1)) (hw := hw) N
    have hreparam := mul_sum_logt (t := t) ht0 N
    rw [← hreparam] at hwsum
    have hsumw1 : (∑ x ∈ Finset.range N, cN * ((x : ℝ) + 1)) = 1 := by
      calc
        (∑ x ∈ Finset.range N, cN * ((x : ℝ) + 1)) = cN * (∑ x ∈ Finset.range N, ((x : ℝ) + 1)) := by
          rw [← Finset.mul_sum]
        _ = cN * ((N : ℝ) * ((N : ℝ) + 1) / 2) := by rw [sum_range_id_add_one]
        _ = 1 := by
          dsimp [cN]
          field_simp [ne_of_gt hNpos]
    have hsumw2 : (∑ x ∈ Finset.range J, cN * ((x : ℝ) + 1))
        = ((J : ℝ) * ((J : ℝ) + 1)) / (((N : ℝ) + 1) * (N : ℝ)) := by
      calc
        (∑ x ∈ Finset.range J, cN * ((x : ℝ) + 1)) = cN * (∑ x ∈ Finset.range J, ((x : ℝ) + 1)) := by
          rw [← Finset.mul_sum]
        _ = cN * ((J : ℝ) * ((J : ℝ) + 1) / 2) := by rw [sum_range_id_add_one]
        _ = ((J : ℝ) * ((J : ℝ) + 1)) / (((N : ℝ) + 1) * (N : ℝ)) := by
          dsimp [cN]
          field_simp [ne_of_gt hNpos]
    calc
      cN * (∑ x ∈ Finset.range N, Real.log (t (x + 1)))
          ≤ (∑ x ∈ Finset.range N, cN * ((x : ℝ) + 1)) * Real.log γ
            + (∑ x ∈ Finset.range J, cN * ((x : ℝ) + 1)) * |Real.log UA - Real.log γ| := hwsum
      _ ≤ Real.log γ + |Real.log UA - Real.log γ| * ((J : ℝ) * ((J : ℝ) + 1)) / (((N : ℝ) + 1) * (N : ℝ)) := by
          have hden' : ((N : ℝ) + 1) * (N : ℝ) ≠ 0 := ne_of_gt hden
          rw [hsumw1, hsumw2]
          have heq : (1 : ℝ) * Real.log γ + (((J : ℝ) * ((J : ℝ) + 1)) / (((N : ℝ) + 1) * (N : ℝ)))
                * |Real.log UA - Real.log γ|
              = Real.log γ + |Real.log UA - Real.log γ| * ((J : ℝ) * ((J : ℝ) + 1)) / (((N : ℝ) + 1) * (N : ℝ)) := by
            field_simp [hden']
          rw [heq]
  rw [hlr]
  calc
    cN * Real.log (m (N + 1)) ≤ cN * ((∑ x ∈ Finset.range N, Real.log ((x : ℝ) + 2)) +
        (∑ x ∈ Finset.range N, Real.log (t (x + 1)))) := hlmul
    _ = cN * (∑ x ∈ Finset.range N, Real.log ((x : ℝ) + 2)) +
        cN * (∑ x ∈ Finset.range N, Real.log (t (x + 1))) := hsplitmul
    _ ≤ 2 * Real.log ((N : ℝ) + 1) / ((N : ℝ) + 1)
        + (Real.log γ + |Real.log UA - Real.log γ| * ((J : ℝ) * ((J : ℝ) + 1)) / (((N : ℝ) + 1) * (N : ℝ))) := add_le_add hterm1 hmul2
    _ = Real.log γ + 2 * Real.log ((N : ℝ) + 1) / ((N : ℝ) + 1)
        + |Real.log UA - Real.log γ| * ((J : ℝ) * ((J : ℝ) + 1)) / (((N : ℝ) + 1) * (N : ℝ)) := by
        linarith

/-- `(n:ℝ)+1 → +∞`. -/
private lemma tendsto_nat_add_one_real_atTop :
    Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
  have hc : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  exact Filter.tendsto_atTop_add_const_right atTop (1 : ℝ) hc

/-- `log (n+1) / (n+1) → 0`. -/
private lemma tendsto_log_succ_div_atTop :
    Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  have hbase : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using (Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 1 (by norm_num : (1 : ℝ) ≠ 0))
  exact hbase.comp tendsto_nat_add_one_real_atTop

/-- `(n+1)·n → +∞`. -/
private lemma tendsto_mul_succ_atTop :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) * (n : ℝ)) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  rcases exists_nat_ge b with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hprod : (n : ℝ) ≤ ((n : ℝ) + 1) * (n : ℝ) := by
    nlinarith [sq_nonneg (n : ℝ)]
  exact le_trans (le_trans hN hn') hprod

/-- `C / ((n+1)·n) → 0`. -/
private lemma tendsto_const_div_mul_succ (C : ℝ) :
    Tendsto (fun n : ℕ => C / (((n : ℝ) + 1) * (n : ℝ))) atTop (𝓝 0) := by
  exact Filter.Tendsto.const_div_atTop tendsto_mul_succ_atTop C

/-- `2·log(n+1)/(n+1) + C/((n+1)·n) → 0`. -/
private lemma tendsto_err (C : ℝ) :
    Tendsto (fun n : ℕ => 2 * Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1) + C / (((n : ℝ) + 1) * (n : ℝ)))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => 2 * (Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1))) atTop (𝓝 (0 : ℝ)) := by
    have hc : Tendsto (fun n : ℕ => (2 : ℝ)) atTop (𝓝 (2 : ℝ)) := tendsto_const_nhds
    simpa using (hc.mul tendsto_log_succ_div_atTop)
  have h1 : Tendsto (fun n : ℕ => 2 * Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) := by
    refine Filter.Tendsto.congr' ?_ hlog
    filter_upwards with n
    ring_nf
  simpa using h1.add (tendsto_const_div_mul_succ C)

/-- **Engine L.**  For positive sequences `t, m` with the DL1 comparison
`m (j+1) ≤ (j+1) * t j * m j` (and `m 1 = 1`), the limsup of the Fekete
root numbers is at most the limsup of the Chebyshev root numbers. -/
theorem fekete_root_le_cheb_root_of_positive {t m : ℕ → ℝ}
    (ht0 : ∀ j : ℕ, 1 ≤ j → 0 < t j)
    (hm0 : ∀ j : ℕ, 1 ≤ j → 0 < m j)
    (hm1 : m 1 = 1)
    (hDL1 : ∀ j : ℕ, 1 ≤ j → m (j + 1) ≤ (j + 1 : ℝ) * t j * m j)
    {UA : ℝ} (hUA0 : 0 < UA)
    (hbdA : ∀ n : ℕ, (t (n + 1)) ^ (1 / ((n + 1 : ℝ))) ≤ UA)
    {UB : ℝ} (hUB0 : 0 < UB)
    (hbdB : ∀ n : ℕ, (m (n + 1)) ^ (2 / (((n + 1 : ℝ)) * (n : ℝ))) ≤ UB) :
    Filter.limsup (fun n : ℕ => (m (n + 1)) ^ (2 / (((n + 1 : ℝ)) * (n : ℝ)))) Filter.atTop
      ≤ Filter.limsup (fun n : ℕ => (t (n + 1)) ^ (1 / ((n + 1 : ℝ)))) Filter.atTop := by
  let A : ℕ → ℝ := fun n => chebRoot t n
  let B : ℕ → ℝ := fun n => feketeRoot m n
  change Filter.limsup B Filter.atTop ≤ Filter.limsup A Filter.atTop
  let L : ℝ := Filter.limsup A Filter.atTop
  have hbA : ∀ n : ℕ, A n ≤ UA := by
    intro n
    simpa [A, chebRoot] using hbdA n
  have hbB : ∀ n : ℕ, B n ≤ UB := by
    intro n
    simpa [B, feketeRoot] using hbdB n
  have hA0 : ∀ n : ℕ, 0 < A n := by
    intro n
    dsimp [A]
    exact Real.rpow_pos_of_pos (ht0 (n + 1) (by omega)) _
  have hB0 : ∀ n : ℕ, 0 < B n := by
    intro n
    dsimp [B]
    exact Real.rpow_pos_of_pos (hm0 (n + 1) (by omega)) _
  have hAbu : Filter.IsBoundedUnder (· ≤ ·) atTop A := isBoundedUnder_of ⟨UA, hbA⟩
  have hfr0 : ∃ᶠ n in atTop, (0 : ℝ) ≤ A n := by
    rw [Filter.frequently_atTop]
    intro a
    refine ⟨a, le_rfl, ?_⟩
    exact le_of_lt (hA0 a)
  have hL0 : 0 ≤ L := by
    dsimp [L]
    exact Filter.le_limsup_of_frequently_le hfr0 hAbu
  -- ε-argument: limsup B ≤ L + ε for every ε > 0.
  apply le_of_forall_pos_le_add
  intro ε hε
  let γ : ℝ := L + ε / 2
  have hγpos : 0 < γ := by
    dsimp [γ]
    linarith
  have hγlt : γ < L + ε := by
    dsimp [γ]
    linarith
  have hLγ : Filter.limsup A Filter.atTop < γ := by
    dsimp [γ, L]
    linarith
  have hAev : ∀ᶠ n in atTop, A n < γ := Filter.eventually_lt_of_limsup_lt hLγ hAbu
  rcases Filter.eventually_atTop.mp hAev with ⟨J, hJ⟩
  let C : ℝ := |Real.log UA - Real.log γ| * ((J : ℝ) * ((J : ℝ) + 1))
  let err : ℕ → ℝ := fun n => 2 * Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1) + C / (((n : ℝ) + 1) * (n : ℝ))
  -- (1) eventually: B n ≤ γ * exp (err n)   (for n ≥ 1)
  have hBlarge : ∀ᶠ n in atTop, B n ≤ γ * Real.exp (err n) := by
    refine Filter.eventually_atTop.2 ⟨1, fun n hn => ?_⟩
    have hbnd := fekete_bound_log (t := t) (m := m) ht0 hm0 hm1 hDL1 (hbdA := fun n => hbA n)
      (hAγ := hJ) n hn
    have hmono := Real.exp_monotone hbnd
    have hB0' : 0 < feketeRoot m n := by simpa [B] using hB0 n
    rw [Real.exp_log hB0'] at hmono
    calc
      B n ≤ Real.exp (Real.log γ + 2 * Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1)
          + |Real.log UA - Real.log γ| * ((J : ℝ) * ((J : ℝ) + 1)) / (((n : ℝ) + 1) * (n : ℝ))) := hmono
      _ = γ * Real.exp (2 * Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1)
          + |Real.log UA - Real.log γ| * ((J : ℝ) * ((J : ℝ) + 1)) / (((n : ℝ) + 1) * (n : ℝ))) := by
          rw [add_assoc, Real.exp_add, Real.exp_log hγpos]
      _ = γ * Real.exp (err n) := by
          rfl
  -- (2) err → 0 so γ · exp (err n) < L + ε eventually
  have herr0 : Tendsto err atTop (𝓝 0) := by
    dsimp [err]
    exact tendsto_err C
  have hgamma : Tendsto (fun n : ℕ => γ * Real.exp (err n)) atTop (𝓝 γ) := by
    have hce : ContinuousAt Real.exp 0 := Real.continuous_exp.continuousAt
    have hce' : Tendsto (fun n => Real.exp (err n)) atTop (𝓝 (Real.exp 0)) := hce.tendsto.comp herr0
    have hγc : Tendsto (fun n : ℕ => γ) atTop (𝓝 γ) := tendsto_const_nhds
    simpa using hγc.mul hce'
  have hsmall : ∀ᶠ n in atTop, γ * Real.exp (err n) < L + ε := by
    exact Filter.Tendsto.eventually_lt hgamma (tendsto_const_nhds (x := L + ε)) hγlt
  -- (3) combine
  have hevB : ∀ᶠ n in atTop, B n < L + ε := by
    filter_upwards [hBlarge, hsmall] with n hBle hlt
    exact lt_of_le_of_lt hBle hlt
  have hevBle : ∀ᶠ n in atTop, B n ≤ L + ε := by
    filter_upwards [hevB] with n hn
    exact le_of_lt hn
  have hBcob : Filter.IsCoboundedUnder (· ≤ ·) atTop B := by
    exact Filter.isCoboundedUnder_le_of_le atTop (f := B) (x := 0) (fun n => le_of_lt (hB0 n))
  exact Filter.limsup_le_of_le hBcob hevBle

end Submission.EngineLower
