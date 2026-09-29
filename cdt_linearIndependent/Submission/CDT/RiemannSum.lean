/-
# Riemann sums of a piecewise Lipschitz function

The main result is `tendsto_riemannSum_of_lipschitz_pieces`: if `f : ℝ → ℝ` is bounded by `L` on
`[0,m]` and `L`-Lipschitz on each of the pieces `[a i, a (i+1)]` (`i < N`, `a 0 = 0`, `a N ≥ m`),
then the Riemann sums converge to the average value:

`(1/d)·Σ_{j=1}^{d} f(m·j/d) → (1/m)·∫_0^m f`.

Proof: the piecewise Lipschitz condition chains across the (finitely many) breakpoints
(`lipschitz_of_pieces_aux`), giving a *global* Lipschitz bound on `[0,m]` (hence continuity and
integrability); then the mesh estimate `abs_riemannSum_sub_integral_le` compares the `j`-th rectangle
`f(m j/d)·(m/d)` with the integral over `[(j-1)m/d, jm/d]`, the error being at most `L(m/d)²`;
summing gives the total error `≤ L·(m/d)·m → 0`.

This is the analytic ingredient of the paper's "horizontal integration" passage (Calegari–Dimitrov–
Tang, §"The cost of an integration"): the added denominators are measured by the Riemann sums of the
model function of Lemma `lcm-2`.
-/
import Mathlib

open Finset MeasureTheory
open scoped BigOperators Topology Interval

theorem continuousOn_of_lipschitz {m L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℝ}
    (hlip : ∀ t ∈ Set.Icc (0:ℝ) m, ∀ u ∈ Set.Icc (0:ℝ) m, |f t - f u| ≤ L * |t - u|) :
    ContinuousOn f (Set.Icc (0:ℝ) m) := by
  intro t₀ ht₀
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  refine ⟨ε / (L + 1), by positivity, fun t ht hdist => ?_⟩
  rw [Real.dist_eq] at hdist ⊢
  have h1 := hlip t ht t₀ ht₀
  have h3 : (L + 1) * |t - t₀| < (L + 1) * (ε / (L + 1)) :=
    mul_lt_mul_of_pos_left hdist (by linarith)
  rw [mul_div_cancel₀ _ (by linarith : (L + 1) ≠ 0)] at h3
  have h2 : L * |t - t₀| ≤ (L + 1) * |t - t₀| := by nlinarith [abs_nonneg (t - t₀)]
  linarith

theorem intervalIntegrable_of_lipschitz {m L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℝ}
    (hlip : ∀ t ∈ Set.Icc (0:ℝ) m, ∀ u ∈ Set.Icc (0:ℝ) m, |f t - f u| ≤ L * |t - u|)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvm : v ≤ m) :
    IntervalIntegrable f volume u v :=
  ((continuousOn_of_lipschitz hL hlip).mono
    (fun x hx => ⟨le_trans hu hx.1, le_trans hx.2 hvm⟩)).intervalIntegrable_of_Icc huv

theorem sum_Icc_one_eq_sum_range {M : Type*} [AddCommMonoid M] (g : ℕ → M) (d : ℕ) :
    (∑ j ∈ Finset.Icc 1 d, g j) = ∑ k ∈ Finset.range d, g (k + 1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega : 1 ≤ d + 1), ih]

theorem abs_riemannSum_sub_integral_le {m L : ℝ} (hm : 0 < m) (hL : 0 ≤ L) {f : ℝ → ℝ}
    (hlip : ∀ t ∈ Set.Icc (0:ℝ) m, ∀ u ∈ Set.Icc (0:ℝ) m, |f t - f u| ≤ L * |t - u|)
    {d : ℕ} (hd : 1 ≤ d) :
    |(∑ j ∈ Finset.Icc 1 d, f (m * (j:ℝ) / (d:ℝ))) * (m / d) - ∫ t in (0:ℝ)..m, f t|
      ≤ L * (m / d) * m := by
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  set Δ := m / d with hΔdef
  have hΔ : 0 < Δ := div_pos hm hd'
  set τ : ℕ → ℝ := fun j => (j : ℝ) * Δ with hτ
  have hτ0 : τ 0 = 0 := by rw [hτ]; simp
  have hτd : τ d = m := by rw [hτ, hΔdef]; field_simp
  have hτmono : ∀ k, τ k ≤ τ (k+1) := by
    intro k; rw [hτ]; push_cast; nlinarith [hΔ]
  have hτmem : ∀ k ≤ d, τ k ∈ Set.Icc (0:ℝ) m := by
    intro k hk
    refine ⟨?_, ?_⟩
    · rw [hτ]; positivity
    · rw [← hτd]
      have h1 : (k:ℝ) ≤ (d:ℝ) := by exact_mod_cast hk
      have h2 : (0:ℝ) < Δ := hΔ
      rw [hτ]
      push_cast
      nlinarith
  have hsam : ∀ j : ℕ, m * (j:ℝ) / (d:ℝ) = τ j := by
    intro j; rw [hτ, hΔdef]; ring
  have hint : ∀ k < d, IntervalIntegrable f volume (τ k) (τ (k+1)) := by
    intro k hk
    exact intervalIntegrable_of_lipschitz hL hlip (by rw [hτ]; positivity) (hτmono k)
      (hτmem (k+1) (by omega)).2
  have hpart : (∑ k ∈ Finset.range d, ∫ t in τ k..τ (k+1), f t) = ∫ t in (0:ℝ)..m, f t := by
    rw [intervalIntegral.sum_integral_adjacent_intervals hint, hτ0, hτd]
  have hlen : ∀ k, τ (k+1) - τ k = Δ := by
    intro k; rw [hτ]; push_cast; ring
  have hconst : ∀ k, (∫ t in τ k..τ (k+1), (f (τ (k+1)) : ℝ)) = f (τ (k+1)) * Δ := by
    intro k; rw [intervalIntegral.integral_const, hlen k, smul_eq_mul]; ring
  have hsum1 : (∑ j ∈ Finset.Icc 1 d, f (τ j)) * Δ
      = ∑ k ∈ Finset.range d, ∫ t in τ k..τ (k+1), (f (τ (k+1))) := by
    rw [sum_Icc_one_eq_sum_range, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => (hconst k).symm
  have hdiff : (∑ j ∈ Finset.Icc 1 d, f (τ j)) * Δ - ∫ t in (0:ℝ)..m, f t
      = ∑ k ∈ Finset.range d, ∫ t in τ k..τ (k+1), (f (τ (k+1)) - f t) := by
    rw [← hpart, hsum1, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hint k (Finset.mem_range.mp hk))]
  have hbound : ∑ k ∈ Finset.range d, |∫ t in τ k..τ (k+1), (f (τ (k+1)) - f t)|
      ≤ ∑ k ∈ Finset.range d, (L * Δ * Δ) := by
    refine Finset.sum_le_sum fun k hk => ?_
    have hk' : k < d := Finset.mem_range.mp hk
    have hkmem : τ (k+1) ∈ Set.Icc (0:ℝ) m := hτmem (k+1) (by omega)
    have hC : ∀ x ∈ Ι (τ k) (τ (k+1)), ‖f (τ (k+1)) - f x‖ ≤ L * Δ := by
      intro x hx
      rw [Set.uIoc_of_le (hτmono k)] at hx
      rw [Real.norm_eq_abs]
      have hx' : x ∈ Set.Icc (τ k) (τ (k+1)) := ⟨le_of_lt hx.1, hx.2⟩
      have hxmem : x ∈ Set.Icc (0:ℝ) m :=
        ⟨le_trans (hτmem k hk'.le).1 hx'.1, le_trans hx'.2 hkmem.2⟩
      have h1 := hlip (τ (k+1)) hkmem x hxmem
      have h2 : |τ (k+1) - x| ≤ Δ := by
        rw [abs_of_nonneg (by linarith [hx'.2]), ← hlen k]
        linarith [hx'.1]
      exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hL)
    have h2 := intervalIntegral.norm_integral_le_of_norm_le_const (a := τ k) (b := τ (k+1))
      (f := fun x => f (τ (k+1)) - f x) (C := L * Δ) hC
    rw [Real.norm_eq_abs] at h2
    have hb : |τ (k+1) - τ k| = Δ := by
      rw [abs_of_nonneg (by rw [hlen k]; linarith), hlen k]
    rw [hb] at h2
    exact h2
  simp only [hsam]
  rw [hdiff]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans hbound ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hΔdef]
  field_simp
  linarith

theorem tendsto_riemannSum_of_lipschitz {m : ℝ} (hm : 0 < m) {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ t ∈ Set.Icc (0:ℝ) m, ∀ u ∈ Set.Icc (0:ℝ) m, |f t - f u| ≤ L * |t - u|) :
    Filter.Tendsto (fun d : ℕ => (∑ j ∈ Finset.Icc 1 d, f (m * (j : ℝ) / (d : ℝ))) / (d : ℝ))
      Filter.atTop (nhds ((∫ t in (0 : ℝ)..m, f t) / m)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  refine ⟨max 1 (⌊m * L / ε⌋₊ + 1), fun d hd => ?_⟩
  have hd1 : 1 ≤ d := le_trans (le_max_left _ _) hd
  have hd' : (0:ℝ) < d := by exact_mod_cast hd1
  have hdle : ⌊m * L / ε⌋₊ + 1 ≤ d := le_trans (le_max_right _ _) hd
  have hlt : m * L / ε < (d : ℝ) := by
    have h1 : m * L / ε < (⌊m * L / ε⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2 : ((⌊m * L / ε⌋₊ + 1 : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdle
    push_cast at h2
    linarith
  have hmL : m * L < ε * d := by
    rw [div_lt_iff₀ hε] at hlt
    linarith
  have hLm : L * (m / d) < ε := by
    rw [show L * (m / d) = L * m / d from by ring, div_lt_iff₀ hd']
    linarith
  have hkey := abs_riemannSum_sub_integral_le hm hL hlip hd1
  have hrewrite : (∑ j ∈ Finset.Icc 1 d, f (m * (j : ℝ) / (d : ℝ))) / (d : ℝ)
      - (∫ t in (0 : ℝ)..m, f t) / m
      = ((∑ j ∈ Finset.Icc 1 d, f (m * (j : ℝ) / (d : ℝ))) * (m / d)
        - ∫ t in (0 : ℝ)..m, f t) / m := by
    rw [div_sub_div _ _ (ne_of_gt hd') (ne_of_gt hm)]
    field_simp
  rw [Real.dist_eq, hrewrite, abs_div, abs_of_pos hm, div_lt_iff₀ hm]
  calc |(∑ j ∈ Finset.Icc 1 d, f (m * (j : ℝ) / (d : ℝ))) * (m / d)
        - ∫ t in (0 : ℝ)..m, f t| ≤ L * (m / d) * m := hkey
    _ < ε * m := by nlinarith [hLm, hm]

theorem abs_sub_le_abs_add (x y z : ℝ) : |x - z| ≤ |x - y| + |y - z| := by
  have h : x - z = (x - y) + (y - z) := by ring
  rw [h]; exact abs_add_le _ _

theorem lipschitz_of_pieces_aux {L : ℝ} (hL : 0 ≤ L) {a : ℕ → ℝ} {N : ℕ}
    (hmono : ∀ i < N, a i < a (i + 1)) (ha0 : a 0 = 0) {f : ℝ → ℝ}
    (hlip : ∀ i < N, ∀ t ∈ Set.Icc (a i) (a (i + 1)), ∀ u ∈ Set.Icc (a i) (a (i + 1)),
      |f t - f u| ≤ L * |t - u|) :
    ∀ n ≤ N, ∀ x y : ℝ, 0 ≤ x → x ≤ y → y ≤ a n → |f x - f y| ≤ L * (y - x) := by
  intro n
  induction n with
  | zero =>
    intro hn x y hx hxy hy
    have hy0 : y ≤ 0 := by rw [ha0] at hy; exact hy
    have hxy0 : x = y := le_antisymm hxy (le_trans hy0 hx)
    rw [hxy0]; simp
  | succ n ih =>
    intro hn x y hx hxy hy
    rcases lt_or_ge y (a n) with h | h
    · exact ih (by omega) x y hx hxy (le_of_lt h)
    · rcases lt_or_ge x (a n) with h2 | h2
      · have hn' : n < N := by omega
        have h1 : |f x - f (a n)| ≤ L * (a n - x) :=
          ih (by omega) x (a n) hx (le_of_lt h2) le_rfl
        have h3 : |f (a n) - f y| ≤ L * (y - a n) := by
          have h5 := hlip n hn' (a n) ⟨le_rfl, le_of_lt (hmono n hn')⟩ y ⟨h, hy⟩
          rwa [abs_of_nonpos (sub_nonpos.mpr h), neg_sub] at h5
        have h4 := abs_sub_le_abs_add (f x) (f (a n)) (f y)
        linarith
      · have hn' : n < N := by omega
        have h1 := hlip n hn' x ⟨h2, le_trans hxy hy⟩ y ⟨le_trans h2 hxy, hy⟩
        rwa [abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub] at h1

theorem tendsto_riemannSum_of_lipschitz_pieces {m : ℝ} (hm : 0 < m) {a : ℕ → ℝ} {N : ℕ}
    (hmono : ∀ i < N, a i < a (i + 1)) (ha0 : a 0 = 0) (hNm : m ≤ a N)
    {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ t ∈ Set.Icc (0:ℝ) m, |f t| ≤ L)
    (hlip : ∀ i < N, ∀ t ∈ Set.Icc (a i) (a (i + 1)), ∀ u ∈ Set.Icc (a i) (a (i + 1)),
      |f t - f u| ≤ L * |t - u|) :
    Filter.Tendsto (fun d : ℕ => (∑ j ∈ Finset.Icc 1 d, f (m * (j : ℝ) / (d : ℝ))) / (d : ℝ))
      Filter.atTop (nhds ((∫ t in (0 : ℝ)..m, f t) / m)) := by
  refine tendsto_riemannSum_of_lipschitz hm hL fun t ht u hu => ?_
  rcases le_total t u with h | h
  · have h1 : |t - u| = u - t := by rw [abs_of_nonpos (sub_nonpos.mpr h), neg_sub]
    have h2 := lipschitz_of_pieces_aux hL hmono ha0 hlip N le_rfl t u ht.1 h (le_trans hu.2 hNm)
    rw [h1]; exact h2
  · have h1 : |t - u| = t - u := abs_of_nonneg (sub_nonneg.mpr h)
    have h2 := lipschitz_of_pieces_aux hL hmono ha0 hlip N le_rfl u t hu.1 h (le_trans ht.2 hNm)
    rw [h1, abs_sub_comm]; exact h2
