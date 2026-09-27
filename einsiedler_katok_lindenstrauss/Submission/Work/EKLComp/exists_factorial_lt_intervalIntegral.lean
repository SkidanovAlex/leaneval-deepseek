import Mathlib

/-!
# A rational (of the form `m / n!`) at which an interval integral beats `α · s`

This file proves `Work.EKLComp.exists_factorial_lt_intervalIntegral`:

If `g : ℝ → ℝ`, `T > 0`, `α > 0` and `α * T < ∫ τ in 0..T, g τ`, then there are naturals
`n, m` with `m > 0` and `α * (m / n!) < ∫ τ in 0..(m/n!), g τ`.

The proof rests on two facts.

* `tail_integral_small`: for an interval-integrable `g` the integral of `|g|` over a shrinking
  right end `(s, T]` tends to `0` as `s → T⁻`. This is the absolute continuity of the indefinite
  integral; it is obtained here from `MeasureTheory.tendsto_setIntegral_of_antitone`.
* `factorial_frac_btwn`: the numbers `m / n!` are dense, in the strong form that they meet every
  interval `(s, T)` with `0 ≤ s < T`.

The formalisation is *junk-value safe*: for a non-integrable function `∫ τ in a..b, g τ = 0`
(`intervalIntegral.integral_undef`), so a strictly positive value of the integral already forces
interval integrability, which is the only hypothesis the two facts above need.
-/

open MeasureTheory Filter Topology
open scoped ENNReal Interval

namespace Work.EKLComp

/-- **Absolute continuity of the indefinite integral, right end.**
If `g` is interval integrable on `[0, T]` and `T > 0`, then for every `η > 0` there is `s` with
`0 < s < T` and `∫ x in s..T, |g x| < η`. -/
lemma tail_integral_small {g : ℝ → ℝ} {T η : ℝ} (hT : 0 < T) (hη : 0 < η)
    (hint : IntervalIntegrable g volume 0 T) :
    ∃ s : ℝ, 0 < s ∧ s < T ∧ ∫ x in s..T, |g x| < η := by
  have habs : IntervalIntegrable (fun x => |g x|) volume 0 T := hint.abs
  have habs' : IntegrableOn (fun x => |g x|) (Set.uIoc 0 T) volume := intervalIntegrable_iff.mp habs
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / T)
  have hNpos : 0 < N := by
    have hpos : (0:ℝ) < 1/T := by positivity
    exact_mod_cast (lt_trans hpos hN)
  have hNR : (0:ℝ) < (N:ℝ) := by exact_mod_cast hNpos
  have hNT : (1:ℝ) < (N:ℝ) * T := by rw [div_lt_iff₀ hT] at hN; linarith
  have hIN : (1:ℝ) / (N:ℝ) < T := by rw [div_lt_iff₀ hNR]; nlinarith [hNT]
  have hsmall : (1:ℝ) / ((N:ℝ)+1) < T := by
    have := one_div_lt_one_div_of_lt hNR (show (N:ℝ) < (N:ℝ)+1 by linarith)
    linarith
  have hNpos' : 0 < T - 1 / ((N:ℝ)+1) := by linarith
  set S : ℕ → Set ℝ := fun k => Set.Ioc (T - 1 / ((k:ℝ)+1)) T with hS
  have hsm : ∀ k, MeasurableSet (S k) := fun k => by simp only [hS]; exact measurableSet_Ioc
  have hanti : Antitone S := by
    intro i j hij x hx
    simp only [hS] at hx ⊢
    have hij' : (i:ℝ) ≤ (j:ℝ) := by exact_mod_cast hij
    refine ⟨lt_of_le_of_lt ?_ hx.1, hx.2⟩
    have h1 : (1:ℝ) / ((j:ℝ)+1) ≤ 1 / ((i:ℝ)+1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  have hfi : ∃ k, IntegrableOn (fun x => |g x|) (S k) volume := by
    refine ⟨N, habs'.mono_set ?_⟩
    intro x hx
    simp only [hS] at hx
    rw [Set.uIoc_of_le hT.le]
    exact ⟨lt_of_lt_of_le hNpos' (le_of_lt hx.1), hx.2⟩
  have htube := tendsto_setIntegral_of_antitone (f := fun x => |g x|) hsm hanti hfi
  have hInter : (⋂ k, S k) = {T} := by
    ext x; constructor
    · intro hx
      rw [Set.mem_singleton_iff]
      have hxk : ∀ k, x ∈ S k := fun k => by rw [Set.mem_iInter] at hx; exact hx k
      have hxT : x ≤ T := by have := hxk 0; simp only [hS] at this; exact this.2
      have hTx : T ≤ x := by
        by_contra hc
        have hxT' : x < T := not_le.mp hc
        have hpos : 0 < T - x := by linarith
        obtain ⟨n, hn⟩ := exists_nat_gt (1 / (T - x))
        have hnpos : 0 < n := by
          have h1 : (0:ℝ) < 1/(T-x) := by positivity
          exact_mod_cast (lt_trans h1 hn)
        have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hnpos
        have hnlt : (1:ℝ)/(n:ℝ) < T - x := by
          rw [div_lt_iff₀ hpos] at hn
          rw [div_lt_iff₀ hnR]; linarith
        have hxk' : T - 1 / ((n:ℝ)+1) < x := by
          have := hxk n; simp only [hS] at this; exact this.1
        have hlt2 : (1:ℝ)/((n:ℝ)+1) ≤ 1/(n:ℝ) :=
          one_div_le_one_div_of_le hnR (by linarith)
        linarith
      linarith
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx, Set.mem_iInter]
      intro k
      simp only [hS]
      have hk : (0:ℝ) < 1 / ((k:ℝ)+1) := by positivity
      exact ⟨by linarith, le_refl T⟩
  have hlim : (∫ x in ⋂ k, S k, |g x|) = 0 := by
    rw [hInter, MeasureTheory.integral_singleton, Measure.real_def, MeasureTheory.measure_singleton]
    simp
  have htube' : Tendsto (fun k : ℕ => ∫ x in S k, |g x|) atTop (𝓝 0) := by
    rw [hlim] at htube; exact htube
  have hFG : ∀ k : ℕ, ∫ x in S k, |g x| = ∫ x in (T - 1 / ((k:ℝ)+1))..T, |g x| := by
    intro k
    simp only [hS]
    have hk : (0:ℝ) < 1 / ((k:ℝ)+1) := by positivity
    exact (intervalIntegral.integral_of_le (by linarith)).symm
  have htube'' : Tendsto (fun k : ℕ => ∫ x in (T - 1 / ((k:ℝ)+1))..T, |g x|) atTop (𝓝 0) :=
    Tendsto.congr' (Filter.Eventually.of_forall (fun k => hFG k)) htube'
  have hev : ∀ᶠ k : ℕ in atTop, ∫ x in (T - 1 / ((k:ℝ)+1))..T, |g x| < η :=
    htube''.eventually (eventually_lt_nhds hη)
  obtain ⟨k, hkb, hkg⟩ : ∃ k : ℕ, (∫ x in (T - 1 / ((k:ℝ)+1))..T, |g x| < η) ∧ N ≤ k :=
    (hev.and (eventually_ge_atTop N)).exists
  refine ⟨T - 1 / ((k:ℝ)+1), ?_, ?_, hkb⟩
  · have hkR : ((N:ℝ)+1) ≤ ((k:ℝ)+1) := by
      have : (N:ℝ) ≤ (k:ℝ) := by exact_mod_cast hkg
      linarith
    have h1 : (1:ℝ) / ((k:ℝ)+1) ≤ 1 / ((N:ℝ)+1) := one_div_le_one_div_of_le (by positivity) hkR
    linarith
  · have hk : (0:ℝ) < 1 / ((k:ℝ)+1) := by positivity
    linarith

/-- **Density of the numbers `m / n!`.**
For reals `0 ≤ s < T` there are `n, m : ℕ` with `0 < m` and `s < m / n! < T`. -/
lemma factorial_frac_btwn {s T : ℝ} (hs : 0 ≤ s) (hsT : s < T) :
    ∃ n m : ℕ, 0 < m ∧ s < (m:ℝ)/(n.factorial:ℝ) ∧ (m:ℝ)/(n.factorial:ℝ) < T := by
  have hpos : 0 < T - s := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / (T - s))
  have hnle : (1:ℝ) / (T - s) < (n.factorial : ℝ) := by
    have : (n : ℝ) ≤ (n.factorial : ℝ) := by exact_mod_cast Nat.self_le_factorial n
    linarith
  have h1 : 1 < (T - s) * (n.factorial : ℝ) := by
    rw [div_lt_iff₀ hpos] at hnle
    linarith
  refine ⟨n, ⌊s * (n.factorial : ℝ)⌋₊ + 1, by positivity, ?_, ?_⟩
  · rw [lt_div_iff₀ (by positivity : (0:ℝ) < (n.factorial:ℝ))]
    push_cast
    have := Nat.lt_floor_add_one (s * (n.factorial : ℝ))
    linarith
  · rw [div_lt_iff₀ (by positivity : (0:ℝ) < (n.factorial:ℝ))]
    push_cast
    have hle := Nat.floor_le (by positivity : (0:ℝ) ≤ s * (n.factorial:ℝ))
    nlinarith [h1]

/-- If `α * T < ∫ τ in 0..T, g τ` with `T > 0`, `α > 0`, then some rational of the form
`m / n!` (`m > 0`) satisfies the same strict inequality. -/
theorem exists_factorial_lt_intervalIntegral {g : ℝ → ℝ} {α T : ℝ} (hT : 0 < T) (hα : 0 < α)
    (h : α * T < ∫ τ in (0:ℝ)..T, g τ) :
    ∃ n m : ℕ, 0 < m ∧ α * ((m : ℝ) / (n.factorial : ℝ)) <
      ∫ τ in (0:ℝ)..((m : ℝ) / (n.factorial : ℝ)), g τ := by
  have hint : IntervalIntegrable g volume 0 T := by
    by_contra hc
    rw [intervalIntegral.integral_undef hc] at h
    nlinarith [mul_pos hα hT]
  have hc0 : 0 < (∫ τ in (0:ℝ)..T, g τ) - α * T := by linarith
  obtain ⟨s, hs0, hsT, htail⟩ := tail_integral_small hT hc0 hint
  obtain ⟨n, m, hm0, hsq, hqT⟩ := factorial_frac_btwn hs0.le hsT
  set q : ℝ := (m:ℝ)/(n.factorial:ℝ) with hqdef
  have hq0 : 0 < q := by rw [hqdef]; positivity
  have hsq' : s ≤ q := by rw [hqdef]; exact le_of_lt hsq
  have hqsT : q ≤ T := by rw [hqdef]; exact le_of_lt hqT
  have htail_q : ∫ x in q..T, |g x| < (∫ τ in (0:ℝ)..T, g τ) - α * T := by
    have habs : IntervalIntegrable (fun x => |g x|) volume s T :=
      (hint.abs).mono_set (by
        rw [Set.uIcc_of_le (le_of_lt hsT), Set.uIcc_of_le hT.le]
        exact Set.Icc_subset_Icc hs0.le le_rfl)
    have hmono := intervalIntegral.integral_mono_interval (f := fun x => |g x|) (μ := volume)
        hsq' hqsT le_rfl
        (Filter.Eventually.of_forall (fun x => abs_nonneg (g x))) habs
    exact lt_of_le_of_lt hmono htail
  have hqTint : IntervalIntegrable g volume q T :=
    hint.mono_set (by
      rw [Set.uIcc_of_le hqsT, Set.uIcc_of_le hT.le]
      exact Set.Icc_subset_Icc hq0.le le_rfl)
  have h0qint : IntervalIntegrable g volume 0 q :=
    hint.mono_set (by
      rw [Set.uIcc_of_le hq0.le, Set.uIcc_of_le hT.le]
      exact Set.Icc_subset_Icc le_rfl hqsT)
  have hadd := intervalIntegral.integral_add_adjacent_intervals h0qint hqTint
  have hgt : α * q < ∫ x in (0:ℝ)..q, g x := by
    have hc' : ∫ x in q..T, g x < (∫ τ in (0:ℝ)..T, g τ) - α * T :=
      lt_of_le_of_lt
        (le_trans (le_abs_self _) (intervalIntegral.abs_integral_le_integral_abs hqsT)) htail_q
    have hαq : α * q < α * T := mul_lt_mul_of_pos_left hqT hα
    nlinarith [hadd]
  refine ⟨n, m, hm0, ?_⟩
  rw [← hqdef]
  exact hgt

end Work.EKLComp
