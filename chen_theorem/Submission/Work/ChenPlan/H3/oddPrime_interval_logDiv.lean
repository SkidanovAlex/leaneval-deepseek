import Mathlib
import Submission.Work.ChenPlan.H3.mertens_deps

namespace Work.ChenPlan.H3

open Finset

noncomputable section

/-- `Σ_{p ≤ n, p odd prime} log p / (p - 1)`. -/
private def oddCum (n : ℕ) : ℝ :=
  ∑ p ∈ (Nat.primesLE n).filter (fun p : ℕ => 3 ≤ p), Real.log (p : ℝ) / ((p : ℝ) - 1)

private lemma abs_log_le_log_two_of_half_le {x : ℝ} (h1 : 1 / 2 ≤ x) (h2 : x ≤ 1) :
    |Real.log x| ≤ Real.log 2 := by
  have hx : 0 < x := by linarith
  have hle : Real.log x ≤ 0 := by
    have h := Real.log_le_log hx h2
    rwa [Real.log_one] at h
  have hge : -Real.log 2 ≤ Real.log x := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) h1
    have h1' : Real.log ((1 : ℝ) / 2) = -Real.log 2 := by
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
    rwa [h1'] at h
  rw [abs_of_nonpos hle]
  linarith

private lemma abs_log_le_log_two_of_le_two {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 2) :
    |Real.log x| ≤ Real.log 2 := by
  have hx : 0 < x := by linarith
  have hnn : 0 ≤ Real.log x := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1) h1
    rwa [Real.log_one] at h
  rw [abs_of_nonneg hnn]
  exact Real.log_le_log hx h2

private lemma abs_sub_le' (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  have h := abs_sub_le a 0 b
  simpa using h

/-- The ratio `(⌈z⌉ - 1) / z` is within a factor `2` of `1` for `z ≥ 2`. -/
private lemma abs_log_ceilSubOne_div_le (z' : ℝ) (hz : 2 ≤ z') :
    |Real.log (((⌈z'⌉₊ - 1 : ℕ) : ℝ) / z')| ≤ Real.log 2 := by
  have hzpos : 0 < z' := by linarith
  have hc1 : 1 ≤ ⌈z'⌉₊ := Nat.one_le_ceil_iff.mpr hzpos
  have hcast : ((⌈z'⌉₊ - 1 : ℕ) : ℝ) = (⌈z'⌉₊ : ℝ) - 1 := by
    rw [Nat.cast_sub hc1, Nat.cast_one]
  have hc_lt : (⌈z'⌉₊ : ℝ) - 1 < z' := by
    have := Nat.ceil_lt_add_one (le_of_lt hzpos); linarith
  refine abs_log_le_log_two_of_half_le ?_ ?_
  · rw [hcast, le_div_iff₀ hzpos]
    have h := Nat.le_ceil z'
    nlinarith
  · rw [hcast, div_le_iff₀ hzpos]
    linarith

/-- The ratio `w / (⌈w⌉ - 1)` is at most `2` for `w ≥ 2`. -/
private lemma abs_log_div_ceilSubOne_le (w : ℝ) (hw : 2 ≤ w) :
    |Real.log (w / ((⌈w⌉₊ - 1 : ℕ) : ℝ))| ≤ Real.log 2 := by
  have hwpos : 0 < w := by linarith
  have ha1 : 1 ≤ ⌈w⌉₊ := Nat.one_le_ceil_iff.mpr hwpos
  have ha2 : 2 ≤ ⌈w⌉₊ := by
    have hlt : ((1 : ℕ) : ℝ) < w := by
      have : (1 : ℝ) < w := by linarith
      simpa using this
    have h := (Nat.lt_ceil (a := w) (n := 1)).mpr hlt
    omega
  have hcast : ((⌈w⌉₊ - 1 : ℕ) : ℝ) = (⌈w⌉₊ : ℝ) - 1 := by
    rw [Nat.cast_sub ha1, Nat.cast_one]
  have hpos : 0 < (⌈w⌉₊ : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (⌈w⌉₊ : ℝ) := by exact_mod_cast ha2
    linarith
  refine abs_log_le_log_two_of_le_two ?_ ?_
  · rw [hcast, le_div_iff₀ hpos]
    have := Nat.ceil_lt_add_one (le_of_lt hwpos); linarith
  · rw [hcast, div_le_iff₀ hpos]
    have := Nat.le_ceil w; linarith

/-- The cumulative odd-prime sum differs from `log n` by a bounded amount. -/
private lemma oddCum_sub_log_bound :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ, 1 ≤ n → |oddCum n - Real.log (n : ℝ)| ≤ A := by
  obtain ⟨C, hCpos, hC⟩ := Commons.NumberTheory.Mertens.sum_log_div_le_log_sharp
  refine ⟨C + Real.log 2, by positivity, ?_⟩
  intro n hn
  rcases eq_or_lt_of_le hn with h1 | h2
  · subst h1
    have h0 : oddCum 1 = 0 := by
      rw [oddCum]
      apply Finset.sum_eq_zero
      intro p hp
      simp only [Finset.mem_filter, Nat.mem_primesLE] at hp
      exact absurd hp.1.2.two_le (by omega)
    rw [h0, Nat.cast_one, Real.log_one, sub_zero, abs_zero]
    positivity
  · have hn2 : 2 ≤ n := by omega
    have hset : (Nat.primesLE n).filter (fun p : ℕ => 2 ≤ p)
        = insert 2 ((Nat.primesLE n).filter (fun p : ℕ => 3 ≤ p)) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_insert, Nat.mem_primesLE]
      constructor
      · rintro ⟨⟨hpn, hpp⟩, hp2⟩
        rcases eq_or_lt_of_le hp2 with h | h
        · exact Or.inl h.symm
        · exact Or.inr ⟨⟨hpn, hpp⟩, h⟩
      · rintro (h | ⟨⟨hpn, hpp⟩, h3⟩)
        · subst h
          exact ⟨⟨hn2, by norm_num⟩, le_rfl⟩
        · exact ⟨⟨hpn, hpp⟩, le_trans (by norm_num : 2 ≤ 3) h3⟩
    have hS : (∑ p ∈ (Nat.primesLE n).filter (fun p : ℕ => 2 ≤ p),
          Real.log (p : ℝ) / ((p : ℝ) - 1)) = Real.log 2 + oddCum n := by
      rw [oddCum, hset, Finset.sum_insert (by simp)]
      norm_num
    have hmain := hC n hn2
    rw [hS] at hmain
    have hkey : oddCum n - Real.log (n : ℝ)
        = (Real.log 2 + oddCum n - Real.log (n : ℝ)) - Real.log 2 := by ring
    rw [hkey]
    have habs : |(Real.log 2 + oddCum n - Real.log (n : ℝ)) - Real.log 2|
        ≤ |Real.log 2 + oddCum n - Real.log (n : ℝ)| + Real.log 2 := by
      have h1 : (Real.log 2 + oddCum n - Real.log (n : ℝ)) - Real.log 2
          = (Real.log 2 + oddCum n - Real.log (n : ℝ)) + (-(Real.log 2)) := by ring
      rw [h1]
      have h2 := abs_add_le (Real.log 2 + oddCum n - Real.log (n : ℝ)) (-(Real.log 2))
      rwa [abs_neg, abs_of_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))] at h2
    calc |(Real.log 2 + oddCum n - Real.log (n : ℝ)) - Real.log 2|
        ≤ |Real.log 2 + oddCum n - Real.log (n : ℝ)| + Real.log 2 := habs
      _ ≤ C + Real.log 2 := by linarith [hmain]

/-- The primes counted by the target sum are exactly the odd primes in the integer interval
`[⌈w⌉, ⌈z'⌉ - 1]`. -/
private lemma filter_set_eq (Y : ℕ) (w z' : ℝ) (hw : 2 ≤ w) (hwz : w < z') (hzY : z' ≤ (Y : ℝ)) :
    (Commons.NumberTheory.Chen.ChenEight.oddLt Y).filter
        (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z')
      = (Nat.primesLE (⌈z'⌉₊ - 1)).filter (fun p : ℕ => 3 ≤ p ∧ ⌈w⌉₊ ≤ p) := by
  have hzpos : 0 < z' := by linarith
  have hcY : ⌈z'⌉₊ ≤ Y := Nat.ceil_le.mpr hzY
  ext p
  simp only [Commons.NumberTheory.Chen.ChenEight.oddLt, Finset.mem_filter, Finset.mem_range,
    Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hpY, hpp, hp3⟩, hpw, hpz⟩
    have ha : ⌈w⌉₊ ≤ p := Nat.ceil_le.mpr hpw
    have hpc : p ≤ ⌈z'⌉₊ - 1 := by
      have h1 : (p : ℝ) < (⌈z'⌉₊ : ℝ) := lt_of_lt_of_le hpz (Nat.le_ceil z')
      have h2 : p < ⌈z'⌉₊ := by exact_mod_cast h1
      omega
    exact ⟨⟨hpc, hpp⟩, hp3, ha⟩
  · rintro ⟨⟨hpc, hpp⟩, hp3, ha⟩
    have hpw : w ≤ (p : ℝ) := Nat.ceil_le.mp ha
    have hpz : (p : ℝ) < z' := by
      have hmem : 1 ≤ ⌈z'⌉₊ := Nat.ceil_pos.mpr hzpos
      have h3 : ((⌈z'⌉₊ - 1 : ℕ) : ℝ) < z' := by
        rw [Nat.cast_sub hmem, Nat.cast_one]
        have h4 := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ z' by linarith)
        linarith
      exact lt_of_le_of_lt (Nat.cast_le.mpr hpc) h3
    have hpY : p < Y := by omega
    exact ⟨⟨hpY, hpp, hp3⟩, hpw, hpz⟩

theorem oddPrime_interval_logDiv :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (Y : ℕ) (w z' : ℝ), 2 ≤ w → w < z' → z' ≤ (Y : ℝ) →
      |(∑ p ∈ (Commons.NumberTheory.Chen.ChenEight.oddLt Y).filter
          (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z'),
          Real.log (p : ℝ) / ((p : ℝ) - 1)) - Real.log (z' / w)| ≤ K := by
  obtain ⟨A, hA0, hAb⟩ := oddCum_sub_log_bound
  have hlog2nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  refine ⟨2 * A + 2 * Real.log 2 + 1, by linarith, ?_⟩
  intro Y w z' hw hwz hzY
  have hzpos : 0 < z' := by linarith
  have hwpos : 0 < w := by linarith
  have hz2 : 2 ≤ z' := by linarith
  have hc3 : 3 ≤ ⌈z'⌉₊ := by
    have hlt : ((2 : ℕ) : ℝ) < z' := by
      have : (2 : ℝ) < z' := by linarith
      simpa using this
    have h := (Nat.lt_ceil (a := z') (n := 2)).mpr hlt
    omega
  have ha2 : 2 ≤ ⌈w⌉₊ := by
    have hlt : ((1 : ℕ) : ℝ) < w := by
      have : (1 : ℝ) < w := by linarith
      simpa using this
    have h := (Nat.lt_ceil (a := w) (n := 1)).mpr hlt
    omega
  rw [filter_set_eq Y w z' hw hwz hzY]
  by_cases hcase : ⌈w⌉₊ ≤ ⌈z'⌉₊ - 1
  · have hsub : (Nat.primesLE (⌈w⌉₊ - 1)).filter (fun p : ℕ => 3 ≤ p)
        ⊆ (Nat.primesLE (⌈z'⌉₊ - 1)).filter (fun p : ℕ => 3 ≤ p) := by
      intro p hp
      simp only [Finset.mem_filter, Nat.mem_primesLE] at hp ⊢
      exact ⟨⟨by omega, hp.1.2⟩, hp.2⟩
    have hU : (Nat.primesLE (⌈z'⌉₊ - 1)).filter (fun p : ℕ => 3 ≤ p ∧ ⌈w⌉₊ ≤ p)
        = (Nat.primesLE (⌈z'⌉₊ - 1)).filter (fun p : ℕ => 3 ≤ p)
          \ (Nat.primesLE (⌈w⌉₊ - 1)).filter (fun p : ℕ => 3 ≤ p) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_sdiff, Nat.mem_primesLE]
      constructor
      · rintro ⟨⟨hpc, hpp⟩, hp3, ha⟩
        refine ⟨⟨⟨hpc, hpp⟩, hp3⟩, ?_⟩
        intro hmem
        omega
      · rintro ⟨⟨⟨hpc, hpp⟩, hp3⟩, hnot⟩
        refine ⟨⟨hpc, hpp⟩, hp3, ?_⟩
        by_contra hlt
        simp only [not_le] at hlt
        exact hnot ⟨⟨by omega, hpp⟩, hp3⟩
    rw [hU]
    have hsum : (∑ p ∈ (Nat.primesLE (⌈z'⌉₊ - 1)).filter (fun p : ℕ => 3 ≤ p)
                    \ (Nat.primesLE (⌈w⌉₊ - 1)).filter (fun p : ℕ => 3 ≤ p),
                  Real.log (p : ℝ) / ((p : ℝ) - 1))
        = oddCum (⌈z'⌉₊ - 1) - oddCum (⌈w⌉₊ - 1) := by
      have hs := Finset.sum_sdiff
        (s₁ := (Nat.primesLE (⌈w⌉₊ - 1)).filter (fun p : ℕ => 3 ≤ p))
        (s₂ := (Nat.primesLE (⌈z'⌉₊ - 1)).filter (fun p : ℕ => 3 ≤ p))
        (f := fun p : ℕ => Real.log (p : ℝ) / ((p : ℝ) - 1)) hsub
      simp only [oddCum]
      linarith [hs]
    rw [hsum]
    have hA1 : |oddCum (⌈z'⌉₊ - 1) - Real.log (((⌈z'⌉₊ - 1 : ℕ) : ℝ))| ≤ A :=
      hAb (⌈z'⌉₊ - 1) (by omega)
    have hA2 : |oddCum (⌈w⌉₊ - 1) - Real.log (((⌈w⌉₊ - 1 : ℕ) : ℝ))| ≤ A :=
      hAb (⌈w⌉₊ - 1) (by omega)
    have hZl : |Real.log (((⌈z'⌉₊ - 1 : ℕ) : ℝ)) - Real.log (((⌈w⌉₊ - 1 : ℕ) : ℝ))
        - Real.log (z' / w)| ≤ 2 * Real.log 2 := by
      have hS1pos : 0 < (((⌈z'⌉₊ - 1 : ℕ) : ℝ)) := by
        have h : (1 : ℕ) ≤ ⌈z'⌉₊ - 1 := by omega
        have h' : (1 : ℝ) ≤ (((⌈z'⌉₊ - 1 : ℕ) : ℝ)) := by exact_mod_cast h
        linarith
      have hS2pos : 0 < (((⌈w⌉₊ - 1 : ℕ) : ℝ)) := by
        have h : (1 : ℕ) ≤ ⌈w⌉₊ - 1 := by omega
        have h' : (1 : ℝ) ≤ (((⌈w⌉₊ - 1 : ℕ) : ℝ)) := by exact_mod_cast h
        linarith
      have hkey : Real.log (((⌈z'⌉₊ - 1 : ℕ) : ℝ)) - Real.log (((⌈w⌉₊ - 1 : ℕ) : ℝ))
            - Real.log (z' / w)
          = Real.log ((((⌈z'⌉₊ - 1 : ℕ) : ℝ)) / z')
            + Real.log (w / (((⌈w⌉₊ - 1 : ℕ) : ℝ))) := by
        rw [Real.log_div (ne_of_gt hS1pos) (ne_of_gt hzpos),
            Real.log_div (ne_of_gt hwpos) (ne_of_gt hS2pos),
            Real.log_div (ne_of_gt hzpos) (ne_of_gt hwpos)]
        ring
      rw [hkey]
      calc |Real.log ((((⌈z'⌉₊ - 1 : ℕ) : ℝ)) / z')
              + Real.log (w / (((⌈w⌉₊ - 1 : ℕ) : ℝ)))|
          ≤ |Real.log ((((⌈z'⌉₊ - 1 : ℕ) : ℝ)) / z')|
              + |Real.log (w / (((⌈w⌉₊ - 1 : ℕ) : ℝ)))| := abs_add_le _ _
        _ ≤ Real.log 2 + Real.log 2 :=
              add_le_add (abs_log_ceilSubOne_div_le z' hz2) (abs_log_div_ceilSubOne_le w hw)
        _ = 2 * Real.log 2 := by ring
    have hdec : oddCum (⌈z'⌉₊ - 1) - oddCum (⌈w⌉₊ - 1) - Real.log (z' / w)
        = (oddCum (⌈z'⌉₊ - 1) - Real.log (((⌈z'⌉₊ - 1 : ℕ) : ℝ)))
          - (oddCum (⌈w⌉₊ - 1) - Real.log (((⌈w⌉₊ - 1 : ℕ) : ℝ)))
          + (Real.log (((⌈z'⌉₊ - 1 : ℕ) : ℝ)) - Real.log (((⌈w⌉₊ - 1 : ℕ) : ℝ))
              - Real.log (z' / w)) := by ring
    rw [hdec]
    have h3 := abs_sub_le' (oddCum (⌈z'⌉₊ - 1) - Real.log (((⌈z'⌉₊ - 1 : ℕ) : ℝ)))
      (oddCum (⌈w⌉₊ - 1) - Real.log (((⌈w⌉₊ - 1 : ℕ) : ℝ)))
    calc |(oddCum (⌈z'⌉₊ - 1) - Real.log (((⌈z'⌉₊ - 1 : ℕ) : ℝ)))
            - (oddCum (⌈w⌉₊ - 1) - Real.log (((⌈w⌉₊ - 1 : ℕ) : ℝ)))
            + (Real.log (((⌈z'⌉₊ - 1 : ℕ) : ℝ)) - Real.log (((⌈w⌉₊ - 1 : ℕ) : ℝ))
                - Real.log (z' / w))|
        ≤ |(oddCum (⌈z'⌉₊ - 1) - Real.log (((⌈z'⌉₊ - 1 : ℕ) : ℝ)))
            - (oddCum (⌈w⌉₊ - 1) - Real.log (((⌈w⌉₊ - 1 : ℕ) : ℝ)))|
          + |Real.log (((⌈z'⌉₊ - 1 : ℕ) : ℝ)) - Real.log (((⌈w⌉₊ - 1 : ℕ) : ℝ))
              - Real.log (z' / w)| := abs_add_le _ _
      _ ≤ (|oddCum (⌈z'⌉₊ - 1) - Real.log (((⌈z'⌉₊ - 1 : ℕ) : ℝ))|
            + |oddCum (⌈w⌉₊ - 1) - Real.log (((⌈w⌉₊ - 1 : ℕ) : ℝ))|)
          + |Real.log (((⌈z'⌉₊ - 1 : ℕ) : ℝ)) - Real.log (((⌈w⌉₊ - 1 : ℕ) : ℝ))
              - Real.log (z' / w)| := by linarith [h3]
      _ ≤ (A + A) + 2 * Real.log 2 := by linarith [hA1, hA2, hZl]
      _ ≤ 2 * A + 2 * Real.log 2 + 1 := by linarith
  · have hUe : (Nat.primesLE (⌈z'⌉₊ - 1)).filter (fun p : ℕ => 3 ≤ p ∧ ⌈w⌉₊ ≤ p) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro p hp
      simp only [Nat.mem_primesLE] at hp
      rintro ⟨-, ha⟩
      omega
    rw [hUe, Finset.sum_empty, zero_sub, abs_neg]
    have hlog_nonneg : 0 ≤ Real.log (z' / w) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hwpos]
      linarith
    rw [abs_of_nonneg hlog_nonneg]
    have hzw : z' / w ≤ 3 / 2 := by
      have hac : ⌈z'⌉₊ ≤ ⌈w⌉₊ := by omega
      have hzc : z' ≤ (⌈z'⌉₊ : ℝ) := Nat.le_ceil z'
      have haw : (⌈w⌉₊ : ℝ) < w + 1 := Nat.ceil_lt_add_one (le_of_lt hwpos)
      have hlt : z' < w + 1 := by
        calc z' ≤ (⌈z'⌉₊ : ℝ) := hzc
          _ ≤ (⌈w⌉₊ : ℝ) := by exact_mod_cast hac
          _ < w + 1 := haw
      rw [div_le_iff₀ hwpos]
      nlinarith
    have hlogle : Real.log (z' / w) ≤ 1 / 2 := by
      have hpos : 0 < z' / w := div_pos hzpos hwpos
      have := Real.log_le_sub_one_of_pos hpos
      linarith
    linarith

end

end Work.ChenPlan.H3
