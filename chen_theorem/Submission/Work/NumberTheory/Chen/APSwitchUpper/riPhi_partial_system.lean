import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.prof
import Submission.Work.NumberTheory.Chen.APSwitchUpper.profC_intervalIntegrable
import Submission.Work.NumberTheory.Chen.APSwitchUpper.sum_intervalIntegral_eq_integral_uIoc

/-!
# `APSwitchUpper.riPhi_partial_system` — the finite-`N` delay system of the `profC` profiles

For `A_N = Σ_{j < N, j even} profC j` and `B_N = Σ_{j < N, j odd} profC j` the two identities

```
s·A_N(s) = (3−s)·1_{s≤3} + ∫_{max(s−1,2)}^{N+1} B_{N−1}        (s ≥ 2)
s·B_N(s) =                        ∫_{s−1}^{N+1} A_{N−1}        (s ≥ 2)
```

(unordered integrals on the right, so that both sides are nonnegative for `s ≥ 2`).
They are the exact finite-`N` content of the delay recursion defining `profC`, obtained by
(i) the pointwise recursion `s·profC j s = ∫_{max(s−1,2)}^{j+2} profC (j−1)` (even `j ≥ 2`),
resp. `s·profC j s = ∫_{s−1}^{j+2} profC (j−1)` (odd `j`), for `s ≥ 2`;
(ii) the observation that the truncation length `j+2 = (j−1)+3` is the support edge of
`profC (j−1)` (`profC_support`), so that a sum of upper-truncated integrals telescopes into the
integral of the sum.

The telescoping is isolated in the auxiliary lemma
`sum_intervalIntegral_eq_integral_uIoc`, and the interval integrability of `profC` in
`profC_intervalIntegrable`; both are proved in sibling files.
-/

namespace Work.NumberTheory.Chen.APSwitchUpper

open Finset
open scoped BigOperators
open MeasureTheory

noncomputable section

/-- `max s 3 - 1 = max (s - 1) 2`, the change of variable `u = t - 1` applied to the lower
endpoint `max s 3` of the recursion for the even-indexed profiles. -/
lemma profC_max_sub_one (s : ℝ) : max s 3 - 1 = max (s - 1) 2 := by
  rcases le_total s 3 with h | h
  · have h1 : max s 3 = 3 := max_eq_right h
    have h2 : max (s - 1) 2 = 2 := max_eq_right (by linarith)
    rw [h1, h2]; norm_num
  · have h1 : max s 3 = s := max_eq_left h
    have h2 : max (s - 1) 2 = s - 1 := max_eq_left (by linarith)
    rw [h1, h2]

/-- **Even-index recursion** (`j` even, `j ≥ 2`, `s ≥ 2`):
`s·profC j s = ∫_{max(s−1,2)}^{j+2} profC (j−1)`.  The upper limit `j + 2 = (j−1) + 3` is the
support edge of `profC (j−1)`, so the identity holds with both sides `0` beyond it. -/
lemma profC_even_mul_eq {j : ℕ} (hj : j % 2 = 0) (hj2 : 2 ≤ j) {s : ℝ} (hs : 2 ≤ s) :
    s * profC j s = ∫ u in (max (s - 1) 2)..((j : ℝ) + 2), profC (j - 1) u := by
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  have hpar : (n + 1) % 2 = 0 := hj
  rw [profC_succ, if_pos hpar]
  have hsub : (n + 1 - 1) = n := by omega
  have hup : ((n + 1 : ℕ) : ℝ) + 2 = (n : ℝ) + 3 := by push_cast; ring
  rw [hup, hsub]
  by_cases hlt : s < (n : ℝ) + 4
  · rw [if_pos ⟨by linarith, hlt⟩]
    rw [mul_div_cancel₀ _ (by linarith : s ≠ 0)]
    rw [intervalIntegral.integral_comp_sub_right (profC n) 1]
    rw [profC_max_sub_one, show (n : ℝ) + 4 - 1 = (n : ℝ) + 3 by ring]
  · rw [if_neg (fun h => hlt h.2)]
    simp only [mul_zero]
    have hge : (n : ℝ) + 3 ≤ max (s - 1) 2 := by
      have h1 : (n : ℝ) + 3 ≤ s - 1 := by linarith [not_lt.mp hlt]
      exact le_trans h1 (le_max_left _ _)
    have hzero : ∫ u in (max (s - 1) 2)..((n : ℝ) + 3), profC n u = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) (fun x hx => ?_)]
      · simp
      · have hx1 : (n : ℝ) + 3 ≤ x := by
          rw [Set.uIcc_of_ge hge] at hx
          exact hx.1
        exact profC_support n x hx1
    exact hzero.symm

/-- **Odd-index recursion** (`j` odd, `s ≥ 2`): `s·profC j s = ∫_{s−1}^{j+2} profC (j−1)`. -/
lemma profC_odd_mul_eq {j : ℕ} (hj : j % 2 = 1) {s : ℝ} (hs : 2 ≤ s) :
    s * profC j s = ∫ u in (s - 1)..((j : ℝ) + 2), profC (j - 1) u := by
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  have hpar : ¬ ((n + 1) % 2 = 0) := by omega
  rw [profC_succ, if_neg hpar]
  have hsub : (n + 1 - 1) = n := by omega
  have hup : ((n + 1 : ℕ) : ℝ) + 2 = (n : ℝ) + 3 := by push_cast; ring
  rw [hup, hsub]
  by_cases hlt : s < (n : ℝ) + 4
  · rw [if_pos ⟨hs, hlt⟩]
    rw [mul_div_cancel₀ _ (by linarith : s ≠ 0)]
    rw [intervalIntegral.integral_comp_sub_right (profC n) 1]
    rw [show (n : ℝ) + 4 - 1 = (n : ℝ) + 3 by ring]
  · rw [if_neg (fun h => hlt h.2)]
    simp only [mul_zero]
    have hge : (n : ℝ) + 3 ≤ s - 1 := by linarith [not_lt.mp hlt]
    have hzero : ∫ u in (s - 1)..((n : ℝ) + 3), profC n u = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) (fun x hx => ?_)]
      · simp
      · have hx1 : (n : ℝ) + 3 ≤ x := by
          rw [Set.uIcc_of_ge hge] at hx
          exact hx.1
        exact profC_support n x hx1
    exact hzero.symm

/-- The base term: for `s ≥ 2`, `s·profC 0 s = (3−s)·1_{s≤3}`. -/
lemma profC_zero_mul (s : ℝ) (hs : 2 ≤ s) :
    s * profC 0 s = (if s ≤ 3 then 3 - s else 0) := by
  rw [profC_zero]
  by_cases h : s ≤ 3
  · rw [if_pos ⟨by linarith, h⟩, if_pos h]
    field_simp
  · rw [if_neg (fun hc => h hc.2), if_neg h, mul_zero]

theorem riPhi_partial_system :
    (∀ (N : ℕ) (s : ℝ), 2 ≤ s → 1 ≤ N →
        s * (Finset.sum ((Finset.range N).filter (fun j => j % 2 = 0)) (fun j => Work.NumberTheory.Chen.APSwitchUpper.profC j s))
          = (if s ≤ 3 then 3 - s else 0)
            + MeasureTheory.integral (MeasureTheory.volume.restrict (Set.uIoc (max (s - 1) 2) ((N : ℝ) + 1)))
                (fun u => Finset.sum ((Finset.range (N - 1)).filter (fun j => j % 2 = 1)) (fun j => Work.NumberTheory.Chen.APSwitchUpper.profC j u)))
    ∧ (∀ (N : ℕ) (s : ℝ), 2 ≤ s → 1 ≤ N →
        s * (Finset.sum ((Finset.range N).filter (fun j => j % 2 = 1)) (fun j => Work.NumberTheory.Chen.APSwitchUpper.profC j s))
          = MeasureTheory.integral (MeasureTheory.volume.restrict (Set.uIoc (s - 1) ((N : ℝ) + 1)))
              (fun u => Finset.sum ((Finset.range (N - 1)).filter (fun j => j % 2 = 0)) (fun j => Work.NumberTheory.Chen.APSwitchUpper.profC j u))) := by
  constructor
  · intro N s hs hN
    set Sodd : Finset ℕ := (Finset.range (N - 1)).filter (fun i => i % 2 = 1) with hSodd
    have hset : (Finset.range N).filter (fun j => j % 2 = 0)
        = insert 0 (Sodd.image (fun i => i + 1)) := by
      rw [hSodd]
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_image]
      constructor
      · rintro ⟨hjN, hje⟩
        rcases Nat.eq_zero_or_pos j with rfl | hjpos
        · exact Or.inl rfl
        · right
          exact ⟨j - 1, ⟨by omega, by omega⟩, by omega⟩
      · rintro (rfl | ⟨i, ⟨hiN, hio⟩, rfl⟩)
        · exact ⟨by omega, by simp⟩
        · exact ⟨by omega, by omega⟩
    have hnotin : (0:ℕ) ∉ Sodd.image (fun i => i + 1) := by
      rw [Finset.mem_image]
      rintro ⟨i, _, hi⟩
      exact Nat.succ_ne_zero i hi
    have hinj : Set.InjOn (fun i : ℕ => i + 1) (↑Sodd) := by
      intro a _ b _ h
      exact Nat.succ.inj (by simpa using h)
    have hpoint : ∀ i ∈ Sodd, s * profC (i + 1) s
        = ∫ u in (max (s - 1) 2)..((i : ℝ) + 3), profC i u := by
      intro i hi
      rw [hSodd, Finset.mem_filter] at hi
      obtain ⟨-, hio⟩ := hi
      have h1 : (i + 1) % 2 = 0 := by omega
      have h2 : 2 ≤ i + 1 := by omega
      have h3 := profC_even_mul_eq h1 h2 hs
      rw [h3]
      rw [show (((i + 1 : ℕ) : ℝ) + 2) = (i : ℝ) + 3 by push_cast; ring,
        show (i + 1 - 1) = i by omega]
    have hu : ∀ i ∈ Sodd, (fun i : ℕ => (i : ℝ) + 3) i ≤ ((N : ℝ) + 1) := by
      intro i hi
      rw [hSodd, Finset.mem_filter, Finset.mem_range] at hi
      have hle : i + 3 ≤ N + 1 := by omega
      have h2 : ((i : ℝ) + 3) ≤ ((N : ℝ) + 1) := by exact_mod_cast hle
      exact h2
    have hint : ∀ i ∈ Sodd, ∀ p q : ℝ, IntervalIntegrable (profC i) MeasureTheory.volume p q :=
      fun i _ p q => profC_intervalIntegrable i p q
    have hsupp : ∀ i ∈ Sodd, ∀ x : ℝ, (fun i : ℕ => (i : ℝ) + 3) i ≤ x → profC i x = 0 :=
      fun i _ x hx => profC_support i x hx
    rw [hset, Finset.sum_insert hnotin, mul_add, profC_zero_mul s hs,
      Finset.mul_sum, Finset.sum_image hinj]
    rw [Finset.sum_congr rfl hpoint]
    rw [sum_intervalIntegral_eq_integral_uIoc Sodd profC (fun i : ℕ => (i : ℝ) + 3)
          (max (s - 1) 2) ((N : ℝ) + 1) hu hint hsupp]
  · intro N s hs hN
    set Seven : Finset ℕ := (Finset.range (N - 1)).filter (fun i => i % 2 = 0) with hSeven
    have hset : (Finset.range N).filter (fun j => j % 2 = 1)
        = Seven.image (fun i => i + 1) := by
      rw [hSeven]
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hjN, hjo⟩
        exact ⟨j - 1, ⟨by omega, by omega⟩, by omega⟩
      · rintro ⟨i, ⟨hiN, hie⟩, rfl⟩
        exact ⟨by omega, by omega⟩
    have hinj : Set.InjOn (fun i : ℕ => i + 1) (↑Seven) := by
      intro a _ b _ h
      exact Nat.succ.inj (by simpa using h)
    have hpoint : ∀ i ∈ Seven, s * profC (i + 1) s
        = ∫ u in (s - 1)..((i : ℝ) + 3), profC i u := by
      intro i hi
      rw [hSeven, Finset.mem_filter] at hi
      obtain ⟨-, hie⟩ := hi
      have h1 : (i + 1) % 2 = 1 := by omega
      have h3 := profC_odd_mul_eq h1 hs
      rw [h3]
      rw [show (((i + 1 : ℕ) : ℝ) + 2) = (i : ℝ) + 3 by push_cast; ring,
        show (i + 1 - 1) = i by omega]
    have hu : ∀ i ∈ Seven, (fun i : ℕ => (i : ℝ) + 3) i ≤ ((N : ℝ) + 1) := by
      intro i hi
      rw [hSeven, Finset.mem_filter, Finset.mem_range] at hi
      have hle : i + 3 ≤ N + 1 := by omega
      have h2 : ((i : ℝ) + 3) ≤ ((N : ℝ) + 1) := by exact_mod_cast hle
      exact h2
    have hint : ∀ i ∈ Seven, ∀ p q : ℝ, IntervalIntegrable (profC i) MeasureTheory.volume p q :=
      fun i _ p q => profC_intervalIntegrable i p q
    have hsupp : ∀ i ∈ Seven, ∀ x : ℝ, (fun i : ℕ => (i : ℝ) + 3) i ≤ x → profC i x = 0 :=
      fun i _ x hx => profC_support i x hx
    rw [hset, Finset.mul_sum, Finset.sum_image hinj]
    rw [Finset.sum_congr rfl hpoint]
    rw [sum_intervalIntegral_eq_integral_uIoc Seven profC (fun i : ℕ => (i : ℝ) + 3)
          (s - 1) ((N : ℝ) + 1) hu hint hsupp]

end

end Work.NumberTheory.Chen.APSwitchUpper
