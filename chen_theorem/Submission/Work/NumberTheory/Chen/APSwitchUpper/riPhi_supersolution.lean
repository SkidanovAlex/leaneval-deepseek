/-
# `APSwitchUpper.riPhi_supersolution` — the comparison (supersolution) principle for `riPhi`

`riPhi_partial_system` gives, with `A_N = Σ_{j<N, j even} profC j` and `B_N = Σ_{j<N, j odd} profC j`,
for `s ≥ 2` and `N ≥ 1`:

```
s·A_N(s) = (3−s)·1_{s≤3} + ∫_{max(s−1,2)}^{N+1} B_{N−1},      s·B_N(s) = ∫_{s−1}^{N+1} A_{N−1}.
```

Hence, if `U, V ≥ 0` with `profC 0 ≤ U` satisfy the *fixed-point inequalities*

```
(3−s)·1_{s≤3} + ∫_{max(s−1,2)}^{b} V ≤ s·U(s),      ∫_{s−1}^{b} U ≤ s·V(s)      (s ≥ 2, all b),
```

then `A_N ≤ U` and `B_N ≤ V` for every `N`.  Since `Σ_j profC (2j) s` is a series of nonnegative
terms whose partial sums are the `A_N(s)`, this gives `riPhi s ≤ U s`.

This is the tool that turns an explicit majorant `U` into a rigorous bound on `riPhi`.
-/
import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.prof
import Submission.Work.NumberTheory.Chen.APSwitchUpper.profC_intervalIntegrable
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhi_partial_system

open Finset MeasureTheory
open scoped BigOperators

namespace Work.NumberTheory.Chen.APSwitchUpper

noncomputable section

/-- `A_N s = Σ_{j<N, j even} profC j s`. -/
def apart (N : ℕ) (s : ℝ) : ℝ :=
  ∑ j ∈ (Finset.range N).filter (fun j => j % 2 = 0), profC j s

/-- `B_N s = Σ_{j<N, j odd} profC j s`. -/
def bpart (N : ℕ) (s : ℝ) : ℝ :=
  ∑ j ∈ (Finset.range N).filter (fun j => j % 2 = 1), profC j s

theorem apart_nonneg (N : ℕ) (s : ℝ) : 0 ≤ apart N s :=
  Finset.sum_nonneg (fun j _ => profC_nonneg j s)

theorem bpart_nonneg (N : ℕ) (s : ℝ) : 0 ≤ bpart N s :=
  Finset.sum_nonneg (fun j _ => profC_nonneg j s)

theorem intervalIntegrable_finset_sum {ι : Type*} (a b : ℝ) (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, IntervalIntegrable (f i) volume a b) :
    IntervalIntegrable (fun x => ∑ i ∈ s, f i x) volume a b := by
  classical
  induction s using Finset.induction with
  | empty => simp [intervalIntegrable_const]
  | insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (hf i (Finset.mem_insert_self i s)).add
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem apart_intervalIntegrable (N : ℕ) (a b : ℝ) :
    IntervalIntegrable (apart N) volume a b := by
  unfold apart
  exact intervalIntegrable_finset_sum a b _ _ (fun j _ => profC_intervalIntegrable j a b)

theorem bpart_intervalIntegrable (N : ℕ) (a b : ℝ) :
    IntervalIntegrable (bpart N) volume a b := by
  unfold bpart
  exact intervalIntegrable_finset_sum a b _ _ (fun j _ => profC_intervalIntegrable j a b)

/-- The partial system in `apart`/`bpart` notation, as an interval integral. -/
theorem apart_mul_eq {N : ℕ} {s : ℝ} (hs : 2 ≤ s) (hN : 1 ≤ N) (hsN : s ≤ (N : ℝ) + 2) :
    s * apart N s = (if s ≤ 3 then 3 - s else 0)
      + ∫ u in (max (s - 1) 2)..((N : ℝ) + 1), bpart (N - 1) u := by
  have hle : max (s - 1) 2 ≤ (N : ℝ) + 1 := by
    refine max_le (by linarith) ?_
    exact_mod_cast (by omega : 2 ≤ N + 1)
  have h := riPhi_partial_system.1 N s hs hN
  rw [show apart N s = ∑ j ∈ (Finset.range N).filter (fun j => j % 2 = 0), profC j s
      from rfl]
  rw [show bpart (N - 1) = fun u => ∑ j ∈ (Finset.range (N - 1)).filter (fun j => j % 2 = 1),
      profC j u from rfl]
  rw [h]
  rw [Set.uIoc_of_le hle, intervalIntegral.integral_of_le hle]

theorem bpart_mul_eq {N : ℕ} {s : ℝ} (hs : 2 ≤ s) (hN : 1 ≤ N) (hsN : s ≤ (N : ℝ) + 2) :
    s * bpart N s = ∫ u in (s - 1)..((N : ℝ) + 1), apart (N - 1) u := by
  have hle : s - 1 ≤ (N : ℝ) + 1 := by linarith
  have h := riPhi_partial_system.2 N s hs hN
  rw [show bpart N s = ∑ j ∈ (Finset.range N).filter (fun j => j % 2 = 1), profC j s
      from rfl]
  rw [show apart (N - 1) = fun u => ∑ j ∈ (Finset.range (N - 1)).filter (fun j => j % 2 = 0),
      profC j u from rfl]
  rw [h]
  rw [Set.uIoc_of_le hle, intervalIntegral.integral_of_le hle]

/-- `A_N s = 0` for `s ≥ N + 2`. -/
theorem apart_eq_zero {N : ℕ} {s : ℝ} (hs : (N : ℝ) + 2 ≤ s) : apart N s = 0 := by
  refine Finset.sum_eq_zero (fun j hj => ?_)
  rw [Finset.mem_filter, Finset.mem_range] at hj
  exact profC_support j s (by
    have : (j : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast (by omega : j + 1 ≤ N)
    linarith)

theorem bpart_eq_zero {N : ℕ} {s : ℝ} (hs : (N : ℝ) + 2 ≤ s) : bpart N s = 0 := by
  refine Finset.sum_eq_zero (fun j hj => ?_)
  rw [Finset.mem_filter, Finset.mem_range] at hj
  exact profC_support j s (by
    have : (j : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast (by omega : j + 1 ≤ N)
    linarith)

/-- **Clamping at an even index `k+1 ≥ 2`.**  For `1 ≤ t ≤ 3` the recursion's lower limit
`max t 3` equals `3`, so `t · profC (k+1) t = 3 · profC (k+1) 3`. -/
theorem profC_clamp_even_succ {k : ℕ} (hk : (k + 1) % 2 = 0) (hk1 : 1 ≤ k) {t : ℝ}
    (h1 : 1 ≤ t) (h3 : t ≤ 3) :
    t * profC (k + 1) t = 3 * profC (k + 1) 3 := by
  have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have ht : 1 ≤ t ∧ t < (k : ℝ) + 4 := ⟨h1, by linarith⟩
  have h3c : (1 : ℝ) ≤ 3 ∧ (3 : ℝ) < (k : ℝ) + 4 := ⟨by norm_num, by linarith⟩
  have hmain : profC (k + 1) t
      = (∫ u in max t 3..((k : ℝ) + 4), profC k (u - 1)) / t := by
    rw [profC_succ, if_pos hk, if_pos ht]
  have h3main : profC (k + 1) 3
      = (∫ u in max 3 3..((k : ℝ) + 4), profC k (u - 1)) / 3 := by
    rw [profC_succ, if_pos hk, if_pos h3c]
  rw [hmain, h3main, max_eq_right h3, max_self,
    mul_div_cancel₀ _ (by linarith : t ≠ 0),
    mul_div_cancel₀ _ (by norm_num : (3 : ℝ) ≠ 0)]

/-- **The pointwise clamping identity at an even index**, `j = 0` singled out. -/
theorem profC_clamp_even (j : ℕ) (hj : j % 2 = 0) {t : ℝ} (h1 : 1 ≤ t) (h3 : t ≤ 3) :
    t * profC j t = 3 * profC j 3 + (if j = 0 then 3 - t else 0) := by
  rcases eq_or_ne j 0 with rfl | hj0
  · rw [if_pos rfl]
    rw [profC_zero, if_pos ⟨h1, h3⟩, profC_zero,
      if_pos ⟨by norm_num, le_refl (3 : ℝ)⟩]
    rw [show (3 : ℝ) - 3 = 0 by norm_num, zero_div, mul_zero, zero_add]
    exact mul_div_cancel₀ _ (by linarith : t ≠ 0)
  · have hdvd : 2 ∣ j := Nat.dvd_of_mod_eq_zero hj
    have hj2 : 2 ≤ j := Nat.le_of_dvd (Nat.pos_of_ne_zero hj0) hdvd
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hj0
    rw [hk] at hj ⊢
    rw [if_neg (by omega : ¬ (k + 1 = 0)), add_zero]
    exact profC_clamp_even_succ hj (by omega) h1 h3

/-- `A_N` satisfies the clamping identity on `[1,3]` (for `1 ≤ N`); this supplies the
`s ∈ [1,2)` range that the supersolution induction needs. -/
theorem apart_linear {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (h1 : 1 ≤ t) (h3 : t ≤ 3) :
    t * apart N t - (3 - t) = 3 * apart N 3 := by
  have hmem0 : 0 ∈ (Finset.range N).filter (fun j => j % 2 = 0) := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by norm_num⟩
  have key : t * apart N t = 3 * apart N 3 + (3 - t) := by
    have hA : t * apart N t
        = ∑ j ∈ (Finset.range N).filter (fun j => j % 2 = 0), t * profC j t := by
      unfold apart
      rw [Finset.mul_sum]
    have hB : 3 * apart N 3
        = ∑ j ∈ (Finset.range N).filter (fun j => j % 2 = 0), 3 * profC j 3 := by
      unfold apart
      rw [Finset.mul_sum]
    have hsum : (∑ j ∈ (Finset.range N).filter (fun j => j % 2 = 0), t * profC j t)
        = ∑ j ∈ (Finset.range N).filter (fun j => j % 2 = 0),
            (3 * profC j 3 + (if j = 0 then 3 - t else 0)) :=
      Finset.sum_congr rfl
        (fun j hj => profC_clamp_even j (Finset.mem_filter.mp hj).2 h1 h3)
    have hsingle : (∑ j ∈ (Finset.range N).filter (fun j => j % 2 = 0),
          (if j = 0 then 3 - t else 0)) = 3 - t := by
      rw [Finset.sum_eq_single 0]
      · rw [if_pos rfl]
      · intro b _ hb
        rw [if_neg hb]
      · intro h0
        exact absurd hmem0 h0
    rw [hA, hB, hsum, Finset.sum_add_distrib, hsingle]
  rw [key]
  ring


theorem riPhi_le_of_supersolution {U V : ℝ → ℝ}
    (hU0 : ∀ s, 0 ≤ U s) (hV0 : ∀ s, 0 ≤ V s)
    (hbase : ∀ s, profC 0 s ≤ U s)
    (hVint : ∀ a b : ℝ, IntervalIntegrable V volume a b)
    (hUint : ∀ a b : ℝ, IntervalIntegrable U volume a b)
    (hUV : ∀ s : ℝ, 2 ≤ s → ∀ b : ℝ, max (s - 1) 2 ≤ b →
      (3 - s) * (if s ≤ 3 then (1:ℝ) else 0) + ∫ u in (max (s - 1) 2)..b, V u ≤ s * U s)
    (hVU : ∀ s : ℝ, 2 ≤ s → ∀ b : ℝ, s - 1 ≤ b → ∫ u in (s - 1)..b, U u ≤ s * V s)
    (hlin : ∀ t : ℝ, 1 ≤ t → t ≤ 3 → (3 - t + 3 * U 3) / t ≤ U t) :
    ∀ s : ℝ, 2 ≤ s → riPhi s ≤ U s := by
  intro s hs
  have key : ∀ N : ℕ, ∀ t : ℝ, 2 ≤ t → apart N t ≤ U t ∧ bpart N t ≤ V t := by
    intro N
    induction N with
    | zero => intro t ht; exact ⟨by simp [apart, hU0 t], by simp [bpart, hV0 t]⟩
    | succ N ih =>
      intro t ht
      have hN1 : 1 ≤ N + 1 := Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero N)
      have hsub : (N + 1 : ℕ) - 1 = N := by omega
      constructor
      · by_cases hbig : (((N + 1 : ℕ)) : ℝ) + 2 < t
        · rw [apart_eq_zero (le_of_lt hbig)]; exact hU0 t
        · have htN : t ≤ (((N + 1 : ℕ)) : ℝ) + 2 := le_of_not_gt hbig
          have h := apart_mul_eq (N := N + 1) ht hN1 htN
          rw [hsub] at h
          have hN2 : max (t - 1) 2 ≤ (((N + 1 : ℕ)) : ℝ) + 1 := by
            refine max_le (by linarith [htN]) ?_
            push_cast; exact_mod_cast (by omega : 2 ≤ N + 1 + 1)
          have hmono : (∫ u in (max (t - 1) 2)..((((N + 1 : ℕ)) : ℝ) + 1), bpart N u)
              ≤ ∫ u in (max (t - 1) 2)..((((N + 1 : ℕ)) : ℝ) + 1), V u := by
            refine intervalIntegral.integral_mono_on (by linarith)
              (bpart_intervalIntegrable N _ _) (hVint _ _) ?_
            intro x hx
            have hx2 : (2:ℝ) ≤ x := le_trans (le_max_right _ _) hx.1
            exact (ih x hx2).2
          have h3 : (3 - t) * (if t ≤ 3 then (1:ℝ) else 0)
              = (if t ≤ 3 then 3 - t else 0) := by
            by_cases h : t ≤ 3
            · rw [if_pos h, if_pos h]; ring
            · rw [if_neg h, if_neg h]; ring
          have hb := hUV t ht ((((N + 1 : ℕ)) : ℝ) + 1) hN2
          rw [h3] at hb
          have hmul : apart (N + 1) t * t ≤ U t * t := by
            rw [mul_comm (apart (N + 1) t) t, h, mul_comm (U t) t]
            exact le_trans (add_le_add (le_refl _) hmono) hb
          exact le_of_mul_le_mul_right hmul (by linarith : (0:ℝ) < t)
      · by_cases hbig : (((N + 1 : ℕ)) : ℝ) + 2 < t
        · rw [bpart_eq_zero (le_of_lt hbig)]; exact hV0 t
        · have htN : t ≤ (((N + 1 : ℕ)) : ℝ) + 2 := le_of_not_gt hbig
          have h := bpart_mul_eq (N := N + 1) ht hN1 htN
          rw [hsub] at h
          have hN2 : t - 1 ≤ (((N + 1 : ℕ)) : ℝ) + 1 := by linarith [htN]
          have hmono : (∫ u in (t - 1)..((((N + 1 : ℕ)) : ℝ) + 1), apart N u)
              ≤ ∫ u in (t - 1)..((((N + 1 : ℕ)) : ℝ) + 1), U u := by
            refine intervalIntegral.integral_mono_on (by linarith)
              (apart_intervalIntegrable N _ _) (hUint _ _) ?_
            intro x hx
            by_cases hx2 : (2:ℝ) ≤ x
            · exact (ih x hx2).1
            · by_cases hN0 : 1 ≤ N
              · -- x ∈ [t-1, 2): the clamping identity
                have hx3 : x ≤ 3 := by linarith [hx2]
                have hx1 : 1 ≤ x := by linarith [hx.1, ht]
                have hA3 : apart N 3 ≤ U 3 := (ih 3 (by norm_num)).1
                have hlin' := hlin x hx1 hx3
                have hclamp := apart_linear hN0 hx1 hx3
                have hxpos : (0:ℝ) < x := by linarith
                rw [div_le_iff₀ hxpos] at hlin'
                have hxx : x * apart N x = (3 - x) + 3 * apart N 3 := by linarith
                have : x * apart N x ≤ x * U x := by
                  rw [hxx]; nlinarith [hA3, hlin']
                exact le_of_mul_le_mul_left this hxpos
              · have hNz : N = 0 := by omega
                subst hNz
                simp only [apart, Finset.range_zero, Finset.filter_empty, Finset.sum_empty]
                exact hU0 x
          have hb := hVU t ht ((((N + 1 : ℕ)) : ℝ) + 1) hN2
          have hmul : bpart (N + 1) t * t ≤ V t * t := by
            rw [mul_comm (bpart (N + 1) t) t, h, mul_comm (V t) t]
            exact le_trans hmono hb
          exact le_of_mul_le_mul_right hmul (by linarith : (0:ℝ) < t)
  have hbound : ∀ n : ℕ, (∑ k ∈ Finset.range n, profC (2 * k) s) ≤ U s := by
    intro n
    have h2n : (∑ k ∈ Finset.range n, profC (2 * k) s) = apart (2 * n) s := by
      unfold apart
      have hsub : (Finset.range (2 * n)).filter (fun j => j % 2 = 0)
          = (Finset.range n).image (fun k => 2 * k) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
        constructor
        · rintro ⟨hj, hje⟩
          exact ⟨j / 2, by omega, by
            rw [Nat.mul_comm]; exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hje)⟩
        · rintro ⟨k, hk, rfl⟩
          exact ⟨by omega, Nat.mul_mod_right 2 k⟩
      rw [hsub, Finset.sum_image]
      intro a _ b _ hab
      exact Nat.mul_left_cancel (by norm_num : 0 < 2) hab
    rw [h2n]
    exact (key (2 * n) s hs).1
  have hsum : Summable (fun k : ℕ => profC (2 * k) s) :=
    summable_of_sum_range_le (fun k => profC_nonneg (2 * k) s) hbound
  have hlim : Filter.Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, profC (2 * k) s)
      Filter.atTop (nhds (∑' k, profC (2 * k) s)) :=
    hsum.hasSum.tendsto_sum_nat
  exact le_of_tendsto hlim (Filter.Eventually.of_forall hbound)

end
end Work.NumberTheory.Chen.APSwitchUpper
