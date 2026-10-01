import Mathlib
import Submission.Work.LinnikBurgess.frame_count_prov_aux.caseT_defs
import Submission.Work.LinnikBurgess.a2_dist_le_two_Icc
import Submission.Work.LinnikBurgess.sum_sqrtGcd_Icc_le
import Submission.Commons.NumberTheory.Divisors.sum_gcd_le_of_pos

namespace Work.LinnikBurgess

open Finset

/-!
# The Case-T `Asum` bound

`frame_count_prov_aux.Asum H m e x0 = ∑_{x ∈ [1,H], x ≠ x0, e ∣ |x0-x|} (wg m x0 x)^2` is the
sum of the squared weight factors over the `x` that are congruent to `x0` modulo `e`.  Since
`(wg m x0 x)^2 = gcd(m, |x0 - x|)`, the estimate to prove is

`Asum H m e x0 ≤ 2 · (H/e) · τ(m)`.

Writing `t = |x0 - x| = e·k` (`t > 0`, `e ∣ t`, so `k ≥ 1`), coprimality of `m` and `e` gives
`gcd(m, e·k) = gcd(m, k)`, and each `k ≤ H/e` arises from at most two values of `x`
(`x = x0 ± e·k`).  Hence

`Asum ≤ 2 · ∑_{k ≤ (H-1)/e} gcd(m,k) ≤ 2 · ((H-1)/e) · τ(m) ≤ 2 · (H/e) · τ(m)`,

the middle inequality being `Commons.NumberTheory.Divisors.sum_gcd_le_of_pos`.

The "two-to-one" step is packaged as the reusable `a2_dist_le_two_Icc`; the arithmetic
progression sum is the lemma `sum_gcd_filter_dvd_le` below.
-/

/-- **Multiples-of-`e` gcd sum.**  For `m > 0`, `e > 0` and `Nat.Coprime m e`, the sum of
`gcd(m,·)` over the multiples of `e` in `[1,N]` is at most `(N/e)·τ(m)`.

Indeed `c = e·k` with `k` running over `[1, N/e]`, and `gcd(m, e·k) = gcd(m,k)` by coprimality;
then `∑_{k ≤ N/e} gcd(m,k) ≤ (N/e)·τ(m)` is `sum_gcd_le_of_pos`.  Coprimality is essential:
for `m = e = p` and `N = 2p` the sum is `2p` while `(N/e)·τ(m) = 4`. -/
theorem sum_gcd_filter_dvd_le {m e N : ℕ} (hm : 0 < m) (he : 0 < e) (hme : Nat.Coprime m e) :
    (∑ c ∈ (Finset.Icc 1 N).filter (fun c => e ∣ c), ((Nat.gcd m c : ℕ) : ℝ))
      ≤ (((N / e : ℕ)) : ℝ) * ((m.divisors.card : ℕ) : ℝ) := by
  -- reindex `c = e*k` (the admissible `c` are exactly the multiples of `e` in `[1,N]`)
  have hbij : (∑ c ∈ (Finset.Icc 1 N).filter (fun c => e ∣ c), Nat.gcd m c)
      = ∑ k ∈ Finset.Icc 1 (N / e), Nat.gcd m (e * k) := by
    refine Finset.sum_bij' (fun c _ => c / e) (fun k _ => e * k) ?_ ?_ ?_ ?_ ?_
    · intro c hc
      obtain ⟨hcIcc, hdvd⟩ := Finset.mem_filter.mp hc
      obtain ⟨hc1, hcN⟩ := Finset.mem_Icc.mp hcIcc
      rw [Finset.mem_Icc]
      refine ⟨?_, Nat.div_le_div_right hcN⟩
      rw [Nat.le_div_iff_mul_le he]
      simpa using Nat.le_of_dvd hc1 hdvd
    · intro k hk
      obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hk
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, ⟨k, rfl⟩⟩
      · exact Nat.one_le_iff_ne_zero.mpr (by positivity)
      · calc e * k ≤ e * (N / e) := Nat.mul_le_mul_left e hkN
          _ ≤ N := Nat.mul_div_le N e
    · intro c hc
      exact Nat.mul_div_cancel' (Finset.mem_filter.mp hc).2
    · intro k _
      exact Nat.mul_div_cancel_left k he
    · intro c hc
      rw [Nat.mul_div_cancel' (Finset.mem_filter.mp hc).2]
  -- coprimality removes the factor `e` from the gcd, and `sum_gcd_le_of_pos` finishes
  have hnat : (∑ c ∈ (Finset.Icc 1 N).filter (fun c => e ∣ c), Nat.gcd m c)
      ≤ (N / e) * m.divisors.card := by
    rw [hbij]
    calc (∑ k ∈ Finset.Icc 1 (N / e), Nat.gcd m (e * k))
        = ∑ k ∈ Finset.Icc 1 (N / e), Nat.gcd m k := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Nat.gcd_comm m (e * k), Nat.gcd_comm m k,
            Nat.Coprime.gcd_mul_left_cancel k hme.symm]
      _ = ∑ k ∈ Finset.Icc 1 (N / e), Nat.gcd k m :=
          Finset.sum_congr rfl (fun k _ => Nat.gcd_comm m k)
      _ ≤ (N / e) * m.divisors.card :=
          Commons.NumberTheory.Divisors.sum_gcd_le_of_pos (N / e) m hm
  calc (∑ c ∈ (Finset.Icc 1 N).filter (fun c => e ∣ c), ((Nat.gcd m c : ℕ) : ℝ))
      = (((∑ c ∈ (Finset.Icc 1 N).filter (fun c => e ∣ c), Nat.gcd m c) : ℕ) : ℝ) := by
        push_cast
        ring
    _ ≤ (((N / e) * m.divisors.card : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = (((N / e : ℕ)) : ℝ) * ((m.divisors.card : ℕ) : ℝ) := by push_cast; ring

/-- **The Case-T `Asum` bound.**  `Asum H m e x0`, the sum of `(wg m x0 x)^2` over
`x ∈ [1,H]`, `x ≠ x0`, with `e ∣ |x0 - x|`, is at most `2 (H/e) τ(m)`.

Route: `(wg m x0 x)^2 = gcd(m, |x0-x|)`, the map `x ↦ |x0 - x|` is at most two-to-one
(`a2_dist_le_two_Icc`), so the sum is at most twice the sum of `gcd(m,c)` over the multiples
`c ≤ H-1` of `e`, which is `(N/e)τ(m)` with `N = H - 1` (`sum_gcd_filter_dvd_le`); finally
`(H-1)/e ≤ H/e`. -/
theorem caseT_Asum_le {H m e : ℕ} (hm : 0 < m) (he : 0 < e) (hme : Nat.Coprime m e)
    {x0 : ℕ} (hx0 : x0 ∈ Finset.Icc 1 H) :
    Work.LinnikBurgess.frame_count_prov_aux.Asum H m e x0
      ≤ 2 * ((H : ℝ) / (e : ℝ)) * ((m.divisors.card : ℕ) : ℝ) := by
  obtain ⟨hx1, hxH⟩ := Finset.mem_Icc.mp hx0
  -- unfold `Asum`, drop the conjunction into `(wg m x0 x)^2 = gcd m |x0 - x|`
  have hAsum : frame_count_prov_aux.Asum H m e x0
      = ∑ x ∈ (Finset.Icc 1 H).filter (fun x => x ≠ x0),
          (if e ∣ del x0 x then ((Nat.gcd m (del x0 x) : ℕ) : ℝ) else 0) := by
    rw [frame_count_prov_aux.Asum, ← Finset.sum_filter,
      ← Finset.filter_filter (p := fun x => x ≠ x0) (q := fun x => e ∣ del x0 x),
      Finset.sum_filter]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [wg_sq m x0 x]
  rw [hAsum]
  -- the two-to-one distance bound
  have hstep1 : (∑ x ∈ (Finset.Icc 1 H).filter (fun x => x ≠ x0),
        (if e ∣ del x0 x then ((Nat.gcd m (del x0 x) : ℕ) : ℝ) else 0))
      ≤ 2 * ∑ c ∈ Finset.Icc 1 (H - 1),
        (if e ∣ c then ((Nat.gcd m c : ℕ) : ℝ) else 0) :=
    a2_dist_le_two_Icc hx1 hxH (F := fun c => if e ∣ c then ((Nat.gcd m c : ℕ) : ℝ) else 0)
      (fun n => by split_ifs with h <;> positivity)
  have hstep2 : 2 * (∑ c ∈ Finset.Icc 1 (H - 1),
        (if e ∣ c then ((Nat.gcd m c : ℕ) : ℝ) else 0))
      = 2 * ∑ c ∈ (Finset.Icc 1 (H - 1)).filter (fun c => e ∣ c), ((Nat.gcd m c : ℕ) : ℝ) := by
    rw [← Finset.sum_filter]
  have hS := sum_gcd_filter_dvd_le (m := m) (e := e) (N := H - 1) hm he hme
  have hcast : (((H - 1) / e : ℕ) : ℝ) ≤ (H : ℝ) / (e : ℝ) := by
    calc (((H - 1) / e : ℕ) : ℝ) ≤ (((H - 1 : ℕ)) : ℝ) / (e : ℝ) := Nat.cast_div_le
      _ ≤ (H : ℝ) / (e : ℝ) := by
          refine div_le_div_of_nonneg_right ?_ (by positivity)
          exact_mod_cast Nat.sub_le H 1
  calc (∑ x ∈ (Finset.Icc 1 H).filter (fun x => x ≠ x0),
          (if e ∣ del x0 x then ((Nat.gcd m (del x0 x) : ℕ) : ℝ) else 0))
      ≤ 2 * (∑ c ∈ Finset.Icc 1 (H - 1),
          (if e ∣ c then ((Nat.gcd m c : ℕ) : ℝ) else 0)) := hstep1
    _ = 2 * (∑ c ∈ (Finset.Icc 1 (H - 1)).filter (fun c => e ∣ c), ((Nat.gcd m c : ℕ) : ℝ)) :=
        hstep2
    _ ≤ 2 * ((((H - 1) / e : ℕ)) : ℝ) * ((m.divisors.card : ℕ) : ℝ) := by
        have h2 := mul_le_mul_of_nonneg_left hS (by norm_num : (0 : ℝ) ≤ 2)
        have h3 : (2 : ℝ) * ((((H - 1) / e : ℕ)) : ℝ) * ((m.divisors.card : ℕ) : ℝ)
            = 2 * (((((H - 1) / e : ℕ)) : ℝ) * ((m.divisors.card : ℕ) : ℝ)) := by ring
        linarith
    _ ≤ 2 * ((H : ℝ) / (e : ℝ)) * ((m.divisors.card : ℕ) : ℝ) := by
        have hD : (0 : ℝ) ≤ ((m.divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
        calc 2 * ((((H - 1) / e : ℕ)) : ℝ) * ((m.divisors.card : ℕ) : ℝ)
            = 2 * (((((H - 1) / e : ℕ)) : ℝ) * ((m.divisors.card : ℕ) : ℝ)) := by ring
          _ ≤ 2 * (((H : ℝ) / (e : ℝ)) * ((m.divisors.card : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcast hD) (by norm_num)
          _ = 2 * ((H : ℝ) / (e : ℝ)) * ((m.divisors.card : ℕ) : ℝ) := by ring

end Work.LinnikBurgess
