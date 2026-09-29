import Mathlib

/-!
# Bounding a sum of reciprocals by a counting function of superlevel sets

If `S` is a finite set of naturals and `f : ℕ → ℝ` is bounded below by `c > 0` on `S`, while for
every `γ > 0` the number of `k ∈ S` with `f k < γ` is at most `A * γ + B`, then

  `∑_{k ∈ S} 1 / f k ≤ (B + 1) / c + A * (1 + log (#S))`.

The proof is the classical "rank/layer-cake" argument: order the elements of `S` by the value of
`f`; the `j`-th smallest value is at least `max c ((j - B)/A)`, and the resulting harmonic sum is
compared with `∑_{j ≤ #S} u j` for the antitone function `u j = min (1/c) (A / max (j - B) (c*A))`.

The two ingredients are isolated below:

* `sum_antitone_rank_le` — a purely combinatorial rearrangement/Abel inequality;
* `inv_sum_numeric_bound` — the elementary estimate `∑_{j ≤ n} u j ≤ (B+1)/c + A(1 + log n)`.
-/

namespace Work.TMC16Core.Core

/-- Telescoping identity: for `a ≤ N`,
`∑_{j < N} [a ≤ j] (u j - u (j+1)) = u a - u N`. -/
private lemma sum_ite_range_sub {u : ℕ → ℝ} {a N : ℕ} (ha : a ≤ N) :
    ∑ j ∈ Finset.range N, (if a ≤ j then u j - u (j+1) else 0) = u a - u N := by
  rw [← Finset.sum_filter]
  have hfil : (Finset.range N).filter (fun j => a ≤ j) = Finset.Ico a N := by
    ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [hfil]
  have h1 : ∑ k ∈ Finset.range N, (u k - u (k+1)) = u 0 - u N := by
    have h := Finset.sum_range_sub u N
    have h' : ∑ k ∈ Finset.range N, (u k - u (k+1)) = -∑ k ∈ Finset.range N, (u (k+1) - u k) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro k hk; ring
    rw [h', h]; ring
  have h2 : ∑ k ∈ Finset.range a, (u k - u (k+1)) = u 0 - u a := by
    have h := Finset.sum_range_sub u a
    have h' : ∑ k ∈ Finset.range a, (u k - u (k+1)) = -∑ k ∈ Finset.range a, (u (k+1) - u k) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro k hk; ring
    rw [h', h]; ring
  have h3 := Finset.sum_range_sub_sum_range (f := fun k => u k - u (k+1)) ha
  rw [h1, h2, hfil] at h3
  linarith

/-- Abel summation for a single function: `∑_{j=1}^{N} u j = N u N + ∑_{j<N} j (u j - u (j+1))`. -/
private lemma abel_sum_Icc (u : ℕ → ℝ) (N : ℕ) :
    ∑ j ∈ Finset.Icc 1 N, u j = (N:ℝ) * u N + ∑ j ∈ Finset.range N, (u j - u (j+1)) * (j:ℝ) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih, Finset.sum_range_succ]
    push_cast
    ring

/-- **Rearrangement lemma.**  If the "counting function" `j ↦ #{x ∈ T | r x ≤ j}` is dominated by
the identity and `u` is a nonnegative antitone sequence, then `∑_{x ∈ T} u (r x)` is at most the sum
of `u` over `{1, …, N}`. -/
private lemma sum_antitone_rank_le {α : Type*} (T : Finset α) (r : α → ℕ) (N : ℕ) {u : ℕ → ℝ}
    (hu : Antitone u) (hu0 : ∀ j, 0 ≤ u j) (hle : ∀ x ∈ T, r x ≤ N)
    (hcnt : ∀ j, (T.filter (fun x => r x ≤ j)).card ≤ j) :
    ∑ x ∈ T, u (r x) ≤ ∑ j ∈ Finset.Icc 1 N, u j := by
  have hc_nn : ∀ j, 0 ≤ u j - u (j+1) := fun j => sub_nonneg.mpr (hu (Nat.le_succ j))
  have hTc : T.card ≤ N := by
    have h := hcnt N
    rwa [Finset.filter_true_of_mem (fun x hx => hle x hx)] at h
  calc ∑ x ∈ T, u (r x)
      = ∑ x ∈ T, (u N + ∑ j ∈ Finset.range N, (if r x ≤ j then u j - u (j+1) else 0)) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [sum_ite_range_sub (hle x hx)]; ring
    _ = T.card * u N + ∑ j ∈ Finset.range N, ∑ x ∈ T, (if r x ≤ j then u j - u (j+1) else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_comm, nsmul_eq_mul]
    _ ≤ T.card * u N + ∑ j ∈ Finset.range N, (u j - u (j+1)) * (j:ℝ) := by
          apply add_le_add_right
          apply Finset.sum_le_sum
          intro j hj
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
          apply mul_le_mul_of_nonneg_left _ (hc_nn j)
          exact_mod_cast hcnt j
    _ ≤ N * u N + ∑ j ∈ Finset.range N, (u j - u (j+1)) * (j:ℝ) := by
          apply add_le_add_left
          apply mul_le_mul_of_nonneg_right _ (hu0 N)
          exact_mod_cast hTc
    _ = ∑ j ∈ Finset.Icc 1 N, u j := (abel_sum_Icc u N).symm

/-- The harmonic sum `∑_{k < M} 1/(k+1)` is at most `1 + log M`. -/
private lemma harmR_le (M : ℕ) :
    ∑ k ∈ Finset.range M, ((k:ℝ)+1)⁻¹ ≤ 1 + Real.log (M:ℝ) := by
  have h := harmonic_le_one_add_log M
  have h2 : (harmonic M : ℝ) = ∑ k ∈ Finset.range M, ((k:ℝ)+1)⁻¹ := by
    rw [harmonic]; push_cast; ring
  rw [h2] at h; exact h

/-- `log (n - B) ≤ log n` for natural numbers (with Lean's `log 0 = 0`). -/
private lemma log_nat_sub_le (B n : ℕ) :
    Real.log ((n - B : ℕ):ℝ) ≤ Real.log (n:ℝ) := by
  rcases Nat.eq_zero_or_pos (n - B) with h | h
  · rw [h, Nat.cast_zero, Real.log_zero]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · rw [hn, Nat.cast_zero, Real.log_zero]
    · exact Real.log_nonneg (by exact_mod_cast hn)
  · have hle : ((n - B : ℕ):ℝ) ≤ (n:ℝ) := by exact_mod_cast Nat.sub_le n B
    exact Real.log_le_log (by exact_mod_cast h) hle

/-- The tail `∑_{j=B+1}^{n} A/(j - B)` is bounded by `A (1 + log (n - B))`. -/
private lemma sum_Icc_inv_shift_le (B n : ℕ) {A : ℝ} (hA : 0 < A) :
    ∑ j ∈ Finset.Icc (B+1) n, A / ((j:ℝ) - (B:ℝ)) ≤ A * (1 + Real.log ((n-B:ℕ):ℝ)) := by
  have himg : Finset.Icc (B+1) n = (Finset.range (n-B)).image (fun k => k + (B+1)) := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨j - B - 1, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩; omega
  rw [himg, Finset.sum_image]
  · calc ∑ k ∈ Finset.range (n-B), A / (((k + (B+1):ℕ):ℝ) - (B:ℝ))
        = ∑ k ∈ Finset.range (n-B), A / ((k:ℝ)+1) := by
          apply Finset.sum_congr rfl; intro k hk
          have hden : (((k + (B+1):ℕ)):ℝ) - (B:ℝ) = (k:ℝ)+1 := by push_cast; ring
          rw [hden]
      _ = A * ∑ k ∈ Finset.range (n-B), ((k:ℝ)+1)⁻¹ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro k hk; rw [div_eq_mul_inv]
      _ ≤ A * (1 + Real.log ((n-B:ℕ):ℝ)) :=
          mul_le_mul_of_nonneg_left (harmR_le (n-B)) (le_of_lt hA)
  · intro k1 hk1 k2 hk2 heq
    simp only [Finset.mem_coe, Finset.mem_range] at hk1 hk2
    exact Nat.add_right_cancel heq

/-- **Elementary estimate.**  For the antitone function
`u j = min (1/c) (A / max (j - B) (c*A))` one has `∑_{j ≤ n} u j ≤ (B+1)/c + A(1 + log n)`. -/
private theorem inv_sum_numeric_bound (n B : ℕ) {A c : ℝ} (hA : 0 < A) (hc : 0 < c) :
    ∑ j ∈ Finset.Icc 1 n, min (1 / c) (A / max ((j : ℝ) - (B : ℝ)) (c * A))
      ≤ ((B : ℝ) + 1) / c + A * (1 + Real.log (n : ℝ)) := by
  have hpt : ∀ j ∈ Finset.Icc 1 n,
      min (1/c) (A / max ((j:ℝ)-(B:ℝ)) (c*A)) ≤ (if j ≤ B then 1/c else A / ((j:ℝ)-(B:ℝ))) := by
    intro j hj
    by_cases hjB : j ≤ B
    · rw [if_pos hjB]; exact min_le_left _ _
    · rw [if_neg hjB]
      apply le_trans (min_le_right _ _)
      apply div_le_div_of_nonneg_left (le_of_lt hA)
      · have : (j:ℝ) > (B:ℝ) := by exact_mod_cast (not_le.mp hjB)
        linarith
      · exact le_max_left _ _
  have hpart1 : ∑ j ∈ (Finset.Icc 1 n).filter (fun j => j ≤ B), 1/c ≤ (B:ℝ)/c := by
    have hsub : (Finset.Icc 1 n).filter (fun j => j ≤ B) ⊆ Finset.Icc 1 B := by
      intro j hj; simp only [Finset.mem_filter, Finset.mem_Icc] at hj ⊢; omega
    calc ∑ j ∈ (Finset.Icc 1 n).filter (fun j => j ≤ B), 1/c
        ≤ ∑ j ∈ Finset.Icc 1 B, 1/c :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro x _ _; positivity)
      _ = (B:ℝ)/c := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
          have h : ((B + 1 - 1 : ℕ) : ℝ) = (B:ℝ) := by simp
          rw [h, mul_one_div]
  have hpart2 : ∑ j ∈ (Finset.Icc 1 n).filter (fun j => ¬ j ≤ B), A / ((j:ℝ)-(B:ℝ))
      ≤ A*(1+Real.log ((n-B:ℕ):ℝ)) := by
    have heq : (Finset.Icc 1 n).filter (fun j => ¬ j ≤ B) = Finset.Icc (B+1) n := by
      ext j; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    rw [heq]; exact sum_Icc_inv_shift_le B n hA
  calc ∑ j ∈ Finset.Icc 1 n, min (1/c) (A / max ((j:ℝ)-(B:ℝ)) (c*A))
      ≤ ∑ j ∈ Finset.Icc 1 n, (if j ≤ B then 1/c else A / ((j:ℝ)-(B:ℝ))) := Finset.sum_le_sum hpt
    _ = ∑ j ∈ (Finset.Icc 1 n).filter (fun j => j ≤ B), 1/c
        + ∑ j ∈ (Finset.Icc 1 n).filter (fun j => ¬ j ≤ B), A / ((j:ℝ)-(B:ℝ)) := by
          rw [Finset.sum_ite]
    _ ≤ (B:ℝ)/c + A*(1+Real.log ((n-B:ℕ):ℝ)) := add_le_add hpart1 hpart2
    _ ≤ ((B:ℝ)+1)/c + A*(1+Real.log (n:ℝ)) := by
          apply add_le_add
          · exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hc)
          · apply mul_le_mul_of_nonneg_left _ (le_of_lt hA)
            linarith [log_nat_sub_le B n]

theorem inv_sum_card_filter (S : Finset ℕ) (f : ℕ → ℝ) {A c : ℝ} {B : ℕ}
    (hA : 0 < A) (hc : 0 < c)
    (hf : ∀ k ∈ S, c ≤ f k)
    (hcard : ∀ γ : ℝ, 0 < γ → ((S.filter (fun k => f k < γ)).card : ℝ) ≤ A * γ + (B : ℝ)) :
    ∑ k ∈ S, (f k)⁻¹ ≤ ((B : ℝ) + 1) / c + A * (1 + Real.log (S.card : ℝ)) := by
  rcases Finset.eq_empty_or_nonempty S with hSe | hSne
  · rw [hSe]
    simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero, Real.log_zero, add_zero, mul_one]
    positivity
  · let r : ℕ → ℕ := fun k => (S.filter (fun k' => f k' ≤ f k)).card
    have hr_bound : ∀ k ∈ S, (r k : ℝ) ≤ A * f k + (B:ℝ) := by
      intro k hk
      have hfk_pos : 0 < f k := lt_of_lt_of_le hc (hf k hk)
      show ((S.filter (fun k' => f k' ≤ f k)).card : ℝ) ≤ A * f k + (B:ℝ)
      refine le_of_forall_pos_le_add (fun ε hε => ?_)
      have hε' : 0 < ε / A := by positivity
      have hsub : S.filter (fun k' => f k' ≤ f k) ⊆ S.filter (fun k' => f k' < f k + ε / A) := by
        intro k' hk'
        simp only [Finset.mem_filter] at hk' ⊢
        exact ⟨hk'.1, by linarith [hk'.2, hε']⟩
      have hφpos : 0 < f k + ε / A := by linarith
      have hcard' := hcard (f k + ε / A) hφpos
      have hcard'' : ((S.filter (fun k' => f k' ≤ f k)).card : ℝ)
          ≤ ((S.filter (fun k' => f k' < f k + ε / A)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      have hkey : A * (f k + ε / A) = A * f k + ε := by
        rw [mul_add, mul_div_assoc', mul_div_cancel_left₀ _ (ne_of_gt hA)]
      linarith
    have hpt : ∀ k ∈ S, (f k)⁻¹ ≤ min (1/c) (A / max (((r k):ℝ) - (B:ℝ)) (c*A)) := by
      intro k hk
      have hfk_pos : 0 < f k := lt_of_lt_of_le hc (hf k hk)
      have hDpos : 0 < max (((r k):ℝ) - (B:ℝ)) (c*A) :=
        lt_of_lt_of_le (mul_pos hc hA) (le_max_right _ _)
      apply le_min
      · rw [one_div]
        exact (inv_le_inv₀ hfk_pos hc).mpr (hf k hk)
      · rw [le_div_iff₀ hDpos]
        have hDle : max (((r k):ℝ) - (B:ℝ)) (c*A) ≤ A * f k := by
          apply max_le
          · linarith [hr_bound k hk]
          · nlinarith [hA, hc, hf k hk]
        calc (f k)⁻¹ * max (((r k):ℝ) - (B:ℝ)) (c*A) ≤ (f k)⁻¹ * (A * f k) :=
              mul_le_mul_of_nonneg_left hDle (by positivity)
          _ = A := by field_simp
    have hu_mono : Antitone (fun j : ℕ => min (1/c) (A / max ((j:ℝ) - (B:ℝ)) (c*A))) := by
      intro i j hij
      have hij' : (i:ℝ) ≤ j := by exact_mod_cast hij
      apply min_le_min le_rfl
      apply div_le_div_of_nonneg_left (le_of_lt hA)
      · exact lt_of_lt_of_le (mul_pos hc hA) (le_max_right _ _)
      · apply max_le_max _ le_rfl
        linarith
    have hu_nn : ∀ j : ℕ, 0 ≤ min (1/c) (A / max ((j:ℝ) - (B:ℝ)) (c*A)) := by
      intro j
      apply le_min
      · positivity
      · apply div_nonneg (le_of_lt hA)
        exact le_trans (le_of_lt (mul_pos hc hA)) (le_max_right _ _)
    have hcnt : ∀ j, (S.filter (fun k => r k ≤ j)).card ≤ j := by
      intro j
      by_contra h
      have hlt : j < (S.filter (fun k => r k ≤ j)).card := not_le.mp h
      have hTne : (S.filter (fun k => r k ≤ j)).Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨k1, hk1mem, hk1max⟩ := Finset.exists_max_image (S.filter (fun k => r k ≤ j)) f hTne
      rw [Finset.mem_filter] at hk1mem
      obtain ⟨hk1S, hk1r⟩ := hk1mem
      have hsub : S.filter (fun k => r k ≤ j) ⊆ S.filter (fun k' => f k' ≤ f k1) := by
        intro k hk
        have hkF : k ∈ S.filter (fun k => r k ≤ j) := hk
        rw [Finset.mem_filter] at hk ⊢
        exact ⟨hk.1, hk1max k hkF⟩
      have hcard := Finset.card_le_card hsub
      have hr1 : (S.filter (fun k' => f k' ≤ f k1)).card = r k1 := rfl
      omega
    have hle : ∀ k ∈ S, r k ≤ S.card := by
      intro k hk
      exact Finset.card_le_card (Finset.filter_subset _ _)
    calc ∑ k ∈ S, (f k)⁻¹
        ≤ ∑ k ∈ S, min (1/c) (A / max (((r k):ℝ) - (B:ℝ)) (c*A)) := Finset.sum_le_sum hpt
      _ ≤ ∑ j ∈ Finset.Icc 1 S.card, min (1/c) (A / max ((j:ℝ) - (B:ℝ)) (c*A)) :=
            sum_antitone_rank_le S r S.card hu_mono hu_nn hle hcnt
      _ ≤ ((B:ℝ)+1)/c + A*(1 + Real.log (S.card:ℝ)) := inv_sum_numeric_bound S.card B hA hc

end Work.TMC16Core.Core
