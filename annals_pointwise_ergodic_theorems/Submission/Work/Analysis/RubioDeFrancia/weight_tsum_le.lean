import Mathlib

namespace Work.Analysis.RubioDeFrancia

/-- For a summable `g : ℕ → ℝ`, the `ℤ`-indexed sum of `g ∘ Int.natAbs` equals
`g 0 + 2 ∑_{k ≥ 0} g (k + 1)`: the value `0` is hit once and every `k ≥ 1` is hit twice
(by `k` and by `-k`). -/
theorem sum_int_natAbs_even (g : ℕ → ℝ) (hg : Summable g) :
    ∑' m : ℤ, g m.natAbs = g 0 + 2 * ∑' k : ℕ, g (k + 1) := by
  have hnat : Summable (fun n : ℕ => g (n : ℤ).natAbs) := by simpa using hg
  have hneg : Summable (fun n : ℕ => g (-(n : ℤ)).natAbs) := by
    simpa [Int.natAbs_neg] using hg
  have hZ : Summable (fun m : ℤ => g m.natAbs) := Summable.of_nat_of_neg hnat hneg
  have h1 : HasSum (fun m : ℤ => g m.natAbs)
      ((∑' n : ℕ, g (n : ℤ).natAbs) + (∑' n : ℕ, g (-(n : ℤ)).natAbs)
        - g (0 : ℤ).natAbs) :=
    HasSum.of_nat_of_neg hnat.hasSum hneg.hasSum
  have h2 : HasSum (fun m : ℤ => g m.natAbs) (∑' m : ℤ, g m.natAbs) := hZ.hasSum
  have hval := h1.unique h2
  rw [← hval]
  have hA : (∑' n : ℕ, g (n : ℤ).natAbs) = ∑' n : ℕ, g n :=
    tsum_congr (fun n => by rw [Int.natAbs_natCast])
  have hB : (∑' n : ℕ, g (-(n : ℤ)).natAbs) = ∑' n : ℕ, g n :=
    tsum_congr (fun n => by rw [Int.natAbs_neg, Int.natAbs_natCast])
  have h0 : g (0 : ℤ).natAbs = g 0 := by rw [Int.natAbs_zero]
  rw [hA, hB, h0, Summable.tsum_eq_zero_add hg]
  ring

/-- `∑_{k ≥ 0} N / (N + k + 1)² ≤ 1` for `N ≥ 1`, together with summability.
The summand is dominated by the telescoping difference `N/(N+k) - N/(N+k+1)`. -/
theorem weight_tail_le (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun k : ℕ => (N : ℝ) / ((N : ℝ) + ((k + 1 : ℕ) : ℝ)) ^ 2) ∧
      (∑' k : ℕ, (N : ℝ) / ((N : ℝ) + ((k + 1 : ℕ) : ℝ)) ^ 2) ≤ 1 := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := by
    have : N ≠ 0 := Nat.one_le_iff_ne_zero.mp hN
    exact_mod_cast this
  have hterm : ∀ k : ℕ,
      (N : ℝ) / ((N : ℝ) + ((k : ℝ) + 1)) ^ 2
        ≤ (N : ℝ) / ((N : ℝ) + (k : ℝ)) - (N : ℝ) / ((N : ℝ) + (k : ℝ) + 1) := by
    intro k
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hk1 : (0 : ℝ) < (N : ℝ) + (k : ℝ) := by linarith
    have hk2 : (0 : ℝ) < (N : ℝ) + (k : ℝ) + 1 := by linarith
    have hR : (N : ℝ) / ((N : ℝ) + (k : ℝ)) - (N : ℝ) / ((N : ℝ) + (k : ℝ) + 1)
        = (N : ℝ) / (((N : ℝ) + (k : ℝ)) * ((N : ℝ) + (k : ℝ) + 1)) := by
      field_simp [hk1.ne', hk2.ne']
      ring
    rw [hR]
    have hb : (0 : ℝ) < ((N : ℝ) + ((k : ℝ) + 1)) ^ 2 := by positivity
    have hd : (0 : ℝ) < ((N : ℝ) + (k : ℝ)) * ((N : ℝ) + (k : ℝ) + 1) := mul_pos hk1 hk2
    rw [div_le_div_iff₀ hb hd]
    nlinarith [hN1, hk]
  have htel : ∀ K : ℕ, ∑ i ∈ Finset.range K,
      ((N : ℝ) / ((N : ℝ) + (i : ℝ)) - (N : ℝ) / ((N : ℝ) + (i : ℝ) + 1))
        = 1 - (N : ℝ) / ((N : ℝ) + (K : ℝ)) := by
    intro K
    have h2 : ∑ i ∈ Finset.range K,
        ((N : ℝ) / ((N : ℝ) + (i : ℝ)) - (N : ℝ) / ((N : ℝ) + (i : ℝ) + 1))
        = - ∑ i ∈ Finset.range K,
            ((N : ℝ) / ((N : ℝ) + ((i + 1 : ℕ) : ℝ)) - (N : ℝ) / ((N : ℝ) + (i : ℝ))) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      push_cast
      ring
    have h1 : ∑ i ∈ Finset.range K,
        ((N : ℝ) / ((N : ℝ) + ((i + 1 : ℕ) : ℝ)) - (N : ℝ) / ((N : ℝ) + (i : ℝ)))
        = (N : ℝ) / ((N : ℝ) + (K : ℝ)) - 1 := by
      have hsub := Finset.sum_range_sub (fun i : ℕ => (N : ℝ) / ((N : ℝ) + (i : ℝ))) K
      simpa only [Nat.cast_zero, add_zero, div_self hN0] using hsub
    rw [h2, h1]
    ring
  have hbound : ∀ K : ℕ,
      ∑ i ∈ Finset.range K, (N : ℝ) / ((N : ℝ) + ((i + 1 : ℕ) : ℝ)) ^ 2 ≤ 1 := by
    intro K
    calc ∑ i ∈ Finset.range K, (N : ℝ) / ((N : ℝ) + ((i + 1 : ℕ) : ℝ)) ^ 2
        ≤ ∑ i ∈ Finset.range K,
            ((N : ℝ) / ((N : ℝ) + (i : ℝ)) - (N : ℝ) / ((N : ℝ) + (i : ℝ) + 1)) := by
          apply Finset.sum_le_sum
          intro i _
          push_cast
          exact hterm i
      _ = 1 - (N : ℝ) / ((N : ℝ) + (K : ℝ)) := htel K
      _ ≤ 1 := by
          have hd : (0 : ℝ) < (N : ℝ) + (K : ℝ) := by
            have : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
            linarith
          have hnn : (0 : ℝ) ≤ (N : ℝ) / ((N : ℝ) + (K : ℝ)) :=
            div_nonneg (by linarith) hd.le
          linarith
  exact ⟨summable_of_sum_range_le (fun k => by positivity) hbound,
    Real.tsum_le_of_sum_range_le (fun k => by positivity) hbound⟩

theorem weight_tsum_le (N : ℕ) (hN : 1 ≤ N) :
    (∑' m : ℤ, ENNReal.ofReal ((N : ℝ) / ((N : ℝ) + |((m : ℤ) : ℝ)|) ^ 2))
      ≤ ENNReal.ofReal 4 := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  set g : ℕ → ℝ := fun k => (N : ℝ) / ((N : ℝ) + (k : ℝ)) ^ 2 with hg
  have htail := weight_tail_le N hN
  have hshift : (fun k : ℕ => g (k + 1))
      = fun k : ℕ => (N : ℝ) / ((N : ℝ) + ((k + 1 : ℕ) : ℝ)) ^ 2 := by
    funext k
    rw [hg]
  have hsumShift : Summable (fun k : ℕ => g (k + 1)) := by
    rw [hshift]; exact htail.1
  have hsumG : Summable g := (summable_nat_add_iff (f := g) 1).mp hsumShift
  have hsumTail : (∑' k : ℕ, g (k + 1)) ≤ 1 := by
    rw [hshift]; exact htail.2
  have hcast : ∀ m : ℤ, ((m.natAbs : ℕ) : ℝ) = |((m : ℤ) : ℝ)| := fun m => by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  have hf_eq : ∀ m : ℤ, (N : ℝ) / ((N : ℝ) + |((m : ℤ) : ℝ)|) ^ 2 = g m.natAbs := by
    intro m
    simp only [hg]
    rw [hcast m]
  have hFsum : Summable (fun m : ℤ => g m.natAbs) := by
    apply Summable.of_nat_of_neg
    · simpa [Int.natAbs_natCast] using hsumG
    · simpa [Int.natAbs_neg, Int.natAbs_natCast] using hsumG
  have hg0 : g 0 ≤ 1 := by
    rw [hg]
    simp only [Nat.cast_zero, add_zero]
    have hb : (0 : ℝ) < (N : ℝ) ^ 2 := by
      have : (0 : ℝ) < (N : ℝ) := by linarith
      positivity
    rw [div_le_one hb]
    nlinarith [hN1]
  have hkey : (∑' m : ℤ, (N : ℝ) / ((N : ℝ) + |((m : ℤ) : ℝ)|) ^ 2) ≤ 4 := by
    have heq : (∑' m : ℤ, (N : ℝ) / ((N : ℝ) + |((m : ℤ) : ℝ)|) ^ 2)
        = ∑' m : ℤ, g m.natAbs := tsum_congr hf_eq
    rw [heq, sum_int_natAbs_even g hsumG]
    linarith
  have hnn : ∀ m : ℤ, (0 : ℝ) ≤ (N : ℝ) / ((N : ℝ) + |((m : ℤ) : ℝ)|) ^ 2 := by
    intro m; positivity
  have hsumZ : Summable (fun m : ℤ => (N : ℝ) / ((N : ℝ) + |((m : ℤ) : ℝ)|) ^ 2) := by
    rw [show (fun m : ℤ => (N : ℝ) / ((N : ℝ) + |((m : ℤ) : ℝ)|) ^ 2)
        = fun m : ℤ => g m.natAbs from funext hf_eq]
    exact hFsum
  calc ∑' m : ℤ, ENNReal.ofReal ((N : ℝ) / ((N : ℝ) + |((m : ℤ) : ℝ)|) ^ 2)
      = ENNReal.ofReal (∑' m : ℤ, (N : ℝ) / ((N : ℝ) + |((m : ℤ) : ℝ)|) ^ 2) :=
        (ENNReal.ofReal_tsum_of_nonneg hnn hsumZ).symm
    _ ≤ ENNReal.ofReal 4 := ENNReal.ofReal_le_ofReal hkey

end Work.Analysis.RubioDeFrancia
