import Submission.Work.ConeSwitch.MathlibNoHG

namespace Work.Deep.Nibble.BJ

/-!
# A layer-cake lower bound

If `0 ≤ y`, `0 < γ` and `y < (K + 1) * γ`, then
`y ≤ γ * #{k ∈ [0, K] : k * γ ≤ y}`.

The proof: with `m = ⌊y / γ⌋₊`, every `k ≤ m` lies in the filtered set
(since `k * γ ≤ m * γ ≤ (y / γ) * γ = y`) and `m ≤ K` (since `y / γ < K + 1`),
so the filtered set contains `{0, …, m}` and has at least `m + 1` elements;
as `y / γ < m + 1`, we get `y < γ * (m + 1) ≤ γ * card`.
-/

theorem layer_cake {y γ : ℝ} (hy : 0 ≤ y) (hγ : 0 < γ) (K : ℕ)
    (hK : y < ((K : ℝ) + 1) * γ) :
    y ≤ γ * ((Finset.range (K + 1)).filter (fun k : ℕ => (k : ℝ) * γ ≤ y)).card := by
  have hγ0 : γ ≠ 0 := ne_of_gt hγ
  have ht0 : 0 ≤ y / γ := div_nonneg hy hγ.le
  obtain ⟨m, hmle, hmlt, hmK⟩ :
      ∃ m : ℕ, ((m : ℝ) ≤ y / γ) ∧ (y / γ < ((m : ℝ) + 1)) ∧ (m ≤ K) := by
    refine ⟨Nat.floor (y / γ), Nat.floor_le ht0, Nat.lt_floor_add_one (y / γ), ?_⟩
    have h1 : y / γ < ((K : ℝ) + 1) := (div_lt_iff₀ hγ).mpr hK
    have h4 : y / γ < ((K + 1 : ℕ) : ℝ) := by
      rw [Nat.cast_succ]
      exact h1
    have h3 : Nat.floor (y / γ) < K + 1 := (Nat.floor_lt ht0).mpr h4
    omega
  have hsub : Finset.range (m + 1) ⊆
      (Finset.range (K + 1)).filter (fun k : ℕ => (k : ℝ) * γ ≤ y) := by
    intro k hk
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr ?_, ?_⟩
    · have hk' : k < m + 1 := Finset.mem_range.mp hk
      omega
    · have hkm : (k : ℝ) ≤ (m : ℝ) :=
        Nat.cast_le.mpr (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
      calc (k : ℝ) * γ ≤ (m : ℝ) * γ := mul_le_mul_of_nonneg_right hkm hγ.le
        _ ≤ (y / γ) * γ := mul_le_mul_of_nonneg_right hmle hγ.le
        _ = y := div_mul_cancel₀ y hγ0
  have hcard : m + 1 ≤
      ((Finset.range (K + 1)).filter (fun k : ℕ => (k : ℝ) * γ ≤ y)).card := by
    calc m + 1 = (Finset.range (m + 1)).card := (Finset.card_range _).symm
      _ ≤ ((Finset.range (K + 1)).filter (fun k : ℕ => (k : ℝ) * γ ≤ y)).card :=
        Finset.card_le_card hsub
  have hlt : y < ((m : ℝ) + 1) * γ := (div_lt_iff₀ hγ).mp hmlt
  calc y ≤ ((m : ℝ) + 1) * γ := le_of_lt hlt
    _ = ((m + 1 : ℕ) : ℝ) * γ := by rw [Nat.cast_succ]
    _ = γ * ((m + 1 : ℕ) : ℝ) := mul_comm _ _
    _ ≤ γ * ((Finset.range (K + 1)).filter (fun k : ℕ => (k : ℝ) * γ ≤ y)).card :=
      mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcard) hγ.le

end Work.Deep.Nibble.BJ
