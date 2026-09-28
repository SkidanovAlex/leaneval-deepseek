import Mathlib

namespace Work.HP.MDEstimates

/-- `2 ^ ((3/2) * j)` rewritten as a monoid power of the constant `2 ^ (3/2)`. -/
private lemma rpow_half (j : ℕ) :
    (2 : ℝ) ^ ((3 : ℝ) / 2 * (j : ℝ)) = ((2 : ℝ) ^ ((3 : ℝ) / 2)) ^ j := by
  rw [Real.rpow_mul (by norm_num)]
  rw [Real.rpow_natCast]

/-- Geometric series bound: for `q ≥ 3/2`, the partial sum `∑_{j≤S} q^j` is at most
`3 q^S`. -/
private lemma geom_bound (q : ℝ) (hq : (3 : ℝ) / 2 ≤ q) (S : ℕ) :
    ∑ j ∈ Finset.range (S + 1), q ^ j ≤ 3 * q ^ S := by
  induction S with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hq0 : 0 ≤ q := by linarith
    have hqS : 0 ≤ q ^ n := pow_nonneg hq0 n
    calc ∑ j ∈ Finset.range (n + 1), q ^ j + q ^ (n + 1)
        ≤ 3 * q ^ n + q ^ (n + 1) := add_le_add ih (le_refl _)
      _ = q ^ n * (3 + q) := by rw [pow_succ]; ring
      _ ≤ q ^ n * (3 * q) := by
          apply mul_le_mul_of_nonneg_left (by linarith) hqS
      _ = 3 * q ^ (n + 1) := by rw [pow_succ]; ring

/-- The number of triples `k` (each with `k.1 + k.2.1 + k.2.2 = n`) in a finite set `K`
is at most `(n+1)^2`: project onto the first two coordinates. -/
private lemma card_filter_sigma_le (K : Finset (ℕ × ℕ × ℕ)) (n : ℕ) :
    (K.filter (fun k => k.1 + k.2.1 + k.2.2 = n)).card ≤ (n + 1) ^ 2 := by
  let f : ℕ × ℕ × ℕ → ℕ × ℕ := fun k => (k.1, k.2.1)
  have hf : Set.InjOn f ↑(K.filter (fun k => k.1 + k.2.1 + k.2.2 = n)) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_filter] at ha hb
    have h1 : a.1 = b.1 := by simpa [f] using congrArg Prod.fst hab
    have h2 : a.2.1 = b.2.1 := by simpa [f] using congrArg Prod.snd hab
    have h3 : a.2.2 = b.2.2 := by omega
    exact Prod.ext h1 (Prod.ext h2 h3)
  have hmap : Set.MapsTo f ↑(K.filter (fun k => k.1 + k.2.1 + k.2.2 = n))
      ↑(Finset.range (n + 1) ×ˢ Finset.range (n + 1)) := by
    intro k hk
    simp only [Finset.mem_coe, Finset.mem_filter] at hk
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range, f]
    constructor <;> omega
  calc (K.filter (fun k => k.1 + k.2.1 + k.2.2 = n)).card
      ≤ (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).card :=
        Finset.card_le_card_of_injOn f hmap hf
    _ = (n + 1) * (n + 1) := by rw [Finset.card_product, Finset.card_range]
    _ = (n + 1) ^ 2 := by ring

/-- Counting bound for the exponential shell sum: grouping `K` by the value of
`σ k = k.1 + k.2.1 + k.2.2` and using `#(layer n) ≤ (n+1)^2` together with a
geometric-series estimate for the ratio `2^(3/2)`. -/
theorem rpow_shell_sum (K : Finset (ℕ × ℕ × ℕ)) (S : ℕ)
    (h : ∀ k ∈ K, k.1 + k.2.1 + k.2.2 ≤ S) :
    (∑ k ∈ K, (2 : ℝ) ^ (((3 : ℝ) / 2) * ((k.1 + k.2.1 + k.2.2 : ℕ) : ℝ)))
      ≤ 3 * ((S : ℝ) + 2) ^ 2 * (2 : ℝ) ^ (((3 : ℝ) / 2) * (S : ℝ)) := by
  have hmap : ∀ k ∈ K, (k.1 + k.2.1 + k.2.2) ∈ Finset.range (S + 1) := by
    intro k hk
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (h k hk)
  have key := Finset.sum_fiberwise_of_maps_to' (s := K) (t := Finset.range (S + 1))
        (g := fun k : ℕ × ℕ × ℕ => k.1 + k.2.1 + k.2.2) hmap
        (fun n => (2 : ℝ) ^ ((3 : ℝ) / 2 * (n : ℝ)))
  rw [← key]
  have hq3 : (3 : ℝ) / 2 ≤ (2 : ℝ) ^ ((3 : ℝ) / 2) := by
    have h1 : (1 : ℝ) ≤ (3 : ℝ) / 2 := by norm_num
    have h2 := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num) h1
    rw [Real.rpow_one] at h2
    linarith
  have hstep1 : ∑ j ∈ Finset.range (S + 1),
        ∑ i ∈ K with i.1 + i.2.1 + i.2.2 = j, (2 : ℝ) ^ ((3 : ℝ) / 2 * (j : ℝ))
      ≤ ∑ j ∈ Finset.range (S + 1), ((S : ℝ) + 2) ^ 2 * (2 : ℝ) ^ ((3 : ℝ) / 2 * (j : ℝ)) := by
    apply Finset.sum_le_sum
    intro j hj
    rw [Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by norm_num) _)
    have hjle : j ≤ S := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hcardNat : (K.filter (fun i : ℕ × ℕ × ℕ => i.1 + i.2.1 + i.2.2 = j)).card ≤ (S + 2) ^ 2 :=
      le_trans (card_filter_sigma_le K j) (by apply Nat.pow_le_pow_left; omega)
    have hcardR : ((K.filter (fun i : ℕ × ℕ × ℕ => i.1 + i.2.1 + i.2.2 = j)).card : ℝ)
        ≤ ((S + 2 : ℕ) : ℝ) ^ 2 := by
      rw [← Nat.cast_pow]; exact_mod_cast hcardNat
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hcardR
  have hgeom : ∑ j ∈ Finset.range (S + 1), (2 : ℝ) ^ ((3 : ℝ) / 2 * (j : ℝ))
      ≤ 3 * (2 : ℝ) ^ ((3 : ℝ) / 2 * (S : ℝ)) := by
    calc ∑ j ∈ Finset.range (S + 1), (2 : ℝ) ^ ((3 : ℝ) / 2 * (j : ℝ))
        = ∑ j ∈ Finset.range (S + 1), ((2 : ℝ) ^ ((3 : ℝ) / 2)) ^ j := by
          apply Finset.sum_congr rfl; intro j _; exact rpow_half j
      _ ≤ 3 * ((2 : ℝ) ^ ((3 : ℝ) / 2)) ^ S := geom_bound ((2 : ℝ) ^ ((3 : ℝ) / 2)) hq3 S
      _ = 3 * (2 : ℝ) ^ ((3 : ℝ) / 2 * (S : ℝ)) := by rw [rpow_half S]
  calc ∑ j ∈ Finset.range (S + 1),
        ∑ i ∈ K with i.1 + i.2.1 + i.2.2 = j, (2 : ℝ) ^ ((3 : ℝ) / 2 * (j : ℝ))
      ≤ ∑ j ∈ Finset.range (S + 1), ((S : ℝ) + 2) ^ 2 * (2 : ℝ) ^ ((3 : ℝ) / 2 * (j : ℝ)) := hstep1
    _ = ((S : ℝ) + 2) ^ 2 * ∑ j ∈ Finset.range (S + 1), (2 : ℝ) ^ ((3 : ℝ) / 2 * (j : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ ((S : ℝ) + 2) ^ 2 * (3 * (2 : ℝ) ^ ((3 : ℝ) / 2 * (S : ℝ))) := by
        apply mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = 3 * ((S : ℝ) + 2) ^ 2 * (2 : ℝ) ^ ((3 : ℝ) / 2 * (S : ℝ)) := by ring

end Work.HP.MDEstimates
