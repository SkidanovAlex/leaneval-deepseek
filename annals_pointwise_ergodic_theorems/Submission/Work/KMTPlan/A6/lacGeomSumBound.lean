import Mathlib
import Submission.Work.KMTPlan.A6.lacunaryLevel

namespace Work.KMTPlan.A6

open Finset
open scoped NNReal BigOperators

/-- **Geometric summation bound along a lacunary family.**

Let `Λ > 1` and let `a : ℕ → ℝ≥0` be `Λ`-lacunary with `a n ≥ 1`.  Then for every real `θ` and
every finite set `S` of indices such that `⌊a n⌋ · θ < 2` for all `n ∈ S`, the sum
`∑_{n ∈ S} ⌊a n⌋ · θ` is bounded by a constant depending only on `Λ`.

Indeed the largest index `m` of `S` satisfies `⌊a m⌋ θ < 2`, and `a m ≥ 1` forces `θ < 2`, so
`a m θ < 4`.  Writing `r = Λ⁻¹ < 1`, lacunarity gives `a n ≤ r^{m - n} · a m`, hence
`⌊a n⌋ θ ≤ 4 r^{m - n}`; the `m - n`, `n ∈ S`, are distinct elements of `{0, …, m}`, so the sum is
at most `4 ∑_{j ≤ m} r^j ≤ 4 / (1 - r)`. -/
theorem lacGeomSumBound (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : ℕ → NNReal), PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      ∀ (θ : ℝ) (S : Finset ℕ),
        (∀ n ∈ S, (Nat.floor (a n) : ℝ) * θ < 2) →
        ∑ n ∈ S, (Nat.floor (a n) : ℝ) * θ ≤ C := by
  refine ⟨4 * (1 - (Λ : ℝ)⁻¹)⁻¹ + 1, ?_, ?_⟩
  · have hL : (1 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
    have hpos : (0 : ℝ) < 1 - (Λ : ℝ)⁻¹ := by
      have h := inv_lt_one_of_one_lt₀ hL
      linarith
    have hpos2 : (0 : ℝ) < 4 * (1 - (Λ : ℝ)⁻¹)⁻¹ := by
      have := inv_pos.mpr hpos
      linarith
    linarith
  · intro a ha ha1 θ S hS
    have hC : (0 : ℝ) < 4 * (1 - (Λ : ℝ)⁻¹)⁻¹ + 1 := by
      have hL : (1 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
      have hpos : (0 : ℝ) < 1 - (Λ : ℝ)⁻¹ := by
        have h := inv_lt_one_of_one_lt₀ hL
        linarith
      have := inv_pos.mpr hpos
      linarith
    have hL : (1 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
    have hL0 : (0 : ℝ) < (Λ : ℝ) := by linarith
    have hr0 : (0 : ℝ) < (Λ : ℝ)⁻¹ := inv_pos.mpr hL0
    have hr1 : (Λ : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hL
    have hq : ‖(Λ : ℝ)⁻¹‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr1
    rcases Finset.eq_empty_or_nonempty S with rfl | hne
    · rw [show (∑ n ∈ (∅ : Finset ℕ), (Nat.floor (a n) : ℝ) * θ) = 0 by simp]
      linarith
    · set m : ℕ := S.max' hne with hm
      have hm_mem : m ∈ S := by rw [hm]; exact S.max'_mem hne
      have hle : ∀ n ∈ S, n ≤ m := by
        intro n hn; rw [hm]; exact S.le_max' n hn
      have hgr : ∀ n, Λ * a n ≤ a (n + 1) := lacunary_growth_step Λ a ha ha1
      have hpow := lacunary_growth_pow Λ a hgr
      -- `θ < 2`
      have hθ2 : θ < 2 := by
        rcases le_or_gt θ 0 with h | h
        · linarith
        · have hfl1 : 1 ≤ Nat.floor (a m) := by
            have h1 : ((1 : ℕ) : NNReal) ≤ a m := by simpa using ha1 m
            exact Nat.le_floor h1
          have hcast : (1 : ℝ) ≤ (Nat.floor (a m) : ℝ) := by exact_mod_cast hfl1
          have hmul : θ ≤ (Nat.floor (a m) : ℝ) * θ := by
            have h2 : (1 : ℝ) * θ ≤ (Nat.floor (a m) : ℝ) * θ :=
              mul_le_mul_of_nonneg_right hcast h.le
            simpa using h2
          linarith [hS m hm_mem]
      -- `(a m) θ < 4`
      have h4 : (a m : ℝ) * θ < 4 := by
        have ham_lt : (a m : ℝ) < (Nat.floor (a m) : ℝ) + 1 := by
          have h := Nat.lt_floor_add_one (a m)
          exact_mod_cast h
        rcases le_or_gt θ 0 with h | h
        · have h1 : (a m : ℝ) * θ ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (by positivity) h
          linarith
        · have h1 : (a m : ℝ) * θ < ((Nat.floor (a m) : ℝ) + 1) * θ :=
            mul_lt_mul_of_pos_right ham_lt h
          have h2 : ((Nat.floor (a m) : ℝ) + 1) * θ < 4 := by
            have := hS m hm_mem
            nlinarith [this, hθ2]
          linarith
      -- the termwise bound
      have hterm : ∀ n ∈ S, (Nat.floor (a n) : ℝ) * θ ≤ 4 * (Λ : ℝ)⁻¹ ^ (m - n) := by
        intro n hn
        have hfl : (Nat.floor (a n) : ℝ) ≤ (a n : ℝ) := by
          have h := Nat.floor_le (show (0 : NNReal) ≤ a n by positivity)
          exact_mod_cast h
        rcases le_or_gt θ 0 with hθ | hθ
        · have h1 : (Nat.floor (a n) : ℝ) * θ ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hθ
          have h2 : (0 : ℝ) ≤ 4 * (Λ : ℝ)⁻¹ ^ (m - n) := by positivity
          linarith
        · have hnle : n ≤ m := hle n hn
          have hp : (Λ : ℝ) ^ (m - n) * (a n : ℝ) ≤ (a m : ℝ) := by
            have h := hpow n (m - n)
            rw [Nat.add_sub_of_le hnle] at h
            exact h
          have hmul : (Λ : ℝ) ^ (m - n) * ((a n : ℝ) * θ) ≤ (a m : ℝ) * θ := by
            have := mul_le_mul_of_nonneg_right hp hθ.le
            simpa only [mul_assoc] using this
          have hLpos' : (0 : ℝ) < (Λ : ℝ) ^ (m - n) := pow_pos hL0 _
          have hlt : (a n : ℝ) * θ < 4 * (Λ : ℝ)⁻¹ ^ (m - n) := by
            have hrew : 4 * (Λ : ℝ)⁻¹ ^ (m - n) = 4 / (Λ : ℝ) ^ (m - n) := by
              rw [div_eq_mul_inv, inv_pow]
            rw [hrew, lt_div_iff₀ hLpos']
            have hmul' : (Λ : ℝ) ^ (m - n) * ((a n : ℝ) * θ) < 4 := lt_of_le_of_lt hmul h4
            nlinarith [hmul']
          have : (Nat.floor (a n) : ℝ) * θ ≤ (a n : ℝ) * θ :=
            mul_le_mul_of_nonneg_right hfl hθ.le
          linarith [this, hlt]
      have hsum1 : ∑ n ∈ S, (Nat.floor (a n) : ℝ) * θ
          ≤ 4 * ∑ n ∈ S, (Λ : ℝ)⁻¹ ^ (m - n) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum hterm
      have hinj : Set.InjOn (fun n => m - n) (↑S : Set ℕ) := by
        intro x hx y hy hxy
        simp only [Finset.mem_coe] at hx hy
        have hxy' : m - x = m - y := hxy
        have hx' : x ≤ m := hle x hx
        have hy' : y ≤ m := hle y hy
        omega
      have himg : ∑ n ∈ S, (Λ : ℝ)⁻¹ ^ (m - n)
          = ∑ j ∈ S.image (fun n => m - n), (Λ : ℝ)⁻¹ ^ j :=
        (Finset.sum_image hinj).symm
      have hsub : S.image (fun n => m - n) ⊆ Finset.range (m + 1) := by
        intro j hj
        rcases Finset.mem_image.mp hj with ⟨n, hn, rfl⟩
        rw [Finset.mem_range]
        exact Nat.lt_succ_of_le (Nat.sub_le m n)
      have hsum2 : ∑ j ∈ S.image (fun n => m - n), (Λ : ℝ)⁻¹ ^ j
          ≤ ∑ j ∈ Finset.range (m + 1), (Λ : ℝ)⁻¹ ^ j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => pow_nonneg hr0.le j)
      have hsum3 : ∑ j ∈ Finset.range (m + 1), (Λ : ℝ)⁻¹ ^ j
          ≤ ∑' j : ℕ, (Λ : ℝ)⁻¹ ^ j :=
        Summable.sum_le_tsum (Finset.range (m + 1)) (fun j _ => pow_nonneg hr0.le j)
          (summable_geometric_of_norm_lt_one hq)
      have htsum : ∑' j : ℕ, (Λ : ℝ)⁻¹ ^ j = (1 - (Λ : ℝ)⁻¹)⁻¹ :=
        tsum_geometric_of_norm_lt_one hq
      calc ∑ n ∈ S, (Nat.floor (a n) : ℝ) * θ
          ≤ 4 * ∑ n ∈ S, (Λ : ℝ)⁻¹ ^ (m - n) := hsum1
        _ = 4 * ∑ j ∈ S.image (fun n => m - n), (Λ : ℝ)⁻¹ ^ j := by rw [himg]
        _ ≤ 4 * ∑ j ∈ Finset.range (m + 1), (Λ : ℝ)⁻¹ ^ j :=
              mul_le_mul_of_nonneg_left hsum2 (by norm_num)
        _ ≤ 4 * ∑' j : ℕ, (Λ : ℝ)⁻¹ ^ j :=
              mul_le_mul_of_nonneg_left hsum3 (by norm_num)
        _ = 4 * (1 - (Λ : ℝ)⁻¹)⁻¹ := by rw [htsum]
        _ ≤ 4 * (1 - (Λ : ℝ)⁻¹)⁻¹ + 1 := by linarith

end Work.KMTPlan.A6
