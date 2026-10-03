import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finset.Max
import Submission.Commons.Analysis.Sum.lacunary_finset_sum_inv_le

open Finset

/-!
# A lacunary finite-sum bound (forward direction)

This file proves `Commons.Analysis.Sum.lacunary_finset_sum_le`: for a finite set `D` of positive
reals that is `Λ`-lacunary (`Λ * M ≤ N` whenever `M < N` in `D`), the sum of `A * N ^ d` over
those `N ∈ D` with `A * N ^ d ≤ Y` is at most `(1 - (Λ ^ d)⁻¹)⁻¹ * Y`.

This is the companion of `Commons.Analysis.Sum.lacunary_finset_sum_inv_le`: the values
`A * N ^ d` grow geometrically along the lacunary set (`A * N ^ d ≥ Λ ^ d * A * M ^ d` when
`M < N`), so the total mass of all terms below the level `Y` is controlled by `Y` via the
sum of the geometric series `1 + r⁻¹ + r⁻² + …` with `r = Λ ^ d > 1`.
-/

namespace Commons.Analysis.Sum

/-- Elementary arithmetic identity: for `1 < r`, `1 + (1 - r⁻¹)⁻¹ * r⁻¹ = (1 - r⁻¹)⁻¹`. -/
theorem one_add_inv_mul_inv (r : ℝ) (hr : 1 < r) :
    1 + (1 - r⁻¹)⁻¹ * r⁻¹ = (1 - r⁻¹)⁻¹ := by
  have hne : (1 - r⁻¹) ≠ 0 := by
    have h1 : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr
    linarith
  have key : (1 - r⁻¹) * (1 + (1 - r⁻¹)⁻¹ * r⁻¹) = 1 := by
    rw [mul_add, mul_one, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    ring
  have key2 : (1 - r⁻¹) * (1 - r⁻¹)⁻¹ = 1 := mul_inv_cancel₀ hne
  exact mul_left_cancel₀ hne (by rw [key, key2])

/-- Const-bound form of the lacunary forward sum estimate: if every term `A * N ^ d` (`N ∈ S`)
is bounded by a nonnegative constant `B`, then the whole sum is at most
`(1 - (Λ ^ d)⁻¹)⁻¹ * B`.  The proof is by induction on the (finite) set `S`, peeling off its
maximum element: all the remaining elements are at most `max / Λ`, so their contribution loses
a factor `Λ ^ d`. -/
theorem lacunary_sum_le_const {Λ : ℝ} (hΛ : 1 < Λ) (d : ℕ) (hd : 1 ≤ d) (A : ℝ) (hA : 0 < A)
    (S : Finset ℝ) (hpos : ∀ N ∈ S, 0 < N)
    (hlac : ∀ M ∈ S, ∀ N ∈ S, M < N → Λ * M ≤ N)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ N ∈ S, A * N ^ d ≤ B) :
    ∑ N ∈ S, A * N ^ d ≤ (1 - (Λ ^ d)⁻¹)⁻¹ * B := by
  have hd0 : d ≠ 0 := by omega
  have hld1 : 1 < Λ ^ d := one_lt_pow₀ hΛ hd0
  have hc_nonneg : 0 ≤ (1 - (Λ ^ d)⁻¹)⁻¹ :=
    inv_nonneg.mpr (by have h := inv_lt_one_of_one_lt₀ hld1; linarith)
  revert hpos hlac B hB hbound
  induction S using Finset.induction_on_max with
  | empty =>
      intro hpos hlac B hB hbound
      rw [Finset.sum_empty]
      exact mul_nonneg hc_nonneg hB
  | insert a s hlt ih =>
      intro hpos hlac B hB hbound
      have hΛpos : 0 < Λ := lt_trans zero_lt_one hΛ
      have ha_notin : a ∉ s := fun h => absurd (hlt a h) (lt_irrefl a)
      have hapos : 0 < a := hpos a (Finset.mem_insert_self a s)
      have hrrpos : 0 < (Λ ^ d)⁻¹ := inv_pos.mpr (pow_pos hΛpos d)
      have hpos_s : ∀ N ∈ s, 0 < N := fun N hN => hpos N (Finset.mem_insert_of_mem hN)
      have hlac_s : ∀ M ∈ s, ∀ N ∈ s, M < N → Λ * M ≤ N :=
        fun M hM N hN h =>
          hlac M (Finset.mem_insert_of_mem hM) N (Finset.mem_insert_of_mem hN) h
      have hbound_s : ∀ N ∈ s, A * N ^ d ≤ A * a ^ d * (Λ ^ d)⁻¹ := by
        intro N hN
        have hNmem : N ∈ insert a s := Finset.mem_insert_of_mem hN
        have hNpos : 0 < N := hpos N hNmem
        have hNa : N < a := hlt N hN
        have hlac_Na : Λ * N ≤ a := hlac N hNmem a (Finset.mem_insert_self a s) hNa
        have hpow : Λ ^ d * N ^ d ≤ a ^ d := by
          have h := pow_le_pow_left₀ (le_of_lt (mul_pos hΛpos hNpos)) hlac_Na d
          rwa [mul_pow] at h
        have hNd : N ^ d ≤ a ^ d * (Λ ^ d)⁻¹ := by
          have h := mul_le_mul_of_nonneg_left hpow (le_of_lt hrrpos)
          rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (pow_pos hΛpos d)), one_mul] at h
          rwa [mul_comm] at h
        calc A * N ^ d ≤ A * (a ^ d * (Λ ^ d)⁻¹) := mul_le_mul_of_nonneg_left hNd (le_of_lt hA)
          _ = A * a ^ d * (Λ ^ d)⁻¹ := by ring
      have hB'' : 0 ≤ A * a ^ d * (Λ ^ d)⁻¹ :=
        mul_nonneg (mul_nonneg (le_of_lt hA) (pow_nonneg (le_of_lt hapos) d)) (le_of_lt hrrpos)
      have hs := ih hpos_s hlac_s (A * a ^ d * (Λ ^ d)⁻¹) hB'' hbound_s
      have hbound_aa : A * a ^ d ≤ B := hbound a (Finset.mem_insert_self a s)
      calc ∑ N ∈ insert a s, A * N ^ d
          = A * a ^ d + ∑ N ∈ s, A * N ^ d := Finset.sum_insert ha_notin
        _ ≤ A * a ^ d + (1 - (Λ ^ d)⁻¹)⁻¹ * (A * a ^ d * (Λ ^ d)⁻¹) :=
              add_le_add le_rfl hs
        _ = A * a ^ d * (1 + (1 - (Λ ^ d)⁻¹)⁻¹ * (Λ ^ d)⁻¹) := by ring
        _ = A * a ^ d * (1 - (Λ ^ d)⁻¹)⁻¹ := by rw [one_add_inv_mul_inv (Λ ^ d) hld1]
        _ ≤ B * (1 - (Λ ^ d)⁻¹)⁻¹ := mul_le_mul_of_nonneg_right hbound_aa hc_nonneg
        _ = (1 - (Λ ^ d)⁻¹)⁻¹ * B := by ring

theorem lacunary_finset_sum_le
    {Λ : ℝ} (hΛ : 1 < Λ) (d : ℕ) (hd : 1 ≤ d) (A : ℝ) (hA : 0 < A)
    (D : Finset ℝ) (hpos : ∀ N ∈ D, 0 < N)
    (hlac : ∀ M ∈ D, ∀ N ∈ D, M < N → Λ * M ≤ N)
    (Y : ℝ) (hY : 0 < Y) :
    ∑ N ∈ D.filter (fun N => A * N ^ d ≤ Y), A * N ^ d ≤ (1 - (Λ ^ d)⁻¹)⁻¹ * Y := by
  have hposS : ∀ N ∈ D.filter (fun N => A * N ^ d ≤ Y), 0 < N :=
    fun N hN => hpos N (Finset.mem_filter.mp hN).1
  have hlacS : ∀ M ∈ D.filter (fun N => A * N ^ d ≤ Y),
      ∀ N ∈ D.filter (fun N => A * N ^ d ≤ Y), M < N → Λ * M ≤ N :=
    fun M hM N hN h => hlac M (Finset.mem_filter.mp hM).1 N (Finset.mem_filter.mp hN).1 h
  have hboundS : ∀ N ∈ D.filter (fun N => A * N ^ d ≤ Y), A * N ^ d ≤ Y :=
    fun N hN => (Finset.mem_filter.mp hN).2
  exact lacunary_sum_le_const hΛ d hd A hA _ hposS hlacS Y (le_of_lt hY) hboundS

end Commons.Analysis.Sum