import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- For an integer `k`, the natural absolute value splits as the sum of the nonnegative
part of `k` and the nonnegative part of `-k`. -/
private lemma natAbs_eq_toNat_add_toNat_neg (k : ℤ) : k.natAbs = k.toNat + (-k).toNat := by
  have h1 : ((k.natAbs : ℤ) = (k.toNat : ℤ) + ((-k).toNat : ℤ)) := by
    rcases lt_or_ge 0 k with hk | hk
    · rw [Int.natAbs_of_nonneg (le_of_lt hk), Int.toNat_of_nonneg (le_of_lt hk),
        Int.toNat_of_nonpos (by omega)]
      ring
    · rw [Int.ofNat_natAbs_of_nonpos hk, Int.toNat_of_nonpos hk,
        Int.toNat_of_nonneg (by omega)]
      ring
  exact_mod_cast h1

/-
Key algebraic identity underlying the characterization of the characteristic polynomial.

Writing `A = ∏ i, z i ^ (k i).toNat`, `B = ∏ i, z i ^ (-(k i)).toNat`,
`C = ∏ i, z i ^ (k i).natAbs` and `D = ∏ i, z i ^ (k i)` (integer powers), the two per-index
identities `k.natAbs = k.toNat + (-k).toNat` and `k = k.toNat - (-k).toNat` give `C = A * B`
and `D = A / B` (using `z i ≠ 0`), whence `C * (D - 1) = A * B * (A / B - 1) = A * (A - B)`.
-/
theorem charPoly_algebra {N : ℕ} (z : Fin N → ℂ) (k : Fin N → ℤ) (hz : ∀ i, z i ≠ 0) :
    (∏ i : Fin N, z i ^ ((k i).toNat)) *
        ((∏ i : Fin N, z i ^ ((k i).toNat)) - (∏ i : Fin N, z i ^ ((-(k i)).toNat)))
      = (∏ i : Fin N, z i ^ ((k i).natAbs)) *
        ((∏ i : Fin N, z i ^ (k i)) - 1) := by
  have hnat : ∀ i : Fin N, (k i).natAbs = (k i).toNat + (-(k i)).toNat :=
    fun i => natAbs_eq_toNat_add_toNat_neg (k i)
  -- `C = A * B`
  have hC : (∏ i : Fin N, z i ^ ((k i).natAbs)) =
      (∏ i : Fin N, z i ^ ((k i).toNat)) * (∏ i : Fin N, z i ^ ((-(k i)).toNat)) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => by rw [hnat i, pow_add])
  -- `D = A / B`
  have hD : (∏ i : Fin N, z i ^ (k i)) =
      (∏ i : Fin N, z i ^ ((k i).toNat)) / (∏ i : Fin N, z i ^ ((-(k i)).toNat)) := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    conv_lhs => rw [← Int.toNat_sub_toNat_neg (k i)]
    rw [zpow_sub₀ (hz i), zpow_natCast, zpow_natCast]
  have hB : (∏ i : Fin N, z i ^ ((-(k i)).toNat)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i _
    exact pow_ne_zero _ (hz i)
  rw [hC, hD]
  field_simp

end Work.BW
