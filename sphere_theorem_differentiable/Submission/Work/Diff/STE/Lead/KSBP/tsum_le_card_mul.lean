import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.KSBP

/-- If `f : (Fin n → ℤ) → ℝ` is supported in the box `{m | ∀ i, |m i| ≤ K}` and is bounded
above by `B`, then the (finite) sum of `f` over all of `Fin n → ℤ` is at most `(2K+1)^n * B`.

Indeed the support is contained in the `piFinset` of the intervals `[-K, K]`, which has exactly
`(2K+1)^n` elements, and each term is at most `B`. -/
theorem tsum_le_card_mul {n K : ℕ} {f : (Fin n → ℤ) → ℝ} {B : ℝ}
    (hsupp : ∀ m : Fin n → ℤ, f m ≠ 0 → ∀ i : Fin n, |m i| ≤ (K : ℤ))
    (hB : ∀ m : Fin n → ℤ, f m ≤ B) :
    ∑' m : Fin n → ℤ, f m ≤ (2 * K + 1) ^ n * B := by
  classical
  set S : Finset (Fin n → ℤ) :=
    Fintype.piFinset (fun _ : Fin n => Finset.Icc (-(K : ℤ)) (K : ℤ)) with hS
  -- The box has exactly `(2K+1)^n` elements.
  have hcard : S.card = (2 * K + 1) ^ n := by
    rw [hS, Fintype.card_piFinset]
    simp only [Int.card_Icc]
    rw [Finset.prod_const]
    simp only [Finset.card_univ, Fintype.card_fin]
    have h : (((K : ℤ) + 1 - (-(K : ℤ))).toNat) = 2 * K + 1 := by omega
    rw [h]
  -- `f` vanishes off the box.
  have hzero : ∀ m ∉ S, f m = 0 := by
    intro m hm
    by_contra hne
    apply hm
    rw [hS, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    exact abs_le.mp (hsupp m hne i)
  rw [tsum_eq_sum hzero]
  calc Finset.sum S f ≤ Finset.sum S (fun _ => B) := Finset.sum_le_sum (fun m _ => hB m)
    _ = (S.card : ℝ) * B := by simp [Finset.sum_const, nsmul_eq_mul]
    _ = (2 * K + 1) ^ n * B := by rw [hcard]; push_cast; ring

end Work.Diff.STE.Lead.KSBP
