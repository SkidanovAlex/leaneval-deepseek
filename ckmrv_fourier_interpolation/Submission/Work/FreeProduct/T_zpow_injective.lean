import Mathlib
import Submission.Work.FreeProduct.Basic
import Submission.Work.FreeProduct.Length

/-!
# `T` has infinite order in `ℤ/2 ∗ ℤ/3`

The element `T = x * y` of `FP = ℤ/2 ∗ ℤ/3` (with `x` the generator of the `ℤ/2` factor and
`y` that of the `ℤ/3` factor) has infinite order, so `n ↦ T ^ n` is injective on `ℤ`.

The proof is the length calculus of `Work.FreeProduct.Length`: the reduced word of the product
of two letters lying in *different* factors prepends both letters, and the resulting word again
starts in the first of the two factors.  Consequently the reduced word of `T ^ n` has length
`2 n`, and `T ^ k ≠ 1` for every `k > 0`.
-/

namespace Work.FreeProduct

open Work.Modular.PresGroup
open scoped MonoidAlgebra

noncomputable section

/-- Prepending a letter to a word whose first letter lies in a *different* factor makes that
letter the first letter of the reduced word. -/
theorem fstIdx_smul_of_fstIdx_ne {i : Bool} (m : Cyc i) (w : W) (hm : m ≠ 1)
    (h : w.fstIdx ≠ some i) : (Monoid.CoprodI.of m • w).fstIdx = some i := by
  rw [← Monoid.CoprodI.Word.cons_eq_smul]
  exact Monoid.CoprodI.Word.fstIdx_cons m w h hm

/-- Left multiplication by the product `of a * of b` of two non-identity letters in *different*
factors simply prepends both letters. -/
theorem toList_mul_smul (a b : Letter) (hab : a.1 ≠ b.1) (ha : a.2 ≠ 1) (hb : b.2 ≠ 1)
    (w : W) (h : w.fstIdx ≠ some b.1) :
    ((Monoid.CoprodI.of a.2 * Monoid.CoprodI.of b.2) • w).toList
      = a :: b :: w.toList := by
  have h1 : (Monoid.CoprodI.of b.2 • w).fstIdx = some b.1 :=
    fstIdx_smul_of_fstIdx_ne b.2 w hb h
  rw [mul_smul,
    toList_smul_of_fstIdx_ne a.2 _ ha (by rw [h1]; exact fun hh => hab (Option.some.inj hh).symm),
    toList_smul_of_fstIdx_ne b.2 w hb h]

/-- The reduced word of `of a * of b • w` starts in the factor of `a`. -/
theorem fstIdx_mul_smul (a b : Letter) (hab : a.1 ≠ b.1) (ha : a.2 ≠ 1) (hb : b.2 ≠ 1)
    (w : W) (h : w.fstIdx ≠ some b.1) :
    ((Monoid.CoprodI.of a.2 * Monoid.CoprodI.of b.2) • w).fstIdx = some a.1 := by
  rw [mul_smul]
  exact fstIdx_smul_of_fstIdx_ne a.2 _ ha
    (by rw [fstIdx_smul_of_fstIdx_ne b.2 w hb h];
        exact fun hh => hab (Option.some.inj hh).symm)

/-- Left multiplication by `of a * of b` increases the length by exactly two. -/
theorem wlen_mul_smul (a b : Letter) (hab : a.1 ≠ b.1) (ha : a.2 ≠ 1) (hb : b.2 ≠ 1)
    (w : W) (h : w.fstIdx ≠ some b.1) :
    wlen ((Monoid.CoprodI.of a.2 * Monoid.CoprodI.of b.2) • w) = wlen w + 2 := by
  have h1 : (Monoid.CoprodI.of b.2 • w).fstIdx = some b.1 :=
    fstIdx_smul_of_fstIdx_ne b.2 w hb h
  simp only [wlen, mul_smul]
  rw [toList_smul_of_fstIdx_ne a.2 _ ha (by rw [h1]; exact fun hh => hab (Option.some.inj hh).symm),
    toList_smul_of_fstIdx_ne b.2 w hb h]
  simp

/-- **The reduced word of `(of a * of b) ^ n` has length `2 n`.**  The second component is the
invariant needed to run the induction: the word always starts in the factor of `b`. -/
theorem wlen_mul_pow (a b : Letter) (hab : a.1 ≠ b.1) (ha : a.2 ≠ 1) (hb : b.2 ≠ 1) (n : ℕ) :
    wlen (Monoid.CoprodI.Word.equiv ((Monoid.CoprodI.of a.2 * Monoid.CoprodI.of b.2) ^ n))
      = 2 * n ∧
    (Monoid.CoprodI.Word.equiv ((Monoid.CoprodI.of a.2 * Monoid.CoprodI.of b.2) ^ n)).fstIdx
      ≠ some b.1 := by
  induction n with
  | zero =>
    rw [pow_zero, equiv_one]
    refine ⟨?_, ?_⟩
    · simp [wlen, Monoid.CoprodI.Word.empty]
    · rw [fstIdx_empty]; exact fun h => nomatch h
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [pow_succ', equiv_mul]
    refine ⟨?_, ?_⟩
    · rw [wlen_mul_smul a b hab ha hb _ ih2, ih1]; ring
    · rw [fstIdx_mul_smul a b hab ha hb _ ih2]
      exact fun h => hab (Option.some.inj h)

/-- The length of `T ^ n` is `2 n`. -/
theorem elen_T_pow (n : ℕ) : elen (T ^ n) = 2 * n :=
  (wlen_mul_pow Lx Ly (by decide) (by decide) (by decide) n).1

/-- `T` has infinite order: no positive power of `T` is trivial. -/
theorem T_pow_ne_one {k : ℕ} (hk : 0 < k) : T ^ k ≠ 1 := by
  intro h
  have h1 : elen (T ^ k) = 2 * k := elen_T_pow k
  rw [h, elen_one] at h1
  omega

theorem zpow_eq_of_le {m n : ℤ} (hle : m ≤ n) (h : T ^ m = T ^ n) : m = n := by
  have hsub : T ^ (n - m) = 1 := by rw [zpow_sub, ← h, mul_inv_cancel]
  have hk : n - m = ((n - m).toNat : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
  rw [hk, zpow_natCast] at hsub
  have h0 : (n - m).toNat = 0 := by
    by_contra hne
    exact T_pow_ne_one (Nat.pos_of_ne_zero hne) hsub
  have hz : n - m = 0 := by rw [hk, h0]; norm_num
  omega

theorem T_zpow_injective : Function.Injective (fun n : ℤ => Work.FreeProduct.T ^ n) := by
  intro m n hmn
  rcases le_total m n with hle | hle
  · exact zpow_eq_of_le hle hmn
  · exact (zpow_eq_of_le hle hmn.symm).symm

end

end Work.FreeProduct
