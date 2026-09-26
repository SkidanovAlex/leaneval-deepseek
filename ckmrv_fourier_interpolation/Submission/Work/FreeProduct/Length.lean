import Mathlib
import Submission.Work.FreeProduct.Basic

/-!
# The length calculus on reduced words

Length bounds and exact computations for left multiplication on `FP = ℤ/2 ∗ ℤ/3`.
-/

namespace Work.FreeProduct

open Work.Modular.PresGroup
open scoped MonoidAlgebra

noncomputable section

/-- Prepending a letter to a reduced word whose first letter lies in a *different* factor just
prepends it. -/
theorem toList_smul_of_fstIdx_ne {i : Bool} (m : Cyc i) (w : W) (hm : m ≠ 1)
    (h : w.fstIdx ≠ some i) :
    (Monoid.CoprodI.of m • w).toList = ⟨i, m⟩ :: w.toList := by
  rw [← Monoid.CoprodI.Word.cons_eq_smul]
  exact Monoid.CoprodI.Word.cons_toList m w h hm

/-- Prepending a letter in the *same* factor as the first letter of the word: the two letters
are multiplied in that factor. -/
theorem smul_cons_same {i : Bool} (m m' : Cyc i) (t : W)
    (h1 : t.fstIdx ≠ some i) (h2 : m' ≠ 1) :
    Monoid.CoprodI.of m • Monoid.CoprodI.Word.cons m' t h1 h2
      = Monoid.CoprodI.of (m * m') • t := by
  rw [Monoid.CoprodI.Word.cons_eq_smul, ← mul_smul, ← map_mul]

/-- Every nonempty reduced word whose first letter lies in the factor `i` is a `cons`. -/
theorem exists_cons_of_fstIdx_eq {i : Bool} {w : W} (h : w.fstIdx = some i) :
    ∃ (m : Cyc i) (t : W) (h1 : t.fstIdx ≠ some i) (hm : m ≠ 1),
      w = Monoid.CoprodI.Word.cons m t h1 hm := by
  induction w using Monoid.CoprodI.Word.consRecOn with
  | empty => simp [Monoid.CoprodI.Word.fstIdx, Monoid.CoprodI.Word.empty] at h
  | cons j m t h1 hm _ =>
    rw [Monoid.CoprodI.Word.fstIdx_cons] at h
    obtain rfl : j = i := Option.some.inj h
    exact ⟨m, t, h1, hm, rfl⟩

theorem wlen_cons {i : Bool} (m : Cyc i) (t : W) (h1 : t.fstIdx ≠ some i) (hm : m ≠ 1) :
    wlen (Monoid.CoprodI.Word.cons m t h1 hm) = wlen t + 1 := rfl

theorem fstIdx_empty : (Monoid.CoprodI.Word.empty : W).fstIdx = none := rfl

/-- Prepending one letter increases the length by at most one. -/
theorem wlen_smul_le {i : Bool} (m : Cyc i) (w : W) :
    wlen (Monoid.CoprodI.of m • w) ≤ wlen w + 1 := by
  revert m
  induction w using Monoid.CoprodI.Word.consRecOn with
  | empty =>
    intro m
    by_cases hm : m = 1
    · subst hm
      rw [map_one, one_smul]
      simp [wlen, Monoid.CoprodI.Word.empty]
    · rw [wlen, toList_smul_of_fstIdx_ne m _ hm (by rw [fstIdx_empty]; exact fun h => nomatch h)]
      simp [wlen, Monoid.CoprodI.Word.empty]
  | cons j m' t h1 h2 ih =>
    intro m
    by_cases hji : j = i
    · subst hji
      rw [smul_cons_same]
      by_cases hmm : m * m' = 1
      · rw [hmm, map_one, one_smul, wlen_cons m' t h1 h2]
        omega
      · calc wlen (Monoid.CoprodI.of (m * m') • t) ≤ wlen t + 1 := ih (m * m')
          _ ≤ wlen (Monoid.CoprodI.Word.cons m' t h1 h2) + 1 := by
              rw [wlen_cons m' t h1 h2]; omega
    · have hf : (Monoid.CoprodI.Word.cons m' t h1 h2).fstIdx = some j :=
        Monoid.CoprodI.Word.fstIdx_cons m' t h1 h2
      have hne : (Monoid.CoprodI.Word.cons m' t h1 h2).fstIdx ≠ some i := by
        intro hc; exact hji (Option.some.inj (hf.symm.trans hc))
      by_cases hm1 : m = 1
      · rw [hm1, map_one, one_smul]; omega
      · rw [wlen, toList_smul_of_fstIdx_ne m _ hm1 hne]
        simp only [wlen, List.length_cons]
        omega

/-- Prepending a letter raises the length exactly by one if the first letter of the word is in a
different factor. -/
theorem wlen_smul_of_fstIdx_ne {i : Bool} (m : Cyc i) (w : W) (hm : m ≠ 1)
    (h : w.fstIdx ≠ some i) :
    wlen (Monoid.CoprodI.of m • w) = wlen w + 1 := by
  rw [wlen, wlen, toList_smul_of_fstIdx_ne m w hm h]
  rfl

/-- Left multiplication by a list of letters increases the length by at most the length of the
list. -/
theorem wlen_toProd_smul_le (L : List Letter) (w : W) :
    wlen (toProd L • w) ≤ wlen w + L.length := by
  induction L with
  | nil => simp [toProd_nil]
  | cons a l ih =>
    rw [toProd_cons, mul_smul]
    calc wlen (Monoid.CoprodI.of a.2 • (toProd l • w))
        ≤ wlen (toProd l • w) + 1 := wlen_smul_le a.2 _
      _ ≤ (wlen w + l.length) + 1 := by omega
      _ = wlen w + (l.length + 1) := by ring

/-- Left multiplication by a group element increases the length by at most the length of the
element. -/
theorem wlen_smul_of_le (g : FP) (w : W) :
    wlen (g • w) ≤ wlen w + elen g := by
  have hg : g = toProd (Monoid.CoprodI.Word.equiv g).toList := by
    rw [toProd]; exact (prod_equiv g).symm
  conv_lhs => rw [hg]
  exact wlen_toProd_smul_le _ _

theorem wlen_equiv (g : FP) : wlen (Monoid.CoprodI.Word.equiv g) = elen g := rfl

/-- The length is subadditive. -/
theorem elen_mul_le (g z : FP) : elen (g * z) ≤ elen g + elen z := by
  show wlen (Monoid.CoprodI.Word.equiv (g * z)) ≤ elen g + elen z
  rw [equiv_mul]
  have h := wlen_smul_of_le g (Monoid.CoprodI.Word.equiv z)
  rw [wlen_equiv z] at h
  linarith

end

end Work.FreeProduct
