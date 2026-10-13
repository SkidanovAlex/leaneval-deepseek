import Mathlib
import Submission.Work.WilC5.Values
import Submission.Work.WilC5.ValueOrder
import Submission.Work.WilC5.ValuesLemmas
import Submission.Work.WilC5.ValArith

namespace Work.WilC5.CutCompAux

open Work.WilC5

/-- **The min rule at the cut.**  In the standard real valuation of an ordered field, if `L` and `a`
lie in *different* archimedean classes, then `L + k·a` (with `k ≠ 0` an integer) has value at most
that of `a`: the summands have distinct values, so the value of the sum is the minimum of the two,
and `k·a` has the value of `a`.

This is the form of the min rule consumed by `CutComp`: the "error term" `log z + (N m)·β` whose
value must be compared with `X (m+1)` is precisely such a sum, and we only ever need the inequality
`v(...) ≤ v(X (m+1))` in one direction (or, after swapping the value classes, the reverse
inequality by the very same lemma applied to `-L`). -/
theorem CutComp_VLe_add_intCast_mul {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {a L : K} {k : ℤ} (hk : k ≠ 0) (h : ¬ Work.WilC5.SameArch L a) :
    Work.WilC5.VLe (L + (k : K) * a) a := by
  -- `L` and `a` have different values, so at most one of the two `VLe` directions can hold.
  have hnot : ¬ (VLe L a ∧ VLe a L) :=
    fun hc => h ((SameArch_iff_VLe L a).mpr hc)
  rcases VLe_total L a with hLa | haL
  · -- Case A: `L` dominates `a`, strictly.  Then it also dominates `k·a`, so `L + k·a`
    -- has the value of `L`, whence `v(L + k·a) = v(L) ≤ v(a)`.
    have hLaL : ¬ VLe a L := fun h' => hnot ⟨hLa, h'⟩
    have h1 : VLe L ((k : K) * a) := VLe_intCast_mul_left k hLa
    have h2 : ¬ VLe ((k : K) * a) L := fun hcon =>
      hLaL (VLe_trans (VLe_intCast_mul k a) hcon)
    have h1x : VLe L (-((k : K) * a)) := by rw [VLe_neg_right]; exact h1
    have h2x : ¬ VLe (-((k : K) * a)) L := by rw [VLe_neg_left]; exact h2
    have hsa : SameArch (L - (-((k : K) * a))) L := SameArch_sub_of_VLe_of_not h1x h2x
    rw [sub_neg_eq_add] at hsa
    exact VLe_trans ((SameArch_iff_VLe (L + (k : K) * a) L).mp hsa).1 hLa
  · -- Case B: `a` dominates `L`, strictly.  Then `k·a` (with `k ≠ 0`) also dominates `L`,
    -- so `L + k·a` has the value of `k·a`, whence `v(L + k·a) = v(k·a) = v(a)`.
    have haLL : ¬ VLe L a := fun h' => hnot ⟨h', haL⟩
    have hka : VLe ((k : K) * a) a := VLe_intCast_mul_of_ne hk a
    have h1 : VLe ((k : K) * a) (-L) := by
      rw [VLe_neg_right]; exact VLe_trans hka haL
    have h2 : ¬ VLe (-L) ((k : K) * a) := by
      rw [VLe_neg_left]
      exact fun hcon => haLL (VLe_trans hcon hka)
    have hsa : SameArch (((k : K) * a) - (-L)) ((k : K) * a) :=
      SameArch_sub_of_VLe_of_not h1 h2
    rw [sub_neg_eq_add, add_comm] at hsa
    exact VLe_trans ((SameArch_iff_VLe (L + (k : K) * a) ((k : K) * a)).mp hsa).1 hka

end Work.WilC5.CutCompAux
