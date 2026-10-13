import Mathlib
import Submission.Work.WilE5.Sys

namespace Work.WilE5.Cells

/-!
  The test order `testLt` is a strict total order: it compares first the source index `i`, then
  the total degree `mSum m`, then the exponent list lexicographically (`mlexLtAux`), and finally
  the peeled direction `l`.  Antisymmetry of the *last* two stages is what this file provides:

  * `mlexLtAux_eq_of_eq_false` — the auxiliary lexicographic comparison on exponent lists is
    antisymmetric (two lists that are `<` in neither direction coincide);
  * `testLt_trichotomy` — consequently `¬ testLt t t'` and `¬ testLt t' t` force `t = t'`.
-/

/-- `mlexLtAux` is antisymmetric: two lists that are not `<` in either direction are equal.
(For lists of the same length this is exactly the totality of the lexicographic order; for lists
of different lengths one of the two comparisons is automatically `true`, so no length hypothesis
is needed.) -/
theorem mlexLtAux_eq_of_eq_false : ∀ (a b : List ℕ), Work.WilE5.mlexLtAux a b = false →
    Work.WilE5.mlexLtAux b a = false → a = b := by
  intro a
  induction a with
  | nil =>
    intro b h1 h2
    cases b with
    | nil => rfl
    | cons y ys => simp [Work.WilE5.mlexLtAux] at h1
  | cons x xs ih =>
    intro b h1 h2
    cases b with
    | nil => simp [Work.WilE5.mlexLtAux] at h2
    | cons y ys =>
      simp only [Work.WilE5.mlexLtAux] at h1 h2
      by_cases hxy : x < y
      · rw [if_pos hxy] at h1
        exact Bool.noConfusion h1
      · by_cases hyx : y < x
        · rw [if_pos hyx] at h2
          exact Bool.noConfusion h2
        · rw [if_neg hxy, if_neg hyx] at h1
          rw [if_neg hyx, if_neg hxy] at h2
          have hxy' : x = y := by omega
          rw [hxy', ih ys h1 h2]

theorem testLt_trichotomy {q : ℕ} {t t' : Work.WilE5.Test q}
    (h1 : Work.WilE5.testLt t t' = false) (h2 : Work.WilE5.testLt t' t = false) : t = t' := by
  -- stage 1: the source indices agree
  have hi : t.i = t'.i := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have ht : Work.WilE5.testLt t t' = true := by
        simp only [Work.WilE5.testLt]
        rw [if_pos h]
      rw [ht] at h1
      exact Bool.noConfusion h1
    · have ht : Work.WilE5.testLt t' t = true := by
        simp only [Work.WilE5.testLt]
        rw [if_pos h]
      rw [ht] at h2
      exact Bool.noConfusion h2
  have hni : ¬ t.i < t'.i := by omega
  have hni' : ¬ t'.i < t.i := by omega
  simp only [Work.WilE5.testLt] at h1 h2
  rw [if_neg hni, if_neg hni'] at h1
  rw [if_neg hni', if_neg hni] at h2
  -- stage 2: the total degrees agree
  have hm1 : ¬ Work.WilE5.mSum t.m < Work.WilE5.mSum t'.m := by
    intro h
    rw [if_pos h] at h1
    exact Bool.noConfusion h1
  have hm2 : ¬ Work.WilE5.mSum t'.m < Work.WilE5.mSum t.m := by
    intro h
    rw [if_pos h] at h2
    exact Bool.noConfusion h2
  rw [if_neg hm1, if_neg hm2] at h1
  rw [if_neg hm2, if_neg hm1] at h2
  -- stage 3: the exponent lists are lexicographically incomparable, hence equal
  have hml1 : Work.WilE5.mlexLtAux (List.ofFn t.m) (List.ofFn t'.m) = false := by
    by_contra hc
    rw [Bool.not_eq_false] at hc
    rw [if_pos hc] at h1
    exact Bool.noConfusion h1
  have hml2 : Work.WilE5.mlexLtAux (List.ofFn t'.m) (List.ofFn t.m) = false := by
    by_contra hc
    rw [Bool.not_eq_false] at hc
    rw [if_pos hc] at h2
    exact Bool.noConfusion h2
  rw [if_neg (by rw [hml1]; exact Bool.false_ne_true),
      if_neg (by rw [hml2]; exact Bool.false_ne_true)] at h1
  rw [if_neg (by rw [hml2]; exact Bool.false_ne_true),
      if_neg (by rw [hml1]; exact Bool.false_ne_true)] at h2
  -- stage 4: the peeled directions agree
  have hl1 : ¬ t.l < t'.l := of_decide_eq_false h1
  have hl2 : ¬ t'.l < t.l := of_decide_eq_false h2
  have hl : t.l = t'.l := by omega
  have hm : t.m = t'.m := List.ofFn_inj.mp (mlexLtAux_eq_of_eq_false _ _ hml1 hml2)
  obtain ⟨i, m, l⟩ := t
  obtain ⟨i', m', l'⟩ := t'
  simp_all

end Work.WilE5.Cells
