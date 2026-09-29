/-
# `merge`/`msort` sort by the first component

`Work.Cert.CJ2.msort` is the fuel-carrying merge sort used by the conjunct-2 certificate: it splits
a list into halves `xs.take (xs.length / 2)`, `xs.drop (xs.length / 2)` and merges the recursively
sorted halves with `Work.Cert.CJ2.merge` (whose own recursion is driven by an explicit fuel).

Here we prove that `msort f l` is sorted by the first component as soon as `l.length ≤ 2 ^ f`, i.e.
as soon as the fuel is at least the dyadic logarithm of the length.  The fuel hypothesis is
genuinely needed: with too little fuel `merge` degenerates to `xs ++ ys`.

The development is elementary, by induction on the fuel:
* `mem_merge` (every element of a merge comes from one of the two inputs),
* `merge_sorted` (merge of two sorted lists is sorted, given enough fuel),
* `merge_length`, `msort_length` (both preserve lengths),
* `msort_pairwise` (the induction on the fuel, with the halving estimates `length / 2 ≤ 2 ^ f` and
  `length - length / 2 ≤ 2 ^ f` supplied by `omega`).
-/
import Mathlib
import Submission.Work.Cert.CJ2.Gen

namespace Work.Cert.CJ2Sum

open Work.Cert.CJ2

/-- The comparison by which the certificate sorts: the first components, non-strictly. -/
private def le1 : ℤ × ℤ → ℤ × ℤ → Prop := fun a b => a.1 ≤ b.1

/-- Every element of `merge fuel xs ys` is an element of `xs` or of `ys` (for any fuel). -/
private theorem mem_merge : ∀ (fuel : ℕ) (xs ys : List (ℤ × ℤ)) (a : ℤ × ℤ),
    a ∈ merge fuel xs ys → a ∈ xs ∨ a ∈ ys := by
  intro fuel
  induction fuel with
  | zero => intro xs ys a h; rw [merge.eq_1] at h; exact List.mem_append.mp h
  | succ f ih =>
    intro xs ys a h
    rcases xs with _ | ⟨x, xs⟩
    · rw [merge.eq_2] at h; exact Or.inr h
    · rcases ys with _ | ⟨y, ys⟩
      · rw [show merge (f + 1) (x :: xs) [] = x :: xs from rfl] at h; exact Or.inl h
      · rw [show merge (f + 1) (x :: xs) (y :: ys) =
            if x.1 ≤ y.1 then x :: merge f xs (y :: ys) else y :: merge f (x :: xs) ys from rfl] at h
        split at h
        · rcases List.mem_cons.mp h with h' | h'
          · exact Or.inl (by simp [h'])
          · rcases ih xs (y :: ys) a h' with h'' | h''
            · exact Or.inl (by simp [h''])
            · exact Or.inr (by simp [h''])
        · rcases List.mem_cons.mp h with h' | h'
          · exact Or.inr (by simp [h'])
          · rcases ih (x :: xs) ys a h' with h'' | h''
            · exact Or.inl (by simp [h''])
            · exact Or.inr (by simp [h''])

/-- Merging two sorted lists yields a sorted list, provided the fuel is at least the total length
(so that `merge` follows the comparison-driven recursion all the way down). -/
private theorem merge_sorted : ∀ (fuel : ℕ) (xs ys : List (ℤ × ℤ)),
    xs.length + ys.length ≤ fuel →
    List.Pairwise le1 xs → List.Pairwise le1 ys →
    List.Pairwise le1 (merge fuel xs ys) := by
  intro fuel
  induction fuel with
  | zero =>
    intro xs ys hlen hx hy
    obtain rfl : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [merge.eq_1, List.nil_append]
    exact hy
  | succ f ih =>
    intro xs ys hlen hx hy
    rcases xs with _ | ⟨x, xs⟩
    · rw [merge.eq_2]; exact hy
    · rcases ys with _ | ⟨y, ys⟩
      · rw [show merge (f + 1) (x :: xs) [] = x :: xs from rfl]; exact hx
      · have hlen₁ : xs.length + (y :: ys).length ≤ f := by
          simp only [List.length_cons] at hlen ⊢; omega
        have hlen₂ : (x :: xs).length + ys.length ≤ f := by
          simp only [List.length_cons] at hlen ⊢; omega
        rw [show merge (f + 1) (x :: xs) (y :: ys) =
            if x.1 ≤ y.1 then x :: merge f xs (y :: ys) else y :: merge f (x :: xs) ys from rfl]
        by_cases hxy : x.1 ≤ y.1
        · rw [if_pos hxy, List.pairwise_cons]
          refine ⟨?_, ih xs (y :: ys) hlen₁ (List.Pairwise.of_cons hx) hy⟩
          intro z hz
          rcases mem_merge f xs (y :: ys) z hz with hz' | hz'
          · exact List.rel_of_pairwise_cons hx hz'
          · rcases List.mem_cons.mp hz' with rfl | hz''
            · exact hxy
            · exact le_trans hxy (List.rel_of_pairwise_cons hy hz'')
        · have hyx : y.1 ≤ x.1 := by omega
          rw [if_neg hxy, List.pairwise_cons]
          refine ⟨?_, ih (x :: xs) ys hlen₂ hx (List.Pairwise.of_cons hy)⟩
          intro z hz
          rcases mem_merge f (x :: xs) ys z hz with hz' | hz'
          · rcases List.mem_cons.mp hz' with rfl | hz''
            · exact hyx
            · exact le_trans hyx (List.rel_of_pairwise_cons hx hz'')
          · exact List.rel_of_pairwise_cons hy hz'

/-- `merge` is length-preserving. -/
private theorem merge_length : ∀ (fuel : ℕ) (xs ys : List (ℤ × ℤ)),
    (merge fuel xs ys).length = xs.length + ys.length := by
  intro fuel
  induction fuel with
  | zero => intro xs ys; rw [merge.eq_1, List.length_append]
  | succ f ih =>
    intro xs ys
    rcases xs with _ | ⟨x, xs⟩
    · rw [merge.eq_2]; simp
    · rcases ys with _ | ⟨y, ys⟩
      · rw [show merge (f + 1) (x :: xs) [] = x :: xs from rfl]; simp
      · rw [show merge (f + 1) (x :: xs) (y :: ys) =
            if x.1 ≤ y.1 then x :: merge f xs (y :: ys) else y :: merge f (x :: xs) ys from rfl]
        by_cases hxy : x.1 ≤ y.1
        · rw [if_pos hxy, List.length_cons, ih]; simp only [List.length_cons]; omega
        · rw [if_neg hxy, List.length_cons, ih]; simp only [List.length_cons]; omega

/-- `msort` is length-preserving. -/
private theorem msort_length : ∀ (f : ℕ) (l : List (ℤ × ℤ)), (msort f l).length = l.length := by
  intro f
  induction f with
  | zero => intro l; rw [msort.eq_1]
  | succ f ih =>
    intro l
    rcases l with _ | ⟨a, t⟩
    · rw [msort.eq_2]
    · rcases t with _ | ⟨b, t⟩
      · rw [msort.eq_3]
      · rw [show msort (f + 1) (a :: b :: t) =
            merge ((a :: b :: t).length + 1) (msort f ((a :: b :: t).take ((a :: b :: t).length / 2)))
              (msort f ((a :: b :: t).drop ((a :: b :: t).length / 2))) from rfl]
        rw [merge_length, ih, ih, List.length_take, List.length_drop]
        omega

/-- Lists of length at most one are sorted by any relation; here we only need `le1`. -/
private theorem pairwise_of_length_le_one {l : List (ℤ × ℤ)} (h : l.length ≤ 1) :
    List.Pairwise le1 l := by
  rw [List.pairwise_iff_get]
  intro i j hij
  exfalso
  have h1 := i.isLt
  have h2 := j.isLt
  have hij' : (i : ℕ) < (j : ℕ) := hij
  omega

/-- Merge sort is correct: with fuel at least `log₂` of the length, the result is sorted by the
first component. -/
private theorem msort_pairwise : ∀ (f : ℕ) (l : List (ℤ × ℤ)),
    l.length ≤ 2 ^ f → List.Pairwise le1 (msort f l) := by
  intro f
  induction f with
  | zero =>
    intro l h
    rw [msort.eq_1]
    exact pairwise_of_length_le_one (by simpa using h)
  | succ f ih =>
    intro l h
    rcases l with _ | ⟨a, t⟩
    · rw [msort.eq_2]; exact List.Pairwise.nil
    · rcases t with _ | ⟨b, t⟩
      · rw [msort.eq_3]; exact List.pairwise_cons.mpr ⟨by simp, List.Pairwise.nil⟩
      · rw [show msort (f + 1) (a :: b :: t) =
            merge ((a :: b :: t).length + 1) (msort f ((a :: b :: t).take ((a :: b :: t).length / 2)))
              (msort f ((a :: b :: t).drop ((a :: b :: t).length / 2))) from rfl]
        apply merge_sorted
        · rw [msort_length, msort_length, List.length_take, List.length_drop]; omega
        · exact ih _ (by rw [List.length_take]; omega)
        · exact ih _ (by rw [List.length_drop]; omega)

theorem msort_sorted (f : ℕ) (l : List (ℤ × ℤ)) (h : l.length ≤ 2 ^ f) :
    List.Pairwise (fun a b : ℤ × ℤ => a.1 ≤ b.1) (Work.Cert.CJ2.msort f l) :=
  msort_pairwise f l h

end Work.Cert.CJ2Sum
