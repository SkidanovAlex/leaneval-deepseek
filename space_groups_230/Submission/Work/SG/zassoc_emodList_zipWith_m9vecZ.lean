import Mathlib
import Submission.Work.SG.SGprelude

/-!
# `zassoc_emodList_zipWith_m9vecZ`

Reducing the vector `v` modulo `d` *before* applying the flat matrix–vector product `m9vecZ M`
and before adding a fixed list `x` pointwise does not change the result modulo `d`:

`emodList d (x + M · (v mod d)) = emodList d (x + M · v)`.

This is the last of the elementary list identities used in `Work.SG.zMul_assoc`: the
translation component of the integer affine product `zMul d` is `u + A · v` reduced mod `d`,
and regrouping `(u + A v) · (w)` requires the reduction of `v` to be absorbable.

The mathematical content is the congruence of `ℤ` arithmetic modulo `d`:
* `(a + b) % d` depends on `b` only through `b % d`,
* `a * b % d` depends on `b` only through `b % d`,
* hence every entry `∑ₖ Mᵢₖ vₖ` of `m9vecZ M v` is congruent mod `d` to the corresponding
  entry of `m9vecZ M (emodList d v)` (the `getD` accessor of `emodList d v` is `v.getD _ 0 % d`),

and then the same congruence survives pointwise addition with `x` (which only truncates the
two lists to the same length, the lengths being unaffected by `emodList`).

Everything holds for `d = 0` as well (there `x % 0 = x`, so `emodList 0` is the identity).
-/

namespace Work.SG

/-! ## Congruence lemmas for `Int.emod` -/

/-- `(a + b) % d` depends on `b` only through `b % d`. -/
private lemma emod_add_congr (d : ℤ) (a b b' : ℤ) (h : b % d = b' % d) :
    (a + b) % d = (a + b') % d := by
  rw [Int.add_emod a b d, Int.add_emod a b' d, h]

/-- `(a * b) % d` depends on `b` only through `b % d`. -/
private lemma emod_mul_congr_right (d : ℤ) (a b b' : ℤ) (h : b % d = b' % d) :
    (a * b) % d = (a * b') % d := by
  rw [Int.mul_emod a b d, Int.mul_emod a b' d, h]

/-- Reducing the right factor modulo `d` does not change `(a * b) % d`. -/
private lemma emod_mul_emod_right (d : ℤ) (a b : ℤ) : (a * (b % d)) % d = (a * b) % d :=
  emod_mul_congr_right d a (b % d) b (Int.emod_emod b d)

/-- Sums of pointwise congruent lists are congruent modulo `d`. -/
private lemma sum_map_emod_congr {α : Type*} (d : ℤ) (l : List α) (f g : α → ℤ)
    (h : ∀ a, f a % d = g a % d) : (l.map f).sum % d = (l.map g).sum % d := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [Int.add_emod (f a) (l.map f).sum d, Int.add_emod (g a) (l.map g).sum d, h a, ih]

/-- The accessor of `emodList d v` is the reduction of the accessor of `v`. -/
private lemma emodList_getD (d : ℕ) (v : List ℤ) (k : ℕ) :
    (emodList d v).getD k 0 = v.getD k 0 % (d : ℤ) := by
  have h := List.getD_map (l := v) (d := (0 : ℤ)) (n := k) (f := fun x => x % (d : ℤ))
  simpa [emodList] using h

/-! ## The matrix–vector product -/

/-- The `i`-th entry of `m9vecZ M (emodList d v)` and of `m9vecZ M v` agree modulo `d`. -/
private lemma m9vecZ_emod_row (d : ℕ) (M v : List ℤ) (i : ℕ) :
    ((List.range 3).map (fun k => M.getD (3 * i + k) 0 * (emodList d v).getD k 0)).sum % (d : ℤ)
      = ((List.range 3).map (fun k => M.getD (3 * i + k) 0 * v.getD k 0)).sum % (d : ℤ) := by
  refine sum_map_emod_congr (d : ℤ) (List.range 3) _ _ ?_
  intro k
  show (M.getD (3 * i + k) 0 * (emodList d v).getD k 0) % (d : ℤ)
      = (M.getD (3 * i + k) 0 * v.getD k 0) % (d : ℤ)
  rw [emodList_getD]
  exact emod_mul_emod_right (d : ℤ) (M.getD (3 * i + k) 0) (v.getD k 0)

/-- Reducing `v` before applying `m9vecZ M` is invisible after a final reduction mod `d`. -/
private theorem m9vecZ_emodList_emod (d : ℕ) (M v : List ℤ) :
    emodList d (m9vecZ M (emodList d v)) = emodList d (m9vecZ M v) := by
  simp only [emodList, m9vecZ, List.map_map]
  apply List.map_congr_left
  intro i _
  exact m9vecZ_emod_row d M v i

/-! ## Pointwise addition -/

/-- Pointwise addition with a fixed list, followed by the reduction `emodList d`, depends on the
second summand only through its own reduction.  (Lengths are preserved by `emodList`, so both
sides truncate in the same way.) -/
private lemma emodList_zipWith_congr (d : ℕ) (x w w' : List ℤ) (h : emodList d w = emodList d w') :
    emodList d (List.zipWith (· + ·) x w) = emodList d (List.zipWith (· + ·) x w') := by
  induction x generalizing w w' with
  | nil => simp [emodList]
  | cons a as ih =>
      cases w with
      | nil =>
        cases w' with
        | nil => rfl
        | cons c cs => simp [emodList] at h
      | cons b bs =>
        cases w' with
        | nil => simp [emodList] at h
        | cons c cs =>
          have hb : b % (d : ℤ) = c % (d : ℤ) := by
            have h' := h
            simp only [emodList, List.map_cons, List.cons.injEq] at h'
            exact h'.1
          have hbs : emodList d bs = emodList d cs := by
            have h' := h
            simp only [emodList, List.map_cons, List.cons.injEq] at h'
            exact h'.2
          simp only [List.zipWith_cons_cons, emodList, List.map_cons, List.cons.injEq]
          refine ⟨?_, ?_⟩
          · exact emod_add_congr (d : ℤ) a b c hb
          · exact ih bs cs hbs

/-- Reducing `v` modulo `d` before applying the flat matrix `M` to it and adding `x` pointwise
does not change the result modulo `d`. -/
theorem zassoc_emodList_zipWith_m9vecZ (d : ℕ) (x M v : List ℤ) :
    emodList d (List.zipWith (· + ·) x (m9vecZ M (emodList d v))) =
      emodList d (List.zipWith (· + ·) x (m9vecZ M v)) :=
  emodList_zipWith_congr d x (m9vecZ M (emodList d v)) (m9vecZ M v)
    (m9vecZ_emodList_emod d M v)

end Work.SG
