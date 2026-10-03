import Mathlib
import Submission.Work.ORHughesFree.Rat.FreeProduct.NU

/-!
# `shiftPad` and appending on the right

`shiftPad b l` applies the parameters `b` (`b.length = l.length + 1`) to the word `l`: its `i`-th
entry is `b_{i+1}⁻¹ · l_i · b_i`.  Reading off the very definition, the recursion consumes the
parameters from the front, always as consecutive *pairs*: the pairs used on `l` of length `n` and
parameters `b = [b₀, …, bₙ]` are `(b₀, b₁), (b₁, b₂), …, (b_{n-1}, bₙ)`.

Consequently, when the parameters are `b ++ b'` and the word is `l ++ k`, the first `n` steps are
exactly `shiftPad b l`, and the recursion continues on `k` with the parameters
`(last b) :: b'`.  That is `shiftPad_append_split` below.  It is the content of the target lemma:
if moreover the last parameter of `b` is `1`, the remaining parameters are the all-ones list of
length `k.length + 1`, which acts trivially on `k` (`shiftPad_replicate_one`).
-/

set_option autoImplicit false

namespace Work.ORHughesFree.Rat
namespace FreeProduct

variable {U : Type} [Group U]

/-- Splitting the parameters as `b ++ b'` and the word as `l ++ k`: provided `b` matches `l`,
`shiftPad` first processes `l` with `b`, and then processes `k` with `(last b) :: b'`.

Note that *no* length condition on `b'` and `k` is needed: the recursion either exhausts the
parameters or the word, and both sides do so at the same point. -/
theorem shiftPad_append_split (b b' : List U) (l k : List (RatU U))
    (h : b.length = l.length + 1) :
    shiftPad (b ++ b') (l ++ k) = shiftPad b l ++ shiftPad (b.getLastD 1 :: b') k := by
  induction l generalizing b with
  | nil =>
    have : b.length = 1 := by simpa using h
    match b, h with
    | [], h => simp at h
    | [c], _ => simp
  | cons x xs ih =>
    match b, h with
    | [], h => simp at h
    | [_], h => simp at h
    | b0 :: b1 :: bs, h =>
      have h1 : (b1 :: bs).length = xs.length + 1 := by simp at h ⊢; omega
      have hIH := ih (b1 :: bs) h1
      simp only [List.cons_append] at hIH
      simp only [List.cons_append, shiftPad_cons]
      rw [hIH]
      simp

/-- If the last element of `b` is `1`, then `getLastD 1` is that last element. -/
theorem getLastD_eq_one_of_getLast?_eq_some_one {b : List U} (hlast : b.getLast? = some 1) :
    b.getLastD (1 : U) = 1 := by
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
  simp

theorem shiftPad_append_right {U : Type} [Group U] (b : List U) (l k : List (Work.ORHughesFree.RatU U))
    (h : b.length = l.length + 1) (hlast : b.getLast? = some 1) :
    Work.ORHughesFree.Rat.FreeProduct.shiftPad b l ++ k
      = Work.ORHughesFree.Rat.FreeProduct.shiftPad (b ++ List.replicate k.length (1 : U)) (l ++ k) := by
  have hg : b.getLastD (1 : U) = 1 := getLastD_eq_one_of_getLast?_eq_some_one hlast
  have key := shiftPad_append_split b (List.replicate k.length (1 : U)) l k h
  rw [hg] at key
  rw [show (1 : U) :: List.replicate k.length 1 = List.replicate (k.length + 1) 1 from
    (List.replicate_succ).symm] at key
  rw [shiftPad_replicate_one k] at key
  exact key.symm

end FreeProduct
end Work.ORHughesFree.Rat
