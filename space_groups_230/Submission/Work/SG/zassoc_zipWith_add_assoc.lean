import Mathlib
import Submission.Work.SG.SGprelude

/-!
# `zassoc_zipWith_add_assoc`: associativity of pointwise addition of lists

The componentwise sum of two lists is `List.zipWith (· + ·)`, which truncates to the shorter
of the two lists.  Regrouping a triple sum is therefore legitimate: both sides have length
`min (min |x| |y|) |z| = min |x| (min |y| |z|)` (associativity of `Nat.min`) and the `i`-th
entry is `(xᵢ + yᵢ) + zᵢ` on the left and `xᵢ + (yᵢ + zᵢ)` on the right, which agree by
associativity of `+` on `ℤ`.

The elementary general fact is proved first (`zipWith_assoc_of_assoc`), the requested
`ℤ`-statement is the specialisation to `Int.add`.
-/

namespace Work.SG

/-- **Associativity of `List.zipWith`** for an associative binary operation: for
`f (f a b) c = f a (f b c)`, regrouping the pointwise triple `f`-combination is allowed.

Both sides truncate to the shortest of the three lists, so no length hypothesis is needed;
at each surviving position the two groupings differ exactly by `hf`. -/
theorem zipWith_assoc_of_assoc {α : Type*} (f : α → α → α)
    (hf : ∀ a b c, f (f a b) c = f a (f b c)) (x y z : List α) :
    List.zipWith f (List.zipWith f x y) z = List.zipWith f x (List.zipWith f y z) := by
  induction x generalizing y z with
  | nil => simp
  | cons a x ih =>
    cases y with
    | nil => simp
    | cons b y =>
      cases z with
      | nil => simp
      | cons c z => simp [ih, hf]

/-- Regrouping a triple of componentwise sums of integer lists. -/
theorem zassoc_zipWith_add_assoc (x y z : List ℤ) :
    List.zipWith (· + ·) (List.zipWith (· + ·) x y) z = List.zipWith (· + ·) x (List.zipWith (· + ·) y z) :=
  zipWith_assoc_of_assoc (· + ·) (fun a b c => add_assoc a b c) x y z

end Work.SG
