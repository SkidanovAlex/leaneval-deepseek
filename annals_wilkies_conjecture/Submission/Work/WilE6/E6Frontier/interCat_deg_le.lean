import Mathlib
import Submission.Work.WilE6.E6Frontier.Defs
import Submission.Work.WilE7.Defs
import Submission.Work.WilE9.Ift.OneShot.oneShotSet_deg_le
import Submission.Work.WilE5.Basic

namespace Work.WilE6.E6Frontier

open WilkiesDesign WilkiesDesign.E

/-!
# Degree of the conjunctions `interCat`

`Work.WilE6.interCat X Y` presents the intersection `X.set ∩ Y.set` over the concatenated chain
`EAChain.cat X.c Y.c`, with the product DNF: one branch `conjCat B C` per pair of branches
`B ∈ X.basics`, `C ∈ Y.basics`.

The degree bookkeeping is exact.  Concatenating the chains does not change the degree of a
branch (`EAPoly.inl`/`EAPoly.inr` are renamings along injections, so `List.totalDegree` is
preserved, see `Work.WilE9.Ift.OneShot.basic_deg_inl/inr`), and `Work.WilE5.conj` adds degrees.
Hence

  `deg (interCat X Y) = |Y.basics| * X.deg + |X.basics| * Y.deg`,

which is the statement below, with `=` in place of `≤`.  The two sums of lists of natural
numbers are elementary: the flat map distributes over the sum, the sum of `B.deg + C.deg` splits,
and constants are factored out.
-/

/-- The degree of the conjunction of two basic conditions over the concatenated chain is the
sum of the two degrees: concatenation is a reindexing and does not change degrees. -/
theorem conjCat_deg {k r₁ r₂ : ℕ} (B : Basic k r₁) (C : Basic k r₂) :
    (Work.WilE6.conjCat B C).deg = B.deg + C.deg := by
  rw [Work.WilE6.conjCat, Work.WilE5.conj_deg, Work.WilE9.Ift.OneShot.basic_deg_inl,
    Work.WilE9.Ift.OneShot.basic_deg_inr]

/-- The sum of a constant list of naturals: `∑ c = |l| * c`. -/
theorem sum_map_const {α : Type*} (l : List α) (c : ℕ) :
    (l.map (fun _ => c)).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a t ih => rw [List.map_cons, List.sum_cons, ih, List.length_cons, Nat.succ_mul]; omega

/-- The sum over a `flatMap` is the sum of the sums of the fibres. -/
theorem sum_flatMap {α : Type*} (L : List α) (f : α → List ℕ) :
    (L.flatMap f).sum = (L.map (fun a => (f a).sum)).sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
    simp only [List.flatMap_cons, List.sum_append, ih, List.map_cons, List.sum_cons]

/-- The contributions of a fixed branch `B` of `X` against all branches of `Y`: the degree sum
of `|Y.basics|` copies of `B.deg` plus the total degree of `Y`. -/
theorem map_conjCat_deg_sum {k r₁ r₂ : ℕ} (B : Basic k r₁) (L : List (Basic k r₂)) :
    ((L.map (fun C => Work.WilE6.conjCat B C)).map Basic.deg).sum
      = L.length * B.deg + (L.map Basic.deg).sum := by
  have h1 : ((L.map (fun C => Work.WilE6.conjCat B C)).map Basic.deg).sum
      = (L.map (fun C => (Work.WilE6.conjCat B C).deg)).sum := by
    rw [List.map_map]; rfl
  have h2 : (L.map (fun C => (Work.WilE6.conjCat B C).deg)) = L.map (fun C => B.deg + C.deg) :=
    List.map_congr_left (fun C _ => conjCat_deg B C)
  rw [h1, h2, List.sum_map_add, sum_map_const]

/-- The exact degree of `interCat`: the product DNF contributes `|Y.basics| * X.deg` from the
`X`-branches and `|X.basics| * Y.deg` from the `Y`-branches. -/
theorem interCat_deg_eq {k : ℕ} (X Y : SemiPf k) :
    (Work.WilE6.interCat X Y).deg = Y.basics.length * X.deg + X.basics.length * Y.deg := by
  show ((X.basics.flatMap (fun B => Y.basics.map (fun C => Work.WilE6.conjCat B C))).map
        Basic.deg).sum = Y.basics.length * X.deg + X.basics.length * Y.deg
  rw [List.map_flatMap, sum_flatMap]
  have h : (X.basics.map (fun B =>
        ((Y.basics.map (fun C => Work.WilE6.conjCat B C)).map Basic.deg).sum))
      = X.basics.map (fun B => Y.basics.length * B.deg + (Y.basics.map Basic.deg).sum) :=
    List.map_congr_left (fun B _ => map_conjCat_deg_sum B Y.basics)
  rw [h, List.sum_map_add, List.sum_map_mul_left, sum_map_const]
  rfl

theorem interCat_deg_le {k : ℕ} (X Y : WilkiesDesign.E.SemiPf k) :
    (Work.WilE6.interCat X Y).deg ≤
      Y.basics.length * X.deg + X.basics.length * Y.deg :=
  le_of_eq (interCat_deg_eq X Y)

end Work.WilE6.E6Frontier
