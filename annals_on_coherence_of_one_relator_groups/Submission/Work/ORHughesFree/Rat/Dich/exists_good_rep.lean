import Mathlib
import Submission.Work.ORHughesFree.Rat.Xgen_mem_closure_iff
import Submission.Work.ORHughesFree.Rat.Xgen_mem_NUV_iff
import Submission.Work.ORHughesFree.Rat.Orbit
import Submission.Work.ORHughesFree.Rat.FreeProduct.NUMonoid
import Submission.Work.ORHughesFree.Rat.SourceFrame
import Submission.Work.ORHughesFree.Rat.mem_NUV_of_list

/-!
# A good representative of an `A`-word

Let `l` be a nonempty list of non-zero elements of `Rat(U)` whose class in the `X`-part of
`U ♮ X` is a product of generators of `NUV V`, i.e.

`⟦l⟧ ∈ Orbit.NUV V`.

Since a class in `NUV V` is a product of `Xgen a` with `a ∈ Rat.A V` and of `Ugen v` with
`v ∈ V`, it has a representative all of whose letters lie in `Rat.A V`: this is exactly
`mem_NUV_of_list`.  Taking that representative `B` gives the first three requirements of the
target statement (`B ≠ []`, the entries in `Rat.A V`, the same class).  The two remaining
requirements — the *same length* and the *same complexity* `treeOfRat` — are automatic for a
representative of the same class: `B` is `shiftPad (1 :: b ++ [1]) l` for some parameter list
`b`, and the `i`-th letter of a `shiftPad`-translate of `l` is `ofGroup b_{i+1}⁻¹ * l_i *
ofGroup b_i`, whose complexity equals that of `l_i` because multiplying by the image of a group
element on either side does not change `treeOfRat` (`RatU.treeOfRat_ofGroup_mul`,
`RatU.treeOfRat_mul_ofGroup`).  Non-zeroness follows from the complexity: a non-zero `z ∈ l` has
`treeOfRat z ≠ 0`, hence `treeOfRat y = treeOfRat z ≠ 0` and `y ≠ 0`.
-/

namespace Work.ORHughesFree.Rat

open Work.ORHughesFree
open Work.ORHughesFree.Rat.FreeProduct

variable {U : Type} [Group U]

/-- **`shiftPad` preserves the complexity of every letter.**  When `b.length = l.length + 1`,
every letter of `shiftPad b l` has the complexity `treeOfRat` of some letter of `l` (namely of the
letter in the same position). -/
theorem treeOfRat_shiftPad_mem (b : List U) (l : List (RatU U))
    (h : b.length = l.length + 1) :
    ∀ y ∈ shiftPad b l, ∃ z ∈ l, treeOfRat U y = treeOfRat U z := by
  induction l generalizing b with
  | nil =>
    intro y hy
    rw [shiftPad_nil] at hy
    exact absurd hy (List.not_mem_nil)
  | cons x xs ih =>
    cases b with
    | nil => simp only [List.length_nil] at h; omega
    | cons b0 bs =>
      cases bs with
      | nil => simp only [List.length_cons, List.length_nil] at h; omega
      | cons b1 bs =>
        have h1 : (b1 :: bs).length = xs.length + 1 := by
          simp only [List.length_cons] at h ⊢; omega
        intro y hy
        rw [shiftPad_cons, List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact ⟨x, List.mem_cons_self, by simp [Rat.treeOfRat_mul]⟩
        · obtain ⟨z, hz, htz⟩ := ih (b1 :: bs) h1 y hy
          exact ⟨z, List.mem_cons_of_mem x hz, htz⟩

end Work.ORHughesFree.Rat

namespace Work.ORHughesFree.Rat.Dich

theorem exists_good_rep {U : Type} [Group U] (V : Subgroup U) (l : List (Work.ORHughesFree.RatU U))
    (hl : l ≠ []) (hne : ∀ y ∈ l, y ≠ 0)
    (hmem : (Sum.inr (Quotient.mk (Work.ORHughesFree.Rat.FreeProduct.relNESetoid U) ⟨l, hl⟩) :
        Work.ORHughesFree.Rat.FreeProduct.NU U) ∈ Work.ORHughesFree.Rat.Orbit.NUV V) :
    ∃ (B : List (Work.ORHughesFree.RatU U)) (hB : B ≠ []),
      B.length = l.length ∧
      (∀ y ∈ B, y ∈ Work.ORHughesFree.Rat.A V ∧ y ≠ 0) ∧
      (∀ y ∈ B, ∃ z ∈ l, Work.ORHughesFree.Rat.treeOfRat U y =
        Work.ORHughesFree.Rat.treeOfRat U z) ∧
      (Quotient.mk (Work.ORHughesFree.Rat.FreeProduct.relNESetoid U) ⟨B, hB⟩ =
        Quotient.mk (Work.ORHughesFree.Rat.FreeProduct.relNESetoid U) ⟨l, hl⟩) := by
  -- a representative of the class all of whose letters lie in `A V`
  obtain ⟨B, hB, hrel, hall⟩ := (Work.ORHughesFree.Rat.mem_NUV_of_list V l hl).mp hmem
  have hrel' := hrel
  obtain ⟨b, hblen, hbeq⟩ := hrel
  have hblen' : b.length + 1 = l.length := hblen
  -- `B` is the `shiftPad`-translate of `l` by the parameters `1 :: b ++ [1]`
  have hB_eq : B = Work.ORHughesFree.Rat.FreeProduct.shiftPad (1 :: (b ++ [1])) l := hbeq
  have hparams : (1 :: (b ++ [1])).length = l.length + 1 := by
    simp only [List.length_cons, List.length_append, List.length_nil]
    omega
  have htree : ∀ y ∈ B, ∃ z ∈ l, Work.ORHughesFree.Rat.treeOfRat U y =
      Work.ORHughesFree.Rat.treeOfRat U z := by
    intro y hy
    rw [hB_eq] at hy
    exact Work.ORHughesFree.Rat.treeOfRat_shiftPad_mem (1 :: (b ++ [1])) l hparams y hy
  refine ⟨B, hB, ?_, ?_, htree, ?_⟩
  · -- same length: `shiftPad` preserves the length
    rw [hB_eq]
    exact Work.ORHughesFree.Rat.FreeProduct.shiftPad_length (1 :: (b ++ [1])) l hparams
  · -- letters in `A V` and non-zero
    intro y hy
    refine ⟨hall y hy, ?_⟩
    obtain ⟨z, hz, htz⟩ := htree y hy
    intro hy0
    exact hne z hz ((Work.ORHughesFree.Rat.treeOfRat_eq_zero_iff U z).mp
      (by rw [← htz, hy0, Work.ORHughesFree.Rat.treeOfRat_zero]))
  · -- the same class
    exact (Quotient.sound hrel').symm

end Work.ORHughesFree.Rat.Dich
