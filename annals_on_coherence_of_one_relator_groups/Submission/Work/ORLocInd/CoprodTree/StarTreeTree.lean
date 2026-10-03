/-
# The graph `Vertex M` is a tree

This file proves that the Bass--Serre graph of the free product
(`Submission.Work.ORLocInd.CoprodTree.StarTreeDefs`) has no non-trivial reduced closed path, using
the invariant of `Submission.Work.ORLocInd.CoprodTree.StarTreePath`.

The argument is the classical "follow the path in the group" argument.  Let `p` be a reduced
closed path based at the vertex `vtx k g`, and let `L` be its list of letters.  The product of the
letters is `g⁻¹ * stt` where `stt` is the state at the endpoint:

* if `k = none` then the end of a closed path is again the central vertex of `g`, so `stt = g` and
  the product is `1`;
* if `k = some i` then the endpoint is the leaf of the state `stt`, whence `g⁻¹ * stt` lies in the
  `i`-th factor of the free product and hence is `of m` for some `m : M i`.

In both cases the product of the letters is an element whose reduced word has length at most `1`,
so the number of letters — which is `p.length / 2` respectively `(p.length + 1) / 2` — is at most
`1`, respectively `2`.  A closed path of length `2` in this graph is never reduced (any arrow joins
a central vertex to a leaf, so the two arrows of a closed path of length 2 are mutually inverse),
which forces `p.length = 0`.
-/
import Mathlib
import Submission.Work.ORLocInd.CoprodTree.StarTreePath

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.CoprodTree

open Quiver
open Work.ORBassSerre
open Classical

variable {ι : Type u}

/-! ## Two bounds on the length of the reduced word of an element -/

/-- The reduced word of the identity is empty. -/
theorem word_length_equiv_one {M : ι → Type u} [∀ i, Group (M i)] :
    (Monoid.CoprodI.Word.equiv (M := M) (1 : Monoid.CoprodI M)).toList.length = 0 := by
  classical
  have h1 : Monoid.CoprodI.Word.equiv (M := M) (1 : Monoid.CoprodI M)
      = Monoid.CoprodI.Word.empty :=
    one_smul (Monoid.CoprodI M) (Monoid.CoprodI.Word.empty : Monoid.CoprodI.Word M)
  rw [h1]
  rfl

/-- The reduced word of an element of one of the factors has length at most one. -/
theorem word_length_of_le_one {M : ι → Type u} [∀ i, Group (M i)] (i : ι) (m : M i) :
    (Monoid.CoprodI.Word.equiv (M := M) (Monoid.CoprodI.of m)).toList.length ≤ 1 := by
  classical
  by_cases hm : m = 1
  · rw [hm, map_one, word_length_equiv_one (M := M)]
    omega
  · let w : Monoid.CoprodI.Word M :=
      ⟨[(⟨i, m⟩ : Σ j, M j)],
        by
          intro x hx
          rw [List.mem_singleton] at hx
          subst hx
          exact hm,
        by simp⟩
    have hprod : Monoid.CoprodI.of m = Monoid.CoprodI.Word.prod w := by
      simp [w, Monoid.CoprodI.Word.prod]
    have hw : Monoid.CoprodI.Word.equiv (M := M) (Monoid.CoprodI.of m) = w := by
      rw [hprod]
      exact (Monoid.CoprodI.Word.equiv (M := M)).right_inv w
    rw [hw]
    simp [w]

/-! ## The main argument -/

/-- A reduced closed path starting at a central vertex is trivial. -/
theorem eq_nil_of_inv_none {M : ι → Type u} [∀ i, Group (M i)] {g : Monoid.CoprodI M}
    {p : Quiver.Path (vtx (none : Option ι) g) (vtx (none : Option ι) g)}
    (hp : p.IsReduced) (hinv : Inv (none : Option ι) g p) : p = Quiver.Path.nil := by
  classical
  have hside : isLeafSide (none : Option ι) p.length = false := by
    by_contra h
    have h' : isLeafSide (none : Option ι) p.length = true := by
      cases hb : isLeafSide (none : Option ι) p.length <;> simp_all
    obtain ⟨i, hi⟩ := (hinv.endpoint_some h').1
    exact vtx_none_ne_vtx_some hi
  have hmod : p.length % 2 ≠ 1 := by
    have h := hside
    rw [isLeafSide_none] at h
    exact of_decide_eq_false h
  have hstt : stt (none : Option ι) g p = g := by
    have h := hinv.endpoint_none hside
    exact ((vtx_none_eq_vtx_none).mp h.symm)
  have hprod : ((letters (none : Option ι) g p).map (fun y => y.2)).prod = 1 := by
    rw [hinv.prod_letters, hstt, inv_mul_cancel]
  have hlen : (letters (none : Option ι) g p).length ≤ 0 := by
    have h := letters_length_le_word_length' hinv.mem (hinv.ne_one_central rfl) hinv.chain hprod
    rwa [word_length_equiv_one (M := M)] at h
  have h0 : (letters (none : Option ι) g p).length = 0 := Nat.le_zero.mp hlen
  rw [letters_length_none] at h0
  exact Quiver.Path.eq_nil_of_length_zero p (by omega)

end Work.ORLocInd.CoprodTree
