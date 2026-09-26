import Submission.Work.ConfineT1
import Submission.Work.FactorAbsorption

open FreeGroup
open Commons.GroupTheory.FreeGroup
set_option autoImplicit false

/-!
# The absorption-level general-`k` aggregate (T1, group form)

`ConfineT1.t1_align_general` gives the *alignment*-level general-`k` T1
disjunction for a list of reduced words whose reduction has length ≤ 1.  This
module lifts it to *group elements*: for `es : List (FreeGroup (Fin n))` with
`2 ≤ es.length` and reduced product length `norm es.prod ≤ 1`, some factor is
fully absorbed by its ≤ 2 neighbours:

    t1_absorb_general :
      AbsorbedRight (es[j]) (es[j+1])  ∨   -- es[j] into the head of es[j+1]
      AbsorbedLeft (es[j+1]) (es[j])   ∨   -- es[j+1] into the tail of es[j]
      MiddleAbsorbed (es[j-1]) (es[j]) (es[j+1])   -- es[j] split over both

The bridge is the word-to-group reduction identity
`reduce_flatten_toWord_prod`: reducing the concatenation of the factor words
equals the word of the product (via `FreeGroup.reduce.sound`, `mk_toWord` and
`mul_mk`).  Then `t1_align_general` is applied to `es.map FreeGroup.toWord`
and each alignment disjunct is converted (`List.getElem_map`) and translated
by the `FactorAbsorption` lemmas `absorbedRight_of_align_eq_left`,
`absorbedLeft_of_align_eq_right`, `middleAbsorbed_of_align_ge`.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-- The `mk` of the concatenation of the factor words is the product of the
factors. -/
lemma mk_flatten_map_prod {α : Type*} [DecidableEq α] (es : List (FreeGroup α)) :
    FreeGroup.mk ((es.map FreeGroup.toWord).flatten) = es.prod := by
  induction es with
  | nil => simpa [FreeGroup.toWord_one] using (FreeGroup.mk_toWord (x := (1 : FreeGroup α)))
  | cons e t ih =>
      change FreeGroup.mk (FreeGroup.toWord e ++ ((t.map FreeGroup.toWord).flatten)) = e * t.prod
      rw [← FreeGroup.mul_mk (L₁ := FreeGroup.toWord e) (L₂ := (t.map FreeGroup.toWord).flatten)]
      rw [FreeGroup.mk_toWord, ih]

/-- The reduction of the concatenation of the factor words equals the word of
the product of the factors. -/
lemma reduce_flatten_toWord_prod {α : Type*} [DecidableEq α]
    (es : List (FreeGroup α)) :
    FreeGroup.reduce ((es.map FreeGroup.toWord).flatten) = es.prod.toWord := by
  have hsound := FreeGroup.reduce.sound (L₁ := (es.map FreeGroup.toWord).flatten)
    (L₂ := es.prod.toWord) (by
      calc
        FreeGroup.mk ((es.map FreeGroup.toWord).flatten) = es.prod := mk_flatten_map_prod es
        _ = FreeGroup.mk (es.prod.toWord) := (FreeGroup.mk_toWord (x := es.prod)).symm)
  have hrr : FreeGroup.reduce (es.prod.toWord) = es.prod.toWord :=
    FreeGroup.isReduced_iff_reduce_eq.mp (FreeGroup.isReduced_toWord (x := es.prod))
  simpa [hrr] using hsound

/-- The reduced length of the concatenation of the factor words is the norm of
the product. -/
lemma reduce_flatten_toWord_length_prod {α : Type*} [DecidableEq α]
    (es : List (FreeGroup α)) :
    (FreeGroup.reduce ((es.map FreeGroup.toWord).flatten)).length = FreeGroup.norm es.prod := by
  rw [reduce_flatten_toWord_prod]
  rfl

/-- **T1, absorption level (the general-`k` aggregate, group form).**  For a
list of `k ≥ 2` group elements whose reduced product has length ≤ 1, some
factor is fully absorbed by its ≤ 2 neighbours: either `es[j]` is absorbed
into the head of `es[j+1]` (`AbsorbedRight`), or `es[j+1]` into the tail of
`es[j]` (`AbsorbedLeft`), or the middle factor `es[j]` is fully absorbed by
its two neighbours (`MiddleAbsorbed`).  This is the content of the classical
aggregate lemma that Nielsen's reduction consumes. -/
theorem t1_absorb_general {n : ℕ} (es : List (FreeGroup (Fin n)))
    (hk : 2 ≤ es.length) (hshort : FreeGroup.norm es.prod ≤ 1) :
    (∃ (j : ℕ) (_hj : j < es.length) (hj1 : j + 1 < es.length),
        AbsorbedRight (es[j]) (es[j + 1])) ∨
    (∃ (j : ℕ) (_hj : j < es.length) (hj1 : j + 1 < es.length),
        AbsorbedLeft (es[j + 1]) (es[j])) ∨
    (∃ (j : ℕ) (_hj0 : 0 < j) (hj1 : j + 1 < es.length)
        (_hj2 : j < es.length) (_hm : j - 1 < es.length),
        MiddleAbsorbed (es[j - 1]) (es[j]) (es[j + 1])) := by
  classical
  let Fs : List (List (Fin n × Bool)) := es.map FreeGroup.toWord
  have hredF : ∀ L ∈ Fs, FreeGroup.IsReduced L := by
    intro L hL
    rcases (List.mem_map.mp hL) with ⟨e, he, rfl⟩
    exact FreeGroup.isReduced_toWord (x := e)
  have hlenF : (FreeGroup.reduce (Fs.flatten)).length ≤ 1 := by
    unfold Fs
    rw [reduce_flatten_toWord_prod]
    simpa [FreeGroup.norm] using hshort
  have hkF : 2 ≤ Fs.length := by simpa [Fs] using hk
  rcases t1_align_general (α := Fin n) Fs hredF hkF hlenF with h1 | h2 | h3
  · -- some j: align (Fs[j]) (Fs[j+1]) = |Fs[j]|
    rcases h1 with ⟨j, hjF, hj1F, hal⟩
    have hj : j < es.length := by simpa [Fs] using hjF
    have hj1 : j + 1 < es.length := by simpa [Fs] using hj1F
    left
    refine ⟨j, hj, hj1, ?_⟩
    have hal' : align ((es[j]).toWord) ((es[j + 1]).toWord) = ((es[j]).toWord).length := by
      unfold Fs at hal
      rw [List.getElem_map] at hal
      rw [List.getElem_map] at hal
      simpa using hal
    exact absorbedRight_of_align_eq_left (es[j]) (es[j + 1]) hal'
  · -- some j: align (Fs[j]) (Fs[j+1]) = |Fs[j+1]|
    rcases h2 with ⟨j, hjF, hj1F, hal⟩
    have hj : j < es.length := by simpa [Fs] using hjF
    have hj1 : j + 1 < es.length := by simpa [Fs] using hj1F
    right; left
    refine ⟨j, hj, hj1, ?_⟩
    have hal' : align ((es[j]).toWord) ((es[j + 1]).toWord) = ((es[j + 1]).toWord).length := by
      unfold Fs at hal
      rw [List.getElem_map] at hal
      rw [List.getElem_map] at hal
      simpa using hal
    exact absorbedLeft_of_align_eq_right (es[j]) (es[j + 1]) hal'
  · -- some j: align (Fs[j-1]) (Fs[j]) + align (Fs[j]) (Fs[j+1]) ≥ |Fs[j]|
    rcases h3 with ⟨j, hj0F, hj1F, hj2F, hmF, hal⟩
    have hj1 : j + 1 < es.length := by simpa [Fs] using hj1F
    have hj2 : j < es.length := by simpa [Fs] using hj2F
    have hm : j - 1 < es.length := by simpa [Fs] using hmF
    right; right
    refine ⟨j, ?_, hj1, hj2, hm, ?_⟩
    · simpa [Fs] using hj0F
    · have hal' : ((es[j]).toWord).length ≤
          align ((es[j - 1]).toWord) ((es[j]).toWord) +
          align ((es[j]).toWord) ((es[j + 1]).toWord) := by
        unfold Fs at hal
        rw [List.getElem_map] at hal
        rw [List.getElem_map] at hal
        rw [List.getElem_map] at hal
        simpa using hal
      exact middleAbsorbed_of_align_ge (es[j - 1]) (es[j]) (es[j + 1]) hal'

end Submission.Nielsen
