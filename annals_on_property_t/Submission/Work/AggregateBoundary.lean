import Submission.Work.AggregateDispatch
import Submission.Work.ConfineT1
import Submission.Work.T2HalfHalf

open FreeGroup
open Commons.GroupTheory.FreeGroup
set_option autoImplicit false

/-!
# Boundary confined factors are strictly shortening

`AggregateDispatch.confined_factor_dispatch` dispatches an *interior*
confined factor of an image aggregate: strict phase (an elementary closure
move strictly decreases `N`) or balanced content.  This module completes the
dispatch for *boundary* confined factors:

* a confined **first** block (`j = 0`) has every letter paired into the
  second block, so `align L₀ L₁ = |L₀|`: the product `es[0]·es[1]` loses the
  whole first word and is strictly shorter than `es[1]` — a strict right
  junction (`confined_zero_strict`, `boundary_zero_move`);
* a confined **last** block (`j + 1 = es.length`, `0 < j`) is symmetric:
  `align L_{j-1} L_j = |L_j|`, the product `es[j-1]·es[j]` is strictly
  shorter than `es[j-1]` — a strict left junction (`confined_last_strict`,
  `boundary_last_move`).

(The non-triviality needed for the strict inequality comes from
`SystemReduced`: no factor is the identity.)  Assembled:

    confined_factor_reduces — for a *confined factor in any position* of an
    image aggregate of length ≥ 2, either a closure move strictly decreases
    `N`, or the factor is interior and the balanced content holds.  This is
    the complete per-factor dispatch that the aggregate step of the reduction
    protocol consumes (`exists_confined_image_aggregate` supplies the confined
    factor; boundary cases reduce strictly, interior cases fall to
    `confined_factor_dispatch`).

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-- The factor words `aggregateWords es` are reduced. -/
private lemma redFs {n : ℕ} (es : List (FreeGroup (Fin n))) :
    ∀ L ∈ aggregateWords es, FreeGroup.IsReduced L :=
  aggregateWords_reduced es

/-- `Fs = aggregateWords es`, first factor is `toWord es[0]`. -/
private lemma Fs0_eq {n : ℕ} (es : List (FreeGroup (Fin n))) (h : 0 < es.length) :
    (aggregateWords es)[0]'(by simpa [aggregateWords_length] using h) = (es[0]'(h)).toWord := by
  unfold aggregateWords
  rw [List.getElem_map]

/-- `Fs = aggregateWords es`, factor at `j` is `toWord es[j]`. -/
private lemma Fsj_eq {n : ℕ} (es : List (FreeGroup (Fin n))) {j : ℕ} (h : j < es.length) :
    (aggregateWords es)[j]'(by simpa [aggregateWords_length] using h) = (es[j]'(h)).toWord := by
  unfold aggregateWords
  rw [List.getElem_map]

/-- A non-trivial factor has a non-empty reduced word. -/
private lemma word_nz_of_ne_one {n : ℕ} (x : FreeGroup (Fin n)) (hx : x ≠ 1) :
    x.toWord ≠ [] := by
  intro hw
  apply hx
  have hm := FreeGroup.mk_toWord (x := x)
  rw [hw] at hm
  have h1 : FreeGroup.mk ([] : List (Fin n × Bool)) = (1 : FreeGroup (Fin n)) := by rfl
  rw [h1] at hm
  exact hm.symm

/-- **First-block full alignment.**  A confined first block of a list of
reduced words is absorbed entirely into the second block:
`align (Fs[0]) (Fs[1]) = (Fs[0]).length`. -/
lemma confined_zero_full_align {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) (hred : ∀ L ∈ Fs, FreeGroup.IsReduced L)
    (h1 : 1 < Fs.length) (hconf : Confined Fs 0) :
    align (Fs[0]) (Fs[1]) = (Fs[0]).length := by
  have hle1 : (Fs[0]).length ≤ align (Fs[0]) (Fs[1]) := by
    exact le_trans (confined_zero_length_le Fs hred h1 hconf)
      (align_right_junction Fs hred (j := 0) h1)
  have hle2 : align (Fs[0]) (Fs[1]) ≤ (Fs[0]).length :=
    align_le_length_left (Fs[0]) (Fs[1])
  omega

/-- **Last-block full alignment.**  A confined last block (`j+1 = Fs.length`,
`0 < j`) is absorbed entirely into the preceding block:
`align (Fs[j-1]) (Fs[j]) = (Fs[j]).length`. -/
lemma confined_last_full_align {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) (hred : ∀ L ∈ Fs, FreeGroup.IsReduced L)
    {j : ℕ} (hj : j < Fs.length) (h2 : 2 ≤ Fs.length) (hlast : j + 1 = Fs.length)
    (hconf : Confined Fs j) :
    align (Fs[j - 1]) (Fs[j]) = (Fs[j]).length := by
  have hj0 : 0 < j := by omega
  have hle1 : (Fs[j]).length ≤ align (Fs[j - 1]) (Fs[j]) := by
    exact le_trans (confined_last_length_le Fs hred hj h2 hlast hconf)
      (align_left_junction Fs hred hj0 hj)
  have hle2 : align (Fs[j - 1]) (Fs[j]) ≤ (Fs[j]).length :=
    align_le_length_right (Fs[j - 1]) (Fs[j])
  omega

/-- **First-block strict junction.**  If the first factor of an image
aggregate is confined, its product with the second factor is strictly shorter
than the second: `|es[0]·es[1]| < |es[1]|`. -/
theorem confined_zero_strict {n : ℕ} (es : List (FreeGroup (Fin n)))
    (hred : SystemReduced es) (hk : 2 ≤ es.length)
    (hconf : Confined (aggregateWords es) 0) :
    FreeGroup.norm ((es[0]'(by omega)) * (es[1]'(by omega)))
        < FreeGroup.norm (es[1]'(by omega)) := by
  classical
  have h1F : 1 < (aggregateWords es).length := by
    rw [aggregateWords_length]
    omega
  have hfull := confined_zero_full_align (aggregateWords es) (redFs es) h1F hconf
  have hb0 : 0 < es.length := by omega
  have hb1 : 1 < es.length := by omega
  have h0 : (aggregateWords es)[0]'(by simpa [aggregateWords_length] using hb0) = (es[0]'(hb0)).toWord :=
    Fs0_eq es hb0
  have h1 : (aggregateWords es)[1]'(by simpa [aggregateWords_length] using hb1) = (es[1]'(hb1)).toWord :=
    Fsj_eq es hb1
  -- |es[0]| ≥ 1 (no trivial factors)
  have hnt : (es[0]'(hb0)).toWord ≠ [] := word_nz_of_ne_one (es[0]'(hb0)) (hred.1 _ (List.getElem_mem hb0))
  have hpos : 0 < (es[0]'(hb0)).toWord.length := by
    rw [List.length_pos_iff_ne_nil]
    exact hnt
  have hpos1 : 0 < (es[1]'(hb1)).toWord.length := by
    rw [List.length_pos_iff_ne_nil]
    exact word_nz_of_ne_one (es[1]'(hb1)) (hred.1 _ (List.getElem_mem hb1))
  have halign : align ((es[0]'(hb0)).toWord) ((es[1]'(hb1)).toWord) = ((es[0]'(hb0)).toWord).length := by
    -- hfull in terms of es
    have hfull' : align ((aggregateWords es)[0]'(by simpa [aggregateWords_length] using hb0))
        ((aggregateWords es)[1]'(by simpa [aggregateWords_length] using hb1)) =
        ((aggregateWords es)[0]'(by simpa [aggregateWords_length] using hb0)).length := hfull
    rw [h0, h1] at hfull'
    simpa using hfull'
  calc
    FreeGroup.norm ((es[0]'(hb0)) * (es[1]'(hb1)))
        = ((es[0]'(hb0)) * (es[1]'(hb1))).toWord.length := rfl
    _ = (FreeGroup.reduce (((es[0]'(hb0)).toWord) ++ ((es[1]'(hb1)).toWord))).length := by
        rw [FreeGroup.toWord_mul]
    _ = ((es[0]'(hb0)).toWord).length + ((es[1]'(hb1)).toWord).length
          - 2 * align ((es[0]'(hb0)).toWord) ((es[1]'(hb1)).toWord) :=
        reduce_append_align ((es[0]'(hb0)).toWord) ((es[1]'(hb1)).toWord)
          (FreeGroup.isReduced_toWord) (FreeGroup.isReduced_toWord)
    _ = ((es[1]'(hb1)).toWord).length - ((es[0]'(hb0)).toWord).length := by
        rw [halign]
        omega
    _ < ((es[1]'(hb1)).toWord).length := by
        apply Nat.sub_lt
        · exact hpos1
        · exact hpos
    _ = FreeGroup.norm (es[1]'(hb1)) := rfl

/-- **First-block boundary move.**  A confined first factor of an image
aggregate is shortened by an elementary closure move: `N (α·γ) < N α`. -/
theorem boundary_zero_move {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (es : List (FreeGroup (Fin n))) (himg : ImageAggregate α es)
    (hred : SystemReduced es) (hk : 2 ≤ es.length)
    (hconf : Confined (aggregateWords es) 0) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ N (α * γ) < N α := by
  have hb0 : 0 < es.length := by omega
  have hb1 : 1 < es.length := by omega
  exact confined_strict_right_move α es himg hred hb0 hb1
    (confined_zero_strict es hred hk hconf)

/-- **Last-block strict junction.**  If the last factor of an image aggregate
is confined, its product with the preceding factor is strictly shorter than
the preceding: `|es[j-1]·es[j]| < |es[j-1]|` (for `j + 1 = es.length`). -/
theorem confined_last_strict {n : ℕ} (es : List (FreeGroup (Fin n)))
    (hred : SystemReduced es) (hk : 2 ≤ es.length)
    {j : ℕ} (hj : j < es.length) (hlast : j + 1 = es.length)
    (hconf : Confined (aggregateWords es) j) :
    FreeGroup.norm ((es[j - 1]'(by omega)) * (es[j]'(hj)))
        < FreeGroup.norm (es[j - 1]'(by omega)) := by
  classical
  have hj0 : 0 < j := by omega
  have h2F : 2 ≤ (aggregateWords es).length := by
    rw [aggregateWords_length]
    exact hk
  have hfull := confined_last_full_align (aggregateWords es) (redFs es)
    (by simpa [aggregateWords_length] using hj) h2F
    (by rw [aggregateWords_length]; exact hlast) hconf
  have hm : j - 1 < es.length := by omega
  have hjmF : (aggregateWords es)[j - 1]'(by simpa [aggregateWords_length] using hm) = (es[j - 1]'(hm)).toWord :=
    Fsj_eq es hm
  have hjF : (aggregateWords es)[j]'(by simpa [aggregateWords_length] using hj) = (es[j]'(hj)).toWord :=
    Fsj_eq es hj
  have hnt : (es[j]'(hj)).toWord ≠ [] := word_nz_of_ne_one (es[j]'(hj)) (hred.1 _ (List.getElem_mem hj))
  have hpos : 0 < (es[j]'(hj)).toWord.length := by
    rw [List.length_pos_iff_ne_nil]
    exact hnt
  have hpos0 : 0 < (es[j - 1]'(hm)).toWord.length := by
    rw [List.length_pos_iff_ne_nil]
    exact word_nz_of_ne_one (es[j - 1]'(hm)) (hred.1 _ (List.getElem_mem hm))
  have halign : align ((es[j - 1]'(hm)).toWord) ((es[j]'(hj)).toWord) = ((es[j]'(hj)).toWord).length := by
    rw [hjmF, hjF] at hfull
    simpa using hfull
  calc
    FreeGroup.norm ((es[j - 1]'(hm)) * (es[j]'(hj)))
        = ((es[j - 1]'(hm)) * (es[j]'(hj))).toWord.length := rfl
    _ = (FreeGroup.reduce (((es[j - 1]'(hm)).toWord) ++ ((es[j]'(hj)).toWord))).length := by
        rw [FreeGroup.toWord_mul]
    _ = ((es[j - 1]'(hm)).toWord).length + ((es[j]'(hj)).toWord).length
          - 2 * align ((es[j - 1]'(hm)).toWord) ((es[j]'(hj)).toWord) :=
        reduce_append_align ((es[j - 1]'(hm)).toWord) ((es[j]'(hj)).toWord)
          (FreeGroup.isReduced_toWord) (FreeGroup.isReduced_toWord)
    _ = ((es[j - 1]'(hm)).toWord).length - ((es[j]'(hj)).toWord).length := by
        rw [halign]
        omega
    _ < ((es[j - 1]'(hm)).toWord).length := by
        apply Nat.sub_lt
        · exact hpos0
        · exact hpos
    _ = FreeGroup.norm (es[j - 1]'(hm)) := rfl

/-- **Last-block boundary move.**  A confined last factor of an image
aggregate is shortened by an elementary closure move: `N (α·γ) < N α`. -/
theorem boundary_last_move {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (es : List (FreeGroup (Fin n))) (himg : ImageAggregate α es)
    (hred : SystemReduced es) (hk : 2 ≤ es.length)
    {j : ℕ} (hj : j < es.length) (hlast : j + 1 = es.length)
    (hconf : Confined (aggregateWords es) j) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ N (α * γ) < N α := by
  have hm : j - 1 < es.length := by omega
  exact confined_strict_left_move α es himg hred hj (by omega) hm
    (confined_last_strict es hred hk hj hlast hconf)

/-- **The complete per-factor dispatch.**  For a confined factor (in any
position) of an image aggregate of length ≥ 2: either an elementary closure
move strictly decreases `N`, or the factor is interior and the balanced
(Fall II) content holds (`es[j] = A ++ B`, `|A| = |B|`, neighbours covering
the two halves).  Boundary confined factors always fall into the strict
case; interior factors are dispatched by `confined_factor_dispatch`. -/
theorem confined_factor_reduces {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (es : List (FreeGroup (Fin n))) (himg : ImageAggregate α es)
    (hred : SystemReduced es) (hk : 2 ≤ es.length)
    {j : ℕ} (hj : j < es.length) (hconf : Confined (aggregateWords es) j) :
    (∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ N (α * γ) < N α) ∨
    (∃ (_hj0 : 0 < j) (hj1 : j + 1 < es.length) (hm : j - 1 < es.length),
      ∃ (A B X Z : List (Fin n × Bool)),
        (es[j]).toWord = A ++ B ∧ A.length = B.length ∧
        (es[j - 1]).toWord = X ++ FreeGroup.invRev A ∧
        (es[j + 1]).toWord = FreeGroup.invRev B ++ Z) := by
  by_cases hj0 : 0 < j
  · by_cases hjk : j + 1 < es.length
    · -- interior: dispatch to strict move or balanced content
      have hm : j - 1 < es.length := by omega
      rcases confined_factor_dispatch α es himg hred hj hj0 hjk hm hconf with hs | hbal
      · left
        exact hs
      · right
        exact ⟨hj0, hjk, hm, hbal⟩
    · -- right boundary: j + 1 = es.length, 0 < j
      left
      have hlast : j + 1 = es.length := by omega
      exact boundary_last_move α es himg hred hk hj hlast hconf
  · -- left boundary: j = 0
    left
    have hj0' : j = 0 := by omega
    subst j
    exact boundary_zero_move α es himg hred hk hconf

end Submission.Nielsen
