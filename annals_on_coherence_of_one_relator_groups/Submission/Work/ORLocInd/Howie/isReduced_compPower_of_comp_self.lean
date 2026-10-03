/-
# Powers of a cyclically reduced closed path are reduced

For a closed path `q` the `m`-fold repetition `Quiver.Path.compPower q m` is reduced as soon as
`q` is reduced and *the square* `q.comp q` is reduced: the only possible backtrack of a
concatenation of copies of `q` is either a backtrack inside one copy (excluded by `q` being
reduced) or a backtrack straddling a join, and every join looks like the join of `q` with `q`
(excluded by `q.comp q` being reduced).  See
`Submission/Work/ORLocInd/Howie/isReduced_comp.lean` for the underlying characterization
`Quiver.Path.isReduced_comp_iff`.

The last three lemmas transfer this to the vocabulary of
`Work.ORLocInd.Howie.IsCyclicallyReduced` (`Submission/Work/ORLocInd/Howie/Relator.lean`).

**Note for users.**  `Work.ORLocInd.Howie.IsCyclicallyReduced q` (as defined: "`q` is not of the
form `e.toPath.comp (q'.cons (reverse e))`") is vacuous for a closed path of length `1`, so it
does *not* exclude a single *self-inverse* loop `e` (`Quiver.reverse e = e`).  For such a path
(`q = e.toPath`, one arrow, `e` its own reverse) the statement "`compPower q m` is reduced for all
`m`" is *false*: `compPower q 2 = e · e` deletes the backtrack `e · e⁻¹ = e · e`.  Consequently:

* `isReduced_compPower_of_comp_self` is the correct general statement (hypothesis
  `(q.comp q).IsReduced`, which is exactly the "cyclically reduced" condition in the usual
  arrow-by-arrow sense);
* `isReduced_compPower_of_cyclic` adds the missing hypothesis `hloop` ruling out the single
  self-inverse loop, and is what one gets from the definition above;
* `isReduced_compPower_of_cyclic_of_noSelfLoop` is the special case of that in which the whole
  graph has no self-inverse loop, i.e. an edge is never equal to its own reverse (Serre's
  convention for graphs).
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.PathReduced
import Submission.Work.ORLocInd.Howie.isReduced_comp
import Submission.Work.ORLocInd.Howie.endsWith_comp
import Submission.Work.ORLocInd.Howie.Relator
import Submission.Work.ORBassSerre.Tree.Prefix.qpath_exists_eq_comp_of_comp_eq

set_option autoImplicit false

universe u

namespace Quiver.Path

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-- **A power of a closed path is reduced if the path is reduced and its square is reduced.**
(Every backtrack of `q.comp (compPower q k)` is inside a copy of `q` or straddles the join; the
join is a join of `q` with `q`.) -/
theorem isReduced_compPower_of_comp_self {v : V} {q : Path v v} (hq : q.IsReduced)
    (h2 : (q.comp q).IsReduced) (m : ℕ) : (compPower q m).IsReduced := by
  induction m with
  | zero => exact IsReduced.nil v
  | succ m ih =>
    rw [compPower_succ]
    refine isReduced_comp_iff.2 ⟨hq, ih, ?_⟩
    rintro ⟨x, p', e, q', hp, hq'⟩
    have hqpos : 1 ≤ q.length := by
      have hl : (compPower q m).length = 1 + q'.length := by
        rw [hq', Quiver.Path.length_comp, Quiver.Path.length_toPath]
      rw [Quiver.Path.compPower_length] at hl
      have hmul : 1 ≤ m * q.length := by omega
      rcases Nat.eq_zero_or_pos q.length with h | h
      · rw [h, Nat.mul_zero] at hmul
        omega
      · exact h
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · rw [hm0, compPower_zero] at hq'
      have hl := congrArg Path.length hq'
      simp only [Path.length_nil, Path.length_comp, Path.length_toPath] at hl
      omega
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      rw [compPower_succ] at hq'
      obtain ⟨t, ht⟩ := Work.ORBassSerre.Tree.Prefix.exists_comp_of_length_le hq'.symm hqpos
      exact joinConflict_not_isReduced ⟨x, p', e, t, hp, ht⟩ h2

end Quiver.Path

namespace Work.ORLocInd.Howie

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]
variable {v : V}

/-- A `q` which is cyclically reduced in the sense of `IsCyclicallyReduced` and which is not a
single self-inverse loop has no backtrack straddling the join of `q` with itself. -/
theorem not_joinConflict_self_of_isCyclicallyReduced {q : Quiver.Path v v}
    (hcyc : IsCyclicallyReduced q)
    (hloop : ∀ f : v ⟶ v, q = f.toPath → Quiver.reverse f ≠ f) :
    ¬ Quiver.Path.JoinConflict q q := by
  rintro ⟨x, p', e, q', hp, hq'⟩
  have hlen : 1 ≤ q.length := by
    have hl := congrArg Quiver.Path.length hp
    simp only [Quiver.Path.length_cons] at hl
    omega
  rcases Nat.lt_or_ge q.length 2 with hlt | hge
  · -- `q` consists of a single arrow
    have hp'len : p'.length = 0 := by
      have hl := congrArg Quiver.Path.length hp
      simp only [Quiver.Path.length_cons] at hl
      omega
    obtain rfl : v = x := Quiver.Path.eq_of_length_zero p' hp'len
    have hp'nil : p' = Quiver.Path.nil := Quiver.Path.eq_nil_of_length_zero p' hp'len
    have hqe : q = e.toPath := by rw [hp, hp'nil]; rfl
    have hq'len : q'.length = 0 := by
      have hl := congrArg Quiver.Path.length hq'
      simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath] at hl
      omega
    have hq'nil : q' = Quiver.Path.nil := Quiver.Path.eq_nil_of_length_zero q' hq'len
    have hqre : q = (Quiver.reverse e).toPath := by rw [hq', hq'nil, Quiver.Path.comp_nil]
    have hre : Quiver.reverse e = e := by
      apply Work.ORBassSerre.Path.Reduction.toPath_inj
      rw [← hqe, ← hqre]
    exact hloop e hqe hre
  · -- `q` has length at least two
    have hq'pos : q'.length ≠ 0 := by
      have hl := congrArg Quiver.Path.length hq'
      simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath] at hl
      omega
    have hends : Quiver.Path.EndsWith q' e := by
      have h1 : Quiver.Path.EndsWith ((Quiver.reverse e).toPath.comp q') e := by
        rw [← hq']
        exact ⟨p', hp⟩
      exact (endsWith_comp hq'pos e).1 h1
    obtain ⟨p'', hp''⟩ := hends
    exact hcyc ⟨x, Quiver.reverse e, p'', by rw [hq', hp'', Quiver.reverse_reverse]⟩

/-- If `q` is reduced and cyclically reduced and is not a single self-inverse loop, then its
square is reduced (i.e. `q` is cyclically reduced in the arrow-by-arrow sense). -/
theorem isReduced_comp_self_of_isCyclicallyReduced {q : Quiver.Path v v} (hq : q.IsReduced)
    (hcyc : IsCyclicallyReduced q)
    (hloop : ∀ f : v ⟶ v, q = f.toPath → Quiver.reverse f ≠ f) :
    (q.comp q).IsReduced :=
  Quiver.Path.isReduced_comp_iff.2
    ⟨hq, hq, not_joinConflict_self_of_isCyclicallyReduced hcyc hloop⟩

/-- A path which starts with `e` and ends with `reverse e` is a closed path whose join with
itself is a backtrack. -/
theorem joinConflict_self_of_cyclic_decomposition {q : Quiver.Path v v} {u : V} (e : v ⟶ u)
    (q' : Quiver.Path u u) (h : q = e.toPath.comp (q'.cons (Quiver.reverse e))) :
    Quiver.Path.JoinConflict q q :=
  ⟨u, e.toPath.comp q', Quiver.reverse e, q'.cons (Quiver.reverse e),
    by rw [h, Quiver.Path.comp_cons],
    by rw [h, Quiver.reverse_reverse]⟩

/-- **Characterization of `q.comp q` being reduced.**  For a closed path `q` the square `q.comp q`
is reduced exactly when `q` is reduced, is cyclically reduced, and is not a single self-inverse
loop.  In other words the definition
`IsCyclicallyReduced q := ¬ ∃ u e q', q = e.toPath.comp (q'.cons (reverse e))` is missing exactly
the exclusion of a one-arrow self-inverse loop. -/
theorem isReduced_comp_self_iff {q : Quiver.Path v v} :
    (q.comp q).IsReduced ↔ q.IsReduced ∧ IsCyclicallyReduced q ∧
      (∀ f : v ⟶ v, q = f.toPath → Quiver.reverse f ≠ f) := by
  constructor
  · intro h
    refine ⟨h.of_comp, ?_, ?_⟩
    · rintro ⟨u, e, q', hdecomp⟩
      exact Quiver.Path.joinConflict_not_isReduced
        (joinConflict_self_of_cyclic_decomposition e q' hdecomp) h
    · intro f hf hrev
      refine Quiver.Path.joinConflict_not_isReduced ?_ h
      exact ⟨v, Quiver.Path.nil, f, Quiver.Path.nil, by rw [hf]; rfl, by rw [hf, hrev]; rfl⟩
  · rintro ⟨hq, hcyc, hloop⟩
    exact isReduced_comp_self_of_isCyclicallyReduced hq hcyc hloop

/-- **The `m`-fold repetition of a cyclically reduced closed path is reduced**, provided the path
is not a single self-inverse loop (the one case the definition of `IsCyclicallyReduced` misses;
see the module documentation). -/
theorem isReduced_compPower_of_cyclic {q : Quiver.Path v v} (hq : q.IsReduced)
    (hcyc : IsCyclicallyReduced q)
    (hloop : ∀ f : v ⟶ v, q = f.toPath → Quiver.reverse f ≠ f) (m : ℕ) :
    (Quiver.Path.compPower q m).IsReduced :=
  Quiver.Path.isReduced_compPower_of_comp_self hq
    (isReduced_comp_self_of_isCyclicallyReduced hq hcyc hloop) m

/-- The same, under the global hypothesis that no arrow of the graph is its own reverse (as in
Serre's definition of a graph). -/
theorem isReduced_compPower_of_cyclic_of_noSelfLoop {q : Quiver.Path v v} (hq : q.IsReduced)
    (hcyc : IsCyclicallyReduced q)
    (hself : ∀ f : v ⟶ v, Quiver.reverse f ≠ f) (m : ℕ) :
    (Quiver.Path.compPower q m).IsReduced :=
  isReduced_compPower_of_cyclic hq hcyc (fun f _ => hself f) m

end Work.ORLocInd.Howie
