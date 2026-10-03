/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Junction backtracking in a tree

A closed walk in a tree, decomposed into reduced non-empty pieces, must backtrack at one of the
junctions between consecutive pieces: for some `j` with `j + 1 < n`, the `j`-th path ends with an
arrow `f` and the `(j+1)`-st path begins with `f⁻¹`.

The proof concatenates the first `k` pieces into a single path and shows, by induction on `k`,
that this concatenation is reduced as long as no junction backtracks occur: a backtrack of
`chain ≫ u k` either lives inside one of the two factors (impossible, both are reduced) or
straddles the junction, in which case the last arrow of the concatenation — which is the last
arrow of the last piece `u (k-1)`, the pieces being non-empty — produces a junction backtrack.
For `k = n` the concatenation is a closed reduced path in a tree, hence `nil`, while it has length
at least `n ≥ 1`.
-/
import Mathlib
import Submission.Work.ORBassSerre.Interface

universe u

namespace Work.ORLocInd.CohenLyndon

open Quiver

/- The auxiliary constructions of `Work.ORLocInd.CohenLyndon.bsJunctionBacktrack`, kept in their
own namespace so as not to collide with the other developments of this area. -/
namespace BsjbAux

/-! ## Concatenating the pieces -/

/-- The concatenation of the first `k` paths of the walk, a path from `z 0` to `z k`. -/
def chain {V : Type u} [Quiver V]
    (z : ℕ → V) (u : (j : ℕ) → Quiver.Path (z j) (z (j + 1))) :
    (k : ℕ) → Quiver.Path (z 0) (z k)
  | 0 => Quiver.Path.nil
  | k + 1 => (chain z u k).comp (u k)

theorem chain_zero {V : Type u} [Quiver V]
    (z : ℕ → V) (u : (j : ℕ) → Quiver.Path (z j) (z (j + 1))) :
    chain z u 0 = Quiver.Path.nil := rfl

theorem chain_succ {V : Type u} [Quiver V]
    (z : ℕ → V) (u : (j : ℕ) → Quiver.Path (z j) (z (j + 1))) (k : ℕ) :
    chain z u (k + 1) = (chain z u k).comp (u k) := rfl

theorem chain_one {V : Type u} [Quiver V]
    (z : ℕ → V) (u : (j : ℕ) → Quiver.Path (z j) (z (j + 1))) :
    chain z u 1 = u 0 := by
  rw [chain_succ, chain_zero, Quiver.Path.nil_comp]

/-- The concatenation of the first `k` pieces has length at least `k`, provided all the pieces
involved are non-empty. -/
theorem chain_length_le {V : Type u} [Quiver V]
    (z : ℕ → V) (u : (j : ℕ) → Quiver.Path (z j) (z (j + 1))) (n : ℕ)
    (hpos : ∀ j, j < n → 0 < (u j).length) :
    ∀ k, k ≤ n → k ≤ (chain z u k).length := by
  intro k
  induction k with
  | zero => intro _; simp [chain_zero]
  | succ k ih =>
    intro hk
    rw [chain_succ, Quiver.Path.length_comp]
    have h1 := ih (by omega)
    have h2 := hpos k (by omega)
    omega

/-- Splitting off the last arrow of the second factor of a composition: if `p ≫ q` ends with the
arrow `e` and `q` is non-empty, then `q` itself ends with `e`. -/
theorem split_last {V : Type u} [Quiver V] {a b c x : V} {p : Quiver.Path a b}
    {q : Quiver.Path b c} {r : Quiver.Path a x} {e : x ⟶ c}
    (h : p.comp q = r.cons e) (hq : 0 < q.length) :
    ∃ q' : Quiver.Path b x, q = q'.cons e := by
  have h' : p.comp q = r.comp e.toPath := by rw [h, Quiver.Path.comp_toPath_eq_cons]
  rcases le_total p.length r.length with hle | hle
  · obtain ⟨r₀, hr₀⟩ := Work.ORBassSerre.Tree.Prefix.exists_comp_of_length_le h' hle
    refine ⟨r₀, ?_⟩
    have h2 : p.comp q = p.comp (r₀.comp e.toPath) := by rw [h', hr₀, Quiver.Path.comp_assoc]
    have h3 : q = r₀.comp e.toPath := Quiver.Path.comp_injective_right p h2
    rwa [Quiver.Path.comp_toPath_eq_cons] at h3
  · obtain ⟨r₀, hr₀⟩ := Work.ORBassSerre.Tree.Prefix.exists_comp_of_length_le h'.symm hle
    have h2 : r.comp (r₀.comp q) = r.comp e.toPath := by
      rw [← Quiver.Path.comp_assoc, ← hr₀]; exact h'
    have h3 : r₀.comp q = e.toPath := Quiver.Path.comp_injective_right r h2
    have hl : r₀.length + q.length = 1 := by
      have := congrArg Quiver.Path.length h3
      simpa using this
    have hx : x = b := Quiver.Path.eq_of_length_zero r₀ (by omega)
    subst hx
    have hr0 : r₀ = Quiver.Path.nil := Quiver.Path.eq_nil_of_length_zero r₀ (by omega)
    rw [hr0, Quiver.Path.nil_comp] at h3
    exact ⟨Quiver.Path.nil, by
      rw [h3, ← Quiver.Path.comp_toPath_eq_cons, Quiver.Path.nil_comp]⟩

/-! ## Junction backtracks -/

/-- A junction backtrack at `j`: the `j`-th path ends with an arrow `f` whose reverse is the
first arrow of the `(j+1)`-st path. -/
def JunctionBacktrack {V : Type u} [Quiver V] [Quiver.HasReverse V]
    (z : ℕ → V) (u : (j : ℕ) → Quiver.Path (z j) (z (j + 1))) (j : ℕ) : Prop :=
  ∃ (x : V) (f : x ⟶ z (j + 1)) (u' : Quiver.Path (z j) x) (v' : Quiver.Path x (z (j + 2))),
    u j = u'.cons f ∧ u (j + 1) = (Quiver.reverse f).toPath.comp v'

/-- **No junction backtrack implies a reduced concatenation.**  If none of the junctions
`j, j + 1` with `j + 1 < n` is a backtrack, and all the pieces up to `n` are reduced and
non-empty, then the concatenation of the first `k ≤ n` pieces is reduced. -/
theorem chain_isReduced {V : Type u} [Quiver V] [Quiver.HasReverse V]
    (z : ℕ → V) (u : (j : ℕ) → Quiver.Path (z j) (z (j + 1))) (n : ℕ)
    (hred : ∀ j, j < n → (u j).IsReduced)
    (hpos : ∀ j, j < n → 0 < (u j).length)
    (hno : ∀ j, j + 1 < n → ¬ JunctionBacktrack z u j) :
    ∀ k, k ≤ n → (chain z u k).IsReduced := by
  intro k
  induction k with
  | zero => intro _; rw [chain_zero]; exact Quiver.Path.IsReduced.nil (z 0)
  | succ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      rw [chain_succ, chain_zero, Quiver.Path.nil_comp]
      exact hred 0 (by omega)
    · by_contra hnr
      simp only [Quiver.Path.IsReduced, not_forall, not_not] at hnr
      obtain ⟨w, hw⟩ := hnr
      rw [chain_succ] at hw
      obtain ⟨x, f, u', v', h1, h2, -⟩ :=
        Work.ORBassSerre.Tree.Junction.qpath_exists_cons_of_deleteBacktrack_comp
          (hu := ih (by omega)) (hv := hred k (by omega)) hw
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      rw [chain_succ] at h1
      obtain ⟨q', hq'⟩ := split_last h1 (hpos m (by omega))
      exact hno m (by omega) ⟨x, f, q', v', hq', h2⟩

/-! ## Casting a path along endpoint equalities -/

theorem isReduced_cast {V : Type u} [Quiver V] [Quiver.HasReverse V] {a b a' b' : V}
    (hu : a = a') (hv : b = b') {p : Quiver.Path a b} (h : p.IsReduced) :
    (p.cast hu hv).IsReduced := by
  subst hu; subst hv
  simpa using h

theorem length_cast {V : Type u} [Quiver V] {a b a' b' : V} (hu : a = a') (hv : b = b')
    (p : Quiver.Path a b) : (p.cast hu hv).length = p.length := by
  subst hu; subst hv
  rfl

end BsjbAux

/-! ## The junction backtracking lemma -/

theorem bsJunctionBacktrack {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (hT : Work.ORBassSerre.IsTree V)
    (n : ℕ) (hn : 1 ≤ n) (z : ℕ → V) (u : (j : ℕ) → Quiver.Path (z j) (z (j + 1)))
    (hred : ∀ j, j < n → (u j).IsReduced)
    (hpos : ∀ j, j < n → 0 < (u j).length)
    (hclosed : z n = z 0) :
    ∃ j, j + 1 < n ∧ ∃ (x : V) (f : x ⟶ z (j + 1)) (u' : Quiver.Path (z j) x)
      (v' : Quiver.Path x (z (j + 2))),
      u j = u'.cons f ∧ u (j + 1) = (Quiver.reverse f).toPath.comp v' := by
  by_contra hcon
  have hno : ∀ j, j + 1 < n → ¬ BsjbAux.JunctionBacktrack z u j := by
    intro j hj hjb
    exact hcon ⟨j, hj, hjb⟩
  have hredW : (BsjbAux.chain z u n).IsReduced :=
    BsjbAux.chain_isReduced z u n hred hpos hno n le_rfl
  have hlenW : n ≤ (BsjbAux.chain z u n).length :=
    BsjbAux.chain_length_le z u n hpos n le_rfl
  have hclosedRed : ((BsjbAux.chain z u n).cast rfl hclosed).IsReduced :=
    BsjbAux.isReduced_cast rfl hclosed hredW
  have hnil : (BsjbAux.chain z u n).cast rfl hclosed = Quiver.Path.nil :=
    hT.2 (z 0) _ hclosedRed
  have hlen0 : ((BsjbAux.chain z u n).cast rfl hclosed).length = 0 := by
    rw [hnil, Quiver.Path.length_nil]
  have hlen' : (BsjbAux.chain z u n).length = 0 :=
    (BsjbAux.length_cast rfl hclosed (BsjbAux.chain z u n)).symm.trans hlen0
  omega

end Work.ORLocInd.CohenLyndon
