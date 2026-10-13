/-
  WilC4/UnifDefs : the vocabulary for `unifFinite_of_omin` (uniform finiteness of
  `rexp`-existential families from o-minimality of every model of `TR`).

  The uniformity argument runs through a *first-order shadow* of "the fibre has at least
  `N + 1` connected components": `AltChain N S` says that `S` contains `N + 1` points
  separated by `N` points outside `S`.  This is first-order (so it transfers to models, and
  Łoś applies at a nonstandard parameter), and in a linear order it is equivalent to
  "`S` has at least `N + 1` order-convex components":

  * `N + 1` points of `S` separated by points outside `S` lie in pairwise distinct convex
    components (a convex set containing two of them would contain the separating point);
  * conversely, distinct convex components of `S` are separated by points outside `S`, and
    two distinct points always have a point between them, so `N + 1` components give a chain.
-/
import Mathlib
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilC2.Basic

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

/-- `AltChain N S`: `S` contains `N + 1` points `x 0, …, x N` with the points `y j` strictly
between `x j` and `x (j+1)`, and all the `y j` lie *outside* `S`.  In a linear order this means
that `S` has at least `N + 1` order-convex components. -/
def AltChain {M : Type*} [LT M] (N : ℕ) (S : Set M) : Prop :=
  ∃ x : Fin (N + 1) → M, ∃ y : Fin N → M,
    (∀ j, x j ∈ S) ∧
    (∀ j : Fin N, y j ∉ S ∧ x (Fin.castSucc j) < y j ∧ y j < x (Fin.succ j))

theorem altChain_zero_iff {M : Type*} [LT M] {S : Set M} : AltChain 0 S ↔ S.Nonempty := by
  constructor
  · rintro ⟨x, y, hx, -⟩
    exact ⟨x 0, hx 0⟩
  · rintro ⟨t, ht⟩
    exact ⟨fun _ => t, fun j => j.elim0, fun _ => ht, fun j => j.elim0⟩

theorem altChain_nonempty {M : Type*} [LT M] {S : Set M} {N : ℕ} (h : AltChain N S) :
    S.Nonempty := by
  obtain ⟨x, y, hx, hy⟩ := h
  exact ⟨x 0, hx 0⟩

/-- The separating points make the chain strictly increasing. -/
theorem altChain_lt {M : Type*} [LinearOrder M] {S : Set M} {N : ℕ} {x : Fin (N + 1) → M}
    {y : Fin N → M} (hy : ∀ j : Fin N, y j ∉ S ∧ x (Fin.castSucc j) < y j ∧ y j < x (Fin.succ j))
    {i j : Fin (N + 1)} (hij : i < j) : x i < x j :=
  Fin.strictMono_iff_lt_succ.mpr
    (fun k => lt_trans (hy k).2.1 (hy k).2.2) hij

/-- `AltChain` is monotone in `N` (downwards). -/
theorem altChain_mono {M : Type*} [LT M] {S : Set M} {N N' : ℕ} (h : AltChain N S)
    (hN : N' ≤ N) : AltChain N' S := by
  obtain ⟨x, y, hx, hy⟩ := h
  have h1 : N' + 1 ≤ N + 1 := by omega
  refine ⟨fun j => x (Fin.castLE h1 j), fun j => y (Fin.castLE hN j), fun j => hx _, ?_⟩
  intro j
  have hcs : Fin.castLE h1 (Fin.castSucc j) = Fin.castSucc (Fin.castLE hN j) := Fin.ext rfl
  have hsc : Fin.castLE h1 (Fin.succ j) = Fin.succ (Fin.castLE hN j) := Fin.ext rfl
  show y (Fin.castLE hN j) ∉ S ∧ x (Fin.castLE h1 (Fin.castSucc j)) < y (Fin.castLE hN j) ∧
    y (Fin.castLE hN j) < x (Fin.castLE h1 (Fin.succ j))
  rw [hcs, hsc]
  exact hy (Fin.castLE hN j)

end Work.WilC4
