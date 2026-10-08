/-
The three closed finite checks underlying `Work.CORE4.A4s`.

* `cent1`: the order-`3` elements of `N_{A₇}(V₁)` centralising `V₁` are exactly `k10` and `k10 * k10`;
* `cent2`: no order-`3` element of `N_{A₇}(V₂)` centralises `V₂`;
* `check1`: for each involution `s ∈ n1Inv` inverting `k10` there is an explicit even witness `e`.

Each is a closed statement about explicit permutations of `Fin 7`; the explicit `Finset`
literals are expanded with `Finset.mem_insert`/`Finset.mem_singleton` and the resulting
finitely many concrete cases are discharged by `decide`.  (This is the pattern of
`Submission/Work/CORE4/A7S4/n2Check.lean`; a single global `decide` is much slower and hits
`maxRecDepth`.)
-/
import Mathlib
import Submission.Work.CORE4.A4sDefs

namespace Work.CORE4.A4s

open Work.CORE4

/-- The `0`-th witness of `wit1`. -/
private def W0 : Equiv.Perm (Fin 7) :=
  (Equiv.swap 1 4 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 6 : Equiv.Perm (Fin 7))

/-- The `1`-th witness of `wit1`. -/
private def W1 : Equiv.Perm (Fin 7) :=
  (Equiv.swap 1 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 4 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 5 : Equiv.Perm (Fin 7))

/-- The `2`-th witness of `wit1`. -/
private def W2 : Equiv.Perm (Fin 7) :=
  (Equiv.swap 1 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 4 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 6 : Equiv.Perm (Fin 7))

/-- The `3`-th witness of `wit1`. -/
private def W3 : Equiv.Perm (Fin 7) :=
  (Equiv.swap 1 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 4 : Equiv.Perm (Fin 7))

/-- The `4`-th witness of `wit1`. -/
private def W4 : Equiv.Perm (Fin 7) :=
  (Equiv.swap 1 4 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 6 : Equiv.Perm (Fin 7))

/-- The `5`-th witness of `wit1`. -/
private def W5 : Equiv.Perm (Fin 7) :=
  (Equiv.swap 1 4 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 5 : Equiv.Perm (Fin 7))

/-- The `6`-th witness of `wit1`. -/
private def W6 : Equiv.Perm (Fin 7) :=
  (Equiv.swap 1 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 4 : Equiv.Perm (Fin 7))

/-- The `7`-th witness of `wit1`. -/
private def W7 : Equiv.Perm (Fin 7) :=
  (Equiv.swap 1 4 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 6 : Equiv.Perm (Fin 7))

/-- The `8`-th witness of `wit1`. -/
private def W8 : Equiv.Perm (Fin 7) :=
  (Equiv.swap 1 4 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 5 : Equiv.Perm (Fin 7))

/-- The `9`-th witness of `wit1`. -/
private def W9 : Equiv.Perm (Fin 7) :=
  (Equiv.swap 0 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 4 : Equiv.Perm (Fin 7))

/-- The `10`-th witness of `wit1`. -/
private def W10 : Equiv.Perm (Fin 7) :=
  (Equiv.swap 0 4 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 6 : Equiv.Perm (Fin 7))

/-- The `11`-th witness of `wit1`. -/
private def W11 : Equiv.Perm (Fin 7) :=
  (Equiv.swap 0 4 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 5 : Equiv.Perm (Fin 7))

/-- The `12`-th witness of `wit1`. -/
private def W12 : Equiv.Perm (Fin 7) :=
  (Equiv.swap 0 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 4 : Equiv.Perm (Fin 7))

/-- The `13`-th witness of `wit1`. -/
private def W13 : Equiv.Perm (Fin 7) :=
  (Equiv.swap 0 4 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 6 : Equiv.Perm (Fin 7))

/-- The `14`-th witness of `wit1`. -/
private def W14 : Equiv.Perm (Fin 7) :=
  (Equiv.swap 0 4 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 5 : Equiv.Perm (Fin 7))

/-- The `15`-th witness of `wit1`. -/
private def W15 : Equiv.Perm (Fin 7) :=
  (Equiv.swap 0 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 4 : Equiv.Perm (Fin 7))

/-- The `16`-th witness of `wit1`. -/
private def W16 : Equiv.Perm (Fin 7) :=
  (Equiv.swap 0 4 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 6 : Equiv.Perm (Fin 7))

/-- The `17`-th witness of `wit1`. -/
private def W17 : Equiv.Perm (Fin 7) :=
  (Equiv.swap 0 4 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 3 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 2 5 : Equiv.Perm (Fin 7))

/-- **`C_{A₇}(V₁)` has a unique subgroup of order `3`.**  The elements of `n1Ord3` commuting
with `tP` and `uP` are exactly `k10 = (4 5 6)` and `k10 * k10`. -/
theorem cent1 : ∀ k : Equiv.Perm (Fin 7), k ∈ n1Ord3 → k * tP = tP * k → k * uP = uP * k →
    k ∈ k1List := by
  intro k hk h1 h2
  simp only [n1Ord3, Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact absurd h1 (by decide)
    | exact absurd h2 (by decide)
    | (simp only [k1List, Finset.mem_insert, Finset.mem_singleton]; decide)

/-- **`C_{A₇}(V₂)` contains no element of order `3`.**  No element of `n2Ord3` centralises
`V₂ = ⟨tP, vP⟩`. -/
theorem cent2 : ∀ k : Equiv.Perm (Fin 7), k ∈ n2Ord3 →
    ¬ (k * tP = tP * k ∧ k * vP = vP * k) := by
  intro k hk
  simp only [n2Ord3, Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/-- **`A4s` finite check.**  For each `s ∈ n1Inv` with `s * k10 * s⁻¹ = k10⁻¹` one of the
explicit witnesses `W0, …, W17` commutes with `s`, normalises `V₁` after conjugating `k10`,
and moves `⟨k10⟩`. -/
theorem check1 : ∀ s : Equiv.Perm (Fin 7), s ∈ n1Inv → s * k10 * s⁻¹ = k10⁻¹ →
    ∃ e : Equiv.Perm (Fin 7), e ∈ wit1 ∧ e * s = s * e ∧ Equiv.Perm.sign e = 1 ∧
      InN1P (e * k10 * e⁻¹) ∧ e * k10 * e⁻¹ ≠ k10 ∧ e * k10 * e⁻¹ ≠ k10 * k10 := by
  intro s hs h
  simp only [n1Inv, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact absurd h (by decide)
    | exact ⟨(W0 : Equiv.Perm (Fin 7)), by decide⟩
    | exact ⟨(W1 : Equiv.Perm (Fin 7)), by decide⟩
    | exact ⟨(W2 : Equiv.Perm (Fin 7)), by decide⟩
    | exact ⟨(W3 : Equiv.Perm (Fin 7)), by decide⟩
    | exact ⟨(W4 : Equiv.Perm (Fin 7)), by decide⟩
    | exact ⟨(W5 : Equiv.Perm (Fin 7)), by decide⟩
    | exact ⟨(W6 : Equiv.Perm (Fin 7)), by decide⟩
    | exact ⟨(W7 : Equiv.Perm (Fin 7)), by decide⟩
    | exact ⟨(W8 : Equiv.Perm (Fin 7)), by decide⟩
    | exact ⟨(W9 : Equiv.Perm (Fin 7)), by decide⟩
    | exact ⟨(W10 : Equiv.Perm (Fin 7)), by decide⟩
    | exact ⟨(W11 : Equiv.Perm (Fin 7)), by decide⟩
    | exact ⟨(W12 : Equiv.Perm (Fin 7)), by decide⟩
    | exact ⟨(W13 : Equiv.Perm (Fin 7)), by decide⟩
    | exact ⟨(W14 : Equiv.Perm (Fin 7)), by decide⟩
    | exact ⟨(W15 : Equiv.Perm (Fin 7)), by decide⟩
    | exact ⟨(W16 : Equiv.Perm (Fin 7)), by decide⟩
    | exact ⟨(W17 : Equiv.Perm (Fin 7)), by decide⟩

end Work.CORE4.A4s
