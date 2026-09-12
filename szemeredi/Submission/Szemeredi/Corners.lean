import Mathlib
import Submission.Szemeredi.Basic

/-!
# Szemerédi's theorem from the multidimensional corners theorem

This file formalises the classical reduction

  *d-dimensional corners theorem (cyclic groups, every d ≥ 1)*  ⇒  *finite
  Szemerédi theorem for (d+1)-term arithmetic progressions*,

which generalises to every dimension the way mathlib's `corners_theorem`
(d = 2) implies Roth's theorem (3-term progressions).  The main theorem is
`finiteSzemeredi_of_cornersD`; see the module docstring in
`Submission.Szemeredi.Corners` for the full architecture.
-/

open scoped BigOperators
open Finset

namespace Szemeredi

section Group

variable {G : Type*} [AddCommGroup G]

/-- A nontrivial `d`-dimensional axis-parallel corner of the set `B ⊆ G^d`:
the point `x` and all points `x + t·eᵢ` (`i < d`) lie in `B`, where `t ≠ 0`.

(Equivalently, an affine copy of `{0} ∪ {e₁, …, e_d}` in `B`.) -/
def IsCornerD {d : ℕ} (B : Set (Fin d → G)) (x : Fin d → G) (t : G) : Prop :=
  t ≠ 0 ∧ x ∈ B ∧
    ∀ i : Fin d, (fun j : Fin d => x j + if j = i then t else 0) ∈ B

/-- A set containing no nontrivial corner. -/
def IsCornerFreeD {d : ℕ} (B : Set (Fin d → G)) : Prop :=
  ¬ ∃ x t, IsCornerD B x t

lemma IsCornerD.mono {d : ℕ} {B C : Set (Fin d → G)} (hBC : B ⊆ C) {x t}
    (h : IsCornerD B x t) : IsCornerD C x t := by
  exact ⟨h.1, hBC h.2.1, fun i => hBC (h.2.2 i)⟩

lemma IsCornerFreeD.mono {d : ℕ} {B C : Set (Fin d → G)} (hBC : B ⊆ C)
    (hC : IsCornerFreeD C) : IsCornerFreeD B := by
  intro hB
  rcases hB with ⟨x, t, hxt⟩
  exact hC ⟨x, t, hxt.mono hBC⟩

end Group

/-- The **finite corners theorem in dimension `d` over cyclic groups** (density form):

for every density `ε > 0` there is a bound `N₀` such that every subset
`B ⊆ (ZMod M)^d` with `ε·M^d ≤ |B|` contains a nontrivial corner, whenever
`M ≥ N₀`.  This is the multidimensional generalisation of mathlib's
`corners_theorem` (which is the `d = 2` case for arbitrary finite abelian
groups); the cases `d ≥ 3` are open (equivalent in difficulty to Szemerédi's
theorem itself). -/
def CornersFiniteD (d : ℕ) (ε : ℝ) : Prop :=
  ∃ N₀ : ℕ, ∀ (M : ℕ), 1 ≤ M → N₀ ≤ M →
    ∀ B : Finset (Fin d → ZMod M),
      ε * (M : ℝ) ^ d ≤ (B.card : ℝ) →
        ∃ x : Fin d → ZMod M, ∃ t : ZMod M, IsCornerD (B : Set (Fin d → ZMod M)) x t

end Szemeredi
