/-
  Work.WilE9.Gen.gen_diff_defs — vocabulary for `Work.WilE9.Gen.gen_diffSet`.

  `ℝ^{dd0 n}` is the ambient space `(v : ℝ^{n+1}, ε, δ, h, x' : ℝⁿ, y₀, v')` of the
  quantifier-elimination chain that computes the differentiability locus of the graph function
  of a `Gen`-set `G`.  The successive ambients `ℝ^{dd1 n} …` are obtained by deleting the last
  coordinates (the quantifiers, innermost first), and the chain `dD1, dE1, dD2, …` codes the
  ε-δ formula with `Gen`-operations only.
-/
import Mathlib
import Submission.Work.WilE9.Defs
import Submission.Work.WilG0.Defs
import Submission.Work.WilE9.Glue.subst_mem

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical Topology
namespace Work.WilE9.Gen

namespace DiffSet

open WilkiesDesign WilkiesDesign.E

/-! ## 1. The successive ambient dimensions -/

abbrev dd0 (n : ℕ) : ℕ := (n + 1) + 1 + 1 + 1 + n + 1 + 1
abbrev dd1 (n : ℕ) : ℕ := (n + 1) + 1 + 1 + 1 + n + 1
abbrev dd2 (n : ℕ) : ℕ := (n + 1) + 1 + 1 + 1 + n
abbrev dd3 (n : ℕ) : ℕ := (n + 1) + 1 + 1 + 1
abbrev dd4 (n : ℕ) : ℕ := (n + 1) + 1 + 1
abbrev dd5 (n : ℕ) : ℕ := (n + 1) + 1

/-- `max a b ≤ a + b`: used to bound the formats produced by `Gen.union₂`/`Gen.inter₂`. -/
lemma max_le_add (a b : ℕ) : max a b ≤ a + b := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]; omega
  · rw [max_eq_left h]; omega

/-! ## 2. Coordinate indices

Every index is the successor tower of the coordinates that are appended on the way down, which
is what makes the one-line peeling lemmas of §3 work. -/

/-- The `k`-th coordinate of the `v`-block, in the `v`-space `ℝ^{n+1}`. -/
def dvI6 (n : ℕ) (k : Fin (n + 1)) : Fin (n + 1) := k

/-- The `k`-th coordinate of the `v`-block, in `ℝ^{dd5 n} = (v, ε)`. -/
def dvI5 (n : ℕ) (k : Fin (n + 1)) : Fin (dd5 n) := Fin.castSucc (dvI6 n k)

/-- In `ℝ^{dd4 n} = (v, ε, δ)`. -/
def dvI4 (n : ℕ) (k : Fin (n + 1)) : Fin (dd4 n) := Fin.castSucc (dvI5 n k)

/-- In `ℝ^{dd3 n} = (v, ε, δ, h)`. -/
def dvI3 (n : ℕ) (k : Fin (n + 1)) : Fin (dd3 n) := Fin.castSucc (dvI4 n k)

/-- In `ℝ^{dd2 n} = (v, ε, δ, h, x')`. -/
def dvI2 (n : ℕ) (k : Fin (n + 1)) : Fin (dd2 n) := Fin.castAdd n (dvI3 n k)

/-- In `ℝ^{dd1 n} = (v, ε, δ, h, x', y₀)`. -/
def dvI1 (n : ℕ) (k : Fin (n + 1)) : Fin (dd1 n) := Fin.castSucc (dvI2 n k)

/-- In the big space `ℝ^{dd0 n}`. -/
def dvI0 (n : ℕ) (k : Fin (n + 1)) : Fin (dd0 n) := Fin.castSucc (dvI1 n k)

def deI5 (n : ℕ) : Fin (dd5 n) := Fin.last (n + 1)
def deI4 (n : ℕ) : Fin (dd4 n) := Fin.castSucc (deI5 n)
def deI3 (n : ℕ) : Fin (dd3 n) := Fin.castSucc (deI4 n)
def deI2 (n : ℕ) : Fin (dd2 n) := Fin.castAdd n (deI3 n)
def deI1 (n : ℕ) : Fin (dd1 n) := Fin.castSucc (deI2 n)
def deI0 (n : ℕ) : Fin (dd0 n) := Fin.castSucc (deI1 n)

def ddI4 (n : ℕ) : Fin (dd4 n) := Fin.last (n + 2)
def ddI3 (n : ℕ) : Fin (dd3 n) := Fin.castSucc (ddI4 n)

def dhI3 (n : ℕ) : Fin (dd3 n) := Fin.last (n + 3)
def dhI2 (n : ℕ) : Fin (dd2 n) := Fin.castAdd n (dhI3 n)
def dhI1 (n : ℕ) : Fin (dd1 n) := Fin.castSucc (dhI2 n)
def dhI0 (n : ℕ) : Fin (dd0 n) := Fin.castSucc (dhI1 n)

/-- The `j`-th coordinate of the `x'`-block in `ℝ^{dd2 n}`. -/
def dxI2 (n : ℕ) (j : Fin n) : Fin (dd2 n) := Fin.natAdd (dd3 n) j
def dxI1 (n : ℕ) (j : Fin n) : Fin (dd1 n) := Fin.castSucc (dxI2 n j)
def dxI0 (n : ℕ) (j : Fin n) : Fin (dd0 n) := Fin.castSucc (dxI1 n j)

def dyI1 (n : ℕ) : Fin (dd1 n) := Fin.last (dd2 n)
def dyI0 (n : ℕ) : Fin (dd0 n) := Fin.castSucc (dyI1 n)

def dvpI0 (n : ℕ) : Fin (dd0 n) := Fin.last (dd1 n)

/-! ## 4. The atoms -/

/-- `h ≠ 0`, at level `dd3`. -/
def dA3 (n : ℕ) : Set (Fin (dd3 n) → ℝ) := {z | z (dhI3 n) ≠ 0}

/-- `-δ < h ∧ h < δ` (equivalent to `|h| < δ`), at level `dd3`. -/
def dA4 (n : ℕ) : Set (Fin (dd3 n) → ℝ) :=
  {z | 0 < z (dhI3 n) + z (ddI3 n)} ∩ {z | 0 < z (ddI3 n) - z (dhI3 n)}

/-- The equations `x'_j = Fin.init v j + h * δ_{ij}`, at level `dd2`. -/
def dA5 (n : ℕ) (i : Fin n) : Set (Fin (dd2 n) → ℝ) :=
  ⋂ j : Fin n, {z | z (dxI2 n j) = z (dvI2 n (Fin.castSucc j)) + z (dhI2 n) *
    (if j = i then (1 : ℝ) else 0)}

/-- `0 < δ`, at level `dd4`. -/
def dA2 (n : ℕ) : Set (Fin (dd4 n) → ℝ) := {z | 0 < z (ddI4 n)}

/-- `0 < ε`, at level `dd5`. -/
def dA1 (n : ℕ) : Set (Fin (dd5 n) → ℝ) := {z | 0 < z (deI5 n)}

/-- `Fin.snoc x' v' ∈ G`, at level `dd0`. -/
def dGB (n : ℕ) (G : Set (Fin (n + 1) → ℝ)) : Set (Fin (dd0 n) → ℝ) :=
  {z | Fin.snoc (fun j : Fin n => z (dxI0 n j)) (z (dvpI0 n)) ∈ G}

/-- `Fin.snoc (Fin.init v) y₀ ∈ G`, at level `dd1`. -/
def dGA (n : ℕ) (G : Set (Fin (n + 1) → ℝ)) : Set (Fin (dd1 n) → ℝ) :=
  {z | Fin.snoc (fun j : Fin n => z (dvI1 n (Fin.castSucc j))) (z (dyI1 n)) ∈ G}

/-- The denominator-cleared difference-quotient atom `|vₙ - (v' - y₀)/h| < ε` at level `dd0`,
with the degenerate branch `h = 0` (where Lean's `x / 0 = 0` makes the target `|vₙ| < ε`). -/
def dA7 (n : ℕ) : Set (Fin (dd0 n) → ℝ) :=
  {z | 0 < z (deI0 n) ∧
    ((z (dhI0 n) ≠ 0 ∧ 0 < (z (deI0 n)) ^ 2 * (z (dhI0 n)) ^ 2 -
        (z (dvI0 n (Fin.last n)) * z (dhI0 n) - (z (dvpI0 n) - z (dyI0 n))) ^ 2) ∨
      (z (dhI0 n) = 0 ∧ (z (dvI0 n (Fin.last n))) ^ 2 < (z (deI0 n)) ^ 2))}

/-! ## 5. The atoms as polynomials -/

def P7a (n : ℕ) : MvPolynomial (Fin (dd0 n)) ℝ := MvPolynomial.X (deI0 n)

def P7b (n : ℕ) : MvPolynomial (Fin (dd0 n)) ℝ := MvPolynomial.X (dhI0 n)

def P7c (n : ℕ) : MvPolynomial (Fin (dd0 n)) ℝ :=
  MvPolynomial.X (deI0 n) ^ 2 * MvPolynomial.X (dhI0 n) ^ 2 -
    (MvPolynomial.X (dvI0 n (Fin.last n)) * MvPolynomial.X (dhI0 n) -
      (MvPolynomial.X (dvpI0 n) - MvPolynomial.X (dyI0 n))) ^ 2

def P7d (n : ℕ) : MvPolynomial (Fin (dd0 n)) ℝ :=
  MvPolynomial.X (deI0 n) ^ 2 - MvPolynomial.X (dvI0 n (Fin.last n)) ^ 2

def P4a (n : ℕ) : MvPolynomial (Fin (dd3 n)) ℝ :=
  MvPolynomial.X (dhI3 n) + MvPolynomial.X (ddI3 n)

def P4b (n : ℕ) : MvPolynomial (Fin (dd3 n)) ℝ :=
  MvPolynomial.X (ddI3 n) - MvPolynomial.X (dhI3 n)

def P5 (n : ℕ) (i : Fin n) (j : Fin n) : MvPolynomial (Fin (dd2 n)) ℝ :=
  MvPolynomial.X (dxI2 n j) - MvPolynomial.X (dvI2 n (Fin.castSucc j)) -
    MvPolynomial.X (dhI2 n) * MvPolynomial.C (if j = i then (1 : ℝ) else 0)


/-! ## 8. The two `G`-atoms as coordinate pullbacks -/

/-- The coordinate selection `(v, ε, δ, h, x', y₀, v') ↦ (x', v')` of the big space. -/
def ιGB (n : ℕ) : Fin (n + 1) → Fin (dd0 n) := Fin.lastCases (dvpI0 n) (dxI0 n)

/-- The coordinate selection `(v, ε, δ, h, x', y₀) ↦ (v₀, …, v_{n-1}, y₀)` of `ℝ^{dd1 n}`. -/
def ιGA (n : ℕ) : Fin (n + 1) → Fin (dd1 n) :=
  Fin.lastCases (dyI1 n) (fun j : Fin n => dvI1 n (Fin.castSucc j))

lemma eq_snoc_ιGB (n : ℕ) (x : Fin (dd0 n) → ℝ) :
    (fun j : Fin (n + 1) => x (ιGB n j)) =
      Fin.snoc (fun j : Fin n => x (dxI0 n j)) (x (dvpI0 n)) := by
  funext j
  refine Fin.lastCases ?_ ?_ j
  · simp [ιGB]
  · intro j'; simp [ιGB]

lemma eq_snoc_ιGA (n : ℕ) (x : Fin (dd1 n) → ℝ) :
    (fun j : Fin (n + 1) => x (ιGA n j)) =
      Fin.snoc (fun j : Fin n => x (dvI1 n (Fin.castSucc j))) (x (dyI1 n)) := by
  funext j
  refine Fin.lastCases ?_ ?_ j
  · simp [ιGA]
  · intro j'; simp [ιGA]


/-! ## 9. The chain of sets -/

def dD1 (n : ℕ) (G : Set (Fin (n + 1) → ℝ)) : Set (Fin (dd0 n) → ℝ) :=
  (dGB n G)ᶜ ∪ (dA7 n)

def dE1 (n : ℕ) (G : Set (Fin (n + 1) → ℝ)) : Set (Fin (dd1 n) → ℝ) :=
  (projLast (dD1 n G)ᶜ)ᶜ

def dD2 (n : ℕ) (G : Set (Fin (n + 1) → ℝ)) : Set (Fin (dd1 n) → ℝ) :=
  (dGA n G)ᶜ ∪ (dE1 n G)

def dE2 (n : ℕ) (G : Set (Fin (n + 1) → ℝ)) : Set (Fin (dd2 n) → ℝ) :=
  (projLast (dD2 n G)ᶜ)ᶜ

def dD3 (n : ℕ) (i : Fin n) (G : Set (Fin (n + 1) → ℝ)) : Set (Fin (dd2 n) → ℝ) :=
  (dA5 n i)ᶜ ∪ (dE2 n G)

def dE3 (n : ℕ) (i : Fin n) (G : Set (Fin (n + 1) → ℝ)) : Set (Fin (dd3 n) → ℝ) :=
  (Work.WilG0.projLastIter (dd3 n) n (dD3 n i G)ᶜ)ᶜ

def dD4 (n : ℕ) (i : Fin n) (G : Set (Fin (n + 1) → ℝ)) : Set (Fin (dd3 n) → ℝ) :=
  (dA3 n)ᶜ ∪ ((dA4 n)ᶜ ∪ (dE3 n i G))

def dE4 (n : ℕ) (i : Fin n) (G : Set (Fin (n + 1) → ℝ)) : Set (Fin (dd4 n) → ℝ) :=
  (projLast (dD4 n i G)ᶜ)ᶜ

def dE5 (n : ℕ) (i : Fin n) (G : Set (Fin (n + 1) → ℝ)) : Set (Fin (dd5 n) → ℝ) :=
  projLast ((dA2 n) ∩ (dE4 n i G))

def dE6 (n : ℕ) (i : Fin n) (G : Set (Fin (n + 1) → ℝ)) : Set (Fin (n + 1) → ℝ) :=
  (projLast (((dA1 n)ᶜ ∪ (dE5 n i G))ᶜ))ᶜ

/-! ## 10. Format and degree budgets of the chain -/

abbrev fGB (F n : ℕ) : ℕ := F + 2 * (dd0 n + (n + 1)) + 1
abbrev fGA (F n : ℕ) : ℕ := F + 2 * (dd1 n + (n + 1)) + 1
abbrev gGB (D : ℕ) : ℕ := D + 2
abbrev gGA (D : ℕ) : ℕ := D + 2

abbrev fD1 (F n : ℕ) : ℕ := (fGB F n + 1) + (dd0 n + 8)
abbrev fE1 (F n : ℕ) : ℕ := fD1 F n + 1 + 1 + 1
abbrev fD2 (F n : ℕ) : ℕ := (fGA F n + 1) + fE1 F n
abbrev fE2 (F n : ℕ) : ℕ := fD2 F n + 1 + 1 + 1
abbrev fD3 (F n : ℕ) : ℕ := ((dd2 n + 1) + 1) + fE2 F n
abbrev fE3 (F n : ℕ) : ℕ := fD3 F n + 1 + n + 1
abbrev fD4 (F n : ℕ) : ℕ := ((dd3 n + 1) + 1) + (((dd3 n + 4) + 1) + fE3 F n)
abbrev fE4 (F n : ℕ) : ℕ := fD4 F n + 1 + 1 + 1
abbrev fE5 (F n : ℕ) : ℕ := (((dd4 n + 2) + fE4 F n) + 1) + 1
abbrev fD6 (F n : ℕ) : ℕ := ((dd5 n + 2) + 1) + fE5 F n
abbrev fE6 (F n : ℕ) : ℕ := fD6 F n + 1 + 1 + 1

abbrev gD1 (D : ℕ) : ℕ := gGB D + 15
abbrev gE1 (D : ℕ) : ℕ := gD1 D
abbrev gD2 (D : ℕ) : ℕ := gGA D + gE1 D
abbrev gE2 (D : ℕ) : ℕ := gD2 D
abbrev gD3 (n D : ℕ) : ℕ := n + gE2 D
abbrev gE3 (n D : ℕ) : ℕ := gD3 n D
abbrev gD4 (n D : ℕ) : ℕ := 1 + (6 + gE3 n D)
abbrev gE4 (n D : ℕ) : ℕ := gD4 n D
abbrev gE5 (n D : ℕ) : ℕ := 3 + gE4 n D
abbrev gD6 (n D : ℕ) : ℕ := 3 + gE5 n D
abbrev gE6 (n D : ℕ) : ℕ := gD6 n D

end DiffSet

end Work.WilE9.Gen
