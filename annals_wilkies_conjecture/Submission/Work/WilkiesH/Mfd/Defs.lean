import Mathlib
import Submission.Work.WilkiesH.Basic

/-!
# Area H (counting) — regular pieces (local manifold charts)

The geometric input of the counting induction (BNZ §6) is the BNZ §2.3
"Stratification" metatheorem: a definable set decomposes into finitely many connected
*regular* (manifold) strata, plus a lower-dimensional remainder.  This file fixes the local
vocabulary in which "regular" is expressed, together with the two facts about it that the
assembly needs:

* `boxAround x δ` — the open box `{y | ∀ i, |y i - x i| < δ}` (sup norm);
* `IsGraphAt μ C x` — `C` agrees, in a box around `x`, with the graph of a continuous
  section `ψ` of a rank-`μ` coordinate projection, over an *open* `Ω ⊆ ℝ^μ`, with `x`
  itself on the graph.  (The domain being *open* is what makes this a manifold condition.)
* `IsManifold μ C` — `IsGraphAt μ C x` at every `x ∈ C`;
* `LocallyIn C X x` — `C` is locally contained in `X` at `x` (local fullness);
* `IsLimitPt C x` — `x` is a limit point of `C`.

`Work.WilkiesH.Mfd.MemAlg` proves: a point of a semialgebraic set `S` which is a `μ`-regular
point of `S` (in the `IsGraphAt` sense) and at which `S` is locally contained in `X` lies in
`X.alg`.  This is the "generic point" half of the basic-block argument; the complementary
"boundary" half is the stratification input of `Work.WilkiesH.Strat.Defs`.
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkiesH

open WilkiesDesign WilkiesConjecture

/-- The open box of radius `δ` around `x` in `ℝⁿ` (in the sup norm). -/
def boxAround {n : ℕ} (x : Fin n → ℝ) (δ : ℝ) : Set (Fin n → ℝ) :=
  {y | ∀ i, |y i - x i| < δ}

@[simp] theorem mem_boxAround {n : ℕ} {x y : Fin n → ℝ} {δ : ℝ} :
    y ∈ boxAround x δ ↔ ∀ i, |y i - x i| < δ := Iff.rfl

/-- The open "coordinate box" of radius `ρ` around `t` in `ℝ^μ`. -/
def cboxAround {μ : ℕ} (t : Fin μ → ℝ) (ρ : ℝ) : Set (Fin μ → ℝ) :=
  {v | ∀ i, |v i - t i| < ρ}

@[simp] theorem mem_cboxAround {μ : ℕ} {t v : Fin μ → ℝ} {ρ : ℝ} :
    v ∈ cboxAround t ρ ↔ ∀ i, |v i - t i| < ρ := Iff.rfl

/-- `IsGraphAt μ C x`: `C` coincides, inside a box around `x`, with the graph of a continuous
section `ψ` of a rank-`μ` coordinate projection, over an open `Ω ⊆ ℝ^μ`, and `x` lies on that
graph. -/
def IsGraphAt {n : ℕ} (μ : ℕ) (C : Set (Fin n → ℝ)) (x : Fin n → ℝ) : Prop :=
  ∃ (e : Fin μ ↪ Fin n) (Ω : Set (Fin μ → ℝ)) (ψ : (Fin μ → ℝ) → (Fin n → ℝ)) (δ : ℝ),
    0 < δ ∧ IsOpen Ω ∧ ContinuousOn ψ Ω ∧ (∀ t ∈ Ω, ψ t ∘ e = t) ∧
      (∃ t ∈ Ω, ψ t = x) ∧
      (∀ y, y ∈ boxAround x δ → (y ∈ C ↔ ∃ t ∈ Ω, ψ t = y))

/-- `C` is a `μ`-dimensional topological submanifold of `ℝⁿ`. -/
def IsManifold {n : ℕ} (μ : ℕ) (C : Set (Fin n → ℝ)) : Prop := ∀ x ∈ C, IsGraphAt μ C x

/-- `C` is *locally contained in* `X` at `x`. -/
def LocallyIn {n : ℕ} (C X : Set (Fin n → ℝ)) (x : Fin n → ℝ) : Prop :=
  ∃ δ > (0 : ℝ), ∀ y, y ∈ boxAround x δ → y ∈ C → y ∈ X

/-- `x` is a limit point of `C`. -/
def IsLimitPt {n : ℕ} (C : Set (Fin n → ℝ)) (x : Fin n → ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ y ∈ C, y ≠ x ∧ (∀ i, |y i - x i| < ε)

end Work.WilkiesH
