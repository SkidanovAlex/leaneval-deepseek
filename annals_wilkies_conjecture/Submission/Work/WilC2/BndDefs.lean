/-
  Boundary points (in the sense used by `Work.WilC2.boundary_finite`) of subsets of a linear
  ordered field: `x` is a boundary point of `D` when no open interval `(x-ε, x+ε)` with
  `ε > 0` lies in `D`, and none lies in `Dᶜ`.
-/
import Mathlib

set_option autoImplicit false

namespace Work.WilC2

variable {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]

/-- `x` is a **boundary point** of `D`: no open interval `(x - ε, x + ε)`, `ε > 0`, is contained
in `D`, and no such interval is contained in `Dᶜ`.  Equivalently, every open interval around `x`
meets both `D` and `Dᶜ`. -/
def IsBnd (D : Set M) (x : M) : Prop :=
  (¬ ∃ ε : M, 0 < ε ∧ Set.Ioo (x - ε) (x + ε) ⊆ D) ∧
    (¬ ∃ ε : M, 0 < ε ∧ Set.Ioo (x - ε) (x + ε) ⊆ Dᶜ)

/-- `IsBnd` is by definition the displayed conjunction. -/
lemma isBnd_iff {D : Set M} {x : M} :
    IsBnd D x ↔ (¬ ∃ ε : M, 0 < ε ∧ Set.Ioo (x - ε) (x + ε) ⊆ D) ∧
      (¬ ∃ ε : M, 0 < ε ∧ Set.Ioo (x - ε) (x + ε) ⊆ Dᶜ) :=
  Iff.rfl

/-- Every positive `ε` gives an interval `(x - ε, x + ε)` containing `x`, hence nonempty. -/
lemma mem_Ioo_self {x ε : M} (hε : 0 < ε) : x ∈ Set.Ioo (x - ε) (x + ε) :=
  ⟨by linarith, by linarith⟩

/-- Decreasing the radius shrinks the interval: if `ε ≤ δ` then `(x-ε, x+ε) ⊆ (x-δ, x+δ)`. -/
lemma Ioo_subset_Ioo {x ε δ : M} (h : ε ≤ δ) :
    Set.Ioo (x - ε) (x + ε) ⊆ Set.Ioo (x - δ) (x + δ) := by
  intro y hy
  simp only [Set.mem_Ioo] at hy ⊢
  exact ⟨by linarith [hy.1], by linarith [hy.2]⟩

end Work.WilC2
