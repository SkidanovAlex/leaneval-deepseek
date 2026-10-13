/-
  WilG1/Choice — the abstract selection rule attached to a fibre.

  For a fibre predicate `P : ℝ → Prop` (the intended instance is `P = inFib K l`, i.e.
  `P t ↔ Fin.snoc l t ∈ K`), the four disjuncts of `selSet K R` describing the selected
  point, restricted to the fibre over a fixed `l ∈ R`, become the predicate `selRule P`.

  The mathematical content of `selSet_fibre` is then purely one-dimensional: if the fibre
  `{s | P s}` is a point or an open interval with `EReal` endpoints, the rule `selRule P`
  selects exactly one point `t` (and `P t` holds).
-/
import Mathlib
import Submission.Work.WilG1.ChoiceDefs

set_option autoImplicit false

noncomputable section

open Classical

namespace Work.WilG1.Choice

/-- The set of reals strictly between two extended reals. -/
def IooE (a b : EReal) : Set ℝ := {s : ℝ | a < (s : EReal) ∧ (s : EReal) < b}

@[simp] theorem mem_IooE {a b : EReal} {s : ℝ} :
    s ∈ IooE a b ↔ a < (s : EReal) ∧ (s : EReal) < b := Iff.rfl

theorem IooE_bot_top : IooE (⊥ : EReal) ⊤ = Set.univ := by
  ext s
  simp only [IooE, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact ⟨EReal.bot_lt_coe s, EReal.coe_lt_top s⟩

theorem IooE_bot_coe (β : ℝ) : IooE (⊥ : EReal) (β : EReal) = Set.Iio β := by
  ext s
  simp only [IooE, Set.mem_setOf_eq, Set.mem_Iio, EReal.bot_lt_coe, true_and,
    EReal.coe_lt_coe_iff]

theorem IooE_coe_top (α : ℝ) : IooE (α : EReal) ⊤ = Set.Ioi α := by
  ext s
  simp only [IooE, Set.mem_setOf_eq, Set.mem_Ioi, EReal.coe_lt_top, and_true,
    EReal.coe_lt_coe_iff]

theorem IooE_coe_coe (α β : ℝ) : IooE (α : EReal) (β : EReal) = Set.Ioo α β := by
  ext s
  simp only [IooE, Set.mem_setOf_eq, Set.mem_Ioo, EReal.coe_lt_coe_iff]

/-- The selection rule of `selSet`, transcribed to an abstract fibre predicate `P`;
`P` plays the role of `inFib K l`.  The four alternatives are, in order: the fibre is
all of `ℝ` (take `0`); the fibre has a unique centre of symmetry (take it); the fibre is
unbounded above but not at its infimum (take `inf + 1`); the fibre is unbounded below but
not at its supremum (take `sup - 1`). -/
def selRule (P : ℝ → Prop) (s : ℝ) : Prop :=
  ((∀ u : ℝ, P u) ∧ s = 0)
  ∨ ((∀ u : ℝ, P (s + u) ↔ P (s - u)) ∧
      ∃ c : ℝ, (∀ u : ℝ, P (c + u) ↔ P (c - u)) ∧
        ∀ c' : ℝ, (∀ u : ℝ, P (c' + u) ↔ P (c' - u)) → c' = c)
  ∨ (P s ∧ ¬ P (s - 1) ∧ (∀ u : ℝ, 0 < u → u < 1 → P (s - 1 + u)) ∧
      ∀ M : ℝ, ∃ u : ℝ, P u ∧ M < u)
  ∨ (P s ∧ ¬ P (s + 1) ∧ (∀ u : ℝ, 0 < u → u < 1 → P (s + 1 - u)) ∧
      ∀ M : ℝ, ∃ u : ℝ, P u ∧ u < M)

/-- `selSet` membership for a point of the fibre over `l`: the parameter condition is
`l ∈ R`, and the remaining four alternatives form `selRule (inFib K l)`. -/
theorem mem_selSet_snoc_iff {p : ℕ} (K : Set (Fin (p + 1) → ℝ)) (R : Set (Fin p → ℝ))
    (l : Fin p → ℝ) (s : ℝ) :
    (Fin.snoc l s ∈ Work.WilG1.selSet K R) ↔ l ∈ R ∧ selRule (Work.WilG1.inFib K l) s := by
  simp only [selRule, Work.WilG1.selSet, Work.WilG1.isAll, Work.WilG1.isCentre,
    Work.WilG1.unbAbove, Work.WilG1.unbBelow, Work.WilG1.inFib, Set.mem_setOf_eq,
    Fin.init_snoc, Fin.snoc_last]

end Work.WilG1.Choice
