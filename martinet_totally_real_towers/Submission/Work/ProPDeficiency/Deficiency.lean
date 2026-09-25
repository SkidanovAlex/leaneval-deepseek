import Mathlib
import Submission.Work.ProPDeficiency.Basic

/-!
# The numeric side of the deficiency formalism

**Namespace** `Work.ProPDeficiency`; module `Submission.Work.ProPDeficiency.Deficiency`.

The arithmetic supplies a presentation with `d` generators and `r` relators; the group theory needs
the numerical inequality `4 * r ≤ d ^ 2` to apply Golod--Shafarevich.  In the number-theoretic
applications either `r = d` (tame route over `ℚ`: the `F_2` Euler characteristic is `1`) or
`r ≤ d + 1` (deficiency at least `-1`), together with a lower bound `d ≥ 5` coming from a
multiquadratic subextension.  This module collects those purely numerical lemmas.

## Main results

* `four_mul_add_one_le_sq_iff` : `4 * (d + 1) ≤ d * d ↔ 5 ≤ d`;
* `four_mul_self_le_sq_iff` : `4 * d ≤ d * d ↔ d = 0 ∨ 4 ≤ d`;
* `four_mul_le_sq_of_le`, `four_mul_le_sq_of_le_add_one` : the two shapes above;
* `four_mul_le_sq_mono` and friends : monotonicity in `r` and in `d`;
* `HasDeficiency.of_isPresentation`, `HasDeficiency.of_isPresentation_neg_one` : from a presentation
  to a deficiency statement;
* `HasPresentation.four_mul_le_sq` : the criterion's numerical hypothesis from a presentation.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ProPDeficiency

/-! ## Pure `ℕ` arithmetic -/

theorem four_mul_add_one_le_sq_iff (d : ℕ) : 4 * (d + 1) ≤ d * d ↔ 5 ≤ d := by
  constructor
  · intro h
    by_contra hd
    have hd' : d ≤ 4 := by omega
    interval_cases d <;> omega
  · intro hd
    have h5 : (5 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    have : (4 * (d + 1) : ℤ) ≤ (d : ℤ) * d := by nlinarith [sq_nonneg ((d : ℤ) - 2)]
    exact_mod_cast this

theorem four_mul_self_le_sq_iff (d : ℕ) : 4 * d ≤ d * d ↔ d = 0 ∨ 4 ≤ d := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · exact Or.inl h0
    · right
      by_contra hd
      have hd' : d ≤ 3 := by omega
      interval_cases d <;> omega
  · rintro (rfl | hd)
    · simp
    · have : (4 : ℤ) * d ≤ (d : ℤ) * d := by
        have h4 : (4 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
        nlinarith [show (0 : ℤ) ≤ (d : ℤ) by positivity]
      exact_mod_cast this

theorem four_mul_le_sq_of_le {r d : ℕ} (h : r ≤ d) (hd : 4 ≤ d) : 4 * r ≤ d * d := by
  have h1 : 4 * r ≤ 4 * d := by omega
  have h2 : 4 * d ≤ d * d := (four_mul_self_le_sq_iff d).mpr (Or.inr hd)
  omega

theorem four_mul_le_sq_of_le_add_one {r d : ℕ} (h : r ≤ d + 1) (hd : 5 ≤ d) :
    4 * r ≤ d * d := by
  have h1 : 4 * r ≤ 4 * (d + 1) := by omega
  have h2 : 4 * (d + 1) ≤ d * d := (four_mul_add_one_le_sq_iff d).mpr hd
  omega

theorem four_mul_le_sq_mono {r r' d d' : ℕ} (hr : r' ≤ r) (hd : d ≤ d')
    (h : 4 * r ≤ d * d) : 4 * r' ≤ d' * d' := by
  have h1 : 4 * r' ≤ 4 * r := by omega
  have h2 : d * d ≤ d' * d' := Nat.mul_le_mul hd hd
  omega

theorem four_mul_le_sq_mono_left {r r' d : ℕ} (hr : r' ≤ r) (h : 4 * r ≤ d * d) :
    4 * r' ≤ d * d := by
  have : 4 * r' ≤ 4 * r := by omega
  omega

theorem four_mul_le_sq_of_le_of_le {r r' d : ℕ} (h : r' ≤ r) (h2 : 4 * r ≤ d * d) :
    4 * r' ≤ d * d := four_mul_le_sq_mono_left h h2

/-! ## From presentations and deficiency to the numerical inequality -/

theorem HasDeficiency.of_isPresentation {G : Type*} [Group G] {α : Type} [Fintype α]
    {rel : Finset (FreeGroup α)} (h : IsPresentation α rel G)
    (hle : rel.card ≤ Fintype.card α) : HasDeficiency G 0 :=
  ⟨Fintype.card α, rel.card,
    ⟨α, inferInstance, rel, rfl, rfl, h⟩,
    Deficiency.of_le hle⟩

theorem HasDeficiency.of_isPresentation_neg_one {G : Type*} [Group G] {α : Type} [Fintype α]
    {rel : Finset (FreeGroup α)} (h : IsPresentation α rel G)
    (hle : rel.card ≤ Fintype.card α + 1) : HasDeficiency G (-1) :=
  ⟨Fintype.card α, rel.card,
    ⟨α, inferInstance, rel, rfl, rfl, h⟩,
    Deficiency.of_le_add_one hle⟩

/-- **The numerical hypothesis of the Golod--Shafarevich criterion**, in the shape the arithmetic
side supplies it: a presentation with deficiency at least `-1` (`r ≤ d + 1`) and `d ≥ 5`. -/
theorem HasPresentation.four_mul_le_sq {G : Type*} [Group G] {d r : ℕ}
    (h : HasPresentation G d r) (hdef : Deficiency d r (-1)) (hd : 5 ≤ d) :
    4 * r ≤ d * d :=
  four_mul_le_sq_of_deficiency hdef hd

/-- The free group on a *finite* type `α` has a presentation with `#α` generators and **no**
relators, so its deficiency is at least `#α`; in particular the deficiency formalism is not
vacuous. -/
theorem hasPresentation_freeGroup (α : Type) [Fintype α] :
    HasPresentation (FreeGroup α) (Fintype.card α) 0 := by
  have h : Subgroup.normalClosure ((∅ : Finset (FreeGroup α)) : Set (FreeGroup α)) = ⊥ := by
    rw [Finset.coe_empty, Subgroup.normalClosure_empty]
  refine ⟨α, inferInstance, ∅, rfl, rfl, ?_⟩
  exact ⟨((QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot).symm⟩

/-- Consequently a free group has deficiency at least its rank. -/
theorem hasDeficiency_freeGroup (α : Type) [Fintype α] :
    HasDeficiency (FreeGroup α) (Fintype.card α : ℤ) :=
  ⟨Fintype.card α, 0, hasPresentation_freeGroup α, by
    simp only [Deficiency]; push_cast; linarith⟩

end Work.ProPDeficiency
