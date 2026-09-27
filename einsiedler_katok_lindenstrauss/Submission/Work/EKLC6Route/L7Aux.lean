import Mathlib
import Submission.Work.EKLC6Route.Defs

/-!
# `Work.EKLC6Route.L7Aux` — auxiliary definitions for the entropy computation (`L7`)

This module collects the definitions and bookkeeping lemmas used by
`Work.EKLC6Route.tsum_negMulLog_ne_top` (L7 of `C6GEOM_ROUTE_LEAD.md`) and by the lemmas
delegated for it.

* `encw`/`decw` make explicit the `Encodable` instance hidden inside `Window.S` (which is
  `Encodable.decode₂ PIdx` w.r.t. `Encodable.ofCountable PIdx`), so that the enumeration of the
  window pieces can be manipulated without instance-mismatch problems;
* `jIdx` is the depth index `none ↦ 0`, `some j ↦ j + 1` used to control the sum over the
  depth label `J : Option ℕ`;
* `cellCount t i` is the number of grid cells at level `i` (`gridLev t i`); it satisfies
  `cellCount t i ≤ 7^9 * exp (9 * betaExp t * i)`.
-/

namespace Work.EKLC6Route

open MeasureTheory

noncomputable section

/-! ## 1. The encoding underlying `Window.S` -/

/-- The encoding of the index type `PIdx` underlying `Window.S`, made explicit. -/
noncomputable def encw : Window.PIdx → ℕ :=
  letI : Encodable Window.PIdx := Encodable.ofCountable _
  Encodable.encode

/-- The decoding of `Window.S`, made explicit. -/
noncomputable def decw : ℕ → Option Window.PIdx :=
  letI : Encodable Window.PIdx := Encodable.ofCountable _
  Encodable.decode₂ Window.PIdx

theorem decw_encw (p : Window.PIdx) : decw (encw p) = some p := by
  unfold decw encw
  exact @Encodable.decode₂_encode Window.PIdx (Encodable.ofCountable Window.PIdx) p

theorem decw_eq_some {n : ℕ} {p : Window.PIdx} : decw n = some p ↔ encw p = n := by
  unfold decw encw
  exact @Encodable.decode₂_eq_some Window.PIdx (Encodable.ofCountable Window.PIdx) n p

theorem encw_injective : Function.Injective encw := by
  intro a b h
  have h1 : decw (encw a) = decw (encw b) := by rw [h]
  rwa [decw_encw, decw_encw, Option.some.injEq] at h1

/-- `Window.S` is the `decw`-pullback of `piece`, with `∅` on the complement of the range. -/
theorem S_eq_match {μ : MeasureTheory.Measure Work.EKLContract.X3} {t : Fin 3 → ℝ}
    (w : Window μ t) (n : ℕ) :
    w.S n = (match decw n with | some p => w.piece p | none => ∅) := by
  rw [Window.S]
  unfold decw
  rfl

/-! ## 2. The depth index -/

/-- The depth index of a label `J : Option ℕ`. -/
def jIdx : Option ℕ → ℕ := fun J => J.elim 0 (· + 1)

@[simp] theorem jIdx_none : jIdx none = 0 := rfl
@[simp] theorem jIdx_some (j : ℕ) : jIdx (some j) = j + 1 := rfl

theorem jIdx_nonneg (J : Option ℕ) : 0 ≤ (jIdx J : ℝ) := Nat.cast_nonneg _

theorem jIdx_injective : Function.Injective jIdx := by
  intro a b h
  cases a <;> cases b <;> simp_all [jIdx]

theorem le_jIdx_add_one (J : Option ℕ) : 1 ≤ jIdx J + 1 := Nat.le_add_left 1 _

/-! ## 3. The number of grid cells at a level -/

/-- The number of grid cells at level `i`. -/
def cellCount (t : Fin 3 → ℝ) (i : ℕ) : ℕ := (2 ^ (gridLev t i + 1) + 3) ^ 9

theorem one_le_cellCount (t : Fin 3 → ℝ) (i : ℕ) : 1 ≤ cellCount t i := by
  refine one_le_pow₀ ?_
  have : (1 : ℕ) ≤ 2 ^ (gridLev t i + 1) := one_le_pow₀ (by norm_num)
  omega

end

end Work.EKLC6Route

namespace Work.EKLC6Route

open MeasureTheory
open scoped ENNReal

noncomputable section

/-! ## 4. Splitting an `ℝ≥0∞`-valued sum over `Option α` -/

/-- Splitting an `ℝ≥0∞`-valued sum over `Option α` into the `none`-term and the range of `some`.

Only the inequality `≤` is proved, which is all that is needed for upper bounds. -/
theorem tsum_option_le {α : Type*} (f : Option α → ℝ≥0∞) :
    (∑' x : Option α, f x) ≤ f none + ∑' a : α, f (some a) := by
  have hset : ({none} : Set (Option α)) ∪ Set.range some = Set.univ := by
    refine Set.eq_univ_iff_forall.mpr fun x => ?_
    cases x with
    | none => exact Or.inl rfl
    | some a => exact Or.inr ⟨a, rfl⟩
  have hU : (∑' x : ↑(({none} : Set (Option α)) ∪ Set.range some), f ↑x)
      = ∑' x : Option α, f x := by
    rw [hset, tsum_subtype]
    simp
  have h2 : (∑' x : ↑(({none} : Set (Option α)) ∪ Set.range some), f ↑x) ≤
      (∑' x : ↑({none} : Set (Option α)), f ↑x)
        + (∑' x : ↑(Set.range (some : α → Option α)), f ↑x) :=
    ENNReal.tsum_union_le f _ _
  have h3 : (∑' x : ↑({none} : Set (Option α)), f ↑x) = f none := by
    rw [tsum_subtype, tsum_eq_single none]
    · simp
    · intro b hb
      exact Set.indicator_of_notMem (by simpa [Set.mem_singleton_iff] using hb) f
  have h4 : (∑' x : ↑(Set.range (some : α → Option α)), f ↑x) = ∑' a : α, f (some a) := by
    refine (Equiv.tsum_eq (Equiv.ofInjective (some : α → Option α) (Option.some_injective α))
      (fun x : ↑(Set.range (some : α → Option α)) => f ↑x)).symm.trans ?_
    exact tsum_congr fun a => rfl
  calc (∑' x : Option α, f x)
      = ∑' x : ↑(({none} : Set (Option α)) ∪ Set.range some), f ↑x := hU.symm
    _ ≤ (∑' x : ↑({none} : Set (Option α)), f ↑x)
        + (∑' x : ↑(Set.range (some : α → Option α)), f ↑x) := h2
    _ = f none + ∑' a : α, f (some a) := by rw [h3, h4]

end

end Work.EKLC6Route
