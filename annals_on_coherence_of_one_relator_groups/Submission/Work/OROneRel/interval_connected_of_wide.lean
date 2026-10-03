import Mathlib
import Submission.Work.OROneRel.interval_connected

/-!
# Connectivity of a `{±A, ±B}`-interval of width at least `A + B`

`Work.OROneRel.interval_connected` establishes connectivity of the `{±A, ±B}`-graph on an
integer interval `[a, b]` of width `b - a ≥ A + B - 2`, for `A, B ≥ 2` coprime, where the
symmetric step relation `S a b A B` requires *both* endpoints to lie in `[a, b]`.

Here we deduce the form needed downstream, `interval_connected_of_wide`: on the interval
`[lo + 1, hi - 1]` of width `hi - lo - 2 ≥ A + B - 2` (i.e. `A + B ≤ hi - lo`), the graph is
connected, and only `1 ≤ A`, `1 ≤ B` are assumed.

The proof is a reduction:

* if `A = 1` or `B = 1`, the graph contains the unit step `t ↦ t + 1`, so chaining unit steps
  connects every two points of the interval (`rtg_of_succ`);
* otherwise `2 ≤ A` and `2 ≤ B`, and we specialise `interval_connected` to `a = lo + 1`,
  `b = hi - 1`.  That theorem yields reachability in the *one-sided* relation `IRel`, which is
  converted back to the two-sided relation `S` by `IRel_rtg_to_S`, using that a path started
  inside the interval only ever visits the interval.

The relation `S (lo + 1) (hi - 1) A B` is definitionally the relation appearing in the target
statement.
-/

namespace Work.OROneRel

set_option autoImplicit false

/-- Reachability in the one-sided relation `IRel lo hi A B`, started at a point of `[lo, hi]`,
only ever visits points of `[lo, hi]`; hence it coincides with reachability in `S lo hi A B`. -/
lemma IRel_rtg_to_S {lo hi A B x y : ℤ} (hx₀ : lo ≤ x) (hx₁ : x ≤ hi)
    (h : Relation.ReflTransGen (IRel lo hi A B) x y) :
    Relation.ReflTransGen (S lo hi A B) x y := by
  suffices ∀ y : ℤ, Relation.ReflTransGen (IRel lo hi A B) x y →
      Relation.ReflTransGen (S lo hi A B) x y ∧ lo ≤ y ∧ y ≤ hi from (this y h).1
  intro y hy
  induction hy with
  | refl => exact ⟨Relation.ReflTransGen.refl, hx₀, hx₁⟩
  | tail hab hbc ih =>
      obtain ⟨ihS, hblo, hbhi⟩ := ih
      obtain ⟨hclo, hchi, hstep⟩ := hbc
      exact ⟨ihS.tail ⟨hblo, hbhi, hclo, hchi, hstep⟩, hclo, hchi⟩

/-- Chaining unit steps: if `t ↦ t + 1` is an allowed `S`-step for every `lo + 1 ≤ t ≤ hi - 2`,
then any `x ≤ y` inside `[lo + 1, hi - 1]` are connected. -/
lemma rtg_of_succ {lo hi A B : ℤ}
    (hstep : ∀ t : ℤ, lo + 1 ≤ t → t ≤ hi - 2 → S (lo + 1) (hi - 1) A B t (t + 1))
    {x y : ℤ} (hx₀ : lo + 1 ≤ x) (_hx₁ : x ≤ hi - 1) (_hy₀ : lo + 1 ≤ y) (hy₁ : y ≤ hi - 1)
    (hxy : x ≤ y) :
    Relation.ReflTransGen (S (lo + 1) (hi - 1) A B) x y := by
  have key : ∀ n : ℤ, x ≤ n → n ≤ hi - 1 →
      Relation.ReflTransGen (S (lo + 1) (hi - 1) A B) x n := by
    intro n hxn hnhi
    revert hnhi
    refine Int.leInduction (motive := fun n _ =>
      n ≤ hi - 1 → Relation.ReflTransGen (S (lo + 1) (hi - 1) A B) x n) ?_ ?_ n hxn
    · intro _; exact Relation.ReflTransGen.refl
    · intro n _ ih hn₁
      have hst : S (lo + 1) (hi - 1) A B n (n + 1) := hstep n (by omega) (by omega)
      exact (ih (by omega)).tail hst
  exact key y hxy hy₁

/-- Case `A = 1` or `B = 1`: the graph contains the unit step. -/
lemma connected_of_one {A B lo hi : ℤ} (hone : A = 1 ∨ B = 1) :
    ∀ x y : ℤ, lo + 1 ≤ x → x ≤ hi - 1 → lo + 1 ≤ y → y ≤ hi - 1 →
      Relation.ReflTransGen (S (lo + 1) (hi - 1) A B) x y := by
  have hstep : ∀ t : ℤ, lo + 1 ≤ t → t ≤ hi - 2 → S (lo + 1) (hi - 1) A B t (t + 1) := by
    intro t ht₀ ht₁
    refine ⟨by omega, by omega, by omega, by omega, ?_⟩
    rcases hone with h | h
    · left; omega
    · right; right; left; omega
  intro x y hx₀ hx₁ hy₀ hy₁
  rcases le_total x y with hxy | hyx
  · exact rtg_of_succ hstep hx₀ hx₁ hy₀ hy₁ hxy
  · exact rtg_symm (rtg_of_succ hstep hy₀ hy₁ hx₀ hx₁ hyx)

/-- Case `A, B ≥ 2`: specialise `interval_connected` to `[lo + 1, hi - 1]`. -/
lemma connected_of_ge_two {A B lo hi : ℤ} (hA : 2 ≤ A) (hB : 2 ≤ B)
    (hbez : ∃ p q : ℤ, p * A + q * B = 1) (hwide : A + B ≤ hi - lo) :
    ∀ x y : ℤ, lo + 1 ≤ x → x ≤ hi - 1 → lo + 1 ≤ y → y ≤ hi - 1 →
      Relation.ReflTransGen (S (lo + 1) (hi - 1) A B) x y := by
  intro x y hx₀ hx₁ hy₀ hy₁
  have hband : A + B - 2 ≤ (hi - 1) - (lo + 1) := by linarith
  have h := interval_connected hA hB hbez (lo + 1) (hi - 1) hband x y hx₀ hx₁ hy₀ hy₁
  exact IRel_rtg_to_S hx₀ hx₁ h

theorem interval_connected_of_wide {A B : ℤ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hbez : ∃ p q : ℤ, p * A + q * B = 1) (lo hi : ℤ) (hwide : A + B ≤ hi - lo) :
    ∀ x y : ℤ, lo + 1 ≤ x → x ≤ hi - 1 → lo + 1 ≤ y → y ≤ hi - 1 →
      Relation.ReflTransGen
        (fun x y : ℤ => lo + 1 ≤ x ∧ x ≤ hi - 1 ∧ lo + 1 ≤ y ∧ y ≤ hi - 1 ∧
          (y = x + A ∨ y = x - A ∨ y = x + B ∨ y = x - B)) x y := by
  by_cases hA1 : A = 1
  · exact connected_of_one (Or.inl hA1)
  by_cases hB1 : B = 1
  · exact connected_of_one (Or.inr hB1)
  exact connected_of_ge_two (by omega) (by omega) hbez hwide

end Work.OROneRel
