import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.s02_lemma22CaseOne
import Submission.Work.BG.s02_classSumSquare
import Submission.Work.BG.CharBridge
import Submission.Work.BG.s02_indDiff

/-!
# Area BG: Bender–Glauberman 1981, Lemma 2.2, consequence `Lemma22SqProp`

This file proves `Work.BG.Lemma22SqProp C` (L2.2-d of `NOTES_BG_s02_leaves.md`): if
`μ, ν ∈ Irr(H₀)` lie in the same `Λ`-orbit with `μ^s ≠ μ`, `ν^s ≠ ν`, and
`(μ - ν)^G = α - β` with `α, β ∈ ±Irr(G)`, then

`α(t)² = β(t)²`.

## The mathematics (Bender–Glauberman 1981, p. 206, "by Lemma 2.2")

Write `X := t^G` (the `G`-class of `t`, a union of conjugacy classes).  Lemma 2.2 case one
(`Work.BG.s02_lemma22CaseOne`) gives

`Σ_{x,y ∈ X} (μ - ν)^G(xy) = 0`,

and since `(μ - ν)^G = α - β` pointwise this says

`Σ_{x,y ∈ X} α(xy) = Σ_{x,y ∈ X} β(xy)`.  (*)

The pure class-sum-square identity of Lemma 2.2-a (`Work.BG.s02_classSumSquare`) applied to
the conjugation-invariant set `X` and to `α`, `β ∈ ±Irr(G)` gives

`α(1) · Σ_{x,y ∈ X} α(xy) = (Σ_{x ∈ X} α(x))²`, `β(1) · Σ_{x,y ∈ X} β(xy) = (Σ_{x ∈ X} β(x))²`;

and since `X` is the full class of `t`, each `Σ_{x ∈ X} θ(x) = |X| · θ(t)`.  Finally
`α(1) = β(1)`, because `(α - β)(1) = (μ - ν)^G(1) = 0` (I-1, `Work.BG.s02_indDiff`): an
induction from `H₀` of a difference of two characters of equal degree (`ν = λ_β μ`,
`λ_β(1) = 1`) has degree `0`.  Substituting (*) therefore gives
`|X|² α(t)² = |X|² β(t)²`, and `|X| ≠ 0` (the class of `t` contains `t`), so `α(t)² = β(t)²`.

## Layout

* `s02_l22d_mem_tClass`, `s02_l22d_sum_tClass`, `s02_l22d_card_cast_ne_zero` — elementary
  facts about the class `t^G`;
* `s02_lemma22Sq` — the theorem.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

variable {G : Type} [Group G] [Finite G] [Fintype G]

/-- Membership in the class of `t`. -/
theorem s02_l22d_mem_tClass (C : Sec2Ctx G) {x : G} : x ∈ tClass C ↔ IsConj x (C.t : G) := by
  simp only [tClass, Finset.mem_filter, Finset.mem_univ, true_and]

/-- For a class function `φ`, the sum over the class of `t` is the class size times the
value at `t`. -/
theorem s02_l22d_sum_tClass (C : Sec2Ctx G) (φ : ClassFunction G ℂ) :
    (∑ x ∈ tClass C, φ x) = ((tClass C).card : ℂ) * φ (C.t : G) := by
  have h : (∑ x ∈ tClass C, φ x) = ∑ x ∈ tClass C, φ (C.t : G) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    exact φ.of_isConj ((s02_l22d_mem_tClass C).mp hx)
  rw [h, Finset.sum_const, nsmul_eq_mul]

/-- The class of `t` is nonempty (it contains `t`), so its size is a nonzero complex
number. -/
theorem s02_l22d_card_cast_ne_zero (C : Sec2Ctx G) : ((tClass C).card : ℂ) ≠ 0 := by
  have ht : (C.t : G) ∈ tClass C := (s02_l22d_mem_tClass C).mpr (IsConj.refl _)
  have hpos : 0 < (tClass C).card := Finset.card_pos.mpr ⟨_, ht⟩
  exact Nat.cast_ne_zero.mpr hpos.ne'

/-- **Bender–Glauberman 1981, Lemma 2.2, consequence `Lemma22SqProp`** (p. 206): if
`μ, ν ∈ Irr(H₀)` are `Λ`-equivalent with `μ^s ≠ μ`, `ν^s ≠ ν` and `(μ - ν)^G = α - β`
with `α, β ∈ ±Irr(G)`, then `α(t)² = β(t)²`. -/
theorem s02_lemma22Sq {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.BG.Lemma22SqProp C := by
  intro μ ν hμ hν hlam hμs hνs α β hα hβ hAB
  -- Lemma 2.2, case one: `Σ_{x,y ∈ t^G} (μ - ν)^G(xy) = 0`.
  have hcase := s02_lemma22CaseOne C μ ν hμ hν hlam hμs hνs
  -- `(μ - ν)^G = α - β` pointwise.
  have hpw : ∀ x y : G, ind C (μ - ν) (x * y) = α (x * y) - β (x * y) := by
    intro x y
    have h := congrArg (fun φ : ClassFunction G ℂ => φ (x * y)) hAB
    simpa only [ClassFunction.sub_apply] using h
  -- Hence the double sums of `α` and of `β` over `t^G` coincide.
  have hsumsplit : (∑ x ∈ tClass C, ∑ y ∈ tClass C, ind C (μ - ν) (x * y))
      = (∑ x ∈ tClass C, ∑ y ∈ tClass C, α (x * y))
        - (∑ x ∈ tClass C, ∑ y ∈ tClass C, β (x * y)) := by
    rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => hpw x y))]
    simp only [Finset.sum_sub_distrib]
  have hSAB : (∑ x ∈ tClass C, ∑ y ∈ tClass C, α (x * y))
      = (∑ x ∈ tClass C, ∑ y ∈ tClass C, β (x * y)) := by
    rw [hsumsplit] at hcase
    exact sub_eq_zero.mp hcase
  -- The class-sum-square identity of Lemma 2.2-a for `α` and for `β`.
  have hcsA := s02_classSumSquare (tClass C) (l22c1_tClass_conj C) α hα
  have hcsB := s02_classSumSquare (tClass C) (l22c1_tClass_conj C) β hβ
  rw [s02_l22d_sum_tClass C α] at hcsA
  rw [s02_l22d_sum_tClass C β] at hcsB
  -- `α(1) = β(1)`, because `(α - β)(1) = (μ - ν)^G(1) = 0`.
  have hα1 : α 1 = β 1 := by
    have hd := (s02_indDiff C μ ν hμ hν hlam).2
    have h := congrArg (fun φ : ClassFunction G ℂ => φ (1 : G)) hAB
    rw [ClassFunction.sub_apply] at h
    rw [hd] at h
    exact sub_eq_zero.mp h.symm
  -- Combine: `(|t^G| · α(t))² = (|t^G| · β(t))²`.
  have heq : (((tClass C).card : ℂ) * α (C.t : G)) ^ 2
      = (((tClass C).card : ℂ) * β (C.t : G)) ^ 2 := by
    rw [← hcsA, ← hcsB, hα1, hSAB]
  -- Cancel the nonzero factor `|t^G|²`.
  rw [mul_pow, mul_pow] at heq
  exact mul_left_cancel₀ (pow_ne_zero 2 (s02_l22d_card_cast_ne_zero C)) heq

end Work.BG
