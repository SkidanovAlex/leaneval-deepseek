/-
# The duality `σ + τ ≥ 1 - ε` from its `sSup` form

This file assembles the `ε`-existential form of `sup_const_mul_add_sup_const_ann` from the
`sSup`-form `supConstMain`.
-/
import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension
import Submission.Work.ORHughesFree.NaturalExtension.Defs
import Submission.Work.ORHughesFree.NaturalExtension.supConstDefs
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.RankAPI.rk_le_left
import Submission.Work.ORHughesFree.RankAPI.rk_le_right
import Submission.Work.ORHughesFree.RankAPI.rk_add_le

set_option autoImplicit false

universe u

namespace Work.ORHughesFree.NaturalExtension

open Matrix Work.ORHughesFree

theorem assembly_of_sup {R : Type u} [Ring R] [VonNeumannRegularRing R]
    [MulSemiringAction (Multiplicative ℤ) R] (rk : SylvesterRank R) (p : SkewL R)
    (hmain : sSup {y : ℝ | ∃ c ∈ C0set R p, y = rk.rk 1 1 (oneByOne c)}
      + sSup {y : ℝ | ∃ c ∈ C1set R p, y = rk.rk 1 1 (oneByOne c)} ≥ 1) :
    ∀ ε : ℝ, 0 < ε → ∃ (c₀ c₁ : R),
      (∃ q q' : SkewL R, q = q' * p ∧ (∀ k : ℤ, k < 0 → coeffElt q k = 0) ∧ coeffElt q 0 = c₀) ∧
      (∃ q'' : SkewL R, q'' * p = 0 ∧ (∀ k : ℤ, k < 0 → coeffElt q'' k = 0) ∧
        coeffElt q'' 0 = c₁) ∧
      rk.rk 1 1 (oneByOne c₀) + rk.rk 1 1 (oneByOne c₁) ≥ 1 - ε := by
  intro ε hε
  set S0 : Set ℝ := {y : ℝ | ∃ c ∈ C0set R p, y = rk.rk 1 1 (oneByOne c)} with hS0
  set S1 : Set ℝ := {y : ℝ | ∃ c ∈ C1set R p, y = rk.rk 1 1 (oneByOne c)} with hS1
  have hcoeff0 : ∀ k : ℤ, coeffElt (0 : SkewL R) k = 0 := by
    intro k; simp [coeffElt]
  have hmem0 : (0 : R) ∈ C0set R p :=
    ⟨0, 0, by rw [zero_mul], fun k _ => hcoeff0 k, rfl⟩
  have hmem1 : (0 : R) ∈ C1set R p :=
    ⟨0, by rw [zero_mul], fun k _ => hcoeff0 k, rfl⟩
  have hne0 : S0.Nonempty := ⟨rk.rk 1 1 (oneByOne 0), 0, hmem0, rfl⟩
  have hne1 : S1.Nonempty := ⟨rk.rk 1 1 (oneByOne 0), 0, hmem1, rfl⟩
  have hle : ∀ c : R, rk.rk 1 1 (oneByOne c) ≤ 1 := by
    intro c
    have h := rk.rk_mul_le_right (oneByOne c) (1 : Matrix (Fin 1) (Fin 1) R)
    simpa [Matrix.mul_one, rk.rk_one] using h
  have hb0 : BddAbove S0 := ⟨1, by rintro y ⟨c, _, rfl⟩; exact hle c⟩
  have hb1 : BddAbove S1 := ⟨1, by rintro y ⟨c, _, rfl⟩; exact hle c⟩
  have key0 : ∃ b ∈ S0, sSup S0 - ε / 2 < b := by
    by_contra h
    push_neg at h
    exact absurd (csSup_le hne0 h) (not_le.mpr (by linarith))
  have key1 : ∃ b ∈ S1, sSup S1 - ε / 2 < b := by
    by_contra h
    push_neg at h
    exact absurd (csSup_le hne1 h) (not_le.mpr (by linarith))
  obtain ⟨b0, hb0mem, hb0lt⟩ := key0
  obtain ⟨b1, hb1mem, hb1lt⟩ := key1
  obtain ⟨c₀, hc₀, hb0eq⟩ := hb0mem
  obtain ⟨c₁, hc₁, hb1eq⟩ := hb1mem
  refine ⟨c₀, c₁, hc₀, hc₁, ?_⟩
  rw [hb0eq] at hb0lt
  rw [hb1eq] at hb1lt
  linarith

end Work.ORHughesFree.NaturalExtension
