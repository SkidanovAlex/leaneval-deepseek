import Mathlib
import Submission.Commons.Combinatorics.Transference.condExp_tower

namespace Commons.Combinatorics.Transference

set_option linter.unusedVariables false

open Finset
open scoped BigOperators

/-- For a partition `Q` (as a `Finset`-valued containing-block map) and a set `S` that is a
union of `Q`-blocks, the pairing of the `Q`-residual `f - 𝔼(f|Q)` with a `Q`-measurable
weight `h` vanishes: `∑_{x ∈ S} (f x - 𝔼(f|Q) x) * h x = 0`. -/
lemma residual_sum_eq_zero {X : Type*} [DecidableEq X]
    (Q : X → Finset X) (hQmem : ∀ x, x ∈ Q x) (hQeq : ∀ x y : X, y ∈ Q x → Q y = Q x)
    {S : Finset X} (hS : ∀ x ∈ S, Q x ⊆ S) (f h : X → ℝ)
    (hh : ∀ x y : X, y ∈ Q x → h y = h x) :
    ∑ x ∈ S, (f x - ((Q x).card : ℝ)⁻¹ * ∑ y ∈ Q x, f y) * h x = 0 := by
  have hinner : ∀ y : X,
      ∑ z ∈ Q y, (f z - ((Q z).card : ℝ)⁻¹ * ∑ w ∈ Q z, f w) * h z = 0 := by
    intro y
    have hz_eq : ∀ z ∈ Q y,
        (f z - ((Q z).card : ℝ)⁻¹ * ∑ w ∈ Q z, f w) * h z
          = (f z - ((Q y).card : ℝ)⁻¹ * ∑ w ∈ Q y, f w) * h y := by
      intro z hz
      rw [hQeq y z hz, hh y z hz]
    rw [Finset.sum_congr rfl hz_eq]
    have hcard : ((Q y).card : ℝ) ≠ 0 := by
      have : 0 < (Q y).card := Finset.card_pos.mpr ⟨y, hQmem y⟩
      exact_mod_cast this.ne'
    have hsum : ∑ z ∈ Q y, (f z - ((Q y).card : ℝ)⁻¹ * ∑ w ∈ Q y, f w) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      rw [← mul_assoc, mul_inv_cancel₀ hcard, one_mul, sub_self]
    rw [← Finset.sum_mul, hsum, zero_mul]
  rw [← sum_block_weighted Q hS (fun y _ => hQmem y) (fun y _ z hz => hQeq y z hz)
        (fun z => (f z - ((Q z).card : ℝ)⁻¹ * ∑ w ∈ Q z, f w) * h z)]
  apply Finset.sum_eq_zero
  intro y hy
  rw [hinner y, mul_zero]

/-- **Restriction reduction.**  For `Q` refining `P` and `Ω` a union of `Q`-atoms, the pairing of
the `Ω`-residual `f - 𝔼(f|P)` with a `Q`-measurable weight `h` only sees the refinement difference
`𝔼(f|Q) - 𝔼(f|P)`. -/
theorem cE_compl_restriction {X : Type*} [Fintype X] [DecidableEq X]
    (P Q : X → Finset X) (hPmem : ∀ x, x ∈ P x)
    (hPeq : ∀ x y : X, y ∈ P x → P y = P x) (hQmem : ∀ x, x ∈ Q x)
    (hQeq : ∀ x y : X, y ∈ Q x → Q y = Q x) (href : ∀ x, Q x ⊆ P x)
    {Ω : Finset X} (hΩ : ∀ x ∈ Ω, Q x ⊆ Ω) (f h : X → ℝ)
    (hh : ∀ x y : X, y ∈ Q x → h y = h x) :
    ∑ x ∈ Finset.univ \ Ω, (f x - ((P x).card : ℝ)⁻¹ * ∑ y ∈ P x, f y) * h x
      = ∑ x ∈ Finset.univ \ Ω,
          (((Q x).card : ℝ)⁻¹ * ∑ y ∈ Q x, f y - ((P x).card : ℝ)⁻¹ * ∑ y ∈ P x, f y) * h x := by
  have hS : ∀ x ∈ Finset.univ \ Ω, Q x ⊆ Finset.univ \ Ω := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    intro z hz
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ z, ?_⟩
    intro hzΩ
    have hQx_sub : Q x ⊆ Ω := by
      rw [← hQeq x z hz]
      exact hΩ z hzΩ
    exact hx.2 (hQx_sub (hQmem x))
  have h0 := residual_sum_eq_zero Q hQmem hQeq hS f h hh
  have key : ∑ x ∈ Finset.univ \ Ω, (f x - ((P x).card : ℝ)⁻¹ * ∑ y ∈ P x, f y) * h x
      = ∑ x ∈ Finset.univ \ Ω, (f x - ((Q x).card : ℝ)⁻¹ * ∑ y ∈ Q x, f y) * h x
        + ∑ x ∈ Finset.univ \ Ω,
            (((Q x).card : ℝ)⁻¹ * ∑ y ∈ Q x, f y - ((P x).card : ℝ)⁻¹ * ∑ y ∈ P x, f y) * h x := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [key, h0, zero_add]

end Commons.Combinatorics.Transference
