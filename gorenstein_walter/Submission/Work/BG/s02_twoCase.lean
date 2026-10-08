import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.CharBridge
import Submission.Work.BG.sumSqFourSplit
import Submission.Work.BG.normFourSplit

/-!
# `Work.BG.s02_twoCase` — the "easy" case `n = 2` of the p. 206 construction (P-2)

Bender–Glauberman, J. Algebra 70 (1981), p. 206, needs the following elementary fact about
virtual characters (recorded in the area's design notes as **P-2**):

> A virtual character `D ∈ ℤ[Irr K]` of degree `D(1) = 0` and squared norm `‖D‖² = 2a`
> with `a ∈ {1, 2}` splits as `D = g₁ - g₂` with `g₁, g₂ ∈ ℤ[Irr K]` of squared norms
> `‖g₁‖² = ‖g₂‖² = a` and with no common irreducible constituent.

(The paper's case analysis is organised by `D = δ_i^* = (θ₁ - θ_i)^*`; the two sub-cases are
`‖D‖² = 2` — a difference of two irreducibles — and `‖D‖² = 4` — a difference of two
norm-two virtual characters.)

## Proof

Write `D = ∑_{a ∈ c.support} c a • a` with `c : ClassFunction K ℂ →₀ ℤ` supported on
`Irr(K)` (layer-2 Fourier API, `mem_ZIrr_inner_self_eq_sum_sq`), so that Parseval gives
`∑_a (c a)² = ‖D‖²` and every coefficient in the support is nonzero
(`Finsupp.mem_support_iff`).

* `a = 1`, so `∑_a (c a)² = 2`: `exists_pair_of_sum_sq_eq_two` (through the library bridge
  `exists_irr_sub_irr_of_inner_self_two`, which additionally uses `D(1) = 0` to force the two
  coefficients to have opposite signs) exhibits `D = α - β` for distinct irreducibles
  `α, β`.  Then `g₁ := α`, `g₂ := β` have norm one and are disjoint, since two distinct
  irreducibles are orthonormal.

* `a = 2`, so `∑_a (c a)² = 4`.  Each `(c a)²` is a positive integer square, so either the
  support is a single index with `(c α)² = 4`, or the support has four indices, all of
  coefficient `±1`; in the latter case any two of them can be put in `S` and the remaining
  two in `T`, giving disjoint `S, T` with `∑_S (c a)² = ∑_T (c a)² = 2`
  (`Work.BG.sumSqFourSplit`).  Given such a split,
  `g₁ := ∑_{a ∈ S} c a • a`, `g₂ := -(∑_{a ∈ T} c a • a)` are virtual characters of norm
  two whose difference is `D`, and they are disjoint because their coefficient supports `S`,
  `T` are (`Work.BG.normFourSplit`).  The single-index alternative would give
  `D(1) = ±2·α(1) ≠ 0`, against the hypothesis.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

theorem s02_twoCase : Work.BG.TwoCaseProp := by
  intro K _ _ _ _ D a ha hD hdeg hnorm
  classical
  rcases ha with rfl | rfl
  · -- `a = 1`: `D` has norm `2` and degree `0`, hence is a difference of two irreducibles.
    have h2 : ClassFunction.inner D D = 2 := by rw [hnorm]; norm_num
    obtain ⟨α, β, hne, heq⟩ := exists_irr_sub_irr_of_inner_self_two hD h2 hdeg
    refine ⟨α, β, α.mem_ZIrr, β.mem_ZIrr, ?_, ?_, heq, ?_⟩
    · rw [irreducibleCharacter_inner_eq_ite]; simp
    · rw [irreducibleCharacter_inner_eq_ite]; simp
    · -- distinct irreducibles are orthonormal, hence disjoint
      intro χ
      by_cases h : α = χ
      · right
        rw [irreducibleCharacter_inner_eq_ite β χ,
          ite_eq_right (fun hb => hne (h.trans hb.symm))]
      · left
        rw [irreducibleCharacter_inner_eq_ite α χ, ite_eq_right h]
  · -- `a = 2`: `D` has norm `4`; split its Fourier support into two norm-two halves.
    have h4 : ClassFunction.inner D D = 4 := by rw [hnorm]; norm_num
    obtain ⟨c, hsupp, hrepr, hsq⟩ := mem_ZIrr_inner_self_eq_sum_sq hD
    have hsumZ : ∑ a ∈ c.support, c a ^ 2 = 4 := by
      have hC : ∑ a ∈ c.support, (c a : ℂ) ^ 2 = 4 := by rw [← hsq]; exact h4
      exact_mod_cast hC
    have hne : ∀ a ∈ c.support, c a ≠ 0 := fun a ha => Finsupp.mem_support_iff.mp ha
    rcases sumSqFourSplit hne hsumZ with
      ⟨α, hs, _hc4⟩ | ⟨S, T, hS, hT, hdisj, hcover, hS2, hT2⟩
    · -- a single coefficient `±2` multiplying an irreducible: degree `≠ 0`
      exfalso
      have hmem : α ∈ c.support := by rw [hs]; simp
      have hα : IsIrreducibleCharacter α := hsupp hmem
      obtain ⟨d, hd, hα1⟩ :=
        irreducibleCharacter_apply_one_eq_pos_natCast (⟨α, hα⟩ : IrreducibleCharacter K)
      have hval : D 1 = (c α : ℂ) * (d : ℂ) := by
        rw [hrepr, hs, Finset.sum_singleton, ClassFunction.smul_apply, hα1]
      rw [hval] at hdeg
      exact (mul_ne_zero (by exact_mod_cast hne α hmem) (by exact_mod_cast hd.ne')) hdeg
    · obtain ⟨g₁, g₂, heq, hg1, hg2, hn1, hn2, hdj⟩ :=
        normFourSplit (fun a ha => hsupp ha) hS hT hdisj hcover hS2 hT2
      exact ⟨g₁, g₂, hg1, hg2, by simpa using hn1, by simpa using hn2,
        hrepr.trans heq, hdj⟩

end Work.BG
