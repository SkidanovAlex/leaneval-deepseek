import Mathlib
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.star_Irr
import Submission.Work.CharCore.isVChar_iff_exists_int_coeffs
import Submission.Work.Clifford.CharPair

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A virtual character of norm one is `±` an irreducible character

Let `f` be a virtual (integral) character of a finite group `G`, i.e. an integral linear
combination of the irreducible characters `Irr G`.  If its norm for the character inner
product `cfInner` equals `1`, then `f` is `±χ` for a single irreducible character `χ`.

This is the "norm-one" step used, for instance, in the Frobenius-group arguments of the
odd-order project: it says that an element of the integral lattice of virtual characters
with self-inner-product one is (up to sign) a basis vector.

## Proof

Write `f = ∑_{χ ∈ Irr G} c χ • χ` with integer coefficients `c` (this is the concrete
description of `IsVChar`, `Work.CharCore.isVChar_iff_exists_int_coeffs`).  Bilinearity of
`cfInner` together with the orthonormality of `Irr G` for `cfInner`
(`Work.CharCore.irr_orthonormal_charCore`, obtained here from the orthonormality of `Irr G`
for the bilinear pairing `Work.Clifford.charPair` and the identity
`star (χ g) = χ g⁻¹` of `Work.CharCore.star_Irr`) gives

`cfInner f f = ∑_{χ} (c χ)^2`.

A sum of squares of integers equal to `1` has exactly one nonzero summand, equal to `±1`
(`Work.CharCore.sum_sq_eq_one_int`), so `f` is `±χ` for that `χ`.

## Main results

* `Work.CharCore.irr_orthonormal_charCore` — `Irr G` is orthonormal for `cfInner`.
* `Work.CharCore.cfInner_eq_sum_sq` — the norm of an integral combination is the sum of the
  squares of the coefficients.
* `Work.CharCore.sum_sq_eq_one_int` — integer arithmetic.
* `Work.CharCore.vchar_norm_one` — the target.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Classical Finset

namespace Work.CharCore

variable {G : Type*} [Group G] [Fintype G]

/-- **Orthonormality of the irreducible characters of `G` for `cfInner`.**

`⟪χ, ψ⟫ = 1` if `χ = ψ` and `= 0` otherwise, for `χ, ψ ∈ Irr G`.

The bilinear companion of `cfInner` is `Work.Clifford.charPair f g = |G|⁻¹ ∑_x f x * g x⁻¹`,
for which `Irr G` is orthonormal by `Work.Clifford.charPair_eq_ite_of_mem_Irr`.  The two
pairings agree on `Irr G` because `star (ψ x) = ψ x⁻¹` (`Work.CharCore.star_Irr`). -/
theorem irr_orthonormal_charCore {χ ψ : G → ℂ} (hχ : χ ∈ Irr G) (hψ : ψ ∈ Irr G) :
    cfInner χ ψ = if χ = ψ then 1 else 0 := by
  have hbridge : cfInner χ ψ = Work.Clifford.charPair χ ψ := by
    rw [cfInner_apply, Work.Clifford.charPair_apply, Fintype.card_eq_nat_card]
    congr 1
    exact Finset.sum_congr rfl fun x _ => by rw [star_Irr ψ hψ x]
  rw [hbridge, Work.Clifford.charPair_eq_ite_of_mem_Irr hχ hψ]

/-- **The norm of an integral combination of irreducible characters is the sum of the squares
of its coefficients.** -/
theorem cfInner_eq_sum_sq {s : Finset (G → ℂ)} (hs : (s : Set (G → ℂ)) ⊆ Irr G) (c : s → ℤ) :
    cfInner (∑ x : s, (c x : ℂ) • (x : G → ℂ))
            (∑ x : s, (c x : ℂ) • (x : G → ℂ)) = ∑ x : s, ((c x : ℤ) : ℂ) ^ 2 := by
  rw [cfInner_sum_smul_left]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [cfInner_sum_smul_right]
  -- the inner sum collapses to the single term `x`
  have hinner : (∑ y : s, starRingEnd ℂ ((c y : ℤ) : ℂ) * cfInner (x : G → ℂ) (y : G → ℂ))
      = ((c x : ℤ) : ℂ) := by
    refine (Finset.sum_eq_single x ?_ ?_).trans ?_
    · intro y _ hy
      rw [irr_orthonormal_charCore (hs x.2) (hs y.2)]
      have hne : ¬ ((x : G → ℂ) = (y : G → ℂ)) := fun hh => hy (Subtype.ext hh).symm
      simp [hne]
    · intro hh; exact absurd (Finset.mem_univ x) hh
    · rw [irr_orthonormal_charCore (hs x.2) (hs x.2)]
      simp
  rw [hinner]
  ring

/-- A sum of squares of integers equal to `1` has exactly one nonzero summand, and it is `±1`. -/
theorem sum_sq_eq_one_int {ι : Type*} [Fintype ι] (c : ι → ℤ)
    (h : ∑ i, c i ^ 2 = 1) :
    ∃ i₀, (c i₀ = 1 ∨ c i₀ = -1) ∧ ∀ i, i ≠ i₀ → c i = 0 := by
  classical
  -- some coefficient is nonzero
  have hex : ∃ i, c i ≠ 0 := by
    by_contra hcon
    have h0 : ∑ i, c i ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have : c i = 0 := by
        by_contra hci
        exact hcon ⟨i, hci⟩
      simp [this]
    omega
  obtain ⟨i₀, hi₀⟩ := hex
  -- and then it is `±1`
  have hle : c i₀ ^ 2 ≤ 1 := by
    have h1 : c i₀ ^ 2 ≤ ∑ i, c i ^ 2 :=
      Finset.single_le_sum (fun i _ => sq_nonneg (c i)) (Finset.mem_univ i₀)
    rwa [h] at h1
  have hge : 1 ≤ c i₀ ^ 2 := by
    have hpos := sq_pos_of_ne_zero hi₀
    omega
  have heq : c i₀ ^ 2 = 1 := le_antisymm hle hge
  have hunit : c i₀ = 1 ∨ c i₀ = -1 := sq_eq_one_iff.mp heq
  refine ⟨i₀, hunit, ?_⟩
  -- all the other coefficients vanish because the remaining sum of squares is `0`
  intro i hi
  have herase : ∑ j ∈ Finset.univ.erase i₀, c j ^ 2 = 0 := by
    have hsplit := Finset.sum_erase_add (s := Finset.univ) (f := fun j => c j ^ 2)
      (Finset.mem_univ i₀)
    rw [h, heq] at hsplit
    omega
  have hz : c i ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (c j))).mp herase i
      (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)
  exact sq_eq_zero_iff.mp hz

theorem vchar_norm_one {G : Type*} [Group G] [Fintype G] {f : G → ℂ} (hf : IsVChar f)
    (h : cfInner f f = 1) : ∃ χ ∈ Irr G, f = χ ∨ f = -χ := by
  obtain ⟨c, hc⟩ := (isVChar_iff_exists_int_coeffs (G := G)).mp hf
  subst hc
  -- the norm formula turns `cfInner f f = 1` into `∑ (c χ)^2 = 1` over the integers
  have hsum : ∑ χ : ↥(Irr G), (c χ) ^ 2 = 1 := by
    have hsqC := cfInner_eq_sum_sq (s := Irr G) (fun _ hx => hx) c
    rw [hsqC] at h
    have hcast : ((∑ χ : ↥(Irr G), (c χ) ^ 2 : ℤ) : ℂ) = ((1 : ℤ) : ℂ) := by
      push_cast
      exact h
    exact Int.cast_injective hcast
  obtain ⟨χ₀, hunit, hzero⟩ := sum_sq_eq_one_int c hsum
  -- so `f` is `±` the single summand at `χ₀`
  refine ⟨(χ₀ : G → ℂ), χ₀.2, ?_⟩
  have hfval : (∑ χ : ↥(Irr G), (c χ : ℂ) • (χ : G → ℂ))
      = (c χ₀ : ℂ) • (χ₀ : G → ℂ) := by
    rw [Finset.sum_eq_single χ₀]
    · intro b _ hb
      rw [hzero b hb]; simp
    · intro hb; exact absurd (Finset.mem_univ χ₀) hb
  rcases hunit with h1 | h1
  · left; rw [hfval, h1]; simp
  · right; rw [hfval, h1]; simp

end Work.CharCore
