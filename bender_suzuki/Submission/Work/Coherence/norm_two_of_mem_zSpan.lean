import Mathlib
import Submission.Work.Coherence.Basic
import Submission.Work.Coherence.sum_sq_eq_two

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Vectors of norm two in `ℤ[S]` (for `S` orthonormal) are signed sums of two elements

If `S` is an orthonormal finite set of complex valued functions on a finite group and
`f ∈ ℤ[S]` satisfies `⟨f, f⟩ = 2`, then `f = ±(χ + ψ)` or `f = ±(χ - ψ)` for two distinct
elements `χ, ψ` of `S`.

Writing `f = ∑_{x ∈ S} c_x x` with `c_x ∈ ℤ`, the norm formula `cfInner_self_eq_sum_sq` gives
`∑_x c_x² = 2`; a sum of squares of integers equal to two has exactly two nonzero terms
(`sum_sq_eq_two`), each of which is `±1`, and the four sign combinations give precisely the
four possibilities `χ + ψ`, `-(χ + ψ)`, `χ - ψ`, `ψ - χ`.
-/

noncomputable section

open Classical

namespace Work.Coherence

universe u

variable {G : Type*}

section

variable [Group G] [Fintype G]

/-- **A vector of `ℤ[S]` of norm two.**  If `S` is orthonormal and `f ∈ ℤ[S]` has
`⟨f, f⟩ = 2`, then `f` is a signed sum of two distinct elements of `S`. -/
theorem norm_two_of_mem_zSpan {G : Type*} [Group G] [Fintype G] {S : Finset (G → ℂ)}
    (hS : Orthonormal S) {f : G → ℂ} (hf : f ∈ ZSpan S) (h : cfInner f f = 2) :
    ∃ χ ∈ S, ∃ ψ ∈ S, χ ≠ ψ ∧
      (f = χ + ψ ∨ f = -(χ + ψ) ∨ f = χ - ψ ∨ f = ψ - χ) := by
  classical
  obtain ⟨c, hc⟩ := mem_zSpan.mp hf
  -- the norm formula turns `⟨f, f⟩ = 2` into `∑ c_x² = 2` over the integers
  have hsumC : ∑ x : S, ((c x : ℤ) : ℂ) ^ 2 = 2 := by
    rw [← cfInner_self_eq_sum_sq hS hc]; exact h
  have hs : ∑ x : S, (c x) ^ 2 = 2 := by
    apply Int.cast_injective (α := ℂ)
    push_cast
    exact hsumC
  -- exactly two coefficients are nonzero, and each is `±1`
  obtain ⟨x, _hx, y, _hy, hxy, hcx, hcy, hzero⟩ := sum_sq_eq_two Finset.univ c hs
  -- hence `f` is the two-term combination `c_x x + c_y y`
  have hpair : f = (c x : ℂ) • (x : G → ℂ) + (c y : ℂ) • (y : G → ℂ) := by
    have hswap : (∑ z ∈ ({x, y} : Finset S), (c z : ℂ) • (z : G → ℂ))
        = ∑ z : S, (c z : ℂ) • (z : G → ℂ) := by
      refine Finset.sum_subset (by intro z hz; simp) ?_
      intro z _ hznot
      have hz0 : c z = 0 := hzero z (Finset.mem_univ z)
        (fun hh => hznot (by simp [hh])) (fun hh => hznot (by simp [hh]))
      simp [hz0]
    rw [hc, ← hswap, Finset.sum_pair hxy]
  refine ⟨(x : G → ℂ), x.2, (y : G → ℂ), y.2, ?_, ?_⟩
  · intro hh; exact hxy (Subtype.ext hh)
  · rcases sq_eq_one_iff.mp hcx with hx1 | hx1 <;> rcases sq_eq_one_iff.mp hcy with hy1 | hy1
    · left; rw [hpair, hx1, hy1]; simp
    · right; right; left; rw [hpair, hx1, hy1]; simp [sub_eq_add_neg]
    · right; right; right; rw [hpair, hx1, hy1]; simp; abel
    · right; left; rw [hpair, hx1, hy1]; simp; abel

end

end Work.Coherence
