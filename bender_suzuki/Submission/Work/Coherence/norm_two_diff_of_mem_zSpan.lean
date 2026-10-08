import Mathlib
import Submission.Work.Coherence.Basic
import Submission.Work.Coherence.sum_sq_eq_two

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Difference of two characters from a vector of norm two and degree zero

If `S` is an orthonormal finite set of complex valued functions on a finite group, all of whose
elements have degree of real part at least `1`, and `f ∈ ℤ[S]` has `f 1 = 0` and
`⟨f, f⟩ = 2`, then `f = χ - ψ` or `f = ψ - χ` for two distinct `χ, ψ ∈ S`.

The proof is the classification of the norm-two vectors of `ℤ[S]`: writing
`f = ∑ c_x x` with `c_x ∈ ℤ`, the norm formula gives `∑ c_x² = 2`, so exactly two coefficients
are nonzero and they are `±1`.  Hence `f` is one of `x + y`, `-(x + y)`, `x - y`, `y - x`; the
first two are excluded because `f 1 = 0` while `(x 1).re, (y 1).re ≥ 1` force
`(x 1 + y 1).re ≥ 2 ≠ 0`.
-/

noncomputable section

open Classical

namespace Work.Coherence

theorem norm_two_diff_of_mem_zSpan {G : Type*} [Group G] [Fintype G] {S : Finset (G → ℂ)}
    (hS : Orthonormal S) {f : G → ℂ} (hf : f ∈ ZSpan S) (h1 : f 1 = 0)
    (hdeg : ∀ z ∈ S, 1 ≤ (z 1).re) (h : cfInner f f = 2) :
    ∃ χ ∈ S, ∃ ψ ∈ S, χ ≠ ψ ∧ (f = χ - ψ ∨ f = ψ - χ) := by
  classical
  obtain ⟨c, hc⟩ := mem_zSpan.mp hf
  -- the norm formula turns `⟨f, f⟩ = 2` into an integral sum of squares equal to `2`
  have hsumC : ∑ x : S, ((c x : ℤ) : ℂ) ^ 2 = 2 := by
    rw [← cfInner_self_eq_sum_sq hS hc]; exact h
  have hs : ∑ x : S, (c x) ^ 2 = 2 := by
    apply Int.cast_injective (α := ℂ)
    push_cast
    exact hsumC
  -- so exactly two basis vectors occur, each with coefficient `±1`
  obtain ⟨x, -, y, -, hxy, hcx, hcy, hzero⟩ :=
    sum_sq_eq_two (Finset.univ : Finset S) c hs
  -- `f` is the two-term combination `(c x) • x + (c y) • y`
  have hfval : f = (c x : ℂ) • (x : G → ℂ) + (c y : ℂ) • (y : G → ℂ) := by
    rw [hc]
    rw [← Finset.sum_subset (s₁ := ({x, y} : Finset S))
          (f := fun z : S => (c z : ℂ) • (z : G → ℂ)) (Finset.subset_univ _) (fun z _ hz => by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
            rw [hzero z (Finset.mem_univ z) hz.1 hz.2]
            simp),
      Finset.sum_pair hxy]
  -- and its value at `1` is the corresponding combination of the two values
  have hf1 : f 1 = (c x : ℂ) * ((x : G → ℂ) 1) + (c y : ℂ) * ((y : G → ℂ) 1) := by
    rw [hc, sum_coeff_apply c 1]
    rw [← Finset.sum_subset (s₁ := ({x, y} : Finset S))
          (f := fun z : S => (c z : ℂ) * ((z : G → ℂ) 1)) (Finset.subset_univ _) (fun z _ hz => by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
            rw [hzero z (Finset.mem_univ z) hz.1 hz.2]
            simp),
      Finset.sum_pair hxy]
  -- degrees are at least `1`, so a sum of two degrees cannot vanish
  have hsum_ne : (x : G → ℂ) 1 + (y : G → ℂ) 1 ≠ 0 := by
    intro h0
    have hre : (((x : G → ℂ) 1) + ((y : G → ℂ) 1)).re = 0 := by rw [h0]; simp
    rw [Complex.add_re] at hre
    have hx := hdeg (x : G → ℂ) x.2
    have hy := hdeg (y : G → ℂ) y.2
    linarith
  have hx1 : c x = 1 ∨ c x = -1 := sq_eq_one_iff.mp hcx
  have hy1 : c y = 1 ∨ c y = -1 := sq_eq_one_iff.mp hcy
  rcases hx1 with hx1 | hx1 <;> rcases hy1 with hy1 | hy1
  · -- both coefficients `1`: `f = x + y`, impossible
    exfalso
    have hf1' : f 1 = (x : G → ℂ) 1 + (y : G → ℂ) 1 := by
      rw [hf1, hx1, hy1]; ring
    rw [hf1'] at h1
    exact hsum_ne h1
  · -- `c x = 1`, `c y = -1`: `f = x - y`
    refine ⟨(x : G → ℂ), x.2, (y : G → ℂ), y.2, ?_, Or.inl ?_⟩
    · exact fun h => hxy (Subtype.coe_injective h)
    · rw [hfval, hx1, hy1]
      simp [sub_eq_add_neg]
  · -- `c x = -1`, `c y = 1`: `f = y - x`
    refine ⟨(x : G → ℂ), x.2, (y : G → ℂ), y.2, ?_, Or.inr ?_⟩
    · exact fun h => hxy (Subtype.coe_injective h)
    · rw [hfval, hx1, hy1]
      simp [sub_eq_add_neg, add_comm]
  · -- both coefficients `-1`: `f = -(x + y)`, impossible
    exfalso
    have hf1' : f 1 = -((x : G → ℂ) 1 + (y : G → ℂ) 1) := by
      rw [hf1, hx1, hy1]; ring
    rw [hf1'] at h1
    exact hsum_ne (neg_eq_zero.mp h1)

end Work.Coherence
