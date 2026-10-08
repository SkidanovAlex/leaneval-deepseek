import Mathlib
import Submission.Work.Coherence.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Coherence

/-- An element of the lattice `ℤ[S]` spanned by an orthonormal set has non-negative "norm"
`⟨f, f⟩ = ∑_x (c x)²`; if that norm vanishes then all integral coordinates vanish and `f = 0`. -/
theorem norm_zero_of_mem_zSpan {G : Type*} [Group G] [Fintype G] {S : Finset (G → ℂ)}
    (hS : Orthonormal S) {f : G → ℂ} (hf : f ∈ ZSpan S) (h : cfInner f f = 0) : f = 0 := by
  obtain ⟨c, hc⟩ := mem_zSpan.mp hf
  -- `⟨f, f⟩` is the sum of the squares of the integral coordinates.
  have hsq : ∑ x : S, ((c x : ℤ) : ℂ) ^ 2 = 0 := by
    rw [← cfInner_self_eq_sum_sq hS hc, h]
  -- Read that sum as the image of the corresponding real sum of squares.
  have hcast : ∑ x : S, ((c x : ℤ) : ℂ) ^ 2 = ((∑ x : S, ((c x : ℝ)) ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun x _ => by push_cast; ring
  rw [hcast] at hsq
  have hreal : ∑ x : S, ((c x : ℝ)) ^ 2 = 0 := Complex.ofReal_eq_zero.mp hsq
  -- A sum of non-negative squares vanishing forces each square to vanish.
  have hzero : ∀ x : S, ((c x : ℝ)) ^ 2 = 0 := by
    have := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
      (f := fun x : S => ((c x : ℝ)) ^ 2) (fun x _ => sq_nonneg _)).mp hreal
    exact fun x => this x (Finset.mem_univ x)
  rw [hc]
  refine Finset.sum_eq_zero fun x _ => ?_
  have hc0 : c x = 0 := by
    have h1 : (c x : ℝ) = 0 := (sq_eq_zero_iff).mp (hzero x)
    exact_mod_cast h1
  rw [hc0]
  simp

end Work.Coherence
