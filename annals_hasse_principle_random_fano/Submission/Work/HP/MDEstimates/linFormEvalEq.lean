import Mathlib

namespace Work.HP.MDEstimates

/-- A degree-1 homogeneous polynomial is its own degree-1 Taylor expansion: evaluating it at `y`
is the sum of its coordinate coefficients times the corresponding coordinate of `y`. -/
lemma linFormEvalEq {σ : Type*} [DecidableEq σ] [Fintype σ]
    {g : MvPolynomial σ ℚ} (hg : g.IsHomogeneous 1) (y : σ → ℚ) :
    MvPolynomial.eval y g = ∑ i, g.coeff (Finsupp.single i 1) * y i := by
  classical
  -- Every monomial appearing in `g` has degree one, so only the coefficients at
  -- `Finsupp.single i 1` can be nonzero.
  have hcoeff : ∀ v : σ →₀ ℕ, v.degree ≠ 1 → g.coeff v = 0 := by
    intro v hv
    by_contra h
    have h1 : Finsupp.weight (1 : σ → ℕ) v = 1 := hg h
    exact hv (by rw [Finsupp.degree_eq_weight_one]; exact h1)
  have hsub : g.support ⊆ Finset.univ.image (fun i : σ => Finsupp.single i 1) := by
    intro v hv
    rw [Finset.mem_image]
    have hdeg : v.degree = 1 := by
      by_contra h
      exact (MvPolynomial.mem_support_iff.mp hv) (hcoeff v h)
    have hr : v ∈ Set.range (fun i : σ => Finsupp.single i 1) := by
      rw [Finsupp.range_single_one]; exact hdeg
    obtain ⟨i, hi⟩ := hr
    exact ⟨i, Finset.mem_univ i, hi⟩
  -- Hence `g` is the linear combination `∑ i, (coeff at X i) • X i`.
  have hkey : g = ∑ i : σ,
      MvPolynomial.monomial (Finsupp.single i 1) (g.coeff (Finsupp.single i 1)) := by
    rw [MvPolynomial.as_sum g]
    rw [Finset.sum_subset hsub (fun x _ hx => by
      rw [MvPolynomial.mem_support_iff] at hx
      rw [not_not] at hx
      rw [hx, map_zero])]
    conv_lhs => rw [Finset.sum_image (s := Finset.univ)
        (g := fun i : σ => Finsupp.single i 1)
        (f := fun v => MvPolynomial.monomial v (g.coeff v))
        (by intro x _ y _ hxy; rw [Finsupp.single_left_injective one_ne_zero hxy])]
    simp
  have hstep : MvPolynomial.eval y g =
      MvPolynomial.eval y (∑ i : σ,
        MvPolynomial.monomial (Finsupp.single i 1) (g.coeff (Finsupp.single i 1))) :=
    congrArg (MvPolynomial.eval y) hkey
  rw [hstep, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MvPolynomial.eval_monomial, Finsupp.prod_single_index (by simp)]
  simp

end Work.HP.MDEstimates
