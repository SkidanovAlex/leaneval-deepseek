import Mathlib
import Submission.Work.Q44Geom.Setup
import Submission.Work.Q44Geom.sat_span

/-!
# `Work.HP.MDEstimates.vanishRatSpanCub`

If a homogeneous cubic `B ∈ ℚ[X₀,…,X₄]` vanishes at every lattice point of a sublattice
`L ⊆ ℤ⁵`, then it vanishes on the whole `ℚ`-span `ratSpan L`.

The argument is "clear denominators, then use homogeneity".  If `x ∈ ratSpan L`, then by
`Work.Q44Geom.mem_ratSpan_iff'` there is a nonzero integer `n` with `n • x` lying in the
image of `L` under the coefficientwise coercion `ℤ⁵ → ℚ⁵`.  Since `B` vanishes on `L`,
`eval (n • x) B = 0`; by homogeneity of degree `3`, `eval (n • x) B = n³ · eval x B`, and
`n ≠ 0` gives the claim.
-/

set_option autoImplicit false

namespace Work.HP.MDEstimates

open MvPolynomial

/-- Scaling a product of monomial factors: replacing the point `x` by `c * x` multiplies
`∏ i, x i ^ (d i)` by `c ^ (∑ i, d i)`. -/
lemma prod_smul_eq (d : Fin 5 →₀ ℕ) (c : ℚ) (x : Fin 5 → ℚ) :
    ∏ i, (c * x i) ^ d i = c ^ (∑ i, d i) * ∏ i, x i ^ d i := by
  rw [Finset.prod_congr rfl (fun i _ => mul_pow c (x i) (d i))]
  rw [Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum]

/-- Homogeneity in monomial form: for a polynomial `B` homogeneous of degree `n`,
evaluating at `fun i => c * x i` scales the value by `c ^ n`. -/
lemma eval_smul_point (B : MvPolynomial (Fin 5) ℚ) (n : ℕ) (hB : B.IsHomogeneous n)
    (c : ℚ) (x : Fin 5 → ℚ) :
    MvPolynomial.eval (fun i => c * x i) B = c ^ n * MvPolynomial.eval x B := by
  rw [MvPolynomial.eval_eq' (fun i => c * x i) B, MvPolynomial.eval_eq' x B, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i, d i = n := by
    rw [← Finsupp.degree_eq_sum]
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hd) (hB.coeff_eq_zero h)
  rw [prod_smul_eq d c x, hdeg]
  ring

/-- Homogeneity for an integer dilation of the point. -/
lemma eval_zsmul_point (B : MvPolynomial (Fin 5) ℚ) (n : ℕ) (hB : B.IsHomogeneous n)
    (k : ℤ) (x : Fin 5 → ℚ) :
    MvPolynomial.eval (k • x) B = (k : ℚ) ^ n * MvPolynomial.eval x B := by
  have hp : (k • x) = fun i => (k : ℚ) * x i := by
    funext i; rw [Pi.smul_apply, zsmul_eq_mul]
  rw [hp, eval_smul_point B n hB (k : ℚ) x]

theorem vanishRatSpanCub {B : MvPolynomial (Fin 5) ℚ} (hB : B.IsHomogeneous 3)
    {L : Submodule ℤ (Fin 5 → ℤ)}
    (hv : ∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) B = 0) :
    ∀ x ∈ Work.Q44Geom.ratSpan L, MvPolynomial.eval x B = 0 := by
  intro x hx
  -- clear denominators: a nonzero integer multiple of `x` is the rational image of `w ∈ L`
  obtain ⟨n, hn, hmem⟩ := (Work.Q44Geom.mem_ratSpan_iff' L x).mp hx
  rw [Submodule.mem_map] at hmem
  obtain ⟨w, hwL, hw⟩ := hmem
  have hvan : MvPolynomial.eval (fun i => (w i : ℚ)) B = 0 := hv w hwL
  have h1 : MvPolynomial.eval (n • x) B = 0 := by
    rw [← hw]; exact hvan
  -- homogeneity of degree `3`
  rw [eval_zsmul_point B 3 hB n x] at h1
  exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero 3 (by exact_mod_cast hn))

end Work.HP.MDEstimates
