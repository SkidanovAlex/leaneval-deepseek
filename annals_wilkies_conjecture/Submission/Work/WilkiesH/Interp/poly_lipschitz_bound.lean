import Mathlib
import Submission.Work.WilkiesH.Defs
import Submission.Work.WilkiesH.Interp.abs_eval_sub_le
import Submission.Work.WilkiesH.Interp.support_sum_degree_le
import Submission.Work.WilkiesH.Interp.abs_eval_map_sub_le_sum

/-!
# Area I — the Lipschitz bound on the cube

For an integral polynomial `P` in `n` variables of total degree `≤ d`, with all coefficients
bounded by `N` in absolute value, the evaluation difference at two points of the cube
`[-1,1]^n` is bounded by `monoCount n d · N · d` times the `ℓ¹`-distance of the points.

The proof is the monomial expansion of the evaluation difference: writing `P` as the sum of its
monomials, the difference of `∏ᵢ yᵢ^{mᵢ}` and `∏ᵢ y'ᵢ^{mᵢ}` telescopes to the single-variable
estimates `|yᵢ^k - y'ᵢ^k| ≤ k |yᵢ - y'ᵢ|` on the cube; summing over the support of `P` and using
that the support injects into the monomials of degree `≤ d` (`support_sum_degree_le`) gives the
claim.
-/

set_option autoImplicit false
noncomputable section

namespace Work.WilkiesH.Interp

open MvPolynomial

/-- The evaluation difference of an integral polynomial at two real points, expanded over the
support of `P`: the coefficients are cast to `ℝ` and the monomial difference is factored. -/
lemma eval_map_sub_eq_sum {n : ℕ} (P : MvPolynomial (Fin n) ℤ) (y y' : Fin n → ℝ) :
    MvPolynomial.eval y (P.map (Int.castRingHom ℝ))
        - MvPolynomial.eval y' (P.map (Int.castRingHom ℝ))
      = ∑ m ∈ P.support, ((P.coeff m : ℝ) * (∏ i, y i ^ m i - ∏ i, y' i ^ m i)) := by
  have hsu : (P.map (Int.castRingHom ℝ)).support = P.support :=
    MvPolynomial.support_map_of_injective P (fun a b h => Int.cast_injective h)
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', hsu]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_map, Int.coe_castRingHom]
  ring

/-- A support coefficient of `P`, cast to `ℝ`, is still bounded by `N`. -/
lemma coeff_cast_abs_le {n : ℕ} (P : MvPolynomial (Fin n) ℤ) {N : ℕ}
    (hcoef : ∀ m ∈ P.support, |(P.coeff m : ℤ)| ≤ (N : ℤ))
    {m : Fin n →₀ ℕ} (hm : m ∈ P.support) : |(P.coeff m : ℝ)| ≤ (N : ℝ) := by
  have h1 : |(P.coeff m : ℝ)| = ((|(P.coeff m : ℤ)| : ℤ) : ℝ) := by rw [Int.cast_abs]
  rw [h1]
  exact_mod_cast hcoef m hm

/-- **The Lipschitz bound.**  For an integral polynomial of total degree `≤ d` whose coefficients
are bounded by `N`, the evaluation difference at two points `y, y'` of the cube `[-1,1]^n` is at
most `monoCount n d · N · d · ‖y - y'‖₁`. -/
theorem poly_lipschitz_bound {μ d N : ℕ} (P : MvPolynomial (Fin (μ + 1)) ℤ)
    (hdeg : P.totalDegree ≤ d) (hcoef : ∀ m ∈ P.support, |(P.coeff m : ℤ)| ≤ (N : ℤ))
    {y y' : Fin (μ + 1) → ℝ} (hy : ∀ i, |y i| ≤ 1) (hy' : ∀ i, |y' i| ≤ 1) :
    |MvPolynomial.eval y (P.map (Int.castRingHom ℝ))
        - MvPolynomial.eval y' (P.map (Int.castRingHom ℝ))|
      ≤ ((Work.WilkiesH.monoCount (μ + 1) d : ℝ) * (N : ℝ) * (d : ℝ))
        * (∑ i, |y i - y' i|) := by
  classical
  set ρ : ℝ := ∑ i, |y i - y' i| with hρdef
  have hρ0 : 0 ≤ ρ := by
    rw [hρdef]
    exact Finset.sum_nonneg fun i _ => abs_nonneg _
  have hcoefR : ∀ m ∈ P.support, |(P.coeff m : ℝ)| ≤ (N : ℝ) :=
    fun m hm => coeff_cast_abs_le P hcoef hm
  -- the reduction to a coefficient-weighted degree sum
  have hred' : |MvPolynomial.eval y (P.map (Int.castRingHom ℝ))
        - MvPolynomial.eval y' (P.map (Int.castRingHom ℝ))|
      ≤ ∑ m ∈ P.support, |(P.coeff m : ℝ)| * (((∑ i, m i : ℕ) : ℝ) * ρ) := by
    have h := abs_eval_map_sub_le_sum P hy hy'
    rwa [← hρdef] at h
  -- pull out the coefficient bound `N`
  have hsum : ∑ m ∈ P.support, |(P.coeff m : ℝ)| * (((∑ i, m i : ℕ) : ℝ) * ρ)
      ≤ (N : ℝ) * ∑ m ∈ P.support, (((∑ i, m i : ℕ) : ℝ) * ρ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun m hm => ?_
    have hnn : 0 ≤ ((∑ i, m i : ℕ) : ℝ) * ρ := mul_nonneg (Nat.cast_nonneg _) hρ0
    exact mul_le_mul_of_nonneg_right (hcoefR m hm) hnn
  have hfac : (N : ℝ) * ∑ m ∈ P.support, (((∑ i, m i : ℕ) : ℝ) * ρ)
      = (N : ℝ) * ρ * ∑ m ∈ P.support, ((∑ i, m i : ℕ) : ℝ) := by
    rw [← Finset.sum_mul]
    ring
  -- the counting bound
  have hlead : ∑ m ∈ P.support, ((∑ i, m i : ℕ) : ℝ)
      ≤ (Work.WilkiesH.monoCount (μ + 1) d : ℝ) * (d : ℝ) := by
    have hnat := support_sum_degree_le P hdeg
    calc ∑ m ∈ P.support, ((∑ i, m i : ℕ) : ℝ)
        = ((∑ m ∈ P.support, (∑ i, m i : ℕ)) : ℝ) := by simp only [Nat.cast_sum]
      _ ≤ ((Work.WilkiesH.monoCount (μ + 1) d * d : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = (Work.WilkiesH.monoCount (μ + 1) d : ℝ) * (d : ℝ) := by push_cast; ring
  calc |MvPolynomial.eval y (P.map (Int.castRingHom ℝ))
        - MvPolynomial.eval y' (P.map (Int.castRingHom ℝ))|
      ≤ ∑ m ∈ P.support, |(P.coeff m : ℝ)| * (((∑ i, m i : ℕ) : ℝ) * ρ) := hred'
    _ ≤ (N : ℝ) * ∑ m ∈ P.support, (((∑ i, m i : ℕ) : ℝ) * ρ) := hsum
    _ = (N : ℝ) * ρ * ∑ m ∈ P.support, ((∑ i, m i : ℕ) : ℝ) := hfac
    _ ≤ (N : ℝ) * ρ * ((Work.WilkiesH.monoCount (μ + 1) d : ℝ) * (d : ℝ)) :=
          mul_le_mul_of_nonneg_left hlead (mul_nonneg (Nat.cast_nonneg N) hρ0)
    _ = ((Work.WilkiesH.monoCount (μ + 1) d : ℝ) * (N : ℝ) * (d : ℝ)) * ρ := by ring

end Work.WilkiesH.Interp
