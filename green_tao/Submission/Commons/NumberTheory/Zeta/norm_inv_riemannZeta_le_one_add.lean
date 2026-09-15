import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.Topology.Algebra.InfiniteSum.Field
import Submission.Commons.NumberTheory.Zeta.re_riemannZeta_ofReal_pos

namespace Commons.NumberTheory.Zeta

open Complex

/-- `HasProd` is monotone for nonnegative real-valued families: if `0 ≤ f i ≤ g i` for all `i`
and both `f` and `g` have (unconditional) products, then `∏' f ≤ ∏' g`. (`ℝ` is not an
`IsOrderedMonoid`, so this needs the explicit nonnegativity hypothesis.) -/
lemma hasProd_le_of_nonneg {ι : Type*} {f g : ι → ℝ} {a b : ℝ}
    (hf : HasProd f a) (hg : HasProd g b) (h0 : ∀ i, 0 ≤ f i) (hfg : ∀ i, f i ≤ g i) :
    a ≤ b := by
  rw [HasProd] at hf hg
  exact le_of_tendsto_of_tendsto' hf hg fun s =>
    Finset.prod_le_prod (fun i _ => h0 i) (fun i _ => hfg i)

/-- Pointwise estimate behind the Euler-product proof of `‖1/ζ(s)‖ ≤ ζ(σ)`: for a prime `p`,
`s.re ≥ σ` and `1 < σ`, the factor `1 - p^{-s}` of the Euler product of `1/ζ(s)` is bounded by
the corresponding positive real factor `(1 - p^{-σ})⁻¹` at the real point `σ`. -/
lemma norm_one_sub_cpow_le_inv_of_le {p : ℕ} (hp : p.Prime) {s : ℂ} {σ : ℝ}
    (hσ : 1 < σ) (hs : σ ≤ s.re) :
    ‖1 - (p : ℂ) ^ (-s)‖ ≤ ‖(1 - (p : ℂ) ^ (-((σ : ℝ) : ℂ)))⁻¹‖ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have ht_lt : (p : ℝ) ^ (-σ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hnorm : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
  have hB : (p : ℂ) ^ (-((σ : ℝ) : ℂ)) = (((p : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    rw [show -((σ : ℝ) : ℂ) = ((-σ : ℝ) : ℂ) by simp]
    rw [← Complex.ofReal_natCast p]
    exact (Complex.ofReal_cpow (le_of_lt hp0) (-σ)).symm
  have hR : ‖(1 - (p : ℂ) ^ (-((σ : ℝ) : ℂ)))⁻¹‖ = (1 - (p : ℝ) ^ (-σ))⁻¹ := by
    rw [norm_inv, hB]
    have hsub : (1 : ℂ) - (((p : ℝ) ^ (-σ) : ℝ) : ℂ)
        = (((1 - (p : ℝ) ^ (-σ) : ℝ)) : ℂ) := by push_cast; ring
    rw [hsub, Complex.norm_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - (p : ℝ) ^ (-σ))]
  have hexp : (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-σ) :=
    Real.rpow_le_rpow_of_exponent_le (le_of_lt hp1) (by linarith)
  have hfin : 1 + (p : ℝ) ^ (-σ) ≤ (1 - (p : ℝ) ^ (-σ))⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ (by linarith)]
    nlinarith [sq_nonneg ((p : ℝ) ^ (-σ))]
  calc ‖1 - (p : ℂ) ^ (-s)‖
      ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ) ^ (-s)‖ := norm_sub_le (1 : ℂ) _
    _ = 1 + (p : ℝ) ^ (-s.re) := by rw [norm_one, hnorm]
    _ ≤ 1 + (p : ℝ) ^ (-σ) := by linarith
    _ ≤ (1 - (p : ℝ) ^ (-σ))⁻¹ := hfin
    _ = ‖(1 - (p : ℂ) ^ (-((σ : ℝ) : ℂ)))⁻¹‖ := hR.symm

theorem norm_inv_riemannZeta_le_one_add {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 1 + a ≤ s.re) :
    ‖(riemannZeta s)⁻¹‖ ≤ (riemannZeta ((1 + a : ℝ) : ℂ)).re := by
  have hσ : (1 : ℝ) < 1 + a := by linarith
  have hs1 : 1 < s.re := lt_of_lt_of_le hσ hs
  have hzeta_ne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs1
  have h1 : HasProd (fun p : Nat.Primes => ‖1 - (p : ℂ) ^ (-s)‖) ‖(riemannZeta s)⁻¹‖ := by
    have h := ((riemannZeta_eulerProduct_hasProd hs1).inv₀ hzeta_ne).norm
    simpa using h
  have h2 : HasProd (fun p : Nat.Primes => ‖(1 - (p : ℂ) ^ (-(((1 + a : ℝ) : ℂ))))⁻¹‖)
      ‖riemannZeta (((1 + a : ℝ)) : ℂ)‖ :=
    (riemannZeta_eulerProduct_hasProd hσ).norm
  have hmain : ‖(riemannZeta s)⁻¹‖ ≤ ‖riemannZeta (((1 + a : ℝ)) : ℂ)‖ :=
    hasProd_le_of_nonneg h1 h2 (fun p => norm_nonneg _)
      (fun p => norm_one_sub_cpow_le_inv_of_le p.2 hσ hs)
  refine le_trans hmain ?_
  have hz : riemannZeta (((1 + a : ℝ)) : ℂ) =
      (((riemannZeta (((1 + a : ℝ)) : ℂ)).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using riemannZeta_im_eq_zero_of_one_lt hσ
  rw [hz, Complex.norm_of_nonneg (le_of_lt (re_riemannZeta_ofReal_pos hσ))]
  simp

end Commons.NumberTheory.Zeta