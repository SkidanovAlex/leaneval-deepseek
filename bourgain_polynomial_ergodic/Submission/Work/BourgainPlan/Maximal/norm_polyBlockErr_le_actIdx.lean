import Mathlib
import Submission.Work.BourgainPlan.Maximal.poly_block_core_defs

namespace Work.BourgainPlan.Maximal

open Finset
open scoped BigOperators
open Commons.Analysis.ExponentialSums

/-- **The error of a model block is bounded by the active profile errors.**  At a scale `k ≥ 4m+4` whose sharp window lies inside the major arcs, the profile-replacement error of the `m`-th block is bounded by the sum, over the active index triples, of the weight times the profile error.

Route.  (i) `poly_majorArcBlock_two_pow_eq_sum` and then
`poly_modelQBlock_two_pow_eq_blockPair`: for `4m+4 ≤ k`,
`star(polyModelQBlock P m (2^k) θ) = ∑_{i ∈ blockPair m} ∑_{l ∈ Icc (-1) c} star(polyModelTermArc P i.1 i.2 l k θ)`;
(use `blockQ_eq m k hk`, `sum_blockPair`, `sum_ite_gcd_eq`, `conj_ite_zero`.)
(ii) `polyBlockCore_eq_sum_sharpTerm`:
`polyBlockCore P m k θ = ∑_{i,l} star(polySharpTerm P i.1 i.2 l k θ)` (which is by definition, using
`starRingEnd` of a product with an indicator).
(iii) `polyBlockErr_eq_sum`: subtract and use `Finset.sum_sub_distrib` and `map_sub`.
(iv) The per-term bound `‖polyModelTermArc P q a l k θ - polySharpTerm P q a l k θ‖ ≤ ‖polyWeight P (q*c.toNat) (a+l*q)‖ * polyErrVal P (θ - ((a/q+l)/c)) k`, by cases on the arc condition: on the arc both are `w * (φ - sharp)` (use `polyModelTermPre`'s definition and `polySharpTerm`) and `polyErrVal` is exactly `‖φ - sharp‖`; off the arc both vanish (use `polyModelTermArc_eq_zero_of_not_act` and `polySharpTerm_eq_zero_of_not_act`, the latter needing `hc` and `hcont`).
(v) Sum the triangle inequality over `blockPair m ×ˢ Icc (-1) c` and restrict to the active indices
with `Finset.sum_le_sum_of_subset_of_nonneg` and `Finset.sum_filter`. -/
theorem norm_polyBlockErr_le_actIdx (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff)
    (hd : 2 ≤ P.natDegree) {k : ℕ}
    (hcont : (P.leadingCoeff : ℝ) * (polyDil P k)⁻¹ ≤ polyArcRad P k) {m : ℕ} (hk : 4*m+4 ≤ k)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ‖polyBlockErr P m k θ‖
      ≤ ∑ p ∈ polyActIdx P m k θ,
          ‖polyWeight P (p.1.1 * P.leadingCoeff.toNat) (p.1.2 + p.2 * p.1.1)‖ *
            polyErrVal P (θ - (((p.1.2:ℝ)/(p.1.1:ℝ) + (p.2:ℝ)) / (P.leadingCoeff:ℝ))) k := by
  set g : (ℕ × ℕ) × ℤ → ℝ := fun p =>
    ‖polyWeight P (p.1.1 * P.leadingCoeff.toNat) (p.1.2 + p.2 * p.1.1)‖ *
      polyErrVal P (θ - (((p.1.2:ℝ)/(p.1.1:ℝ) + (p.2:ℝ)) / (P.leadingCoeff:ℝ))) k with hg
  rw [polyBlockErr_eq_sum P hk θ]
  rw [← Finset.sum_product (blockPair m) (Finset.Icc (-1:ℤ) P.leadingCoeff)
    (fun p : (ℕ × ℕ) × ℤ =>
      starRingEnd ℂ (polyModelTermArc P p.1.1 p.1.2 p.2 k θ - polySharpTerm P p.1.1 p.1.2 p.2 k θ))]
  calc ‖∑ p ∈ blockPair m ×ˢ Finset.Icc (-1:ℤ) P.leadingCoeff,
          starRingEnd ℂ (polyModelTermArc P p.1.1 p.1.2 p.2 k θ - polySharpTerm P p.1.1 p.1.2 p.2 k θ)‖
      ≤ ∑ p ∈ blockPair m ×ˢ Finset.Icc (-1:ℤ) P.leadingCoeff,
          (if |(P.leadingCoeff : ℝ) * θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (p.2:ℝ)| ≤ polyArcRad P k
            then g p else 0) := by
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun p hp => ?_))
        by_cases harc : |(P.leadingCoeff : ℝ) * θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (p.2:ℝ)|
            ≤ polyArcRad P k
        · rw [if_pos harc, Complex.norm_conj]
          simpa only [hg] using
            norm_polyModelTermArc_sub_sharp_le P hc hcont (k := k) p.1.1 p.1.2 p.2 θ
        · rw [if_neg harc]
          have h1 := polyModelTermArc_eq_zero_of_not_act P p.1.1 p.1.2 p.2 θ harc
          have h2 := polySharpTerm_eq_zero_of_not_act P hc hcont p.1.1 p.1.2 p.2 θ harc
          rw [h1, h2, sub_zero, map_zero, norm_zero]
    _ = ∑ p ∈ polyActIdx P m k θ, g p := by
        rw [polyActIdx_eq_filter, polyAllIdx, ← Finset.sum_filter]


end Work.BourgainPlan.Maximal
