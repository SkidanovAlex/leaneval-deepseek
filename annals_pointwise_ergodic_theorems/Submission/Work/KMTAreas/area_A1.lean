/-
Area A1 of the frozen KMT contract: `Work.KMTContract.AreaA1`, i.e.
`Work.Analysis.IWMultiplier.IWMultiplierBoundStatement_even` — the Ionescu–Wainger multiplier
theorem for even exponents (MSZ3 Theorem 2.1; cited by Krause–Mirek–Tao as Theorem `thm:iw` and
proved in their Appendix `iw-app` by reference to `[MSZ3, Theorem 2.1]`).

## What is proved here (complete)

`AreaA1` is the conjunction of

1. *non-aliasing* of the good major arcs
   (`Work.Analysis.IonescuWainger.exists_goodMajorArcs_nonAliasing`, proved in the workspace), and
2. the *multiplier bound* `‖T^{≤l}_φ‖_{ℓ^{2k₀}(ℤ;H)} ≲ ⟨l⟩ ‖T_φ‖_{L^{2k₀}(ℝ)}` for `k₀ ≥ 2`.

The reduction of (2) to the single `Prop` `Work.KMTAreas.IWEvenMultiplierGap`
(`Submission/Work/KMTAreas/iw_family.lean`) is proved there as
`Work.KMTAreas.areaA1_of_IWEvenMultiplierGap`, and the gap itself is proved in
`Submission/Work/KMTAreas/iwGap.lean` as `Work.KMTAreas.iwEvenMultiplierGap_proof`.

## The proof of the gap (route map)

* `Work.KMTAreas.main_signed_strata_uniform` — Tao's `main` for an arbitrary *signed* selection of
  the strata of a pairwise coprime set (the superset form: a bound for the full arc set does not
  control its subsets).  It is the proof of the closure's `main_narrow_sigmaLe_uniform` with the
  coefficients `εs` threaded through Tao's `ortho-apply`(i).
* `Work.KMTAreas.strata_biUnion_eq_iwArithFreqs` — the arithmetic identification of
  `(ℚ/ℤ)_{≤l} = iwArithFreqs ρ l` with the union of the strata `Σ_A` over the selected subsets
  `P = {A ⊆ S_l : |A| ≤ D_ρ+1, Q_0^{(l)} ∈ A or |A| ≤ D_ρ}` of Tao's denominator set `S_l`
  (`Work.KMTAreas.iwSL`), so that `εs = 1_P` turns the signed strata sum into
  `T^{≤l}_φ = opArc ψ (iwArithFreqs ρ l)`.
* the *large* scales `l ≥ l₀(r,ρ)`: the arithmetic core `2r ε (iwSLmax)^{2r(D_ρ+1)} < 1/2`
  (`Work.KMTAreas.iwSLmax_smallness_large`) supplies all six smallness hypotheses of Tao's `main`
  (via `nonce_smallness_of_good` / `petal_smallness_of_good`), the flat bump comes from
  `exists_flat_bump_uniform`, and the multiplier-norm hypothesis `IWMult r (periodize φ) M` from
  `IsLqMultiplierBound (2r) φ M` is `Work.KMTAreas.IWMult_periodize`.
* the *small* scales `l < l₀(r,ρ)`: finitely many, bounded elementarily by the single-arc
  Magyar–Stein–Wainger bound plus the triangle inequality
  (`Work.KMTAreas.iwArithFreqs_small_scale`).
* the `tsum`-to-`eLpNorm` conversion (`Work.KMTAreas.eLpNorm_count_le_of_tsum_le`) and the
  quantitative scalar-to-vector lift (`Work.KMTAreas.IWLqBound_of_scalar_mul`).

The threshold `l₀(r,ρ)` depends on the exponent but not on the scale, which is exactly the
quantifier order `∃C_ρ, ∀q, ∃C_q, ∀l,k` of Theorem `thm:iw`.
-/
import Mathlib
import Submission.Work.KMTAreas.iwGap

set_option autoImplicit false

namespace Work.KMTAreas

/-- **Area A1** of the frozen KMT contract. -/
theorem area_A1 : Work.KMTContract.AreaA1 :=
  Work.KMTAreas.areaA1_of_IWEvenMultiplierGap iwEvenMultiplierGap_proof

end Work.KMTAreas
