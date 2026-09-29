import Mathlib
import Submission.Work.C7.xdefs
import Submission.Work.CLift.defs

/-!
# The analytic evaluation of `Lps = log(1-x)`, and why `PowerSeries.eval₂` cannot express it

The requested lemma `Work.C7.eval2_Lps`,

```
PowerSeries.eval₂ (algebraMap ℚ ℂ) z Work.C7.Lps = Complex.log (1 - z)      (‖z‖ < 1),
```

is **not a theorem**.  `PowerSeries.eval₂` is `MvPowerSeries.eval₂`, which is *not* analytic
evaluation into `ℂ`: it is the extension of polynomial evaluation by density along
`MvPolynomial.toMvPowerSeries`, and *every* Mathlib lemma that computes its value at a
non-polynomial series (`eval₂_eq_tsum`, `hasSum_eval₂`, `continuous_eval₂`, `eval₂Hom`, `aeval`,
`eval₂_unique`, …) requires the hypothesis `IsLinearTopology S S` on the target.  For
`S = ℂ` with its usual topology that hypothesis is false — the only `ℂ`-submodules of `ℂ` are
`⊥` and `⊤`, so a basis of neighbourhoods of `0` made of submodules would force
`({0} : Set ℂ) ∈ 𝓝 0` (see `not_isLinearTopology_complex` below).  Consequently, for a
`f : PowerSeries ℚ` which is not a polynomial, `PowerSeries.eval₂ φ a f` is *defined* by

```
Classical.epsilon (fun c => (comap toMvPowerSeries (𝓝 f)).map (Polynomial.eval₂ φ a) ≤ 𝓝 c)
```

(`MvPowerSeries.eval₂` is `IsDenseInducing.extend`, `IsDenseInducing.extend` is
`Filter.limUnder` and `Filter.lim` is `Classical.epsilon`).  So `eval₂ φ z f` is the limit of the
polynomial evaluations `p ↦ p(z)` along the polynomials tending to `f` — when that limit exists.

For `f = Lps` that limit **does not exist** for `1/√2 < ‖z‖ < 1`: with
`p_N = trunc_N Lps + 2^N X^{2N}` one has `↑p_N → Lps` (coefficientwise convergence is convergence
for the product topology, `MvPowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto`), while
`p_N(z) - (trunc_N Lps)(z) = (2z²)^N → ∞` since `|2z²| = 2‖z‖² > 1`.  In that case the
`Classical.epsilon` falls back on its default, `Classical.choice (· : Nonempty ℂ)`, which by proof
irrelevance of `Nonempty ℂ` is the *same* opaque element of `ℂ` for every such `z`.  Hence the
requested identity cannot be derived from the axioms (and, if it held at two such `z`, it would
force `Complex.log (1 - z₁) = Complex.log (1 - z₂)`).

What *is* true — and what the request is really about — is the convergence of the coefficient
series to `Complex.log (1 - z)`, `Complex.hasSum_taylorSeries_neg_log`.  The evaluation of a
rational power series at a complex point used throughout this project is `Work.CLift.evA`
(`Submission/Work/CLift/defs.lean`); the results below state the identity for `evA`, and record
the "partial sums" form, which (being polynomial evaluations) *is* what `PowerSeries.eval₂`
computes.
-/

namespace Work.C7

open PowerSeries
open scoped Topology

/-- `Lps = log(1-x)`: its coefficient series converges to `Complex.log (1 - z)` on the unit disc. -/
theorem hasSum_Lps {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => ((PowerSeries.coeff n Lps : ℚ) : ℂ) * z ^ n) (Complex.log (1 - z)) := by
  have h := (Complex.hasSum_taylorSeries_neg_log hz).neg
  simp only [neg_neg] at h
  refine h.congr_fun ?_
  intro n
  rw [coeff_Lps]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [if_neg hn]
    push_cast
    ring

/-- The analytic evaluation of `Lps = log(1-x)`: `evA Lps z = Complex.log (1 - z)` for `‖z‖ < 1`.
This is the corrected form of the requested `Work.C7.eval2_Lps`. -/
theorem evA_Lps {z : ℂ} (hz : ‖z‖ < 1) : Work.CLift.evA Lps z = Complex.log (1 - z) := by
  rw [Work.CLift.evA]
  exact (hasSum_Lps hz).tsum_eq

/-- The partial sums of `Lps` — which *are* polynomials, and for which `PowerSeries.eval₂` is the
ordinary polynomial evaluation — converge to `Complex.log (1 - z)`.  This is the faithful form of
the requested `Work.C7.eval2_Lps`. -/
theorem tendsto_eval2_trunc_Lps {z : ℂ} (hz : ‖z‖ < 1) :
    Filter.Tendsto
      (fun N : ℕ => PowerSeries.eval₂ (algebraMap ℚ ℂ) z
        ((PowerSeries.trunc N Lps : Polynomial ℚ) : PowerSeries ℚ))
      Filter.atTop (𝓝 (Complex.log (1 - z))) := by
  have h := (hasSum_Lps hz).tendsto_sum_nat
  refine Filter.Tendsto.congr' ?_ h
  refine Filter.Eventually.of_forall fun N => ?_
  show (∑ i ∈ Finset.range N, ((PowerSeries.coeff i Lps : ℚ) : ℂ) * z ^ i)
      = PowerSeries.eval₂ (algebraMap ℚ ℂ) z
          ((PowerSeries.trunc N Lps : Polynomial ℚ) : PowerSeries ℚ)
  rw [PowerSeries.eval₂_coe, PowerSeries.eval₂_trunc_eq_sum_range]
  rfl

/-- `IsLinearTopology ℂ ℂ` is false for the usual topology on `ℂ`: the only `ℂ`-submodules of `ℂ`
are `⊥` and `⊤`, so a basis of neighbourhoods of `0` consisting of submodules would force
`({0} : Set ℂ) ∈ 𝓝 0`, which is impossible since `ℂ` is a nontrivial normed space.
This is why the evaluation lemmas for `PowerSeries.eval₂` (`eval₂_eq_tsum`, `hasSum_eval₂`,
`aeval`, …) do not apply with target `ℂ`. -/
theorem not_isLinearTopology_complex : ¬ IsLinearTopology ℂ ℂ := by
  intro h
  have hne : ({0} : Set ℂ) ∉ 𝓝 (0 : ℂ) := by
    intro hmem
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hmem
    have hx : ((ε / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) ε := by
      rw [Metric.mem_ball, dist_zero_right]
      have h1 : ‖((ε / 2 : ℝ) : ℂ)‖ = ε / 2 := by
        have h2 : Complex.normSq (((ε / 2 : ℝ) : ℂ)) = (ε / 2) ^ 2 := by
          rw [Complex.normSq_ofReal]; ring
        rw [Complex.normSq_eq_norm_sq] at h2
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h | h
        · linarith
        · have := norm_nonneg (((ε / 2 : ℝ) : ℂ)); linarith
      rw [h1]; linarith
    have hz : ((ε / 2 : ℝ) : ℂ) = 0 := by
      have := hball hx; simpa using this
    have : ε / 2 = 0 := Complex.ofReal_inj.mp hz
    linarith
  obtain ⟨N, hNmem, hNsub⟩ := h.hasBasis_submodule'.mem_iff.mp
    (Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1))
  by_cases h1 : (1 : ℂ) ∈ N
  · have := hNsub h1
    rw [Metric.mem_ball, dist_zero_right, norm_one] at this
    norm_num at this
  · have hNbot : ({0} : Set ℂ) = (N : Set ℂ) := by
      ext x
      constructor
      · intro hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact N.zero_mem
      · intro hx
        by_contra hx0
        exact h1 (by
          have := N.smul_mem (x⁻¹) hx
          rwa [smul_eq_mul, inv_mul_cancel₀ hx0] at this)
    exact hne (by rw [hNbot]; exact hNmem)

end Work.C7
