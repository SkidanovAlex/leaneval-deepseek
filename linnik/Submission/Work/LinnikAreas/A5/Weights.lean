/-
# Area 5 (HB Lemma 13.3): the test-function family used in the proof

HB's test function of Lemma 13.3 is `f₁(t) = sinh((K−t)λ)` on `[0,K]`, normalised so that
`f(0) = 1` (the normalisation is what makes the constant in the smoothing estimate (§5) uniform
in λ).  Both the smoothing estimate and the Chebyshev-ψ (Lambert) input need the test function to
be bounded *everywhere* on ℝ (the Lambert lemma hypotheses the global bound `‖f‖ ≤ M`), so we cut
the smooth branch off at `t = 0`:

* `wc K lam t = (sinh (Kλ))⁻¹ * f₁(K,λ,t)` for `t ≥ 0`, and `0` for `t < 0`  (the λ > 0 family);
* `gc K t = (K−t)/K` for `t ∈ [0,K]`, and `0` elsewhere                    (the λ = 0 endpoint).

Both are globally bounded by `1`, supported in `[0,K]`, equal to `1` at `t = 0`, C² on `(0,K)`,
and their Laplace transforms over `(0,K)` are `(sinh (Kλ))⁻¹ · F₁(K,λ,·)` and `G₀(K,·)`.
-/
import Mathlib
import Submission.Work.LinnikAreas.A5.Basic

open Complex DirichletCharacter Metric
open scoped Interval Topology BigOperators

noncomputable section

namespace Work.LinnikAreas.A5

/-- The normalised test function of HB Lemma 13.3 for `λ > 0`, cut off at `t = 0`
(so that it is bounded on all of ℝ): `wc K lam t = 1` at `t = 0`,
`= sinh((K−t)λ)/sinh(Kλ)` for `0 ≤ t ≤ K`, and `0` outside `[0,K]`. -/
def wc (K lam : ℝ) : ℝ → ℝ :=
  fun t => if 0 ≤ t then (Real.sinh (K * lam))⁻¹ * f1 K lam t else 0

/-- The `λ = 0` endpoint test function of Lemma 13.3, cut off at `t = 0`:
`gc K t = (K−t)/K` on `[0,K]` and `0` outside. -/
def gc (K : ℝ) : ℝ → ℝ :=
  fun t => if 0 ≤ t ∧ t ≤ K then (K - t) / K else 0

/-- The Laplace transform of the normalised weight `wc K lam`, i.e. `∫₀^K e^{-zt} wc(t) dt`
(equivalently `∫₀^K e^{-zt} (sinh (Kλ))⁻¹ f₁(t) dt`, since `wc` agrees with the normalised
`f₁` on `(0,K)`). -/
def Ftil (K lam : ℝ) : ℂ → ℂ := fun z => ((Real.sinh (K * lam))⁻¹ : ℂ) * F1 K lam z

lemma wc_of_nonneg {K lam t : ℝ} (h : 0 ≤ t) :
    wc K lam t = (Real.sinh (K * lam))⁻¹ * f1 K lam t := if_pos h

lemma wc_of_neg {K lam t : ℝ} (h : t < 0) : wc K lam t = 0 := if_neg (not_le.mpr h)

lemma gc_of_mem {K t : ℝ} (h0 : 0 ≤ t) (hK : t ≤ K) : gc K t = (K - t) / K :=
  if_pos ⟨h0, hK⟩

lemma gc_of_not_mem {K t : ℝ} (h : ¬(0 ≤ t ∧ t ≤ K)) : gc K t = 0 := if_neg h

lemma gc_of_ge {K t : ℝ} (h : K ≤ t) : gc K t = 0 := by
  by_cases hmem : 0 ≤ t ∧ t ≤ K
  · rw [gc, if_pos hmem, le_antisymm hmem.2 h, sub_self, zero_div]
  · exact if_neg hmem

lemma gc_of_lt {K t : ℝ} (h : t < 0) : gc K t = 0 :=
  if_neg (fun hc => absurd h (not_lt.mpr hc.1))

end Work.LinnikAreas.A5
