import Mathlib
import Submission.Work.LinnikAreas.Density4.qpow_prod_deriv

/-!
# The limit at `s = 1` of the regularised Euler product of `L(s, χ₀)`

For `q ≥ 2` put

`f(s) = q^s · ∏_{p | q} (1 - p^{-s})`  (so `f : ℂ → ℂ` is entire, `f(1) = φ(q)`).

Then `f(s) · ζ(s)` has a simple pole at `s = 1` whose singular part is `φ(q) / ((s-1) Γ_ℝ(s))`
(note `Γ_ℝ(1) = 1`); subtracting it gives a function that extends continuously to `s = 1`, and

`lim_{s → 1, s ≠ 1} [ f(s) ζ(s) - φ(q) / ((s-1) Γ_ℝ(s)) ]
   = φ(q) · (log q + ζ(1) + ∑_{p | q} log p / (p - 1))`,

where `ζ(1)` is Mathlib's value `(γ - log 4π)/2` of `riemannZeta` at `1`.

The proof rewrites the expression, for `s ≠ 1`, as

`f(s) · (ζ(s) - 1 / ((s-1) Γ_ℝ(s)))  +  (f(s) - f(1))/(s-1) · 1/Γ_ℝ(s)`,

i.e. a sum of products of:
* `f(s) → f(1) = φ(q)` (continuity);
* `ζ(s) - 1/((s-1)Γ_ℝ(s)) → ζ(1)` (Mathlib's `tendsto_riemannZeta_sub_one_div_Gammaℝ`);
* the difference quotient of `f` at `1`, tending to `f'(1)`
  (the separately proved `qpow_prod_deriv`);
* `1/Γ_ℝ(s) → 1/Γ_ℝ(1) = 1` (the reciprocal Gamma factor is entire).
-/

namespace Work.LinnikAreas.Density4

theorem limit_main (q : ℕ) [NeZero q] (hq : 2 ≤ q) :
    Filter.Tendsto
      (fun s : ℂ => (q : ℂ) ^ s * (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) * riemannZeta s
        - (q.totient : ℂ) / ((s - 1) * Complex.Gammaℝ s))
      (nhdsWithin (1 : ℂ) {1}ᶜ)
      (nhds ((q.totient : ℂ) * ((Real.log q : ℂ) + riemannZeta 1
        + ∑ p ∈ q.primeFactors, ((Real.log p / ((p : ℝ) - 1) : ℝ) : ℂ)))) := by
  classical
  -- the Euler-product factor `f` and its derivative value at `1`
  set f : ℂ → ℂ := fun s : ℂ => (q : ℂ) ^ s * ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s)) with hf
  -- `f 1 = φ(q)`
  have hf1 : f 1 = (q.totient : ℂ) := by
    rw [hf]
    have h := Nat.totient_eq_mul_prod_factors q
    have h' := congrArg (fun r : ℚ => (r : ℂ)) h
    push_cast at h'
    show (q : ℂ) ^ 1 * ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-1)) = (q.totient : ℂ)
    simp only [Complex.cpow_one, Complex.cpow_neg_one]
    exact h'.symm
  -- `f'(1) = φ(q) (log q + ∑ log p/(p-1))`
  have hf_deriv : HasDerivAt f ((q.totient : ℂ) * ((Real.log q : ℂ)
      + ∑ p ∈ q.primeFactors, ((Real.log p / ((p : ℝ) - 1) : ℝ) : ℂ))) 1 := by
    rw [hf]; exact qpow_prod_deriv q hq
  -- `f(s) → f(1) = φ(q)`
  have hA : Filter.Tendsto f (nhdsWithin (1 : ℂ) {1}ᶜ) (nhds (q.totient : ℂ)) := by
    have h := hf_deriv.continuousAt.tendsto
    rw [hf1] at h
    exact h.mono_left nhdsWithin_le_nhds
  -- `ζ(s) - 1/((s-1)Γ_ℝ(s)) → ζ(1)`
  have hZ : Filter.Tendsto (fun s : ℂ => riemannZeta s - 1 / ((s - 1) * Complex.Gammaℝ s))
      (nhdsWithin (1 : ℂ) {1}ᶜ) (nhds (riemannZeta 1)) := by
    have h := ZetaAsymptotics.tendsto_riemannZeta_sub_one_div_Gammaℝ
    rw [riemannZeta_one]
    refine h.congr' ?_
    filter_upwards with s
    rw [div_div]; ring_nf
  -- `1/Γ_ℝ(s) → 1`
  have hInvG : Filter.Tendsto (fun s : ℂ => 1 / Complex.Gammaℝ s)
      (nhdsWithin (1 : ℂ) {1}ᶜ) (nhds 1) := by
    have h := Complex.differentiable_Gammaℝ_inv.continuous.tendsto 1
    have h2 : Filter.Tendsto (fun s : ℂ => (Complex.Gammaℝ s)⁻¹)
        (nhdsWithin (1 : ℂ) {1}ᶜ) (nhds ((Complex.Gammaℝ 1)⁻¹)) :=
      h.mono_left (nhdsWithin_le_nhds (s := {1}ᶜ))
    simpa [one_div] using h2
  -- the difference quotient of `f` at `1` tends to `f'(1)`
  have hslope : Filter.Tendsto (slope f 1) (nhdsWithin (1 : ℂ) {1}ᶜ)
      (nhds ((q.totient : ℂ) * ((Real.log q : ℂ)
        + ∑ p ∈ q.primeFactors, ((Real.log p / ((p : ℝ) - 1) : ℝ) : ℂ)))) :=
    hf_deriv.tendsto_slope
  -- assemble the limit of the rewritten expression
  have hcomb : Filter.Tendsto
      (fun s : ℂ => f s * (riemannZeta s - 1 / ((s - 1) * Complex.Gammaℝ s))
        + slope f 1 s * (1 / Complex.Gammaℝ s))
      (nhdsWithin (1 : ℂ) {1}ᶜ)
      (nhds ((q.totient : ℂ) * ((Real.log q : ℂ) + riemannZeta 1
        + ∑ p ∈ q.primeFactors, ((Real.log p / ((p : ℝ) - 1) : ℝ) : ℂ)))) := by
    have h := (hA.mul hZ).add (hslope.mul hInvG)
    convert h using 1
    ring_nf
  -- the two functions agree near `s = 1` (indeed for all `s ≠ 1`)
  refine hcomb.congr' ?_
  filter_upwards with s
  rw [slope_def_field, hf1]
  simp only [hf]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end Work.LinnikAreas.Density4
