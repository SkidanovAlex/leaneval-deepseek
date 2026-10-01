import Mathlib
import Submission.Work.LinnikAreas.Density4.limit_main

/-!
# The value at `s = 1` of the `L`-function of the trivial character mod `q`

For the trivial Dirichlet character `1` modulo `q` (`q ≥ 2`), the `L`-function
`L(s, χ₀) = ζ(s) ∏_{p | q} (1 - p^{-s})` has a simple pole at `s = 1`.  Mathlib's
`DirichletCharacter.LFunction` assigns a definite value at that pole (it is defined as a
linear combination of Hurwitz zeta functions), and this file computes it:

`L(1, χ₀) = (∏_{p | q} (1 - p⁻¹)) * (log q + ζ(1) + ∑_{p | q} log p / (p - 1))`,

where `ζ(1)` is Mathlib's value `(γ - log 4π)/2` of the Riemann zeta function at `1`.

The proof reduces the value to the limit of the meromorphic identity
`L(s, χ₀) = ζ(s) ∏_{p | q} (1 - p^{-s})` (`LFunctionTrivChar_eq_mul_riemannZeta`) after
subtracting the common pole `φ(q) / ((s-1) Γ_ℝ(s))`; the `Γ_ℝ(s)` normalisation is exactly
what turns the Euler–Mascheroni constant `γ` into Mathlib's `ζ(1)`.
-/

open DirichletCharacter

namespace Work.LinnikAreas.Density4

/-- Euler's product formula for `Nat.totient`, transported to `ℂ`. -/
theorem totient_cast_eq (q : ℕ) :
    (q.totient : ℂ) = (q : ℂ) * ∏ p ∈ q.primeFactors, (1 - (p : ℂ)⁻¹) := by
  have h := Nat.totient_eq_mul_prod_factors q
  have h' := congrArg (fun r : ℚ => (r : ℂ)) h
  push_cast at h'
  exact h'

theorem LFunction_one_apply_one (q : ℕ) [NeZero q] (hq : 2 ≤ q) :
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) 1
      = (∏ p ∈ q.primeFactors, ((1 : ℂ) - (p : ℂ)⁻¹))
        * ((Real.log q : ℂ) + riemannZeta 1
            + ∑ p ∈ q.primeFactors, ((Real.log p / ((p : ℝ) - 1) : ℝ) : ℂ)) := by
  classical
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  set S : ℂ := ∑ p ∈ q.primeFactors, ((Real.log p / ((p : ℝ) - 1) : ℝ) : ℂ) with hS
  set R : ℂ := ∏ p ∈ q.primeFactors, ((1 : ℂ) - (p : ℂ)⁻¹) with hR
  -- Unfolding of the `L`-function as a linear combination of Hurwitz zeta functions.
  have hdef : ∀ s : ℂ, DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s
      = (q : ℂ)^(-s) * ∑ a : ZMod q, (1 : DirichletCharacter ℂ q) a
          * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle a) s := by
    intro s; rw [DirichletCharacter.LFunction, ZMod.LFunction]
  -- The total mass of the trivial character is `φ(q)`.
  have hsumc : ∑ a : ZMod q, (1 : DirichletCharacter ℂ q) a = (q.totient : ℂ) := by
    rw [MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]
  -- `q^s · L(s, χ₀)` is the raw Hurwitz-zeta combination.
  have h2 : ∀ s : ℂ, (q : ℂ)^s * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s
      = ∑ a : ZMod q, (1 : DirichletCharacter ℂ q) a
          * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle a) s := by
    intro s
    rw [hdef s, ← mul_assoc, ← Complex.cpow_add s (-s) hq0, add_neg_cancel,
      Complex.cpow_zero, one_mul]
  -- Away from `s = 1`, that combination is the Euler-product expression.
  have hTs : ∀ s : ℂ, s ≠ 1 → (∑ a : ZMod q, (1 : DirichletCharacter ℂ q) a
        * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle a) s)
      = (q : ℂ)^s * (∏ p ∈ q.primeFactors, (1 - (p : ℂ)^(-s))) * riemannZeta s := by
    intro s hs1
    rw [← h2 s, mul_assoc]
    congr 1
    exact DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := q) hs1
  -- Each summand, with the common pole removed, tends to its value at `s = 1`.
  have hlimU : Filter.Tendsto
      (fun s : ℂ => ∑ a : ZMod q, (1 : DirichletCharacter ℂ q) a *
        (HurwitzZeta.hurwitzZeta (ZMod.toAddCircle a) s - 1 / ((s - 1) * Complex.Gammaℝ s)))
      (nhds (1:ℂ))
      (nhds (∑ a : ZMod q, (1 : DirichletCharacter ℂ q) a
        * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle a) 1)) := by
    refine tendsto_finset_sum _ (fun a _ => ?_)
    refine Filter.Tendsto.mul tendsto_const_nhds ?_
    refine (HurwitzZeta.tendsto_hurwitzZeta_sub_one_div_nhds_one (ZMod.toAddCircle a)).congr' ?_
    filter_upwards with s
    rw [div_div]
  -- The same expression coincides with the pole-subtracted Euler product near `s = 1`.
  have hev : (fun s : ℂ => ∑ a : ZMod q, (1 : DirichletCharacter ℂ q) a *
          (HurwitzZeta.hurwitzZeta (ZMod.toAddCircle a) s - 1 / ((s - 1) * Complex.Gammaℝ s)))
      =ᶠ[nhdsWithin (1 : ℂ) {1}ᶜ]
      (fun s : ℂ => (q : ℂ)^s * (∏ p ∈ q.primeFactors, (1 - (p : ℂ)^(-s))) * riemannZeta s
          - (q.totient : ℂ) / ((s - 1) * Complex.Gammaℝ s)) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs1 : s ≠ 1 := hs
    simp only [mul_sub, Finset.sum_sub_distrib, div_eq_mul_inv, one_mul]
    rw [← Finset.sum_mul, hsumc, hTs s hs1]
  have hlimG : Filter.Tendsto
      (fun s : ℂ => (q : ℂ)^s * (∏ p ∈ q.primeFactors, (1 - (p : ℂ)^(-s))) * riemannZeta s
          - (q.totient : ℂ) / ((s - 1) * Complex.Gammaℝ s))
      (nhdsWithin (1 : ℂ) {1}ᶜ)
      (nhds ((q.totient : ℂ) * ((Real.log q : ℂ) + riemannZeta 1 + S))) := by
    rw [hS]; exact limit_main q hq
  -- Hence the raw combination equals `φ(q) * (log q + ζ(1) + S)`.
  have hsum1 : (∑ a : ZMod q, (1 : DirichletCharacter ℂ q) a
        * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle a) 1)
      = (q.totient : ℂ) * ((Real.log q : ℂ) + riemannZeta 1 + S) :=
    tendsto_nhds_unique (hlimU.mono_left nhdsWithin_le_nhds |>.congr' hev) hlimG
  rw [hdef 1, hsum1]
  rw [Complex.cpow_neg, Complex.cpow_one]
  have hφR : (q:ℂ)⁻¹ * (q.totient : ℂ) = R := by
    rw [hR, totient_cast_eq]
    rw [← mul_assoc, inv_mul_cancel₀ hq0, one_mul]
  rw [← mul_assoc, hφR]

end Work.LinnikAreas.Density4
