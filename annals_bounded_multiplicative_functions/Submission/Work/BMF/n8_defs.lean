import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# N8: definitions for the passage from local to global structure

Definitions (no proofs) for the node `Work.BMF.global_structure` (MRTTZ §3, from Prop. 3.9 to the
end of the section).

* `Qprod Ps` is `∏_{p ∈ Ps} p` as a real number.
* `GoodQuad A δ x T q qf γ Ps` is the "good quadruple" of MRTTZ §3: a local structure
  `(x, T, q, qf, γ, Ps)` at an interval `x` of the family `A.fam`, with the frequency `T`, the
  minimal coarse modulus `q`, the modulus `qf` of the fine lattice condition produced by
  `solve_adi` (N6), the lattice part `γ` of the phase and the large set `Ps` of primes certifying it.
* `ModZConst γ γ'` is `γ = γ' mod ℤ` (their difference is a constant integer polynomial).
* `Latc k l qf Ps = (∏Ps)^l / (k! qf^k)` is the lattice in which the `l`-th derivative of `γ` at
  an integer point lies (MRTTZ Lemma `dte` combined with `int_fine`).
* `PrimesBig k δ X P₂` is the "`∏𝒫` is effectively infinite" input: the product of any large set
  of primes in `[P₂/2, P₂]` dominates all polynomial-size quantities.
* `LocalTwist f ψ T₀ x L H' c` is the extraction conclusion on a single interval.
-/

namespace Work.BMF

open Polynomial BoundedMultiplicativeFunctions

/-- `∏_{p ∈ Ps} p`, as a real number. -/
noncomputable def Qprod (Ps : Finset ℕ) : ℝ := ∏ p ∈ Ps, (p : ℝ)

/-- The lattice constant of a good quadruple at level `l`: `(∏Ps)^l / (k! qf^k)`. -/
noncomputable def Latc (k l : ℕ) (qf : ℕ) (Ps : Finset ℕ) : ℝ :=
  (Qprod Ps) ^ l / ((k.factorial : ℝ) * (qf : ℝ) ^ k)

/-- **The good quadruple** of MRTTZ §3 (after Prop. 3.8): a local structure
`(x, T, q, qf, γ, Ps)` at a point `x` of the family.

* `T` is the frequency, with `|T| ≤ δ⁻¹ N^{k+1}` where `N = X/L`.
* `q` is the *minimal* natural number with `IntegralOn q γ`, and `q ≤ X^{1/δ}`.
* `qf` is the modulus of the fine lattice condition `IntegralOn (qf / ∏Ps) γ` produced by
  `solve_adi` (N6); it is also of polynomial size, and `q ∣ qf`.
* `Ps` is a set of primes in `[P₂/2, P₂]` of cardinality `≥ δ π₀(P₂)`, none dividing `q`.
* `γ` has degree `≤ k`, and `P_x = ε + (T/2π) log + γ` on `[x, x+L]` with `|ε'| ≤ δ⁻¹/L`. -/
structure GoodQuad {k : ℕ} {f : ℕ → ℂ} {cA CA X L P₁ P₂ : ℝ} {ℓ : ℕ}
    (A : ADIData k f cA CA X L P₁ P₂ ℓ) (δ : ℝ) (x T : ℝ) (q qf : ℕ) (γ : Polynomial ℝ)
    (Ps : Finset ℕ) : Prop where
  x_mem : x ∈ A.fam
  deg : γ ∈ degreeLE ℝ (k : WithBot ℕ)
  T_bound : |T| ≤ δ⁻¹ * (X / L) ^ (k + 1)
  q_bound : 1 ≤ q
  q_le : (q : ℝ) ≤ X ^ (1 / δ)
  qf_bound : 1 ≤ qf
  qf_le : (qf : ℝ) ≤ X ^ (1 / δ)
  primes : ∀ p ∈ Ps, IsPrimeIn (P₂ / 2) P₂ p
  card : δ * pi0 P₂ ≤ (Ps.card : ℝ)
  not_dvd : ∀ p ∈ Ps, ¬ p ∣ q
  int_coarse : IntegralOn (q : ℝ) γ
  minimal : ∀ r : ℕ, 1 ≤ r → IntegralOn (r : ℝ) γ → q ≤ r
  int_fine : IntegralOn ((qf : ℝ) / Qprod Ps) γ
  decomp : ∀ t ∈ Set.Icc x (x + L),
    |deriv (fun s ↦ (A.pol x).eval s - T / (2 * Real.pi) * Real.log s - γ.eval s) t|
      ≤ δ⁻¹ / L

/-- `γ` and `γ'` agree modulo the constant integer polynomials. -/
def ModZConst (γ γ' : Polynomial ℝ) : Prop := ∃ c : ℤ, γ = γ' + Polynomial.C (c : ℝ)

/-- The "`∏𝒫` is effectively infinite" input: the product of any set of primes in `[P₂/2, P₂]`
of cardinality at least `δ¹² π₀(P₂)` dominates all polynomial-size quantities (everything bounded
by `X^{1/δ}` and by `(X/L)^{k+1}`). -/
def PrimesBig (k : ℕ) (δ X P₂ : ℝ) : Prop :=
  ∀ Ps : Finset ℕ, (∀ p ∈ Ps, IsPrimeIn (P₂ / 2) P₂ p) → δ ^ 12 * pi0 P₂ ≤ (Ps.card : ℝ) →
    ((k.factorial : ℝ) * (X ^ (1 / δ)) ^ (2 * k)) *
      (2 * ((k : ℝ) + 1) * δ⁻¹ * ((X ^ (1 / δ)) ^ (k + 1) + 1)) ≤ Qprod Ps

/-- The conclusion of the extraction step (MRTTZ, last page of §3) on a single interval:
the average over shifts `y ∈ [x, x+L]` of the twisted short sum of length `H'` is `≫ L H'`. -/
noncomputable def LocalTwist (f ψ : ℕ → ℂ) (T₀ x L H' c : ℝ) : Prop :=
  c * L * H' ≤ ∫ y in x..(x + L),
    ‖∑ n ∈ natIcc y (y + H'), f n * ψ n * (n : ℂ) ^ (-(Complex.I * T₀))‖


/-- The number of geometric quadruples between `A₁` and `A₂`: tuples `(i, i', p, p')` with
`i ∈ A₁`, `i' ∈ A₂`, `p, p'` primes in `[Pp, 2Pp]` and `Gq i i' p p'`. -/
noncomputable def quadCount {ι : Type} [DecidableEq ι] (Gq : ι → ι → ℕ → ℕ → Prop)
    [∀ (i i' : ι) (p p' : ℕ), Decidable (Gq i i' p p')] (Pp : ℝ) (A₁ A₂ : Finset ι) : ℕ :=
  (((A₁.product A₂).product ((primesIn Pp (2 * Pp)).product (primesIn Pp (2 * Pp)))).filter
    (fun v ↦ Gq v.1.1 v.1.2 v.2.1 v.2.2)).card

end Work.BMF
