import Mathlib
import Submission.Work.KMTContract.Areas

/-!
# Definitions for Area A3 (`ℓ^p`-improving estimates for polynomial averages)

`Work.KMTContract.AreaA3` is the statement

`∀ Q : ℤ[X], 2 ≤ Q.natDegree → ∃ p : ℝ, 1 < p ∧ p < 2 ∧ ∃ C : ℝ≥0, 0 < C ∧ ∀ N ≥ 1, ∀ f : ℤ → ℂ,
  ‖A_N f‖_{ℓ²} ≤ C · N^{d(1/2-1/p)} · ‖f‖_{ℓ^p}`

where `A_N f(x) = N⁻¹ ∑_{n ≤ N} f (x - Q(n))` and `d = Q.natDegree`.  This is Krause–Mirek–Tao,
Proposition `lp-improv`, in the "for some `p < 2`" form that the paper uses.

## The route formalised here

For `k ≥ 1` put `κ = 1/(2k)`, so that `p := 2k/(k+1)` satisfies `1/p = 1/2 + κ`.  The whole
estimate is then equivalent to a single *arithmetic* input, involving the `2k`-th moment of the
polynomial exponential sum `S_N(θ) = ∑_{n ≤ N} e(-2πi θ Q(n))`:

  `∫₀¹ |N⁻¹ S_N(θ)|^{2k} dθ = N^{-2k} · E_k(N)`,
  `E_k(N) := polyEnergy Q k N = #{(n⃗,m⃗) ∈ [1,N]^k × [1,N]^k : ∑ᵢ Q(nᵢ) = ∑ⱼ Q(mⱼ)}`.

Namely, if `E_k(N) ≤ C^{2k} N^{2k-d}`, then Plancherel's identity for finite supports, Hölder's
inequality in the pair of exponents `(2k, (2k)')` with `(2k)' = 2k/(2k-1)`, and the
Hausdorff–Young inequality `‖f̂‖_{ℓ^{(2k)'}} ≤ ‖f‖_{ℓ^p}` (valid because `(2k)' = p'`) give

  `‖A_N f‖_{ℓ²} = ‖m_N · f̂‖_{L²} ≤ ‖m_N‖_{L^{2k}} ‖f̂‖_{L^{(2k)'}} ≤ C N^{-d/(2k)} ‖f‖_{ℓ^p}`,

and `N^{-d/(2k)} = N^{d(1/2-1/p)}` with `p = 2k/(k+1) < 2`.  So

`PolyEnergyBound Q` (below)  ⟹  `PolyImproving Q`,

with the reduction carried out in `Submission/Work/KMTAreas/area_A3.lean`.
-/

set_option autoImplicit false

namespace Work.A3

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- The `s`-fold **energy** of the polynomial sequence `Q(1),…,Q(N)`: the number of pairs of
`s`-tuples in `[1,N]^s` whose `Q`-sums agree.  (This is the number of pairs of `s`-tuples, so it
is the `2s`-th moment of the exponential sum: `∫₀¹|∑_{n≤N}e(-2πiθQ(n))|^{2s}dθ = polyEnergy Q s N`;
see `Work.A3.moment_identity`.) -/
def polyEnergy (Q : ℤ[X]) (s N : ℕ) : ℕ :=
  (((Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (N : ℤ))).product
   (Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (N : ℤ)))).filter
   (fun p => (∑ i, Q.eval (p.1 i)) = (∑ i, Q.eval (p.2 i)))).card

/-- **The arithmetic core of Area A3**: for *some* `s ≥ 2`, the energy of the polynomial sequence
is bounded by `C^{2s} N^{2s-d}`, `d = deg Q`.  (Since the energy is the `2s`-th moment of the
exponential sum, this is exactly the statement `‖m_N‖_{L^{2s}} ≤ C N^{-d/(2s)}`.)  For `s` large
this is the classical "many variables" mean-value estimate for polynomial exponential sums (a
Vinogradov/Hua-type bound): Weyl's inequality for the minor arcs together with the circle method
on the major arcs.  Note that `s` has to be taken *large*: the estimate is sharp, and for small
`s` the arithmetic fluctuations of the representation count (class numbers, i.e. `L(1,χ)` factors
for `d = 2`) defeat it; for `s` large the singular series converges and the bound is the classical
Waring-type asymptotic upper bound.  (`s ≥ 2` is exactly what the reduction to `PolyImproving`
needs: it makes `p = 2s/(s+1) > 1`.) -/
def PolyEnergyBound (Q : ℤ[X]) : Prop :=
  ∃ s : ℕ, 2 ≤ s ∧ ∃ C : ℝ≥0, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
    (polyEnergy Q s N : ℝ) ≤ (C : ℝ) ^ (2 * s) * (N : ℝ) ^ (2 * s - Q.natDegree)

/-- The normalised polynomial exponential sum `m_N(θ) = N⁻¹ ∑_{n ∈ [1,N]} e(-2πi θ Q(n))`,
the Fourier multiplier of the averaging operator `A_N f(x) = N⁻¹∑_{n≤N} f(x - Q(n))`. -/
def kmtMul (Q : ℤ[X]) (N : ℕ) (θ : ℝ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N,
    Complex.exp (-(2 * Real.pi * Complex.I * (((Q.eval (n : ℤ) : ℤ) : ℝ) * θ)))

/-- The Fourier transform `f̂(θ) = ∑_x f(x) e(-2πi x θ)` of a function on `ℤ`, as a function of
the frequency `θ ∈ ℝ` (it is `1`-periodic). -/
def kmtFhat (f : ℤ → ℂ) (θ : ℝ) : ℂ :=
  ∑' x : ℤ, f x * Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℝ) * θ)))

end

end Work.A3
