import Mathlib
import Submission.Work.A3.moment_identity

/-!
# The circle-method vocabulary of Area A3

This module collects the objects in which the *arithmetic core* `Work.A3.PolyEnergyBound` of
Area A3 is phrased, so that the pieces of its proof (the minor-arc bound = Weyl's inequality,
the major arcs = complete sums + the singular integral, and the assembly) can be stated and
proved independently.

## The exponential sum and the energy

`expSum Q N θ = ∑_{n=1}^{N} e(-2πi θ Q(n))` is (up to the sign convention, which is the one of
`Work.A3.kmtMul`) the polynomial exponential sum whose `2k`-th moment is the energy:

`∫₀¹ ‖expSum Q N θ‖^{2k} dθ = polyEnergy Q k N`.

Hence `PolyEnergyBound Q` is literally the statement `∃ s ≥ 2, ∃ C, ∀ N ≥ 1,
∫₀¹‖expSum Q N‖^{2s} ≤ C^{2s} N^{2s-d}`, i.e. the **sharp ("Waring-type") mean value estimate**
for the exponential sum: the analysis of it is the Hardy–Littlewood circle method.

## The circle-method pieces

* `completeSum Q a q = ∑_{r<q} e(-2πi a Q(r)/q)` — the complete exponential sum mod `q`; its
  power saving `‖completeSum Q a q‖ ≤ C q^{1-δ}` (`(a,q) = 1`, `δ > 0`, `C` depending on `Q`,
  Weyl differencing over `ℤ/q`) is what makes the major-arc contribution summable in `q`;
* `Qreal Q` is `Q` viewed as a real polynomial, `singInt Q N β = ∫₀^{N} e(-2πi β Q(t)) dt` is the
  singular integral; `∫_ℝ ‖singInt Q N β‖^{2s} dβ ≤ C^{2s} N^{2s-d}` (first-derivative test) is
  the second ingredient of the major arcs;
* `majorArcSet Q N η` is the union of the closed arcs of radius `1/(q N^{d/2})` around the
  reduced fractions `a/q` with `1 ≤ q ≤ N^η` (`d = deg Q`): the *major arcs*.  Its complement is
  where Weyl's inequality gives `‖expSum Q N θ‖ ≤ N^{1-δ}`.

The dichotomy "major arcs / minor arcs" of the circle method is
`[0,1] = majorArcSet Q N η ∪ (majorArcSet Q N η)ᶜ`: on the complement, the Dirichlet
approximation `‖θ - a/q‖ ≤ 1/(q N^{d/2})`, `q ≤ N^{d/2}`, has `q > N^η`, and Weyl's inequality
turns this into a power saving in `N`.
-/

set_option autoImplicit false

namespace Work.A3

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- The polynomial exponential sum `S_N(θ) = ∑_{n ∈ [1,N]} e(-2πi θ Q(n))`, in the sign
convention of the multiplier `Work.A3.kmtMul` (so that `kmtMul Q N θ = N⁻¹ * expSum Q N θ`). -/
def expSum (Q : ℤ[X]) (N : ℕ) (θ : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N,
    Complex.exp (-(2 * Real.pi * Complex.I * (((Q.eval (n : ℤ) : ℤ) : ℝ) * θ)))

/-- `expSum` is `N` times the multiplier `kmtMul`. -/
lemma kmtMul_eq_inv_mul_expSum (Q : ℤ[X]) (N : ℕ) (θ : ℝ) :
    kmtMul Q N θ = (N : ℂ)⁻¹ * expSum Q N θ := rfl

/-- **The energy is the moment of `expSum`**: `∫₀¹‖expSum Q N‖^{2k} = polyEnergy Q k N`.

This is `Work.A3.moment_identity` unwound through `kmtMul = N⁻¹ expSum`. -/
theorem integral_norm_expSum_pow (Q : ℤ[X]) (N k : ℕ) (hN : 1 ≤ N) :
    ∫ θ in Set.Icc (0 : ℝ) 1, ‖expSum Q N θ‖ ^ (2 * k) = (polyEnergy Q k N : ℝ) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hpt : ∀ θ : ℝ, ‖expSum Q N θ‖ ^ (2 * k)
      = ((N : ℝ) ^ (2 * k)) * ‖kmtMul Q N θ‖ ^ (2 * k) := by
    intro θ
    rw [kmtMul_eq_inv_mul_expSum, norm_mul]
    have h1 : ‖((N : ℂ))⁻¹‖ = ((N : ℝ))⁻¹ := by
      rw [norm_inv, Complex.norm_natCast]
    rw [h1, mul_pow, inv_pow]
    field_simp
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    moment_identity Q N k hN]
  field_simp

/-- The **complete exponential sum** mod `q`: `∑_{r=0}^{q-1} e(-2πi a Q(r)/q)`. -/
def completeSum (Q : ℤ[X]) (a : ℤ) (q : ℕ) : ℂ :=
  ∑ r ∈ Finset.range q,
    Complex.exp (-(2 * Real.pi * Complex.I * ((a : ℝ) * ((Q.eval (r : ℤ) : ℤ) : ℝ) / (q : ℝ))))

/-- The polynomial `Q`, viewed as a real polynomial (for the singular integral). -/
def Qreal (Q : ℤ[X]) : ℝ[X] := Q.map (Int.castRingHom ℝ)

/-- The **singular integral** `v(β) = ∫₀^{N} e(-2πi β Q(t)) dt`. -/
def singInt (Q : ℤ[X]) (N : ℕ) (β : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..(N : ℝ),
    Complex.exp (-(2 * Real.pi * Complex.I * (β * (Qreal Q).eval t)))

/-- The **major arcs** of the circle method at level `η`: the union of the closed arcs of radius
`1/(q N^{d/2})` around the reduced fractions `a/q` with `q ≤ N^η`, where `d = deg Q`. -/
def majorArcSet (Q : ℤ[X]) (N : ℕ) (η : ℝ) : Set ℝ :=
  {θ : ℝ | ∃ (q : ℕ) (a : ℤ), 1 ≤ q ∧ IsCoprime a (q : ℤ) ∧ (q : ℝ) ≤ (N : ℝ) ^ η ∧
    |θ - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) * (N : ℝ) ^ ((Q.natDegree : ℝ) / 2))}

end

end Work.A3
