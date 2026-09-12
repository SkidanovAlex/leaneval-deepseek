import Mathlib
import Submission.Minpoly
import Submission.Powers
import Submission.GOnCutPlane
import Submission.SquarePoly
import Submission.RootOfUnity
import Submission.SquareReflect
import Submission.RationalSqrt
import Submission.Kronecker
import Submission.Induction

/-!
# Algebraic tail of the analytic engine

The engine `Submission.Engine.house_bound_of_pow2_irreducible` reduces (by
contradiction under `house α < 2^(1/(4·|argSet α|))`) to proving that the
integer Hankel determinants `hankelDet a k` of the formal square-root
sequence `a` of `Gpoly (minpoly ℤ α)` vanish for all large `k`.  That last
step is the *analytic* content (Pólya/Bertrandias/Dubinin; not proved here).

This module proves the purely algebraic tail: **if** the Hankel determinants
`hankelDet a k` are eventually zero, **then** `pow4 P = pow2 P`
(`P := minpoly ℤ α`) and hence `α` is a root of unity -- contradicting the
`¬ IsOfFinOrder α` hypothesis of the engine.  The chain (all verified
elsewhere) is:

1. `Submission.Kronecker.seriesRational_of_hankel_eventually_zero`:
   eventually-vanishing Hankel determinants make the integer sequence `a`
   rational (`SeriesRational a`);
2. `Submission.RationalSqrt.square_of_rational_conv_square`: a rational
   sequence whose convolution-square is `G.coeff` makes `G` a perfect square
   in `ℤ[X]`;
3. `Submission.SquareReflect.pow_product_square_of_reflect_square`: a square
   `G = (R₂R₄)` forces `pow2 P * pow4 P` to be a square;
4. `Submission.SquarePoly.pow4_eq_pow2_of_square`: if `pow2 P` is irreducible,
   the only way `pow2 P * pow4 P` is a square is `pow4 P = pow2 P`;
5. `Submission.RootOfUnity.pow4_eq_pow2_imp_rootOfUnity`: that equality makes
   `α` a root of unity, contradiction.

Also recorded here is the engine's *desired input form*:
`EngineHankelInput α` says exactly "there is an integer `a` with `a 0 = 1`,
`conv²(a) = Gpoly-coefficients`, and `hankelDet a k = 0` for all large `k`".
The analytic engine will construct that input from
`house α < 2^(1/(4·|argSet α|))`; this module shows that such an input
contradicts the engine hypotheses.
-/

noncomputable section

open scoped Polynomial Topology

namespace Submission.EngineAlg

open Polynomial
open Submission.Powers
open Submission.GOnCutPlane
open Submission.Kronecker
open Submission.RationalSqrt
open Submission.SquareReflect
open Submission.SquarePoly
open Submission.RootOfUnity
open Submission.Minpoly

variable {K : Type*} [Field K] [NumberField K]

/-- The convolution-square data of `a` matching `G := Gpoly (minpoly ℤ α)`. -/
def ConvSq (P : ℤ[X]) (a : ℕ → ℤ) : Prop :=
  ∀ k : ℕ, (∑ i ∈ Finset.range (k + 1), a i * a (k - i)) = (Gpoly P).coeff k

/-- The analytic input the engine must produce from `house α` being small:
an integer sequence `a` (the coefficients of the formal square root of
`Gpoly (minpoly ℤ α)` at `w = 0`, so `a 0 = 1` and `(∑ aᵢaⱼ) = G.coeff`)
whose Hankel determinants `det (a(i+j))_{i,j<k}` are eventually zero. -/
def HankelInput (α : K) (hα : IsIntegral ℤ α) : Prop :=
  let P : ℤ[X] := minpoly ℤ α
  ∃ a : ℕ → ℤ, a 0 = 1 ∧ ConvSq P a ∧
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → hankelDet a k = 0

/-- A nonzero algebraic integer whose formal square-root sequence `a` of
`Gpoly (minpoly ℤ α)` has eventually vanishing Hankel determinants is a root
of unity.  (Algebraic tail: Kronecker + rational-square + dichotomy.) -/
theorem rootOfUnity_of_hankelInput (α : K) (hα : IsIntegral ℤ α) (hα0 : α ≠ 0)
    (h2irr : Irreducible (pow2 (minpoly ℤ α))) :
    HankelInput α hα → IsOfFinOrder α := by
  classical
  intro hInput
  let P : ℤ[X] := minpoly ℤ α
  have hPmonic : P.Monic := minpoly_int_monic α hα
  rcases hInput with ⟨a, ha0, haConv, K, hK⟩
  -- 1. Kronecker: eventually vanishing Hankel determinants ⟹ rational.
  have hrat : SeriesRational a :=
    seriesRational_of_hankel_eventually_zero a ha0 ⟨K, hK⟩
  -- 2. rational + convolution-square ⟹ Gpoly P is a perfect square.
  have hsqG : ∃ g : ℤ[X], Gpoly P = g ^ 2 := by
    exact square_of_rational_conv_square a (Gpoly P) haConv hrat
  -- 3. reflection: a square of R₂R₄ = Gpoly P forces pow2 P * pow4 P square.
  have hsqPP : ∃ f : ℤ[X], pow2 P * pow4 P = f ^ 2 := by
    refine pow_product_square_of_reflect_square P hPmonic ?_
    simpa [Gpoly] using hsqG
  -- 4. irreducibility of pow2 P: the product square forces pow4 P = pow2 P.
  have h4eq2 : pow4 P = pow2 P := pow4_eq_pow2_of_square P hPmonic h2irr hsqPP
  -- 5. that equality forces α to be a root of unity.
  change pow4 (minpoly ℤ α) = pow2 (minpoly ℤ α) at h4eq2
  exact pow4_eq_pow2_imp_rootOfUnity α hα hα0 h4eq2

/-- **The engine's algebraic contradiction.**  Under the engine hypotheses
(`¬ IsOfFinOrder α`, `pow2 (minpoly ℤ α)` irreducible), no Hankel input can
exist. -/
theorem no_hankelInput (α : K) (hα : IsIntegral ℤ α) (hα0 : α ≠ 0)
    (hROU : ¬ IsOfFinOrder α) (h2irr : Irreducible (pow2 (minpoly ℤ α))) :
    ¬ HankelInput α hα := by
  intro hInput
  exact hROU (rootOfUnity_of_hankelInput α hα hα0 h2irr hInput)

/-- Failure of the house bound means `house α` is strictly below the bound
`2^(1/(4·|argSet α|))`.  (The engine proceeds by contradiction from this.) -/
lemma house_lt_of_not_bound (α : K) :
    ¬ Submission.Induction.Bound α → NumberField.house α <
      (2 : ℝ) ^ (1 / (4 * ((Submission.Conjugates.argSet α).card : ℝ))) := by
  intro hnot
  dsimp [Submission.Induction.Bound] at hnot
  exact lt_of_not_ge hnot

end Submission.EngineAlg

end
